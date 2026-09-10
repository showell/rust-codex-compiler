//! The CST to the AST: Cobblestone's `Desugarer.codex`.
//!
//! Seven forms are REWRITTEN rather than translated, and each one is a rule
//! nothing in the parse tree hints at:
//!
//! ```text
//! (a, b)              ->  MkTup2 a b
//! for x in xs -> b    ->  map-list (\x -> b) xs
//! (e)                 ->  e
//! not x               ->  x == False
//! a |> f              ->  f a                 -- the operands SWAP
//! s in rest           ->  let __seq = s in rest
//! e revised { f = v } ->  let __rev = e in let __rv0 = v in
//!                         __record-set __rev "f" __rv0
//! ```
//!
//! Two are easy to get subtly wrong and neither is caught by a
//! declaration-layer gate:
//!
//! - `|>` SWAPS its operands. `a |> f` is `f a`.
//! - `for .. ->` is a comprehension, not a loop, and lowers to `map-list` over
//!   a lambda. That is why a chapter using comprehensions needs `Foreword
//!   ListUtils` in scope even though it never writes `map-list`.
//!
//! `not x` becoming `x == False` is the one that looks like a mistake and is
//! not: there is no negation node in the AST, and `AUnaryExpr` is arithmetic
//! negation alone.
//!
//! Application is curried on both sides -- our `App` node is built one
//! argument at a time and `AApplyExpr` takes one -- so that translation is
//! structural rather than a fold.

use crate::ast::*;
use crate::symbol::SymTab;
use std::cell::RefCell;
use std::rc::Rc;
use crate::cst::{Node, NodeKind};
use crate::token::{Kind, Token};

pub struct Desugar<'a> {
    src: &'a [u8],
    slug: String,
    /// **A `RefCell` so the fourteen `&self` methods below keep their
    /// signatures.** Interning needs `&mut`, and threading mutability through
    /// a recursive-descent lowering that never mutates anything else would
    /// have been a worse trade than one borrow flag per name. The table moves
    /// into the `Chapter` when the walk finishes.
    syms: RefCell<SymTab>,
    /// **A SYNTHETIC NODE GETS AN IDENTITY, NOT A POSITION.** Every node this
    /// desugarer invents -- a derived `__eq_<T>`, a comprehension's `map-list`
    /// spine, a `MkTupN` pattern -- has no source position, and upstream
    /// stamps them all with one span whose file id is 0 and records nothing
    /// for them. That is fine for upstream, whose lowering rebuilds every
    /// type it needs from declarations. Ours carries the checker's answers
    /// forward BY SPAN, so two invented nodes sharing one span shared one
    /// answer, and `Red` in `__eq_Color` read back the prelude's `Tup2`.
    /// Each invented node now gets the next offset in file 0; the line stays
    /// 0, which is what `is_synthetic` reads.
    synth: std::cell::Cell<u32>,
}

fn span_of(t: &Token) -> Span {
    Span { line: t.line, col: t.col, offset: t.offset, len: t.len }
}

/// The first real token under a node -- every AST span upstream builds is
/// `token-span` of some token this node holds.
fn head_token<'n>(n: &'n Node) -> Option<&'n Token> {
    n.tokens().find(|t| !t.kind.is_trivia() && !t.kind.is_layout())
}

fn head_span(n: &Node) -> Span {
    head_token(n).map(span_of).unwrap_or_default()
}

impl<'a> Desugar<'a> {
    pub fn new(src: &'a [u8]) -> Self {
        Desugar {
            src,
            slug: String::new(),
            syms: RefCell::new(SymTab::default()),
            synth: std::cell::Cell::new(0),
        }
    }

    /// The next synthetic span: line 0, and an offset no other invented node
    /// has. Offsets start at 1 so no synthetic node is ever `self.synth()`.
    fn synth(&self) -> Span {
        let n = self.synth.get() + 1;
        self.synth.set(n);
        Span { line: 0, col: 0, offset: n, len: 0 }
    }

    fn text(&self, t: &Token) -> String {
        String::from_utf8_lossy(t.text(self.src)).into_owned()
    }

    /// `literal-value-text` (Desugarer.codex:113): a literal token's VALUE,
    /// which for two kinds is not its source spelling.
    ///
    /// **THIS IS THE ONE PLACE A LITERAL IS DECODED.** Everything downstream --
    /// the interpreter, the checker, lowering, the IR emitter, constant
    /// folding -- reads the value, so none of them owns an escape rule and no
    /// two of them can disagree about one. They did: three copies of the text
    /// decode and two of the char decode, and `interp`'s answered `t` for
    /// `\t` where upstream answers two spaces.
    ///
    /// * a TEXT literal becomes its body with escapes resolved, NO QUOTES;
    /// * a CHAR literal becomes its CHAR-CODE, in decimal, as text -- so `'a'`
    ///   arrives downstream as `"15"`;
    /// * everything else keeps the token's own text, because an integer's
    ///   `#` and `_` and a Real's digits are read by the consumer that needs
    ///   them.
    fn literal_value(&self, t: &Token) -> String {
        match t.kind {
            Kind::TextLiteral => {
                let raw = self.text(t);
                let body = raw
                    .strip_prefix('"')
                    .map_or(raw.as_str(), |s| s.strip_suffix('"').unwrap_or(s));
                crate::lexer::decode_escapes(body)
            }
            Kind::CharLiteral => {
                crate::charcode::char_literal_code(&self.text(t)).to_string()
            }
            _ => self.text(t),
        }
    }

    /// A token's text as an interned name. This is the one that runs 6.19
    /// million times over the corpus; `text` above still serves the places
    /// that want an owned string, which is literals and chapter metadata.
    /// The field named by a `.field` access or a `.field = v` assignment: the
    /// first non-trivia token AFTER the dot.
    ///
    /// **THIS WAS `.last()` OF THE NON-DOT TOKENS AND IT WAS WRONG, silently.**
    /// A newline is NOT trivia in Codex -- it is significant outside brackets,
    /// which is CDX1070's whole cause -- so a field assignment at the end of a
    /// line owned the tokens `[Dot, Identifier, Spaces, Equals, Newline,
    /// Newline]` and `.last()` took a NEWLINE as the field's name. The record
    /// then grew a second field whose name was "\n", and the real field kept
    /// its old value.
    ///
    /// Nothing caught it for a long time because almost nothing outside the
    /// compiler assigns to a field: 49 sites in the whole checkout, 47 of them
    /// in `codex/compiler`. Interpreting Cobblestone's own lexer is what found
    /// it -- `scan-ident-rest` ends by assigning `st.offset` and returning
    /// `st`, so the scanner never advanced and a two-character identifier
    /// looped forever.
    ///
    /// Taking the token after the dot is unambiguous: the parser bumps the dot
    /// and the name adjacently, and a chained access wraps each level in its
    /// own node, so there is exactly one dot per node.
    fn field_after_dot(&self, n: &Node) -> Name {
        let mut toks = n.own_tokens().skip_while(|t| t.kind != Kind::Dot);
        toks.next();
        toks.filter(|t| !t.kind.is_trivia())
            .map(|t| self.sym(t))
            .next()
            .unwrap_or_default()
    }

    fn sym(&self, t: &Token) -> Name {
        let raw = t.text(self.src);
        match std::str::from_utf8(raw) {
            Ok(s) => self.syms.borrow_mut().intern(s),
            Err(_) => self.syms.borrow_mut().intern(&String::from_utf8_lossy(raw)),
        }
    }

    /// A name the desugarer WRITES rather than reads -- `__seq`, `__rev`,
    /// `map-list`, `MkTup3`. Nobody typed these, so they are interned like any
    /// other name and cost nothing after the first.
    fn sym_str(&self, s: &str) -> Name {
        self.syms.borrow_mut().intern(s)
    }

    /// A name back as text, for the few places that carry one as metadata
    /// rather than as a name: a chapter's own title, a runtime-budget list, an
    /// error's reason.
    fn str_of(&self, n: Name) -> String {
        self.syms.borrow().text(n).to_string()
    }

    /// The first name-shaped token's text.
    fn name_of(&self, n: &Node) -> Name {
        n.tokens()
            .find(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
            .map(|t| self.sym(t))
            .unwrap_or_default()
    }

    /// The first token whatever its kind -- a record field or a constructor
    /// may be named with a keyword.
    fn leading(&self, n: &Node) -> Name {
        n.tokens().find(|t| !t.kind.is_trivia()).map(|t| self.sym(t)).unwrap_or_default()
    }

    // -- expressions ---------------------------------------------------------

    pub fn expr(&self, n: &Node) -> Expr {
        let kids = n.child_nodes();
        let sp = head_span(n);
        match n.kind {
            NodeKind::Lit => match head_token(n) {
                Some(t) => Expr::Lit(self.literal_value(t), literal_kind(t.kind), span_of(t)),
                None => Expr::Error("lit".into(), sp),
            },
            NodeKind::Name | NodeKind::Selector => Expr::NameRef(self.leading(n), sp),
            NodeKind::Paren => kids.first().map_or(Expr::Error(String::new(), sp), |k| self.expr(k)),
            NodeKind::App => match kids.as_slice() {
                [f, a] => Expr::Apply(Rc::new(self.expr(f)), Rc::new(self.expr(a)), sp),
                _ => Expr::Error("app".into(), sp),
            },
            NodeKind::Bin => self.binary(n, &kids, sp),
            NodeKind::Unary => self.unary(n, &kids, sp),
            NodeKind::IfExpr => match kids.as_slice() {
                [c, t, e] => Expr::If(
                    Rc::new(self.expr(c)),
                    Rc::new(self.expr(t)),
                    Rc::new(self.expr(e)),
                    sp,
                ),
                _ => Expr::Error("if".into(), sp),
            },
            NodeKind::LetExpr => {
                let body = kids
                    .iter()
                    .rfind(|k| k.kind != NodeKind::LetBinding)
                    .map_or(Expr::Error(String::new(), sp), |b| self.expr(b));
                let mut binds: Vec<LetBind> = Vec::new();
                let mut inner = body;
                for b in n.children_of(NodeKind::LetBinding) {
                    let value = b
                        .child_nodes()
                        .last()
                        .map_or(Expr::Error(String::new(), sp), |v| self.expr(v));
                    // `let (x, y) = p in body` is NOT a binding: upstream's
                    // `finish-let-pattern` makes it a one-armed MATCH over the
                    // value, which is the only way the pattern's variables
                    // reach the body. Reading it as a binding named after the
                    // first variable loses every other one -- `y` was
                    // undefined in all 1,226 units of the corpus, because the
                    // prelude's `snd` is written this way.
                    if let Some(pn) = b.child_nodes().into_iter().find(|k| is_pattern(k.kind)) {
                        let dp = self.pat(pn);
                        let arm = MatchArm {
                            pattern: dp,
                            body: inner,
                            guard: Expr::Lit("True".into(), LiteralKind::BoolLit, self.synth()),
                            span: head_span(pn),
                            alt_group: head_span(pn).offset,
                        };
                        inner = Expr::Match(Rc::new(value), vec![arm], sp);
                        break;
                    }
                    binds.push(LetBind {
                        name: self.name_of(b),
                        value,
                        span: head_span(b),
                    });
                }
                if binds.is_empty() {
                    inner
                } else {
                    Expr::Let(binds, Rc::new(inner), sp)
                }
            }
            NodeKind::SeqExpr => match kids.as_slice() {
                // `stmt in rest` is a let binding nobody wrote.
                [stmt, rest] => {
                    let value = self.expr(stmt);
                    let span = head_span(&kids[0]);
                    Expr::Let(
                        vec![LetBind { name: self.sym_str("__seq"), value, span }],
                        Rc::new(self.expr(rest)),
                        sp,
                    )
                }
                _ => Expr::Error("seq".into(), sp),
            },
            NodeKind::MatchExpr | NodeKind::Induction => {
                let scrut = kids
                    .first()
                    .filter(|k| k.kind != NodeKind::MatchArm)
                    .map_or(Expr::Error(String::new(), sp), |s| self.expr(s));
                let arms = self.arms(n);
                if n.kind == NodeKind::Induction {
                    Expr::Induction(Rc::new(scrut), arms, sp)
                } else {
                    Expr::Match(Rc::new(scrut), arms, sp)
                }
            }
            NodeKind::ListLit => Expr::List(kids.iter().map(|k| self.expr(k)).collect(), sp),
            NodeKind::RecordLit => Expr::Record(
                self.leading(n),
                n.children_of(NodeKind::RecordField)
                    .map(|f| FieldExpr {
                        name: self.leading(f),
                        value: f
                            .child_nodes()
                            .last()
                            .map_or(Expr::Error(String::new(), sp), |v| self.expr(v)),
                        span: head_span(f),
                    })
                    .collect(),
                sp,
            ),
            NodeKind::FieldAccess => {
                let field = self.field_after_dot(n);
                Expr::FieldAccess(
                    Rc::new(kids.first().map_or(Expr::Error(String::new(), sp), |r| self.expr(r))),
                    field,
                    sp,
                )
            }
            NodeKind::FieldAssign => {
                let field = self.field_after_dot(n);
                match kids.as_slice() {
                    [rec, val] => Expr::FieldAssign(
                        Rc::new(self.expr(rec)),
                        field,
                        Rc::new(self.expr(val)),
                        sp,
                    ),
                    _ => Expr::Error("field-assign".into(), sp),
                }
            }
            NodeKind::Tuple => {
                // `(a, b)` is `MkTup2 a b`, applied one argument at a time.
                let elems: Vec<Expr> = kids.iter().map(|k| self.expr(k)).collect();
                let base = Expr::NameRef(self.sym_str(&format!("MkTup{}", elems.len())), self.synth());
                elems.into_iter().fold(base, |f, a| Expr::Apply(Rc::new(f), Rc::new(a), sp))
            }
            NodeKind::ForExpr => {
                // `for x in xs -> b` is `map-list (\x -> b) xs`.
                //
                // **THE `map-list` NAME CARRIES THE LOOP VARIABLE'S SPAN**,
                // upstream's `token-span var-tok` (Desugarer.codex:80); the
                // lambda and both applications are synthetic. The name is
                // the one invented node here the checker can record an
                // expression type for, so it is one `expr-types` per
                // comprehension -- the whole of the 33-unit `ai-*` family
                // when this node was synthetic like the others.
                let var_tok = n
                    .own_tokens()
                    .find(|t| matches!(t.kind, Kind::Identifier | Kind::Underscore) && self.text(t) != "for");
                let var = var_tok.map(|t| self.sym(t)).unwrap_or_default();
                let var_span = var_tok.map_or_else(|| self.synth(), span_of);
                match kids.as_slice() {
                    [list, body] => {
                        let lam = Expr::Lambda(
                            vec![var],
                            Rc::new(self.expr(body)),
                            self.synth(),
                        );
                        let map_fn = Expr::NameRef(self.sym_str("map-list"), var_span);
                        Expr::Apply(
                            Rc::new(Expr::Apply(Rc::new(map_fn), Rc::new(lam), self.synth())),
                            Rc::new(self.expr(list)),
                            self.synth(),
                        )
                    }
                    _ => Expr::Error("for".into(), sp),
                }
            }
            NodeKind::Lambda => {
                let params: Vec<Name> = n
                    .own_tokens()
                    .filter(|t| matches!(t.kind, Kind::Identifier | Kind::Underscore))
                    .map(|t| self.sym(t))
                    .collect();
                Expr::Lambda(
                    params,
                    Rc::new(kids.first().map_or(Expr::Error(String::new(), sp), |b| self.expr(b))),
                    sp,
                )
            }
            NodeKind::ActBlock => Expr::Act(self.stmts(n), sp),
            NodeKind::TryExpr => {
                let count = n
                    .own_tokens()
                    .find(|t| t.kind == Kind::IntegerLiteral)
                    .and_then(|t| self.text(t).parse().ok())
                    .unwrap_or(0);
                let sect = |k: NodeKind| {
                    n.children_of(k).next().map(|s| self.stmts(s)).unwrap_or_default()
                };
                Expr::Try(Box::new(TryExpr {
                    count,
                    body: sect(NodeKind::TryBody),
                    fallback: sect(NodeKind::TryFallback),
                    failure: sect(NodeKind::TryFailure),
                    span: sp,
                }))
            }
            NodeKind::HandleExpr => {
                let eff = self.name_of(n);
                let body = kids
                    .iter()
                    .find(|k| k.kind != NodeKind::HandleClause)
                    .map_or(Expr::Error(String::new(), sp), |b| self.expr(b));
                let clauses = n
                    .children_of(NodeKind::HandleClause)
                    .map(|c| {
                        // The LAST parameter is the resume continuation.
                        let mut names: Vec<Name> = c
                            .children_of(NodeKind::ParamGroup)
                            .map(|p| self.name_of(p))
                            .collect();
                        let resume = names.pop().unwrap_or_default();
                        HandleClause {
                            op_name: self.leading(c),
                            params: names,
                            resume_name: resume,
                            body: c
                                .child_nodes()
                                .into_iter()
                                .find(|k| k.kind != NodeKind::ParamGroup)
                                .map_or(Expr::Error(String::new(), sp), |b| self.expr(b)),
                            span: head_span(c),
                        }
                    })
                    .collect();
                Expr::Handle(Box::new(HandleExpr {
                    effect: eff,
                    body: Rc::new(body),
                    clauses,
                    span: sp,
                }))
            }
            NodeKind::WithTimeout => {
                let timeout = n
                    .own_tokens()
                    .find(|t| t.kind == Kind::IntegerLiteral)
                    .map(|t| self.text(t))
                    .unwrap_or_default();
                // **THE SAME ROW READER THE TYPE PATH USES.** This arm had
                // its own, which took the identifiers alone -- so
                // `Device.Block` became two effects and every SCOPE was
                // dropped. `effect_row` already knew both, and the wire spells
                // one scope per effect whether or not the author wrote it.
                let (effects, labels, _tail) = n
                    .children_of(NodeKind::EffectRow)
                    .next()
                    .map(|r| self.effect_row(r))
                    .unwrap_or_default();
                Expr::WithTimeout(Box::new(WithTimeoutExpr {
                    timeout,
                    effects,
                    labels,
                    body: Rc::new(
                        kids.iter()
                            .find(|k| k.kind != NodeKind::EffectRow)
                            .map_or(Expr::Error(String::new(), sp), |b| self.expr(b)),
                    ),
                    span: sp,
                }))
            }
            NodeKind::LazyExpr => Expr::Lazy(
                Rc::new(kids.first().map_or(Expr::Error(String::new(), sp), |i| self.expr(i))),
                self.synth(),
            ),
            NodeKind::Revised => {
                // `e revised { f = v }` (subject 42753). The receiver is bound
                // once, EVERY field value is bound once before any of them is
                // written, and the writes are a `__record-set` spine:
                //
                //     let __rev = e in let __rv0 = v in
                //       __record-set __rev "f" __rv0
                //
                // **THE VALUES ARE HOISTED ABOVE THE WRITES** because a value
                // may read the receiver, and `__record-set` writes into a
                // shared template -- evaluating `v` after the first write
                // would read a record that had already changed.
                //
                // **DIRECT CHILDREN, NOT `descendants`.** A nested record
                // literal in a field's value has `RecordField` children of its
                // own, and a deep walk claimed them for the receiver: `o
                // revised { ob = Inner { ia = 5 } }` asked `Outer` for a field
                // `ia`. That was four of the corpus's refusals.
                let base = kids.first().map_or(Expr::Error(String::new(), sp), |b| self.expr(b));
                let fields: Vec<(Name, Expr, bool)> = n
                    .children_of(NodeKind::RecordField)
                    .map(|f| {
                        let v = f
                            .child_nodes()
                            .last()
                            .map_or(Expr::Error(String::new(), sp), |v| self.expr(v));
                        // `is-narrow-app`: a narrowing conversion is hoisted
                        // by its ARGUMENT and re-applied at the use, so the
                        // binding holds the wide value.
                        match v {
                            Expr::Apply(ref h, ref a, _)
                                if matches!(**h, Expr::NameRef(n, _) if self.str_of(n) == "__narrow") =>
                            {
                                (self.leading(f), (**a).clone(), true)
                            }
                            other => (self.leading(f), other, false),
                        }
                    })
                    .collect();
                let rv = |i: usize| self.sym_str(&format!("__rv{i}"));
                let mut chain = Expr::NameRef(self.sym_str("__rev"), self.synth());
                for (i, (fname, _, narrow)) in fields.iter().enumerate() {
                    let mut val = Expr::NameRef(rv(i), self.synth());
                    if *narrow {
                        val = Expr::Apply(
                            Rc::new(Expr::NameRef(self.sym_str("__narrow"), self.synth())),
                            Rc::new(val),
                            self.synth(),
                        );
                    }
                    let set = Expr::NameRef(self.sym_str("__record-set"), self.synth());
                    let a1 = Expr::Apply(Rc::new(set), Rc::new(chain), self.synth());
                    let lit = Expr::Lit(
                        self.str_of(*fname),
                        LiteralKind::TextLit,
                        self.synth(),
                    );
                    let a2 = Expr::Apply(Rc::new(a1), Rc::new(lit), self.synth());
                    chain = Expr::Apply(Rc::new(a2), Rc::new(val), self.synth());
                }
                // One `let` per value, innermost last, then the receiver's.
                let mut body = chain;
                for (i, (_, value, _)) in fields.into_iter().enumerate().rev() {
                    body = Expr::Let(
                        vec![LetBind { name: rv(i), value, span: self.synth() }],
                        Rc::new(body),
                        self.synth(),
                    );
                }
                Expr::Let(
                    vec![LetBind { name: self.sym_str("__rev"), value: base, span: self.synth() }],
                    Rc::new(body),
                    sp,
                )
            }
            NodeKind::ErrExpr => Expr::Error(self.str_of(self.leading(n)), sp),
            // A node we do not translate is an error we can NAME, which is
            // better than an empty body that looks understood.
            _ => Expr::Error(format!("{:?}", n.kind), sp),
        }
    }

    fn binary(&self, n: &Node, kids: &[&Node], sp: Span) -> Expr {
        // **THE OPERATOR IS NEVER A LAYOUT TOKEN.** `a\n + b` puts the
        // newline before the `+` among this node's own tokens, and picking the
        // first non-trivia one took the NEWLINE as the operator -- which
        // `binary_op` then read as `&`, because `&` was its fallback. Nine
        // definitions in `ringplug-source.codex` are written that way.
        let op_tok =
            n.own_tokens().find(|t| !t.kind.is_trivia() && !t.kind.is_layout()).copied();
        let (l, r) = match kids {
            [l, r] => (self.expr(l), self.expr(r)),
            _ => return Expr::Error("bin".into(), sp),
        };
        let Some(op) = op_tok else { return Expr::Error("bin".into(), sp) };
        let osp = span_of(&op);
        // `a |> f` is `f a`. The operands SWAP, and nothing about the token
        // says so.
        if op.kind == Kind::PipeForward {
            return Expr::Apply(Rc::new(r), Rc::new(l), osp);
        }
        let Some(bop) = binary_op(op.kind) else {
            return Expr::Error(format!("binary operator {:?}", op.kind), osp);
        };
        Expr::Binary(Rc::new(l), bop, Rc::new(r), osp)
    }

    fn unary(&self, n: &Node, kids: &[&Node], sp: Span) -> Expr {
        let op = n.own_tokens().find(|t| !t.kind.is_trivia() && !t.kind.is_layout()).copied();
        let inner = kids.first().map_or(Expr::Error(String::new(), sp), |k| self.expr(k));
        let Some(op) = op else { return inner };
        let osp = span_of(&op);
        // There is no negation node: `not x` IS `x == False`, and `AUnaryExpr`
        // is arithmetic negation alone.
        if op.kind == Kind::NotKeyword {
            return Expr::Binary(
                Rc::new(inner),
                BinaryOp::OpEq,
                Rc::new(Expr::Lit("False".into(), LiteralKind::BoolLit, osp)),
                osp,
            );
        }
        Expr::Unary(Rc::new(inner), osp)
    }

    fn stmts(&self, n: &Node) -> Vec<ActStmt> {
        n.child_nodes()
            .into_iter()
            .filter_map(|s| {
                let sp = head_span(s);
                let body = s.child_nodes();
                match s.kind {
                    NodeKind::ActBind => Some(ActStmt::Bind(
                        self.name_of(s),
                        body.first().map_or(Expr::Error(String::new(), sp), |e| self.expr(e)),
                        sp,
                    )),
                    NodeKind::ActStmt => Some(ActStmt::Exec(
                        body.first().map_or(Expr::Error(String::new(), sp), |e| self.expr(e)),
                        sp,
                    )),
                    _ => None,
                }
            })
            .collect()
    }

    /// One arm per PATTERN: upstream fans `is A | B -> body` into two arms
    /// sharing a body and relates them by `alt-group`, which is why the CST
    /// keeps the patterns together and this is where they separate.
    fn arms(&self, n: &Node) -> Vec<MatchArm> {
        let mut out = Vec::new();
        for a in n.children_of(NodeKind::MatchArm) {
            let kids = a.child_nodes();
            let pats: Vec<&Node> = kids.iter().copied().filter(|k| is_pattern(k.kind)).collect();
            let guard = a
                .children_of(NodeKind::Guard)
                .next()
                .and_then(|g| g.child_nodes().first().map(|e| self.expr(e)))
                .unwrap_or_else(|| {
                    Expr::Lit("True".into(), LiteralKind::BoolLit, self.synth())
                });
            let body = kids
                .iter()
                .rfind(|k| !is_pattern(k.kind) && k.kind != NodeKind::Guard)
                .map_or(Expr::Error(String::new(), head_span(a)), |b| self.expr(b));
            let group = pats.first().map(|p| head_span(p).offset).unwrap_or(0);
            for p in pats {
                let dp = self.pat(p);
                out.push(MatchArm {
                    pattern: dp,
                    body: body.clone(),
                    guard: guard.clone(),
                    span: head_span(p),
                    alt_group: group,
                });
            }
        }
        out
    }

    // -- the chapter ---------------------------------------------------------

    /// `desugar-document`, as far as the pieces that need no scope.
    ///
    /// The synthesis steps upstream runs after the plain translation --
    /// `synth-family-member-defs`, `synth-conversion-defs`,
    /// `synth-derived-defs`, `synth-instance-defs`, `rewrite-constrained-defs`,
    /// `insert-dicts-at-call-sites` -- are NOT here yet, and the def count says
    /// so rather than the tree pretending they ran.
    pub fn chapter(&mut self, tree: &Node) -> Chapter {
        let mut ch = Chapter::default();
        // The unit's own chapter is the last one; a definition's slug is the
        // chapter it was WRITTEN in, so the walk tracks it.
        let mut slug = String::new();
        for child in tree.child_nodes() {
            match child.kind {
                NodeKind::ChapterHeader => {
                    slug = crate::preamble::header_text(child, self.src);
                    ch.name = self.sym_str(&slug);
                    ch.chapter_title = slug.clone();
                }
                NodeKind::SectionHeader => {
                    ch.section_titles.push(crate::preamble::header_text(child, self.src));
                }
                NodeKind::Def => {
                    self.slug = slug.clone();
                    ch.defs.push(self.def(child));
                }
                NodeKind::TypeDef => {
                    if let Some(td) = self.type_def(child) {
                        ch.type_defs.push(td);
                    }
                }
                NodeKind::EffectDef => ch.effect_defs.push(EffectDef {
                    name: self.name_of(child),
                    ops: self.ops(child),
                    span: head_span(child),
                }),
                NodeKind::ClassDef => ch.class_defs.push(ClassDef {
                    name: self.name_of(child),
                    methods: self.ops(child),
                    superclass: child
                        .children_of(NodeKind::Superclass)
                        .next()
                        .map(|s| self.leading(s)),
                    span: head_span(child),
                }),
                NodeKind::InstanceDef => ch.instance_defs.push(self.instance_def(child)),
                NodeKind::Cites => ch.citations.push(CitesDecl {
                    quire: self.name_of(child),
                    chapter_name: Name::default(),
                    selected_names: Vec::new(),
                    citing_chapter: slug.clone(),
                    span: head_span(child),
                }),
                NodeKind::Grounds => {
                    for name in ground_names(child, self.src) {
                        ch.ground_effects.push(format!("{slug}\n{name}"));
                    }
                }
                _ => {}
            }
        }
        for d in tree.descendants(NodeKind::Def) {
            if d.children_of(NodeKind::Punctual).next().is_some() {
                ch.rt_names.push(self.str_of(self.def_name(d)));
            }
        }
        // **THE DESUGARER SYNTHESISES DEFINITIONS, AND THEY GO LAST.**
        // `desugar-document` (Ast/Desugarer.codex:610) appends family-member,
        // conversion and DERIVED defs after the chapter's own, in type-
        // declaration order.
        // **FAMILY MEMBERS COME BEFORE THE DERIVED DEFINITIONS.**
        // `desugar-document` appends family-member, conversion and derived
        // defs in that order, and registration order is what `next-id` counts.
        self.synth_family_defs(tree, &mut ch);
        self.synth_derived_defs(&mut ch);
        // The dictionary TYPE before the definitions that build one, and both
        // after the derived defs -- `desugar-document`'s order (subject 43290).
        self.synth_class_type_defs(&mut ch);
        self.synth_instance_defs(&mut ch);
        for e in crate::builtins::BUILTIN_EFFECT_NAMES.iter().chain(crate::builtins::BUILTIN_TYPE_NAMES.iter()) {
            self.sym_str(e);
        }
        ch.syms = std::mem::take(&mut *self.syms.borrow_mut());
        // The chapter scoper runs on the whole unit, before the proof plan
        // reads definitions by name.
        crate::scoper::apply(&mut ch);
        ch.proof_plan = crate::proof_norm::prepare(&mut ch);
        ch
    }

    /// `synth-derived-defs`: one `__eq_<T>` per variant that is EQ-SAFE.
    ///
    /// **EVERY SUM GETS STRUCTURAL EQUALITY WHETHER IT ASKS OR NOT**, unless a
    /// constructor field names `Real`. `push-derived-for-type` fires on
    /// `deriving-has "Eq" | td-eq-safe td`, and `td-eq-safe` is exactly "a
    /// variant body, and no constructor field names Real" -- float equality is
    /// excluded because NaN is not equal to itself, so a generated structural
    /// comparison would be quietly wrong.
    ///
    /// It is a REAL definition, two parameters and a nested `when`, so it
    /// registers, checks and can be lowered like any other; a chapter missing
    /// it reports a smaller `next-id` than upstream for the same source and
    /// can emit a `(defs ...)` short of a definition.
    ///
    /// The guard was `td-self-recursive` through U55 and widened to
    /// `td-eq-safe` at U56, which is why every corpus unit went from agreeing
    /// on the counters to diverging by about 64 substitutions at once.
    ///
    /// STILL MISSING: the `deriving Eq` half of the guard. Our parser does not
    /// capture the clause, so a type that carries a `Real` AND asks for Eq
    /// gets one upstream and none here.
    ///
    /// `deriving Show` and `deriving Ord` synthesise two more. Those are NOT
    /// here: our parser does not capture the `deriving` clause at all, so they
    /// need a parser change first. Fifteen files in the depot carry one.
    /// `instance <Class> <Type> where <methods>`. The parser bumps the class
    /// and the type straight into the node, so they are the first two
    /// significant tokens; everything after is `where` and the methods.
    fn instance_def(&self, n: &Node) -> InstanceDef {
        let sig: Vec<&Token> = n
            .own_tokens()
            .filter(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
            .collect();
        let class_name = sig.first().map(|t| self.sym(t)).unwrap_or_default();
        // `instance-head-key` (subject 43?): a bare name is itself, and an
        // applied head is `List[Integer]`. It is a KEY, not a type -- it names
        // the synthesised definitions and nothing reads it as a type.
        let head: Vec<String> =
            sig.iter().skip(1).map(|t| self.text(t).to_string()).collect();
        let key = match head.len() {
            0 => String::new(),
            1 => head[0].clone(),
            _ => format!("{}[{}]", head[0], head[1..].join(",")),
        };
        InstanceDef {
            class_name,
            type_name: self.sym_str(&key),
            methods: n
                .children_of(NodeKind::InstanceMethod)
                .map(|m| InstanceMethodDef {
                    name: self.leading(m),
                    // `name_of`, as a definition's parameters are: the
                    // LEADING token of `(x)` is the paren.
                    params: m
                        .children_of(NodeKind::ParamGroup)
                        .map(|g| self.name_of(g))
                        .collect(),
                    body: m
                        .child_nodes()
                        .iter()
                        .rev()
                        .find(|k| k.kind != NodeKind::ParamGroup)
                        .map_or(Expr::Error(String::new(), self.synth()), |b| self.expr(b)),
                    span: head_span(m),
                })
                .collect(),
            span: head_span(n),
        }
    }

    /// `synth-class-type-defs` (subject 43678). **A CLASS IS A RECORD TYPE**:
    /// `class C where m : T` declares `CDict (a) = record { m-impl : T }`, and
    /// a superclass adds a `__super-<S> : <S>Dict` field in FRONT of the
    /// methods. The single type parameter is always named `a`.
    ///
    /// It costs one fresh variable per class, because a record with one type
    /// parameter parameterises to one -- which is the whole of the `class`
    /// line's divergence.
    fn synth_class_type_defs(&self, ch: &mut Chapter) {
        let mut out = Vec::new();
        for cd in &ch.class_defs {
            let dict = self.sym_str(&format!("{}Dict", self.syms.borrow().text(cd.name)));
            let mut fields: Vec<RecordFieldDef> = Vec::new();
            if let Some(sup) = cd.superclass {
                let sup_text = self.syms.borrow().text(sup).to_string();
                fields.push(RecordFieldDef {
                    name: self.sym_str(&format!("__super-{sup_text}")),
                    type_expr: TypeExpr::Named(self.sym_str(&format!("{sup_text}Dict")), self.synth()),
                    span: self.synth(),
                });
            }
            for m in &cd.methods {
                let mname = self.syms.borrow().text(m.name).to_string();
                fields.push(RecordFieldDef {
                    name: self.sym_str(&format!("{mname}-impl")),
                    type_expr: m.type_expr.clone(),
                    span: self.synth(),
                });
            }
            out.push(TypeDef::Record(dict, vec![self.sym_str("a")], fields, false, self.synth()));
        }
        ch.type_defs.extend(out);
    }

    /// `synth-instance-defs` (subject 44113). One `instance` is up to three
    /// kinds of definition:
    ///
    /// ```text
    /// C-dict-Integer = CDict { m-impl = \x -> <body> }   the dictionary
    /// m-Integer (x) = <body>                             the specialisation
    /// m (x) = <body>                                     only when the class
    ///                                                    has ONE instance
    /// ```
    ///
    /// The bare method exists only for a single-instance class because with
    /// two instances the name is ambiguous and the call site takes a
    /// dictionary instead. **A METHOD WITH NO PARAMETERS IS NOT WRAPPED IN A
    /// LAMBDA** in the dictionary field; one with parameters is.
    fn synth_instance_defs(&self, ch: &mut Chapter) {
        let mut out = Vec::new();
        for id in &ch.instance_defs {
            let class_text = self.syms.borrow().text(id.class_name).to_string();
            let key = self.syms.borrow().text(id.type_name).to_string();
            let instances = ch
                .instance_defs
                .iter()
                .filter(|o| o.class_name == id.class_name)
                .count();
            let superclass = ch
                .class_defs
                .iter()
                .find(|c| c.name == id.class_name)
                .and_then(|c| c.superclass);

            let mut fields: Vec<FieldExpr> = Vec::new();
            if let Some(sup) = superclass {
                let sup_text = self.syms.borrow().text(sup).to_string();
                fields.push(FieldExpr {
                    name: self.sym_str(&format!("__super-{sup_text}")),
                    value: Expr::NameRef(self.sym_str(&format!("{sup_text}-dict-{key}")), self.synth()),
                    span: self.synth(),
                });
            }
            for m in &id.methods {
                let mname = self.syms.borrow().text(m.name).to_string();
                let value = if m.params.is_empty() {
                    m.body.clone()
                } else {
                    Expr::Lambda(m.params.clone(), Rc::new(m.body.clone()), self.synth())
                };
                fields.push(FieldExpr {
                    name: self.sym_str(&format!("{mname}-impl")),
                    value,
                    span: self.synth(),
                });
            }
            let mk = |name: Name, params: Vec<Name>, body: Expr| Def {
                name,
                params: params.into_iter().map(|n| Param { name: n, span: self.synth() }).collect(),
                declared_type: Vec::new(),
                body,
                chapter_slug: String::new(),
                span: self.synth(),
                is_claim: false,
                is_punctual: false,
                wcet_budget: 0,
            };
            out.push(mk(
                self.sym_str(&format!("{class_text}-dict-{key}")),
                Vec::new(),
                Expr::Record(self.sym_str(&format!("{class_text}Dict")), fields, self.synth()),
            ));
            for m in &id.methods {
                let mname = self.syms.borrow().text(m.name).to_string();
                out.push(mk(
                    self.sym_str(&format!("{mname}-{key}")),
                    m.params.clone(),
                    m.body.clone(),
                ));
            }
            if instances == 1 {
                for m in &id.methods {
                    out.push(mk(m.name, m.params.clone(), m.body.clone()));
                }
            }
        }
        ch.defs.extend(out);
    }

    /// `synth-family-members` (subject 43215). **A `unit family` IS TWO
    /// DEFINITIONS PER MEMBER**, and we wrote none of them:
    ///
    /// ```text
    /// Duration = unit family Nanosecond
    ///   Microsecond = 1000
    ///
    /// Microsecond : Integer -> Duration
    /// Microsecond (__fv) = Duration (__fv * 1000)
    /// Duration-to-Microsecond : Duration -> Integer
    /// Duration-to-Microsecond (__fv) = __fv / 1000
    /// ```
    ///
    /// A factor of 1 is the base member and drops the arithmetic on both
    /// sides. Every span is synthetic, so none of these names reaches
    /// `expr-types` -- which is exactly why `expr-types` already agreed with
    /// the oracle on programs whose `next-id` did not.
    fn synth_family_defs(&self, tree: &Node, ch: &mut Chapter) {
        let int = |me: &Self| TypeExpr::Named(me.sym_str("Integer"), self.synth());
        let mut out = Vec::new();
        for td in tree.descendants(NodeKind::TypeDef) {
            let Some(fam) = td.children_of(NodeKind::UnitFamilyBody).next() else { continue };
            let family = self.leading(td);
            let fam_text = self.syms.borrow().text(family).to_string();
            let fam_ty = TypeExpr::Named(family, self.synth());
            for m in fam.children_of(NodeKind::UnitFamilyMember) {
                // **THE CST IS LOSSLESS, SO THE FIRST TOKEN IS USUALLY
                // WHITESPACE.** Taking it named every member `"    "`, which
                // the counters could not see: the synthesised definitions are
                // unreachable in most units and get pruned before emission, so
                // only their MINTS showed, and those were right.
                let Some(name_tok) = m.own_tokens().find(|t| t.kind == Kind::TypeIdentifier)
                else { continue };
                let member = self.sym(name_tok);
                let factor: i64 = m
                    .own_tokens()
                    .find(|t| t.kind == Kind::IntegerLiteral)
                    .and_then(|t| self.text(t).parse().ok())
                    .unwrap_or(1);
                let fv = self.sym_str("__fv");
                let param = || vec![Param { name: fv, span: self.synth() }];
                let var = || Expr::NameRef(fv, self.synth());
                let lit = || Expr::Lit(factor.to_string(), LiteralKind::IntLit, self.synth());

                // `synth-family-ctor`: Integer in, the family out.
                let scaled = if factor == 1 {
                    var()
                } else {
                    Expr::Binary(Rc::new(var()), BinaryOp::OpMul, Rc::new(lit()), self.synth())
                };
                out.push(Def {
                    name: member,
                    params: param(),
                    declared_type: vec![TypeExpr::Fun(Rc::new(int(self)), Rc::new(fam_ty.clone()), self.synth())],
                    body: Expr::Apply(
                        Rc::new(Expr::NameRef(family, self.synth())),
                        Rc::new(scaled),
                        self.synth(),
                    ),
                    chapter_slug: String::new(),
                    span: self.synth(),
                    is_claim: false,
                    is_punctual: false,
                    wcet_budget: 0,
                });

                // `synth-family-extract`: the family in, Integer out.
                let member_text = self.syms.borrow().text(member).to_string();
                let extract = self.sym_str(&format!("{fam_text}-to-{member_text}"));
                let divided = if factor == 1 {
                    var()
                } else {
                    Expr::Binary(Rc::new(var()), BinaryOp::OpDiv, Rc::new(lit()), self.synth())
                };
                out.push(Def {
                    name: extract,
                    params: param(),
                    declared_type: vec![TypeExpr::Fun(Rc::new(fam_ty.clone()), Rc::new(int(self)), self.synth())],
                    body: divided,
                    chapter_slug: String::new(),
                    span: self.synth(),
                    is_claim: false,
                    is_punctual: false,
                    wcet_budget: 0,
                });
            }
        }
        ch.defs.extend(out);
    }

    fn synth_derived_defs(&self, ch: &mut Chapter) {
        let mut out = Vec::new();
        // `find`, not `intern`: upstream compares the field type's TEXT to
        // "Real", so asking the question must not add a symbol that the
        // chapter never mentioned. A chapter with no `Real` anywhere cannot
        // have a field naming one, so the absent symbol answers eq-safe.
        let real = self.syms.borrow().find("Real");
        for td in &ch.type_defs {
            let TypeDef::Variant(name, _, ctors, _) = td else { continue };
            let eq_safe = match real {
                None => true,
                Some(r) => !ctors
                    .iter()
                    .any(|c| c.fields.iter().any(|f| type_names(f, r))),
            };
            if eq_safe {
                out.push(self.eq_def(*name, ctors));
            }
        }
        ch.defs.extend(out);
    }

    /// `gen-eq-def`: `__eq_T (__ex) (__ey)` is a `when` over `__ex` whose every
    /// arm is a `when` over `__ey` -- the same constructor, comparing fields
    /// pairwise, or a wildcard answering False.
    ///
    /// EVERY SPAN HERE IS SYNTHETIC, which is load-bearing: `record-expr-type`
    /// skips a synthetic span, so none of these names reaches `expr-types`.
    /// That is why `expr-types` already matched on units whose `next-id` did
    /// not -- the missing definitions mint variables and record nothing.
    fn eq_def(&self, tname: Name, ctors: &[VariantCtorDef]) -> Def {
        // **THE LIVE TABLE, NOT THE CHAPTER'S.** `ch.syms` is filled by the
        // `take` on the line after this runs, so reading a name out of it here
        // answers `<not this table>` -- which is what every derived definition
        // was called, and would have collided them all onto one name.
        let eq_name = format!("__eq_{}", self.syms.borrow().text(tname));
        let (xn, yn) = (self.sym_str("__ex"), self.sym_str("__ey"));
        let tref = TypeExpr::Named(tname, self.synth());
        let boolean = TypeExpr::Named(self.sym_str("Boolean"), self.synth());
        let arms = ctors
            .iter()
            .map(|c| {
                let n = c.fields.len();
                let xv: Vec<Name> = (0..n).map(|i| self.sym_str(&format!("__exf{i}"))).collect();
                let yv: Vec<Name> = (0..n).map(|i| self.sym_str(&format!("__eyf{i}"))).collect();
                let pats = |vs: &[Name]| vs.iter().map(|v| Pat::Var(*v, self.synth())).collect::<Vec<_>>();
                // Field equality, folded left with `&`; no fields is `True`.
                let body = xv.iter().zip(&yv).fold(None::<Expr>, |acc, (x, y)| {
                    let one = Expr::Binary(
                        Rc::new(Expr::NameRef(*x, self.synth())),
                        BinaryOp::OpEq,
                        Rc::new(Expr::NameRef(*y, self.synth())),
                        self.synth(),
                    );
                    Some(match acc {
                        None => one,
                        Some(a) => Expr::Binary(Rc::new(a), BinaryOp::OpAnd, Rc::new(one), self.synth()),
                    })
                })
                .unwrap_or_else(|| Expr::Lit("True".into(), LiteralKind::BoolLit, self.synth()));
                let yes = MatchArm {
                    pattern: Pat::Ctor(c.name, pats(&yv), self.synth()),
                    body,
                    guard: Expr::Lit("True".into(), LiteralKind::BoolLit, self.synth()),
                    span: self.synth(),
                    alt_group: NO_ALT_GROUP,
                };
                let no = MatchArm {
                    pattern: Pat::Wild(self.synth()),
                    body: Expr::Lit("False".into(), LiteralKind::BoolLit, self.synth()),
                    guard: Expr::Lit("True".into(), LiteralKind::BoolLit, self.synth()),
                    span: self.synth(),
                    alt_group: NO_ALT_GROUP,
                };
                MatchArm {
                    pattern: Pat::Ctor(c.name, pats(&xv), self.synth()),
                    body: Expr::Match(Rc::new(Expr::NameRef(yn, self.synth())), vec![yes, no], self.synth()),
                    guard: Expr::Lit("True".into(), LiteralKind::BoolLit, self.synth()),
                    span: self.synth(),
                    alt_group: NO_ALT_GROUP,
                }
            })
            .collect();
        Def {
            name: self.sym_str(&eq_name),
            params: vec![Param { name: xn, span: self.synth() }, Param { name: yn, span: self.synth() }],
            declared_type: vec![TypeExpr::Fun(
                Rc::new(tref.clone()),
                Rc::new(TypeExpr::Fun(Rc::new(tref), Rc::new(boolean), self.synth())),
                self.synth(),
            )],
            body: Expr::Match(Rc::new(Expr::NameRef(xn, self.synth())), arms, self.synth()),
            chapter_slug: String::new(),
            span: self.synth(),
            is_claim: false,
            is_punctual: false,
            wcet_budget: 0,
        }
    }

    fn def_name(&self, d: &Node) -> Name {
        d.children_of(NodeKind::DefEquation)
            .next()
            .map(|e| self.name_of(e))
            .filter(|n| *n != Name::default())
            .or_else(|| d.children_of(NodeKind::TypeAnnotation).next().map(|a| self.name_of(a)))
            .unwrap_or_default()
    }

    fn def(&self, d: &Node) -> Def {
        // Upstream's span is `token-span (d.name)`, and the name comes from
        // the EQUATION line when there is one -- which is why a constant's
        // position is its annotation's and everything else's is its equation's.
        let eq = d.children_of(NodeKind::DefEquation).next();
        let name_tok = eq
            .and_then(|e| e.tokens().find(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier)))
            .or_else(|| {
                d.children_of(NodeKind::TypeAnnotation)
                    .next()
                    .and_then(|a| a.tokens().find(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier)))
            })
            .copied();
        let params = eq
            .map(|e| {
                e.children_of(NodeKind::ParamGroup)
                    .map(|p| Param { name: self.name_of(p), span: head_span(p) })
                    .collect()
            })
            .unwrap_or_default();
        let declared_type = d
            .children_of(NodeKind::TypeAnnotation)
            .next()
            .and_then(|a| a.child_nodes().first().and_then(|te| te.child_nodes().first().map(|t| self.type_expr(t))))
            .into_iter()
            .collect();
        let body = d
            .child_nodes()
            .into_iter()
            .find(|k| {
                !matches!(
                    k.kind,
                    NodeKind::TypeAnnotation
                        | NodeKind::DefEquation
                        | NodeKind::Punctual
                        | NodeKind::Bounded
                        | NodeKind::Claim
                        | NodeKind::Qed
                        | NodeKind::ProseBlock
                        | NodeKind::Loose
                )
            })
            .map(|b| self.expr(b))
            .unwrap_or_else(|| Expr::Error("no body".into(), self.synth()));
        let punct = d.children_of(NodeKind::Punctual).next();
        Def {
            name: name_tok.map(|t| self.sym(&t)).unwrap_or_default(),
            params,
            declared_type,
            body,
            chapter_slug: self.slug.clone(),
            span: name_tok.map(|t| span_of(&t)).unwrap_or_default(),
            // The `claim` is parked INSIDE the definition that proves it, which
            // is what makes the association structural rather than "the next
            // sibling". That is also what makes it readable here.
            is_claim: d.child_nodes().iter().any(|k| k.kind == NodeKind::Claim),
            is_punctual: punct.is_some(),
            // The budget is the literal the author wrote after the keyword,
            // and it is OPTIONAL: `punctual f` declares the discipline without
            // a number.
            wcet_budget: punct
                .and_then(|p| p.tokens().find(|t| t.kind == Kind::IntegerLiteral))
                .and_then(|t| self.text(t).parse().ok())
                .unwrap_or(0),
        }
    }

    fn ops(&self, n: &Node) -> Vec<EffectOpDef> {
        n.children_of(NodeKind::EffectOp)
            .map(|o| EffectOpDef {
                name: self.leading(o),
                type_expr: o
                    .child_nodes()
                    .first()
                    .map(|t| self.type_expr(t))
                    .unwrap_or(TypeExpr::Named(Name::default(), self.synth())),
                span: head_span(o),
            })
            .collect()
    }

    fn type_def(&self, td: &Node) -> Option<TypeDef> {
        let name = self.name_of(td);
        let sp = head_span(td);
        let tps: Vec<Name> = td
            .children_of(NodeKind::TypeParams)
            .flat_map(|p| p.tokens())
            .filter(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
            .map(|t| self.sym(t))
            .collect();
        if let Some(rec) = td.children_of(NodeKind::RecordBody).next() {
            let mutable = td.tokens().any(|t| t.kind == Kind::MutableKeyword);
            let fields = rec
                .children_of(NodeKind::RecordFieldDef)
                .map(|f| RecordFieldDef {
                    name: self.leading(f),
                    type_expr: f
                        .child_nodes()
                        .first()
                        .map(|t| self.type_expr(t))
                        .unwrap_or(TypeExpr::Named(Name::default(), self.synth())),
                    span: head_span(f),
                })
                .collect();
            return Some(TypeDef::Record(name, tps, fields, mutable, sp));
        }
        if let Some(var) = td.children_of(NodeKind::VariantBody).next() {
            let ctors = var
                .children_of(NodeKind::VariantCtor)
                .map(|c| VariantCtorDef {
                    name: self.leading(c),
                    fields: c
                        .children_of(NodeKind::CtorField)
                        .filter_map(|f| f.child_nodes().first().map(|t| self.type_expr(t)))
                        .collect(),
                    return_type: c
                        .children_of(NodeKind::CtorReturn)
                        .filter_map(|r| r.child_nodes().first().map(|t| self.type_expr(t)))
                        .collect(),
                    span: head_span(c),
                })
                .collect();
            return Some(TypeDef::Variant(name, tps, ctors, sp));
        }
        if let Some(u) = td.children_of(NodeKind::UnitBody).next() {
            let base = u
                .child_nodes()
                .first()
                .map(|t| self.type_expr(t))
                .unwrap_or(TypeExpr::Named(self.sym_str("Integer"), sp));
            return Some(TypeDef::Unit(name, base, sp));
        }
        if td.children_of(NodeKind::UnitFamilyBody).next().is_some() {
            return Some(TypeDef::Unit(name, TypeExpr::Named(self.sym_str("Integer"), sp), sp));
        }
        None
    }

    // -- type expressions ----------------------------------------------------

    pub fn type_expr(&self, n: &Node) -> TypeExpr {
        let kids = n.child_nodes();
        let sp = head_span(n);
        let first = |i: usize| {
            kids.get(i)
                .map(|k| self.type_expr(k))
                .unwrap_or(TypeExpr::Named(Name::default(), sp))
        };
        match n.kind {
            NodeKind::NamedType => TypeExpr::Named(
                self.sym_str(
                    &n.tokens()
                        .filter(|t| !t.kind.is_trivia())
                        .map(|t| self.text(t))
                        .collect::<Vec<_>>()
                        .concat(),
                ),
                sp,
            ),
            NodeKind::ParenType => first(0),
            NodeKind::FunType => TypeExpr::Fun(Rc::new(first(0)), Rc::new(first(1)), sp),
            NodeKind::AppType => match kids.split_first() {
                Some((base, args)) => args.iter().fold(self.type_expr(base), |acc, a| {
                    TypeExpr::App(Rc::new(acc), vec![self.type_expr(a)], sp)
                }),
                None => TypeExpr::Named(Name::default(), sp),
            },
            NodeKind::ArithType => {
                let op = n
                    .own_tokens()
                    .find(|t| !t.kind.is_trivia())
                    .map(|t| self.sym(t))
                    .unwrap_or_default();
                TypeExpr::App(
                    Rc::new(TypeExpr::Named(op, sp)),
                    kids.iter().map(|k| self.type_expr(k)).collect(),
                    sp,
                )
            }
            NodeKind::BoundedIntType => {
                let toks: Vec<_> = n.tokens().filter(|t| !t.kind.is_trivia()).collect();
                let mut nums = Vec::new();
                for (i, t) in toks.iter().enumerate() {
                    if t.kind == Kind::IntegerLiteral {
                        let neg = i > 0 && toks[i - 1].kind == Kind::Minus;
                        // **`parse()` CANNOT READ THE LOWER BOUND.**
                        // `Integer between -9223372036854775808 and ...` is
                        // written as a minus and a literal, and
                        // `9223372036854775807 + 1` is not an `i64`, so
                        // `parse::<i64>()` failed and `unwrap_or(0)` made the
                        // bound zero -- 20 definitions of the compiler said
                        // `(int 0 ...)` where every gold says `(int i64-min
                        // ...)`. `lit-text-to-integer` accumulates `acc * 10 +
                        // d` in wrapping arithmetic, which lands exactly on
                        // `i64::MIN`, and negating that wraps back to itself.
                        let v = crate::token::lit_text_to_integer(&self.text(t));
                        nums.push(if neg { v.wrapping_neg() } else { v });
                    }
                }
                let mode = n
                    .tokens()
                    .find_map(|t| match t.text(self.src) {
                        b"wrapping" => Some(OverflowMode::Wrapping),
                        b"clamping" => Some(OverflowMode::Clamping),
                        _ => None,
                    })
                    .unwrap_or(OverflowMode::Error);
                TypeExpr::BoundedInt(
                    Rc::new(first(0)),
                    nums.first().copied().unwrap_or(0),
                    nums.get(1).copied().unwrap_or(0),
                    mode,
                    sp,
                )
            }
            NodeKind::LinearType => TypeExpr::Linear(Rc::new(first(0)), sp),
            NodeKind::PropEqType => TypeExpr::PropEq(Rc::new(first(0)), Rc::new(first(1)), sp),
            NodeKind::ConstrainedType => first(kids.len().saturating_sub(1)),
            // `for all (xs : T), P` -- the variable is the name after the
            // paren. Taking the first name under the node returns `for`,
            // which is an ordinary identifier the lexer knows nothing about.
            NodeKind::ForAllType => {
                let var = n
                    .own_tokens()
                    .skip_while(|t| t.kind != Kind::LeftParen)
                    .find(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
                    .map(|t| self.sym(t))
                    .unwrap_or_default();
                TypeExpr::Forall(var, Rc::new(first(0)), Rc::new(first(1)), sp)
            }
            // **A DOTTED EFFECT IS ONE NAME AND A SCOPE BELONGS TO THE EFFECT
            // IT FOLLOWS.** `[Console "stdout", FileSystem.Read "/config/"]` is
            // two effects, `Console` and `FileSystem.Read`, with a scope each.
            // Taking the identifiers alone made `Device.Block` two effects and
            // dropped every scope in the depot; the scopes must also be
            // POSITIONAL, because a scope in the middle of a row cannot be
            // recovered by padding the end.
            NodeKind::EffectType => {
                let (effs, scopes, tail) = self.effect_row(n);
                TypeExpr::Effect(effs, scopes, tail, Rc::new(first(0)), sp)
            }
            NodeKind::TupleType => {
                let elems: Vec<TypeExpr> = kids.iter().map(|k| self.type_expr(k)).collect();
                let base = TypeExpr::Named(self.sym_str(&format!("Tup{}", elems.len())), sp);
                elems.into_iter().fold(base, |f, a| TypeExpr::App(Rc::new(f), vec![a], sp))
            }
            _ => TypeExpr::Named(Name::default(), sp),
        }
    }

    /// `[Console "stdout", FileSystem.Read "/config/", e]` as its effect names,
    /// their scopes, and the ROW TAIL.
    ///
    /// **A LOWERCASE IDENTIFIER IN AN EFFECT ROW IS THE TAIL, NOT AN EFFECT.**
    /// `parse-row-tail` (Syntax/Parser.codex) accepts at most one, refuses a
    /// dot on it (`cdx-row-tail-decorated`) and refuses a second
    /// (`cdx-row-two-tails`); an effect NAME is a TypeIdentifier, may be dotted
    /// and may carry a scope literal. The token kind is the whole distinction.
    ///
    /// It is what makes `[e]` a row VARIABLE, which `parameterize-type` mints
    /// an id for and every reference instantiates. Treated as an effect name it
    /// is an undefined effect that costs nothing and spells nothing.
    ///
    /// Assembled from the TOKENS rather than read off child nodes: an effect
    /// row is not a type, so the parser leaves it flat and a dotted name
    /// arrives as three tokens.
    fn effect_row(&self, n: &Node) -> (Vec<Name>, Vec<String>, Vec<Name>) {
        let (mut effs, mut scopes, mut tail) = (Vec::new(), Vec::new(), Vec::new());
        let mut name = String::new();
        let mut scope = String::new();
        let mut is_tail = false;
        let mut flush = |name: &mut String, scope: &mut String, is_tail: &mut bool| {
            if name.is_empty() {
                return;
            }
            if *is_tail {
                tail.push(std::mem::take(name));
                scope.clear();
            } else {
                effs.push(std::mem::take(name));
                scopes.push(std::mem::take(scope));
            }
            *is_tail = false;
        };
        for t in n.own_tokens().filter(|t| !t.kind.is_trivia()) {
            match t.kind {
                Kind::LeftBracket | Kind::RightBracket => {}
                Kind::Comma => flush(&mut name, &mut scope, &mut is_tail),
                // The scope is a text literal, and what the wire carries is
                // its VALUE -- the quotes are syntax.
                Kind::TextLiteral => {
                    let raw = String::from_utf8_lossy(t.text(self.src)).to_string();
                    scope = raw.trim_matches('"').to_string();
                }
                _ => {
                    if name.is_empty() && t.kind == Kind::Identifier {
                        is_tail = true;
                    }
                    name.push_str(&String::from_utf8_lossy(t.text(self.src)));
                }
            }
        }
        flush(&mut name, &mut scope, &mut is_tail);
        (
            effs.iter().map(|e| self.sym_str(e)).collect(),
            scopes,
            tail.iter().map(|e| self.sym_str(e)).collect(),
        )
    }

    // -- patterns ------------------------------------------------------------

    pub fn pat(&self, n: &Node) -> Pat {
        let sp = head_span(n);
        match n.kind {
            NodeKind::VarPat => Pat::Var(self.leading(n), sp),
            NodeKind::LitPat => match head_token(n) {
                Some(t) => Pat::Lit(self.literal_value(t), literal_kind(t.kind), sp),
                None => Pat::Wild(sp),
            },
            NodeKind::CtorPat => Pat::Ctor(
                self.leading(n),
                n.child_nodes().into_iter().map(|k| self.pat(k)).collect(),
                sp,
            ),
            NodeKind::ParenPat => {
                n.child_nodes().first().map_or(Pat::Wild(sp), |k| self.pat(k))
            }
            // A tuple pattern is the tuple constructor's pattern.
            NodeKind::TuplePat => {
                let subs: Vec<Pat> = n.child_nodes().into_iter().map(|k| self.pat(k)).collect();
                Pat::Ctor(self.sym_str(&format!("MkTup{}", subs.len())), subs, sp)
            }
            NodeKind::VecPat => {
                Pat::Vec_(n.child_nodes().into_iter().map(|k| self.pat(k)).collect(), sp)
            }
            _ => Pat::Wild(sp),
        }
    }
}

/// **NOT FANNED OUT OF A `|`-GROUP.** Upstream writes `-1`; our `alt_group` is
/// the source OFFSET of the pattern it came from and so cannot hold one. A
/// synthetic arm has no offset to give, and every synthetic arm sharing 0 would
/// claim they were all alternatives of one pattern. Nothing reads the field
/// today -- when something does, this is the value it has to know about.
const NO_ALT_GROUP: u32 = u32::MAX;

/// Does this type expression NAME the given type? `td-self-recursive` asks it
/// of every constructor field, and `List (N a)` counts as much as a bare `N`.
fn type_names(t: &TypeExpr, n: Name) -> bool {
    match t {
        TypeExpr::Named(m, _) => *m == n,
        TypeExpr::Fun(a, b, _) => type_names(a, n) || type_names(b, n),
        TypeExpr::App(h, args, _) => {
            type_names(h, n) || args.iter().any(|a| type_names(a, n))
        }
        TypeExpr::Effect(_, _, _, r, _) => type_names(r, n),
        TypeExpr::Linear(i, _) | TypeExpr::BoundedInt(i, ..) => type_names(i, n),
        TypeExpr::PropEq(a, b, _) => type_names(a, n) || type_names(b, n),
        TypeExpr::Constrained(_, _, i, _) => type_names(i, n),
        TypeExpr::Forall(_, a, b, _) => type_names(a, n) || type_names(b, n),
    }
}

/// The effect names a `grounds` declaration lists, with a dotted effect
/// joined back into one name.
fn ground_names(n: &Node, src: &[u8]) -> Vec<String> {
    let mut out = Vec::new();
    let mut name = String::new();
    for t in n.tokens().filter(|t| !t.kind.is_trivia()) {
        match t.kind {
            Kind::GroundsKeyword | Kind::Newline | Kind::EndOfFile => {}
            Kind::Comma => {
                if !name.is_empty() {
                    out.push(std::mem::take(&mut name));
                }
            }
            _ => name.push_str(&String::from_utf8_lossy(t.text(src))),
        }
    }
    if !name.is_empty() {
        out.push(name);
    }
    out
}

fn is_pattern(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::VarPat
            | NodeKind::LitPat
            | NodeKind::CtorPat
            | NodeKind::WildPat
            | NodeKind::TuplePat
            | NodeKind::ParenPat
            | NodeKind::VecPat
            | NodeKind::ErrPat
    )
}

fn literal_kind(k: Kind) -> LiteralKind {
    match k {
        Kind::NumberLiteral => LiteralKind::NumLit,
        Kind::TextLiteral => LiteralKind::TextLit,
        Kind::CharLiteral => LiteralKind::CharLit,
        Kind::TrueKeyword | Kind::FalseKeyword => LiteralKind::BoolLit,
        _ => LiteralKind::IntLit,
    }
}

/// **NO FALLBACK.** This answered `&` for anything it did not recognise, and
/// what actually reached it was a NEWLINE -- so nine definitions in
/// `ringplug-source.codex` had their `+` and `|` rewritten to `&` by the
/// desugarer, silently. The types still agreed (upstream's `&` answers its
/// left operand) so nothing failed; the only tell was that `&` is the one
/// operator that RECORDS an expression type, and the checker's `expr-types`
/// counter ran one over the oracle's. The token filter is fixed above; this
/// refuses rather than guess, so the next unrecognised token is a named error
/// instead of a counter nobody can explain.
fn binary_op(k: Kind) -> Option<BinaryOp> {
    Some(match k {
        Kind::Plus => BinaryOp::OpAdd,
        Kind::Minus => BinaryOp::OpSub,
        Kind::Star => BinaryOp::OpMul,
        Kind::Slash => BinaryOp::OpDiv,
        Kind::Caret => BinaryOp::OpPow,
        Kind::DoubleEquals => BinaryOp::OpEq,
        Kind::NotEquals => BinaryOp::OpNotEq,
        Kind::LessThan => BinaryOp::OpLt,
        Kind::GreaterThan => BinaryOp::OpGt,
        Kind::LessOrEqual => BinaryOp::OpLtEq,
        Kind::GreaterOrEqual => BinaryOp::OpGtEq,
        Kind::TripleEquals => BinaryOp::OpDefEq,
        // `&` is OpAnd, NOT OpAppend. It is overloaded -- append for text and
        // lists, conjunction for booleans, bitwise for integers -- and
        // upstream leaves the choice to the types. An interpreter makes it by
        // looking at the two values, which is the whole reason it needs none.
        Kind::Ampersand => BinaryOp::OpAnd,
        Kind::ColonColon => BinaryOp::OpCons,
        Kind::AndKeyword => BinaryOp::OpBoolAnd,
        Kind::Pipe | Kind::OrKeyword => BinaryOp::OpOr,
        // `xor` on booleans is inequality, and upstream says so directly.
        Kind::XorKeyword => BinaryOp::OpNotEq,
        Kind::Tilde => BinaryOp::OpApproxEq,
        Kind::TildeZero => BinaryOp::OpApproxEqExact,
        _ => return None,
    })
}

/// A binary operator that begins a continuation line is still that operator.
///
/// The subject is `ringplug-source.codex`, where nine definitions are written
/// this way; the first of them, `is-zig-primitive`, is what these two cases
/// are cut down from.
#[cfg(test)]
mod continuation_line_operator {
    use crate::ast::{BinaryOp, Expr};

    fn body_op(src: &str) -> BinaryOp {
        let bytes = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&bytes);
        let mut dg = super::Desugar::new(&bytes);
        let ch = dg.chapter(&parsed.tree);
        match &ch.defs.last().expect("one definition").body {
            Expr::Binary(_, op, _, _) => *op,
            other => panic!("not a binary: {other:?}"),
        }
    }

    const ONE_LINE: &str = "Chapter: P\nSection: S\n  f : Text -> Integer\n  f (s) = text-length s + text-length s\n";

    const TWO_LINES: &str = "Chapter: P\nSection: S\n  f : Text -> Integer\n  f (s) =\n   text-length s\n   + text-length s\n";

    #[test]
    fn a_newline_before_the_operator_does_not_make_it_an_ampersand() {
        assert_eq!(body_op(ONE_LINE), BinaryOp::OpAdd);
        assert_eq!(body_op(TWO_LINES), BinaryOp::OpAdd);
    }
}

/// The lower bound of a full-range integer.
///
/// `Integer between -9223372036854775808 and 9223372036854775807 wrapping` is
/// how the compiler's own `cons-mix` declares its accumulator, and
/// `parse::<i64>()` cannot read the magnitude: it is one past `i64::MAX`. The
/// bound arrived as zero, and twenty definitions of the compiler said `(int 0
/// ...)` where every gold says `(int i64-min ...)`.
#[cfg(test)]
mod full_range_integer_bound {
    use crate::ast::{OverflowMode, TypeExpr};

    fn bounds(src: &str) -> (i64, i64, OverflowMode) {
        let bytes = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&bytes);
        let mut dg = super::Desugar::new(&bytes);
        let ch = dg.chapter(&parsed.tree);
        let d = ch.defs.last().expect("one definition");
        let mut t = d.declared_type.first().expect("a declared type");
        while let TypeExpr::Fun(a, _, _) = t {
            t = a;
        }
        match t {
            TypeExpr::BoundedInt(_, lo, hi, m, _) => (*lo, *hi, *m),
            other => panic!("not a bounded integer: {other:?}"),
        }
    }

    #[test]
    fn the_lower_bound_is_i64_min_and_not_zero() {
        let src = "Chapter: P\nSection: S\n  mix : Integer between -9223372036854775808 and 9223372036854775807 wrapping -> Integer\n  mix (h) = h\n";
        assert_eq!(bounds(src), (i64::MIN, i64::MAX, OverflowMode::Wrapping));
    }

    #[test]
    fn an_ordinary_bound_is_unchanged() {
        let src = "Chapter: P\nSection: S\n  f : Integer between 0 and 255 -> Integer\n  f (b) = b\n";
        assert_eq!(bounds(src), (0, 255, OverflowMode::Error));
    }
}

/// What a `unit family` declaration is worth in definitions.
#[cfg(test)]
mod a_unit_family_is_definitions_not_just_a_type {

    /// **A `unit family` IS TWO DEFINITIONS PER MEMBER**, and we synthesised
    /// none: the constructor `M : Integer -> F` and the extractor
    /// `F-to-M : F -> Integer` (subject 43215). They mint at REGISTRATION, so
    /// the whole corpus's unit-bearing programs were short one type variable
    /// and three effect rows per member -- 169 ids and 507 rows on a single
    /// unit, every one of them ahead of code that then numbered differently.
    #[test]
    fn a_unit_family_synthesises_a_ctor_and_an_extractor_per_member() {
        let src = "Chapter: U\n\nSection: S\n  Duration = unit family Nanosecond\n    Nanosecond = 1\n    Microsecond = 1000\n\n  opening : Integer = 7\n";
        let bytes = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&bytes);
        let mut dg = super::Desugar::new(&bytes);
        let ch = dg.chapter(&parsed.tree);
        let names: Vec<String> = ch.defs.iter().map(|d| ch.syms.text(d.name).to_string()).collect();
        for want in [
            "Nanosecond",
            "Duration-to-Nanosecond",
            "Microsecond",
            "Duration-to-Microsecond",
        ] {
            assert!(names.iter().any(|n| n == want), "missing {want}: {names:?}");
        }
        // The base member's factor is 1, and both sides drop the arithmetic.
        let base = ch.defs.iter().find(|d| ch.syms.text(d.name) == "Duration-to-Nanosecond").unwrap();
        assert!(matches!(base.body, crate::ast::Expr::NameRef(..)), "{:?}", base.body);
    }
}
