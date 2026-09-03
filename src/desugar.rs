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
//! e revised { f = v } ->  let __rev = e in ... a chain of field assignments
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
use std::rc::Rc;
use crate::cst::{Node, NodeKind};
use crate::token::{Kind, Token};

pub struct Desugar<'a> {
    src: &'a [u8],
    slug: String,
}

fn span_of(t: &Token) -> Span {
    Span { line: t.line, col: t.col, offset: t.offset, len: t.len }
}

/// The first real token under a node -- every AST span upstream builds is
/// `token-span` of some token this node holds.
fn head_token<'n>(n: &'n Node) -> Option<&'n Token> {
    n.tokens().find(|t| !t.kind.is_trivia() && t.kind != Kind::Newline)
}

fn head_span(n: &Node) -> Span {
    head_token(n).map(span_of).unwrap_or_default()
}

impl<'a> Desugar<'a> {
    pub fn new(src: &'a [u8]) -> Self {
        Desugar { src, slug: String::new() }
    }

    fn text(&self, t: &Token) -> String {
        String::from_utf8_lossy(t.text(self.src)).into_owned()
    }

    /// The first name-shaped token's text.
    fn name_of(&self, n: &Node) -> Name {
        n.tokens()
            .find(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
            .map(|t| self.text(t))
            .unwrap_or_default()
    }

    /// The first token whatever its kind -- a record field or a constructor
    /// may be named with a keyword.
    fn leading(&self, n: &Node) -> Name {
        n.tokens().find(|t| !t.kind.is_trivia()).map(|t| self.text(t)).unwrap_or_default()
    }

    // -- expressions ---------------------------------------------------------

    pub fn expr(&self, n: &Node) -> Expr {
        let kids = n.child_nodes();
        let sp = head_span(n);
        match n.kind {
            NodeKind::Lit => match head_token(n) {
                Some(t) => Expr::Lit(self.text(t), literal_kind(t.kind), span_of(t)),
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
                            guard: Expr::Lit("True".into(), LiteralKind::BoolLit, Span::default()),
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
                        vec![LetBind { name: "__seq".into(), value, span }],
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
                let field = n
                    .own_tokens()
                    .filter(|t| !t.kind.is_trivia() && t.kind != Kind::Dot)
                    .last()
                    .map(|t| self.text(t))
                    .unwrap_or_default();
                Expr::FieldAccess(
                    Rc::new(kids.first().map_or(Expr::Error(String::new(), sp), |r| self.expr(r))),
                    field,
                    sp,
                )
            }
            NodeKind::FieldAssign => {
                let field = n
                    .own_tokens()
                    .filter(|t| !t.kind.is_trivia() && t.kind != Kind::Dot && t.kind != Kind::Equals)
                    .last()
                    .map(|t| self.text(t))
                    .unwrap_or_default();
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
                let base = Expr::NameRef(format!("MkTup{}", elems.len()), Span::default());
                elems.into_iter().fold(base, |f, a| Expr::Apply(Rc::new(f), Rc::new(a), sp))
            }
            NodeKind::ForExpr => {
                // `for x in xs -> b` is `map-list (\x -> b) xs`.
                let var = n
                    .own_tokens()
                    .find(|t| matches!(t.kind, Kind::Identifier | Kind::Underscore) && self.text(t) != "for")
                    .map(|t| self.text(t))
                    .unwrap_or_default();
                match kids.as_slice() {
                    [list, body] => {
                        let lam = Expr::Lambda(
                            vec![var],
                            Rc::new(self.expr(body)),
                            Span::default(),
                        );
                        let map_fn = Expr::NameRef("map-list".into(), Span::default());
                        Expr::Apply(
                            Rc::new(Expr::Apply(Rc::new(map_fn), Rc::new(lam), Span::default())),
                            Rc::new(self.expr(list)),
                            Span::default(),
                        )
                    }
                    _ => Expr::Error("for".into(), sp),
                }
            }
            NodeKind::Lambda => {
                let params: Vec<Name> = n
                    .own_tokens()
                    .filter(|t| matches!(t.kind, Kind::Identifier | Kind::Underscore))
                    .map(|t| self.text(t))
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
                Expr::Try(
                    count,
                    sect(NodeKind::TryBody),
                    sect(NodeKind::TryFallback),
                    sect(NodeKind::TryFailure),
                    sp,
                )
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
                Expr::Handle(eff, Rc::new(body), clauses, sp)
            }
            NodeKind::WithTimeout => {
                let timeout = n
                    .own_tokens()
                    .find(|t| t.kind == Kind::IntegerLiteral)
                    .map(|t| self.text(t))
                    .unwrap_or_default();
                let effs: Vec<Name> = n
                    .children_of(NodeKind::EffectRow)
                    .flat_map(|r| r.tokens())
                    .filter(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
                    .map(|t| self.text(t))
                    .collect();
                Expr::WithTimeout(
                    timeout,
                    effs,
                    Vec::new(),
                    Rc::new(
                        kids.iter()
                            .find(|k| k.kind != NodeKind::EffectRow)
                            .map_or(Expr::Error(String::new(), sp), |b| self.expr(b)),
                    ),
                    sp,
                )
            }
            NodeKind::LazyExpr => Expr::Lazy(
                Rc::new(kids.first().map_or(Expr::Error(String::new(), sp), |i| self.expr(i))),
                Span::default(),
            ),
            NodeKind::Revised => {
                // `e revised { f = v }` becomes a `__rev` binding and a chain
                // of field assignments over it.
                let base =
                    kids.first().map_or(Expr::Error(String::new(), sp), |b| self.expr(b));
                let mut chain = Expr::NameRef("__rev".into(), Span::default());
                for f in n.descendants(NodeKind::RecordField) {
                    let value = f
                        .child_nodes()
                        .last()
                        .map_or(Expr::Error(String::new(), sp), |v| self.expr(v));
                    chain = Expr::FieldAssign(
                        Rc::new(chain),
                        self.leading(f),
                        Rc::new(value),
                        Span::default(),
                    );
                }
                Expr::Let(
                    vec![LetBind { name: "__rev".into(), value: base, span: Span::default() }],
                    Rc::new(chain),
                    sp,
                )
            }
            NodeKind::ErrExpr => Expr::Error(self.leading(n), sp),
            // A node we do not translate is an error we can NAME, which is
            // better than an empty body that looks understood.
            _ => Expr::Error(format!("{:?}", n.kind), sp),
        }
    }

    fn binary(&self, n: &Node, kids: &[&Node], sp: Span) -> Expr {
        let op_tok = n.own_tokens().find(|t| !t.kind.is_trivia()).copied();
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
        Expr::Binary(Rc::new(l), binary_op(op.kind), Rc::new(r), osp)
    }

    fn unary(&self, n: &Node, kids: &[&Node], sp: Span) -> Expr {
        let op = n.own_tokens().find(|t| !t.kind.is_trivia()).copied();
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
                    Expr::Lit("True".into(), LiteralKind::BoolLit, Span::default())
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
                    ch.name = slug.clone();
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
                    span: head_span(child),
                }),
                NodeKind::InstanceDef => ch.instance_defs.push(InstanceDef {
                    class_name: self.name_of(child),
                    type_name: String::new(),
                    methods: Vec::new(),
                    span: head_span(child),
                }),
                NodeKind::Cites => ch.citations.push(CitesDecl {
                    quire: self.name_of(child),
                    chapter_name: String::new(),
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
                ch.rt_names.push(self.def_name(d));
            }
        }
        ch
    }

    fn def_name(&self, d: &Node) -> Name {
        d.children_of(NodeKind::DefEquation)
            .next()
            .map(|e| self.name_of(e))
            .filter(|n| !n.is_empty())
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
            .unwrap_or_else(|| Expr::Error("no body".into(), Span::default()));
        Def {
            name: name_tok.map(|t| self.text(&t)).unwrap_or_default(),
            params,
            declared_type,
            body,
            chapter_slug: self.slug.clone(),
            span: name_tok.map(|t| span_of(&t)).unwrap_or_default(),
            // The `claim` is parked INSIDE the definition that proves it, which
            // is what makes the association structural rather than "the next
            // sibling". That is also what makes it readable here.
            is_claim: d.child_nodes().iter().any(|k| k.kind == NodeKind::Claim),
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
                    .unwrap_or(TypeExpr::Named(String::new(), Span::default())),
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
            .map(|t| self.text(t))
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
                        .unwrap_or(TypeExpr::Named(String::new(), Span::default())),
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
                .unwrap_or(TypeExpr::Named("Integer".into(), sp));
            return Some(TypeDef::Unit(name, base, sp));
        }
        if td.children_of(NodeKind::UnitFamilyBody).next().is_some() {
            return Some(TypeDef::Unit(name, TypeExpr::Named("Integer".into(), sp), sp));
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
                .unwrap_or(TypeExpr::Named(String::new(), sp))
        };
        match n.kind {
            NodeKind::NamedType => TypeExpr::Named(
                n.tokens()
                    .filter(|t| !t.kind.is_trivia())
                    .map(|t| self.text(t))
                    .collect::<Vec<_>>()
                    .concat(),
                sp,
            ),
            NodeKind::ParenType => first(0),
            NodeKind::FunType => TypeExpr::Fun(Rc::new(first(0)), Rc::new(first(1)), sp),
            NodeKind::AppType => match kids.split_first() {
                Some((base, args)) => args.iter().fold(self.type_expr(base), |acc, a| {
                    TypeExpr::App(Rc::new(acc), vec![self.type_expr(a)], sp)
                }),
                None => TypeExpr::Named(String::new(), sp),
            },
            NodeKind::ArithType => {
                let op = n
                    .own_tokens()
                    .find(|t| !t.kind.is_trivia())
                    .map(|t| self.text(t))
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
                        let v: i64 = self.text(t).parse().unwrap_or(0);
                        nums.push(if neg { -v } else { v });
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
                    .map(|t| self.text(t))
                    .unwrap_or_default();
                TypeExpr::Forall(var, Rc::new(first(0)), Rc::new(first(1)), sp)
            }
            NodeKind::EffectType => {
                let effs: Vec<Name> = n
                    .own_tokens()
                    .filter(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
                    .map(|t| self.text(t))
                    .collect();
                TypeExpr::Effect(effs, Vec::new(), Vec::new(), Rc::new(first(0)), sp)
            }
            NodeKind::TupleType => {
                let elems: Vec<TypeExpr> = kids.iter().map(|k| self.type_expr(k)).collect();
                let base = TypeExpr::Named(format!("Tup{}", elems.len()), sp);
                elems.into_iter().fold(base, |f, a| TypeExpr::App(Rc::new(f), vec![a], sp))
            }
            _ => TypeExpr::Named(String::new(), sp),
        }
    }

    // -- patterns ------------------------------------------------------------

    pub fn pat(&self, n: &Node) -> Pat {
        let sp = head_span(n);
        match n.kind {
            NodeKind::VarPat => Pat::Var(self.leading(n), sp),
            NodeKind::LitPat => match head_token(n) {
                Some(t) => Pat::Lit(self.text(t), literal_kind(t.kind), sp),
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
                Pat::Ctor(format!("MkTup{}", subs.len()), subs, sp)
            }
            NodeKind::VecPat => {
                Pat::Vec_(n.child_nodes().into_iter().map(|k| self.pat(k)).collect(), sp)
            }
            _ => Pat::Wild(sp),
        }
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

fn binary_op(k: Kind) -> BinaryOp {
    match k {
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
        _ => BinaryOp::OpAnd,
    }
}
