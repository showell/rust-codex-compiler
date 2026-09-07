//! IR definition BODIES -- the `(defs ...)` the preamble stops short of.
//!
//! `preamble.rs` emits everything above `(defs` and is byte-identical on all
//! 1,012 golds, because that part is fixed by syntax alone. Below it, nearly
//! every node carries a TYPE:
//!
//! ```text
//! (def "opening" "NegIntParse" (params) int-default
//!   (apply (name "text-to-integer" (fn text int-default)) (text-lit "-5") int-default) 0 0)
//! ```
//!
//! so reaching a body means knowing types, not just shapes. This walks the
//! desugared AST and emits what it can TYPE WITH CERTAINTY, from three sources
//! and no inference: a definition's own declared type, the builtin table's
//! declared types, and the literals.
//!
//! ## It refuses rather than guesses, and that is the whole design
//!
//! Every function here returns `None` on anything it cannot type exactly. A
//! guessed type is not a partial answer -- it is a wrong answer that reads
//! exactly like a right one until someone diffs 900 bytes of nested s-
//! expressions. The gate is byte-identity against a gold, so a near miss is
//! worth nothing and a confident near miss is worth less than nothing.
//!
//! ## The golds are POST-PIPELINE, and that is a ceiling on this file
//!
//! A gold is not the raw lowered IR. It is that IR after
//! `fold-constants, inline-leaf-calls, inline-single-caller` -- the
//! `CDX4030 PIPELINE` line every compile log carries. `type-checker-test`
//! showed it: its gold's `opening` is `add-one (add-one 40)` and the
//! `apply-twice` it actually calls is GONE, inlined away as a single-caller
//! function.
//!
//! So units match here only where no pass fired on them. That is a real
//! oracle for those units and a hard ceiling for the rest: matching a gold
//! whose shape a pass changed needs the passes, not a better emitter. Do not
//! read a DIFFER on such a unit as an emission bug without checking whether a
//! pass explains it first.
//!
//! What it therefore cannot do yet, and must not pretend to: inferred types
//! (no annotation), local bindings whose type comes from their value, records,
//! lists, matches, effects. Those need the checker. `emit_defs` returns None
//! for the whole chapter if any definition in it is out of reach, because a
//! chapter emitted with half its defs is not comparable to anything.

use crate::symbol::{Sym, SymTab};
use crate::ast::{BinaryOp, Chapter, Expr, LiteralKind};
use crate::check::{Binding, Overflow, RealMode, RealWidth, Ty, TypeDefs, UnifyState};
use std::collections::BTreeMap;

/// A CHECKED type, as the IR spells it -- `ir-emit-type`
/// (Emit/IRTextEmitter.codex:241), arm for arm.
///
/// TOTAL, where `render_type` below is partial. A `CodexType` is the checker's
/// answer and every one of them has a spelling; a `TypeExpr` is a syntax tree
/// with no answer for a name the checker resolves, which is why that one
/// returns an Option and this one does not. The `otherwise` arm upstream keeps
/// as a floor for a variant added later is the `_ =>` here.
pub fn render_ty(syms: &SymTab, t: &Ty) -> String {
    let q = |n: Sym| format!("{:?}", syms.text(n));
    let list = |xs: &[Ty]| -> String {
        xs.iter().map(|x| format!(" {}", render_ty(syms, x))).collect()
    };
    match t {
        // `is-default-int` (line 104): the unbounded trapping integer, which
        // is what a bare `Integer` means and most of what a gold carries.
        Ty::Integer(lo, hi, m) if *lo == i64::MIN && *hi == i64::MAX && *m == Overflow::Error => {
            "int-default".into()
        }
        Ty::Integer(lo, hi, m) => format!(
            "(int {lo} {hi} {})",
            match m {
                Overflow::Error => "ov-error",
                Overflow::Wrapping => "ov-wrap",
                Overflow::Clamping => "ov-clamp",
            }
        ),
        Ty::Real(w, m) => match (w, m) {
            (RealWidth::F64, RealMode::Default) => "real".into(),
            (RealWidth::F64, RealMode::Trapping) => "real-trapping".into(),
            (RealWidth::F64, RealMode::Saturating) => "real-saturating".into(),
            (RealWidth::F32, RealMode::Default) => "real-approx".into(),
            (RealWidth::F32, RealMode::Trapping) => "real-approx-trapping".into(),
            (RealWidth::F32, RealMode::Saturating) => "real-approx-saturating".into(),
        },
        Ty::Text => "text".into(),
        Ty::Boolean => "boolean".into(),
        Ty::Char => "char".into(),
        Ty::Void => "void".into(),
        Ty::Nothing => "nothing".into(),
        Ty::Error => "error".into(),
        Ty::NoExpect => "noexpect".into(),
        Ty::Fun(p, row, r) => format!(
            "(fn {} {}{})",
            render_ty(syms, p),
            render_ty(syms, r),
            render_row(syms, row)
        ),
        Ty::List(e) => format!("(list {})", render_ty(syms, e)),
        Ty::LinkedList(e) => format!("(llist {})", render_ty(syms, e)),
        Ty::Var(id) => format!("(tvar {id})"),
        Ty::ForAll(id, b) => format!("(forall {id} {})", render_ty(syms, b)),
        // A row quantifier is TRANSPARENT on this wire: upstream emits the
        // body and drops the binder.
        Ty::ForAllEff(_, b) => render_ty(syms, b),
        Ty::Sum(n, a) => format!("(sum {} (args{}))", q(*n), list(a)),
        Ty::Constructed(n, a) => format!("(ctd {} (args{}))", q(*n), list(a)),
        Ty::Effectful(effs, sc, r) => format!(
            "(effectful (effs{}) (scopes{}) {})",
            effs.iter().map(|n| format!(" {}", q(*n))).collect::<String>(),
            // A scope is written down only where there is one, so the list is
            // PADDED to the effects: three effects print `(scopes "" "" "")`.
            (0..effs.len())
                .map(|i| format!(" {:?}", sc.get(i).map_or("", |x| x.as_str())))
                .collect::<String>(),
            render_ty(syms, r)
        ),
        Ty::Unit(n, inner) => format!("(unit {} {})", q(*n), render_ty(syms, inner)),
        Ty::Vector(n, e) => format!("(vector {n} {})", render_ty(syms, e)),
        Ty::VectorMask(n) => format!("(vector-mask {n})"),
        Ty::Linear(inner) => render_ty(syms, inner),
        Ty::Proof => "proof".into(),
        Ty::PropEq(a, b) => format!("(propeq {} {})", render_ty(syms, a), render_ty(syms, b)),
        Ty::TypeCon(n) => format!("(tycon {})", q(*n)),
        Ty::TypeApply(f, a) => {
            format!("(tyapply {} {})", render_ty(syms, f), render_ty(syms, a))
        }
        // `record-ty` recovers its arguments from the field variables when it
        // has none of its own, and this carries no fields. Left as the floor
        // it is rather than half-spelled.
        Ty::Record(n, a) => format!("(record-ty {} (args{}))", q(*n), list(a)),
    }
}

/// `ir-emit-row` (line 225). **ONLY A ROW CARRYING CONCRETE LABELS IS
/// PUBLISHED.** An open row with no labels is a row variable, and rows are
/// inert through the compiler's own stage 2 -- so a bare row variable is a
/// fact no consumer can use, and publishing every one of them grew the IR text
/// 15.4 per cent on `list-pattern` when upstream measured it.
fn render_row(syms: &SymTab, row: &crate::check::EffectRow) -> String {
    let _ = syms;
    if row.labels.is_empty() {
        return String::new();
    }
    let labels: String = row
        .labels
        .iter()
        .map(|(n, sc)| format!(" (label {n:?} {sc:?})"))
        .collect();
    format!(" (row (labels{}) {:?} {})", labels, row.tail, row.id)
}

/// **THE INPUTS `lower-chapter` TAKES.** Upstream's driver hands lowering
/// `(checked.scoped) (checked.all-bindings) (checked.ust)` -- the chapter, the
/// bindings the checker made, and the unification state -- and this carries
/// the same three.
///
/// The `Env` that stood here built its own answer from declared types plus a
/// table of 117 wire spellings, and could therefore never see a row the
/// checker minted: `print-line-uni` is `(fn text nothing (row ... "" 6))` and
/// the 6 is fib's own body's arithmetic. A static table has no way to hold it.
///
/// **NAMES ARE NOT LOOKED UP HERE AT ALL.** They are read out of `expr-types`
/// by SPAN, which is what `lookup-expr-type (ctx.ust) sp` does upstream. That
/// is not a shortcut: `fib` appears twice in its own body and the checker
/// recorded a different row id at each occurrence, so a lookup by name would
/// have to pick one and would be wrong about the other.
pub struct Lower<'a> {
    syms: &'a SymTab,
    st: &'a UnifyState,
    /// The chapter's type declarations. Lowering asks them two things a field
    /// access needs and the checker did not record: the field's TYPE, and its
    /// SLOT, which the wire spells as `"py/1"`.
    tds: &'a TypeDefs,
    /// This chapter's own definitions, keyed by name, for the `(def ...)`
    /// headers. Bodies do not consult it.
    bindings: BTreeMap<Sym, Ty>,
    /// The `__lam_N` each lambda in the chapter lifts to, by span. Assigned
    /// over the WHOLE chapter before any pruning -- see `lambda_names`.
    lam_names: BTreeMap<u64, String>,
    /// The `(def "__lam_N" ...)` lines lifted so far, appended after the
    /// chapter's own definitions in the order they were lifted.
    lifted: std::cell::RefCell<Vec<String>>,
    /// The LOCAL binders in scope at the node being lowered -- `enclosing`,
    /// the set a lambda may capture from. Only lambda lifting reads it, but
    /// every binding form has to maintain it, so it lives here rather than
    /// widening `expr`'s signature for one caller.
    scope: std::cell::RefCell<Vec<Sym>>,
}

/// A scope push that pops itself, so a `?` out of the middle of a binding form
/// cannot leave `enclosing` holding names that went out of scope.
struct Scope<'s>(&'s std::cell::RefCell<Vec<Sym>>, usize);

impl Drop for Scope<'_> {
    fn drop(&mut self) {
        self.0.borrow_mut().truncate(self.1);
    }
}

impl<'s> Scope<'s> {
    fn open(cx: &'s Lower) -> Scope<'s> {
        Scope(&cx.scope, cx.scope.borrow().len())
    }
    fn bind(&self, n: Sym) {
        self.0.borrow_mut().push(n);
    }
}

impl<'a> Lower<'a> {
    pub fn new(
        ch: &'a Chapter,
        bindings: &[Binding],
        st: &'a UnifyState,
        tds: &'a TypeDefs,
    ) -> Lower<'a> {
        Lower {
            syms: &ch.syms,
            st,
            tds,
            bindings: bindings.iter().map(|b| (b.name, b.ty.clone())).collect(),
            lam_names: lambda_names(ch),
            lifted: std::cell::RefCell::new(Vec::new()),
            scope: std::cell::RefCell::new(Vec::new()),
        }
    }

    /// The type the checker recorded at this exact source position, resolved
    /// through the substitutions -- `deep-resolve (ctx.ust) (lookup-expr-type
    /// (ctx.ust) sp)`. A HALF-resolved type reaches the wire as `(tvar 4)`
    /// where the oracle spells `int-default`, so the walk is the deep one.
    fn at(&self, sp: crate::ast::Span) -> Option<Ty> {
        self.st.expr_type_at(sp).map(|t| self.st.deep_resolve(t))
    }
}

/// One expression, as `(ir-text, its-type)`, or the REASON it was refused.
///
/// The reason is the whole point of the return type. A bare `None` told us the
/// corpus refused 1,008 of 1,012 units and nothing about which missing piece
/// would buy the most, so the next node form got picked by guessing. A reason
/// turns that into a histogram.
fn expr(e: &Expr, cx: &Lower) -> Result<(String, Ty), String> {
    match e {
        // Literals carry no type of their own in the IR -- `(int-lit 1)`, not
        // `(int-lit 1 int-default)` -- but their type is needed by whatever
        // encloses them, so it is returned alongside.
        Expr::Lit(v, LiteralKind::IntLit, _) => {
            Ok((format!("(int-lit {v})"), Ty::Integer(i64::MIN, i64::MAX, Overflow::Error)))
        }
        Expr::Lit(v, LiteralKind::TextLit, _) => Ok((format!("(text-lit {v})"), Ty::Text)),
        // **`true`, NOT `True`.** The source spells the constructor and the
        // wire spells the VALUE, lowercase. Every program carrying a boolean
        // literal differed by those two bytes.
        Expr::Lit(v, LiteralKind::BoolLit, _) => Ok((
            format!("(bool-lit {})", if v == "True" { "true" } else { "false" }),
            Ty::Boolean,
        )),
        // `(char-lit 15)` for `'a'` -- the CHAR-CODE, not the byte and not the
        // codepoint. `lower-literal` reads `text-to-integer text` because
        // upstream's desugarer already turned the token into that number;
        // ours keeps the raw token, so the decode happens at this end instead.
        Expr::Lit(v, LiteralKind::CharLit, _) => Ok((
            format!("(char-lit {})", crate::charcode::char_literal_code(v)),
            Ty::Char,
        )),
        Expr::Lit(_, k, _) => Err(format!("literal kind {k:?}")),
        // `(negate X TYPE)`, and the type is the OPERAND's -- negating does
        // not change it. `-n` is this; `0 - n` is a `binary sub-int` and the
        // two are different nodes on the wire even where a reader would call
        // them the same expression.
        Expr::Unary(x, _) => {
            let (xt, xty) = expr(x, cx)?;
            let rendered = render_ty(cx.syms, &xty);
            Ok((format!("(negate {xt} {rendered})"), xty))
        }
        // Straight out of `expr-types`, at this node's own span.
        Expr::NameRef(n, sp) => match cx.at(*sp) {
            Some(t) => Ok((
                format!("(name {:?} {})", cx.syms.text(*n), render_ty(cx.syms, &t)),
                t,
            )),
            None => Err(format!("the checker recorded no type at `{}`", cx.syms.text(*n))),
        },
        Expr::Apply(f, a, _) => {
            let (ft, fty) = expr(f, cx)?;
            let (at, _aty) = expr(a, cx)?;
            // The result of applying one argument is the arrow's right half.
            // A non-arrow here is an over-application, which is a real error
            // and not something to paper over with the same type back.
            let res = match fty {
                Ty::Fun(_, _, r) => *r,
                other => {
                    return Err(format!("applying a non-arrow `{}`", render_ty(cx.syms, &other)))
                }
            };
            Ok((format!("(apply {ft} {at} {})", render_ty(cx.syms, &res)), res))
        }
        // `(binary <op> L R <type>)`. THE OPERATOR NAME DEPENDS ON THE OPERAND
        // TYPE -- `add-int`, `add-num` and `add-vec` are three names for one
        // source `+` -- so this needs the operands typed first and refuses
        // where it cannot tell. A comparison answers `boolean` whatever it
        // compared; arithmetic answers what it was given.
        Expr::Binary(l, op, r, _) => {
            let (lt, lty) = expr(l, cx)?;
            let (rt, rty) = expr(r, cx)?;
            // **THE RESULT IS THE LEFT OPERAND'S TYPE, AND TWO INTEGERS OF
            // DIFFERENT BOUNDS ARE COMPATIBLE.** `b + 1` over
            // `Integer between 0 and 255` answers `(int 0 255 ov-error)` and
            // `1 + b` answers `int-default` -- so the rule is simply the LEFT,
            // not the wider or the narrower of the two. Two differently
            // bounded operands follow the same rule.
            //
            // Requiring the two to be EQUAL refused every arithmetic touching a
            // bounded declaration, which the depot writes constantly.
            let compatible = match (&lty, &rty) {
                (Ty::Integer(..), Ty::Integer(..)) => true,
                (Ty::Real(..), Ty::Real(..)) => true,
                _ => lty == rty,
            };
            if !compatible {
                return Err(format!(
                    "binary operands disagree: `{}` vs `{}`",
                    render_ty(cx.syms, &lty),
                    render_ty(cx.syms, &rty)
                ));
            }
            let arith = |stem: &str| -> Result<String, String> {
                match &lty {
                    Ty::Integer(..) => Ok(format!("{stem}-int")),
                    Ty::Real(..) => Ok(format!("{stem}-num")),
                    other => Err(format!("{stem} on `{}`", render_ty(cx.syms, other))),
                }
            };
            let (name, ty) = match op {
                BinaryOp::OpAdd => (arith("add")?, lty.clone()),
                BinaryOp::OpSub => (arith("sub")?, lty.clone()),
                BinaryOp::OpMul => (arith("mul")?, lty.clone()),
                BinaryOp::OpDiv => (arith("div")?, lty.clone()),
                BinaryOp::OpEq => ("eq".into(), Ty::Boolean),
                BinaryOp::OpNotEq => ("ne".into(), Ty::Boolean),
                BinaryOp::OpLt => ("lt".into(), Ty::Boolean),
                BinaryOp::OpGt => ("gt".into(), Ty::Boolean),
                BinaryOp::OpLtEq => ("le".into(), Ty::Boolean),
                BinaryOp::OpGtEq => ("ge".into(), Ty::Boolean),
                // **ONE TOKEN, THREE ATOMS.** `&` is `and` over Booleans,
                // `append-text` over Text and `append-list` over a List, and
                // the OPERAND type is what picks. `and` the keyword is only
                // ever logical.
                BinaryOp::OpAnd | BinaryOp::OpAppend => match &lty {
                    Ty::Boolean => ("and".to_string(), Ty::Boolean),
                    Ty::Text => ("append-text".to_string(), lty.clone()),
                    Ty::List(_) => ("append-list".to_string(), lty.clone()),
                    other => {
                        return Err(format!("`&` on `{}`", render_ty(cx.syms, other)))
                    }
                },
                BinaryOp::OpBoolAnd => ("and".into(), Ty::Boolean),
                BinaryOp::OpOr => ("or".into(), Ty::Boolean),
                other => return Err(format!("binary op {other:?}")),
            };
            let rendered = render_ty(cx.syms, &ty);
            Ok((format!("(binary {name} {lt} {rt} {rendered})"), ty))
        }
        // `(if C T E <type>)`. The type is the BRANCHES', and both must agree
        // -- if they do not, this is not a place to pick one and move on.
        Expr::If(c, th, el, _) => {
            let (ct, _) = expr(c, cx)?;
            let (tt, tty) = expr(th, cx)?;
            let (et, ety) = expr(el, cx)?;
            if tty != ety {
                return Err(format!(
                    "if branches disagree: `{}` vs `{}`",
                    render_ty(cx.syms, &tty),
                    render_ty(cx.syms, &ety)
                ));
            }
            let rendered = render_ty(cx.syms, &tty);
            Ok((format!("(if {ct} {tt} {et} {rendered})"), tty))
        }
        // `(list-expr (elems ...) ELEM)` -- the trailing type is the ELEMENT's,
        // not the list's, checked against golds carrying text and nested-list
        // elements rather than assumed from the integer cases. The NODE's type
        // is `(list ELEM)`.
        //
        // An empty list has no element to read a type from and is refused: the
        // type is in the context, which the checker decides and this does not.
        Expr::List(xs, sp) => {
            // An empty list's element type is the variable the checker minted
            // for it, resolved through the substitutions -- so `[]` in a call
            // to `list-length` spells `(list-expr (elems) int-default)`.
            if xs.is_empty() {
                let e = cx.at(*sp).ok_or("empty list literal with no recorded element type")?;
                let rendered = render_ty(cx.syms, &e);
                return Ok((
                    format!("(list-expr (elems) {rendered})"),
                    Ty::List(Box::new(e)),
                ));
            }
            let mut parts = Vec::new();
            let mut elem: Option<Ty> = None;
            for x in xs {
                let (xt, xty) = expr(x, cx)?;
                match &elem {
                    None => elem = Some(xty),
                    Some(e) if *e == xty => {}
                    Some(e) => {
                        return Err(format!(
                            "list elements disagree: `{}` vs `{}`",
                            render_ty(cx.syms, e),
                            render_ty(cx.syms, &xty)
                        ))
                    }
                }
                parts.push(xt);
            }
            let e = elem.unwrap();
            let rendered = render_ty(cx.syms, &e);
            Ok((
                format!("(list-expr (elems {}) {rendered})", parts.join(" ")),
                Ty::List(Box::new(e)),
            ))
        }
        // `(let "n" TYPE VALUE BODY)`, nested one deep per binding, and the
        // let's own type is the BODY's -- a let evaluates to its body.
        Expr::Let(binds, body, _) => {
            let scope = Scope::open(cx);
            let mut heads = Vec::new();
            for b in binds {
                let (vt, vty) = expr(&b.value, cx)?;
                // `lift-expr`'s `IrLet` arm adds the name for the BODY only,
                // and the golds nest one let per binding -- so binding i's
                // value sees 0..i and not itself.
                scope.bind(b.name);
                heads.push((b.name, vty, vt));
            }
            let (bt, bty) = expr(body, cx)?;
            let mut out = bt;
            for (n, ty, v) in heads.into_iter().rev() {
                out = format!(
                    "(let {:?} {} {} {})",
                    cx.syms.text(n),
                    render_ty(cx.syms, &ty),
                    v,
                    out
                );
            }
            Ok((out, bty))
        }
        // `(act (stmts S...) TYPE)`, one `(do-exec E)` or `(do-bind "n" TYPE E)`
        // per statement, and the block's type is the type of what it ENDS
        // with -- an act evaluates to its last statement, the same way a let
        // evaluates to its body.
        //
        // A bind's written type is the type of what it binds. Upstream's row
        // arithmetic decides what the EFFECT of the block is; this is the
        // value side, which is all the wire carries here.
        Expr::Act(stmts, _) => {
            let scope = Scope::open(cx);
            let mut parts = Vec::new();
            let mut last = Ty::Nothing;
            for st in stmts {
                match st {
                    crate::ast::ActStmt::Exec(e, _) => {
                        let (t, ty) = expr(e, cx)?;
                        parts.push(format!("(do-exec {t})"));
                        last = ty;
                    }
                    crate::ast::ActStmt::Bind(n, e, _) => {
                        let (t, ty) = expr(e, cx)?;
                        // `lift-act-stmts` binds the name for the statements
                        // AFTER this one, not for its own value.
                        scope.bind(*n);
                        parts.push(format!(
                            "(do-bind {:?} {} {})",
                            cx.syms.text(*n),
                            render_ty(cx.syms, &ty),
                            t
                        ));
                        last = ty;
                    }
                }
            }
            let rendered = render_ty(cx.syms, &last);
            Ok((format!("(act (stmts {}) {rendered})", parts.join(" ")), last))
        }
        // `(record "P" (fields (field-val "px" X) ...) TYPE)`. The fields are
        // emitted IN THE ORDER THE EXPRESSION WRITES THEM, not the order the
        // record declares them -- measured, because the reverse is the obvious
        // guess and it is wrong.
        Expr::Record(n, fields, sp) => {
            let ty = cx
                .at(*sp)
                .ok_or_else(|| format!("no recorded type for record `{}`", cx.syms.text(*n)))?;
            let mut parts = String::new();
            for f in fields {
                let (v, _) = expr(&f.value, cx)?;
                parts.push_str(&format!(" (field-val {:?} {v})", cx.syms.text(f.name)));
            }
            let rendered = render_ty(cx.syms, &ty);
            Ok((
                format!("(record {:?} (fields{}) {rendered})", cx.syms.text(*n), parts),
                ty,
            ))
        }
        // `(field-access OBJ "py/1" TYPE)` -- the field's name AND its slot in
        // the declaration. The checker records no type here, so both the type
        // and the slot are read back out of the type declarations.
        Expr::FieldAccess(r, f, _) => {
            let (rt, rty) = expr(r, cx)?;
            let name = match &rty {
                Ty::Record(n, _) | Ty::Constructed(n, _) => *n,
                other => {
                    return Err(format!(
                        "field access on `{}`, which is not a record",
                        render_ty(cx.syms, other)
                    ))
                }
            };
            let (Some(fty), Some(slot)) = (cx.tds.field(name, *f), cx.tds.field_index(name, *f))
            else {
                return Err(format!(
                    "`{}` has no field `{}` here",
                    cx.syms.text(name),
                    cx.syms.text(*f)
                ));
            };
            let fty = cx.st.deep_resolve(fty);
            let rendered = render_ty(cx.syms, &fty);
            Ok((
                format!(
                    "(field-access {rt} {:?} {rendered})",
                    format!("{}/{}", cx.syms.text(*f), slot)
                ),
                fty,
            ))
        }
        // **A LAMBDA IS NOT A NODE ON THIS WIRE.** `lift-lambdas` turned it
        // into a top-level `__lam_N` and left a reference behind, so what this
        // arm emits is that reference -- `(name "__lam_0" TY)`, applied to
        // each captured variable -- and it pushes the definition itself onto
        // `cx.lifted` for `emit_defs_checked` to append.
        Expr::Lambda(ps, body, sp) => {
            // `lift-one-lambda` recursing on an `IrLambda` body concatenates
            // the parameters, so `\a -> \b -> e` lifts to ONE definition of
            // two parameters. Its name was reserved for the outer span.
            let mut params: Vec<Sym> = ps.clone();
            let mut inner: &Expr = body;
            while let Expr::Lambda(ips, ib, _) = inner {
                params.extend(ips.iter().copied());
                inner = ib;
            }
            let name = cx
                .lam_names
                .get(&crate::check::expr_type_key(*sp))
                .ok_or("a lambda the numbering pass never saw")?
                .clone();
            // `expected-or-recorded-ty`: we have only the recorded half, which
            // is what `lower-lambda` falls back to when nothing above expects
            // a type. Where the two disagree this will show as a diff rather
            // than as a wrong answer that reads right.
            let lam_ty = cx.at(*sp).ok_or("the checker recorded no type for this lambda")?;
            // `infer-lambda-return-ty` peels one arrow per parameter, and
            // `lower-lambda-params` reads the parameter types off the same
            // spine.
            let mut ret = lam_ty;
            let mut param_tys = Vec::new();
            for p in &params {
                match ret {
                    Ty::Fun(a, _, r) => {
                        param_tys.push(*a);
                        ret = *r;
                    }
                    _ => {
                        return Err(format!(
                            "lambda parameter `{}` has no arrow to come from",
                            cx.syms.text(*p)
                        ))
                    }
                }
            }
            // The body is lifted FIRST -- which is what makes a nested lambda
            // take the lower number -- with the parameters in scope.
            let body_text = {
                let scope = Scope::open(cx);
                params.iter().for_each(|p| scope.bind(*p));
                expr(inner, cx)?.0
            };
            // `collect-free-vars body-expr param-names enclosing []`: bound is
            // the lambda's OWN parameters, capturable is the scope outside it.
            let outer: Vec<Sym> = cx.scope.borrow().clone();
            let mut caps = BTreeMap::new();
            let mut bound = params.clone();
            free_vars(inner, &mut bound, &outer, cx, &mut caps)?;
            // `build-function-ty` uses `empty-row` for every arrow it builds.
            let arrows = |ps: &[(Sym, Ty)], ret: &Ty| -> Ty {
                ps.iter().rev().fold(ret.clone(), |acc, (_, t)| {
                    Ty::Fun(Box::new(t.clone()), Default::default(), Box::new(acc))
                })
            };
            let own: Vec<(Sym, Ty)> =
                params.iter().copied().zip(param_tys.into_iter()).collect();
            // `build-lifted-params`: the captures come FIRST, in name order.
            let captures: Vec<(Sym, Ty)> = caps.into_values().collect();
            let lifted_params: Vec<(Sym, Ty)> =
                captures.iter().cloned().chain(own.iter().cloned()).collect();
            let lifted_ty = arrows(&lifted_params, &ret);
            let params_text: String = lifted_params
                .iter()
                .map(|(n, t)| {
                    format!(" (param {:?} {})", cx.syms.text(*n), render_ty(cx.syms, t))
                })
                .collect();
            cx.lifted.borrow_mut().push(format!(
                "\n  (def {:?} \"\" (params{}) {} {} 0 0)",
                name,
                params_text,
                render_ty(cx.syms, &lifted_ty),
                body_text
            ));
            // `build-partial-app`: the name, then one apply per capture, each
            // typed with what is LEFT of the arrow after it.
            let mut acc = format!("(name {name:?} {})", render_ty(cx.syms, &lifted_ty));
            let mut acc_ty = lifted_ty;
            for (n, t) in &captures {
                acc_ty = match acc_ty {
                    Ty::Fun(_, _, r) => *r,
                    other => other,
                };
                acc = format!(
                    "(apply {acc} (name {:?} {}) {})",
                    cx.syms.text(*n),
                    render_ty(cx.syms, t),
                    render_ty(cx.syms, &acc_ty)
                );
            }
            Ok((acc, acc_ty))
        }
        // `(field-store OBJ "parts/0" VALUE TYPE)`, and **THE TYPE IS THE
        // RECORD'S, NOT THE FIELD'S** -- `lower-expr`'s `AFieldAssignExpr` arm
        // builds `IrFieldStore rec-ir (field.value) val-ir rec-ty s`, so a
        // store evaluates to the record it wrote into. The `let __seq` the
        // desugarer wraps it in therefore binds the record type, which is what
        // makes `sb.parts = ...` sequenceable.
        //
        // The slot comes from the type declarations exactly as it does for a
        // read: the emitter calls `ir-resolve-field-index (ir-expr-type r) f`
        // on the OBJECT's type in both cases.
        Expr::FieldAssign(r, f, v, _) => {
            let (rt, rty) = expr(r, cx)?;
            let name = match &rty {
                Ty::Record(n, _) | Ty::Constructed(n, _) => *n,
                other => {
                    return Err(format!(
                        "field store into `{}`, which is not a record",
                        render_ty(cx.syms, other)
                    ))
                }
            };
            let Some(slot) = cx.tds.field_index(name, *f) else {
                return Err(format!(
                    "`{}` has no field `{}` here",
                    cx.syms.text(name),
                    cx.syms.text(*f)
                ));
            };
            let (vt, _) = expr(v, cx)?;
            let rendered = render_ty(cx.syms, &rty);
            Ok((
                format!(
                    "(field-store {rt} {:?} {vt} {rendered})",
                    format!("{}/{}", cx.syms.text(*f), slot)
                ),
                rty,
            ))
        }
        // `(match SC (branches (branch PAT BODY GUARD) ...) TYPE)`. Every arm
        // carries a guard -- an unguarded one carries `(bool-lit true)`, which
        // the desugarer put there -- and the arms have already been unified
        // into one type, so the first body's is the match's.
        Expr::Match(scrut, arms, _) => {
            let (st_, sty) = expr(scrut, cx)?;
            let mut parts = String::new();
            let mut ty: Option<Ty> = None;
            for a in arms {
                let pat = pattern(&a.pattern, &sty, cx)?;
                // The names the pattern binds are in scope for the body AND
                // the guard -- `lift-branches` builds one `branch-enclosing`
                // and hands it to both.
                let scope = Scope::open(cx);
                let mut names = Vec::new();
                pat_names(&a.pattern, &mut names);
                names.into_iter().for_each(|n| scope.bind(n));
                let (body, bty) = expr(&a.body, cx)?;
                let (guard, _) = expr(&a.guard, cx)?;
                parts.push_str(&format!(" (branch {pat} {body} {guard})"));
                ty.get_or_insert(bty);
            }
            let ty = ty.ok_or("a match with no arms")?;
            let rendered = render_ty(cx.syms, &ty);
            Ok((format!("(match {st_} (branches{parts}) {rendered})"), ty))
        }
        other => Err(node_kind(other).to_string()),
    }
}

/// One pattern. **A CONSTRUCTOR PATTERN CARRIES THE SCRUTINEE'S TYPE**, not its
/// own result type, and its sub-patterns carry the FIELD types -- which come
/// from the constructor's binding, peeled arrow by arrow.
///
/// A wildcard is the bare atom `wild-pat`, with no parentheses and no type.
fn pattern(p: &crate::ast::Pat, scrut: &Ty, cx: &Lower) -> Result<String, String> {
    use crate::ast::Pat as P;
    match p {
        P::Wild(_) => Ok("wild-pat".into()),
        P::Var(n, _) => Ok(format!(
            "(var-pat {:?} {})",
            cx.syms.text(*n),
            render_ty(cx.syms, scrut)
        )),
        P::Lit(v, _, _) => {
            Ok(format!("(lit-pat {:?} {})", v, render_ty(cx.syms, scrut)))
        }
        P::Ctor(name, subs, _) => {
            let bound = cx
                .bindings
                .get(name)
                .ok_or_else(|| format!("no constructor `{}`", cx.syms.text(*name)))?;
            // **A POLYMORPHIC CONSTRUCTOR IS REFUSED, NOT GUESSED AT.** Its
            // field types are quantified, and instantiating one here would
            // mint -- which lowering must not do. Substituting the scrutinee's
            // arguments through the quantifier is the way in, and it needs its
            // own measurement rather than an assumption.
            let mut spine = match bound {
                Ty::ForAll(..) | Ty::ForAllEff(..) => {
                    return Err(format!(
                        "polymorphic constructor `{}` in a pattern",
                        cx.syms.text(*name)
                    ))
                }
                other => other.clone(),
            };
            let mut out = String::new();
            for sub in subs {
                let field = match spine {
                    Ty::Fun(a, _, r) => {
                        spine = *r;
                        cx.st.deep_resolve(&a)
                    }
                    _ => {
                        return Err(format!(
                            "`{}` takes fewer fields than the pattern binds",
                            cx.syms.text(*name)
                        ))
                    }
                };
                out.push_str(&format!(" {}", pattern(sub, &field, cx)?));
            }
            Ok(format!(
                "(ctor-pat {:?} (subs{}) {})",
                cx.syms.text(*name),
                out,
                render_ty(cx.syms, scrut)
            ))
        }
        P::Vec_(..) => Err("vector pattern".into()),
    }
}

/// The variant's name, for the refusal histogram.
fn node_kind(e: &Expr) -> &'static str {
    match e {
        Expr::Lit(..) => "Lit",
        Expr::NameRef(..) => "NameRef",
        Expr::Apply(..) => "Apply",
        Expr::Binary(..) => "Binary",
        Expr::Unary(..) => "Unary",
        Expr::If(..) => "If",
        Expr::Let(..) => "Let",
        Expr::Lambda(..) => "Lambda",
        Expr::Match(..) => "Match",
        Expr::List(..) => "List",
        Expr::Record(..) => "Record",
        Expr::FieldAccess(..) => "FieldAccess",
        Expr::Act(..) => "Act",
        Expr::Handle(..) => "Handle",
        Expr::WithTimeout(..) => "WithTimeout",
        Expr::Try(..) => "Try",
        Expr::FieldAssign(..) => "FieldAssign",
        Expr::Lazy(..) => "Lazy",
        Expr::Error(..) => "Error",
        Expr::Induction(..) => "Induction",
    }
}

/// The definition lines for a chapter, or None if ANY definition in it is
/// out of reach -- a chapter with half its defs emitted compares to nothing.
/// The driver's own root set, `opening.codex:1373`:
///
/// ```text
/// ir-emit-roots = ["opening", "vb-capacity-auto", "vb-read-auto",
///                  "vb-write-auto", "fat16-servicer-read", "fat16-servicer-write"]
/// ```
///
/// NOT just `opening`. The block-device and FAT16 servicers are entered by the
/// runtime rather than called, so a call-graph walk cannot find them -- which
/// is exactly what `hal-device-declared` showed: its gold keeps `vb-off-magic`
/// from VirtioBlk, and rooting at `opening` alone dropped it.
pub const IR_EMIT_ROOTS: [&str; 6] = [
    "opening",
    "vb-capacity-auto",
    "vb-read-auto",
    "vb-write-auto",
    "fat16-servicer-read",
    "fat16-servicer-write",
];

/// Check, then lower -- the driver's own two steps, in its own order
/// (`opening.codex:798`). A caller that already has a `checked` hands it to
/// `emit_defs_checked` instead of paying for a second pass.
pub fn emit_defs(ch: &Chapter) -> Result<String, String> {
    let (bindings, st, tds) = crate::check::check_chapter_full(ch);
    emit_defs_checked(ch, &bindings, &st, &tds, &IR_EMIT_ROOTS)
}

/// Names reachable from the roots, following NameRefs through def bodies.
///
/// A gold's `(defs` is PRUNED: a resolved unit carries every cited chapter, and
/// `neg-int-parse` cites Foreword ListUtils, yet its gold holds one definition.
/// Emitting the unit's whole def list would be a different document from the
/// gold no matter how correct each line was -- and it is also why a chapter that
/// looks impossible to type usually is not: the untypable definitions are
/// library code nothing in the program reaches.
fn reachable(ch: &Chapter, roots: &[&str]) -> std::collections::BTreeSet<String> {
    let by_name: BTreeMap<&str, &crate::ast::Def> =
        ch.defs.iter().map(|d| (ch.syms.text(d.name), d)).collect();
    let mut seen = std::collections::BTreeSet::new();
    let mut stack: Vec<String> =
        roots.iter().filter(|r| by_name.contains_key(**r)).map(|r| r.to_string()).collect();
    while let Some(n) = stack.pop() {
        if !seen.insert(n.clone()) {
            continue;
        }
        if let Some(d) = by_name.get(n.as_str()) {
            d.body.walk(&mut |x| {
                if let Expr::NameRef(m, _) = x {
                    if by_name.contains_key(ch.syms.text(*m)) && !seen.contains(ch.syms.text(*m)) {
                        stack.push(ch.syms.text(*m).to_string());
                    }
                }
            });
        }
    }
    seen
}

pub fn emit_defs_checked(
    ch: &Chapter,
    bindings: &[Binding],
    st: &UnifyState,
    tds: &TypeDefs,
    roots: &[&str],
) -> Result<String, String> {
    let keep = reachable(ch, roots);
    if keep.is_empty() {
        return Err("no root reached: the chapter defines none of ir-emit-roots".into());
    }
    let cx = Lower::new(ch, bindings, st, tds);
    // The OPENER is the preamble's last line, so this contributes only the
    // definitions. `preamble::emit` ends at `  (defs` because that is where the
    // syntax-only part of a gold stops.
    let mut out = String::new();
    for d in ch.defs.iter().filter(|d| keep.contains(ch.syms.text(d.name))) {
        // **THE CHECKER'S BINDING, NOT THE DECLARATION.** They agree wherever
        // a definition declares a type and only the checker has an answer
        // where one does not -- `register-all-defs` mints a variable for it,
        // and that variable is what the arrow spine below has to peel.
        let bound = match cx.bindings.get(&d.name) {
            Some(t) => st.deep_resolve(t),
            None => {
                return Err(format!("`{}` was never bound by the checker", ch.syms.text(d.name)))
            }
        };
        let declared = render_ty(&ch.syms, &bound);
        // Parameter types come from walking the bound arrow spine, which is
        // the only place they are written down.
        let mut rest = bound.clone();
        let mut params = String::new();
        // `absorb-outer-lambdas`: a definition written `f = \x -> ...` carries
        // that lambda's parameters as its OWN, and the lambda is never lifted.
        let mut own: Vec<Sym> = d.params.iter().map(|p| p.name).collect();
        let mut body_expr: &Expr = &d.body;
        while let Expr::Lambda(ps, inner, _) = body_expr {
            own.extend(ps.iter().copied());
            body_expr = inner;
        }
        // `lift-defs` opens each definition with its parameters as the whole
        // of `enclosing` -- nothing outside a definition is capturable.
        let scope = Scope::open(&cx);
        own.iter().for_each(|p| scope.bind(*p));
        for p in &own {
            let (arg, res) = match rest {
                Ty::Fun(a, _, r) => (*a, *r),
                _ => {
                    return Err(format!(
                        "`{}` has more params than its type has arrows",
                        ch.syms.text(d.name)
                    ))
                }
            };
            params.push_str(&format!(
                " (param {:?} {})",
                ch.syms.text(*p),
                render_ty(&ch.syms, &arg)
            ));
            rest = res;
        }
        let (body, _bty) =
            expr(body_expr, &cx).map_err(|r| format!("{}: {r}", ch.syms.text(d.name)))?;
        drop(scope);
        out.push_str(&format!(
            "\n  (def {:?} {:?} (params{}) {} {} 0 0)",
            ch.syms.text(d.name), d.chapter_slug, params, declared, body
        ));
    }
    // `lift-lambdas` appends its definitions after the chapter's own:
    // `__record-set chapter "defs" (defs & (ctx.lifted))`. Pruning is not a
    // second question here -- a lifted definition is reachable exactly when
    // the definition that referenced it is, and only kept definitions were
    // walked.
    for d in cx.lifted.borrow().iter() {
        out.push_str(d);
    }
    Ok(out)
}

/// The `--- lower ---` section: a SHAPE dump, not IR text.
///
/// `LowerHarness.codex` prints each definition's header and then its expression
/// tree as depth-prefixed kinds. The walk is PRE-ORDER and descends only into
/// arms that carry an IRExpr -- a node holding a statement list prints its kind
/// and stops, because the point is to diff two arms against each other and a
/// node the walk does not enter is still a node both arms must agree on.
///
/// Cheaper to match than the IR text and it grades the same thing: whether the
/// tree we lowered has the shape upstream lowered.
/// NOT PRUNED. `ir-prune-unreachable-roots` runs at EMIT time -- the driver
/// writes `emit-ir-chapter (ir-prune-unreachable-roots lifted-ir
/// ir-emit-roots)` -- so the IR golds are pruned and this rung is not. `fib`
/// shows the difference directly: nothing calls `double`, the IR gold drops it,
/// and lower.truth keeps it.
pub fn lower_section(ch: &Chapter, _roots: &[&str]) -> String {
    let tds = crate::check::TypeDefs::new(ch);
    let defs: Vec<&crate::ast::Def> = ch.defs.iter().collect();
    let mut s = String::from("--- lower ---\n");
    s.push_str(&format!("ir-name |{}|\n", ch.syms.text(ch.name)));
    s.push_str(&format!("ir-defs {}\n", defs.len()));
    s.push_str("ir-eff-ops 0\n.\n");
    for d in &defs {
        let ty = d
            .declared_type
            .first()
            .and_then(|t| crate::check::resolve_declared(&ch.syms, &tds, t))
            .map_or_else(|| "other".to_string(), |t| crate::check::type_kind(&ch.syms, &t));
        s.push_str(&format!(
            "irdef {} params {} slug {} punctual 0 uparams 0 ty {}\n",
            ch.syms.text(d.name),
            d.params.len(),
            d.chapter_slug,
            ty
        ));
        shape(&ch.syms, &d.body, 0, &mut s);
    }
    s.push_str(".\n---\n");
    s
}

fn kind(syms: &SymTab, e: &Expr) -> String {
    match e {
        Expr::Lit(_, LiteralKind::IntLit, _) => "int".into(),
        Expr::Lit(_, LiteralKind::NumLit, _) => "num".into(),
        Expr::Lit(_, LiteralKind::TextLit, _) => "text".into(),
        Expr::Lit(_, LiteralKind::BoolLit, _) => "bool".into(),
        Expr::Lit(_, LiteralKind::CharLit, _) => "char".into(),
        Expr::NameRef(n, _) => format!("name:{}", syms.text(*n)),
        Expr::Binary(..) => "binary".into(),
        Expr::Unary(..) => "negate".into(),
        Expr::If(..) => "if".into(),
        Expr::Let(bs, ..) => {
            format!("let:{}", bs.first().map_or("", |b| syms.text(b.name)))
        }
        Expr::Apply(..) => "apply".into(),
        Expr::Lambda(..) => "lambda".into(),
        Expr::List(..) => "list".into(),
        Expr::Match(..) => "match".into(),
        Expr::Act(..) => "act".into(),
        Expr::Record(n, ..) => format!("record:{}", syms.text(*n)),
        Expr::FieldAccess(_, f, _) => format!("field:{}", syms.text(*f)),
        Expr::FieldAssign(_, f, _, _) => format!("store:{}", syms.text(*f)),
        Expr::Error(..) => "error".into(),
        _ => "other".into(),
    }
}

fn shape(syms: &SymTab, e: &Expr, d: usize, out: &mut String) {
    out.push_str(&format!("e{d} {}\n", kind(syms, e)));
    match e {
        Expr::Binary(l, _, r, _) => {
            shape(syms, l, d + 1, out);
            shape(syms, r, d + 1, out);
        }
        Expr::Unary(x, _) => shape(syms, x, d + 1, out),
        Expr::If(c, t, e2, _) => {
            shape(syms, c, d + 1, out);
            shape(syms, t, d + 1, out);
            shape(syms, e2, d + 1, out);
        }
        Expr::Let(bs, body, _) => {
            if let Some(b) = bs.first() {
                shape(syms, &b.value, d + 1, out);
            }
            shape(syms, body, d + 1, out);
        }
        Expr::Apply(f, a, _) => {
            shape(syms, f, d + 1, out);
            shape(syms, a, d + 1, out);
        }
        Expr::Lambda(_, b, _) => shape(syms, b, d + 1, out),
        Expr::FieldAccess(r, _, _) => shape(syms, r, d + 1, out),
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    /// The IR text for one chapter, or the refusal.
    ///
    /// Through the real front end -- parse, desugar, emit -- because the point
    /// of these is the SPELLING that reaches the wire, and a unit test that
    /// built a `TypeExpr` by hand would be testing my idea of the AST rather
    /// than the one the parser makes.
    fn ir(src: &str) -> String {
        let bytes = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&bytes);
        let mut dg = crate::desugar::Desugar::new(&bytes);
        let ch = dg.chapter(&parsed.tree);
        match super::emit_defs(&ch) {
            Ok(s) => s,
            Err(e) => format!("REFUSED: {e}"),
        }
    }

    /// Just the one definition's line, which is what these are about.
    fn def_line(src: &str, name: &str) -> String {
        let all = ir(src);
        all.lines()
            .find(|l| l.contains(&format!("(def {name:?}")))
            .map(|l| l.trim().to_string())
            .unwrap_or(all)
    }

    const PURE: &str = "Chapter: T\n\nSection: S\n  f : Integer -> Integer\n  f (n) = n\n\n";

    /// **`[Console] Nothing` IS `(effectful (effs "Console") (scopes "") nothing)`.**
    ///
    /// `scopes` is PARALLEL TO `effs`, one string per effect and empty when the
    /// effect is unscoped -- read off real IR rather than guessed, where three
    /// effects print `(scopes "" "" "")`. Rendering it as a single empty list
    /// would be wrong for every multi-effect definition and right for the one
    /// a test would obviously reach for.
    #[test]
    fn an_effect_row_renders_with_a_scope_for_each_effect() {
        let src = format!(
            "{PURE}Section: E\n  opening : [Console] Nothing = act\n   f 1\n  end\n"
        );
        assert!(
            def_line(&src, "opening")
                .contains(r#"(effectful (effs "Console") (scopes "") nothing)"#),
            "got: {}",
            def_line(&src, "opening")
        );
    }

    #[test]
    fn two_effects_carry_two_scopes() {
        let src = format!(
            "{PURE}Section: E\n  opening : [Console, FileSystem] Nothing = act\n   f 1\n  end\n"
        );
        assert!(
            def_line(&src, "opening").contains(
                r#"(effectful (effs "Console" "FileSystem") (scopes "" "") nothing)"#
            ),
            "got: {}",
            def_line(&src, "opening")
        );
    }

    /// **AN `act` IS `(act (stmts ...) TYPE)` and each statement is wrapped.**
    /// `print-line-uni "a"` alone is one `do-exec`; the block's type is the
    /// type of what it ends with.
    #[test]
    fn an_act_block_wraps_its_statements() {
        let src = format!(
            "{PURE}Section: E\n  opening : [Console] Nothing = act\n   f 1\n   f 2\n  end\n"
        );
        let line = def_line(&src, "opening");
        assert!(line.contains("(act (stmts (do-exec "), "got: {line}");
        assert!(line.matches("(do-exec ").count() == 2, "one per statement: {line}");
        assert!(line.ends_with("int-default) 0 0)"), "the act ends with its last statement's type: {line}");
    }

    /// **THE ROW ID IS THE CHECKER'S, AND IT MOVES.** `print-line-uni` in a
    /// chapter that applies nothing before it takes row 0; the same call in
    /// fib takes row 6, because fib's own body left the counter there. The two
    /// assertions differ in one digit and that digit is the entire reason a
    /// static table could not answer this.
    ///
    /// Both read off `codexir` at `u56-candidate-sunday`. `f` is absent from
    /// each because nothing calls it.
    #[test]
    fn an_effectful_builtin_carries_the_row_the_checker_minted() {
        let src = format!(
            "{PURE}Section: E\n  opening : [Console] Nothing = act\n   print-line-uni \"a\"\n  end\n"
        );
        assert_eq!(
            def_line(&src, "opening"),
            r#"(def "opening" "T" (params) (effectful (effs "Console") (scopes "") nothing) (act (stmts (do-exec (apply (name "print-line-uni" (fn text nothing (row (labels (label "Console.Write" "")) "" 0))) (text-lit "a") nothing))) nothing) 0 0)"#
        );
    }

    /// **THE ORACLE'S OWN BYTES, FOR THE WHOLE SLICE SUBJECT.**
    ///
    /// `codexir < fib.codex` at `u56-candidate-sunday`, the two definition
    /// lines verbatim. Everything the native road was missing is in the
    /// `opening` line and nowhere else:
    ///
    ///   * `print-line-uni` carries the row the CHECKER minted -- id 6, which
    ///     is what fib's own body leaves the counter at -- and no static table
    ///     can answer that.
    ///   * `show` is `(fn int-default text)`: a `forall` instantiated to a
    ///     fresh variable, then UNIFIED with the argument through the
    ///     application. Rendering the declared type gives `(fn (tvar 4) text)`.
    ///   * every `apply` carries its RESOLVED result, which is the same
    ///     substitution read a second time.
    ///
    /// `double` is absent because nothing calls it and `ir-prune-unreachable-roots`
    /// runs before emission.
    #[test]
    fn fib_is_byte_identical_to_the_oracle() {
        let src = "Chapter: Fib\n\nSection: Math\n  fib : Integer -> Integer\n  fib (n) =\n   if n <= 1 then n\n   else fib (n - 1) + fib (n - 2)\n\n  double : Integer -> Integer\n  double (n) = n + n\n\nSection: Main\n  opening : [Console] Nothing = act\n   print-line-uni (show (fib 20))\n  end\n";
        assert_eq!(
            ir(src),
            "\n  (def \"fib\" \"Fib\" (params (param \"n\" int-default)) (fn int-default int-default) (if (binary le (name \"n\" int-default) (int-lit 1) boolean) (name \"n\" int-default) (binary add-int (apply (name \"fib\" (fn int-default int-default)) (binary sub-int (name \"n\" int-default) (int-lit 1) int-default) int-default) (apply (name \"fib\" (fn int-default int-default)) (binary sub-int (name \"n\" int-default) (int-lit 2) int-default) int-default) int-default) int-default) 0 0)\
             \n  (def \"opening\" \"Fib\" (params) (effectful (effs \"Console\") (scopes \"\") nothing) (act (stmts (do-exec (apply (name \"print-line-uni\" (fn text nothing (row (labels (label \"Console.Write\" \"\")) \"\" 6))) (apply (name \"show\" (fn int-default text)) (apply (name \"fib\" (fn int-default int-default)) (int-lit 20) int-default) text) nothing))) nothing) 0 0)"
        );
    }

    /// **A DOTTED EFFECT IS ONE NAME, AND A SCOPE BELONGS TO THE EFFECT IT
    /// FOLLOWS.** `[Device.Block]` is one effect; taking the identifiers and
    /// dropping the dots makes it two, pads `(scopes)` to match, and produces
    /// a signature no reader can resolve.
    ///
    /// Both lines are `codexir`'s at `u56-candidate-sunday`. The second is
    /// `[Console "stdout", FileSystem.Read "/config/"]`, which is the shape
    /// that needs the scope kept POSITIONAL: a scope in the middle of a row
    /// cannot be recovered by padding the end.
    #[test]
    fn an_effect_row_keeps_dotted_names_and_their_scopes() {
        let dotted = "Chapter: BlockIdentify\n\nSection: Body\n  opening : [Device.Block] Integer = block-sector-count\n";
        assert_eq!(
            def_line(dotted, "opening"),
            r#"(def "opening" "BlockIdentify" (params) (effectful (effs "Device.Block") (scopes "") int-default) (name "block-sector-count" int-default) 0 0)"#
        );

        let scoped = "Chapter: Sc\n\nSection: S\n  opening : [Console \"stdout\", FileSystem.Read \"/config/\"] Nothing = act\n   print-line-uni \"a\"\n  end\n";
        assert!(
            def_line(scoped, "opening").contains(
                r#"(effectful (effs "Console" "FileSystem.Read") (scopes "stdout" "/config/") nothing)"#
            ),
            "got: {}",
            def_line(scoped, "opening")
        );
    }

    /// **AN EMPTY LIST'S ELEMENT TYPE COMES FROM THE CONTEXT**, which is a
    /// variable the checker minted and unification decided. `codexir`'s bytes
    /// at `u56-candidate-sunday`, with `f` called twice so the single-caller
    /// pass leaves it standing.
    #[test]
    fn an_empty_list_carries_the_element_type_the_checker_decided() {
        let src = "Chapter: T\n\nSection: S\n  f : Integer -> List Integer\n  f (x) = []\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (list-length (f 1)))\n   print-line-uni (show (list-length (f 2)))\n  end\n";
        assert_eq!(
            def_line(src, "f"),
            r#"(def "f" "T" (params (param "x" int-default)) (fn int-default (list int-default)) (list-expr (elems) int-default) 0 0)"#
        );
    }

    /// **A POLYMORPHIC DEFINITION SPELLS THE TYPE ITS OWN BODY WAS CHECKED
    /// WITH.** `ident : List a -> List a` reaches the wire as
    /// `(fn (list (tvar 2)) (list (tvar 2)))` -- the variable
    /// `instantiate-collect` minted for it -- and its parameter carries the
    /// same. The generalised `forall` is what REFERENCES instantiate from; it
    /// has no arrow to peel, and lowering that instead refused every
    /// polymorphic definition in the corpus.
    ///
    /// `codexir`'s bytes at `u56-candidate-sunday`, with `ident` called twice
    /// so the single-caller pass leaves it standing. Note the call sites carry
    /// `int-default`, resolved, while the definition keeps its variable.
    #[test]
    fn a_polymorphic_definition_keeps_its_own_type_variable() {
        let src = "Chapter: T\n\nSection: S\n  ident : List a -> List a\n  ident (xs) = xs\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (list-length (ident [1])))\n   print-line-uni (show (list-length (ident [2])))\n  end\n";
        assert_eq!(
            def_line(src, "ident"),
            r#"(def "ident" "T" (params (param "xs" (list (tvar 2)))) (fn (list (tvar 2)) (list (tvar 2))) (name "xs" (list (tvar 2))) 0 0)"#
        );
        assert!(
            def_line(src, "opening")
                .contains(r#"(name "ident" (fn (list int-default) (list int-default)))"#),
            "the call site resolves: {}",
            def_line(src, "opening")
        );
    }

    /// **`-n` IS A NEGATE NODE; `0 - n` IS A BINARY.** The two spell
    /// differently on the wire even though a reader would call them the same
    /// expression, and the negate carries its OPERAND's type. `codexir`'s
    /// bytes, with `neg2` called twice so it survives the single-caller pass.
    #[test]
    fn a_unary_minus_is_a_negate_node() {
        let src = "Chapter: T\n\nSection: S\n  neg2 : Integer -> Integer\n  neg2 (n) = -n\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (neg2 1))\n   print-line-uni (show (neg2 2))\n  end\n";
        assert_eq!(
            def_line(src, "neg2"),
            r#"(def "neg2" "T" (params (param "n" int-default)) (fn int-default int-default) (negate (name "n" int-default) int-default) 0 0)"#
        );
    }

    /// **A RECORD LITERAL EMITS ITS FIELDS IN THE ORDER THE EXPRESSION WRITES
    /// THEM, AND A FIELD ACCESS CARRIES THE DECLARATION'S SLOT.** Both halves
    /// measured: `P { py = ..., px = ... }` emits `py` first even though the
    /// declaration puts `px` first, and `p.py` is `"py/1"` because `py` is
    /// declared second.
    #[test]
    fn a_record_writes_its_fields_in_expression_order_and_reads_them_by_slot() {
        let decl = "Chapter: T\n\nSection: S\n  P = record { px : Integer, py : Text }\n\n";
        let calls = "\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (getx (mk 1)))\n   print-line-uni (show (getx (mk 2)))\n  end\n";
        let src = format!(
            "{decl}  mk : Integer -> P\n  mk (a) = P {{ px = a, py = \"z\" }}\n\n  \
             getx : P -> Integer\n  getx (p) = p.px\n{calls}"
        );
        assert_eq!(
            def_line(&src, "mk"),
            r#"(def "mk" "T" (params (param "a" int-default)) (fn int-default (record-ty "P" (args))) (record "P" (fields (field-val "px" (name "a" int-default)) (field-val "py" (text-lit "z"))) (record-ty "P" (args))) 0 0)"#
        );
        assert_eq!(
            def_line(&src, "getx"),
            r#"(def "getx" "T" (params (param "p" (record-ty "P" (args)))) (fn (record-ty "P" (args)) int-default) (field-access (name "p" (record-ty "P" (args))) "px/0" int-default) 0 0)"#
        );

        // Written out of declaration order, and emitted the way it is written.
        let swapped = format!(
            "{decl}  mk : Integer -> P\n  mk (a) = P {{ py = \"z\", px = a }}\n\n  \
             getx : P -> Integer\n  getx (p) = p.px\n{calls}"
        );
        assert!(
            def_line(&swapped, "mk").contains(
                r#"(fields (field-val "py" (text-lit "z")) (field-val "px" (name "a" int-default)))"#
            ),
            "got: {}",
            def_line(&swapped, "mk")
        );
    }

    /// **A BOUNDED INTEGER MEETING AN ORDINARY ONE ANSWERS THE LEFT.**
    /// `b + 1` over `Integer between 0 and 255` is `(int 0 255 ov-error)`;
    /// `1 + b` is `int-default`. Not the wider, not the narrower -- the left.
    #[test]
    fn arithmetic_on_a_bounded_integer_answers_the_left_operand() {
        let calls = "\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (w 3))\n   print-line-uni (show (w 4))\n  end\n";
        let right = format!(
            "Chapter: T\n\nSection: S\n  w : Integer between 0 and 255 -> Integer\n  w (b) = b + 1\n{calls}"
        );
        assert_eq!(
            def_line(&right, "w"),
            r#"(def "w" "T" (params (param "b" (int 0 255 ov-error))) (fn (int 0 255 ov-error) int-default) (binary add-int (name "b" (int 0 255 ov-error)) (int-lit 1) (int 0 255 ov-error)) 0 0)"#
        );

        let left = format!(
            "Chapter: T\n\nSection: S\n  w : Integer between 0 and 255 -> Integer\n  w (b) = 1 + b\n{calls}"
        );
        assert!(
            def_line(&left, "w").contains(
                r#"(binary add-int (int-lit 1) (name "b" (int 0 255 ov-error)) int-default)"#
            ),
            "got: {}",
            def_line(&left, "w")
        );
    }

    /// **A CONSTRUCTOR PATTERN CARRIES THE SCRUTINEE'S TYPE, A WILDCARD IS A
    /// BARE ATOM, AND EVERY BRANCH HAS A GUARD.** An unguarded arm carries
    /// `(bool-lit true)`, which the desugarer put there -- and note the
    /// lowercase: the source spells the constructor `True`, the wire spells the
    /// value.
    #[test]
    fn a_match_spells_its_patterns_against_the_scrutinee() {
        let decl = "Chapter: T\n\nSection: S\n  M =\n    | Some (Integer)\n    | Nowt\n\n";
        let calls = "\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (unwrap (Some 1)))\n   print-line-uni (show (unwrap Nowt))\n  end\n";
        let src = format!(
            "{decl}  unwrap : M -> Integer\n  unwrap (m) = when m\n    is Some (x) -> x\n    is Nowt -> 0\n{calls}"
        );
        assert_eq!(
            def_line(&src, "unwrap"),
            r#"(def "unwrap" "T" (params (param "m" (sum "M" (args)))) (fn (sum "M" (args)) int-default) (match (name "m" (sum "M" (args))) (branches (branch (ctor-pat "Some" (subs (var-pat "x" int-default)) (sum "M" (args))) (name "x" int-default) (bool-lit true)) (branch (ctor-pat "Nowt" (subs) (sum "M" (args))) (int-lit 0) (bool-lit true))) int-default) 0 0)"#
        );

        let wild = format!(
            "{decl}  unwrap : M -> Integer\n  unwrap (m) = when m\n    is Some (x) -> x\n    is otherwise -> 7\n{calls}"
        );
        assert!(
            def_line(&wild, "unwrap").contains("(branch wild-pat (int-lit 7) (bool-lit true))"),
            "got: {}",
            def_line(&wild, "unwrap")
        );
    }

    /// `True` in source is `true` on the wire -- the source names the
    /// constructor, the wire carries the value.
    #[test]
    fn a_boolean_literal_is_lowercase_on_the_wire() {
        let src = "Chapter: T\n\nSection: S\n  yes : Integer -> Boolean\n  yes (n) = True\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (yes 1))\n   print-line-uni (show (yes 2))\n  end\n";
        assert_eq!(
            def_line(src, "yes"),
            r#"(def "yes" "T" (params (param "n" int-default)) (fn int-default boolean) (bool-lit true) 0 0)"#
        );
    }

    /// **ONE TOKEN, THREE ATOMS.** `&` is `and` over Booleans, `append-text`
    /// over Text and `append-list` over a List, and the OPERAND type picks.
    /// Inferring Boolean for it unconditionally made `a & b & "!"` see a
    /// Boolean meeting a Text at the second `&` -- a disagreement that is not
    /// in the program.
    #[test]
    fn the_ampersand_is_three_operators() {
        let src = "Chapter: T\n\nSection: S\n  j : Text, Text -> Text\n  j (a) (b) = a & b & \"!\"\n\n  k : Boolean, Boolean -> Boolean\n  k (a) (b) = a & b\n\n  l : List Integer, List Integer -> List Integer\n  l (a) (b) = a & b\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (j \"x\" \"y\")\n   print-line-uni (show (k True False))\n   print-line-uni (show (list-length (l [1] [2])))\n   print-line-uni (j \"p\" \"q\")\n  end\n";
        assert!(def_line(src, "j").contains("(binary append-text (binary append-text"), "{}", def_line(src, "j"));
        assert!(def_line(src, "k").contains("(binary and "), "{}", def_line(src, "k"));
        assert!(def_line(src, "l").contains("(binary append-list "), "{}", def_line(src, "l"));
    }

    /// A pure definition still renders exactly as it did, which is the thing
    /// these changes must not disturb: it is already byte-identical to the
    /// oracle and that is the only verified ground the native road stands on.
    #[test]
    fn a_pure_definition_is_unchanged() {
        let src = "Chapter: Fib\n\nSection: M\n  fib : Integer -> Integer\n  fib (n) =\n   if n <= 1 then n\n   else fib (n - 1) + fib (n - 2)\n\nSection: E\n  opening : Integer\n  opening = fib 20\n";
        assert_eq!(
            def_line(src, "fib"),
            r#"(def "fib" "Fib" (params (param "n" int-default)) (fn int-default int-default) (if (binary le (name "n" int-default) (int-lit 1) boolean) (name "n" int-default) (binary add-int (apply (name "fib" (fn int-default int-default)) (binary sub-int (name "n" int-default) (int-lit 1) int-default) int-default) (apply (name "fib" (fn int-default int-default)) (binary sub-int (name "n" int-default) (int-lit 2) int-default) int-default) int-default) int-default) 0 0)"#
        );
    }
}

// ---------------------------------------------------------------------------
// Lambda lifting -- `lift-lambdas` (LambdaLifting.codex:19)
// ---------------------------------------------------------------------------
//
// A lambda never reaches the IR text as a lambda. `lift-lambdas` runs between
// lowering and emission and rewrites every one into a TOP-LEVEL definition
// named `__lam_N`, appended after the chapter's own defs with an empty
// chapter-slug, plus a reference to it at the site the lambda stood.
//
// Three things about it are load-bearing and none is guessable:
//
//   * **The name is allocated AFTER the body is lifted**, so a nested lambda
//     gets the LOWER number. `lift-one-lambda` lifts the body, then calls
//     `gen-unique-name`.
//   * **Numbering runs over the WHOLE chapter, before pruning.** The driver
//     writes `emit-ir-chapter (ir-prune-unreachable-roots lifted-ir ...)`, so
//     a lambda inside a definition the gold never shows still consumed a
//     number. That is why the counter is assigned by a pre-pass over
//     `ch.defs` rather than as the emitter walks the definitions it keeps.
//   * **Captured variables become the LEADING parameters, sorted by name**,
//     and the reference site is a partial application over them.
//
// A definition whose body IS a lambda is not lifted at all:
// `absorb-outer-lambdas` merges those parameters into the definition's own.

/// Every lambda in the chapter, keyed by `expr_type_key` of its span, mapped
/// to the `__lam_N` it will be lifted to.
///
/// `collect-reserved-names` seeds the reserved set with every definition name,
/// so a chapter that already defines `__lam_0` pushes the first lambda to
/// `__lam_1`. Contrived, and one line.
fn lambda_names(ch: &Chapter) -> BTreeMap<u64, String> {
    let mut reserved: std::collections::BTreeSet<String> =
        ch.defs.iter().map(|d| ch.syms.text(d.name).to_string()).collect();
    let mut counter: u32 = 0;
    let mut out = BTreeMap::new();
    for d in &ch.defs {
        number_lambdas(absorbed_body(&d.body), &mut reserved, &mut counter, &mut out);
    }
    out
}

/// `absorb-outer-lambdas`: the body under any lambdas a definition wears
/// directly, whose parameters are the definition's own.
fn absorbed_body(body: &Expr) -> &Expr {
    let mut b = body;
    while let Expr::Lambda(_, inner, _) = b {
        b = inner;
    }
    b
}

/// `gen-unique-name-loop`: the first `__lam_N` nothing has taken, and the
/// counter resumes past it.
fn gen_lam_name(reserved: &mut std::collections::BTreeSet<String>, counter: &mut u32) -> String {
    loop {
        let cand = format!("__lam_{}", *counter);
        *counter += 1;
        if reserved.insert(cand.clone()) {
            return cand;
        }
    }
}

/// `lift-expr`'s traversal, for numbering alone. The ORDER is the whole point,
/// so this mirrors the arms rather than reusing `Expr::walk` -- that one is
/// pre-order and would number a lambda before its own body.
fn number_lambdas(
    e: &Expr,
    reserved: &mut std::collections::BTreeSet<String>,
    counter: &mut u32,
    out: &mut BTreeMap<u64, String>,
) {
    use crate::ast::ActStmt;
    let mut go = |x: &Expr| number_lambdas(x, reserved, counter, out);
    match e {
        Expr::Lit(..) | Expr::NameRef(..) | Expr::Error(..) => {}
        Expr::Lambda(_, body, sp) => {
            // A curried chain is ONE lifted definition: `lift-one-lambda`
            // recurses on an `IrLambda` body with the parameters concatenated.
            number_lambdas(absorbed_body(body), reserved, counter, out);
            let n = gen_lam_name(reserved, counter);
            out.insert(crate::check::expr_type_key(*sp), n);
        }
        Expr::Apply(a, b, _) | Expr::Binary(a, _, b, _) | Expr::FieldAssign(a, _, b, _) => {
            go(a);
            go(b);
        }
        Expr::Unary(a, _) | Expr::Lazy(a, _) | Expr::FieldAccess(a, _, _) => go(a),
        Expr::If(a, b, c, _) => {
            go(a);
            go(b);
            go(c);
        }
        Expr::Let(bs, body, _) => {
            for b in bs {
                go(&b.value);
            }
            go(body);
        }
        // `lift-branches` takes the body before the guard.
        Expr::Match(s, arms, _) | Expr::Induction(s, arms, _) => {
            go(s);
            for a in arms {
                go(&a.body);
                go(&a.guard);
            }
        }
        Expr::List(xs, _) => xs.iter().for_each(go),
        Expr::Record(_, fs, _) => fs.iter().for_each(|f| go(&f.value)),
        Expr::Act(ss, _) => ss.iter().for_each(|s| match s {
            ActStmt::Bind(_, v, _) | ActStmt::Exec(v, _) => go(v),
        }),
        Expr::Handle(h) => {
            go(&h.body);
            h.clauses.iter().for_each(|c| go(&c.body));
        }
        Expr::WithTimeout(w) => go(&w.body),
        Expr::Try(t) => {
            for group in [&t.body, &t.fallback, &t.failure] {
                group.iter().for_each(|s| match s {
                    ActStmt::Bind(_, v, _) | ActStmt::Exec(v, _) => go(v),
                });
            }
        }
    }
}

/// Every name a pattern binds, for the branch's `enclosing` set.
fn pat_names(p: &crate::ast::Pat, out: &mut Vec<Sym>) {
    use crate::ast::Pat as P;
    match p {
        P::Var(n, _) => out.push(*n),
        P::Wild(..) | P::Lit(..) => {}
        P::Ctor(_, subs, _) | P::Vec_(subs, _) => subs.iter().for_each(|s| pat_names(s, out)),
    }
}

/// `collect-free-vars`: the names this body reads that the ENCLOSING scope
/// binds and the lambda's own parameters do not.
///
/// A global -- another definition, a builtin -- is never captured, which falls
/// out of `capturable` holding only local binders. The type is the one the
/// checker recorded at the FIRST occurrence, because `free-var-has` stops the
/// second from replacing it.
fn free_vars(
    e: &Expr,
    bound: &mut Vec<Sym>,
    capturable: &[Sym],
    cx: &Lower,
    out: &mut BTreeMap<String, (Sym, Ty)>,
) -> Result<(), String> {
    use crate::ast::ActStmt;
    match e {
        Expr::NameRef(n, sp) => {
            if capturable.contains(n) && !bound.contains(n) {
                let key = cx.syms.text(*n).to_string();
                if !out.contains_key(&key) {
                    let t = cx.at(*sp).ok_or_else(|| {
                        format!("no recorded type for the captured `{}`", cx.syms.text(*n))
                    })?;
                    out.insert(key, (*n, t));
                }
            }
        }
        Expr::Lit(..) | Expr::Error(..) => {}
        Expr::Lambda(ps, body, _) => {
            let n = bound.len();
            bound.extend(ps.iter().copied());
            free_vars(body, bound, capturable, cx, out)?;
            bound.truncate(n);
        }
        Expr::Apply(a, b, _) | Expr::Binary(a, _, b, _) | Expr::FieldAssign(a, _, b, _) => {
            free_vars(a, bound, capturable, cx, out)?;
            free_vars(b, bound, capturable, cx, out)?;
        }
        Expr::Unary(a, _) | Expr::Lazy(a, _) | Expr::FieldAccess(a, _, _) => {
            free_vars(a, bound, capturable, cx, out)?
        }
        Expr::If(a, b, c, _) => {
            free_vars(a, bound, capturable, cx, out)?;
            free_vars(b, bound, capturable, cx, out)?;
            free_vars(c, bound, capturable, cx, out)?;
        }
        Expr::Let(bs, body, _) => {
            let n = bound.len();
            for b in bs {
                free_vars(&b.value, bound, capturable, cx, out)?;
                bound.push(b.name);
            }
            free_vars(body, bound, capturable, cx, out)?;
            bound.truncate(n);
        }
        Expr::Match(s, arms, _) | Expr::Induction(s, arms, _) => {
            free_vars(s, bound, capturable, cx, out)?;
            for a in arms {
                let n = bound.len();
                pat_names(&a.pattern, bound);
                free_vars(&a.body, bound, capturable, cx, out)?;
                free_vars(&a.guard, bound, capturable, cx, out)?;
                bound.truncate(n);
            }
        }
        Expr::List(xs, _) => {
            for x in xs {
                free_vars(x, bound, capturable, cx, out)?;
            }
        }
        Expr::Record(_, fs, _) => {
            for f in fs {
                free_vars(&f.value, bound, capturable, cx, out)?;
            }
        }
        Expr::Act(ss, _) => {
            let n = bound.len();
            for s in ss {
                match s {
                    ActStmt::Bind(nm, v, _) => {
                        free_vars(v, bound, capturable, cx, out)?;
                        bound.push(*nm);
                    }
                    ActStmt::Exec(v, _) => free_vars(v, bound, capturable, cx, out)?,
                }
            }
            bound.truncate(n);
        }
        Expr::Handle(h) => {
            free_vars(&h.body, bound, capturable, cx, out)?;
            for c in &h.clauses {
                let n = bound.len();
                bound.push(c.resume_name);
                free_vars(&c.body, bound, capturable, cx, out)?;
                bound.truncate(n);
            }
        }
        Expr::WithTimeout(w) => free_vars(&w.body, bound, capturable, cx, out)?,
        Expr::Try(t) => {
            for group in [&t.body, &t.fallback, &t.failure] {
                let n = bound.len();
                for s in group {
                    match s {
                        ActStmt::Bind(nm, v, _) => {
                            free_vars(v, bound, capturable, cx, out)?;
                            bound.push(*nm);
                        }
                        ActStmt::Exec(v, _) => free_vars(v, bound, capturable, cx, out)?,
                    }
                }
                bound.truncate(n);
            }
        }
    }
    Ok(())
}
