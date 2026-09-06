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
use crate::check::{Binding, Overflow, RealMode, RealWidth, Ty, UnifyState};
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
    /// This chapter's own definitions, keyed by name, for the `(def ...)`
    /// headers. Bodies do not consult it.
    bindings: BTreeMap<Sym, Ty>,
}

impl<'a> Lower<'a> {
    pub fn new(ch: &'a Chapter, bindings: &[Binding], st: &'a UnifyState) -> Lower<'a> {
        Lower {
            syms: &ch.syms,
            st,
            bindings: bindings.iter().map(|b| (b.name, b.ty.clone())).collect(),
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
        Expr::Lit(v, LiteralKind::BoolLit, _) => Ok((format!("(bool-lit {v})"), Ty::Boolean)),
        Expr::Lit(_, k, _) => Err(format!("literal kind {k:?}")),
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
            if lty != rty {
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
                BinaryOp::OpAnd | BinaryOp::OpBoolAnd => ("and".into(), Ty::Boolean),
                BinaryOp::OpOr => ("or".into(), Ty::Boolean),
                BinaryOp::OpAppend => match &lty {
                    Ty::Text => ("append-text".to_string(), lty.clone()),
                    Ty::List(_) => ("append-list".to_string(), lty.clone()),
                    other => {
                        return Err(format!("append on `{}`", render_ty(cx.syms, other)))
                    }
                },
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
        Expr::List(xs, _) => {
            if xs.is_empty() {
                return Err("empty list literal (its type is in the context)".into());
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
            let mut heads = Vec::new();
            for b in binds {
                let (vt, vty) = expr(&b.value, cx)?;
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
        other => Err(node_kind(other).to_string()),
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
    let (bindings, st) = crate::check::check_chapter(ch);
    emit_defs_checked(ch, &bindings, &st, &IR_EMIT_ROOTS)
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
    roots: &[&str],
) -> Result<String, String> {
    let keep = reachable(ch, roots);
    if keep.is_empty() {
        return Err("no root reached: the chapter defines none of ir-emit-roots".into());
    }
    let cx = Lower::new(ch, bindings, st);
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
        for p in &d.params {
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
                ch.syms.text(p.name),
                render_ty(&ch.syms, &arg)
            ));
            rest = res;
        }
        let (body, _bty) =
            expr(&d.body, &cx).map_err(|r| format!("{}: {r}", ch.syms.text(d.name)))?;
        out.push_str(&format!(
            "\n  (def {:?} {:?} (params{}) {} {} 0 0)",
            ch.syms.text(d.name), d.chapter_slug, params, declared, body
        ));
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
    let defs: Vec<&crate::ast::Def> = ch.defs.iter().collect();
    let mut s = String::from("--- lower ---\n");
    s.push_str(&format!("ir-name |{}|\n", ch.syms.text(ch.name)));
    s.push_str(&format!("ir-defs {}\n", defs.len()));
    s.push_str("ir-eff-ops 0\n.\n");
    for d in &defs {
        let ty = d
            .declared_type
            .first()
            .and_then(|t| crate::check::resolve_declared(&ch.syms, t))
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
        assert!(
            def_line(dotted, "opening")
                .contains(r#"(effectful (effs "Device.Block") (scopes "") int-default)"#),
            "got: {}",
            def_line(dotted, "opening")
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
