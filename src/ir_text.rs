//! IR text -- `Emit/IRTextEmitter.codex`.
//!
//! The tree in, the wire out. Nothing here decides anything: every type is
//! already on its node and every operator already chosen, because a spelling
//! that depended on a decision made HERE would be a decision the optimisation
//! passes never saw. That separation is the point of having a tree at all.
//!
//! **A near miss is worth less than nothing.** The gate is byte-identity
//! against a document of nested s-expressions, so a wrong space or a dropped
//! quote reads exactly like a wrong type until someone diffs 900 bytes.

use crate::check::{Overflow, RealMode, RealWidth, Ty};
use crate::ir_chapter::{IrActStmt, IrDef, IrExpr, IrPat};
use crate::symbol::{Sym, SymTab};

/// `safe-int-text` (IRTextEmitter.codex:112). **`i64::MIN` IS A SENTINEL
/// ATOM ON THIS WIRE**, not a number.
///
/// Upstream's reason is its own: `__itoa` negates a negative input into a
/// positive register before its digit loop, and `abs(i64-min)` overflows, so
/// the emitter cannot spell it. Ours has no such trouble and must print
/// `i64-min` anyway, because the plug parsers on the far side read the atom.
///
/// Four sites spell an integer on this wire and all four go through here:
/// the two bounds of `(int lo hi mode)`, the two of `(a-bounded ...)`, and
/// `(int-lit n)` / `(num-lit n)`.
pub fn safe_int_text(n: i64) -> String {
    if n == i64::MIN {
        "i64-min".into()
    } else {
        n.to_string()
    }
}

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
            "(int {} {} {})",
            safe_int_text(*lo),
            safe_int_text(*hi),
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

/// One expression, as the wire spells it -- `ir-emit-expr` (line 370).
pub fn emit_expr(syms: &SymTab, e: &IrExpr) -> String {
    use IrExpr as E;
    let q = |n: Sym| format!("{:?}", syms.text(n));
    let t = |x: &Ty| render_ty(syms, x);
    let sub = |x: &IrExpr| emit_expr(syms, x);
    match e {
        // A literal carries no type on the wire: `(int-lit 1)`, never
        // `(int-lit 1 int-default)`.
        E::IntLit(v, _) => format!("(int-lit {})", safe_int_text(*v)),
        E::NumLit(v, _) => format!("(num-lit {})", safe_int_text(*v)),
        // `ir-quote` (line 71). The literal arrives DECODED, and only three
        // characters are escaped on the way back out -- backslash, quote and
        // newline. A tab does not appear in the list because a tab cannot
        // reach here: `\t` decoded to two spaces.
        E::TextLit(v, _) => format!("(text-lit {})", ir_quote(v)),
        // **`true`, NOT `True`.** The source spells the constructor and the
        // wire spells the value.
        E::BoolLit(b, _) => format!("(bool-lit {})", if *b { "true" } else { "false" }),
        E::CharLit(c, _) => format!("(char-lit {c})"),
        E::Name(n, ty, _) => format!("(name {} {})", q(*n), t(ty)),
        E::Binary(op, l, r, ty, _) => {
            format!("(binary {} {} {} {})", op.atom_typed(ty), sub(l), sub(r), t(ty))
        }
        E::Negate(x, ty, _) => format!("(negate {} {})", sub(x), t(ty)),
        E::If(c, th, el, ty, _) => {
            format!("(if {} {} {} {})", sub(c), sub(th), sub(el), t(ty))
        }
        E::Let(n, ty, v, b, _) => {
            format!("(let {} {} {} {})", q(*n), t(ty), sub(v), sub(b))
        }
        E::Apply(f, a, ty, _) => format!("(apply {} {} {})", sub(f), sub(a), t(ty)),
        E::Lambda(ps, b, ty, _) => {
            format!("(lambda (params{}) {} {})", emit_params(syms, ps), sub(b), t(ty))
        }
        // The trailing type is the ELEMENT's, not the list's.
        E::List(xs, elem, _) => format!(
            "(list-expr (elems{}) {})",
            xs.iter().map(|x| format!(" {}", sub(x))).collect::<String>(),
            t(elem)
        ),
        E::Match(sc, bs, ty, _) => format!(
            "(match {} (branches{}) {})",
            sub(sc),
            bs.iter()
                .map(|b| format!(
                    " (branch {} {} {})",
                    emit_pat(syms, &b.pattern),
                    sub(&b.body),
                    sub(&b.guard)
                ))
                .collect::<String>(),
            t(ty)
        ),
        E::Act(ss, ty, _) => format!(
            "(act (stmts{}) {})",
            ss.iter()
                .map(|s| match s {
                    IrActStmt::Exec(x, _) => format!(" (do-exec {})", sub(x)),
                    IrActStmt::Bind(n, bty, x, _) =>
                        format!(" (do-bind {} {} {})", q(*n), t(bty), sub(x)),
                })
                .collect::<String>(),
            t(ty)
        ),
        // The fields are emitted IN THE ORDER THE EXPRESSION WRITES THEM, not
        // the order the record declares them -- measured, because the reverse
        // is the obvious guess and it is wrong.
        E::Record(n, fs, ty, _) => format!(
            "(record {} (fields{}) {})",
            q(*n),
            fs.iter()
                .map(|f| format!(" (field-val {} {})", q(f.name), sub(&f.value)))
                .collect::<String>(),
            t(ty)
        ),
        E::FieldAccess(r, slot, ty, _) => {
            format!("(field-access {} {:?} {})", sub(r), slot, t(ty))
        }
        E::FieldStore(r, slot, v, ty, _) => {
            format!("(field-store {} {:?} {} {})", sub(r), slot, sub(v), t(ty))
        }
    }
}

/// A wildcard is the bare atom `wild-pat`, with no parentheses and no type.
pub fn emit_pat(syms: &SymTab, p: &IrPat) -> String {
    match p {
        IrPat::Wild(_) => "wild-pat".into(),
        IrPat::Var(n, ty, _) => {
            format!("(var-pat {:?} {})", syms.text(*n), render_ty(syms, ty))
        }
        IrPat::Lit(v, ty, _) => format!("(lit-pat {} {})", ir_quote(v), render_ty(syms, ty)),
        IrPat::Ctor(n, subs, ty, _) => format!(
            "(ctor-pat {:?} (subs{}) {})",
            syms.text(*n),
            subs.iter().map(|s| format!(" {}", emit_pat(syms, s))).collect::<String>(),
            render_ty(syms, ty)
        ),
        IrPat::Vec_(subs, ty, _) => format!(
            "(vec-pat (subs{}) {})",
            subs.iter().map(|s| format!(" {}", emit_pat(syms, s))).collect::<String>(),
            render_ty(syms, ty)
        ),
    }
}

fn emit_params(syms: &SymTab, ps: &[crate::ir_chapter::IrParam]) -> String {
    ps.iter()
        .map(|p| format!(" (param {:?} {})", syms.text(p.name), render_ty(syms, &p.ty)))
        .collect()
}

/// One definition line. The two trailing numbers are `is-punctual` and
/// `wcet-budget` (`ir-emit-def`, subject 58000).
pub fn emit_def(syms: &SymTab, d: &IrDef) -> String {
    format!(
        "\n  (def {:?} {:?} (params{}) {} {} {} {})",
        syms.text(d.name),
        d.chapter_slug,
        emit_params(syms, &d.params),
        render_ty(syms, &d.ty),
        emit_expr(syms, &d.body),
        i32::from(d.is_punctual),
        d.wcet_budget
    )
}

/// The `(defs ...)` body: every definition, in order.
pub fn emit_defs(syms: &SymTab, defs: &[IrDef]) -> String {
    defs.iter().map(|d| emit_def(syms, d)).collect()
}

/// `ir-quote` (IRTextEmitter.codex:71). **THREE ESCAPES AND NO MORE.** Rust's
/// own `{:?}` is close but not the same -- it also escapes tabs, carriage
/// returns and every non-printable as `\u{..}` -- so this is written out
/// rather than borrowed.
fn ir_quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}
