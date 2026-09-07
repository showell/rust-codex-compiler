//! The RESOLVE phase -- `Parsmi--Resolve Types`, a chapter of its own upstream
//! and a pass of its own here.
//!
//! **A BARE CONSTRUCTED TYPE IS A NAME, NOT AN ANSWER.** `ConstructedTy "Foo"
//! []` is what the checker writes for any uppercase name it has nowhere better
//! to put -- a builtin's declared type says `List TypeBinding` and means
//! whatever this unit declares `TypeBinding` to be. Nothing in the checker
//! rewrites it, because nothing in the checker has both the type-def map and
//! the finished IR at once. This pass has both, and it runs over every type on
//! every node before the lift.
//!
//! It is the difference between `(ctd "TypeBinding" (args))` and
//! `(record-ty "TypeBinding" (args))` on the wire, and the two are not
//! interchangeable to a consumer: the record spelling carries the arity.
//!
//! Reproduced in six lines against `codexir`: a program using
//! `__self-type-defs` says `ctd` when nothing declares `TypeBinding`, `sum`
//! when a variant declares it, and `record-ty` with the declaration's own type
//! arguments when a record does.

use crate::check::Ty;
use crate::ir_chapter::{IrActStmt, IrBranch, IrDef, IrExpr, IrFieldVal, IrParam, IrPat};
use crate::symbol::{Sym, SymTab};
use std::collections::BTreeMap;

/// `sort-bindings (type-map & all-bindings)`: the chapter's type declarations
/// and every name the checker gave a type, in one table. The type map wins a
/// collision, which is what the concatenation order says.
pub type TypeMap = BTreeMap<Sym, Ty>;

/// `strip-fun-args-resolve`. **NOT `strip-fun-args`** -- this one does not
/// look through a quantifier, only through arrows. A name bound to a
/// constructor FUNCTION resolves to what that function returns.
fn strip_fun_args(t: &Ty) -> Ty {
    match t {
        Ty::Fun(_, _, r) => strip_fun_args(r),
        other => other.clone(),
    }
}

/// `resolve-ty-deep`.
///
/// A `ConstructedTy` WITH arguments keeps its head and resolves its arguments;
/// only a bare one is looked up. A record or a sum is returned untouched --
/// they are not in the walk at all, so a declared type's own arguments and
/// fields are never rewritten.
pub fn resolve_ty_deep(syms: &SymTab, m: &TypeMap, t: &Ty) -> Ty {
    let go = |x: &Ty| resolve_ty_deep(syms, m, x);
    match t {
        Ty::Constructed(n, args) if !args.is_empty() => {
            Ty::Constructed(*n, args.iter().map(go).collect())
        }
        Ty::Constructed(n, _) => match m.get(n) {
            Some(r @ (Ty::Record(..) | Ty::Sum(..))) => r.clone(),
            Some(f @ Ty::Fun(..)) => strip_fun_args(f),
            _ => Ty::Constructed(*n, Vec::new()),
        },
        Ty::Fun(p, row, r) => Ty::Fun(Box::new(go(p)), row.clone(), Box::new(go(r))),
        Ty::List(e) => Ty::List(Box::new(go(e))),
        Ty::LinkedList(e) => Ty::LinkedList(Box::new(go(e))),
        Ty::ForAll(i, b) => Ty::ForAll(*i, Box::new(go(b))),
        Ty::ForAllEff(i, b) => Ty::ForAllEff(*i, Box::new(go(b))),
        Ty::Effectful(e, sc, r) => Ty::Effectful(e.clone(), sc.clone(), Box::new(go(r))),
        Ty::Unit(n, inner) => Ty::Unit(*n, Box::new(go(inner))),
        Ty::Vector(n, e) => Ty::Vector(*n, Box::new(go(e))),
        Ty::TypeApply(f, a) => {
            let (rf, ra) = (go(f), go(a));
            match rf {
                Ty::TypeCon(n) if syms.text(n) == "List" => Ty::List(Box::new(ra)),
                Ty::TypeCon(n) => Ty::Constructed(n, vec![ra]),
                other => Ty::TypeApply(Box::new(other), Box::new(ra)),
            }
        }
        // A linear type is TRANSPARENT here, as it is on the wire.
        Ty::Linear(inner) => go(inner),
        other => other.clone(),
    }
}

fn pat(syms: &SymTab, m: &TypeMap, p: &IrPat) -> IrPat {
    let t = |x: &Ty| resolve_ty_deep(syms, m, x);
    match p {
        IrPat::Var(n, ty, s) => IrPat::Var(*n, t(ty), *s),
        IrPat::Lit(v, ty, s) => IrPat::Lit(v.clone(), t(ty), *s),
        IrPat::Ctor(n, subs, ty, s) => {
            IrPat::Ctor(*n, subs.iter().map(|x| pat(syms, m, x)).collect(), t(ty), *s)
        }
        IrPat::Vec_(subs, ty, s) => {
            IrPat::Vec_(subs.iter().map(|x| pat(syms, m, x)).collect(), t(ty), *s)
        }
        IrPat::Wild(s) => IrPat::Wild(*s),
    }
}

fn expr(syms: &SymTab, m: &TypeMap, e: &IrExpr) -> IrExpr {
    use IrExpr as E;
    let t = |x: &Ty| resolve_ty_deep(syms, m, x);
    let go = |x: &IrExpr| Box::new(expr(syms, m, x));
    match e {
        E::IntLit(..) | E::NumLit(..) | E::TextLit(..) | E::BoolLit(..) | E::CharLit(..) => {
            e.clone()
        }
        E::Name(n, ty, s) => E::Name(*n, t(ty), *s),
        E::Binary(op, l, r, ty, s) => E::Binary(*op, go(l), go(r), t(ty), *s),
        E::Negate(x, ty, s) => E::Negate(go(x), t(ty), *s),
        E::If(c, th, el, ty, s) => E::If(go(c), go(th), go(el), t(ty), *s),
        E::Let(n, ty, v, b, s) => E::Let(*n, t(ty), go(v), go(b), *s),
        E::Apply(f, a, ty, s) => E::Apply(go(f), go(a), t(ty), *s),
        E::Lambda(ps, b, ty, s) => E::Lambda(
            ps.iter()
                .map(|p| IrParam { name: p.name, ty: t(&p.ty), span: p.span })
                .collect(),
            go(b),
            t(ty),
            *s,
        ),
        E::List(xs, ty, s) => {
            E::List(xs.iter().map(|x| expr(syms, m, x)).collect(), t(ty), *s)
        }
        E::Match(sc, bs, ty, s) => E::Match(
            go(sc),
            bs.iter()
                .map(|b| IrBranch {
                    pattern: pat(syms, m, &b.pattern),
                    body: expr(syms, m, &b.body),
                    guard: expr(syms, m, &b.guard),
                    span: b.span,
                })
                .collect(),
            t(ty),
            *s,
        ),
        E::Act(ss, ty, s) => E::Act(
            ss.iter()
                .map(|st| match st {
                    IrActStmt::Bind(n, bt, v, sp) => {
                        IrActStmt::Bind(*n, t(bt), expr(syms, m, v), *sp)
                    }
                    IrActStmt::Exec(v, sp) => IrActStmt::Exec(expr(syms, m, v), *sp),
                })
                .collect(),
            t(ty),
            *s,
        ),
        E::Record(n, fs, ty, s) => E::Record(
            *n,
            fs.iter()
                .map(|f| IrFieldVal { name: f.name, value: expr(syms, m, &f.value) })
                .collect(),
            t(ty),
            *s,
        ),
        E::FieldAccess(r, f, ty, s) => E::FieldAccess(go(r), f.clone(), t(ty), *s),
        E::FieldStore(r, f, v, ty, s) => E::FieldStore(go(r), f.clone(), go(v), t(ty), *s),
    }
}

/// `rewrite-ir-defs`: every type on every node of every definition.
pub fn resolve_defs(defs: Vec<IrDef>, syms: &SymTab, m: &TypeMap) -> Vec<IrDef> {
    defs.into_iter()
        .map(|d| IrDef {
            params: d
                .params
                .iter()
                .map(|p| IrParam {
                    name: p.name,
                    ty: resolve_ty_deep(syms, m, &p.ty),
                    span: p.span,
                })
                .collect(),
            ty: resolve_ty_deep(syms, m, &d.ty),
            body: expr(syms, m, &d.body),
            ..d
        })
        .collect()
}

/// The lookup's three answers, and the one it declines.
#[cfg(test)]
mod what_a_bare_name_resolves_to {
    use super::{resolve_ty_deep, TypeMap};
    use crate::check::Ty;
    use crate::symbol::SymTab;

    #[test]
    fn a_record_a_sum_a_constructor_and_nothing() {
        let mut syms = SymTab::default();
        let (rec, sum, ctor, gone) =
            (syms.intern("R"), syms.intern("S"), syms.intern("C"), syms.intern("G"));
        let mut m = TypeMap::new();
        m.insert(rec, Ty::Record(rec, Vec::new()));
        m.insert(sum, Ty::Sum(sum, Vec::new()));
        // A name bound to a CONSTRUCTOR resolves to what that constructor
        // returns, not to the arrow.
        m.insert(
            ctor,
            Ty::Fun(Box::new(Ty::Text), Default::default(), Box::new(Ty::Record(rec, Vec::new()))),
        );
        let bare = |n| Ty::Constructed(n, Vec::new());
        assert_eq!(resolve_ty_deep(&syms, &m, &bare(rec)), Ty::Record(rec, Vec::new()));
        assert_eq!(resolve_ty_deep(&syms, &m, &bare(sum)), Ty::Sum(sum, Vec::new()));
        assert_eq!(resolve_ty_deep(&syms, &m, &bare(ctor)), Ty::Record(rec, Vec::new()));
        // Nothing declares `G`, so it stays the name it was.
        assert_eq!(resolve_ty_deep(&syms, &m, &bare(gone)), bare(gone));
    }

    #[test]
    fn a_constructed_type_with_arguments_keeps_its_head() {
        let mut syms = SymTab::default();
        let (maybe, rec) = (syms.intern("Maybe"), syms.intern("R"));
        let mut m = TypeMap::new();
        m.insert(rec, Ty::Record(rec, Vec::new()));
        let t = Ty::Constructed(maybe, vec![Ty::Constructed(rec, Vec::new())]);
        assert_eq!(
            resolve_ty_deep(&syms, &m, &t),
            Ty::Constructed(maybe, vec![Ty::Record(rec, Vec::new())])
        );
    }
}
