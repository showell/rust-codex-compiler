//! Lowering's type arithmetic -- `LoweringTypes.codex`, plus the three
//! predicates in `Lowering.codex` that only these callers use.
//!
//! ## The wire's type is not the checker's answer
//!
//! The checker unifies, so after it runs a branch of an `if` and the `if`
//! itself have ONE type. The wire does not: `guarded-field`'s then-branch is
//! `(int 0 15 ov-error)`, its else-branch is `(int-lit 0)` and the `if` around
//! them is `int-default`. Three types, all correct, none derived from the
//! others.
//!
//! They come from the EXPECTED type instead -- what `lower-expr`'s second
//! argument carries down from the definition's declared return type. So an
//! emitter that reads types back out of its children can get every leaf right
//! and still be wrong about every node above them, which is what refusing
//! `if branches disagree` was really reporting.
//!
//! `merge-ty` and `branch-recorded-ty` are how the expectation and what was
//! actually lowered are reconciled, and `usable-witness-ty` is the rule for
//! when a lowered type is allowed to speak: **a bounded integer never is.**
//! `Integer between 0 and 15` widens to `Integer`, so reading the branch's
//! type back would publish a bound the program does not have.

use crate::check::Ty;

/// `ty-has-error` (Lowering.codex:297). A list of errors is an error; nothing
/// else recurses, which is upstream's choice and not an oversight -- these are
/// the two shapes lowering hands back when it could not answer.
pub fn has_error(t: &Ty) -> bool {
    match t {
        Ty::Error | Ty::NoExpect => true,
        Ty::List(e) => has_error(e),
        _ => false,
    }
}

/// `ty-has-typevars` (Unifier.codex:802), which DOES recurse everywhere.
pub fn has_typevars(t: &Ty) -> bool {
    match t {
        Ty::Var(_) => true,
        _ => children(t).into_iter().any(has_typevars),
    }
}

/// `ty-admits-widening` (Lowering.codex:833). An integer and a real, and
/// nothing else: those are the two the language will silently accept in a
/// wider form, so neither can be trusted to speak for the node above it.
pub fn admits_widening(t: &Ty) -> bool {
    matches!(t, Ty::Integer(..) | Ty::Real(..))
}

/// `usable-witness-ty` (Lowering.codex:827).
pub fn usable_witness(t: &Ty) -> bool {
    !has_error(t) && !has_typevars(t) && !admits_widening(t)
}

/// `merge-ty` (Lowering.codex:304): the expectation wins unless it has nothing
/// to say, and a list merges elementwise so that `List <error>` against
/// `List text` answers `List text`.
pub fn merge(a: &Ty, b: &Ty) -> Ty {
    match a {
        Ty::Error | Ty::NoExpect => b.clone(),
        Ty::List(ea) => match b {
            Ty::List(eb) => Ty::List(Box::new(merge(ea, eb))),
            _ => a.clone(),
        },
        _ => a.clone(),
    }
}

/// `if-witness-ty` (Lowering.codex:840): the then-branch if it can speak,
/// otherwise the else-branch -- whether or not THAT one can.
pub fn if_witness(then_ty: &Ty, else_ty: &Ty) -> Ty {
    if usable_witness(then_ty) { then_ty.clone() } else { else_ty.clone() }
}

/// `match-witness-ty` (Lowering.codex:844): the first arm body that can speak,
/// and `ErrorTy` if none can.
pub fn match_witness<'t>(bodies: impl Iterator<Item = &'t Ty>) -> Ty {
    for b in bodies {
        if usable_witness(b) {
            return b.clone();
        }
    }
    Ty::Error
}

/// `branch-recorded-ty` (Lowering.codex:821). An expectation with no type
/// variables in it is already the answer; one that has them learns them from
/// the branch that was actually lowered.
pub fn branch_recorded(ty: &Ty, witness: &Ty) -> Ty {
    if !has_typevars(ty) || !usable_witness(witness) {
        return ty.clone();
    }
    subst_from_arg(ty, witness, ty)
}

/// `subst-type-vars-from-arg` (LoweringTypes.codex:57). Match `param` against
/// `arg` structurally; wherever `param` is a variable, that variable's binding
/// is the corresponding piece of `arg`, and every occurrence of it in `target`
/// is replaced.
///
/// A mismatch is not an error -- it answers `target` unchanged. Two types that
/// do not line up simply teach nothing.
pub fn subst_from_arg(param: &Ty, arg: &Ty, target: &Ty) -> Ty {
    let named = |pa: &[Ty], aa: &[Ty]| -> Ty {
        let mut t = target.clone();
        for (p, a) in pa.iter().zip(aa.iter()) {
            t = subst_from_arg(p, a, &t);
        }
        t
    };
    match (param, arg) {
        (Ty::Var(id), _) => subst_var(target, *id, arg),
        (Ty::List(pe), Ty::List(ae)) => subst_from_arg(pe, ae, target),
        (Ty::Fun(pp, _, pr), Ty::Fun(ap, _, ar)) => {
            let t = subst_from_arg(pp, ap, target);
            subst_from_arg(pr, ar, &t)
        }
        (Ty::TypeApply(pf, pa), Ty::TypeApply(af, aa)) => {
            let t = subst_from_arg(pf, af, target);
            subst_from_arg(pa, aa, &t)
        }
        (Ty::Sum(pn, pa), Ty::Sum(an, aa))
        | (Ty::Record(pn, pa), Ty::Record(an, aa))
        | (Ty::Constructed(pn, pa), Ty::Constructed(an, aa)) => {
            if pn == an {
                named(pa, aa)
            } else {
                target.clone()
            }
        }
        (Ty::LinkedList(pe), Ty::LinkedList(ae))
        | (Ty::Vector(_, pe), Ty::Vector(_, ae))
        | (Ty::Linear(pe), Ty::Linear(ae)) => subst_from_arg(pe, ae, target),
        (Ty::Unit(pn, pe), Ty::Unit(an, ae)) if pn == an => subst_from_arg(pe, ae, target),
        _ => target.clone(),
    }
}

/// `subst-type-var-in-target` (LoweringTypes.codex:99). A `forall` that binds
/// the same id SHADOWS it and is left alone; a row quantifier binds a row id,
/// which is a different numberspace, so it never shadows.
pub fn subst_var(t: &Ty, id: u32, with: &Ty) -> Ty {
    if !has_typevars(t) {
        return t.clone();
    }
    match t {
        Ty::Var(i) => {
            if *i == id {
                with.clone()
            } else {
                t.clone()
            }
        }
        Ty::ForAll(fid, body) => {
            if *fid == id {
                t.clone()
            } else {
                Ty::ForAll(*fid, Box::new(subst_var(body, id, with)))
            }
        }
        Ty::ForAllEff(fid, body) => Ty::ForAllEff(*fid, Box::new(subst_var(body, id, with))),
        _ => map_children(t, &mut |c| subst_var(c, id, with)),
    }
}

/// `codex-type-fold-children`, read-only half: every `CodexType` a type holds.
fn children(t: &Ty) -> Vec<&Ty> {
    match t {
        Ty::Fun(a, _, r) | Ty::PropEq(a, r) | Ty::TypeApply(a, r) => vec![a, r],
        Ty::List(e)
        | Ty::LinkedList(e)
        | Ty::ForAll(_, e)
        | Ty::ForAllEff(_, e)
        | Ty::Effectful(_, _, e)
        | Ty::Unit(_, e)
        | Ty::Vector(_, e)
        | Ty::Linear(e) => vec![e],
        Ty::Sum(_, a) | Ty::Record(_, a) | Ty::Constructed(_, a) => a.iter().collect(),
        _ => vec![],
    }
}

/// `codex-type-map-children`: the same shape back with each child rewritten.
fn map_children(t: &Ty, f: &mut dyn FnMut(&Ty) -> Ty) -> Ty {
    let each = |xs: &Vec<Ty>, f: &mut dyn FnMut(&Ty) -> Ty| xs.iter().map(|x| f(x)).collect();
    match t {
        Ty::Fun(a, row, r) => Ty::Fun(Box::new(f(a)), row.clone(), Box::new(f(r))),
        Ty::PropEq(a, b) => Ty::PropEq(Box::new(f(a)), Box::new(f(b))),
        Ty::TypeApply(a, b) => Ty::TypeApply(Box::new(f(a)), Box::new(f(b))),
        Ty::List(e) => Ty::List(Box::new(f(e))),
        Ty::LinkedList(e) => Ty::LinkedList(Box::new(f(e))),
        Ty::ForAll(i, e) => Ty::ForAll(*i, Box::new(f(e))),
        Ty::ForAllEff(i, e) => Ty::ForAllEff(*i, Box::new(f(e))),
        Ty::Effectful(effs, sc, e) => {
            Ty::Effectful(effs.clone(), sc.clone(), Box::new(f(e)))
        }
        Ty::Unit(n, e) => Ty::Unit(*n, Box::new(f(e))),
        Ty::Vector(w, e) => Ty::Vector(*w, Box::new(f(e))),
        Ty::Linear(e) => Ty::Linear(Box::new(f(e))),
        Ty::Sum(n, a) => Ty::Sum(*n, each(a, f)),
        Ty::Record(n, a) => Ty::Record(*n, each(a, f)),
        Ty::Constructed(n, a) => Ty::Constructed(*n, each(a, f)),
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::Overflow;

    /// **A BOUNDED INTEGER IS NEVER A WITNESS**, which is the whole reason
    /// `guarded-field`'s `if` is `int-default` and not `(int 0 15 ov-error)`.
    #[test]
    fn a_bounded_integer_cannot_speak_for_the_node_above_it() {
        assert!(!usable_witness(&Ty::Integer(0, 15, Overflow::Error)));
        assert!(!usable_witness(&Ty::Integer(i64::MIN, i64::MAX, Overflow::Error)));
        assert!(usable_witness(&Ty::Text));
        assert!(!usable_witness(&Ty::Var(3)));
        assert!(!usable_witness(&Ty::List(Box::new(Ty::Error))));
    }

    /// `merge-ty` prefers the EXPECTATION, and descends only into a list.
    #[test]
    fn the_expectation_wins_unless_it_has_nothing_to_say() {
        assert_eq!(merge(&Ty::NoExpect, &Ty::Text), Ty::Text);
        assert_eq!(merge(&Ty::Text, &Ty::Boolean), Ty::Text);
        assert_eq!(
            merge(&Ty::List(Box::new(Ty::Error)), &Ty::List(Box::new(Ty::Text))),
            Ty::List(Box::new(Ty::Text))
        );
    }

    /// A `forall` binding the same id shadows it; a row quantifier does not,
    /// because row ids are a separate counter.
    #[test]
    fn a_forall_shadows_its_own_variable() {
        let inner = Ty::Var(7);
        assert_eq!(subst_var(&inner, 7, &Ty::Text), Ty::Text);
        let shadowed = Ty::ForAll(7, Box::new(Ty::Var(7)));
        assert_eq!(subst_var(&shadowed, 7, &Ty::Text), shadowed);
        let rowq = Ty::ForAllEff(1, Box::new(Ty::Var(7)));
        assert_eq!(subst_var(&rowq, 7, &Ty::Text), Ty::ForAllEff(1, Box::new(Ty::Text)));
    }

    /// A mismatch teaches nothing rather than failing.
    #[test]
    fn types_that_do_not_line_up_leave_the_target_alone() {
        let target = Ty::List(Box::new(Ty::Var(2)));
        assert_eq!(subst_from_arg(&Ty::Text, &Ty::Boolean, &target), target);
        assert_eq!(
            subst_from_arg(&Ty::List(Box::new(Ty::Var(2))), &Ty::List(Box::new(Ty::Text)), &target),
            Ty::List(Box::new(Ty::Text))
        );
    }
}

/// `peel-fun-return`.
pub fn peel_fun_return(t: &Ty) -> Option<&Ty> {
    match t {
        Ty::Fun(_, _, r) => Some(r),
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => peel_fun_return(b),
        _ => None,
    }
}

/// `peel-returns-n`: the type left after `k` arguments. An effect row is peeled
/// WITHOUT spending an argument -- it wraps the result, it is not one.
pub fn peel_returns_n(t: &Ty, k: usize) -> Option<&Ty> {
    if k == 0 {
        return Some(t);
    }
    match t {
        Ty::Effectful(_, _, inner) => peel_returns_n(inner, k),
        other => peel_returns_n(peel_fun_return(other)?, k - 1),
    }
}
