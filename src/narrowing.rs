//! The narrowing lints -- `lint-arg-narrowing`, `lint-record-set` and
//! `lint-narrowing-check` (TypeCheckerInference.codex:850, :960, :1329) over
//! the range prover `aexpr-proven-range` (:1000ff) and the interval
//! arithmetic of `foreword/math/Interval.codex`.
//!
//! A bounded integer -- a field, a constructor field, a parameter declared
//! `Integer between lo and hi` in the trapping mode -- takes a literal only
//! when the literal is inside the bound (CDX2050), and takes any other
//! value only when the value's PROVEN range is inside it (CDX2051). The
//! proof is interval arithmetic over what the checker already knows: a
//! literal is itself, a local carries the range its binding or its `if`
//! condition established, a nullary literal definition is a constant, a
//! declared return is its declared bound, and a handful of builtins have
//! structural bounds. `__narrow` asserts a range and traps at runtime.

use crate::ast::{BinaryOp, Expr, LiteralKind};
use crate::check::{strip_forall, Cdx, Overflow, Ty, TyEnv, UnifyState};
use crate::token::lit_text_to_integer;

pub type Range = (i64, i64);

pub const UNKNOWN: Range = (i64::MIN, i64::MAX);
const EMPTY: Range = (1, 0);

fn is_empty(r: Range) -> bool {
    r.0 > r.1
}

fn is_unknown(r: Range) -> bool {
    r == UNKNOWN
}

fn is_bounded(r: Range) -> bool {
    r.0 > i64::MIN || r.1 < i64::MAX
}

// ---------------------------------------------------------------------------
// `foreword/math/Interval`: an empty interval absorbs, an overflowing
// endpoint answers unknown.

fn iv_add(a: Range, b: Range) -> Range {
    if is_empty(a) || is_empty(b) {
        return EMPTY;
    }
    match (a.0.checked_add(b.0), a.1.checked_add(b.1)) {
        (Some(lo), Some(hi)) => (lo, hi),
        _ => UNKNOWN,
    }
}

fn iv_sub(a: Range, b: Range) -> Range {
    if is_empty(a) || is_empty(b) {
        return EMPTY;
    }
    match (a.0.checked_sub(b.1), a.1.checked_sub(b.0)) {
        (Some(lo), Some(hi)) => (lo, hi),
        _ => UNKNOWN,
    }
}

fn iv_mul(a: Range, b: Range) -> Range {
    if is_empty(a) || is_empty(b) {
        return EMPTY;
    }
    let ps = [a.0.checked_mul(b.0), a.0.checked_mul(b.1), a.1.checked_mul(b.0), a.1.checked_mul(b.1)];
    if ps.iter().any(Option::is_none) {
        return UNKNOWN;
    }
    let ps: Vec<i64> = ps.iter().map(|p| p.unwrap()).collect();
    (*ps.iter().min().unwrap(), *ps.iter().max().unwrap())
}

fn iv_div(a: Range, b: Range) -> Range {
    if is_empty(a) || is_empty(b) {
        return EMPTY;
    }
    if b.0 <= 0 && b.1 >= 0 {
        return UNKNOWN;
    }
    if a.0 == i64::MIN && b.1 == -1 {
        return UNKNOWN;
    }
    let qs = [a.0 / b.0, a.0 / b.1, a.1 / b.0, a.1 / b.1];
    (*qs.iter().min().unwrap(), *qs.iter().max().unwrap())
}

fn iv_union(a: Range, b: Range) -> Range {
    if is_empty(a) && is_empty(b) {
        return EMPTY;
    }
    if is_empty(a) {
        return b;
    }
    if is_empty(b) {
        return a;
    }
    (a.0.min(b.0), a.1.max(b.1))
}

fn iv_intersect(a: Range, b: Range) -> Range {
    let lo = a.0.max(b.0);
    let hi = a.1.min(b.1);
    if lo > hi {
        EMPTY
    } else {
        (lo, hi)
    }
}

/// `interval-range`: an empty interval reads back as unknown.
fn interval_range(a: Range) -> Range {
    if is_empty(a) {
        UNKNOWN
    } else {
        a
    }
}

// ---------------------------------------------------------------------------
// `Section: Lint value-expression range analysis`.

/// `builtin-return-range`: structural bounds only.
fn builtin_return_range(name: &str) -> Range {
    match name {
        "list-length" | "text-length" | "__deck-pos" | "__heap-save" | "__buf-write-bytes" => (0, 4_294_967_295),
        _ => UNKNOWN,
    }
}

pub fn apply_head_name<'e>(e: &'e Expr, env: &'e TyEnv<'_>) -> &'e str {
    match e {
        Expr::Apply(f, _, _) => apply_head_name(f, env),
        Expr::NameRef(n, _) => env.syms.text(*n),
        _ => "",
    }
}

fn is_two_arg_call(func: &Expr, name: &str, env: &TyEnv<'_>) -> bool {
    match func {
        Expr::Apply(inner, _, _) => matches!(&**inner, Expr::NameRef(n, _) if env.syms.text(*n) == name),
        _ => false,
    }
}

fn is_narrow_call(e: &Expr, env: &TyEnv<'_>) -> bool {
    matches!(e, Expr::Apply(f, _, _) if matches!(&**f, Expr::NameRef(n, _) if env.syms.text(*n) == "__narrow"))
}

/// `fun-final-return-range`.
fn fun_final_return_range(t: &Ty) -> Range {
    match t {
        Ty::Fun(_, _, r) => fun_final_return_range(r),
        Ty::Effectful(_, _, r) => fun_final_return_range(r),
        Ty::Integer(lo, hi, _) => (*lo, *hi),
        _ => UNKNOWN,
    }
}

/// The prover, with the `if`-arm refinements that upstream threads through
/// a functional environment carried here as an overlay.
struct Prover<'a, 'e> {
    env: &'a TyEnv<'e>,
    st: &'a UnifyState,
    extra: Vec<(String, Range)>,
}

/// `CondRefine`.
struct CondRefine {
    target: String,
    recv: String,
    then_iv: Range,
    else_iv: Range,
}

impl Prover<'_, '_> {
    fn local_range(&self, name: &str) -> Range {
        if let Some((_, r)) = self.extra.iter().rev().find(|(n, _)| n == name) {
            return *r;
        }
        self.env.local_range(name).unwrap_or(UNKNOWN)
    }

    fn name_range(&self, n: crate::ast::Name) -> Range {
        match self.env.const_range(n) {
            Some(r) => r,
            None => builtin_return_range(self.env.syms.text(n)),
        }
    }

    fn declared_return_range(&self, name: &str) -> Range {
        let Some(sym) = self.env.syms.find(name) else { return UNKNOWN };
        let Some(t) = self.env.get(sym) else { return UNKNOWN };
        fun_final_return_range(&strip_forall(&self.st.deep_resolve(t)))
    }

    /// `aexpr-proven-range`.
    fn range(&mut self, e: &Expr) -> Range {
        match e {
            Expr::Lit(v, LiteralKind::IntLit, _) => {
                let n = lit_text_to_integer(v);
                (n, n)
            }
            Expr::Lit(..) => UNKNOWN,
            Expr::NameRef(n, _) => {
                if self.env.is_local(*n) {
                    self.local_range(self.env.syms.text(*n))
                } else {
                    self.name_range(*n)
                }
            }
            Expr::Apply(f, a, _) => self.apply_range(f, a),
            Expr::Binary(l, op, r, _) => self.binary_range(*op, l, r),
            Expr::If(c, t, el, _) => self.if_range(c, t, el),
            Expr::Let(binds, body, _) => {
                let mark = self.extra.len();
                for b in binds {
                    let r = self.range(&b.value);
                    if is_bounded(r) {
                        self.extra.push((self.env.syms.text(b.name).to_string(), r));
                    }
                }
                let out = self.range(body);
                self.extra.truncate(mark);
                out
            }
            Expr::FieldAccess(obj, f, _) => self.field_range(obj, self.env.syms.text(*f)),
            _ => UNKNOWN,
        }
    }

    /// `apply-proven-range`.
    fn apply_range(&mut self, func: &Expr, arg: &Expr) -> Range {
        let head = apply_head_name(func, self.env).to_string();
        if head.is_empty() {
            return UNKNOWN;
        }
        if head == "__narrow" {
            return self.range(arg);
        }
        if self.env.syms.find(&head).is_some_and(|s| self.env.is_local(s)) {
            return UNKNOWN;
        }
        if is_two_arg_call(func, "int-mod", self.env) {
            let (lo, hi) = self.range(arg);
            return if lo > 0 { (0, hi - 1) } else { UNKNOWN };
        }
        let b = builtin_return_range(&head);
        if is_bounded(b) {
            return b;
        }
        self.declared_return_range(&head)
    }

    fn binary_range(&mut self, op: BinaryOp, l: &Expr, r: &Expr) -> Range {
        let a = self.range(l);
        let b = self.range(r);
        match op {
            BinaryOp::OpAdd => interval_range(iv_add(a, b)),
            BinaryOp::OpSub => interval_range(iv_sub(a, b)),
            BinaryOp::OpMul => interval_range(iv_mul(a, b)),
            BinaryOp::OpDiv => interval_range(iv_div(a, b)),
            _ => UNKNOWN,
        }
    }

    /// `if-proven-range`: the condition refines a local or a field in each
    /// arm; an arm the condition rules out contributes nothing.
    fn if_range(&mut self, c: &Expr, t: &Expr, el: &Expr) -> Range {
        let rf = self.cond_refine(c);
        if !rf.target.is_empty() && is_empty(rf.then_iv) {
            return self.arm_range(&rf, rf.else_iv, el);
        }
        if !rf.target.is_empty() && is_empty(rf.else_iv) {
            return self.arm_range(&rf, rf.then_iv, t);
        }
        let a = self.arm_range(&rf, rf.then_iv, t);
        let b = self.arm_range(&rf, rf.else_iv, el);
        interval_range(iv_union(a, b))
    }

    /// `arm-refined-env` then the arm's range.
    fn arm_range(&mut self, rf: &CondRefine, iv: Range, arm: &Expr) -> Range {
        let refine = !rf.target.is_empty()
            && !is_empty(iv)
            && !is_unknown(iv)
            && (rf.recv.is_empty() || arm_reads_only(arm, &rf.recv, self.env));
        if !refine {
            return self.range(arm);
        }
        self.extra.push((rf.target.clone(), iv));
        let out = self.range(arm);
        self.extra.pop();
        out
    }

    /// `field-proven-range`: a refined `recv.field`, else the field's
    /// declared bound.
    fn field_range(&mut self, obj: &Expr, fname: &str) -> Range {
        let Expr::NameRef(n, _) = obj else { return UNKNOWN };
        let recv = self.env.syms.text(*n);
        let key = format!("{recv}.{fname}");
        if let Some((_, r)) = self.extra.iter().rev().find(|(k, _)| *k == key) {
            return *r;
        }
        if let Some(r) = self.env.local_range(&key) {
            return r;
        }
        self.field_declared_range(*n, fname)
    }

    fn field_declared_range(&self, recv: crate::ast::Name, fname: &str) -> Range {
        let Some(obj_ty) = self.env.get(recv) else { return UNKNOWN };
        let Some(fsym) = self.env.syms.find(fname) else { return UNKNOWN };
        match crate::check::field_type_for_lint(self.env, &self.st.deep_resolve(obj_ty), fsym) {
            Some(Ty::Integer(lo, hi, Overflow::Error)) => (lo, hi),
            _ => UNKNOWN,
        }
    }

    /// `cond-refine`: a comparison against a local or a field of a local.
    fn cond_refine(&mut self, c: &Expr) -> CondRefine {
        let none = CondRefine { target: String::new(), recv: String::new(), then_iv: UNKNOWN, else_iv: UNKNOWN };
        let Expr::Binary(l, op, r, _) = c else { return none };
        if !compare_op_refines(*op) {
            return none;
        }
        let other = self.range(r);
        let from_left = self.refine_target(l, *op, other);
        if !from_left.target.is_empty() {
            return from_left;
        }
        let other = self.range(l);
        self.refine_target(r, swap_compare_op(*op), other)
    }

    fn refine_target(&self, side: &Expr, op: BinaryOp, other: Range) -> CondRefine {
        let none = CondRefine { target: String::new(), recv: String::new(), then_iv: UNKNOWN, else_iv: UNKNOWN };
        match side {
            Expr::NameRef(n, _) if self.env.is_local(*n) => {
                let name = self.env.syms.text(*n).to_string();
                let cur = self.local_range(&name);
                CondRefine {
                    target: name,
                    recv: String::new(),
                    then_iv: iv_intersect(cur, compare_implied(op, other, true)),
                    else_iv: iv_intersect(cur, compare_implied(op, other, false)),
                }
            }
            Expr::FieldAccess(obj, f, _) => match &**obj {
                Expr::NameRef(rn, _) => {
                    let recv = self.env.syms.text(*rn).to_string();
                    let fname = self.env.syms.text(*f);
                    let cur = self.field_declared_range(*rn, fname);
                    CondRefine {
                        target: format!("{recv}.{fname}"),
                        recv,
                        then_iv: iv_intersect(cur, compare_implied(op, other, true)),
                        else_iv: iv_intersect(cur, compare_implied(op, other, false)),
                    }
                }
                _ => none,
            },
            _ => none,
        }
    }
}

fn compare_op_refines(op: BinaryOp) -> bool {
    matches!(op, BinaryOp::OpLt | BinaryOp::OpGt | BinaryOp::OpLtEq | BinaryOp::OpGtEq | BinaryOp::OpEq)
}

fn swap_compare_op(op: BinaryOp) -> BinaryOp {
    match op {
        BinaryOp::OpLt => BinaryOp::OpGt,
        BinaryOp::OpGt => BinaryOp::OpLt,
        BinaryOp::OpLtEq => BinaryOp::OpGtEq,
        BinaryOp::OpGtEq => BinaryOp::OpLtEq,
        other => other,
    }
}

fn lt_bound(bound: i64) -> Range {
    if bound == i64::MIN {
        EMPTY
    } else {
        (i64::MIN, bound - 1)
    }
}

fn gt_bound(bound: i64) -> Range {
    if bound == i64::MAX {
        EMPTY
    } else {
        (bound + 1, i64::MAX)
    }
}

/// `compare-implied-interval`.
fn compare_implied(op: BinaryOp, other: Range, taken: bool) -> Range {
    let (o_lo, o_hi) = other;
    match op {
        BinaryOp::OpLt => {
            if taken {
                lt_bound(o_hi)
            } else {
                (o_lo, i64::MAX)
            }
        }
        BinaryOp::OpLtEq => {
            if taken {
                (i64::MIN, o_hi)
            } else {
                gt_bound(o_lo)
            }
        }
        BinaryOp::OpGt => {
            if taken {
                gt_bound(o_lo)
            } else {
                (i64::MIN, o_hi)
            }
        }
        BinaryOp::OpGtEq => {
            if taken {
                (o_lo, i64::MAX)
            } else {
                lt_bound(o_hi)
            }
        }
        BinaryOp::OpEq => {
            if taken {
                (o_lo, o_hi)
            } else {
                UNKNOWN
            }
        }
        _ => UNKNOWN,
    }
}

/// `arm-reads-only`: the arm never writes through `name`.
fn arm_reads_only(e: &Expr, name: &str, env: &TyEnv<'_>) -> bool {
    match e {
        Expr::Lit(..) => true,
        Expr::NameRef(n, _) => env.syms.text(*n) != name,
        Expr::FieldAccess(obj, _, _) => match &**obj {
            Expr::NameRef(..) => true,
            other => arm_reads_only(other, name, env),
        },
        Expr::Apply(f, a, _) => arm_reads_only(f, name, env) && arm_reads_only(a, name, env),
        Expr::Binary(l, _, r, _) => arm_reads_only(l, name, env) && arm_reads_only(r, name, env),
        Expr::Unary(x, _) | Expr::Lazy(x, _) => arm_reads_only(x, name, env),
        Expr::If(c, t, el, _) => {
            arm_reads_only(c, name, env) && arm_reads_only(t, name, env) && arm_reads_only(el, name, env)
        }
        Expr::List(xs, _) => xs.iter().all(|x| arm_reads_only(x, name, env)),
        Expr::Record(_, fs, _) => fs.iter().all(|f| arm_reads_only(&f.value, name, env)),
        Expr::Let(binds, body, _) => {
            arm_reads_only(body, name, env) && binds.iter().all(|b| arm_reads_only(&b.value, name, env))
        }
        _ => false,
    }
}

/// `aexpr-proven-range`, from the outside.
pub fn proven_range(e: &Expr, env: &TyEnv<'_>, st: &UnifyState) -> Range {
    Prover { env, st, extra: Vec::new() }.range(e)
}

/// What an `if` condition establishes for each arm: the refined name and
/// its interval in the then-arm and the else-arm, when the condition is a
/// comparison against a local or a field of a local (`cond-refine`).
pub struct ArmRefinement {
    pub target: String,
    pub recv: String,
    pub then_iv: Range,
    pub else_iv: Range,
}

pub fn if_refinement(c: &Expr, env: &TyEnv<'_>, st: &UnifyState) -> Option<ArmRefinement> {
    let rf = Prover { env, st, extra: Vec::new() }.cond_refine(c);
    if rf.target.is_empty() {
        return None;
    }
    Some(ArmRefinement { target: rf.target, recv: rf.recv, then_iv: rf.then_iv, else_iv: rf.else_iv })
}

/// `arm-refined-env`'s decision: the interval to note for this arm, if any.
pub fn arm_refinement(rf: &ArmRefinement, iv: Range, arm: &Expr, env: &TyEnv<'_>) -> Option<Range> {
    if is_empty(iv) || is_unknown(iv) {
        return None;
    }
    if !rf.recv.is_empty() && !arm_reads_only(arm, &rf.recv, env) {
        return None;
    }
    Some(iv)
}

// ---------------------------------------------------------------------------
// The lints.

/// `lint-narrowing-check`: a bounded trapping integer takes a literal only
/// inside its bound, and any other value only when its range is proven.
pub fn lint_narrowing_check(
    value_arg: &Expr,
    value_ty: &Ty,
    field_ty: &Ty,
    descriptor: &str,
    env: &TyEnv<'_>,
    st: &mut UnifyState,
) {
    if is_narrow_call(value_arg, env) {
        return;
    }
    let Ty::Integer(f_lo, f_hi, Overflow::Error) = field_ty else { return };
    let (f_lo, f_hi) = (*f_lo, *f_hi);
    if let Expr::Lit(text, LiteralKind::IntLit, _) = value_arg {
        let n = lit_text_to_integer(text);
        if n < f_lo || n > f_hi {
            st.error(
                Cdx::NARROWING_RECORD_SET_LITERAL,
                format!("{descriptor} has bound {f_lo}..{f_hi} but assigned literal {n} is out of range"),
            );
        }
        return;
    }
    if let Expr::Lit(..) = value_arg {
        return;
    }
    let Ty::Integer(v_lo, v_hi, _) = st.deep_resolve(value_ty) else { return };
    if v_lo >= f_lo && v_hi <= f_hi {
        return;
    }
    // `lint-narrowing-prove`: a proven range inside the bound passes (an
    // info upstream, nothing here); anything else is CDX2051.
    let (p_lo, p_hi) = proven_range(value_arg, env, st);
    if p_lo >= f_lo && p_hi <= f_hi {
        return;
    }
    st.error(
        Cdx::NARROWING_RECORD_SET,
        format!("{descriptor} has bound {f_lo}..{f_hi} but the value's proven range is {p_lo}..{p_hi}; prove the value's range or assert it with __narrow, which traps at runtime if violated"),
    );
}

/// `lint-arg-narrowing`: the callee's declared parameter, when bounded.
pub fn lint_arg_narrowing(func: &Expr, func_ty: &Ty, arg: &Expr, arg_ty: &Ty, env: &TyEnv<'_>, st: &mut UnifyState) {
    let resolved = strip_forall(&st.deep_resolve(func_ty));
    let Ty::Fun(p, _, _) = resolved else { return };
    let declared = st.deep_resolve(&p);
    let Ty::Integer(lo, hi, _) = &declared else { return };
    if *lo <= i64::MIN && *hi >= i64::MAX {
        return;
    }
    let head = apply_head_name(func, env);
    let desc = if is_ctor_of_own_sum(head, env, st) {
        format!("field of constructor '{head}'")
    } else {
        "bounded parameter".to_string()
    };
    lint_narrowing_check(arg, arg_ty, &declared, &desc, env, st);
}

/// `is-ctor-of-own-sum`: a capitalised name whose type ends in a sum.
fn is_ctor_of_own_sum(head: &str, env: &TyEnv<'_>, st: &UnifyState) -> bool {
    if !head.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
        return false;
    }
    let Some(sym) = env.syms.find(head) else { return false };
    let Some(t) = env.get(sym) else { return false };
    let mut t = strip_forall(&st.deep_resolve(t));
    while let Ty::Fun(_, _, r) = t {
        t = *r;
    }
    matches!(t, Ty::Sum(..))
}

/// `record-local-range`: what a `let` binding is proven to hold, else its
/// bounded declared type.
pub fn local_range_of(value: &Expr, resolved_ty: &Ty, env: &TyEnv<'_>, st: &UnifyState) -> Option<Range> {
    let r = proven_range(value, env, st);
    if is_bounded(r) {
        return Some(r);
    }
    match resolved_ty {
        Ty::Integer(lo, hi, _) if *lo > i64::MIN || *hi < i64::MAX => Some((*lo, *hi)),
        _ => None,
    }
}

/// `bind-param-range`: a parameter declared bounded and trapping.
pub fn param_range_of(ty: &Ty) -> Option<Range> {
    match ty {
        Ty::Integer(lo, hi, Overflow::Error) if *lo > i64::MIN || *hi < i64::MAX => Some((*lo, *hi)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interval_arithmetic_refuses_overflow_and_zero_divisors() {
        assert_eq!(iv_add((0, 255), (1, 1)), (1, 256));
        assert_eq!(iv_add((i64::MAX - 1, i64::MAX), (1, 1)), UNKNOWN);
        assert_eq!(iv_div((0, 255), (8, 8)), (0, 31));
        assert_eq!(iv_div((0, 255), (-1, 1)), UNKNOWN);
        assert_eq!(iv_mul((-2, 3), (4, 5)), (-10, 15));
        assert!(is_empty(iv_intersect((0, 5), (10, 20))));
        assert_eq!(iv_union((0, 5), (10, 20)), (0, 20));
    }

    #[test]
    fn a_comparison_implies_an_interval_on_each_arm() {
        assert_eq!(compare_implied(BinaryOp::OpLt, (10, 10), true), (i64::MIN, 9));
        assert_eq!(compare_implied(BinaryOp::OpLt, (10, 10), false), (10, i64::MAX));
        assert_eq!(compare_implied(BinaryOp::OpGtEq, (0, 0), false), (i64::MIN, -1));
    }
}
