//! Cost Model 3.3 -- upstream's `Section: Cost Model 3.3 -- the growing
//! rung`, `-- the bounded declaration` and `-- the none rung`
//! (TypeChecker.codex:1569-2093).
//!
//! `bounded <class> name` declares a CEILING in the lattice `none < fixed <
//! budgeted < linear < growing`. The inference answers, transitively over
//! calls: whether a definition is GROWING (an argument of a self call is
//! its own parameter copied by `&`), whether it ALLOCATES at all, and
//! whether it allocates PAST A NAMED BOUND -- read against the registry's
//! per-builtin allocation class, strictly for `fixed` and leniently for
//! `budgeted`. A name in call position that is neither a definition here
//! nor a builtin measured at zero is read as allocating: abstain toward
//! refusal.

use crate::ast::{BinaryOp, Chapter, Def, Expr, LiteralKind, Name};
use crate::builtins::builtin_alloc;
use crate::check::{expr_type_key, Cdx, Ty, UnifyState};
use crate::symbol::SymTab;

fn is_rt_unsafe_name(n: &str) -> bool {
    matches!(n, "__alloc" | "list-push" | "list-concat" | "__list-with-capacity" | "__linked-list-push")
}

fn is_rt_safe_builtin(n: &str) -> bool {
    matches!(
        n,
        "list-at"
            | "list-length"
            | "text-length"
            | "text-at"
            | "array-at"
            | "array-length"
            | "bit-and"
            | "bit-or"
            | "bit-xor"
            | "bit-shl"
            | "bit-shr"
            | "bit-shru"
            | "bit-not"
            | "int-mod"
            | "int-rem"
            | "abs"
            | "min"
            | "max"
    )
}

fn cost_class_rank(c: &str) -> i32 {
    match c {
        "none" => 0,
        "fixed" => 1,
        "budgeted" => 2,
        "linear" => 3,
        "growing" => 4,
        _ => -1,
    }
}

/// `cost-apply-head`: the name at the head of an application spine.
fn apply_head(e: &Expr) -> Option<Name> {
    match e {
        Expr::Apply(f, _, _) => apply_head(f),
        Expr::NameRef(n, _) => Some(*n),
        _ => None,
    }
}

/// `cost-apply-args`: outermost first, so source position `i` of `n` sits
/// at `n - 1 - i`.
fn apply_args<'a>(e: &'a Expr, acc: &mut Vec<&'a Expr>) {
    if let Expr::Apply(f, a, _) = e {
        acc.push(a);
        apply_args(f, acc);
    }
}

/// The recorded type at a span, resolved.
fn type_at(st: &UnifyState, sp: crate::ast::Span) -> Option<Ty> {
    let key = expr_type_key(sp);
    st.expr_types.iter().find(|(k, _)| *k == key).map(|(_, t)| st.deep_resolve(t))
}

struct Cx<'a> {
    st: &'a UnifyState,
    syms: &'a SymTab,
    defs: &'a [Def],
}

impl Cx<'_> {
    fn text(&self, n: Name) -> &str {
        self.syms.text(n)
    }

    fn def_known(&self, n: Name) -> bool {
        self.defs.iter().any(|d| d.name == n)
    }

    // ---- the growing rung --------------------------------------------

    /// RULE 2: an append whose right operand is an empty literal aliases.
    fn operand_grows(e: &Expr) -> bool {
        match e {
            Expr::List(xs, _) => !xs.is_empty(),
            Expr::Lit(t, _, _) => !t.is_empty(),
            _ => true,
        }
    }

    /// RULE 3: a Text append with a non-allocating right operand is linear.
    fn rhs_allocates(e: &Expr) -> bool {
        match e {
            Expr::Lit(..) | Expr::NameRef(..) => false,
            Expr::FieldAccess(obj, _, _) => Self::rhs_allocates(obj),
            _ => true,
        }
    }

    fn append_copies(&self, sp: crate::ast::Span, rhs: &Expr) -> bool {
        match type_at(self.st, sp) {
            Some(Ty::Text) => Self::rhs_allocates(rhs),
            _ => true,
        }
    }

    /// RULE 1: the argument is this parameter appended to.
    fn arg_is_self_append(&self, arg: &Expr, pname: Name) -> bool {
        match arg {
            Expr::Binary(l, BinaryOp::OpAnd, r, sp) => {
                matches!(&**l, Expr::NameRef(n, _) if *n == pname) && Self::operand_grows(r) && self.append_copies(*sp, r)
            }
            _ => false,
        }
    }

    fn call_grows(&self, args: &[&Expr], params: &[Name]) -> bool {
        let nargs = args.len();
        (0..nargs.min(params.len())).any(|i| self.arg_is_self_append(args[nargs - 1 - i], params[i]))
    }

    /// `cost-expr-grows`.
    fn expr_grows(&self, e: &Expr, me: Name, params: &[Name]) -> bool {
        match e {
            Expr::Apply(f, a, _) => {
                if apply_head(e) == Some(me) {
                    let mut args = Vec::new();
                    apply_args(e, &mut args);
                    if self.call_grows(&args, params) {
                        return true;
                    }
                }
                self.expr_grows(f, me, params) || self.expr_grows(a, me, params)
            }
            _ => self.any_child(e, |c| self.expr_grows(c, me, params)),
        }
    }

    // ---- the none rung -------------------------------------------------

    fn builtin_nonalloc(&self, n: &str) -> bool {
        is_rt_safe_builtin(n) || builtin_alloc(n) == "none"
    }

    fn head_allocates(&self, allocating: &[Name], head: Option<Name>) -> bool {
        match head {
            None => true,
            Some(h) => {
                allocating.contains(&h) || (!self.def_known(h) && !self.builtin_nonalloc(self.text(h)))
            }
        }
    }

    fn binop_allocates(&self, op: BinaryOp, sp: crate::ast::Span) -> bool {
        match op {
            BinaryOp::OpAnd => !matches!(type_at(self.st, sp), Some(Ty::Boolean)),
            BinaryOp::OpBoolAnd => false,
            BinaryOp::OpAppend => true,
            _ => false,
        }
    }

    /// `cost-expr-allocates`: every form not listed allocates.
    fn expr_allocates(&self, e: &Expr, allocating: &[Name]) -> bool {
        match e {
            Expr::Lit(..) => false,
            Expr::NameRef(n, _) => is_rt_unsafe_name(self.text(*n)) || allocating.contains(n),
            Expr::Apply(f, a, _) => {
                self.head_allocates(allocating, apply_head(e))
                    || self.expr_allocates(f, allocating)
                    || self.expr_allocates(a, allocating)
            }
            Expr::Binary(l, op, r, sp) => {
                self.binop_allocates(*op, *sp) || self.expr_allocates(l, allocating) || self.expr_allocates(r, allocating)
            }
            Expr::Unary(x, _) => self.expr_allocates(x, allocating),
            Expr::If(c, t, el, _) => {
                self.expr_allocates(c, allocating) || self.expr_allocates(t, allocating) || self.expr_allocates(el, allocating)
            }
            Expr::Let(bs, b, _) => {
                bs.iter().any(|x| self.expr_allocates(&x.value, allocating)) || self.expr_allocates(b, allocating)
            }
            Expr::Match(sc, arms, _) => {
                self.expr_allocates(sc, allocating)
                    || arms.iter().any(|a| self.expr_allocates(&a.guard, allocating) || self.expr_allocates(&a.body, allocating))
            }
            Expr::FieldAccess(obj, _, _) => self.expr_allocates(obj, allocating),
            _ => true,
        }
    }

    // ---- the budgeted and fixed rungs ----------------------------------

    fn budget_arg(c: &str) -> usize {
        c.strip_prefix("budgeted:").and_then(|n| n.parse().ok()).unwrap_or(0)
    }

    /// `cost-arg-literal`: argument N, counted from one in source order.
    fn arg_literal(args: &[&Expr], n: usize) -> bool {
        let k = args.len();
        if n == 0 || n > k {
            return false;
        }
        matches!(args[k - n], Expr::Lit(..))
    }

    fn head_overbudget(&self, over: &[Name], head: Option<Name>, args: &[&Expr], strict: bool) -> bool {
        let Some(h) = head else { return true };
        if over.contains(&h) {
            return true;
        }
        if self.def_known(h) {
            return false;
        }
        let name = self.text(h);
        let c = builtin_alloc(name);
        match c {
            "none" | "fixed" => false,
            "budgeted" => strict,
            _ if Self::budget_arg(c) > 0 => !Self::arg_literal(args, Self::budget_arg(c)),
            _ => !is_rt_safe_builtin(name),
        }
    }

    /// `cost-expr-overbudget`: the arguments are collected once at the
    /// outermost node and the walk recurses over them.
    fn expr_overbudget(&self, e: &Expr, over: &[Name], strict: bool) -> bool {
        match e {
            Expr::Lit(..) => false,
            Expr::NameRef(n, _) => is_rt_unsafe_name(self.text(*n)) || over.contains(n),
            Expr::Apply(..) => {
                let mut args = Vec::new();
                apply_args(e, &mut args);
                self.head_overbudget(over, apply_head(e), &args, strict)
                    || args.iter().any(|a| self.expr_overbudget(a, over, strict))
            }
            Expr::Binary(l, op, r, sp) => {
                self.binop_allocates(*op, *sp) || self.expr_overbudget(l, over, strict) || self.expr_overbudget(r, over, strict)
            }
            Expr::Unary(x, _) => self.expr_overbudget(x, over, strict),
            Expr::If(c, t, el, _) => {
                self.expr_overbudget(c, over, strict)
                    || self.expr_overbudget(t, over, strict)
                    || self.expr_overbudget(el, over, strict)
            }
            Expr::Let(bs, b, _) => {
                bs.iter().any(|x| self.expr_overbudget(&x.value, over, strict)) || self.expr_overbudget(b, over, strict)
            }
            Expr::Match(sc, arms, _) => {
                self.expr_overbudget(sc, over, strict)
                    || arms.iter().any(|a| self.expr_overbudget(&a.guard, over, strict) || self.expr_overbudget(&a.body, over, strict))
            }
            Expr::FieldAccess(obj, _, _) => self.expr_overbudget(obj, over, strict),
            _ => true,
        }
    }

    // ---- closure under calls ---------------------------------------------

    /// `collect-rt-mentions` with self excluded: does the body mention any
    /// of `known`?
    fn mentions_any(&self, d: &Def, known: &[Name]) -> bool {
        let mut hit = false;
        d.body.walk(&mut |e| {
            if let Expr::NameRef(n, _) = e {
                if *n != d.name && known.contains(n) {
                    hit = true;
                }
            }
        });
        hit
    }

    /// One pass per definition is enough to add every definition that
    /// reaches a member (`cost-growing-close` and kin).
    fn close(&self, mut acc: Vec<Name>) -> Vec<Name> {
        for _ in 0..self.defs.len() {
            let known = acc.clone();
            let mut grown = acc.clone();
            for d in self.defs {
                if !grown.contains(&d.name) && self.mentions_any(d, &known) {
                    grown.push(d.name);
                }
            }
            if grown.len() == acc.len() {
                break;
            }
            acc = grown;
        }
        acc
    }

    fn growing_set(&self) -> Vec<Name> {
        let seed: Vec<Name> = self
            .defs
            .iter()
            .filter(|d| {
                let params: Vec<Name> = d.params.iter().map(|p| p.name).collect();
                self.expr_grows(&d.body, d.name, &params)
            })
            .map(|d| d.name)
            .collect();
        if seed.is_empty() {
            return seed;
        }
        self.close(seed)
    }

    fn alloc_set(&self) -> Vec<Name> {
        let seed: Vec<Name> = self.defs.iter().filter(|d| self.expr_allocates(&d.body, &[])).map(|d| d.name).collect();
        if seed.is_empty() {
            return seed;
        }
        self.close(seed)
    }

    /// `cost-over-set`: the seed, then each round re-reads every body
    /// against the set so far (`cost-over-step` walks the body, not the
    /// mentions).
    fn over_set(&self, strict: bool) -> Vec<Name> {
        let mut acc: Vec<Name> =
            self.defs.iter().filter(|d| self.expr_overbudget(&d.body, &[], strict)).map(|d| d.name).collect();
        if acc.is_empty() {
            return acc;
        }
        for _ in 0..self.defs.len() {
            let known = acc.clone();
            let mut grown = acc.clone();
            for d in self.defs {
                if !grown.contains(&d.name) && self.expr_overbudget(&d.body, &known, strict) {
                    grown.push(d.name);
                }
            }
            if grown.len() == acc.len() {
                break;
            }
            acc = grown;
        }
        acc
    }

    fn any_child(&self, e: &Expr, f: impl Fn(&Expr) -> bool) -> bool {
        let mut kids: Vec<&Expr> = Vec::new();
        match e {
            Expr::If(c, t, el, _) => kids.extend([&**c, &**t, &**el]),
            Expr::Let(bs, b, _) => {
                kids.extend(bs.iter().map(|x| &x.value));
                kids.push(b);
            }
            Expr::Apply(a, b, _) | Expr::Binary(a, _, b, _) | Expr::FieldAssign(a, _, b, _) => kids.extend([&**a, &**b]),
            Expr::Unary(x, _) | Expr::Lazy(x, _) | Expr::FieldAccess(x, _, _) | Expr::Lambda(_, x, _) => kids.push(x),
            Expr::Match(sc, arms, _) | Expr::Induction(sc, arms, _) => {
                kids.push(sc);
                for a in arms {
                    kids.push(&a.guard);
                    kids.push(&a.body);
                }
            }
            Expr::List(xs, _) => kids.extend(xs.iter()),
            Expr::Record(_, fs, _) => kids.extend(fs.iter().map(|x| &x.value)),
            Expr::Act(stmts, _) => {
                for s in stmts {
                    match s {
                        crate::ast::ActStmt::Exec(x, _) | crate::ast::ActStmt::Bind(_, x, _) => kids.push(x),
                    }
                }
            }
            Expr::Try(t) => {
                for s in t.body.iter().chain(t.fallback.iter()).chain(t.failure.iter()) {
                    match s {
                        crate::ast::ActStmt::Exec(x, _) | crate::ast::ActStmt::Bind(_, x, _) => kids.push(x),
                    }
                }
            }
            Expr::Handle(h) => kids.push(&h.body),
            Expr::WithTimeout(w) => kids.push(&w.body),
            Expr::Lit(..) | Expr::NameRef(..) | Expr::Error(..) => {}
        }
        kids.into_iter().any(f)
    }
}

/// `check-bounded-decls`, after the punctual cycles: every `bounded`
/// declaration against the inferred sets.
pub fn check_bounded_decls(ch: &Chapter, st: &mut UnifyState) {
    let anns: Vec<(Name, String)> =
        ch.defs.iter().filter_map(|d| d.bounded_class.as_ref().map(|c| (d.name, c.clone()))).collect();
    if anns.is_empty() {
        return;
    }
    let cx = Cx { st, syms: &ch.syms, defs: &ch.defs };
    let growing = cx.growing_set();
    if std::env::var_os("CDX_TRACE_DIAGS").is_some() {
        let names = |v: &[Name]| v.iter().map(|n| ch.syms.text(*n).to_string()).collect::<Vec<_>>().join(" ");
        eprintln!("COST anns {:?} growing [{}]", anns.iter().map(|(n, c)| format!("{}:{c}", ch.syms.text(*n))).collect::<Vec<_>>(), names(&growing));
    }
    let allocating = if anns.iter().any(|(_, c)| c == "none") { cx.alloc_set() } else { Vec::new() };
    let over = if anns.iter().any(|(_, c)| c == "budgeted") { cx.over_set(false) } else { Vec::new() };
    let overfixed = if anns.iter().any(|(_, c)| c == "fixed") { cx.over_set(true) } else { Vec::new() };
    let mut errs: Vec<(u16, String)> = Vec::new();
    for (target, class) in &anns {
        let name = ch.syms.text(*target);
        let rank = cost_class_rank(class);
        if rank < 0 {
            errs.push((Cdx::BOUNDED_UNKNOWN_CLASS, format!("'bounded {class}' on '{name}' names no class; the lattice is none < fixed < budgeted < linear < growing")));
        } else if rank == 0 {
            if allocating.contains(target) {
                errs.push((Cdx::BOUNDED_EXCEEDED, format!("'{name}' declares bounded none but allocates, here or in something it calls")));
            }
        } else if rank == 1 {
            if overfixed.contains(target) {
                errs.push((Cdx::BOUNDED_EXCEEDED, format!("'{name}' declares bounded fixed but does not allocate the same bytes every call, here or in something it calls: a builtin whose allocation follows a budget or its input, or a definition that does")));
            }
        } else if rank == 2 {
            if over.contains(target) {
                errs.push((Cdx::BOUNDED_EXCEEDED, format!("'{name}' declares bounded budgeted but allocates past a named bound, here or in something it calls: a builtin whose allocation follows its input, or a definition that does")));
            }
        } else if rank < 4 && growing.contains(target) {
            errs.push((Cdx::BOUNDED_EXCEEDED, format!("'{name}' declares bounded {class} but is inferred growing: an accumulator is copied by & inside a self call, here or in something it calls")));
        }
    }
    for (code, msg) in errs {
        st.error(code, msg);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_lattice_is_ranked() {
        assert!(cost_class_rank("none") < cost_class_rank("fixed"));
        assert!(cost_class_rank("fixed") < cost_class_rank("budgeted"));
        assert!(cost_class_rank("budgeted") < cost_class_rank("linear"));
        assert!(cost_class_rank("linear") < cost_class_rank("growing"));
        assert_eq!(cost_class_rank("quadratic"), -1);
    }

    #[test]
    fn a_budget_names_its_argument() {
        assert_eq!(Cx::budget_arg("budgeted:3"), 3);
        assert_eq!(Cx::budget_arg("budgeted"), 0);
    }
}
