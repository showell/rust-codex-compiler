//! The linear and mutable discipline -- `check-linearity-def` and the `lin-of`
//! walk it runs.
//!
//! **A LINEAR VALUE IS USED EXACTLY ONCE.** Not at least once, not at most
//! once: a parameter declared `linear T` must be consumed on every path,
//! exactly one time, and may not escape into anything that could run it zero
//! times or twice. The whole subsystem is one walk that answers six questions
//! at once, because they are six ways for the same discipline to break and a
//! separate pass per question would walk the body six times and disagree with
//! itself at the joins.
//!
//! `lin_of` returns a `LinResult` and the combinators are where the meaning
//! lives:
//!
//! * `lin_seq` -- two things that both happen: counts ADD.
//! * `lin_branch` -- two arms of which one happens: counts must be EQUAL, and
//!   the result carries the first arm's. Unequal is not "maybe fine", it is
//!   `ok = False`.
//! * `lin_move_join` / `lin_retain_join` -- a `let` that rebinds the value to a
//!   new name. After a MOVE the old name is dead, and every later mention of it
//!   is counted into `dead` rather than into `count`, which is what separates
//!   "used twice" from "used after it was given away".
//!
//! The TAIL flag is what separates "consumed" from "returned": a linear value
//! in tail position leaves the function, and that is only legal where the
//! return type says so.

use crate::ast::{ActStmt, Def, Expr, MatchArm, Pat, TypeExpr};
use crate::check::{Cdx, Ty, UnifyState};
use crate::symbol::{Sym, SymTab};
use std::collections::BTreeMap;

/// `LinResult` (subject 50622). Six answers from one walk.
#[derive(Clone, Debug, PartialEq)]
pub struct LinResult {
    /// How many times the value is used on this path.
    pub count: i64,
    /// False once two branches disagreed about the count.
    pub ok: bool,
    /// Mentions of a name that was already moved away.
    pub dead: i64,
    /// It reaches tail position, so it leaves the function.
    pub ret: bool,
    /// The first plain (non-linear) parameter it was passed to, by callee name.
    pub esc: String,
    /// The first thing that captured it and may run zero or many times.
    pub cap: String,
}

impl LinResult {
    fn zero() -> LinResult {
        LinResult { count: 0, ok: true, dead: 0, ret: false, esc: String::new(), cap: String::new() }
    }
    fn one() -> LinResult {
        LinResult { count: 1, ..LinResult::zero() }
    }
    fn used(tail: bool) -> LinResult {
        LinResult { count: 1, ret: tail, ..LinResult::zero() }
    }
    /// `lin-flags`: is there anything here at all worth carrying?
    fn flagged(&self) -> bool {
        self.count > 0 || self.dead > 0 || !self.esc.is_empty() || !self.cap.is_empty()
    }
}

/// `lin-esc-first`: the FIRST reason wins and later ones are dropped. One
/// diagnostic per value is the contract; a second would name the same defect.
fn first(a: &str, b: &str) -> String {
    if a.is_empty() { b.to_string() } else { a.to_string() }
}

/// `lin-seq`: both happen, so the counts ADD.
fn seq(a: LinResult, b: LinResult) -> LinResult {
    LinResult {
        count: a.count + b.count,
        ok: a.ok && b.ok,
        dead: a.dead + b.dead,
        ret: a.ret || b.ret,
        esc: first(&a.esc, &b.esc),
        cap: first(&a.cap, &b.cap),
    }
}

/// `lin-branch`: one arm happens, so they must AGREE on the count.
fn branch(a: LinResult, b: LinResult) -> LinResult {
    LinResult {
        count: a.count,
        ok: a.ok && b.ok && a.count == b.count,
        dead: a.dead + b.dead,
        ret: a.ret || b.ret,
        esc: first(&a.esc, &b.esc),
        cap: first(&a.cap, &b.cap),
    }
}

/// `lin-move-join`: the value was rebound to `h` and this name is now dead, so
/// everything the old name still does counts as `dead`.
fn move_join(moved: LinResult, dead: LinResult) -> LinResult {
    LinResult {
        dead: moved.dead + dead.dead + dead.count + i64::from(!dead.ok),
        esc: first(&moved.esc, &dead.esc),
        cap: first(&moved.cap, &dead.cap),
        ..moved
    }
}

/// `lin-retain-join`: the binding STASHED the value (a closure, a partial
/// application, a list or a record) rather than moving it, so the original
/// name keeps one use and the new name is followed too.
fn retain_join(c: LinResult, moved: LinResult, dead: LinResult) -> LinResult {
    LinResult {
        count: moved.count + if c.count > 0 { c.count - 1 } else { 0 },
        ok: c.ok && moved.ok,
        dead: c.dead + moved.dead + dead.count + dead.dead + i64::from(!dead.ok),
        ret: moved.ret,
        esc: first(&c.esc, &first(&moved.esc, &dead.esc)),
        cap: first(&c.cap, &first(&moved.cap, &dead.cap)),
    }
}

/// What the walk needs to know about names it does not own.
pub struct LinEnv<'a> {
    pub syms: &'a SymTab,
    /// Every name the chapter registered, by the type it declared. Used for one
    /// question only: is the callee's k-th parameter declared linear?
    pub bindings: &'a BTreeMap<Sym, Ty>,
}

impl LinEnv<'_> {
    /// `callee-param-linear` + `registered-param-is-linear`. A callee we cannot
    /// find answers FALSE, which makes the argument an escape -- the safe
    /// direction, and upstream's.
    fn callee_param_linear(&self, head: Option<Sym>, k: usize) -> bool {
        let Some(h) = head else { return false };
        let Some(t) = self.bindings.get(&h) else { return false };
        param_at(t, k).is_some_and(|p| matches!(p, Ty::Linear(_)))
    }
}

/// The k-th parameter of a registered type, looking through quantifiers.
fn param_at(t: &Ty, k: usize) -> Option<Ty> {
    match t {
        Ty::Fun(p, _, r) => {
            if k == 0 { Some((**p).clone()) } else { param_at(r, k - 1) }
        }
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => param_at(b, k),
        _ => None,
    }
}

/// `registered-fun-param-count`.
fn param_count(t: &Ty) -> usize {
    match t {
        Ty::Fun(_, _, r) => 1 + param_count(r),
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => param_count(b),
        _ => 0,
    }
}

/// `apply-head-name`: the name at the root of an application spine.
fn head_name(e: &Expr) -> Option<Sym> {
    match e {
        Expr::Apply(f, _, _) => head_name(f),
        Expr::NameRef(n, _) => Some(*n),
        _ => None,
    }
}

/// `apply-arg-count`.
fn arg_count(e: &Expr) -> usize {
    match e {
        Expr::Apply(f, _, _) => 1 + arg_count(f),
        _ => 0,
    }
}

/// `apat-binds-name`.
fn pat_binds(p: &Pat, v: Sym) -> bool {
    match p {
        Pat::Var(n, _) => *n == v,
        Pat::Ctor(_, subs, _) | Pat::Vec_(subs, _) => subs.iter().any(|s| pat_binds(s, v)),
        _ => false,
    }
}

/// `lin-stash-elem`: a name mentioned inside a list or record literal is STORED
/// rather than consumed, and the binding that holds it retains it.
fn stashes(e: &Expr, v: Sym) -> bool {
    match e {
        Expr::NameRef(n, _) => *n == v,
        Expr::List(xs, _) => xs.iter().any(|x| stashes(x, v)),
        Expr::Record(_, fs, _) => fs.iter().any(|f| stashes(&f.value, v)),
        _ => false,
    }
}

/// `lin-of` (subject 50685).
pub fn lin_of(env: &LinEnv, v: Sym, tail: bool, e: &Expr) -> LinResult {
    match e {
        Expr::NameRef(n, _) => {
            if *n == v { LinResult::used(tail) } else { LinResult::zero() }
        }
        Expr::Apply(..) => lin_spine(env, v, head_name(e), e),
        Expr::Binary(l, _, r, _) => {
            seq(lin_of(env, v, false, l), lin_of(env, v, false, r))
        }
        Expr::Unary(x, _) => lin_of(env, v, false, x),
        Expr::If(c, t, el, _) => seq(
            lin_of(env, v, false, c),
            branch(lin_of(env, v, tail, t), lin_of(env, v, tail, el)),
        ),
        Expr::Let(binds, body, _) => lin_let(env, v, tail, binds, body, 0),
        Expr::Lambda(ps, body, _) => {
            if ps.contains(&v) { LinResult::zero() } else { lin_lambda_node(env, v, tail, body) }
        }
        Expr::Handle(h) => seq(
            lin_of(env, v, false, &h.body),
            lin_clauses(env, v, &h.clauses),
        ),
        Expr::WithTimeout(w) => lin_of(env, v, tail, &w.body),
        Expr::Match(scrut, arms, _) => seq(
            lin_of(env, v, false, scrut),
            lin_arms(env, v, tail, arms, 0),
        ),
        Expr::List(xs, _) => {
            xs.iter().fold(LinResult::zero(), |a, x| seq(a, lin_of(env, v, false, x)))
        }
        Expr::Record(_, fs, _) => fs
            .iter()
            .fold(LinResult::zero(), |a, f| seq(a, lin_of(env, v, false, &f.value))),
        Expr::FieldAccess(obj, _, _) => lin_of(env, v, false, obj),
        Expr::Act(stmts, _) => lin_stmts(env, v, stmts, 0),
        Expr::Try(t) => seq(
            lin_stmts(env, v, &t.body, 0),
            seq(lin_stmts(env, v, &t.fallback, 0), lin_stmts(env, v, &t.failure, 0)),
        ),
        Expr::FieldAssign(rec, _, val, _) => {
            seq(lin_of(env, v, false, rec), lin_of(env, v, false, val))
        }
        Expr::Lazy(inner, _) => lin_of(env, v, false, inner),
        _ => LinResult::zero(),
    }
}

/// `lin-spine`: walk an application left to right, so each argument knows its
/// own position `k` and can ask whether THAT parameter is linear.
fn lin_spine(env: &LinEnv, v: Sym, head: Option<Sym>, e: &Expr) -> LinResult {
    match e {
        Expr::Apply(f, a, _) => {
            seq(lin_spine(env, v, head, f), lin_arg(env, v, head, arg_count(f), a))
        }
        other => lin_of(env, v, false, other),
    }
}

/// `lin-arg`. The value passed directly to a linear parameter is CONSUMED;
/// passed to a plain one it ESCAPES; passed inside a lambda it is CAPTURED by
/// something that may run zero or many times.
fn lin_arg(env: &LinEnv, v: Sym, head: Option<Sym>, k: usize, a: &Expr) -> LinResult {
    match a {
        Expr::NameRef(n, _) => {
            if *n != v {
                LinResult::zero()
            } else if env.callee_param_linear(head, k) {
                LinResult::one()
            } else {
                LinResult {
                    count: 1,
                    esc: match head {
                        Some(h) => env.syms.text(h).to_string(),
                        None => "a function value".into(),
                    },
                    ..LinResult::zero()
                }
            }
        }
        Expr::Lambda(..) => {
            let c = lin_of(env, v, false, a);
            if c.flagged() {
                LinResult {
                    ret: false,
                    cap: first(&c.cap, "a closure passed as an argument"),
                    ..c
                }
            } else {
                c
            }
        }
        other => lin_of(env, v, false, other),
    }
}

/// `lin-lambda-node`: a lambda in TAIL position returns the value it closed
/// over, which is an escape by another road.
fn lin_lambda_node(env: &LinEnv, v: Sym, tail: bool, body: &Expr) -> LinResult {
    let c = lin_of(env, v, false, body);
    if tail && c.flagged() { LinResult { ret: true, ..c } } else { c }
}

/// `lin-bind-retains`: does this binding STASH the value rather than move it?
fn bind_retains(env: &LinEnv, value: &Expr, v: Sym, c: &LinResult) -> bool {
    match value {
        Expr::Lambda(..) => c.flagged(),
        Expr::Apply(..) => {
            // A PARTIAL application holds its arguments; a saturated one
            // consumes them.
            c.flagged()
                && head_name(value)
                    .and_then(|h| env.bindings.get(&h))
                    .is_some_and(|t| arg_count(value) < param_count(t))
        }
        Expr::List(..) | Expr::Record(..) => stashes(value, v),
        _ => false,
    }
}

/// `lin-let` (subject 50813) and its two joins.
fn lin_let(env: &LinEnv, v: Sym, tail: bool, binds: &[crate::ast::LetBind], body: &Expr, i: usize) -> LinResult {
    let Some(b) = binds.get(i) else { return lin_of(env, v, tail, body) };
    // `let h = v` MOVES the value to a new name.
    if matches!(&b.value, Expr::NameRef(n, _) if *n == v) {
        return lin_let_moved(env, v, b.name, tail, binds, body, i + 1);
    }
    let here = lin_of(env, v, false, &b.value);
    if bind_retains(env, &b.value, v, &here) {
        return lin_let_retained(env, v, b.name, tail, here, binds, body, i + 1);
    }
    // **A LET THAT REBINDS THE NAME ENDS THE VALUE'S STORY.** Everything after
    // is a different `v`, so the walk stops with what the bound value did.
    if b.name == v {
        return here;
    }
    seq(here, lin_let(env, v, tail, binds, body, i + 1))
}

fn lin_let_moved(env: &LinEnv, v: Sym, h: Sym, tail: bool, binds: &[crate::ast::LetBind], body: &Expr, i: usize) -> LinResult {
    if h == v {
        return lin_let(env, v, tail, binds, body, i);
    }
    move_join(
        lin_let(env, h, tail, binds, body, i),
        lin_let(env, v, false, binds, body, i),
    )
}

fn lin_let_retained(env: &LinEnv, v: Sym, h: Sym, tail: bool, c: LinResult, binds: &[crate::ast::LetBind], body: &Expr, i: usize) -> LinResult {
    if h == v {
        return c;
    }
    retain_join(
        c,
        lin_let(env, h, tail, binds, body, i),
        lin_let(env, v, false, binds, body, i),
    )
}

/// `lin-stmts`. A `<-` that rebinds the name ends the story, as a let does.
fn lin_stmts(env: &LinEnv, v: Sym, stmts: &[ActStmt], i: usize) -> LinResult {
    let Some(s) = stmts.get(i) else { return LinResult::zero() };
    match s {
        ActStmt::Exec(e, _) => seq(lin_of(env, v, false, e), lin_stmts(env, v, stmts, i + 1)),
        ActStmt::Bind(n, e, _) => {
            if *n == v {
                lin_of(env, v, false, e)
            } else {
                seq(lin_of(env, v, false, e), lin_stmts(env, v, stmts, i + 1))
            }
        }
    }
}

/// `lin-arms`. Arms BRANCH against each other, and an arm whose pattern binds
/// the name is a different value entirely.
fn lin_arms(env: &LinEnv, v: Sym, tail: bool, arms: &[MatchArm], i: usize) -> LinResult {
    let Some(arm) = arms.get(i) else { return LinResult::zero() };
    let this = if pat_binds(&arm.pattern, v) {
        LinResult::zero()
    } else {
        seq(lin_of(env, v, false, &arm.guard), lin_of(env, v, tail, &arm.body))
    };
    if i + 1 >= arms.len() {
        this
    } else {
        branch(this, lin_arms(env, v, tail, arms, i + 1))
    }
}

/// `lin-clauses`: a handler clause may run zero or many times.
fn lin_clauses(env: &LinEnv, v: Sym, clauses: &[crate::ast::HandleClause]) -> LinResult {
    clauses.iter().fold(LinResult::zero(), |acc, cl| {
        let here = if cl.params.contains(&v) || cl.resume_name == v {
            LinResult::zero()
        } else {
            let c = lin_of(env, v, false, &cl.body);
            if c.flagged() {
                LinResult { ret: false, cap: first(&c.cap, "a handler clause"), ..c }
            } else {
                c
            }
        };
        seq(acc, here)
    })
}

// ---------------------------------------------------------------------------
// Minted owners
// ---------------------------------------------------------------------------

/// `return-is-linear-after` (subject 51195). Does applying `k` arguments to
/// this type yield a `linear`?
///
/// **A PARTIAL APPLICATION IS NOT A MINT**: the `FunTy` arm answers False the
/// moment `k` runs out, because what you are holding is still a function.
fn returns_linear_after(t: &Ty, k: usize) -> bool {
    match t {
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => returns_linear_after(b, k),
        Ty::Fun(_, _, r) => k > 0 && returns_linear_after(r, k - 1),
        Ty::Effectful(_, _, ret) => k == 0 && returns_linear_after(ret, 0),
        Ty::Linear(_) => k == 0,
        _ => false,
    }
}

/// `expr-is-mint`: this expression CREATES a linear owner, so the name it is
/// bound to carries the discipline even though no parameter declared it.
fn expr_is_mint(env: &LinEnv, e: &Expr) -> bool {
    let Expr::Apply(..) = e else { return false };
    head_name(e)
        .and_then(|h| env.bindings.get(&h))
        .is_some_and(|t| returns_linear_after(t, arg_count(e)))
}

/// `report-minted-owner` (subject 51331). The same six questions as a declared
/// parameter, and the same order -- only the value's provenance differs, and
/// the message says so.
fn report_minted_owner(def: &Def, env: &LinEnv, v: Sym, r: &LinResult, st: &mut UnifyState) {
    let name = env.syms.text(v);
    let owner = env.syms.text(def.name);
    let minted = "minted by a linear-returning call";
    let bad_ret = r.ret && !return_sanctioned(env.syms, def);

    if r.dead > 0 {
        st.error(Cdx::USE_AFTER_CONSUME, format!(
            "Linear value '{name}', {minted}, was moved to a new owner by a let binding and then mentioned again; after a move the original name is dead"));
    } else if !r.cap.is_empty() {
        st.error(Cdx::LINEAR_CAPTURE, format!(
            "Linear value '{name}', {minted}, is captured by {}, which may run zero or many times; a linear value may be captured only by a let-bound closure, which is then called exactly once", r.cap));
    } else if !r.esc.is_empty() {
        st.error(Cdx::LINEAR_ESCAPE, format!(
            "Linear value '{name}', {minted}, is passed to a plain (non-linear) parameter of '{}'; a linear value moves only through parameters declared linear. Use freeze to exit the discipline deliberately", r.esc));
    } else if bad_ret {
        st.error(Cdx::LINEAR_RETURN, format!(
            "Linear value '{name}', {minted}, is returned from '{owner}', whose return type is not declared linear; declare the return linear, or consume the value with freeze"));
    } else if !r.ok {
        st.error(Cdx::USE_AFTER_CONSUME, format!(
            "Linear value '{name}', {minted}, is used a different number of times across branches; each branch must use it exactly once"));
    } else if r.count > 1 {
        st.error(Cdx::USE_AFTER_CONSUME, format!(
            "Linear value '{name}', {minted}, is used {} times; a linear value must be used exactly once", r.count));
    } else if r.count == 0 {
        st.error(Cdx::LINEAR_UNUSED, format!(
            "Linear value '{name}', {minted}, is never used; a linear value must be used exactly once"));
    }
}

/// `check-mints` (subject 51350). A walk looking for BINDINGS, not for uses:
/// every `let` and every `<-` is asked whether the value it binds was minted,
/// and if so the name is followed for the rest of its scope with the same
/// `lin_of` machinery a declared parameter gets.
///
/// The TAIL flag rides along for the same reason it does there.
pub fn check_mints(def: &Def, env: &LinEnv, tail: bool, e: &Expr, st: &mut UnifyState) {
    match e {
        Expr::Let(binds, body, _) => check_mints_binds(def, env, tail, binds, body, 0, st),
        Expr::If(c, t, el, _) => {
            check_mints(def, env, false, c, st);
            check_mints(def, env, tail, t, st);
            check_mints(def, env, tail, el, st);
        }
        Expr::Apply(f, a, _) => {
            check_mints(def, env, false, f, st);
            check_mints(def, env, false, a, st);
        }
        Expr::Binary(l, _, r, _) => {
            check_mints(def, env, false, l, st);
            check_mints(def, env, false, r, st);
        }
        Expr::Unary(x, _) => check_mints(def, env, false, x, st),
        Expr::Lambda(_, body, _) => check_mints(def, env, false, body, st),
        Expr::Handle(h) => {
            check_mints(def, env, false, &h.body, st);
            for cl in &h.clauses {
                check_mints(def, env, false, &cl.body, st);
            }
        }
        Expr::WithTimeout(w) => check_mints(def, env, tail, &w.body, st),
        Expr::Match(scrut, arms, _) => {
            check_mints(def, env, false, scrut, st);
            for arm in arms {
                check_mints(def, env, false, &arm.guard, st);
                check_mints(def, env, tail, &arm.body, st);
            }
        }
        Expr::List(xs, _) => {
            for x in xs {
                check_mints(def, env, false, x, st);
            }
        }
        Expr::Record(_, fs, _) => {
            for f in fs {
                check_mints(def, env, false, &f.value, st);
            }
        }
        Expr::FieldAccess(obj, _, _) => check_mints(def, env, false, obj, st),
        Expr::Act(stmts, _) => check_mints_stmts(def, env, stmts, 0, st),
        Expr::Try(t) => {
            check_mints_stmts(def, env, &t.body, 0, st);
            check_mints_stmts(def, env, &t.fallback, 0, st);
            check_mints_stmts(def, env, &t.failure, 0, st);
        }
        Expr::FieldAssign(rec, _, val, _) => {
            check_mints(def, env, false, rec, st);
            check_mints(def, env, false, val, st);
        }
        Expr::Lazy(inner, _) => check_mints(def, env, false, inner, st),
        _ => {}
    }
}

fn check_mints_binds(def: &Def, env: &LinEnv, tail: bool, binds: &[crate::ast::LetBind], body: &Expr, i: usize, st: &mut UnifyState) {
    let Some(b) = binds.get(i) else {
        return check_mints(def, env, tail, body, st);
    };
    check_mints(def, env, false, &b.value, st);
    if expr_is_mint(env, &b.value) {
        let r = lin_let(env, b.name, tail, binds, body, i + 1);
        report_minted_owner(def, env, b.name, &r, st);
    }
    check_mints_binds(def, env, tail, binds, body, i + 1, st);
}

fn check_mints_stmts(def: &Def, env: &LinEnv, stmts: &[ActStmt], i: usize, st: &mut UnifyState) {
    let Some(s) = stmts.get(i) else { return };
    match s {
        ActStmt::Exec(e, _) => check_mints(def, env, false, e, st),
        ActStmt::Bind(n, e, _) => {
            check_mints(def, env, false, e, st);
            if expr_is_mint(env, e) {
                let r = lin_stmts(env, *n, stmts, i + 1);
                report_minted_owner(def, env, *n, &r, st);
            }
        }
    }
    check_mints_stmts(def, env, stmts, i + 1, st);
}

// ---------------------------------------------------------------------------
// The entry point
// ---------------------------------------------------------------------------

/// `is-linear-atype`: SYNTACTIC. `linear T` in the declaration, not a resolved
/// type -- the discipline is something the author wrote down.
fn is_linear_atype(t: &TypeExpr) -> bool {
    matches!(t, TypeExpr::Linear(..))
}

/// `atype-strip-effect`.
fn strip_effect(t: &TypeExpr) -> &TypeExpr {
    match t {
        TypeExpr::Effect(_, _, _, ret, _) => ret,
        other => other,
    }
}

/// `afun-return-after`: the return type after `k` parameters.
fn return_after(t: &TypeExpr, k: usize) -> &TypeExpr {
    match (k, t) {
        (0, _) => t,
        (_, TypeExpr::Fun(_, r, _)) => return_after(r, k - 1),
        _ => t,
    }
}

/// `atype-core-name`: the name under any wrappers.
fn core_name(t: &TypeExpr) -> Option<Sym> {
    match t {
        TypeExpr::Linear(inner, _) => core_name(inner),
        TypeExpr::Named(n, _) => Some(*n),
        TypeExpr::App(head, _, _) => core_name(head),
        _ => None,
    }
}

/// `atype-app-arg-list` + `atype-tuple-has-linear`: a tuple return sanctions a
/// linear component.
fn tuple_has_linear(syms: &SymTab, t: &TypeExpr) -> bool {
    let mut args: Vec<&TypeExpr> = Vec::new();
    let mut cur = t;
    while let TypeExpr::App(head, a, _) = cur {
        args.splice(0..0, a.iter());
        cur = head;
    }
    if args.is_empty() {
        return false;
    }
    let want = format!("Tup{}", args.len());
    core_name(t).is_some_and(|n| syms.text(n) == want) && args.iter().any(|a| is_linear_atype(a))
}

/// `is-freeze-door`: `freeze`, whose whole job is to leave the discipline, and
/// whose body is a bare name.
fn is_freeze_door(syms: &SymTab, def: &Def) -> bool {
    syms.text(def.name) == "freeze" && matches!(def.body, Expr::NameRef(..))
}

/// `linear-return-sanctioned`: may this definition hand a linear value back?
fn return_sanctioned(syms: &SymTab, def: &Def) -> bool {
    let Some(dt) = def.declared_type.first() else { return false };
    if is_freeze_door(syms, def) {
        return true;
    }
    let rt = strip_effect(return_after(dt, def.params.len()));
    is_linear_atype(rt) || tuple_has_linear(syms, rt)
}

/// `check-linearity-def` (subject 51065). **A DEFINITION THAT DECLARES NO TYPE
/// IS NOT CHECKED**: the discipline is something the author wrote down, and
/// there is nothing written down here.
pub fn check_def(def: &Def, env: &LinEnv, st: &mut UnifyState) {
    let Some(dt) = def.declared_type.first() else { return };
    let mut ty = dt;
    for p in &def.params {
        let TypeExpr::Fun(pty, rest, _) = ty else { break };
        check_one_param(def, env, pty, p, st);
        ty = rest;
    }
    // Parameters first, then the values the body MINTS -- upstream's order, and
    // it decides which diagnostic a definition with both reports first.
    check_mints(def, env, true, &def.body, st);
}

fn check_one_param(def: &Def, env: &LinEnv, pty: &TypeExpr, p: &crate::ast::Param, st: &mut UnifyState) {
    if !is_linear_atype(pty) {
        return;
    }
    let r = lin_of(env, p.name, true, &def.body);
    let name = env.syms.text(p.name);
    let owner = env.syms.text(def.name);
    let bad_ret = r.ret && !return_sanctioned(env.syms, def);

    // **THE ORDER IS THE DIAGNOSIS.** Upstream tests dead, then capture, then
    // escape, then return, then branch disagreement, then the counts -- and a
    // value that is both captured and used twice is reported as CAPTURED,
    // because that is the reason the count is wrong.
    if r.dead > 0 {
        st.error(Cdx::USE_AFTER_CONSUME, format!(
            "Linear value '{name}' was moved to a new owner by a let binding and then mentioned again; after a move the original name is dead"));
    } else if !r.cap.is_empty() {
        st.error(Cdx::LINEAR_CAPTURE, format!(
            "Linear value '{name}' is captured by {}, which may run zero or many times; a linear value may be captured only by a let-bound closure, which is then called exactly once", r.cap));
    } else if !r.esc.is_empty() {
        st.error(Cdx::LINEAR_ESCAPE, format!(
            "Linear value '{name}' is passed to a plain (non-linear) parameter of '{}'; a linear value moves only through parameters declared linear. Use freeze to exit the discipline deliberately", r.esc));
    } else if bad_ret {
        st.error(Cdx::LINEAR_RETURN, format!(
            "Linear value '{name}' is returned from '{owner}', whose return type is not declared linear; that is an unsanctioned freeze. Declare the return linear, or consume the value with freeze"));
    } else if !r.ok {
        st.error(Cdx::USE_AFTER_CONSUME, format!(
            "Linear value '{name}' is used a different number of times across branches; each branch must use it exactly once"));
    } else if r.count > 1 {
        st.error(Cdx::USE_AFTER_CONSUME, format!(
            "Linear value '{name}' is used {} times; a linear value must be used exactly once", r.count));
    } else if r.count == 0 {
        st.error(Cdx::LINEAR_UNUSED, format!(
            "Linear value '{name}' is never used; a linear value must be used exactly once"));
    }
}

/// The rules the gate cannot localise: each of these is one sentence of the
/// discipline, and a refactor that breaks one would still pass most of the
/// corpus units.
#[cfg(test)]
mod the_discipline {
    /// The CDX codes a chapter reports, in order.
    fn codes(body: &str) -> Vec<u16> {
        let src = format!(
            "Chapter: T\n\nSection: S\n  consume : linear Integer -> Integer\n  consume (n) = n * 2\n\n{body}"
        );
        let bytes = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&bytes);
        let mut dg = crate::desugar::Desugar::new(&bytes);
        let ch = dg.chapter(&parsed.tree);
        let (_, st, _) = crate::check::check_chapter_full(&ch);
        st.diags.iter().map(|d| d.code).collect()
    }

    #[test]
    fn exactly_once_is_clean_and_twice_and_never_are_not() {
        assert_eq!(codes("  f : linear Integer -> Integer\n  f (n) = consume n\n"), vec![]);
        assert_eq!(
            codes("  f : linear Integer -> Integer\n  f (n) = consume n + consume n\n"),
            vec![crate::check::Cdx::USE_AFTER_CONSUME]
        );
        assert_eq!(
            codes("  f : linear Integer -> Integer\n  f (n) = 7\n"),
            vec![crate::check::Cdx::LINEAR_UNUSED]
        );
    }

    /// **BRANCHES MUST AGREE, AND THE COUNT IS NOT A MAXIMUM.** One arm using
    /// it and the other not is a defect even though one path is correct --
    /// `lin_branch` requires equality rather than taking either side.
    #[test]
    fn the_arms_of_an_if_must_use_it_the_same_number_of_times() {
        assert_eq!(
            codes("  f : linear Integer, Boolean -> Integer\n  f (n) (b) = if b then consume n else 0\n"),
            vec![crate::check::Cdx::USE_AFTER_CONSUME]
        );
        // Both arms consume it once: correct, and the total is still one.
        assert_eq!(
            codes("  f : linear Integer, Boolean -> Integer\n  f (n) (b) = if b then consume n else consume n\n"),
            vec![]
        );
    }

    /// **A LET THAT REBINDS THE NAME ENDS THE VALUE'S STORY.** Everything after
    /// is a different `n`, and counting the shadow would report a use the
    /// linear value never had. `linear-smoke`'s `shadow-test` is this case.
    #[test]
    fn a_shadowing_let_ends_the_story() {
        assert_eq!(
            codes("  f : linear Integer -> Integer\n  f (n) = let base = consume n\n   in let n = 7\n   in base + n + n\n"),
            vec![]
        );
    }

    /// Passing it to a plain parameter is an ESCAPE, and the callee is named.
    #[test]
    fn a_plain_parameter_is_an_escape() {
        assert_eq!(
            codes("  plain : Integer -> Integer\n  plain (x) = x\n\n  f : linear Integer -> Integer\n  f (n) = plain n\n"),
            vec![crate::check::Cdx::LINEAR_ESCAPE]
        );
    }

    /// A definition with NO declared type is not checked at all: the discipline
    /// is something the author wrote down.
    #[test]
    fn an_undeclared_definition_is_not_checked() {
        assert_eq!(codes("  f (n) = 7\n"), vec![]);
    }

    /// A value MINTED by a linear-returning call carries the discipline even
    /// though no parameter declared it.
    fn minted(body: &str) -> Vec<u16> {
        codes(&format!(
            "  acquire : Integer -> linear Integer\n  acquire (n) = n\n\n  release : linear Integer -> Integer\n  release (g) = g + 0\n\n{body}"
        ))
    }

    #[test]
    fn a_minted_owner_is_bound_by_the_same_rules() {
        assert_eq!(
            minted("  f : Integer -> Integer\n  f (n) = let g = acquire n in release g\n"),
            vec![]
        );
        assert_eq!(
            minted("  f : Integer -> Integer\n  f (n) = let g = acquire n in release g + release g\n"),
            vec![crate::check::Cdx::USE_AFTER_CONSUME]
        );
        assert_eq!(
            minted("  f : Integer -> Integer\n  f (n) = let g = acquire n in n + 1\n"),
            vec![crate::check::Cdx::LINEAR_UNUSED]
        );
    }

    /// **A PARTIAL APPLICATION IS NOT A MINT.** `acquire` with no argument is
    /// still a function, and binding it mints nothing -- so the name it is
    /// bound to is not under the discipline and using it twice is fine.
    #[test]
    fn a_partial_application_mints_nothing() {
        assert_eq!(
            minted("  f : Integer -> Integer\n  f (n) = let mk = acquire in release (mk n) + release (mk n)\n"),
            vec![]
        );
    }
}
