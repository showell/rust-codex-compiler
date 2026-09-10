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
use crate::check::{Cdx, Ty, TypeDefs, UnifyState};
use crate::lowering_types as lt;
use crate::symbol::{Sym, SymTab};
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

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

/// `lin-path-max`: two paths of which one is taken, where they are allowed to
/// disagree. The mutable rule counts the WORST path rather than demanding the
/// arms match, which is what separates it from `branch`.
fn path_max(a: LinResult, b: LinResult) -> LinResult {
    LinResult {
        count: if a.count >= b.count { a.count } else { b.count },
        ok: a.ok && b.ok,
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
    /// The chapter's type declarations. The mutable walk reads record FIELDS,
    /// which `Ty::Record` does not carry.
    pub tds: &'a TypeDefs,
    /// The record types declared `mutable` -- upstream's `"__mutable-" & name`
    /// markers.
    pub mutables: &'a BTreeSet<Sym>,
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
pub fn check_mints(def: &Def, env: &LinEnv, tup: &TupEnv, tail: bool, e: &Expr, st: &mut UnifyState) {
    match e {
        Expr::Let(binds, body, _) => check_mints_binds(def, env, tup, tail, binds, body, 0, st),
        Expr::If(c, t, el, _) => {
            check_mints(def, env, tup, false, c, st);
            check_mints(def, env, tup, tail, t, st);
            check_mints(def, env, tup, tail, el, st);
        }
        Expr::Apply(f, a, _) => {
            check_mints(def, env, tup, false, f, st);
            check_mints(def, env, tup, false, a, st);
        }
        Expr::Binary(l, _, r, _) => {
            check_mints(def, env, tup, false, l, st);
            check_mints(def, env, tup, false, r, st);
        }
        Expr::Unary(x, _) => check_mints(def, env, tup, false, x, st),
        Expr::Lambda(_, body, _) => check_mints(def, env, tup, false, body, st),
        Expr::Handle(h) => {
            check_mints(def, env, tup, false, &h.body, st);
            for cl in &h.clauses {
                check_mints(def, env, tup, false, &cl.body, st);
            }
        }
        Expr::WithTimeout(w) => check_mints(def, env, tup, tail, &w.body, st),
        Expr::Match(scrut, arms, _) => {
            check_mints(def, env, tup, false, scrut, st);
            // `check-mints-arms` carries ONE tuple type for every arm: it is
            // the scrutinee's, and the arms only decide where its linear
            // components land.
            let tt = tuple_mint_type(env, tup, scrut);
            for arm in arms {
                check_mints(def, env, tup, false, &arm.guard, st);
                match &tt {
                    Some(t) => check_tuple_arm(def, env, tup, tail, t, arm, st),
                    None => check_mints(def, env, tup, tail, &arm.body, st),
                }
            }
        }
        Expr::List(xs, _) => {
            for x in xs {
                check_mints(def, env, tup, false, x, st);
            }
        }
        Expr::Record(_, fs, _) => {
            for f in fs {
                check_mints(def, env, tup, false, &f.value, st);
            }
        }
        Expr::FieldAccess(obj, _, _) => check_mints(def, env, tup, false, obj, st),
        Expr::Act(stmts, _) => check_mints_stmts(def, env, tup, stmts, 0, st),
        Expr::Try(t) => {
            check_mints_stmts(def, env, tup, &t.body, 0, st);
            check_mints_stmts(def, env, tup, &t.fallback, 0, st);
            check_mints_stmts(def, env, tup, &t.failure, 0, st);
        }
        Expr::FieldAssign(rec, _, val, _) => {
            check_mints(def, env, tup, false, rec, st);
            check_mints(def, env, tup, false, val, st);
        }
        Expr::Lazy(inner, _) => check_mints(def, env, tup, false, inner, st),
        _ => {}
    }
}

fn check_mints_binds(def: &Def, env: &LinEnv, tup: &TupEnv, tail: bool, binds: &[crate::ast::LetBind], body: &Expr, i: usize, st: &mut UnifyState) {
    let Some(b) = binds.get(i) else {
        return check_mints(def, env, tup, tail, body, st);
    };
    check_mints(def, env, tup, false, &b.value, st);
    let tt = tuple_mint_type(env, tup, &b.value);
    if expr_is_mint(env, &b.value) || tt.is_some() {
        // A tuple carrying a linear component makes its NAME an owner too:
        // dropping the pair drops the component inside it.
        let r = lin_let(env, b.name, tail, binds, body, i + 1);
        report_minted_owner(def, env, b.name, &r, st);
    } else if let Some(mtn) = expr_mut_mint_name(env, &b.value) {
        let r = consume_let(env, mtn, b.name, binds, body, i + 1);
        report_minted_mutable(def, env, b.name, &r, st);
    }
    let next = after_tuple_bind(tup, b.name, tt.as_ref());
    check_mints_binds(def, env, &next, tail, binds, body, i + 1, st);
}

fn check_mints_stmts(def: &Def, env: &LinEnv, tup: &TupEnv, stmts: &[ActStmt], i: usize, st: &mut UnifyState) {
    let Some(s) = stmts.get(i) else { return };
    match s {
        ActStmt::Exec(e, _) => check_mints(def, env, tup, false, e, st),
        ActStmt::Bind(n, e, _) => {
            check_mints(def, env, tup, false, e, st);
            let tt = tuple_mint_type(env, tup, e);
            if expr_is_mint(env, e) || tt.is_some() {
                let r = lin_stmts(env, *n, stmts, i + 1);
                report_minted_owner(def, env, *n, &r, st);
            } else if let Some(mtn) = expr_mut_mint_name(env, e) {
                let r = consume_stmts(env, mtn, *n, stmts, i + 1);
                report_minted_mutable(def, env, *n, &r, st);
            }
            let next = after_tuple_bind(tup, *n, tt.as_ref());
            return check_mints_stmts(def, env, &next, stmts, i + 1, st);
        }
    }
    check_mints_stmts(def, env, tup, stmts, i + 1, st);
}

// ---------------------------------------------------------------------------
// A tuple that carries a linear component
// ---------------------------------------------------------------------------

/// Which names currently hold a tuple with a linear component in it, and what
/// that tuple's type is -- upstream's `"__tupmint-" & v` bindings. It is scoped
/// to one definition's `check_mints` walk and rebound the way upstream rebinds,
/// so it is threaded by value rather than living on `LinEnv`.
type TupEnv = BTreeMap<Sym, Ty>;

/// `tuple-linear-positions`: the argument slots of a `TupN` that were declared
/// `linear`. **THE ARITY MUST MATCH THE NAME**: `Tup2` with three arguments is
/// not a tuple, and answering positions for it would put the discipline on a
/// value that never had it.
fn tuple_linear_positions(syms: &SymTab, t: &Ty) -> Vec<usize> {
    let (n, args) = match t {
        Ty::Constructed(n, args) | Ty::Sum(n, args) => (n, args),
        _ => return Vec::new(),
    };
    if syms.text(*n) != format!("Tup{}", args.len()) {
        return Vec::new();
    }
    args.iter()
        .enumerate()
        .filter(|(_, a)| matches!(a, Ty::Linear(_)))
        .map(|(i, _)| i)
        .collect()
}

/// `return-type-after`: what applying `k` arguments yields. Unlike
/// `peel_returns_n`, running out of arrow before running out of arguments is a
/// failure rather than the type itself -- a partial application is not a value
/// of the return type.
fn return_type_after(t: &Ty, k: usize) -> Option<&Ty> {
    match t {
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => return_type_after(b, k),
        Ty::Fun(_, _, r) => {
            if k == 0 { None } else { return_type_after(r, k - 1) }
        }
        Ty::Effectful(_, _, ret) => {
            if k == 0 { return_type_after(ret, 0) } else { None }
        }
        other => {
            if k == 0 { Some(other) } else { None }
        }
    }
}

/// `expr-tuple-mint-type` + `tuple-mint-only`: the tuple type this expression
/// yields, kept ONLY when some component of it is linear. A name answers from
/// what it was bound to, which is how the discipline survives
/// `let p = acquire2 n in let (g, k) = p`.
fn tuple_mint_type(env: &LinEnv, tup: &TupEnv, e: &Expr) -> Option<Ty> {
    let t = match e {
        Expr::Apply(..) => {
            let reg = env.bindings.get(&head_name(e)?)?;
            return_type_after(reg, arg_count(e))?.clone()
        }
        Expr::NameRef(n, _) => tup.get(n)?.clone(),
        _ => return None,
    };
    (!tuple_linear_positions(env.syms, &t).is_empty()).then_some(t)
}

/// `env-after-tuple-bind`. Binding a name to a tuple-mint records it; binding
/// it to anything else must ERASE an older record under the same name, or a
/// shadowed binding keeps the discipline of a value it no longer holds.
fn after_tuple_bind<'a>(tup: &'a TupEnv, v: Sym, tt: Option<&Ty>) -> Cow<'a, TupEnv> {
    match tt {
        Some(t) => {
            let mut m = tup.clone();
            m.insert(v, t.clone());
            Cow::Owned(m)
        }
        None if tup.contains_key(&v) => {
            let mut m = tup.clone();
            m.remove(&v);
            Cow::Owned(m)
        }
        None => Cow::Borrowed(tup),
    }
}

/// `check-tuple-arm` (subject 51283). The scrutinee yielded a tuple with a
/// linear component, so the pattern that takes it apart decides where the
/// discipline lands.
fn check_tuple_arm(
    def: &Def,
    env: &LinEnv,
    tup: &TupEnv,
    tail: bool,
    tt: &Ty,
    arm: &MatchArm,
    st: &mut UnifyState,
) {
    match &arm.pattern {
        Pat::Ctor(_, subs, _) => {
            for pos in tuple_linear_positions(env.syms, tt) {
                if let Some(sub) = subs.get(pos) {
                    check_tuple_component(def, env, tail, sub, pos, &arm.body, st);
                }
            }
            check_mints(def, env, tup, tail, &arm.body, st);
        }
        // The whole tuple is bound to one name: that NAME carries the
        // discipline, and it carries the tuple type into the body so a later
        // destructuring still finds it.
        Pat::Var(n, _) => {
            let r = lin_of(env, *n, tail, &arm.body);
            report_minted_owner(def, env, *n, &r, st);
            let inner = after_tuple_bind(tup, *n, Some(tt));
            check_mints(def, env, &inner, tail, &arm.body, st);
        }
        Pat::Wild(_) => {
            st.error(Cdx::LINEAR_UNUSED,
                "A tuple carrying a linear component is discarded by a wildcard pattern; bind each linear component and use it exactly once".to_string());
            check_mints(def, env, tup, tail, &arm.body, st);
        }
        _ => check_mints(def, env, tup, tail, &arm.body, st),
    }
}

/// `check-tuple-component`: one linear slot of the tuple, and only the slots
/// the TYPE says are linear -- a plain component beside a linear one is an
/// ordinary binding and is not walked.
fn check_tuple_component(
    def: &Def,
    env: &LinEnv,
    tail: bool,
    sub: &Pat,
    pos: usize,
    body: &Expr,
    st: &mut UnifyState,
) {
    match sub {
        Pat::Var(n, _) => {
            let r = lin_of(env, *n, tail, body);
            report_minted_owner(def, env, *n, &r, st);
        }
        Pat::Wild(_) => st.error(Cdx::LINEAR_UNUSED, format!(
            "Linear component {pos} of a tuple is discarded by a wildcard pattern; bind it and use it exactly once")),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// The mutable discipline
// ---------------------------------------------------------------------------

/// `type-mentions-mut` (subject 50906). Fuel-bounded because a record's fields
/// can reach the record again, and a self-referential type would otherwise
/// walk forever.
fn type_mentions_mut(env: &LinEnv, t: &Ty, target: Sym, fuel: i32) -> bool {
    if fuel <= 0 {
        return false;
    }
    match t {
        Ty::Record(n, args) => {
            *n == target
                || args.iter().any(|a| type_mentions_mut(env, a, target, fuel - 1))
                || env.tds.record_fields(*n).is_some_and(|fs| {
                    fs.iter().any(|(_, ft)| type_mentions_mut(env, ft, target, fuel - 1))
                })
        }
        Ty::Constructed(n, args) => {
            *n == target
                || args.iter().any(|a| type_mentions_mut(env, a, target, fuel - 1))
                || env
                    .tds
                    .declared()
                    .get(n)
                    .is_some_and(|r| type_mentions_mut(env, r, target, fuel - 1))
        }
        Ty::Fun(_, _, r) => type_mentions_mut(env, r, target, fuel - 1),
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => type_mentions_mut(env, b, target, fuel - 1),
        Ty::Effectful(_, _, inner) => type_mentions_mut(env, inner, target, fuel - 1),
        Ty::Linear(inner) => type_mentions_mut(env, inner, target, fuel - 1),
        _ => false,
    }
}

/// `return-mentions-mut`: does the value this call HANDS BACK still hold the
/// mutable record? A `List Counter` does, and so does a `(Integer, Counter)` --
/// which is why laundering it through a container is not an escape from the
/// rule.
fn return_mentions_mut(env: &LinEnv, t: &Ty, target: Sym, fuel: i32) -> bool {
    if fuel <= 0 {
        return false;
    }
    match t {
        Ty::List(e) | Ty::LinkedList(e) => return_mentions_mut(env, e, target, fuel - 1),
        Ty::Sum(_, args) => args.iter().any(|a| type_mentions_mut(env, a, target, fuel - 1)),
        Ty::Fun(_, _, r) => return_mentions_mut(env, r, target, fuel - 1),
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => return_mentions_mut(env, b, target, fuel - 1),
        Ty::Effectful(_, _, inner) => return_mentions_mut(env, inner, target, fuel - 1),
        Ty::Linear(inner) => return_mentions_mut(env, inner, target, fuel - 1),
        other => type_mentions_mut(env, other, target, fuel),
    }
}

/// `apply-threads`: does this call pass the mutable record ON to a new owner?
/// A callee we cannot find answers FALSE -- the opposite of the linear rule's
/// safe direction, because here an unknown callee is assumed to consume and
/// discard rather than to thread.
fn apply_threads(env: &LinEnv, target: Sym, e: &Expr) -> bool {
    let Some(h) = head_name(e) else { return false };
    let Some(t) = env.bindings.get(&h) else { return false };
    lt::peel_returns_n(t, arg_count(e))
        .is_some_and(|r| return_mentions_mut(env, r, target, 8))
}

/// `arg-is-bare` + `spine-has-bare`: is the name passed to this call DIRECTLY,
/// rather than inside an expression?
fn spine_has_bare(v: Sym, e: &Expr) -> bool {
    match e {
        Expr::Apply(f, a, _) => {
            matches!(a.as_ref(), Expr::NameRef(n, _) if *n == v) || spine_has_bare(v, f)
        }
        _ => false,
    }
}

/// `consume-of` (subject 50974). **A DIFFERENT RULE FROM `lin_of`, WALKED THE
/// SAME WAY.** A mutable record may be handed to a new owner at most once, and
/// only a hand-off counts: reading a field of it is free, and passing it to a
/// call that does not give it back is a consumption that ends there. So the
/// walk carries the mutable TYPE name as well as the variable -- the type is
/// what tells it whether a callee threads the record onward.
fn consume_of(env: &LinEnv, target: Sym, v: Sym, e: &Expr) -> LinResult {
    match e {
        Expr::NameRef(n, _) => {
            if *n == v { LinResult::one() } else { LinResult::zero() }
        }
        Expr::FieldAccess(obj, _, _) => consume_read(env, target, v, obj),
        Expr::Apply(..) => {
            let threads = spine_has_bare(v, e) && apply_threads(env, target, e);
            consume_spine(env, target, v, threads, e)
        }
        Expr::Binary(l, _, r, _) => {
            seq(consume_of(env, target, v, l), consume_of(env, target, v, r))
        }
        Expr::Unary(x, _) => consume_of(env, target, v, x),
        Expr::If(c, t, el, _) => seq(
            consume_of(env, target, v, c),
            path_max(consume_of(env, target, v, t), consume_of(env, target, v, el)),
        ),
        Expr::Let(binds, body, _) => consume_let(env, target, v, binds, body, 0),
        Expr::Lambda(ps, body, _) => {
            if ps.contains(&v) { LinResult::zero() } else { consume_of(env, target, v, body) }
        }
        Expr::Handle(h) => seq(
            consume_of(env, target, v, &h.body),
            consume_clauses(env, target, v, &h.clauses),
        ),
        Expr::WithTimeout(w) => consume_of(env, target, v, &w.body),
        Expr::Match(scrut, arms, _) => seq(
            consume_of(env, target, v, scrut),
            consume_arms(env, target, v, arms, 0),
        ),
        Expr::List(xs, _) => xs
            .iter()
            .fold(LinResult::zero(), |a, x| seq(a, consume_of(env, target, v, x))),
        Expr::Record(_, fs, _) => fs
            .iter()
            .fold(LinResult::zero(), |a, f| seq(a, consume_of(env, target, v, &f.value))),
        Expr::Act(stmts, _) => consume_stmts(env, target, v, stmts, 0),
        Expr::Try(t) => seq(
            consume_stmts(env, target, v, &t.body, 0),
            path_max(
                consume_stmts(env, target, v, &t.fallback, 0),
                consume_stmts(env, target, v, &t.failure, 0),
            ),
        ),
        Expr::FieldAssign(rec, _, val, _) => seq(
            consume_read(env, target, v, rec),
            consume_of(env, target, v, val),
        ),
        Expr::Lazy(inner, _) => consume_of(env, target, v, inner),
        _ => LinResult::zero(),
    }
}

/// `consume-read`: **READING A FIELD IS NOT A HAND-OFF.** `p.left` mentions
/// `p` and consumes nothing; only a compound receiver is walked further.
fn consume_read(env: &LinEnv, target: Sym, v: Sym, obj: &Expr) -> LinResult {
    match obj {
        Expr::NameRef(..) => LinResult::zero(),
        other => consume_of(env, target, v, other),
    }
}

fn consume_spine(env: &LinEnv, target: Sym, v: Sym, threads: bool, e: &Expr) -> LinResult {
    match e {
        Expr::Apply(f, a, _) => seq(
            consume_spine(env, target, v, threads, f),
            consume_arg(env, target, v, threads, a),
        ),
        other => consume_of(env, target, v, other),
    }
}

/// `consume-arg`: the bare name costs one ONLY where the call threads it back
/// out. A call that swallows the record is the last owner, and there is nothing
/// left to alias.
fn consume_arg(env: &LinEnv, target: Sym, v: Sym, threads: bool, a: &Expr) -> LinResult {
    match a {
        Expr::NameRef(n, _) => {
            if *n == v && threads { LinResult::one() } else { LinResult::zero() }
        }
        other => consume_of(env, target, v, other),
    }
}

fn consume_let(
    env: &LinEnv,
    target: Sym,
    v: Sym,
    binds: &[crate::ast::LetBind],
    body: &Expr,
    i: usize,
) -> LinResult {
    let Some(b) = binds.get(i) else { return consume_of(env, target, v, body) };
    if matches!(&b.value, Expr::NameRef(n, _) if *n == v) {
        return consume_let_moved(env, target, v, b.name, binds, body, i + 1);
    }
    let here = consume_of(env, target, v, &b.value);
    if b.name == v {
        return here;
    }
    seq(here, consume_let(env, target, v, binds, body, i + 1))
}

/// `consume-let-moved`: `let m2 = m` renames the record. The new name carries
/// the rule from here on, and every later mention of the OLD one is dead --
/// which is the whole of `mutable-launder-alias`.
fn consume_let_moved(
    env: &LinEnv,
    target: Sym,
    v: Sym,
    h: Sym,
    binds: &[crate::ast::LetBind],
    body: &Expr,
    i: usize,
) -> LinResult {
    if h == v {
        return consume_let(env, target, v, binds, body, i);
    }
    move_join(
        consume_let(env, target, h, binds, body, i),
        lin_let(env, v, false, binds, body, i),
    )
}

fn consume_stmts(env: &LinEnv, target: Sym, v: Sym, stmts: &[ActStmt], i: usize) -> LinResult {
    let Some(s) = stmts.get(i) else { return LinResult::zero() };
    match s {
        ActStmt::Exec(e, _) => seq(
            consume_of(env, target, v, e),
            consume_stmts(env, target, v, stmts, i + 1),
        ),
        ActStmt::Bind(n, e, _) => {
            if *n == v {
                consume_of(env, target, v, e)
            } else {
                seq(
                    consume_of(env, target, v, e),
                    consume_stmts(env, target, v, stmts, i + 1),
                )
            }
        }
    }
}

fn consume_arms(env: &LinEnv, target: Sym, v: Sym, arms: &[MatchArm], i: usize) -> LinResult {
    let Some(arm) = arms.get(i) else { return LinResult::zero() };
    let this = if pat_binds(&arm.pattern, v) {
        LinResult::zero()
    } else {
        seq(
            consume_of(env, target, v, &arm.guard),
            consume_of(env, target, v, &arm.body),
        )
    };
    if i + 1 >= arms.len() {
        this
    } else {
        path_max(this, consume_arms(env, target, v, arms, i + 1))
    }
}

fn consume_clauses(
    env: &LinEnv,
    target: Sym,
    v: Sym,
    clauses: &[crate::ast::HandleClause],
) -> LinResult {
    clauses.iter().fold(LinResult::zero(), |acc, cl| {
        let here = if cl.params.contains(&v) || cl.resume_name == v {
            LinResult::zero()
        } else {
            consume_of(env, target, v, &cl.body)
        };
        seq(acc, here)
    })
}

/// `mutable-name-of` + `return-mutable-name-after`: applying `k` arguments to
/// this type yields a mutable record -- which one?
fn return_mutable_name_after(env: &LinEnv, t: &Ty, k: usize) -> Option<Sym> {
    match t {
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => return_mutable_name_after(env, b, k),
        Ty::Fun(_, _, r) => {
            if k == 0 { None } else { return_mutable_name_after(env, r, k - 1) }
        }
        Ty::Effectful(_, _, ret) => {
            if k == 0 { return_mutable_name_after(env, ret, 0) } else { None }
        }
        Ty::Record(n, _) | Ty::Constructed(n, _) => {
            if k == 0 && env.mutables.contains(n) { Some(*n) } else { None }
        }
        _ => None,
    }
}

/// `expr-mut-mint-name`: this expression BUILDS a mutable record, so the name
/// it is bound to carries the rule even though no parameter declared it.
fn expr_mut_mint_name(env: &LinEnv, e: &Expr) -> Option<Sym> {
    match e {
        Expr::Apply(..) => {
            let t = env.bindings.get(&head_name(e)?)?;
            return_mutable_name_after(env, t, arg_count(e))
        }
        Expr::NameRef(n, _) => return_mutable_name_after(env, env.bindings.get(n)?, 0),
        _ => None,
    }
}

/// `report-minted-mutable` (subject 51323).
fn report_minted_mutable(def: &Def, env: &LinEnv, v: Sym, r: &LinResult, st: &mut UnifyState) {
    let name = env.syms.text(v);
    let owner = env.syms.text(def.name);
    let minted = "minted by a call";
    if r.dead > 0 {
        st.error(Cdx::MUTABLE_ALIAS, format!(
            "In '{owner}', mutable record '{name}', {minted}, was moved to a new owner by a let binding and then mentioned again; after a move the original name is dead"));
    } else if r.count > 1 {
        st.error(Cdx::MUTABLE_ALIAS, format!(
            "In '{owner}', mutable record '{name}', {minted}, is consumed {} times on a single path; a mutable record may be handed to a new owner at most once",
            r.count));
    }
}

/// `check-one-mutable-param` (subject 51115). Two questions, not six: the
/// mutable rule is about ALIASING, so it has nothing to say about escape,
/// capture or return.
fn check_one_mutable_param(
    def: &Def,
    env: &LinEnv,
    tn: Sym,
    p: &crate::ast::Param,
    st: &mut UnifyState,
) {
    let r = consume_of(env, tn, p.name, &def.body);
    let name = env.syms.text(p.name);
    let owner = env.syms.text(def.name);
    if r.dead > 0 {
        st.error(Cdx::MUTABLE_ALIAS, format!(
            "In '{owner}', mutable record '{name}' was moved to a new owner by a let binding and then mentioned again; after a move the original name is dead"));
    } else if r.count > 1 {
        st.error(Cdx::MUTABLE_ALIAS, format!(
            "In '{owner}', mutable record '{name}' is consumed {} times on a single path; a mutable record may be handed to a new owner at most once",
            r.count));
    }
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
    check_mints(def, env, &TupEnv::new(), true, &def.body, st);
}

fn check_one_param(def: &Def, env: &LinEnv, pty: &TypeExpr, p: &crate::ast::Param, st: &mut UnifyState) {
    // The mutable rule is asked FIRST, and a mutable parameter never reaches
    // the linear one: the two disciplines are disjoint, and upstream's order is
    // what decides that for a type that somehow declared both.
    if let Some(tn) = core_name(pty) {
        if env.mutables.contains(&tn) {
            return check_one_mutable_param(def, env, tn, p, st);
        }
    }
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

    /// A chapter with a mutable record, a call that hands it on (`thread`) and
    /// one that does not (`peek`).
    fn mutable(body: &str) -> Vec<u16> {
        codes(&format!(
            "  mutable Cell = record {{\n    n : Integer\n  }}\n\n  thread : Cell -> Cell\n  thread (c) = c\n\n  peek : Cell -> Integer\n  peek (c) = c.n\n\n{body}"
        ))
    }

    /// **READING IS NOT OWNING.** The mutable rule counts hand-offs, so a
    /// record read twice is clean where a linear value read twice is not --
    /// the two disciplines disagree here on purpose.
    #[test]
    fn reading_a_mutable_record_twice_is_clean() {
        assert_eq!(mutable("  f : Cell -> Integer\n  f (c) = c.n + c.n\n"), vec![]);
        assert_eq!(mutable("  f : Cell -> Integer\n  f (c) = peek c + peek c\n"), vec![]);
    }

    /// **ONLY A CALL THAT GIVES IT BACK IS A HAND-OFF.** `peek` swallows the
    /// record and is the last owner; `thread` returns it, so calling `thread`
    /// twice makes two owners of one record.
    #[test]
    fn handing_a_mutable_record_on_twice_is_an_alias() {
        assert_eq!(mutable("  f : Cell -> Integer\n  f (c) = (thread c).n\n"), vec![]);
        assert_eq!(
            mutable("  f : Cell -> Integer\n  f (c) = (thread c).n + (thread c).n\n"),
            vec![crate::check::Cdx::MUTABLE_ALIAS]
        );
    }

    /// A tuple carrying a linear component, and the pattern that takes it
    /// apart. `Tup2` has to be declared here because the discipline is keyed on
    /// the NAME matching the arity.
    fn tupled(body: &str) -> Vec<u16> {
        codes(&format!(
            "  Tup2 (a) (b) =\n    | MkTup2 (a) (b)\n\n  acquire2 : Integer -> (linear Integer, Integer)\n  acquire2 (n) = MkTup2 n n\n\n  release : linear Integer -> Integer\n  release (g) = g + 0\n\n{body}"
        ))
    }

    /// **THE COMPONENT INSIDE THE TUPLE CARRIES THE DISCIPLINE, NOT THE TUPLE.**
    /// Destructuring is where it lands, and the plain component beside it is an
    /// ordinary binding.
    #[test]
    fn a_linear_component_of_a_tuple_must_still_be_used_once() {
        assert_eq!(
            tupled("  f : Integer -> Integer\n  f (n) = let (g, k) = acquire2 n in release g + k\n"),
            vec![]
        );
        assert_eq!(
            tupled("  f : Integer -> Integer\n  f (n) = let (g, k) = acquire2 n in k\n"),
            vec![crate::check::Cdx::LINEAR_UNUSED]
        );
        assert_eq!(
            tupled("  f : Integer -> Integer\n  f (n) = let (g, k) = acquire2 n in release g + release g + k\n"),
            vec![crate::check::Cdx::USE_AFTER_CONSUME]
        );
    }

    /// A wildcard is not a way out: it is reported against the POSITION, since
    /// there is no name to report against.
    #[test]
    fn a_wildcard_cannot_discard_a_linear_component() {
        assert_eq!(
            tupled("  f : Integer -> Integer\n  f (n) = let (_, k) = acquire2 n in k\n"),
            vec![crate::check::Cdx::LINEAR_UNUSED]
        );
    }

    /// **THE TUPLE TYPE SURVIVES A REBINDING.** `let p = ... in let (g, k) = p`
    /// destructures a NAME, so the walk has to remember what that name holds --
    /// and the name itself is an owner while it holds it.
    #[test]
    fn a_tuple_bound_to_a_name_keeps_its_discipline() {
        assert_eq!(
            tupled("  f : Integer -> Integer\n  f (n) = let p = acquire2 n in let (g, k) = p in release g + k\n"),
            vec![]
        );
        assert_eq!(
            tupled("  f : Integer -> Integer\n  f (n) = let p = acquire2 n in let (g, k) = p in k\n"),
            vec![crate::check::Cdx::LINEAR_UNUSED]
        );
        // Never taken apart at all: the pair itself is the dropped owner.
        assert_eq!(
            tupled("  f : Integer -> Integer\n  f (n) = let p = acquire2 n in 7\n"),
            vec![crate::check::Cdx::LINEAR_UNUSED]
        );
    }

    /// **RENAMING IT DOES NOT LAUNDER IT.** `let d = c` moves the record to a
    /// new owner, and the old name is dead from there on -- reported as the
    /// MOVE, not as a count, because that is the reason the count is wrong.
    #[test]
    fn a_let_alias_moves_the_record_and_kills_the_old_name() {
        assert_eq!(
            mutable("  f : Cell -> Integer\n  f (c) = let d = c in (thread d).n + (thread c).n\n"),
            vec![crate::check::Cdx::MUTABLE_ALIAS]
        );
        // The old name is not mentioned again: one owner, and clean.
        assert_eq!(
            mutable("  f : Cell -> Integer\n  f (c) = let d = c in (thread d).n\n"),
            vec![]
        );
    }
}
