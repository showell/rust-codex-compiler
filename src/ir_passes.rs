//! The IR pipeline -- the rewriting passes in `IR/Lowering.codex`, and the
//! prune the driver runs at emit time.
//!
//! **THE GOLDS ARE POST-PIPELINE**, which is the whole reason this file
//! exists. `CDX4030 PIPELINE` names three passes on every compile:
//!
//! ```text
//!   fold-constants, inline-leaf-calls, inline-single-caller
//! ```
//!
//! and then `ir-prune-unreachable-roots` drops what nothing references any
//! more. Those two facts compose into the effect that is visible in every
//! gold: a small function is substituted into its callers and then DISAPPEARS.
//! `sb-length`, `signal-delivered-count`, `fused-lt` are in no gold at all,
//! and an emitter that types them perfectly still emits a different document.

use crate::check::{Overflow, Ty};
use crate::ir_chapter::{IrActStmt, IrBinOp, IrDef, IrExpr, IrPat};
use crate::lowering_types as lt;
use crate::symbol::{Sym, SymTab};
use std::collections::{BTreeMap, BTreeSet};

/// The three passes, in the driver's order.
///
/// **THE ORDER IS NOT COSMETIC.** `fold-constants` turns `negate (int-lit 2)`
/// into `(int-lit -2)`, and only THEN is that argument simple enough for the
/// leaf pass to substitute -- `negation-abutment` keeps `one` and `three` if
/// the fold has not run, because their call sites are written `one -5` and
/// `three 1 -2 3`.
pub fn pipeline(defs: Vec<IrDef>, syms: &SymTab) -> Vec<IrDef> {
    let defs = fold_constants(defs, syms);
    let defs = inline_leaf_calls(defs, syms);
    inline_single_caller(defs, syms)
}

// ---------------------------------------------------------------------------
// Constant folding
// ---------------------------------------------------------------------------

/// `fold-constants-in-chapter`. Four rewrites and no more: a negated integer
/// literal, and three builtins over literal arguments.
///
/// **A NAME THE CHAPTER DEFINES IS NEVER FOLDED.** `text-length` and
/// `char-code` are builtins until a program declares its own, and folding a
/// call to a definition that merely shares the name would compute the wrong
/// answer at compile time -- which is why `defined` is collected first.
pub fn fold_constants(defs: Vec<IrDef>, syms: &SymTab) -> Vec<IrDef> {
    let defined: BTreeSet<Sym> = defs.iter().map(|d| d.name).collect();
    defs.into_iter()
        .map(|d| IrDef { body: fold_expr(&d.body, &defined, syms), ..d })
        .collect()
}

fn fold_expr(e: &IrExpr, defined: &BTreeSet<Sym>, syms: &SymTab) -> IrExpr {
    use IrExpr as E;
    let go = |x: &IrExpr| Box::new(fold_expr(x, defined, syms));
    match e {
        // `-5` is one node on the wire, not a negate around a literal.
        // `-9223372036854775808` lexes to `i64::MIN` by wrapping accumulation
        // and negating that wraps back to itself, as upstream's does.
        E::Negate(x, t, s) => match fold_expr(x, defined, syms) {
            E::IntLit(v, _) => E::IntLit(v.wrapping_neg(), *s),
            fx => E::Negate(Box::new(fx), t.clone(), *s),
        },
        E::Apply(f, a, t, s) => {
            let f = fold_expr(f, defined, syms);
            let a = fold_expr(a, defined, syms);
            fold_apply(f, a, t, *s, defined, syms)
        }
        E::Binary(op, l, r, t, s) => E::Binary(*op, go(l), go(r), t.clone(), *s),
        E::If(c, th, el, t, s) => E::If(go(c), go(th), go(el), t.clone(), *s),
        E::Let(n, t, v, b, s) => E::Let(*n, t.clone(), go(v), go(b), *s),
        E::Lambda(ps, b, t, s) => E::Lambda(ps.clone(), go(b), t.clone(), *s),
        E::FieldAccess(r, f, t, s) => E::FieldAccess(go(r), f.clone(), t.clone(), *s),
        E::FieldStore(r, f, v, t, s) => E::FieldStore(go(r), f.clone(), go(v), t.clone(), *s),
        E::List(xs, t, s) => {
            E::List(xs.iter().map(|x| fold_expr(x, defined, syms)).collect(), t.clone(), *s)
        }
        E::Record(n, fs, t, s) => E::Record(
            *n,
            fs.iter()
                .map(|f| crate::ir_chapter::IrFieldVal {
                    name: f.name,
                    value: fold_expr(&f.value, defined, syms),
                })
                .collect(),
            t.clone(),
            *s,
        ),
        E::WithTimeout(secs, effs, sc, b, t, s) => {
            E::WithTimeout(*secs, effs.clone(), sc.clone(), go(b), t.clone(), *s)
        }
        E::Try(max, b, fb, fl, t, s) => {
            let f = |ss: &Vec<IrActStmt>| -> Vec<IrActStmt> {
                ss.iter()
                    .map(|st| match st {
                        IrActStmt::Exec(v, sp) => {
                            IrActStmt::Exec(fold_expr(v, defined, syms), *sp)
                        }
                        IrActStmt::Bind(n, bt, v, sp) => {
                            IrActStmt::Bind(*n, bt.clone(), fold_expr(v, defined, syms), *sp)
                        }
                    })
                    .collect()
            };
            E::Try(*max, f(b), f(fb), f(fl), t.clone(), *s)
        }
        E::Handle(eff, b, cs, t, s) => E::Handle(
            eff.clone(),
            go(b),
            cs.iter()
                .map(|c| crate::ir_chapter::IrHandleClause {
                    body: fold_expr(&c.body, defined, syms),
                    ..c.clone()
                })
                .collect(),
            t.clone(),
            *s,
        ),
        E::Match(sc, bs, t, s) => E::Match(
            go(sc),
            bs.iter()
                .map(|b| crate::ir_chapter::IrBranch {
                    pattern: b.pattern.clone(),
                    body: fold_expr(&b.body, defined, syms),
                    guard: fold_expr(&b.guard, defined, syms),
                    span: b.span,
                })
                .collect(),
            t.clone(),
            *s,
        ),
        E::Act(ss, t, s) => E::Act(
            ss.iter()
                .map(|st| match st {
                    IrActStmt::Exec(v, sp) => IrActStmt::Exec(fold_expr(v, defined, syms), *sp),
                    IrActStmt::Bind(n, bt, v, sp) => {
                        IrActStmt::Bind(*n, bt.clone(), fold_expr(v, defined, syms), *sp)
                    }
                })
                .collect(),
            t.clone(),
            *s,
        ),
        other => other.clone(),
    }
}

fn fold_apply(
    f: IrExpr,
    a: IrExpr,
    t: &Ty,
    s: crate::ast::Span,
    defined: &BTreeSet<Sym>,
    syms: &SymTab,
) -> IrExpr {
    let unfolded = |f: IrExpr, a: IrExpr| IrExpr::Apply(Box::new(f), Box::new(a), t.clone(), s);
    match &f {
        IrExpr::Name(n, _, _) if !defined.contains(n) => match (syms.text(*n), &a) {
            // One unit per CHARACTER, not per byte -- a Codex `Text` is CCE
            // units. The literal is decoded already, so this is a count.
            ("text-length", IrExpr::TextLit(v, _)) => {
                IrExpr::IntLit(v.chars().count() as i64, s)
            }
            // A char literal already IS its char-code by the time it is here.
            ("char-code", IrExpr::CharLit(v, _)) => IrExpr::IntLit(*v, s),
            _ => unfolded(f, a),
        },
        // `char-code-at` is saturated by two arguments, so the fold sits on
        // the OUTER apply and reads the inner one's argument.
        IrExpr::Apply(inner_f, str_arg, _, _) => match (&**inner_f, &**str_arg, &a) {
            (IrExpr::Name(n, _, _), IrExpr::TextLit(v, _), IrExpr::IntLit(i, _))
                if syms.text(*n) == "char-code-at" && !defined.contains(n) =>
            {
                match usize::try_from(*i).ok().and_then(|i| v.chars().nth(i)) {
                    Some(c) => IrExpr::IntLit(crate::charcode::char_code(c), s),
                    None => unfolded(f, a),
                }
            }
            _ => unfolded(f, a),
        },
        _ => unfolded(f, a),
    }
}

/// A definition a call site may be replaced by: its parameters, their declared
/// types, and its body. `InlineLeaf` upstream, and both passes use it.
struct Candidate {
    name: Sym,
    params: Vec<Sym>,
    ptys: Vec<Ty>,
    /// The declared type AFTER the parameters: what the call site receives.
    rty: Ty,
    body: IrExpr,
}

/// A candidate's declared return type. Lowering has already refused any
/// definition with more parameters than its type has arrows.
fn declared_return(d: &IrDef) -> Ty {
    lt::peel_returns_n(&d.ty, d.params.len())
        .cloned()
        .expect("lowering refuses a definition with more params than arrows")
}

/// **A BOUNDED SIGNATURE IS NEVER INLINED.** A function with a bounded
/// parameter or return is enforced by runtime guards at its entry and
/// epilogue; splicing its body into the caller would bypass them.
fn has_bounded_boundary(d: &IrDef) -> bool {
    let bounded = |t: &Ty| {
        matches!(t, Ty::Integer(lo, hi, Overflow::Error)
            if *lo != i64::MIN || *hi != i64::MAX)
    };
    if d.params.iter().any(|p| bounded(&p.ty)) {
        return true;
    }
    let mut ret = d.ty.clone();
    for _ in 0..d.params.len() {
        ret = match ret {
            Ty::Fun(_, _, r) | Ty::ForAll(_, r) | Ty::ForAllEff(_, r) => *r,
            other => return bounded(&other),
        };
    }
    bounded(&ret)
}

/// The name at the head of an application spine, and the arguments under it.
fn apply_root(e: &IrExpr) -> Option<Sym> {
    match e {
        IrExpr::Apply(f, _, _, _) => apply_root(f),
        IrExpr::Name(n, _, _) => Some(*n),
        _ => None,
    }
}

fn apply_args(e: &IrExpr) -> Vec<&IrExpr> {
    match e {
        IrExpr::Apply(f, a, _, _) => {
            let mut v = apply_args(f);
            v.push(a);
            v
        }
        _ => Vec::new(),
    }
}

/// **AN ARGUMENT MUST BE A NAME OR AN INTEGER LITERAL.** Substitution copies
/// the argument once per occurrence of the parameter, so anything with a cost
/// or an effect would be duplicated or reordered.
fn args_simple(args: &[&IrExpr]) -> bool {
    args.iter().all(|a| matches!(a, IrExpr::Name(..) | IrExpr::IntLit(..)))
}

/// Whether this body calls any candidate -- the guard that decides whether a
/// definition is rewritten at all.
fn has_call(e: &IrExpr, cands: &[Candidate]) -> bool {
    if let IrExpr::Apply(..) = e {
        if apply_root(e).is_some_and(|r| cands.iter().any(|c| c.name == r)) {
            return true;
        }
    }
    e.children().iter().any(|c| has_call(c, cands))
}

/// Every name a pattern binds, appended -- `push-pat-names`.
fn push_pat_names(bound: &mut Vec<Sym>, p: &IrPat) {
    crate::lambda_lifting::pat_names(p, bound);
}

// ---------------------------------------------------------------------------
// Leaf inlining
// ---------------------------------------------------------------------------

/// `leaf-body-ok`: integer literals, this function's own parameters, and
/// integer arithmetic over them -- twelve nodes of fuel and nothing else.
///
/// It is deliberately far narrower than the single-caller pass below, because
/// this one duplicates the body at EVERY call site.
fn leaf_body_ok(e: &IrExpr, params: &[Sym], fuel: i32) -> i32 {
    if fuel <= 0 {
        return -1;
    }
    match e {
        IrExpr::IntLit(..) => fuel - 1,
        IrExpr::Name(n, _, _) => {
            if params.contains(n) {
                fuel - 1
            } else {
                -1
            }
        }
        IrExpr::Binary(op, l, r, _, _) => {
            if !matches!(
                op,
                IrBinOp::AddInt | IrBinOp::SubInt | IrBinOp::MulInt | IrBinOp::DivInt
            ) {
                return -1;
            }
            let lf = leaf_body_ok(l, params, fuel - 1);
            if lf < 0 {
                -1
            } else {
                leaf_body_ok(r, params, lf)
            }
        }
        _ => -1,
    }
}

fn collect_leaf_defs(defs: &[IrDef], syms: &SymTab) -> Vec<Candidate> {
    defs.iter()
        .filter(|d| syms.text(d.name) != "deck-record" && !has_bounded_boundary(d))
        .filter(|d| (1..=3).contains(&d.params.len()))
        .filter(|d| {
            let ps: Vec<Sym> = d.params.iter().map(|p| p.name).collect();
            leaf_body_ok(&d.body, &ps, 12) >= 0
        })
        .map(|d| Candidate {
            name: d.name,
            params: d.params.iter().map(|p| p.name).collect(),
            ptys: d.params.iter().map(|p| p.ty.clone()).collect(),
            rty: declared_return(d),
            body: d.body.clone(),
        })
        .collect()
}

/// `subst-leaf`: names and integer arithmetic, which is the whole vocabulary
/// `leaf_body_ok` admits.
fn subst_leaf(e: &IrExpr, params: &[Sym], args: &[&IrExpr]) -> IrExpr {
    match e {
        IrExpr::Name(n, _, _) => match params.iter().position(|p| p == n) {
            Some(i) => args[i].clone(),
            None => e.clone(),
        },
        IrExpr::Binary(op, l, r, t, s) => IrExpr::Binary(
            *op,
            Box::new(subst_leaf(l, params, args)),
            Box::new(subst_leaf(r, params, args)),
            t.clone(),
            *s,
        ),
        other => other.clone(),
    }
}

pub fn inline_leaf_calls(defs: Vec<IrDef>, syms: &SymTab) -> Vec<IrDef> {
    let cands = collect_leaf_defs(&defs, syms);
    if cands.is_empty() {
        return defs;
    }
    defs.into_iter()
        .map(|d| {
            if !has_call(&d.body, &cands) {
                return d;
            }
            let mut bound: Vec<Sym> = d.params.iter().map(|p| p.name).collect();
            let body = rewrite(&d.body, &cands, &mut bound, &leaf_site);
            IrDef { body, ..d }
        })
        .collect()
}

/// `inline-apply-site`. A root that is LOCALLY BOUND is a value, not this
/// definition, and is left alone.
fn leaf_site(e: &IrExpr, cands: &[Candidate], bound: &[Sym]) -> IrExpr {
    let Some(root) = apply_root(e) else { return e.clone() };
    if bound.contains(&root) {
        return e.clone();
    }
    let Some(c) = cands.iter().find(|c| c.name == root) else { return e.clone() };
    let args = apply_args(e);
    if args.len() != c.params.len() || !args_simple(&args) {
        return e.clone();
    }
    subst_leaf(&c.body, &c.params, &args)
}

// ---------------------------------------------------------------------------
// Single-caller inlining
// ---------------------------------------------------------------------------

/// `once-binder-free` is an ALLOW-LIST: literals, names, arithmetic, `if`,
/// application, lists, records and field access. Every other constructor --
/// let, lambda, match, act, and anything added later -- is refused, because
/// substituting a body that BINDS a name into a caller that binds the same
/// name captures it.
///
/// **THIS LIST AND `subst_once` BELOW ARE WRITTEN TO BE READ SIDE BY SIDE.**
/// Widening one without the other is how this pass would silently leave a
/// parameter name loose in the caller.
fn once_binder_free(e: &IrExpr) -> bool {
    use IrExpr as E;
    match e {
        E::IntLit(..)
        | E::NumLit(..)
        | E::TextLit(..)
        | E::BoolLit(..)
        | E::CharLit(..)
        | E::Name(..) => true,
        E::Negate(x, _, _) | E::FieldAccess(x, _, _, _) => once_binder_free(x),
        E::Binary(_, l, r, _, _) | E::FieldStore(l, _, r, _, _) => {
            once_binder_free(l) && once_binder_free(r)
        }
        E::Apply(f, a, _, _) => once_binder_free(f) && once_binder_free(a),
        E::If(c, t, el, _, _) => {
            once_binder_free(c) && once_binder_free(t) && once_binder_free(el)
        }
        E::List(xs, _, _) => xs.iter().all(once_binder_free),
        E::Record(_, fs, _, _) => fs.iter().all(|f| once_binder_free(&f.value)),
        _ => false,
    }
}

/// `once-free-escapes`: a name in the body that is neither a parameter nor a
/// global, but happens to be bound AT THE CALL SITE. Substituting there would
/// capture it, so the site is declined.
fn once_free_escapes(e: &IrExpr, params: &[Sym], bound: &[Sym]) -> bool {
    match e {
        IrExpr::Name(n, _, _) => !params.contains(n) && bound.contains(n),
        other => other.children().iter().any(|c| once_free_escapes(c, params, bound)),
    }
}

fn collect_once_defs(defs: &[IrDef], syms: &SymTab) -> Vec<Candidate> {
    defs.iter()
        .filter(|d| syms.text(d.name) != "deck-record" && !has_bounded_boundary(d))
        .filter(|d| (1..=4).contains(&d.params.len()))
        .filter(|d| once_binder_free(&d.body))
        .map(|d| Candidate {
            name: d.name,
            params: d.params.iter().map(|p| p.name).collect(),
            ptys: d.params.iter().map(|p| p.ty.clone()).collect(),
            rty: declared_return(d),
            body: d.body.clone(),
        })
        .collect()
}

/// `once-retype`: the candidate's declared parameter types matched against
/// the argument types, AND ITS DECLARED RETURN TYPE AGAINST THE CALL SITE'S
/// TYPE, and whatever that teaches substituted into each node's type. A
/// polymorphic helper inlined at a concrete call site would otherwise carry
/// its own type variables into the caller.
///
/// The return pair is what reaches a variable that appears in no parameter --
/// `make-empty : Integer -> List a` is generic where it is defined, and only
/// the site (already resolved by the checker, orphans defaulted) says what `a`
/// is here. Parameters alone would carry `a` into the caller as a hole.
fn once_retype(ty: &Ty, ptys: &[Ty], atys: &[Ty]) -> Ty {
    ptys.iter().zip(atys.iter()).fold(ty.clone(), |t, (p, a)| lt::subst_from_arg(p, a, &t))
}

/// Substitution over exactly the vocabulary `once_binder_free` admits.
fn subst_once(
    e: &IrExpr,
    params: &[Sym],
    args: &[&IrExpr],
    ptys: &[Ty],
    atys: &[Ty],
) -> IrExpr {
    use IrExpr as E;
    let rt = |t: &Ty| once_retype(t, ptys, atys);
    let go = |x: &IrExpr| Box::new(subst_once(x, params, args, ptys, atys));
    match e {
        E::Name(n, t, s) => match params.iter().position(|p| p == n) {
            Some(i) => args[i].clone(),
            None if ptys.is_empty() => e.clone(),
            None => E::Name(*n, rt(t), *s),
        },
        E::Negate(x, t, s) => E::Negate(go(x), rt(t), *s),
        E::Binary(op, l, r, t, s) => E::Binary(*op, go(l), go(r), rt(t), *s),
        E::If(c, th, el, t, s) => E::If(go(c), go(th), go(el), rt(t), *s),
        E::Apply(f, a, t, s) => E::Apply(go(f), go(a), rt(t), *s),
        E::FieldAccess(r, f, t, s) => E::FieldAccess(go(r), f.clone(), rt(t), *s),
        E::FieldStore(r, f, v, t, s) => E::FieldStore(go(r), f.clone(), go(v), rt(t), *s),
        E::List(xs, t, s) => E::List(
            xs.iter().map(|x| subst_once(x, params, args, ptys, atys)).collect(),
            rt(t),
            *s,
        ),
        E::Record(n, fs, t, s) => E::Record(
            *n,
            fs.iter()
                .map(|f| crate::ir_chapter::IrFieldVal {
                    name: f.name,
                    value: subst_once(&f.value, params, args, ptys, atys),
                })
                .collect(),
            rt(t),
            *s,
        ),
        other => other.clone(),
    }
}

/// The reference census. **THIS WALK MUST REACH EVERY CONSTRUCTOR THAT CAN
/// HOLD A SUB-EXPRESSION**: a reference it misses makes a two-caller
/// definition look like a one-caller definition, and undercounting is the one
/// direction that is not conservative.
fn count_refs(defs: &[IrDef], cands: &[Candidate]) -> Vec<usize> {
    let mut counts = vec![0usize; cands.len()];
    for d in defs {
        d.body.walk(&mut |x| {
            if let IrExpr::Name(n, _, _) = x {
                if let Some(i) = cands.iter().position(|c| c.name == *n) {
                    counts[i] += 1;
                }
            }
        });
    }
    counts
}

pub fn inline_single_caller(defs: Vec<IrDef>, syms: &SymTab) -> Vec<IrDef> {
    let local = collect_once_defs(&defs, syms);
    if local.is_empty() {
        return defs;
    }
    let counts = count_refs(&defs, &local);
    let cands: Vec<Candidate> = local
        .into_iter()
        .zip(counts)
        .filter(|(_, n)| *n == 1)
        .map(|(c, _)| c)
        .collect();
    if cands.is_empty() {
        return defs;
    }
    defs.into_iter()
        .map(|d| {
            if !has_call(&d.body, &cands) {
                return d;
            }
            let mut bound: Vec<Sym> = d.params.iter().map(|p| p.name).collect();
            let body = rewrite(&d.body, &cands, &mut bound, &once_site);
            IrDef { body, ..d }
        })
        .collect()
}

/// `once-apply-site`.
fn once_site(e: &IrExpr, cands: &[Candidate], bound: &[Sym]) -> IrExpr {
    let Some(root) = apply_root(e) else { return e.clone() };
    if bound.contains(&root) {
        return e.clone();
    }
    let Some(c) = cands.iter().find(|c| c.name == root) else { return e.clone() };
    let args = apply_args(e);
    if args.len() != c.params.len() || !args_simple(&args) {
        return e.clone();
    }
    if once_free_escapes(&c.body, &c.params, bound) {
        return e.clone();
    }
    // The types are threaded only where the signature is polymorphic; a
    // monomorphic candidate's body already says what it means.
    if c.ptys.iter().chain(std::iter::once(&c.rty)).any(lt::has_typevars) {
        let mut ptys = c.ptys.clone();
        ptys.push(c.rty.clone());
        let mut atys: Vec<Ty> = args.iter().map(|a| a.ty()).collect();
        atys.push(e.ty());
        subst_once(&c.body, &c.params, &args, &ptys, &atys)
    } else {
        subst_once(&c.body, &c.params, &args, &[], &[])
    }
}

// ---------------------------------------------------------------------------

/// `inline-expr` and `once-expr` are the same walk with a different site rule,
/// so they are one function here.
///
/// **THE SITE RULE FIRES ON THE WAY OUT.** An application is rewritten after
/// its own function and argument have been, so a call whose argument is itself
/// an inlinable call is handled inner-first.
fn rewrite(
    e: &IrExpr,
    cands: &[Candidate],
    bound: &mut Vec<Sym>,
    site: &dyn Fn(&IrExpr, &[Candidate], &[Sym]) -> IrExpr,
) -> IrExpr {
    use IrExpr as E;
    match e {
        E::Apply(f, a, t, s) => {
            let f = rewrite(f, cands, bound, site);
            let a = rewrite(a, cands, bound, site);
            site(&E::Apply(Box::new(f), Box::new(a), t.clone(), *s), cands, bound)
        }
        E::Binary(op, l, r, t, s) => E::Binary(
            *op,
            Box::new(rewrite(l, cands, bound, site)),
            Box::new(rewrite(r, cands, bound, site)),
            t.clone(),
            *s,
        ),
        E::If(c, th, el, t, s) => E::If(
            Box::new(rewrite(c, cands, bound, site)),
            Box::new(rewrite(th, cands, bound, site)),
            Box::new(rewrite(el, cands, bound, site)),
            t.clone(),
            *s,
        ),
        E::Let(n, t, v, b, s) => {
            let v = rewrite(v, cands, bound, site);
            bound.push(*n);
            let b = rewrite(b, cands, bound, site);
            bound.pop();
            E::Let(*n, t.clone(), Box::new(v), Box::new(b), *s)
        }
        E::Lambda(ps, b, t, s) => {
            let mark = bound.len();
            bound.extend(ps.iter().map(|p| p.name));
            let b = rewrite(b, cands, bound, site);
            bound.truncate(mark);
            E::Lambda(ps.clone(), Box::new(b), t.clone(), *s)
        }
        E::Negate(x, t, s) => E::Negate(Box::new(rewrite(x, cands, bound, site)), t.clone(), *s),
        E::WithTimeout(secs, effs, sc, b, t, s) => E::WithTimeout(
            *secs,
            effs.clone(),
            sc.clone(),
            Box::new(rewrite(b, cands, bound, site)),
            t.clone(),
            *s,
        ),
        E::Try(max, b, fb, fl, t, s) => {
            let mut f = |ss: &Vec<IrActStmt>| -> Vec<IrActStmt> {
                let mark = bound.len();
                let out: Vec<_> = ss
                    .iter()
                    .map(|st| match st {
                        IrActStmt::Exec(v, sp) => {
                            IrActStmt::Exec(rewrite(v, cands, bound, site), *sp)
                        }
                        IrActStmt::Bind(n, bt, v, sp) => {
                            let v = rewrite(v, cands, bound, site);
                            bound.push(*n);
                            IrActStmt::Bind(*n, bt.clone(), v, *sp)
                        }
                    })
                    .collect();
                bound.truncate(mark);
                out
            };
            E::Try(*max, f(b), f(fb), f(fl), t.clone(), *s)
        }
        E::Handle(eff, b, cs, t, s) => E::Handle(
            eff.clone(),
            Box::new(rewrite(b, cands, bound, site)),
            cs.iter()
                .map(|c| {
                    let mark = bound.len();
                    bound.extend(c.params.iter().copied());
                    bound.push(c.resume_name);
                    let body = rewrite(&c.body, cands, bound, site);
                    bound.truncate(mark);
                    crate::ir_chapter::IrHandleClause { body, ..c.clone() }
                })
                .collect(),
            t.clone(),
            *s,
        ),
        E::Match(sc, bs, t, s) => E::Match(
            Box::new(rewrite(sc, cands, bound, site)),
            bs.iter()
                .map(|b| {
                    let mark = bound.len();
                    push_pat_names(bound, &b.pattern);
                    let body = rewrite(&b.body, cands, bound, site);
                    let guard = rewrite(&b.guard, cands, bound, site);
                    bound.truncate(mark);
                    crate::ir_chapter::IrBranch {
                        pattern: b.pattern.clone(),
                        body,
                        guard,
                        span: b.span,
                    }
                })
                .collect(),
            t.clone(),
            *s,
        ),
        E::Act(ss, t, s) => {
            let mark = bound.len();
            let ss = ss
                .iter()
                .map(|st| match st {
                    IrActStmt::Exec(v, sp) => {
                        IrActStmt::Exec(rewrite(v, cands, bound, site), *sp)
                    }
                    IrActStmt::Bind(n, bt, v, sp) => {
                        let v = rewrite(v, cands, bound, site);
                        bound.push(*n);
                        IrActStmt::Bind(*n, bt.clone(), v, *sp)
                    }
                })
                .collect();
            bound.truncate(mark);
            E::Act(ss, t.clone(), *s)
        }
        E::Record(n, fs, t, s) => E::Record(
            *n,
            fs.iter()
                .map(|f| crate::ir_chapter::IrFieldVal {
                    name: f.name,
                    value: rewrite(&f.value, cands, bound, site),
                })
                .collect(),
            t.clone(),
            *s,
        ),
        E::FieldAccess(r, f, t, s) => {
            E::FieldAccess(Box::new(rewrite(r, cands, bound, site)), f.clone(), t.clone(), *s)
        }
        E::FieldStore(r, f, v, t, s) => E::FieldStore(
            Box::new(rewrite(r, cands, bound, site)),
            f.clone(),
            Box::new(rewrite(v, cands, bound, site)),
            t.clone(),
            *s,
        ),
        E::List(xs, t, s) => E::List(
            xs.iter().map(|x| rewrite(x, cands, bound, site)).collect(),
            t.clone(),
            *s,
        ),
        other => other.clone(),
    }
}

/// `ir-prune-unreachable-roots`. Every definition reachable from the roots by
/// following the names its body mentions, in the original order.
///
/// **THIS RUNS LAST, AFTER THE PASSES**, which is what makes an inlined-away
/// definition disappear rather than merely lose its caller.
pub fn prune_unreachable_roots(defs: Vec<IrDef>, roots: &[&str], syms: &SymTab) -> Vec<IrDef> {
    let by_name: BTreeMap<Sym, usize> =
        defs.iter().enumerate().map(|(i, d)| (d.name, i)).collect();
    let mut seen: BTreeSet<Sym> = BTreeSet::new();
    let mut stack: Vec<Sym> =
        roots.iter().filter_map(|r| syms.find(r)).filter(|n| by_name.contains_key(n)).collect();
    while let Some(n) = stack.pop() {
        if !seen.insert(n) {
            continue;
        }
        if let Some(i) = by_name.get(&n) {
            defs[*i].body.walk(&mut |x| {
                if let IrExpr::Name(m, _, _) = x {
                    if by_name.contains_key(m) && !seen.contains(m) {
                        stack.push(*m);
                    }
                }
            });
        }
    }
    defs.into_iter().filter(|d| seen.contains(&d.name)).collect()
}
