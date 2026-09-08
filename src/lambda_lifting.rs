//! `IR/LambdaLifting.codex` -- a pass over the lowered chapter.
//!
//! A lambda never reaches the IR text as a lambda. `lift-lambdas` rewrites
//! every one into a top-level definition named `__lam_N`, appended after the
//! chapter's own definitions with an empty chapter-slug, and leaves a
//! reference behind at the site the lambda stood.
//!
//! Three things about it are load-bearing and none is guessable:
//!
//! * **The name is allocated AFTER the body is lifted**, so a NESTED lambda
//!   gets the LOWER number. `lift-one-lambda` lifts the body, then calls
//!   `gen-unique-name`.
//! * **Numbering runs over the WHOLE chapter, before pruning.** The driver
//!   writes `emit-ir-chapter (ir-prune-unreachable-roots lifted-ir ...)`, so a
//!   lambda inside a definition the gold never shows still consumed a number.
//!   That is why `number_lambdas` walks the AST's whole definition list rather
//!   than the lowered one, which is already pruned -- see `ir::emit_defs`.
//! * **Captured variables become the LEADING parameters, sorted by name**, and
//!   the reference site is a partial application over them.
//!
//! A definition whose body IS a lambda is not lifted at all:
//! `absorb-outer-lambdas` merges those parameters into the definition's own,
//! which `lowering::lower_def` has already done by the time this runs.

use crate::ast::Span;
use crate::check::Ty;
use crate::ir_chapter::{IrActStmt, IrDef, IrExpr, IrParam, IrPat};
use crate::symbol::{Sym, SymTab};
use std::collections::{BTreeMap, BTreeSet};

/// `gen-unique-name` (LambdaLifting.codex:59112): the reserved set and the
/// counter, minted DURING the lift.
///
/// **THERE IS NO SEPARATE NUMBERING PASS UPSTREAM, AND OURS COST 90
/// DEFINITIONS.** It keyed each name by the lambda's span, and a lambda the
/// DESUGARER built has a synthetic one -- `for l in xs -> l.name` becomes a
/// `map-list` over a lambda with no source position of its own -- so they all
/// collided. The 3.44 MB self-host emitted ninety definitions called
/// `__lam_372` where `codexir` has ninety distinct ones.
///
/// Interior mutability because `lift_expr` threads this through an immutable
/// borrow, exactly as upstream threads `ctx`.
pub struct LamNames {
    reserved: std::cell::RefCell<BTreeSet<String>>,
    counter: std::cell::Cell<u32>,
}

impl LamNames {
    /// `collect-reserved-names`, over the LOWERED definitions -- which is the
    /// set upstream reserves from, not the chapter's AST.
    fn new(defs: &[IrDef], syms: &SymTab) -> LamNames {
        LamNames {
            reserved: std::cell::RefCell::new(
                defs.iter().map(|d| syms.text(d.name).to_string()).collect(),
            ),
            counter: std::cell::Cell::new(0),
        }
    }

    /// `gen-unique-name-loop`: the first `__lam_N` nothing has taken, and the
    /// counter resumes past it.
    fn gen(&self) -> String {
        let mut reserved = self.reserved.borrow_mut();
        loop {
            let cand = format!("__lam_{}", self.counter.get());
            self.counter.set(self.counter.get() + 1);
            if reserved.insert(cand.clone()) {
                return cand;
            }
        }
    }
}

/// `lift-lambdas` (LambdaLifting.codex:19). The definitions with every lambda
/// replaced, followed by the definitions those lambdas became.
///
pub fn lift_lambdas(defs: Vec<IrDef>, syms: &mut SymTab) -> Vec<IrDef> {
    let names = &LamNames::new(&defs, syms);
    let mut lifted = Vec::new();
    let mut out = Vec::with_capacity(defs.len());
    for d in defs {
        // `lift-defs` opens each definition with its parameters as the whole
        // of `enclosing` -- nothing outside a definition is capturable.
        let mut scope: Vec<Sym> = d.params.iter().map(|p| p.name).collect();
        let body = lift_expr(d.body, &mut scope, names, syms, &mut lifted);
        out.push(IrDef { body, ..d });
    }
    out.extend(lifted);
    out
}

/// `lift-expr`. `enclosing` is the set a lambda here may capture from: local
/// binders only, so a reference to another definition or a builtin is never
/// captured.
fn lift_expr(
    e: IrExpr,
    enclosing: &mut Vec<Sym>,
    names: &LamNames,
    syms: &mut SymTab,
    lifted: &mut Vec<IrDef>,
) -> IrExpr {
    use IrExpr as E;
    let go = |x: Box<IrExpr>, enc: &mut Vec<Sym>, syms: &mut SymTab, lf: &mut Vec<IrDef>| {
        Box::new(lift_expr(*x, enc, names, syms, lf))
    };
    match e {
        E::IntLit(..)
        | E::NumLit(..)
        | E::TextLit(..)
        | E::BoolLit(..)
        | E::CharLit(..)
        | E::Name(..) => e,
        E::Lambda(ps, body, ty, sp) => {
            lift_one(ps, *body, ty, sp, enclosing, names, syms, lifted)
        }
        E::Binary(op, l, r, t, s) => {
            let l = go(l, enclosing, syms, lifted);
            let r = go(r, enclosing, syms, lifted);
            E::Binary(op, l, r, t, s)
        }
        E::Negate(x, t, s) => E::Negate(go(x, enclosing, syms, lifted), t, s),
        E::If(c, th, el, t, s) => {
            let c = go(c, enclosing, syms, lifted);
            let th = go(th, enclosing, syms, lifted);
            let el = go(el, enclosing, syms, lifted);
            E::If(c, th, el, t, s)
        }
        // A let binds its name for the BODY, not for its own value.
        E::Let(n, t, v, b, s) => {
            let v = go(v, enclosing, syms, lifted);
            enclosing.push(n);
            let b = go(b, enclosing, syms, lifted);
            enclosing.pop();
            E::Let(n, t, v, b, s)
        }
        E::Apply(f, a, t, s) => {
            let f = go(f, enclosing, syms, lifted);
            let a = go(a, enclosing, syms, lifted);
            E::Apply(f, a, t, s)
        }
        E::List(xs, t, s) => E::List(
            xs.into_iter().map(|x| lift_expr(x, enclosing, names, syms, lifted)).collect(),
            t,
            s,
        ),
        E::Record(n, fs, t, s) => E::Record(
            n,
            fs.into_iter()
                .map(|mut f| {
                    f.value = lift_expr(f.value, enclosing, names, syms, lifted);
                    f
                })
                .collect(),
            t,
            s,
        ),
        E::FieldAccess(r, f, t, s) => E::FieldAccess(go(r, enclosing, syms, lifted), f, t, s),
        E::FieldStore(r, f, v, t, s) => {
            let r = go(r, enclosing, syms, lifted);
            let v = go(v, enclosing, syms, lifted);
            E::FieldStore(r, f, v, t, s)
        }
        // **A CLAUSE'S PARAMETERS AND ITS RESUME NAME ARE IN SCOPE FOR ITS
        // BODY.** They are not written anywhere a pattern walk would find, so
        // a lambda inside a clause would capture them as free variables and
        // lift them into its own parameter list.
        E::Handle(eff, b, cs, t, s) => {
            let b = go(b, enclosing, syms, lifted);
            let cs = cs
                .into_iter()
                .map(|mut c| {
                    let mark = enclosing.len();
                    enclosing.extend(c.params.iter().copied());
                    enclosing.push(c.resume_name);
                    c.body = lift_expr(c.body, enclosing, names, syms, lifted);
                    enclosing.truncate(mark);
                    c
                })
                .collect();
            E::Handle(eff, b, cs, t, s)
        }
        // A branch's pattern names are in scope for the BODY AND THE GUARD,
        // and the body is lifted first.
        E::Match(sc, bs, t, s) => {
            let sc = go(sc, enclosing, syms, lifted);
            let bs = bs
                .into_iter()
                .map(|mut b| {
                    let mark = enclosing.len();
                    pat_names(&b.pattern, enclosing);
                    b.body = lift_expr(b.body, enclosing, names, syms, lifted);
                    b.guard = lift_expr(b.guard, enclosing, names, syms, lifted);
                    enclosing.truncate(mark);
                    b
                })
                .collect();
            E::Match(sc, bs, t, s)
        }
        // A bind's name is in scope for the statements AFTER it.
        E::Act(ss, t, s) => {
            let mark = enclosing.len();
            let ss = ss
                .into_iter()
                .map(|st| match st {
                    IrActStmt::Exec(v, sp) => {
                        IrActStmt::Exec(lift_expr(v, enclosing, names, syms, lifted), sp)
                    }
                    IrActStmt::Bind(n, bt, v, sp) => {
                        let v = lift_expr(v, enclosing, names, syms, lifted);
                        enclosing.push(n);
                        IrActStmt::Bind(n, bt, v, sp)
                    }
                })
                .collect();
            enclosing.truncate(mark);
            E::Act(ss, t, s)
        }
    }
}

/// `lift-one-lambda`. The body first, then the name, then the definition.
#[allow(clippy::too_many_arguments)]
fn lift_one(
    ps: Vec<IrParam>,
    body: IrExpr,
    ty: Ty,
    sp: Span,
    enclosing: &mut Vec<Sym>,
    names: &LamNames,
    syms: &mut SymTab,
    lifted: &mut Vec<IrDef>,
) -> IrExpr {
    // The body is lifted with the parameters in scope, and this happens BEFORE
    // the name is taken -- which is what makes a nested lambda take the lower
    // number.
    let mark = enclosing.len();
    enclosing.extend(ps.iter().map(|p| p.name));
    let body = lift_expr(body, enclosing, names, syms, lifted);
    enclosing.truncate(mark);

    // `collect-free-vars body-expr param-names enclosing []`: bound is the
    // lambda's OWN parameters, capturable is the scope outside it.
    let mut caps: BTreeMap<Vec<u8>, (Sym, Ty)> = BTreeMap::new();
    let mut bound: Vec<Sym> = ps.iter().map(|p| p.name).collect();
    free_vars(&body, &mut bound, enclosing, syms, &mut caps);

    // **THE NAME IS TAKEN AFTER THE BODY**, which is what makes a nested
    // lambda take the lower number: `lift-one-lambda` calls `gen-unique-name`
    // on the context its own `lift-expr` returned.
    let name = syms.intern(&names.gen());

    // `infer-lambda-return-ty` peels one arrow per parameter, and
    // `build-function-ty` builds the lifted arrows with `empty-row`.
    let mut ret = ty;
    for _ in &ps {
        ret = match ret {
            Ty::Fun(_, _, r) => *r,
            other => other,
        };
    }
    let arrows = |params: &[IrParam], ret: &Ty| -> Ty {
        params.iter().rev().fold(ret.clone(), |acc, p| {
            Ty::Fun(Box::new(p.ty.clone()), Default::default(), Box::new(acc))
        })
    };
    // `build-lifted-params`: the captures come FIRST, in name order.
    let captures: Vec<(Sym, Ty)> = caps.into_values().collect();
    let mut lifted_params: Vec<IrParam> = captures
        .iter()
        .map(|(n, t)| IrParam { name: *n, ty: t.clone(), span: sp })
        .collect();
    lifted_params.extend(ps.iter().cloned());
    let lifted_ty = arrows(&lifted_params, &ret);

    lifted.push(IrDef {
        name,
        params: lifted_params,
        ty: lifted_ty.clone(),
        body,
        chapter_slug: String::new(),
        span: sp,
        // A lifted lambda is nobody's `punctual` definition, and a lambda
        // parameter cannot be declared linear.
        is_punctual: false,
        wcet_budget: 0,
        unique_params: Vec::new(),
    });

    // `build-partial-app`: the name, then one apply per capture, each typed
    // with what is LEFT of the arrow after it.
    let mut acc = IrExpr::Name(name, lifted_ty.clone(), sp);
    let mut acc_ty = lifted_ty;
    for (n, t) in &captures {
        acc_ty = match acc_ty {
            Ty::Fun(_, _, r) => *r,
            other => other,
        };
        acc = IrExpr::Apply(
            Box::new(acc),
            Box::new(IrExpr::Name(*n, t.clone(), sp)),
            acc_ty.clone(),
            sp,
        );
    }
    acc
}

/// `collect-free-vars`: the names this body reads that the ENCLOSING scope
/// binds and the lambda's own parameters do not.
///
/// The type is the one recorded at the FIRST occurrence, because
/// `free-var-has` stops the second from replacing it, and the map is keyed by
/// NAME so the order is `bsearch-freevar-pos`'s -- alphabetical.
fn free_vars(
    e: &IrExpr,
    bound: &mut Vec<Sym>,
    capturable: &[Sym],
    syms: &SymTab,
    out: &mut BTreeMap<Vec<u8>, (Sym, Ty)>,
) {
    use IrExpr as E;
    match e {
        E::Name(n, t, _) => {
            if capturable.contains(n) && !bound.contains(n) {
                // **THE ORDER IS `text-compare`'s, WHICH IS NOT ASCII.**
                // `collect-free-vars` keeps its list sorted by
                // `bsearch-freevar-pos`, and a Codex Text compares as CCE
                // units on a frequency-ordered alphabet: `o` is 16 and `n` is
                // 18, so `old-id` sorts BEFORE `new-id` and the lifted
                // definition takes them in that order. Sorting the bytes put
                // three of the compiler's lifted lambdas' parameters the
                // other way round.
                out.entry(crate::preamble::cce_key(syms.text(*n))).or_insert((*n, t.clone()));
            }
        }
        E::Lambda(ps, b, _, _) => {
            let mark = bound.len();
            bound.extend(ps.iter().map(|p| p.name));
            free_vars(b, bound, capturable, syms, out);
            bound.truncate(mark);
        }
        E::Let(n, _, v, b, _) => {
            free_vars(v, bound, capturable, syms, out);
            bound.push(*n);
            free_vars(b, bound, capturable, syms, out);
            bound.pop();
        }
        E::Handle(_, b, cs, _, _) => {
            free_vars(b, bound, capturable, syms, out);
            for c in cs {
                let mark = bound.len();
                bound.extend(c.params.iter().copied());
                bound.push(c.resume_name);
                free_vars(&c.body, bound, capturable, syms, out);
                bound.truncate(mark);
            }
        }
        E::Match(sc, bs, _, _) => {
            free_vars(sc, bound, capturable, syms, out);
            for b in bs {
                let mark = bound.len();
                pat_names(&b.pattern, bound);
                free_vars(&b.body, bound, capturable, syms, out);
                free_vars(&b.guard, bound, capturable, syms, out);
                bound.truncate(mark);
            }
        }
        E::Act(ss, _, _) => {
            let mark = bound.len();
            for st in ss {
                match st {
                    IrActStmt::Exec(v, _) => free_vars(v, bound, capturable, syms, out),
                    IrActStmt::Bind(n, _, v, _) => {
                        free_vars(v, bound, capturable, syms, out);
                        bound.push(*n);
                    }
                }
            }
            bound.truncate(mark);
        }
        other => {
            for c in other.children() {
                free_vars(c, bound, capturable, syms, out);
            }
        }
    }
}

/// Every name a pattern binds.
pub fn pat_names(p: &IrPat, out: &mut Vec<Sym>) {
    match p {
        IrPat::Var(n, _, _) => out.push(*n),
        IrPat::Wild(..) | IrPat::Lit(..) => {}
        IrPat::Ctor(_, subs, _, _) | IrPat::Vec_(subs, _, _) => {
            subs.iter().for_each(|s| pat_names(s, out))
        }
    }
}

