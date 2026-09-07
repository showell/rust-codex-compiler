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

/// `lift-lambdas` (LambdaLifting.codex:19). The definitions with every lambda
/// replaced, followed by the definitions those lambdas became.
///
/// `names` maps a lambda's span to the `__lam_N` reserved for it by
/// `number_lambdas`, which is a separate pass because it must see definitions
/// this one never will.
pub fn lift_lambdas(
    defs: Vec<IrDef>,
    names: &BTreeMap<u64, String>,
    syms: &mut SymTab,
) -> Vec<IrDef> {
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
    names: &BTreeMap<u64, String>,
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
    names: &BTreeMap<u64, String>,
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
    let mut caps: BTreeMap<String, (Sym, Ty)> = BTreeMap::new();
    let mut bound: Vec<Sym> = ps.iter().map(|p| p.name).collect();
    free_vars(&body, &mut bound, enclosing, syms, &mut caps);

    // The numbering pass reserved a name for this span. A lambda it never saw
    // is a bug in that pass, not something to paper over with a fresh name --
    // two lambdas sharing a name would emit two definitions under one.
    let name = match names.get(&crate::check::expr_type_key(sp)) {
        Some(n) => syms.intern(n),
        None => syms.intern("__lam_unnumbered"),
    };

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
    out: &mut BTreeMap<String, (Sym, Ty)>,
) {
    use IrExpr as E;
    match e {
        E::Name(n, t, _) => {
            if capturable.contains(n) && !bound.contains(n) {
                out.entry(syms.text(*n).to_string()).or_insert((*n, t.clone()));
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

/// Every lambda in the chapter, keyed by `expr_type_key` of its span, mapped
/// to the `__lam_N` it will be lifted to.
///
/// **THIS WALKS THE AST, AND IT WALKS ALL OF IT.** Numbering happens before
/// pruning upstream, so a lambda in a definition the emitter will never reach
/// still consumed a number. `collect-reserved-names` seeds the reserved set
/// with every definition name, so a chapter that already defines `__lam_0`
/// pushes the first lambda to `__lam_1`.
pub fn number_lambdas(ch: &crate::ast::Chapter) -> BTreeMap<u64, String> {
    let mut reserved: BTreeSet<String> =
        ch.defs.iter().map(|d| ch.syms.text(d.name).to_string()).collect();
    let mut counter: u32 = 0;
    let mut out = BTreeMap::new();
    for d in &ch.defs {
        number(absorbed_body(&d.body), &mut reserved, &mut counter, &mut out);
    }
    out
}

/// The body under any lambdas a definition wears directly, whose parameters
/// are the definition's own.
fn absorbed_body(body: &crate::ast::Expr) -> &crate::ast::Expr {
    let mut b = body;
    while let crate::ast::Expr::Lambda(_, inner, _) = b {
        b = inner;
    }
    b
}

/// `lift-expr`'s traversal, for numbering alone. The ORDER is the whole point,
/// so this mirrors the arms rather than reusing `Expr::walk` -- that one is
/// pre-order and would number a lambda before its own body.
fn number(
    e: &crate::ast::Expr,
    reserved: &mut BTreeSet<String>,
    counter: &mut u32,
    out: &mut BTreeMap<u64, String>,
) {
    use crate::ast::ActStmt;
    use crate::ast::Expr as E;
    let mut go = |x: &E| number(x, reserved, counter, out);
    match e {
        E::Lit(..) | E::NameRef(..) | E::Error(..) => {}
        E::Lambda(_, body, sp) => {
            // A curried chain is ONE lifted definition: `lift-one-lambda`
            // recurses on a lambda body with the parameters concatenated.
            number(absorbed_body(body), reserved, counter, out);
            // `gen-unique-name-loop`: the first `__lam_N` nothing has taken,
            // and the counter resumes past it.
            let name = loop {
                let cand = format!("__lam_{}", *counter);
                *counter += 1;
                if reserved.insert(cand.clone()) {
                    break cand;
                }
            };
            out.insert(crate::check::expr_type_key(*sp), name);
        }
        E::Apply(a, b, _) | E::Binary(a, _, b, _) | E::FieldAssign(a, _, b, _) => {
            go(a);
            go(b);
        }
        E::Unary(a, _) | E::Lazy(a, _) | E::FieldAccess(a, _, _) => go(a),
        E::If(a, b, c, _) => {
            go(a);
            go(b);
            go(c);
        }
        E::Let(bs, body, _) => {
            for b in bs {
                go(&b.value);
            }
            go(body);
        }
        // `lift-branches` takes the body before the guard.
        E::Match(s, arms, _) | E::Induction(s, arms, _) => {
            go(s);
            for a in arms {
                go(&a.body);
                go(&a.guard);
            }
        }
        E::List(xs, _) => xs.iter().for_each(go),
        E::Record(_, fs, _) => fs.iter().for_each(|f| go(&f.value)),
        E::Act(ss, _) => ss.iter().for_each(|s| match s {
            ActStmt::Bind(_, v, _) | ActStmt::Exec(v, _) => go(v),
        }),
        E::Handle(h) => {
            go(&h.body);
            h.clauses.iter().for_each(|c| go(&c.body));
        }
        E::WithTimeout(w) => go(&w.body),
        E::Try(t) => {
            for group in [&t.body, &t.fallback, &t.failure] {
                group.iter().for_each(|s| match s {
                    ActStmt::Bind(_, v, _) | ActStmt::Exec(v, _) => go(v),
                });
            }
        }
    }
}
