//! **A PROJECTION OF A GENERATED DICTIONARY IS A DIRECT METHOD USE** (U62,
//! upstream's `collect-dict-projections` and `rewrite-dict-projections`,
//! Ast/Desugarer.codex; MethodLocalPolymorphism.md, stage 2).
//!
//! `C-dict-T.m-impl`, and `d.m-impl` where `d` is bound by a `let` to
//! `C-dict-T` and not shadowed, become the name `m-T` -- for every method `m`
//! of `C` that has method-local type variables. After it each use is an
//! ordinary reference to a definition whose declared type quantifies those
//! variables, so the checker instantiates it per use and lowering types each
//! use from that instantiation. A `let` whose dictionary no longer occurs is
//! dropped. Every other use of a dictionary -- passed, returned, stored,
//! captured -- is left alone, and stays the boundary a typed backend refuses.
//!
//! The map from dictionary to field to target comes from the instance
//! definitions the desugarer turned into those definitions, never from a
//! name's spelling.
use crate::ast::{ActStmt, Chapter, Expr, FieldExpr, HandleClause, LetBind, MatchArm, Pat, TypeExpr};
use crate::symbol::{Sym, SymTab};
use std::rc::Rc;

struct Projection {
    dict: Sym,
    field: Sym,
    target: Sym,
}

/// Names in scope, innermost last: a name bound to a generated dictionary
/// carries it, and any other binding of the name shadows it with `None`.
type Env = Vec<(Sym, Option<Sym>)>;

pub fn apply(ch: &mut Chapter) {
    let projs = collect(ch);
    if projs.is_empty() {
        return;
    }
    let dicts: Vec<Sym> = projs.iter().map(|p| p.dict).collect();
    let rw = Rewrite { projs: &projs, dicts: &dicts };
    for d in ch.defs.iter_mut() {
        if !mentions_any(&d.body, &dicts) {
            continue;
        }
        let env: Env = d.params.iter().map(|p| (p.name, None)).collect();
        d.body = rw.expr(&d.body, &env);
    }
}

/// `collect-dict-projections`: one entry per instance and per method whose
/// class signature names a type variable other than the class's `a`.
fn collect(ch: &mut Chapter) -> Vec<Projection> {
    let mut out = Vec::new();
    let Chapter { syms, class_defs, instance_defs, .. } = ch;
    for id in instance_defs.iter() {
        let Some(cd) = class_defs.iter().find(|c| c.name == id.class_name) else { continue };
        let class = syms.text(id.class_name).to_string();
        let key = syms.text(id.type_name).to_string();
        for m in &id.methods {
            let Some(op) = cd.methods.iter().find(|o| o.name == m.name) else { continue };
            if !has_own_binder(&op.type_expr, syms) {
                continue;
            }
            let mname = syms.text(m.name).to_string();
            out.push(Projection {
                dict: syms.intern(&format!("{class}-dict-{key}")),
                field: syms.intern(&format!("{mname}-impl")),
                target: syms.intern(&format!("{mname}-{key}")),
            });
        }
    }
    out
}

/// `method-free-vars ... ["a"]` is non-empty: a lowercase name in type
/// position that is not the class variable.
fn has_own_binder(t: &TypeExpr, syms: &SymTab) -> bool {
    match t {
        TypeExpr::Named(n, _) => {
            let s = syms.text(*n);
            s != "a" && s.starts_with(|c: char| c.is_ascii_lowercase())
        }
        TypeExpr::Fun(a, r, _) | TypeExpr::PropEq(a, r, _) => has_own_binder(a, syms) || has_own_binder(r, syms),
        TypeExpr::App(c, args, _) => has_own_binder(c, syms) || args.iter().any(|x| has_own_binder(x, syms)),
        TypeExpr::Effect(_, _, _, r, _) | TypeExpr::Linear(r, _) | TypeExpr::BoundedInt(r, ..) | TypeExpr::Constrained(_, _, r, _) => {
            has_own_binder(r, syms)
        }
        TypeExpr::Forall(_, vt, p, _) => has_own_binder(vt, syms) || has_own_binder(p, syms),
    }
}

struct Rewrite<'a> {
    projs: &'a [Projection],
    dicts: &'a [Sym],
}

impl Rewrite<'_> {
    /// `dict-of-expr` / `bound-dict-name`: the generated dictionary a name
    /// denotes, through the innermost binding, else the name itself when it
    /// is one.
    fn dict_of(&self, e: &Expr, env: &Env) -> Option<Sym> {
        let Expr::NameRef(n, _) = e else { return None };
        match env.iter().rev().find(|(m, _)| m == n) {
            Some((_, d)) => *d,
            None => self.dicts.contains(n).then_some(*n),
        }
    }

    fn target(&self, dict: Sym, field: Sym) -> Option<Sym> {
        self.projs.iter().find(|p| p.dict == dict && p.field == field).map(|p| p.target)
    }

    fn expr(&self, e: &Expr, env: &Env) -> Expr {
        let go = |x: &Expr| self.expr(x, env);
        match e {
            Expr::FieldAccess(r, f, s) => {
                if let Some(t) = self.dict_of(r, env).and_then(|d| self.target(d, *f)) {
                    return Expr::NameRef(t, *s);
                }
                Expr::FieldAccess(Rc::new(go(r)), *f, *s)
            }
            Expr::Apply(f, a, s) => Expr::Apply(Rc::new(go(f)), Rc::new(go(a)), *s),
            Expr::Binary(l, op, r, s) => Expr::Binary(Rc::new(go(l)), *op, Rc::new(go(r)), *s),
            Expr::Unary(x, s) => Expr::Unary(Rc::new(go(x)), *s),
            Expr::If(c, t, el, s) => Expr::If(Rc::new(go(c)), Rc::new(go(t)), Rc::new(go(el)), *s),
            Expr::Let(binds, body, s) => self.let_(binds, body, *s, env),
            Expr::Lambda(ps, body, s) => Expr::Lambda(ps.clone(), Rc::new(self.expr(body, &shadow(env, ps))), *s),
            Expr::Match(sc, arms, s) => Expr::Match(Rc::new(go(sc)), self.arms(arms, env), *s),
            Expr::Induction(sc, arms, s) => Expr::Induction(Rc::new(go(sc)), self.arms(arms, env), *s),
            Expr::List(xs, s) => Expr::List(xs.iter().map(go).collect(), *s),
            Expr::Record(n, fs, s) => Expr::Record(
                *n,
                fs.iter().map(|f| FieldExpr { name: f.name, value: go(&f.value), span: f.span }).collect(),
                *s,
            ),
            Expr::Act(ss, s) => Expr::Act(self.stmts(ss, env), *s),
            Expr::Handle(h) => {
                let mut h2 = (**h).clone();
                h2.body = Rc::new(go(&h.body));
                h2.clauses = h
                    .clauses
                    .iter()
                    .map(|c| {
                        let mut names = c.params.clone();
                        names.push(c.resume_name);
                        HandleClause { body: self.expr(&c.body, &shadow(env, &names)), ..c.clone() }
                    })
                    .collect();
                Expr::Handle(Box::new(h2))
            }
            Expr::WithTimeout(w) => {
                let mut w2 = (**w).clone();
                w2.body = Rc::new(go(&w.body));
                Expr::WithTimeout(Box::new(w2))
            }
            Expr::Try(t) => {
                let mut t2 = (**t).clone();
                t2.body = self.stmts(&t.body, env);
                t2.fallback = self.stmts(&t.fallback, env);
                t2.failure = self.stmts(&t.failure, env);
                Expr::Try(Box::new(t2))
            }
            Expr::FieldAssign(r, f, v, s) => Expr::FieldAssign(Rc::new(go(r)), *f, Rc::new(go(v)), *s),
            Expr::Lazy(x, s) => Expr::Lazy(Rc::new(go(x)), *s),
            Expr::Lit(..) | Expr::NameRef(..) | Expr::Error(..) => e.clone(),
        }
    }

    /// `rewrite-dict-let`: each bind records the dictionary its value
    /// denotes, the body is rewritten under them, and a bind of a dictionary
    /// that neither the body nor a later bind still names is dropped.
    fn let_(&self, binds: &[LetBind], body: &Expr, s: crate::ast::Span, env: &Env) -> Expr {
        let mut env2 = env.clone();
        let mut out: Vec<(LetBind, Option<Sym>)> = Vec::new();
        for b in binds {
            let dn = self.dict_of(&b.value, &env2);
            out.push((LetBind { name: b.name, value: self.expr(&b.value, &env2), span: b.span }, dn));
            env2.push((b.name, dn));
        }
        let new_body = self.expr(body, &env2);
        let kept: Vec<LetBind> = out
            .iter()
            .enumerate()
            .filter(|(i, (b, dn))| {
                dn.is_none()
                    || uses(&new_body, b.name)
                    || out[i + 1..].iter().any(|(later, _)| uses(&later.value, b.name))
            })
            .map(|(_, (b, _))| b.clone())
            .collect();
        if kept.is_empty() {
            new_body
        } else {
            Expr::Let(kept, Rc::new(new_body), s)
        }
    }

    fn arms(&self, arms: &[MatchArm], env: &Env) -> Vec<MatchArm> {
        arms.iter()
            .map(|a| {
                let inner = shadow(env, &pat_names(&a.pattern));
                MatchArm { body: self.expr(&a.body, &inner), guard: self.expr(&a.guard, &inner), ..a.clone() }
            })
            .collect()
    }

    fn stmts(&self, ss: &[ActStmt], env: &Env) -> Vec<ActStmt> {
        let mut env = env.clone();
        let mut out = Vec::new();
        for st in ss {
            match st {
                ActStmt::Bind(n, v, s) => {
                    out.push(ActStmt::Bind(*n, self.expr(v, &env), *s));
                    env.push((*n, None));
                }
                ActStmt::Exec(v, s) => out.push(ActStmt::Exec(self.expr(v, &env), *s)),
            }
        }
        out
    }
}

fn shadow(env: &Env, names: &[Sym]) -> Env {
    let mut e = env.clone();
    e.extend(names.iter().map(|n| (*n, None)));
    e
}

fn pat_names(p: &Pat) -> Vec<Sym> {
    match p {
        Pat::Var(n, _) => vec![*n],
        Pat::Ctor(_, subs, _) | Pat::Vec_(subs, _) => subs.iter().flat_map(pat_names).collect(),
        Pat::Lit(..) | Pat::Wild(..) => Vec::new(),
    }
}

/// Whether `n` occurs as a name anywhere in `e` (`aexpr-uses-name`).
fn uses(e: &Expr, n: Sym) -> bool {
    mentions_any(e, &[n])
}

/// Whether any of `names` occurs as a name anywhere in `e`.
fn mentions_any(e: &Expr, names: &[Sym]) -> bool {
    let m = |x: &Expr| mentions_any(x, names);
    let stmts = |ss: &[ActStmt]| {
        ss.iter().any(|s| match s {
            ActStmt::Bind(_, v, _) | ActStmt::Exec(v, _) => m(v),
        })
    };
    match e {
        Expr::NameRef(x, _) => names.contains(x),
        Expr::Apply(a, b, _) | Expr::Binary(a, _, b, _) | Expr::FieldAssign(a, _, b, _) => m(a) || m(b),
        Expr::Unary(x, _) | Expr::Lambda(_, x, _) | Expr::FieldAccess(x, _, _) | Expr::Lazy(x, _) => m(x),
        Expr::If(c, t, el, _) => m(c) || m(t) || m(el),
        Expr::Let(bs, body, _) => bs.iter().any(|b| m(&b.value)) || m(body),
        Expr::Match(sc, arms, _) | Expr::Induction(sc, arms, _) => m(sc) || arms.iter().any(|a| m(&a.body) || m(&a.guard)),
        Expr::List(xs, _) => xs.iter().any(m),
        Expr::Record(_, fs, _) => fs.iter().any(|f| m(&f.value)),
        Expr::Act(ss, _) => stmts(ss),
        Expr::Handle(h) => m(&h.body) || h.clauses.iter().any(|c| m(&c.body)),
        Expr::WithTimeout(w) => m(&w.body),
        Expr::Try(t) => stmts(&t.body) || stmts(&t.fallback) || stmts(&t.failure),
        Expr::Lit(..) | Expr::Error(..) => false,
    }
}
