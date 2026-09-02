//! Name resolution: Cobblestone's `NameResolver.codex`.
//!
//! **A scope is two sets and they are not the same thing.** `names` is the
//! chapter's -- top-level definitions, constructors and builtins -- built once
//! and never touched again; `locals` is the per-definition set of parameters,
//! `let` bindings, lambda parameters and pattern variables. Upstream split
//! them for cost (a 2,000-entry list was being cloned on every local binding)
//! and the split is load-bearing here too: forking a scope clones the locals
//! and shares the names.
//!
//! **An unknown name is not an error if it starts with a capital.**
//! `is-type-name` passes anything whose first character is an uppercase
//! letter, so `Nothing` and `MkTup2` resolve without being declared -- and
//! "uppercase" is the char-code range `'E'..'Z'`, which is every capital in
//! the frequency alphabet and nothing else.
//!
//! Three scoping rules a reasonable guess gets backwards:
//!
//! * a `let` binding is in scope for LATER bindings and for the body, but not
//!   for its own value -- upstream adds it after resolving the value;
//! * `induction on n` puts `n` IN SCOPE for the arms, if the scrutinee is a
//!   bare name;
//! * a record literal's field VALUES are resolved and its type name is not.

use crate::ast::*;
use crate::builtins::BUILTINS;
use std::collections::HashSet;

/// Where a name went wrong. The message text is upstream's, because these are
/// diagnostics the front end has to produce and not just count.
#[derive(Debug, Clone)]
pub struct ResolveError {
    pub msg: String,
    pub span: Span,
}

/// `max-errors`, from `BuildSettings.codex`.
pub const MAX_ERRORS: usize = 20;

/// What a `DiagnosticBag` would REPORT for this many errors.
///
/// The bag does not count; it SATURATES. `bag-add-error` stops at
/// `max-errors`, pushes one "Too many errors. Further errors suppressed."
/// and increments once more, so the count sticks at 21 however many arrive
/// after. Reporting the raw total instead reads as a much worse program than
/// the compiler thinks it has -- 116 against 21 on the name resolver's own
/// chapter, which is how this rule was found.
pub fn bag_error_count(n: usize) -> usize {
    if n <= MAX_ERRORS {
        n
    } else {
        MAX_ERRORS + 1
    }
}

pub struct Resolved {
    /// Every error, uncapped. The bag's own count is `bag_error_count`.
    pub errors: Vec<ResolveError>,
    pub top_level_names: Vec<String>,
    pub type_names: Vec<String>,
    pub ctor_names: Vec<String>,
}

/// What one walk of a chapter collects.
///
/// `errors` is the phase's product. `refs` is a SIDE CHANNEL: every
/// `NameRef` that was not a local at the point it was read, tagged with the
/// definition it was read in. The resolver does not want it and does not pay
/// for it -- `collect_refs` is false for `resolve` -- but the call graph
/// cannot be built without the locals set at each point, and that set is
/// exactly what this walk maintains. Rebuilding it in a second walker is how
/// the two would come to disagree about `let`, `induction on` and pattern
/// binders, which are the three rules a reasonable guess gets backwards.
pub struct Walk {
    pub errors: Vec<ResolveError>,
    pub refs: Vec<(usize, String)>,
    collect_refs: bool,
    def_index: usize,
}

impl Walk {
    fn new(collect_refs: bool) -> Self {
        Walk { errors: Vec::new(), refs: Vec::new(), collect_refs, def_index: 0 }
    }
    fn push(&mut self, e: ResolveError) {
        self.errors.push(e);
    }
    fn saw(&mut self, n: &str) {
        if self.collect_refs {
            self.refs.push((self.def_index, n.to_string()));
        }
    }
}

#[derive(Clone)]
struct Scope<'a> {
    names: &'a HashSet<String>,
    locals: HashSet<String>,
}

impl Scope<'_> {
    fn has(&self, n: &str) -> bool {
        self.locals.contains(n) || self.names.contains(n)
    }
    /// `scope-fork`: the locals are cloned, the chapter names are shared.
    fn fork(&self) -> Scope<'_> {
        Scope { names: self.names, locals: self.locals.clone() }
    }
}

/// `is-type-name`: a first character in the char-code range `'E'..'Z'`, which
/// is exactly the capitals. Testing `is_ascii_uppercase` agrees here only
/// because the alphabet's capitals are the ASCII ones; the RANGE is the rule.
fn is_type_name(n: &str) -> bool {
    n.chars().next().is_some_and(|c| c.is_ascii_uppercase())
}

fn undefined(name: &str, span: Span) -> ResolveError {
    ResolveError { msg: format!("Undefined name: {name}"), span }
}

pub fn resolve(ch: &Chapter) -> Resolved {
    walk(ch, false).0
}

/// The same walk, keeping the free-name side channel. `refs[i]` names every
/// non-local read inside `ch.defs[i]`, in encounter order and with
/// duplicates -- the caller decides whether a name read twice is one edge or
/// two.
pub fn resolve_refs(ch: &Chapter) -> (Resolved, Vec<Vec<String>>) {
    let (r, w) = walk(ch, true);
    let mut per_def: Vec<Vec<String>> = vec![Vec::new(); ch.defs.len()];
    for (i, n) in w.refs {
        per_def[i].push(n);
    }
    (r, per_def)
}

fn walk(ch: &Chapter, collect_refs: bool) -> (Resolved, Walk) {
    // The chapter's own set, built once.
    let mut top: Vec<String> = ch.defs.iter().map(|d| d.name.clone()).collect();
    top.sort_by(|a, b| crate::preamble::cce_key(a).cmp(&crate::preamble::cce_key(b)));
    top.dedup();

    let mut type_names: Vec<String> = ch
        .type_defs
        .iter()
        .map(|t| match t {
            TypeDef::Record(n, ..) | TypeDef::Variant(n, ..) | TypeDef::Unit(n, ..) => n.clone(),
        })
        .collect();
    type_names.sort_by(|a, b| crate::preamble::cce_key(a).cmp(&crate::preamble::cce_key(b)));
    type_names.dedup();

    let mut ctor_names: Vec<String> = Vec::new();
    for t in &ch.type_defs {
        match t {
            TypeDef::Variant(_, _, cs, _) => {
                ctor_names.extend(cs.iter().map(|c| c.name.clone()))
            }
            TypeDef::Unit(n, ..) => ctor_names.push(n.clone()),
            TypeDef::Record(..) => {}
        }
    }
    ctor_names.sort_by(|a, b| crate::preamble::cce_key(a).cmp(&crate::preamble::cce_key(b)));
    ctor_names.dedup();

    let mut names: HashSet<String> = top.iter().cloned().collect();
    names.extend(ctor_names.iter().cloned());
    names.extend(BUILTINS.iter().map(|(s, _)| s.to_string()));
    for e in &ch.effect_defs {
        names.extend(e.ops.iter().map(|o| o.name.clone()));
    }
    for c in &ch.class_defs {
        names.extend(c.methods.iter().map(|m| m.name.clone()));
    }

    let mut w = Walk::new(collect_refs);
    for (i, d) in ch.defs.iter().enumerate() {
        w.def_index = i;
        let mut sc = Scope { names: &names, locals: HashSet::new() };
        let mut seen = HashSet::new();
        for p in &d.params {
            if !seen.insert(p.name.clone()) {
                w.push(ResolveError {
                    msg: format!("Duplicate parameter: '{}'", p.name),
                    span: p.span,
                });
            }
            sc.locals.insert(p.name.clone());
        }
        // A declared type that is a `forall` BINDS its variable for the body,
        // through as many nested binders as it has: `claim p : for all (xs :
        // T), for all (ys : T), ..` puts both in scope for the proof, and the
        // proof is where they are used.
        let mut ty = d.declared_type.first();
        while let Some(TypeExpr::Forall(v, _, inner, _)) = ty {
            sc.locals.insert(v.clone());
            ty = Some(inner);
        }
        expr(&mut sc, &d.body, &mut w);
    }

    let errors = std::mem::take(&mut w.errors);
    (Resolved { errors, top_level_names: top, type_names, ctor_names }, w)
}

fn expr(sc: &mut Scope<'_>, e: &Expr, w: &mut Walk) {
    match e {
        Expr::Lit(..) | Expr::Error(..) => {}
        Expr::NameRef(n, s) => {
            if !sc.locals.contains(n) {
                w.saw(n);
            }
            if !sc.has(n) && !is_type_name(n) {
                w.push(undefined(n, *s));
            }
        }
        Expr::Apply(a, b, _) | Expr::Binary(a, _, b, _) | Expr::FieldAssign(a, _, b, _) => {
            expr(sc, a, w);
            expr(sc, b, w);
        }
        Expr::Unary(a, _) | Expr::Lazy(a, _) | Expr::FieldAccess(a, _, _) => expr(sc, a, w),
        Expr::If(a, b, c, _) => {
            expr(sc, a, w);
            expr(sc, b, w);
            expr(sc, c, w);
        }
        Expr::Let(binds, body, _) => {
            let mut fork = sc.fork();
            let mut seen = HashSet::new();
            for b in binds {
                // The value is resolved BEFORE the name is added: a binding
                // cannot see itself, but it can see every one before it.
                expr(&mut fork, &b.value, w);
                if !seen.insert(b.name.clone()) {
                    w.push(ResolveError {
                        msg: format!("Duplicate binding: '{}'", b.name),
                        span: b.span,
                    });
                }
                fork.locals.insert(b.name.clone());
            }
            expr(&mut fork, body, w);
        }
        Expr::Lambda(params, body, _) => {
            let mut fork = sc.fork();
            let mut seen = HashSet::new();
            for p in params {
                if !seen.insert(p.clone()) {
                    w.push(ResolveError {
                        msg: format!("Duplicate parameter: '{p}'"),
                        span: Span::default(),
                    });
                }
                fork.locals.insert(p.clone());
            }
            expr(&mut fork, body, w);
        }
        Expr::Match(scrut, arms, _) => {
            expr(sc, scrut, w);
            match_arms(sc, arms, w);
        }
        Expr::Induction(scrut, arms, _) => {
            // `induction on n` binds `n` for the arms, and only when the
            // scrutinee is a bare name.
            let mut fork = sc.fork();
            if let Expr::NameRef(n, _) = &**scrut {
                fork.locals.insert(n.clone());
            }
            match_arms(&mut fork, arms, w);
        }
        Expr::List(xs, _) => {
            for x in xs {
                expr(sc, x, w);
            }
        }
        // A record literal's TYPE name is not resolved -- only its values.
        Expr::Record(_, fs, _) => {
            for f in fs {
                expr(sc, &f.value, w);
            }
        }
        Expr::Act(ss, _) => {
            let mut fork = sc.fork();
            act_stmts(&mut fork, ss, w);
        }
        Expr::Handle(_, body, clauses, _) => {
            expr(sc, body, w);
            for c in clauses {
                let mut fork = sc.fork();
                fork.locals.insert(c.resume_name.clone());
                let mut seen: HashSet<String> = [c.resume_name.clone()].into_iter().collect();
                for p in &c.params {
                    if !seen.insert(p.clone()) {
                        w.push(ResolveError {
                            msg: format!("Duplicate parameter: '{p}'"),
                            span: c.span,
                        });
                    }
                    fork.locals.insert(p.clone());
                }
                expr(&mut fork, &c.body, w);
            }
        }
        Expr::WithTimeout(_, _, _, body, _) => expr(sc, body, w),
        Expr::Try(_, a, b, c, _) => {
            for region in [a, b, c] {
                let mut fork = sc.fork();
                act_stmts(&mut fork, region, w);
            }
        }
    }
}

fn match_arms(sc: &mut Scope<'_>, arms: &[MatchArm], w: &mut Walk) {
    for a in arms {
        let mut fork = sc.fork();
        let mut seen = HashSet::new();
        pattern(&mut fork, &a.pattern, &mut seen, w);
        expr(&mut fork, &a.guard, w);
        expr(&mut fork, &a.body, w);
    }
}

fn pattern(
    sc: &mut Scope<'_>,
    p: &Pat,
    seen: &mut HashSet<String>,
    w: &mut Walk,
) {
    match p {
        Pat::Var(n, s) => {
            if !seen.insert(n.clone()) {
                w.push(ResolveError {
                    msg: format!("Duplicate pattern variable: '{n}'"),
                    span: *s,
                });
            } else {
                sc.locals.insert(n.clone());
            }
        }
        // A constructor's NAME is not resolved here -- only its sub-patterns.
        Pat::Ctor(_, subs, _) | Pat::Vec_(subs, _) => {
            for s in subs {
                pattern(sc, s, seen, w);
            }
        }
        Pat::Lit(..) | Pat::Wild(..) => {}
    }
}

fn act_stmts(sc: &mut Scope<'_>, stmts: &[ActStmt], w: &mut Walk) {
    let mut seen = HashSet::new();
    for s in stmts {
        match s {
            // A `let` STATEMENT in an act block does NOT fork: its bindings
            // stay in scope for every statement after it, and a chain of them
            // (`let b = .. in let c = .. in ..`) contributes all of its names.
            // `codex/test/act-let-scope.codex` is named for exactly this, and
            // forking here left `a` undefined on the line after it.
            ActStmt::Exec(e, _) => {
                let mut cur = e;
                loop {
                    let Expr::Let(binds, body, _) = cur else {
                        expr(sc, cur, w);
                        break;
                    };
                    let mut bound = HashSet::new();
                    for b in binds {
                        expr(sc, &b.value, w);
                        if !bound.insert(b.name.clone()) {
                            w.push(ResolveError {
                                msg: format!("Duplicate binding: '{}'", b.name),
                                span: b.span,
                            });
                        }
                        sc.locals.insert(b.name.clone());
                    }
                    cur = body;
                }
            }
            ActStmt::Bind(name, e, sp) => {
                // The value first, then the name -- a bind cannot see itself.
                expr(sc, e, w);
                if !seen.insert(name.clone()) {
                    w.push(ResolveError {
                        msg: format!("Duplicate binding: '{name}'"),
                        span: *sp,
                    });
                }
                sc.locals.insert(name.clone());
            }
        }
    }
}
