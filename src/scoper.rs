//! The chapter scoper -- upstream's `Semantics/ChapterScoper.codex`.
//!
//! A compilation unit is several chapters, and two of them may define the
//! same name. Upstream keeps both: a colliding name is MANGLED with its
//! chapter (`slugify(chapter) & "_" & name`), each chapter's own mentions
//! resolve to its own definition, and a chapter that defines neither gets
//! the first chapter's. `opening` never collides. The mangled names are
//! what the IR carries.
//!
//! Without this, one environment held the last definition of a colliding
//! name for every chapter, and the desk family's `format-time (dt) =
//! pad2 (dt.hour) ...` was checked against another chapter's `format-time :
//! Integer -> Text` -- a record where an integer belongs, on a program the
//! oracle compiles clean.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::ast::{ActStmt, Chapter, Expr, HandleClause, HandleExpr, LetBind, MatchArm, Name, Pat, TryExpr, WithTimeoutExpr};
use crate::symbol::SymTab;

/// `slugify`: spaces to dashes, uppercase to lowercase.
fn slugify(s: &str) -> String {
    s.chars().map(|c| if c == ' ' { '-' } else { c.to_ascii_lowercase() }).collect()
}

/// `mangle-name`.
fn mangle(slug: &str, name: &str) -> String {
    format!("{}_{}", slugify(slug), name)
}

pub fn apply(ch: &mut Chapter) {
    let opening = ch.syms.find("opening");
    // `find-colliding-names`: a name defined in two chapters.
    let mut chapters_of: BTreeMap<Name, BTreeSet<String>> = BTreeMap::new();
    for d in &ch.defs {
        if Some(d.name) == opening {
            continue;
        }
        chapters_of.entry(d.name).or_default().insert(d.chapter_slug.clone());
    }
    let colliding: BTreeSet<Name> = chapters_of.iter().filter(|(_, cs)| cs.len() > 1).map(|(n, _)| *n).collect();
    if colliding.is_empty() {
        return;
    }
    // The first chapter defining each colliding name, in definition order:
    // what a chapter that defines neither resolves to.
    let mut first_slug: BTreeMap<Name, String> = BTreeMap::new();
    for d in &ch.defs {
        if colliding.contains(&d.name) {
            first_slug.entry(d.name).or_insert_with(|| d.chapter_slug.clone());
        }
    }
    // `build-chapter-rename-map`, per chapter.
    let slugs: BTreeSet<String> = ch.defs.iter().map(|d| d.chapter_slug.clone()).collect();
    let mut maps: BTreeMap<String, BTreeMap<Name, Name>> = BTreeMap::new();
    for slug in &slugs {
        let mut map = BTreeMap::new();
        for n in &colliding {
            let defines_here = ch.defs.iter().any(|d| d.name == *n && d.chapter_slug == *slug);
            let owner = if defines_here { slug.clone() } else { first_slug[n].clone() };
            let mangled = ch.syms.intern(&mangle(&owner, ch.syms.text(*n)));
            map.insert(*n, mangled);
        }
        maps.insert(slug.clone(), map);
    }
    // Rename the definitions and rewrite every mention in their bodies.
    for d in &mut ch.defs {
        let map = &maps[&d.chapter_slug];
        if colliding.contains(&d.name) {
            d.name = map[&d.name];
        }
        let mut scope = Scope { map, shadowed: Vec::new() };
        scope.push_names(d.params.iter().map(|p| p.name));
        d.body = scope.expr(&d.body);
    }
    let _ = &ch.syms as &SymTab;
}

/// The chapter's rename map, minus the names bound locally around the
/// expression being rewritten (`remove-renames-for-params` and kin).
struct Scope<'a> {
    map: &'a BTreeMap<Name, Name>,
    shadowed: Vec<Name>,
}

impl Scope<'_> {
    fn push_names(&mut self, names: impl Iterator<Item = Name>) {
        self.shadowed.extend(names);
    }

    fn lookup(&self, n: Name) -> Name {
        if self.shadowed.contains(&n) {
            return n;
        }
        self.map.get(&n).copied().unwrap_or(n)
    }

    fn scoped<T>(&mut self, names: Vec<Name>, f: impl FnOnce(&mut Self) -> T) -> T {
        let mark = self.shadowed.len();
        self.shadowed.extend(names);
        let out = f(self);
        self.shadowed.truncate(mark);
        out
    }

    fn rc(&mut self, e: &Rc<Expr>) -> Rc<Expr> {
        Rc::new(self.expr(e))
    }

    fn arms(&mut self, arms: &[MatchArm]) -> Vec<MatchArm> {
        arms.iter()
            .map(|a| {
                let bound = pat_names(&a.pattern);
                self.scoped(bound, |s| MatchArm {
                    pattern: a.pattern.clone(),
                    body: s.expr(&a.body),
                    guard: s.expr(&a.guard),
                    span: a.span,
                    alt_group: a.alt_group,
                })
            })
            .collect()
    }

    fn stmts(&mut self, stmts: &[ActStmt]) -> Vec<ActStmt> {
        let mark = self.shadowed.len();
        let mut out = Vec::new();
        for s in stmts {
            match s {
                ActStmt::Bind(n, e, sp) => {
                    let e2 = self.expr(e);
                    self.shadowed.push(*n);
                    out.push(ActStmt::Bind(*n, e2, *sp));
                }
                ActStmt::Exec(e, sp) => out.push(ActStmt::Exec(self.expr(e), *sp)),
            }
        }
        self.shadowed.truncate(mark);
        out
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        match e {
            Expr::NameRef(n, sp) => Expr::NameRef(self.lookup(*n), *sp),
            Expr::Lit(..) | Expr::Error(..) => e.clone(),
            Expr::Apply(f, a, sp) => Expr::Apply(self.rc(f), self.rc(a), *sp),
            Expr::Binary(l, op, r, sp) => Expr::Binary(self.rc(l), *op, self.rc(r), *sp),
            Expr::Unary(x, sp) => Expr::Unary(self.rc(x), *sp),
            Expr::Lazy(x, sp) => Expr::Lazy(self.rc(x), *sp),
            Expr::If(c, t, el, sp) => Expr::If(self.rc(c), self.rc(t), self.rc(el), *sp),
            Expr::Let(binds, body, sp) => {
                let mark = self.shadowed.len();
                let mut out = Vec::new();
                for b in binds {
                    let value = self.expr(&b.value);
                    self.shadowed.push(b.name);
                    out.push(LetBind { name: b.name, value, span: b.span });
                }
                let body2 = self.rc(body);
                self.shadowed.truncate(mark);
                Expr::Let(out, body2, *sp)
            }
            Expr::Lambda(ps, body, sp) => {
                let body2 = self.scoped(ps.clone(), |s| s.rc(body));
                Expr::Lambda(ps.clone(), body2, *sp)
            }
            Expr::Match(sc, arms, sp) => Expr::Match(self.rc(sc), self.arms(arms), *sp),
            Expr::Induction(sc, arms, sp) => Expr::Induction(self.rc(sc), self.arms(arms), *sp),
            Expr::List(xs, sp) => Expr::List(xs.iter().map(|x| self.expr(x)).collect(), *sp),
            Expr::Record(n, fields, sp) => Expr::Record(
                *n,
                fields
                    .iter()
                    .map(|f| crate::ast::FieldExpr { name: f.name, value: self.expr(&f.value), span: f.span })
                    .collect(),
                *sp,
            ),
            Expr::FieldAccess(r, f, sp) => Expr::FieldAccess(self.rc(r), *f, *sp),
            Expr::FieldAssign(r, f, v, sp) => Expr::FieldAssign(self.rc(r), *f, self.rc(v), *sp),
            Expr::Act(stmts, sp) => Expr::Act(self.stmts(stmts), *sp),
            Expr::Handle(h) => Expr::Handle(Box::new(HandleExpr {
                effect: h.effect,
                body: self.rc(&h.body),
                clauses: h
                    .clauses
                    .iter()
                    .map(|c| {
                        let bound: Vec<Name> = c.params.iter().copied().chain(std::iter::once(c.resume_name)).collect();
                        let body = self.scoped(bound, |s| s.expr(&c.body));
                        HandleClause {
                            op_name: c.op_name,
                            params: c.params.clone(),
                            resume_name: c.resume_name,
                            body,
                            span: c.span,
                        }
                    })
                    .collect(),
                span: h.span,
            })),
            Expr::WithTimeout(w) => Expr::WithTimeout(Box::new(WithTimeoutExpr {
                timeout: w.timeout.clone(),
                effects: w.effects.clone(),
                labels: w.labels.clone(),
                body: self.rc(&w.body),
                span: w.span,
            })),
            Expr::Try(t) => Expr::Try(Box::new(TryExpr {
                count: t.count,
                body: self.stmts(&t.body),
                fallback: self.stmts(&t.fallback),
                failure: self.stmts(&t.failure),
                span: t.span,
            })),
        }
    }
}

fn pat_names(p: &Pat) -> Vec<Name> {
    match p {
        Pat::Var(n, _) => vec![*n],
        Pat::Ctor(_, subs, _) | Pat::Vec_(subs, _) => subs.iter().flat_map(pat_names).collect(),
        _ => Vec::new(),
    }
}
