//! The chapter scoper -- upstream's `Semantics/ChapterScoper.codex`.
//!
//! A compilation unit is several chapters, and two of them may define the
//! same name. Upstream keeps both: a colliding name is MANGLED with its
//! chapter (`slugify(chapter) & "_" & name`), each chapter's own mentions
//! resolve to its own definition, and a chapter that defines neither must
//! CITE the one it means (`cites Q chapter C (name)`, `apply-cite-selected`).
//! A mention that is neither its chapter's own nor cited is AMBIGUOUS: it is
//! left unmangled and recorded in `Chapter::ambiguous_refs`, and the checker
//! refuses it (CDX3027), as upstream's resolver does. `opening` never
//! collides. The mangled names are what the IR carries.
//!
//! Without this, one environment held the last definition of a colliding
//! name for every chapter, and the desk family's `format-time (dt) =
//! pad2 (dt.hour) ...` was checked against another chapter's `format-time :
//! Integer -> Text` -- a record where an integer belongs, on a program the
//! oracle compiles clean.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use crate::ast::{ActStmt, Chapter, Span, Expr, HandleClause, HandleExpr, LetBind, MatchArm, Name, Pat, TryExpr, WithTimeoutExpr};
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
    // `build-all-assignments`: one per definition the source wrote, in order.
    // The desugarer's synthesised definitions carry no chapter and are not
    // among them.
    let assignments: Vec<(Name, String)> =
        ch.defs.iter().filter(|d| !d.chapter_slug.is_empty()).map(|d| (d.name, d.chapter_slug.clone())).collect();
    let slug_cache: Vec<String> = assignments.iter().map(|(_, s)| cite_key(s)).collect();
    // `build-chapter-rename-map`, then `apply-cite-overrides`, per chapter.
    let slugs: BTreeSet<String> = ch.defs.iter().map(|d| d.chapter_slug.clone()).collect();
    let mut maps: BTreeMap<String, BTreeMap<Name, Owner>> = BTreeMap::new();
    for slug in &slugs {
        let mut map: BTreeMap<Name, Owner> = BTreeMap::new();
        for (n, owner) in &assignments {
            if !colliding.contains(n) {
                continue;
            }
            if owner == slug {
                map.insert(*n, Owner::Mangled(owner.clone()));
            } else {
                match map.get_mut(n) {
                    Some(Owner::Ambiguous(others)) => others.push(owner.clone()),
                    Some(Owner::Mangled(_)) => {}
                    None => {
                        map.insert(*n, Owner::Ambiguous(vec![owner.clone()]));
                    }
                }
            }
        }
        for c in ch.citations.iter().filter(|c| c.citing_chapter == *slug) {
            let quire = ch.syms.text(c.quire).to_string();
            let chapter = ch.syms.text(c.chapter_name).to_string();
            let cite_slug = cite_slug_for(&quire, &chapter, &assignments, &slug_cache);
            for n in &c.selected_names {
                let defines_here = assignments.iter().any(|(a, s)| a == n && s == slug);
                if colliding.contains(n) && !defines_here {
                    map.insert(*n, Owner::Mangled(cite_slug.clone()));
                }
            }
        }
        maps.insert(slug.clone(), map);
    }
    // Every chapter's own mangled names, interned once.
    let mut mangled: BTreeMap<String, BTreeMap<Name, Name>> = BTreeMap::new();
    for (slug, map) in &maps {
        let mut m = BTreeMap::new();
        for (n, o) in map {
            if let Owner::Mangled(owner) = o {
                m.insert(*n, ch.syms.intern(&mangle(owner, ch.syms.text(*n))));
            }
        }
        mangled.insert(slug.clone(), m);
    }
    // Rename the definitions and rewrite every mention in their bodies.
    let mut ambiguous: Vec<(Span, String)> = Vec::new();
    for d in &mut ch.defs {
        let map = &mangled[&d.chapter_slug];
        if colliding.contains(&d.name) {
            if let Some(m) = map.get(&d.name) {
                d.name = *m;
            }
        }
        let mut scope = Scope {
            map,
            owners: &maps[&d.chapter_slug],
            syms: &ch.syms,
            shadowed: Vec::new(),
            ambiguous: &mut ambiguous,
        };
        scope.push_names(d.params.iter().map(|p| p.name));
        d.body = scope.expr(&d.body);
    }
    for (sp, msg) in ambiguous {
        ch.ambiguous_refs.insert((sp.offset, sp.len), msg);
    }
}

/// Where a colliding name points from one chapter: a definition, by the
/// chapter that owns it, or nowhere yet -- the chapters that define it, in
/// definition order, none of them this one (`ambiguity-marker`).
#[derive(Clone, Debug)]
enum Owner {
    Mangled(String),
    Ambiguous(Vec<String>),
}

/// `cite-key`: spaces removed, ASCII letters lowered.
fn cite_key(s: &str) -> String {
    s.chars().filter(|c| *c != ' ').map(|c| c.to_ascii_lowercase()).collect()
}

/// `find-slug-for-cite-name`: the slug whose key is `quire--chapter`, else
/// the one slug that is the bare chapter or ends in `--chapter`. The count is
/// over ASSIGNMENTS, one per definition, as upstream's `count-bare-matches`
/// walks the slug cache: a bare cite finds its chapter only when that chapter
/// carries one definition. "" when nothing matches.
fn cite_slug_for(quire: &str, chapter: &str, assignments: &[(Name, String)], slug_cache: &[String]) -> String {
    let exact = cite_key(&format!("{quire}--{chapter}"));
    if let Some(i) = slug_cache.iter().position(|s| *s == exact) {
        return assignments[i].1.clone();
    }
    let bare = cite_key(chapter);
    let suffix = format!("--{bare}");
    let hits = |s: &String| *s == bare || s.ends_with(&suffix);
    if slug_cache.iter().filter(|s| hits(s)).count() == 1 {
        if let Some(i) = slug_cache.iter().position(hits) {
            return assignments[i].1.clone();
        }
    }
    String::new()
}

/// The chapter's rename map, minus the names bound locally around the
/// expression being rewritten (`remove-renames-for-params` and kin).
struct Scope<'a> {
    map: &'a BTreeMap<Name, Name>,
    owners: &'a BTreeMap<Name, Owner>,
    syms: &'a SymTab,
    shadowed: Vec<Name>,
    ambiguous: &'a mut Vec<(Span, String)>,
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

    /// A mention: its chapter's name for it, or -- for a colliding name this
    /// chapter neither defines nor cites -- the name unchanged, with the
    /// resolver's CDX3027 message recorded against its span.
    fn mention(&mut self, n: Name, sp: Span) -> Name {
        if !self.shadowed.contains(&n) {
            if let Some(Owner::Ambiguous(others)) = self.owners.get(&n) {
                let name = self.syms.text(n);
                self.ambiguous.push((
                    sp,
                    format!(
                        "'{name}' is defined in more than one other chapter ({}) and in none of this chapter's; \
                         cite the one you mean by name: cites <Quire> chapter <Name> ({name})",
                        others.join(", ")
                    ),
                ));
                return n;
            }
        }
        self.lookup(n)
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
            Expr::NameRef(n, sp) => Expr::NameRef(self.mention(*n, *sp), *sp),
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
