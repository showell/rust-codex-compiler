//! **CODEX WRITES A LIST IN PLACE; ROC ANSWERS A NEW ONE.** `list-set-at xs i
//! v` changes `xs` itself, so every later use of `xs` -- in this definition,
//! or in a caller that passed it -- sees the write. A Roc list is a value.
//! This pass, run on the lowered definitions before `roc_emit`, makes the
//! writes explicit so the value semantics mean what the in-place ones did:
//!
//! - **A write is a new VERSION.** After `list-set-at xs ...` (bound or not),
//!   every later use of `xs`, or of any name bound to it, is the new version.
//! - **A function that writes a list parameter hands the last version back.**
//!   If it already answers that list it is a *list writer* and its answer is
//!   the new version; otherwise it is a *tuple writer* and answers
//!   `(answer, list, ...)`, one list per written parameter in parameter order.
//!   A caller then carries on with the version it got back. Which functions
//!   write is a fixed point over the chapter, since a call to a writer writes.
//! - **A branch that leaves a list at different versions answers them.** The
//!   `if` or `when` returns `(value, list, ...)` and the code after it
//!   continues with those. In tail position the definition's own tuple is
//!   built in each branch instead, so a self-call stays a tail call.
//!
//! What a write does inside an expression is hoisted, in evaluation order,
//! into `let`s just ahead of it, never past a branch or a lambda: a
//! conditional write stays conditional. A read of the list among the same
//! call's earlier arguments sees the written version, where Codex's
//! left-to-right evaluation saw the old one; no program in the corpus reads
//! a list in the same call that writes it.
//!
//! Refused, by definition, with the reason: a write to a list held in a
//! record field whose answer is dropped (`dropped_field_write`), a write to
//! a list after it was stored by name in a record, a list or a constructor, a lambda
//! that writes a list it captured, a writer used as a value, a write in one statement of an `act`
//! that a later statement reads, and a write under `handle`, `with-timeout`
//! or `try`.
//!
//! The tuple is spelled with reserved names `roc_emit` writes as Roc: the
//! type and the constructor are `__copyout`, and `__copyout-at-K` is the
//! K-th element.
use crate::check::Ty;
use crate::ir_chapter::{IrActStmt, IrBranch, IrDef, IrExpr};
use crate::symbol::{Sym, SymTab};
use std::collections::{BTreeMap, BTreeSet};

pub const TUPLE: &str = "__copyout";
pub const AT: &str = "__copyout-at-";

#[derive(Clone, Debug, PartialEq)]
struct Writer {
    arity: usize,
    /// The written parameters' positions, in order.
    written: Vec<usize>,
    /// It answers the (one) list it writes, so the answer is the version.
    returns_list: bool,
}

/// Rewrite every definition that writes a list; answer the definitions it
/// could not, with the reason. A definition it could not rewrite is left as
/// lowered.
pub fn apply(defs: Vec<IrDef>, syms: &mut SymTab) -> (Vec<IrDef>, Vec<(Sym, String)>) {
    let Some(set_at) = syms.find("list-set-at") else { return (defs, Vec::new()) };
    let tuple = syms.intern(TUPLE);
    let mut writers: BTreeMap<Sym, Writer> = BTreeMap::new();
    // The fixed point. Writing only grows, so this ends; the bound is a
    // guard, not a limit anything reaches.
    for _ in 0..64 {
        let mut next = BTreeMap::new();
        for d in &defs {
            if !touches(d, set_at, &writers) {
                continue;
            }
            let mut rw = Rw::new(syms, set_at, tuple, &writers);
            if let Ok(Some(w)) = rw.classify(d) {
                next.insert(d.name, w);
            }
        }
        if next == writers {
            break;
        }
        writers = next;
    }
    // **WHICH WRITERS ANSWER THEIR LIST IS A GREATEST FIXED POINT.** A
    // writer that answers the list it writes (`brotli-histo`, answering
    // `freq`) usually says so by a self-call in tail position, and the
    // iteration above, starting from nothing, can never see that: it settles
    // on a tuple. So every single-list writer whose result is that list is
    // assumed to answer it, and one whose leaves say otherwise is dropped,
    // until none is. It matters beyond shape: the answer of a list writer IS
    // the list, and a caller that writes through it must advance that list.
    let by_name: BTreeMap<Sym, &IrDef> = defs.iter().map(|d| (d.name, d)).collect();
    let mut assumed: BTreeSet<Sym> = writers
        .iter()
        .filter(|(n, w)| {
            let d = by_name[*n];
            w.written.len() == 1 && result_after(&d.ty, d.params.len()) == d.params[w.written[0]].ty
        })
        .map(|(n, _)| *n)
        .collect();
    loop {
        let mut trial = writers.clone();
        for n in &assumed {
            trial.get_mut(n).expect("a writer").returns_list = true;
        }
        let mut dropped = Vec::new();
        for n in &assumed {
            let d = by_name[n];
            let p = d.params[trial[n].written[0]].name;
            let mut rw = Rw::new(syms, set_at, tuple, &trial);
            if !rw.answers_list(d, p) {
                dropped.push(*n);
            }
        }
        if dropped.is_empty() {
            writers = trial;
            break;
        }
        for n in dropped {
            assumed.remove(&n);
        }
    }
    if std::env::var_os("LV_TRACE").is_some() {
        for (n, w) in &writers {
            eprintln!("list_versions: `{}` writes {:?}{}", syms.text(*n), w.written, if w.returns_list { ", answers the list" } else { "" });
        }
    }
    // Each chapter's own top-level names, which a version must not shadow.
    let mut chapter_names: BTreeMap<String, BTreeSet<Sym>> = BTreeMap::new();
    for d in &defs {
        chapter_names.entry(d.origin.clone()).or_default().insert(d.name);
    }
    let mut out = Vec::new();
    let mut failed = Vec::new();
    for d in defs {
        if !touches(&d, set_at, &writers) {
            out.push(d);
            continue;
        }
        let mut rw = Rw::new(syms, set_at, tuple, &writers);
        rw.taken = chapter_names[&d.origin].clone();
        rw.taken.extend(d.params.iter().map(|p| p.name));
        d.body.walk(&mut |x| match x {
            IrExpr::Name(n, _, _) | IrExpr::Let(n, ..) => {
                rw.taken.insert(*n);
            }
            IrExpr::Match(_, bs, _, _) => {
                for b in bs {
                    rw.taken.extend(pat_names(&b.pattern));
                }
            }
            IrExpr::Lambda(ps, ..) => rw.taken.extend(ps.iter().map(|p| p.name)),
            _ => {}
        });
        let result = rw.rewrite(&d).and_then(|nd| match rw.violation.take() {
            Some(why) => Err(why),
            None => Ok(nd),
        });
        match result {
            Ok(nd) => out.push(nd),
            Err(why) => {
                failed.push((d.name, why));
                out.push(d);
            }
        }
    }
    (out, failed)
}

/// **A WRITE THROUGH A RECORD FIELD WHOSE ANSWER IS DROPPED.** Writing
/// `(node.forward)` changes the list every holder of that record sees; a Roc
/// record keeps the old one, and no renaming reaches it. A program that uses
/// the answer (rebuilding the record with it, as `fb-set` does) means the
/// same thing in both; one that binds it to a name it never reads, or runs it
/// as a statement, relies on the record changing under it
/// (`rts-extend-path-loop`'s `dummy`), and is refused.
fn dropped_field_write(v: &IrExpr, set_at: Sym) -> bool {
    let (head, args) = flatten(v);
    matches!(head, IrExpr::Name(f, _, _) if *f == set_at) && args.len() == 3 && matches!(args[0], IrExpr::FieldAccess(..))
}

fn mentions(e: &IrExpr, n: Sym) -> bool {
    let mut hit = false;
    e.walk(&mut |x| {
        if matches!(x, IrExpr::Name(m, _, _) if *m == n) {
            hit = true;
        }
    });
    hit
}

const DROPPED_FIELD_WRITE: &str =
    "it writes a list held in a record field and drops the answer, relying on the record changing under it";

/// Whether a definition writes a list or calls a writer at all; one that
/// does neither is passed through as it is.
fn touches(d: &IrDef, set_at: Sym, writers: &BTreeMap<Sym, Writer>) -> bool {
    let mut hit = false;
    d.body.walk(&mut |x| {
        if let IrExpr::Name(n, _, _) = x {
            if *n == set_at || writers.contains_key(n) {
                hit = true;
            }
        }
    });
    hit
}

/// The versions in scope: each list's ROOT (the name it was first bound to)
/// and the name its current version has.
#[derive(Clone, Default)]
struct Env {
    current: BTreeMap<Sym, Sym>,
    /// Every name bound to a version of a root, the root itself included.
    root_of: BTreeMap<Sym, Sym>,
    /// The names in scope here: a list bound inside one arm is not joined
    /// after it.
    bound: BTreeSet<Sym>,
    /// Roots stored, by name, in a record, a list or a constructor: they
    /// hold the list itself, so a later write would have to reach them too,
    /// and no renaming does.
    stored: BTreeSet<Sym>,
}

impl Env {
    fn root(&self, n: Sym) -> Sym {
        self.root_of.get(&n).copied().unwrap_or(n)
    }
}

type Pre = Vec<(Sym, Ty, IrExpr)>;

struct Rw<'a> {
    syms: &'a mut SymTab,
    set_at: Sym,
    tuple: Sym,
    writers: &'a BTreeMap<Sym, Writer>,
    /// Each root's list type, for the versions minted from it.
    types: BTreeMap<Sym, Ty>,
    fresh: usize,
    /// The roots the last `join` answered, for `finish_join`.
    pending: Vec<Sym>,
    /// Set when a list is written after it was stored (`Env::stored`).
    violation: Option<String>,
    /// **THE NAMES A VERSION MAY NOT TAKE**: the definition's own and its
    /// chapter's top-level names. Checking the unit's whole symbol table
    /// instead numbered versions by which OTHER chapters the unit cited, and
    /// a chapter's emitted text then depended on the program, which the
    /// shared chapters of roc-apps tests/ported cannot allow.
    taken: BTreeSet<Sym>,
}

fn wrap(mut pre: Pre, mut x: IrExpr) -> IrExpr {
    // `v = e; v` is `e`: a tail call stays a tail call.
    if let (Some((v, _, _)), IrExpr::Name(n, _, _)) = (pre.last(), &x) {
        if v == n {
            x = pre.pop().expect("checked").2;
        }
    }
    while let Some((n, t, v)) = pre.pop() {
        let s = v.span();
        x = IrExpr::Let(n, t, Box::new(v), Box::new(x), s);
    }
    x
}

fn flatten(e: &IrExpr) -> (&IrExpr, Vec<&IrExpr>) {
    let mut args = Vec::new();
    let mut head = e;
    while let IrExpr::Apply(f, a, _, _) = head {
        args.push(&**a);
        head = f;
    }
    args.reverse();
    (head, args)
}

/// `f a b` as nested applications, each typed by peeling `f`'s type.
fn call(f: IrExpr, args: Vec<IrExpr>, result: Ty) -> IrExpr {
    let n = args.len();
    let mut cur = f;
    let mut fty = cur.ty();
    for (i, a) in args.into_iter().enumerate() {
        let r = if i + 1 == n { result.clone() } else { peel(&fty) };
        let s = a.span();
        cur = IrExpr::Apply(Box::new(cur), Box::new(a), r.clone(), s);
        fty = r;
    }
    cur
}

fn peel(t: &Ty) -> Ty {
    match t {
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => peel(b),
        Ty::Fun(_, _, r) => (**r).clone(),
        _ => Ty::Error,
    }
}

/// A definition's type with its result, after `k` parameters, replaced.
fn with_result(t: &Ty, k: usize, new: &Ty) -> Ty {
    if k == 0 {
        return new.clone();
    }
    match t {
        Ty::ForAll(v, b) => Ty::ForAll(*v, Box::new(with_result(b, k, new))),
        Ty::ForAllEff(v, b) => Ty::ForAllEff(*v, Box::new(with_result(b, k, new))),
        Ty::Fun(p, row, r) => Ty::Fun(p.clone(), row.clone(), Box::new(with_result(r, k - 1, new))),
        other => other.clone(),
    }
}

fn result_after(t: &Ty, k: usize) -> Ty {
    let mut cur = t.clone();
    for _ in 0..k {
        cur = peel(&cur);
    }
    cur
}

fn is_list(t: &Ty) -> bool {
    matches!(t, Ty::List(_))
}

impl<'a> Rw<'a> {
    fn new(syms: &'a mut SymTab, set_at: Sym, tuple: Sym, writers: &'a BTreeMap<Sym, Writer>) -> Rw<'a> {
        Rw { syms, set_at, tuple, writers, types: BTreeMap::new(), fresh: 0, pending: Vec::new(), violation: None, taken: BTreeSet::new() }
    }

    fn mint(&mut self, base: Sym) -> Sym {
        self.fresh += 1;
        let b = self.syms.text(base).trim_start_matches('_').to_string();
        let mut k = self.fresh;
        loop {
            let cand = self.syms.intern(&format!("{b}-v{k}"));
            if self.taken.insert(cand) {
                self.fresh = k;
                return cand;
            }
            k += 1;
        }
    }

    fn tuple_ty(&self, parts: Vec<Ty>) -> Ty {
        Ty::Constructed(self.tuple, parts)
    }

    fn at(&mut self, t: &IrExpr, k: usize, ty: Ty) -> IrExpr {
        let s = t.span();
        let f = self.syms.intern(&format!("{AT}{k}"));
        let fty = Ty::Fun(Box::new(t.ty()), Default::default(), Box::new(ty.clone()));
        IrExpr::Apply(Box::new(IrExpr::Name(f, fty, s)), Box::new(t.clone()), ty, s)
    }

    fn pack(&mut self, parts: Vec<IrExpr>) -> IrExpr {
        let tys: Vec<Ty> = parts.iter().map(|p| p.ty()).collect();
        let tt = self.tuple_ty(tys.clone());
        let mut fty = tt.clone();
        for t in tys.iter().rev() {
            fty = Ty::Fun(Box::new(t.clone()), Default::default(), Box::new(fty));
        }
        let s = parts[0].span();
        call(IrExpr::Name(self.tuple, fty, s), parts, tt)
    }

    /// The version of `root` now, as an expression.
    fn version(&self, root: Sym, env: &Env, s: crate::ast::Span) -> IrExpr {
        let n = env.current.get(&root).copied().unwrap_or(root);
        IrExpr::Name(n, self.types.get(&root).cloned().unwrap_or(Ty::Error), s)
    }

    fn note_list(&mut self, n: Sym, t: &Ty) {
        if is_list(t) {
            self.types.entry(n).or_insert_with(|| t.clone());
        }
    }

    /// Record `v` as the new version of `root`.
    fn advance(&mut self, env: &mut Env, root: Sym, v: Sym) {
        if env.stored.contains(&root) && self.violation.is_none() {
            self.violation = Some(format!(
                "it writes `{}` after storing it in a record or a list, which hold the list itself",
                self.syms.text(root)
            ));
        }
        env.current.insert(root, v);
        env.root_of.insert(v, root);
        if let Some(t) = self.types.get(&root).cloned() {
            self.types.insert(v, t);
        }
    }

    /// The root a list argument names, if it names one.
    fn root_arg(&self, a: &IrExpr, env: &Env) -> Option<Sym> {
        self.alias_root(a, env)
    }

    /// **WHICH LIST AN EXPRESSION IS.** A name is its root; so is a write to
    /// it (`list-set-at x ...` answers `x`), a call to a list writer (its
    /// answer is the list it wrote), a `let` by its body, and a branch whose
    /// every arm is the same list. Anything else is a list of its own.
    fn alias_root(&self, a: &IrExpr, env: &Env) -> Option<Sym> {
        match a {
            // **ONLY A LOCAL LIST IS WRITTEN IN PLACE.** A top-level constant
            // is shared by every reader, and Codex copies it on a write:
            // `list-set-at w-direct 0 99` leaves `w-direct` as it was
            // (codex/test's const-share pins it). So a name that is not a
            // parameter or bound here names no root.
            IrExpr::Name(n, t, _) if env.bound.contains(&env.root(*n)) && (is_list(t) || self.types.contains_key(&env.root(*n))) => {
                Some(env.root(*n))
            }
            IrExpr::Let(_, _, _, body, _) => self.alias_root(body, env),
            IrExpr::If(_, x, y, _, _) => {
                let r = self.alias_root(x, env)?;
                (self.alias_root(y, env) == Some(r)).then_some(r)
            }
            IrExpr::Match(_, bs, _, _) => {
                let r = self.alias_root(&bs.first()?.body, env)?;
                bs.iter().all(|b| self.alias_root(&b.body, env) == Some(r)).then_some(r)
            }
            IrExpr::Apply(..) => {
                let (head, args) = flatten(a);
                let IrExpr::Name(f, _, _) = head else { return None };
                if *f == self.set_at && args.len() == 3 {
                    return self.alias_root(args[0], env);
                }
                let w = self.writers.get(f)?;
                if w.returns_list && args.len() == w.arity {
                    return self.alias_root(args[w.written[0]], env);
                }
                None
            }
            _ => None,
        }
    }

    /// Which parameters a definition writes, and how it answers.
    fn classify(&mut self, d: &IrDef) -> Result<Option<Writer>, String> {
        let mut env = params_env(d);
        for p in &d.params {
            self.note_list(p.name, &p.ty);
        }
        let mut pre = Pre::new();
        self.expr(&d.body, &mut env, &mut pre)?;
        let written: Vec<usize> = d
            .params
            .iter()
            .enumerate()
            .filter(|(_, p)| is_list(&p.ty) && env.current.contains_key(&p.name))
            .map(|(i, _)| i)
            .collect();
        if written.is_empty() {
            return Ok(None);
        }
        // A list writer answers the version of the one list it writes on
        // every path; `leaves_are` says so after the fact.
        let returns_list = written.len() == 1 && self.answers_list(d, d.params[written[0]].name);
        Ok(Some(Writer { arity: d.params.len(), written, returns_list }))
    }

    /// Every leaf of `d` answers the version `p` has there, or is a tail
    /// call to a list writer that writes `p`.
    fn answers_list(&mut self, d: &IrDef, p: Sym) -> bool {
        for q in &d.params {
            self.note_list(q.name, &q.ty);
        }
        let mut env = params_env(d);
        let mut ok = true;
        let r = self.tail(&d.body, &mut env, &[p], true, &mut |rw, x, env| {
            let v = rw.version(p, env, x.span());
            ok &= matches!((&x, &v), (IrExpr::Name(a, _, _), IrExpr::Name(b, _, _)) if a == b);
            Ok(x)
        });
        ok && r.is_ok()
    }

    fn rewrite(&mut self, d: &IrDef) -> Result<IrDef, String> {
        for p in &d.params {
            self.note_list(p.name, &p.ty);
        }
        let mut nd = d.clone();
        let Some(w) = self.writers.get(&d.name).cloned() else {
            let mut env = params_env(d);
            nd.body = self.block(&d.body, &mut env)?;
            return Ok(nd);
        };
        let roots: Vec<Sym> = w.written.iter().map(|&i| d.params[i].name).collect();
        let mut env = params_env(d);
        if w.returns_list {
            nd.body = self.tail(&d.body, &mut env, &roots, true, &mut |_, x, _| Ok(x))?;
            return Ok(nd);
        }
        let ans = result_after(&d.ty, d.params.len());
        let mut parts = vec![ans];
        parts.extend(roots.iter().map(|r| self.types[r].clone()));
        let tt = self.tuple_ty(parts);
        nd.ty = with_result(&d.ty, d.params.len(), &tt);
        let name = d.name;
        nd.body = self.tail(&d.body, &mut env, &roots, false, &mut |rw, x, env| rw.leaf(x, env, &roots, name))?;
        Ok(nd)
    }

    /// A tuple writer's answer at one leaf: `(x, versions...)`, or, when `x`
    /// is already a call answering exactly that, the call.
    fn leaf(&mut self, x: IrExpr, env: &Env, roots: &[Sym], _me: Sym) -> Result<IrExpr, String> {
        let mut parts = vec![x];
        for r in roots {
            let s = parts[0].span();
            parts.push(self.version(*r, env, s));
        }
        Ok(self.pack(parts))
    }

    /// A statement position: its writes stay inside.
    fn block(&mut self, e: &IrExpr, env: &mut Env) -> Result<IrExpr, String> {
        let mut pre = Pre::new();
        let x = self.expr(e, env, &mut pre)?;
        Ok(wrap(pre, x))
    }

    /// A definition's body in tail position: each leaf goes through `leaf`,
    /// with the versions at that leaf, and branches are not joined.
    fn tail(
        &mut self,
        e: &IrExpr,
        env: &mut Env,
        roots: &[Sym],
        list: bool,
        leaf: &mut dyn FnMut(&mut Self, IrExpr, &Env) -> Result<IrExpr, String>,
    ) -> Result<IrExpr, String> {
        let mut pre = Pre::new();
        let mut cur = e;
        loop {
            match cur {
                IrExpr::Let(n, t, v, body, _) => {
                    if dropped_field_write(v, self.set_at) && !mentions(body, *n) {
                        return Err(DROPPED_FIELD_WRITE.into());
                    }
                    let v2 = self.expr(v, env, &mut pre)?;
                    self.bind(*n, t, &v2, env);
                    pre.push((*n, t.clone(), v2));
                    cur = body;
                }
                IrExpr::If(c, a, b, t, s) => {
                    let c2 = self.expr(c, env, &mut pre)?;
                    let a2 = self.tail(a, &mut env.clone(), roots, list, leaf)?;
                    let b2 = self.tail(b, &mut env.clone(), roots, list, leaf)?;
                    let t2 = if a2.ty() == b2.ty() { a2.ty() } else { t.clone() };
                    return Ok(wrap(pre, IrExpr::If(Box::new(c2), Box::new(a2), Box::new(b2), t2, *s)));
                }
                IrExpr::Match(sc, bs, t, s) => {
                    let sc2 = self.expr(sc, env, &mut pre)?;
                    let mut out = Vec::new();
                    for b in bs {
                        let mut e2 = env.clone();
                        e2.bound.extend(pat_names(&b.pattern));
                        let guard = self.pure_guard(&b.guard, &e2)?;
                        let body = self.tail(&b.body, &mut e2, roots, list, leaf)?;
                        out.push(IrBranch { pattern: b.pattern.clone(), body, guard, span: b.span });
                    }
                    let t2 = out.first().map(|b| b.body.ty()).unwrap_or(t.clone());
                    return Ok(wrap(pre, IrExpr::Match(Box::new(sc2), out, t2, *s)));
                }
                _ => {
                    // A tail call to a writer whose tuple is ours is kept
                    // whole: it is the answer, and a self-call stays a loop.
                    if let Some(x) = self.tail_call(cur, env, &mut pre, roots, list)? {
                        return Ok(wrap(pre, x));
                    }
                    let x = self.expr(cur, env, &mut pre)?;
                    let x = leaf(self, x, env)?;
                    return Ok(wrap(pre, x));
                }
            }
        }
    }

    /// `cur` is a call to a writer that answers what this definition does --
    /// the same kind, writing our roots in the same order: its arguments are
    /// rewritten and the call is kept whole, so a self-call stays a loop. The
    /// arguments are tried on copies and committed only if it lines up.
    fn tail_call(&mut self, cur: &IrExpr, env: &mut Env, pre: &mut Pre, roots: &[Sym], list: bool) -> Result<Option<IrExpr>, String> {
        let (head, args) = flatten(cur);
        let IrExpr::Name(f, _, _) = head else { return Ok(None) };
        let Some(w) = self.writers.get(f).cloned() else { return Ok(None) };
        if args.len() != w.arity || w.written.len() != roots.len() || w.returns_list != list {
            return Ok(None);
        }
        let (mut env2, mut pre2) = (env.clone(), pre.clone());
        let mut xs = Vec::new();
        for a in &args {
            xs.push(self.expr(a, &mut env2, &mut pre2)?);
        }
        let xs = self.references_last(xs, &env2);
        let lines_up = w
            .written
            .iter()
            .zip(roots)
            .all(|(k, r)| matches!(&xs[*k], IrExpr::Name(n, _, _) if env2.root(*n) == *r));
        if !lines_up {
            return Ok(None);
        }
        *env = env2;
        *pre = pre2;
        let ty = if w.returns_list { cur.ty() } else { self.call_tuple_ty(cur.ty(), &w, &xs) };
        Ok(Some(call(head.clone(), xs, ty)))
    }

    fn call_tuple_ty(&self, ans: Ty, w: &Writer, xs: &[IrExpr]) -> Ty {
        let mut parts = vec![ans];
        parts.extend(w.written.iter().map(|k| xs[*k].ty()));
        self.tuple_ty(parts)
    }

    fn bind(&mut self, n: Sym, t: &Ty, v: &IrExpr, env: &mut Env) {
        env.bound.insert(n);
        self.note_list(n, t);
        // `let a = xs`, or anything that IS `xs` (`alias_root`): `a` is
        // another name for the same list, and now its current one.
        if is_list(t) {
            if let Some(r) = self.alias_root(v, env) {
                if r != n {
                    env.root_of.insert(n, r);
                    env.current.insert(r, n);
                }
            }
        }
    }

    fn pure_guard(&mut self, g: &IrExpr, env: &Env) -> Result<IrExpr, String> {
        let mut e2 = env.clone();
        let mut pre = Pre::new();
        let x = self.expr(g, &mut e2, &mut pre)?;
        if !pre.is_empty() || e2.current != env.current {
            return Err("a `when` guard writes a list".into());
        }
        Ok(x)
    }

    /// **A LIST PASSED BY NAME IS A REFERENCE.** The callee sees it as it
    /// is once every argument has been evaluated, so a bare list name among
    /// the arguments is the version after them all -- `f x (g-writes x)` hands
    /// `f` the written `x`. A read such as `list-at x 0` was evaluated in its
    /// turn and keeps the version it saw.
    fn references_last(&self, xs: Vec<IrExpr>, env: &Env) -> Vec<IrExpr> {
        xs.into_iter().map(|x| if matches!(x, IrExpr::Name(..)) { self.rename(&x, env) } else { x }).collect()
    }

    /// `references_last`, and each list stored by name is marked stored.
    fn store(&self, xs: Vec<IrExpr>, env: &mut Env) -> Vec<IrExpr> {
        let xs = self.references_last(xs, env);
        for x in &xs {
            if let IrExpr::Name(n, _, _) = x {
                let r = env.root(*n);
                if self.types.contains_key(&r) {
                    env.stored.insert(r);
                }
            }
        }
        xs
    }

    fn rename(&self, e: &IrExpr, env: &Env) -> IrExpr {
        match e {
            IrExpr::Name(n, t, s) => {
                let r = env.root(*n);
                match env.current.get(&r) {
                    Some(v) if self.types.contains_key(&r) => IrExpr::Name(*v, t.clone(), *s),
                    _ => e.clone(),
                }
            }
            _ => e.clone(),
        }
    }

    fn expr(&mut self, e: &IrExpr, env: &mut Env, pre: &mut Pre) -> Result<IrExpr, String> {
        use IrExpr as E;
        Ok(match e {
            E::IntLit(..) | E::NumLit(..) | E::TextLit(..) | E::BoolLit(..) | E::CharLit(..) => e.clone(),
            E::Name(n, t, _) => {
                self.note_list(env.root(*n), t);
                self.rename(e, env)
            }
            E::Binary(op, l, r, t, s) => {
                let l = self.expr(l, env, pre)?;
                let r = self.expr(r, env, pre)?;
                E::Binary(*op, Box::new(l), Box::new(r), t.clone(), *s)
            }
            E::Negate(x, t, s) => E::Negate(Box::new(self.expr(x, env, pre)?), t.clone(), *s),
            E::FieldAccess(x, f, t, s) => E::FieldAccess(Box::new(self.expr(x, env, pre)?), f.clone(), t.clone(), *s),
            E::FieldStore(x, f, v, t, s) => {
                let x = self.expr(x, env, pre)?;
                let v = self.expr(v, env, pre)?;
                E::FieldStore(Box::new(x), f.clone(), Box::new(v), t.clone(), *s)
            }
            // **A LIST STORED BY NAME IS THE LIST ITSELF**, as an argument
            // is: the version after every element or field is evaluated
            // (`brdix-build` stores four tables and fills them in its last
            // field). A later write to it could not reach the copy stored.
            E::List(xs, t, s) => {
                let mut out = Vec::new();
                for x in xs {
                    out.push(self.expr(x, env, pre)?);
                }
                let out = self.store(out, env);
                E::List(out, t.clone(), *s)
            }
            E::Record(n, fs, t, s) => {
                let mut vals = Vec::new();
                for f in fs {
                    vals.push(self.expr(&f.value, env, pre)?);
                }
                let vals = self.store(vals, env);
                let out = fs
                    .iter()
                    .zip(vals)
                    .map(|(f, value)| crate::ir_chapter::IrFieldVal { name: f.name, value })
                    .collect();
                E::Record(*n, out, t.clone(), *s)
            }
            E::Let(n, t, v, body, _) => {
                if dropped_field_write(v, self.set_at) && !mentions(body, *n) {
                    return Err(DROPPED_FIELD_WRITE.into());
                }
                let v2 = self.expr(v, env, pre)?;
                self.bind(*n, t, &v2, env);
                pre.push((*n, t.clone(), v2));
                self.expr(body, env, pre)?
            }
            E::If(c, a, b, t, s) => {
                let c = self.expr(c, env, pre)?;
                let (mut ea, mut eb) = (env.clone(), env.clone());
                let (mut pa, mut pb) = (Pre::new(), Pre::new());
                let xa = self.expr(a, &mut ea, &mut pa)?;
                let xb = self.expr(b, &mut eb, &mut pb)?;
                let arms = vec![(pa, xa, ea), (pb, xb, eb)];
                let (mut out, ty) = self.join(arms, t.clone(), env, pre)?;
                let (ob, oa) = (out.pop().expect("two"), out.pop().expect("two"));
                self.finish_join(E::If(Box::new(c), Box::new(oa), Box::new(ob), ty.clone(), *s), ty, env, pre)
            }
            E::Match(sc, bs, t, s) => {
                let sc = self.expr(sc, env, pre)?;
                let mut arms = Vec::new();
                let mut guards = Vec::new();
                for b in bs {
                    let mut eb = env.clone();
                    eb.bound.extend(pat_names(&b.pattern));
                    guards.push(self.pure_guard(&b.guard, &eb)?);
                    let mut pb = Pre::new();
                    let xb = self.expr(&b.body, &mut eb, &mut pb)?;
                    arms.push((pb, xb, eb));
                }
                let (bodies, ty) = self.join(arms, t.clone(), env, pre)?;
                let out: Vec<IrBranch> = bs
                    .iter()
                    .zip(bodies)
                    .zip(guards)
                    .map(|((b, body), guard)| IrBranch { pattern: b.pattern.clone(), body, guard, span: b.span })
                    .collect();
                self.finish_join(E::Match(Box::new(sc), out, ty.clone(), *s), ty, env, pre)
            }
            E::Lambda(ps, body, t, s) => {
                let mut inner = env.clone();
                inner.bound.extend(ps.iter().map(|p| p.name));
                let b = self.block(body, &mut inner)?;
                if inner.current.iter().any(|(r, v)| env.current.get(r).copied().unwrap_or(*r) != *v) {
                    return Err("a lambda writes a list it captured".into());
                }
                E::Lambda(ps.clone(), Box::new(b), t.clone(), *s)
            }
            E::Act(stmts, t, s) => {
                let mut out = Vec::new();
                let before = env.current.clone();
                for (i, st) in stmts.iter().enumerate() {
                    let mut inner = Env { current: before.clone(), ..env.clone() };
                    let (st2, touched) = match st {
                        IrActStmt::Bind(n, bt, v, sp) => {
                            let v2 = self.block(v, &mut inner)?;
                            (IrActStmt::Bind(*n, bt.clone(), v2, *sp), inner.current != before)
                        }
                        IrActStmt::Exec(v, sp) => {
                            if dropped_field_write(v, self.set_at) {
                                return Err(DROPPED_FIELD_WRITE.into());
                            }
                            let v2 = self.block(v, &mut inner)?;
                            (IrActStmt::Exec(v2, *sp), inner.current != before)
                        }
                    };
                    if touched {
                        let later_reads = stmts[i + 1..].iter().any(|l| {
                            let mut hit = false;
                            let v = match l {
                                IrActStmt::Bind(_, _, v, _) | IrActStmt::Exec(v, _) => v,
                            };
                            v.walk(&mut |x| {
                                if let E::Name(n, _, _) = x {
                                    if inner.current.contains_key(&env.root(*n)) {
                                        hit = true;
                                    }
                                }
                            });
                            hit
                        });
                        if later_reads {
                            return Err("an `act` statement writes a list a later statement reads".into());
                        }
                    }
                    out.push(st2);
                }
                E::Act(out, t.clone(), *s)
            }
            E::Handle(..) | E::WithTimeout(..) | E::Try(..) => {
                let mut hit = false;
                e.walk(&mut |x| {
                    if let E::Name(n, _, _) = x {
                        if *n == self.set_at || self.writers.contains_key(n) {
                            hit = true;
                        }
                    }
                });
                if hit {
                    return Err("a list is written under `handle`, `with-timeout` or `try`".into());
                }
                e.clone()
            }
            E::Apply(..) => self.apply(e, env, pre)?,
        })
    }

    fn apply(&mut self, e: &IrExpr, env: &mut Env, pre: &mut Pre) -> Result<IrExpr, String> {
        let (head, args) = flatten(e);
        let IrExpr::Name(f, _, _) = head else {
            let h = self.expr(head, env, pre)?;
            let mut xs = Vec::new();
            for a in &args {
                xs.push(self.expr(a, env, pre)?);
            }
            return Ok(call(h, xs, e.ty()));
        };
        let f = *f;
        // The written argument's ROOT is read off the argument before it is
        // renamed to its current version.
        let roots: Vec<Option<Sym>> = args.iter().map(|a| self.root_arg(a, env)).collect();
        let mut xs = Vec::new();
        for a in &args {
            xs.push(self.expr(a, env, pre)?);
        }
        let mut xs = self.references_last(xs, env);
        if f == self.set_at && xs.len() == 3 {
            let c = call(head.clone(), xs, e.ty());
            if let Some(r) = roots[0] {
                self.note_list(r, &e.ty());
                let v = self.mint(r);
                pre.push((v, e.ty(), c));
                self.advance(env, r, v);
                return Ok(IrExpr::Name(v, e.ty(), e.span()));
            }
            return Ok(c);
        }
        if self.syms.text(f).starts_with(|c: char| c.is_ascii_uppercase()) {
            let xs = self.store(xs, env);
            return Ok(call(head.clone(), xs, e.ty()));
        }
        if let Some(w) = self.writers.get(&f).cloned() {
            if xs.len() < w.arity {
                return Err(format!("`{}`, which writes a list it is given, is used as a value", self.syms.text(f)));
            }
            let extra = xs.split_off(w.arity);
            let x = self.finish_call(head, xs, result_after(&head.ty(), w.arity), &w, &roots, env, pre);

            return Ok(if extra.is_empty() { x } else { call(x, extra, e.ty()) });
        }
        Ok(call(head.clone(), xs, e.ty()))
    }

    /// A saturated call to a writer: bound, its versions advanced, and its
    /// answer returned.
    #[allow(clippy::too_many_arguments)]
    fn finish_call(
        &mut self,
        head: &IrExpr,
        xs: Vec<IrExpr>,
        ans: Ty,
        w: &Writer,
        roots: &[Option<Sym>],
        env: &mut Env,
        pre: &mut Pre,
    ) -> IrExpr {
        let s = head.span();
        let base = match head {
            IrExpr::Name(n, _, _) => *n,
            _ => self.tuple,
        };
        if w.returns_list {
            let c = call(head.clone(), xs, ans.clone());
            let v = self.mint(base);
            pre.push((v, ans.clone(), c));
            if let Some(r) = roots.get(w.written[0]).copied().flatten() {
                self.advance(env, r, v);
            }
            return IrExpr::Name(v, ans, s);
        }
        let tt = self.call_tuple_ty(ans.clone(), w, &xs);
        let list_tys: Vec<Ty> = w.written.iter().map(|k| xs[*k].ty()).collect();
        let c = call(head.clone(), xs, tt.clone());
        let t = self.mint(base);
        pre.push((t, tt.clone(), c));
        let tn = IrExpr::Name(t, tt, s);
        for (j, k) in w.written.iter().enumerate() {
            if let Some(r) = roots.get(*k).copied().flatten() {
                let v = self.mint(r);
                let p = self.at(&tn, j + 1, list_tys[j].clone());
                pre.push((v, list_tys[j].clone(), p));
                self.advance(env, r, v);
            }
        }
        self.at(&tn, 0, ans)
    }

    /// Arms that left lists at different versions answer `(value, lists)`,
    /// in a root order shared by every arm; arms that agree are left alone.
    fn join(&mut self, arms: Vec<(Pre, IrExpr, Env)>, ty: Ty, env: &Env, _pre: &Pre) -> Result<(Vec<IrExpr>, Ty), String> {
        let mut differ: BTreeSet<Sym> = BTreeSet::new();
        let at = |e: &Env, r: Sym| e.current.get(&r).copied().unwrap_or(r);
        let all_roots: BTreeSet<Sym> = arms.iter().flat_map(|(_, _, e)| e.current.keys().copied()).collect();
        for r in all_roots.into_iter().filter(|r| env.bound.contains(r)) {
            let first = at(&arms[0].2, r);
            if arms.iter().any(|(_, _, e)| at(e, r) != first) || first != at(env, r) {
                differ.insert(r);
            }
        }
        self.pending = differ.iter().copied().collect();
        if differ.is_empty() {
            return Ok((arms.into_iter().map(|(p, x, _)| wrap(p, x)).collect(), ty));
        }
        let roots: Vec<Sym> = differ.into_iter().collect();
        let mut parts = vec![ty];
        parts.extend(roots.iter().map(|r| self.types.get(r).cloned().unwrap_or(Ty::Error)));
        let tt = self.tuple_ty(parts);
        let mut out = Vec::new();
        for (p, x, e) in arms {
            let mut ps = vec![x];
            for r in &roots {
                let s = ps[0].span();
                ps.push(self.version(*r, &e, s));
            }
            let packed = self.pack(ps);
            out.push(wrap(p, packed));
        }
        Ok((out, tt))
    }

    /// After a joined branch: bind it, advance the lists it answered, and
    /// give back its value.
    fn finish_join(&mut self, branch: IrExpr, ty: Ty, env: &mut Env, pre: &mut Pre) -> IrExpr {
        let roots = std::mem::take(&mut self.pending);
        if roots.is_empty() {
            return branch;
        }
        let Ty::Constructed(_, parts) = ty.clone() else { return branch };
        let s = branch.span();
        let t = self.mint(self.tuple);
        pre.push((t, ty.clone(), branch));
        let tn = IrExpr::Name(t, ty, s);
        for (j, r) in roots.iter().enumerate() {
            let v = self.mint(*r);
            let p = self.at(&tn, j + 1, parts[j + 1].clone());
            pre.push((v, parts[j + 1].clone(), p));
            self.advance(env, *r, v);
        }
        self.at(&tn, 0, parts[0].clone())
    }
}

fn params_env(d: &IrDef) -> Env {
    Env { bound: d.params.iter().map(|p| p.name).collect(), ..Env::default() }
}

fn pat_names(p: &crate::ir_chapter::IrPat) -> Vec<Sym> {
    let mut out = Vec::new();
    crate::lambda_lifting::pat_names(p, &mut out);
    out
}
