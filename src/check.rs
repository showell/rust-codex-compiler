//! The CHECK layer: semantic types, and the state the checker threads.
//!
//! This is rung five, and it is deliberately being built BEFORE any more of
//! rung six. `ir.rs` reached 8 of 1,012 golds and then stalled against a
//! refusal histogram that was 480 effect rows, 155 names with no type and 21
//! empty list literals -- every one of them this layer's output. Adding node
//! forms to lowering was working around an absent checker.
//!
//! ## The oracle, and why it is a demanding one
//!
//! `$CODEX_GOLDS/rungs/check.truth` is what upstream's own checker prints for
//! `fib`:
//!
//! ```text
//! --- check ---
//! check-errors 0
//! type-bindings 3
//! tb fib fn
//! tb double fn
//! tb opening eff
//! .
//! substitutions 8
//! next-id 8
//! expr-types 11
//! ---
//! ```
//!
//! The last three are unification INTERNALS. Matching `next-id 8` means
//! allocating fresh type variables in the same order and the same number as
//! upstream does -- not merely reaching the same conclusion. That is a much
//! sharper oracle than "the types look right", and it is why this file mirrors
//! `Types/CodexType.codex` constructor for constructor rather than inventing a
//! representation that would be easier to write and impossible to compare.
//!
//! ## Order of construction
//!
//! The bindings and their kinds come from DECLARED types alone and can be got
//! right immediately. The three counts need inference and will not match until
//! it does. Reporting the section with the counts wrong is the point: the diff
//! against the gold says how far off, every run, instead of nothing until the
//! end.

use crate::symbol::{Sym, SymTab};
use crate::ast::Name;

/// Upstream's `CodexType`, `Types/CodexType.codex`. Mirrored constructor for
/// constructor: a representation that cannot express what theirs expresses
/// cannot be compared against theirs.
#[derive(Clone, Debug, PartialEq)]
pub enum Ty {
    Integer(i64, i64, Overflow),
    Real(RealWidth, RealMode),
    Text,
    Boolean,
    Char,
    Void,
    Nothing,
    Error,
    NoExpect,
    Fun(Box<Ty>, EffectRow, Box<Ty>),
    List(Box<Ty>),
    LinkedList(Box<Ty>),
    Var(u32),
    ForAll(u32, Box<Ty>),
    Sum(Name, Vec<Ty>),
    Record(Name, Vec<Ty>),
    Constructed(Name, Vec<Ty>),
    Effectful(Vec<Name>, Vec<String>, Box<Ty>),
    Proof,
    PropEq(Box<Ty>, Box<Ty>),
    Unit(Name, Box<Ty>),
    Vector(i64, Box<Ty>),
    VectorMask(i64),
    TypeCon(Name),
    TypeApply(Box<Ty>, Box<Ty>),
    /// The quantified id is a ROW id, and row ids share `EffectRow`'s
    /// signed spelling: -1 is "no tail", not row 4,294,967,295.
    ForAllEff(i32, Box<Ty>),
    Linear(Box<Ty>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Overflow {
    Error,
    Wrapping,
    Clamping,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealWidth {
    F64,
    F32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealMode {
    /// `RmDefault`. The mode a bare `Real` carries, and the one that prints as
    /// `real` rather than `real-trapping` -- a fourth mode of our own read as
    /// trapping and would have spelled every Real on the wire wrong.
    Default,
    Trapping,
    Saturating,
}

/// An effect row. Empty is the common case and prints as nothing.
///
/// **THE ID IS `-1` UNTIL SOMETHING MINTS ONE.** `empty-row`
/// (CodexType.codex:74) is `tail-id = -1`, and `open-spine-rows` mints only
/// where the tail is absent -- so a default of 0 is a row that already has an
/// id, nothing would ever be minted, and every row the wire spells would be
/// row zero.
#[derive(Clone, Debug, PartialEq)]
pub struct EffectRow {
    pub labels: Vec<(String, String)>,
    pub tail: String,
    pub id: i32,
}

impl Default for EffectRow {
    fn default() -> EffectRow {
        EffectRow { labels: Vec::new(), tail: String::new(), id: -1 }
    }
}

/// The name `type-kind` prints for a binding, from the check harness:
/// `CheckHarness.codex` lines 44-62. These strings are compared against the
/// gold, so they are not ours to choose.
pub fn type_kind(syms: &SymTab, t: &Ty) -> String {
    match t {
        Ty::Integer(..) => "int".into(),
        Ty::Text => "text".into(),
        Ty::Boolean => "bool".into(),
        Ty::Char => "char".into(),
        Ty::List(_) => "list".into(),
        Ty::Fun(..) => "fn".into(),
        Ty::Effectful(..) => "eff".into(),
        Ty::ForAll(..) => "forall".into(),
        Ty::ForAllEff(..) => "foralleff".into(),
        Ty::Var(_) => "tvar".into(),
        Ty::Sum(n, _) => format!("sum:{}", syms.text(*n)),
        Ty::Record(n, _) => format!("rec:{}", syms.text(*n)),
        Ty::Constructed(n, _) => format!("con:{}", syms.text(*n)),
        Ty::TypeCon(n) => format!("tycon:{}", syms.text(*n)),
        _ => "other".into(),
    }
}

/// One name bound to one type, in the order the checker registered it.
#[derive(Clone, Debug)]
pub struct Binding {
    pub name: Sym,
    pub ty: Ty,
}

/// The state the checker threads, and the three numbers the gold grades.
///
/// `next_id` is NOT `substitutions.len()`, and the gold shows them equal at 8
/// only by coincidence on this subject. They count different things: how many
/// fresh variables were minted, and how many of them were resolved.
#[derive(Debug)]
pub struct UnifyState {
    /// A SLOT ARRAY INDEXED BY VARIABLE ID, not a list of pairs: upstream's is
    /// `List CodexType` and slot `i` holds what variable `i` resolved to,
    /// initialised to `TypeVar i` -- itself. `resolve` (Unifier.codex:101)
    /// reads `list-at substitutions id`, so the index IS the identity, and a
    /// pair list would answer the same questions with a different length.
    pub substitutions: Vec<Ty>,
    pub next_id: u32,
    /// Row ids are a SEPARATE counter from type-variable ids. `next-id` in the
    /// gold counts only the latter, so minting a row must not advance it.
    pub next_row_id: i32,
    /// **KEYED BY SPAN, WHICH IS HOW LOWERING FINDS THEM.** Upstream's
    /// `expr-types` is `List ExprTypeEntry` with a packed span for a key
    /// (Unifier.codex:134), and `lower-chapter` reads it back with
    /// `lookup-expr-type (ctx.ust) sp`. A map keyed by NAME cannot answer that
    /// question at all: `fib` appears twice in its own body and the wire
    /// spells a different row id at each.
    /// **ROWS RESOLVE THROUGH THEIR OWN SLOT ARRAY**, the way types resolve
    /// through `substitutions`. `add-row-subst` binds an open row's tail to
    /// another row, and `resolve-row` follows it -- without which two rows
    /// already equated by an earlier unification look distinct and mint again.
    pub row_subst: Vec<EffectRow>,
    pub expr_types: Vec<(u64, Ty)>,
    pub errors: usize,
    /// Applications this unifier could not decide. **NOT `errors`:** a `false`
    /// out of a partial unifier is our ignorance and not the program's fault,
    /// and `check-errors` is graded against the oracle. Counted so the gap is
    /// visible rather than swallowed.
    pub unify_gaps: usize,
}

/// `expr-type-key` (Unifier.codex:133): file id in the top 16 bits, start
/// offset in the middle 32, length capped at 65535 in the low 16 -- an exact
/// 64-bit fit. Upstream's previous decimal packing aliased distinct spans
/// past a megabyte of source, which is a trap worth not re-digging.
///
/// One file here, so the file id is the constant 1. It cannot be 0: upstream
/// calls file id 0 SYNTHETIC and records nothing for it.
pub fn expr_type_key(sp: crate::ast::Span) -> u64 {
    (1u64 << 48) + (sp.offset as u64) * 65536 + (sp.len.min(65535) as u64)
}

impl Default for UnifyState {
    /// `empty-unification-state` (Unifier.codex:41) is NOT empty. It starts
    /// with two substitution slots and `next-id = 2`, so every id we hand out
    /// is two higher than a counter starting at zero -- and those ids are
    /// PRINTED into the IR as `(tvar 41)`, so starting at zero is not a
    /// harmless offset.
    fn default() -> UnifyState {
        UnifyState {
            substitutions: vec![Ty::Var(0), Ty::Var(1)],
            next_id: 2,
            next_row_id: 0,
            row_subst: Vec::new(),
            expr_types: Vec::new(),
            errors: 0,
            unify_gaps: 0,
        }
    }
}

impl UnifyState {
    /// Mint a fresh type variable. ORDER MATTERS: the gold records how many
    /// were minted, so a checker that reaches the same answer by a different
    /// route reports a different number and is wrong here.
    pub fn fresh(&mut self) -> Ty {
        // `advance-id` pushes a SLOT and advances the id together, so
        // `substitutions.len()` and `next_id` move in lockstep and the gold
        // reports both as 8 for the same reason.
        let id = self.next_id;
        self.substitutions.push(Ty::Var(id));
        self.next_id += 1;
        Ty::Var(id)
    }

    /// A fresh effect-row id, on its own counter.
    pub fn fresh_row(&mut self) -> i32 {
        let id = self.next_row_id;
        // A slot holding itself is an unbound row variable, exactly as a
        // substitution slot holding `Var(i)` is an unbound type variable.
        self.row_subst.push(EffectRow { id, ..Default::default() });
        self.next_row_id += 1;
        id
    }

    /// `resolve-row`: follow an open row's tail to what it was bound to.
    pub fn resolve_row(&self, r: &EffectRow) -> EffectRow {
        let mut cur = r.clone();
        for _ in 0..10_000 {
            if cur.id < 0 {
                return cur;
            }
            match self.row_subst.get(cur.id as usize) {
                Some(slot) if slot.id != cur.id || !slot.labels.is_empty() => {
                    // The labels a row picked up on the way are kept: an open
                    // row bound to a closed one carries that one's effects.
                    let mut next = slot.clone();
                    for l in &cur.labels {
                        if !next.labels.contains(l) {
                            next.labels.push(l.clone());
                        }
                    }
                    if next.id == cur.id {
                        return next;
                    }
                    cur = next;
                }
                _ => return cur,
            }
        }
        cur
    }

    fn add_row_subst(&mut self, id: i32, r: EffectRow) {
        if let Some(slot) = self.row_subst.get_mut(id as usize) {
            *slot = r;
        }
    }

    /// `unify-row` (Unifier.codex:344). **THE ONLY ARM THAT MINTS IS
    /// OPEN-MEETS-OPEN WITH DIFFERENT TAILS**, which equates the two variables
    /// through a third: two closed rows agree or fail, and an open row meeting
    /// a closed one is simply bound to it.
    ///
    /// That one mint is what a row-parametric signature costs beyond its
    /// registration and its own instantiation, and it is what an application
    /// costs beyond its call row. Not unifying rows at all left both of those
    /// unaccounted, so every `[e]` in the depot came out one row low per use.
    pub fn unify_row(&mut self, r1: &EffectRow, r2: &EffectRow) -> bool {
        let a = self.resolve_row(r1);
        let b = self.resolve_row(r2);
        if a.labels == b.labels && a.tail == b.tail && a.id == b.id {
            return true;
        }
        let only1: Vec<_> = a.labels.iter().filter(|l| !b.labels.contains(l)).cloned().collect();
        let only2: Vec<_> = b.labels.iter().filter(|l| !a.labels.contains(l)).cloned().collect();
        match (a.id >= 0, b.id >= 0) {
            // Both closed: they agree or they do not, and neither mints.
            (false, false) => only1.is_empty() && only2.is_empty(),
            (true, false) => {
                if !only1.is_empty() {
                    return false;
                }
                self.add_row_subst(a.id, EffectRow { labels: only2, ..Default::default() });
                true
            }
            (false, true) => {
                if !only2.is_empty() {
                    return false;
                }
                self.add_row_subst(b.id, EffectRow { labels: only1, ..Default::default() });
                true
            }
            (true, true) if a.id == b.id => only1.is_empty() && only2.is_empty(),
            (true, true) => {
                let t3 = self.fresh_row();
                self.add_row_subst(a.id, EffectRow { labels: only2, tail: String::new(), id: t3 });
                self.add_row_subst(b.id, EffectRow { labels: only1, tail: String::new(), id: t3 });
                true
            }
        }
    }

    /// `record-expr-type` (Unifier.codex:148). Appended unsorted, because a
    /// record is on the hot path and a sort is not.
    pub fn record_expr_type(&mut self, sp: crate::ast::Span, t: Ty) {
        self.expr_types.push((expr_type_key(sp), t));
    }

    /// Sorted ONCE at the check/lower boundary, where upstream sorts it
    /// (`TypeChecker.codex:2343`), so the lookups lowering does are a binary
    /// search rather than a scan per node.
    pub fn sort_expr_types(&mut self) {
        self.expr_types.sort_by_key(|(k, _)| *k);
    }

    /// `lookup-expr-type`. Call `sort_expr_types` first -- unsorted, this
    /// answers None for entries that are present, which is the silent half of
    /// a wrong answer.
    pub fn expr_type_at(&self, sp: crate::ast::Span) -> Option<&Ty> {
        let k = expr_type_key(sp);
        let i = self.expr_types.partition_point(|(e, _)| *e < k);
        self.expr_types.get(i).filter(|(e, _)| *e == k).map(|(_, t)| t)
    }

    /// `instantiate-type` (TypeCheckerInference.codex:214): one fresh variable
    /// per `forall` and one fresh ROW per `foralleff`, substituted for the
    /// BOUND id alone. Replacing every variable in the body instead is the
    /// same type with different ids the moment a type quantifies two.
    pub fn instantiate(&mut self, t: &Ty) -> Ty {
        self.instantiate_inner(t, 1)
    }

    fn instantiate_inner(&mut self, t: &Ty, _unused: usize) -> Ty {
        match t {
            Ty::ForAll(id, body) => {
                let fr = self.fresh();
                let b = subst_type_var(body, *id, &fr);
                self.instantiate_inner(&b, 0)
            }
            Ty::ForAllEff(id, body) => {
                let r = self.fresh_row();
                let b = subst_row_var(body, *id, r);
                self.instantiate_inner(&b, 0)
            }
            other => other.clone(),
        }
    }

    /// `open-spine-rows` (TypeCheckerInference.codex:188): **THE RESULT FIRST,
    /// THEN THE ARROW HOLDING IT.** One row per arrow in the result chain, so
    /// a two-parameter function costs two rows at every reference; the
    /// innermost arrow takes the lower id. A row that already carries a tail
    /// keeps it.
    ///
    /// The PARAMETER is not walked into. `double-it : (Integer -> Integer) ->
    /// Integer` mints one row, not two -- measured on `codexcheck`, and the
    /// difference is the whole reason this recurses on `r` alone.
    pub fn open_spine_rows(&mut self, t: &Ty) -> Ty {
        match t {
            Ty::Fun(p, row, r) => {
                let r2 = self.open_spine_rows(r);
                let row2 = if row.id < 0 && row.tail.is_empty() {
                    EffectRow { id: self.fresh_row(), ..row.clone() }
                } else {
                    row.clone()
                };
                Ty::Fun(p.clone(), row2, Box::new(r2))
            }
            other => other.clone(),
        }
    }

    /// Follow a variable to what it was bound to, one level of structure.
    /// `resolve` (Unifier.codex:101) reads `list-at substitutions id`, and a
    /// slot holding itself is an unbound variable.
    pub fn resolve(&self, t: &Ty) -> Ty {
        let mut cur = t.clone();
        // A cycle would be an occurs-check failure upstream refuses to build;
        // the bound is here so a bug in this file cannot hang a compile.
        for _ in 0..10_000 {
            let Ty::Var(i) = cur else { return cur };
            match self.substitutions.get(i as usize) {
                Some(slot) if *slot != Ty::Var(i) => cur = slot.clone(),
                _ => return cur,
            }
        }
        cur
    }

    /// `deep-resolve`: every variable in the type, not just the outermost.
    /// This is what lowering prints, so a half-resolved type reaches the wire
    /// as `(tvar 4)` where the oracle spells `int-default`.
    pub fn deep_resolve(&self, t: &Ty) -> Ty {
        let t = self.resolve(t);
        match t {
            Ty::Fun(p, row, r) => Ty::Fun(
                Box::new(self.deep_resolve(&p)),
                row,
                Box::new(self.deep_resolve(&r)),
            ),
            Ty::List(e) => Ty::List(Box::new(self.deep_resolve(&e))),
            Ty::LinkedList(e) => Ty::LinkedList(Box::new(self.deep_resolve(&e))),
            Ty::Linear(e) => Ty::Linear(Box::new(self.deep_resolve(&e))),
            Ty::Effectful(e, sc, r) => {
                Ty::Effectful(e, sc, Box::new(self.deep_resolve(&r)))
            }
            Ty::Sum(n, a) => Ty::Sum(n, a.iter().map(|x| self.deep_resolve(x)).collect()),
            Ty::Record(n, a) => Ty::Record(n, a.iter().map(|x| self.deep_resolve(x)).collect()),
            Ty::Constructed(n, a) => {
                Ty::Constructed(n, a.iter().map(|x| self.deep_resolve(x)).collect())
            }
            Ty::Vector(n, e) => Ty::Vector(n, Box::new(self.deep_resolve(&e))),
            Ty::Unit(n, e) => Ty::Unit(n, Box::new(self.deep_resolve(&e))),
            other => other,
        }
    }

    fn bind_var(&mut self, id: u32, t: Ty) {
        if let Some(slot) = self.substitutions.get_mut(id as usize) {
            *slot = t;
        }
    }

    /// Enough of `unify` to bind what an application decided, which is the
    /// whole of what an inferred type is made of: `show` reaches the wire as
    /// `(fn int-default text)` only because its instantiated variable met the
    /// argument here.
    ///
    pub fn unify(&mut self, a: &Ty, b: &Ty) -> bool {
        let a = self.resolve(a);
        let b = self.resolve(b);
        match (&a, &b) {
            // An error type has already been reported once. Unifying against
            // it succeeds so one unknown name does not cascade.
            (Ty::Error, _) | (_, Ty::Error) => true,
            (Ty::Var(i), Ty::Var(j)) if i == j => true,
            (Ty::Var(i), _) => {
                self.bind_var(*i, b.clone());
                true
            }
            (_, Ty::Var(j)) => {
                self.bind_var(*j, a.clone());
                true
            }
            (Ty::Fun(p1, row1, r1), Ty::Fun(p2, row2, r2)) => {
                let (p1, r1, p2, r2) = (p1.clone(), r1.clone(), p2.clone(), r2.clone());
                let (row1, row2) = (row1.clone(), row2.clone());
                let l = self.unify(&p1, &p2);
                let rw = self.unify_row(&row1, &row2);
                let r = self.unify(&r1, &r2);
                l && rw && r
            }
            (Ty::List(x), Ty::List(y)) => {
                let (x, y) = (x.clone(), y.clone());
                self.unify(&x, &y)
            }
            _ => a == b,
        }
    }
}

/// Replace one BOUND type variable, by id. Everything else is carried through
/// unchanged, including a nested `forall` that binds a different id.
fn subst_type_var(t: &Ty, id: u32, with: &Ty) -> Ty {
    match t {
        Ty::Var(i) if *i == id => with.clone(),
        Ty::Fun(p, row, r) => Ty::Fun(
            Box::new(subst_type_var(p, id, with)),
            row.clone(),
            Box::new(subst_type_var(r, id, with)),
        ),
        Ty::List(e) => Ty::List(Box::new(subst_type_var(e, id, with))),
        Ty::LinkedList(e) => Ty::LinkedList(Box::new(subst_type_var(e, id, with))),
        Ty::Linear(e) => Ty::Linear(Box::new(subst_type_var(e, id, with))),
        Ty::Effectful(e, sc, r) => Ty::Effectful(
            e.clone(),
            sc.clone(),
            Box::new(subst_type_var(r, id, with)),
        ),
        Ty::Sum(n, a) => {
            Ty::Sum(n.clone(), a.iter().map(|x| subst_type_var(x, id, with)).collect())
        }
        Ty::Record(n, a) => {
            Ty::Record(n.clone(), a.iter().map(|x| subst_type_var(x, id, with)).collect())
        }
        Ty::Constructed(n, a) => Ty::Constructed(
            n.clone(),
            a.iter().map(|x| subst_type_var(x, id, with)).collect(),
        ),
        Ty::Vector(n, e) => Ty::Vector(*n, Box::new(subst_type_var(e, id, with))),
        Ty::Unit(n, e) => Ty::Unit(n.clone(), Box::new(subst_type_var(e, id, with))),
        // A quantifier that binds the SAME id shadows it, and the body below
        // it is not ours to touch.
        Ty::ForAll(i, _) if *i == id => t.clone(),
        Ty::ForAll(i, b) => Ty::ForAll(*i, Box::new(subst_type_var(b, id, with))),
        Ty::ForAllEff(i, b) => Ty::ForAllEff(*i, Box::new(subst_type_var(b, id, with))),
        other => other.clone(),
    }
}

/// Replace one BOUND row variable, by id -- `subst-row-var`, the row half of
/// the same walk.
fn subst_row_var(t: &Ty, id: i32, with: i32) -> Ty {
    match t {
        Ty::Fun(p, row, r) => {
            // **KEYED ON THE ID, AND THE TAIL NAME SURVIVES.** `subst-row-var`
            // (TypeCheckerInference.codex:251) matches `row.tail-id == old-id`
            // and calls `row-with-tail-id`, which rewrites the id and keeps the
            // name. Requiring an empty tail here meant the substitution never
            // fired on the row variables it exists for.
            let row2 = if row.id == id {
                EffectRow { id: with, ..row.clone() }
            } else {
                row.clone()
            };
            Ty::Fun(
                Box::new(subst_row_var(p, id, with)),
                row2,
                Box::new(subst_row_var(r, id, with)),
            )
        }
        Ty::List(e) => Ty::List(Box::new(subst_row_var(e, id, with))),
        Ty::Effectful(e, sc, r) => {
            Ty::Effectful(e.clone(), sc.clone(), Box::new(subst_row_var(r, id, with)))
        }
        Ty::ForAllEff(i, _) if *i == id => t.clone(),
        Ty::ForAll(i, b) => Ty::ForAll(*i, Box::new(subst_row_var(b, id, with))),
        other => other.clone(),
    }
}

/// A DECLARED type expression, as the checker's semantic type.
///
/// Declared only: this is the half that needs no inference, and it is enough to
/// settle every binding the gold names. What it cannot do is invent a type for
/// a definition that declares none -- that is inference, and it returns None
/// here rather than a plausible stand-in.
pub fn resolve_declared(syms: &SymTab, t: &crate::ast::TypeExpr) -> Option<Ty> {
    use crate::ast::TypeExpr as T;
    Some(match t {
        T::Named(n, _) => match syms.text(*n) {
            "Integer" => Ty::Integer(i64::MIN, i64::MAX, Overflow::Error),
            "Text" => Ty::Text,
            "Boolean" => Ty::Boolean,
            "Char" => Ty::Char,
            "Nothing" => Ty::Nothing,
            "Real" => Ty::Real(RealWidth::F64, RealMode::Default),
            _ => Ty::TypeCon(n.clone()),
        },
        // **AN EFFECT ANNOTATION ON AN ARROW'S RESULT IS THE ARROW'S ROW**,
        // and the result is what is left underneath. `resolve-type-expr`
        // (TypeChecker.codex:14) does exactly this, and the builtin table
        // agrees: `print-line-uni : Text -> [Console] Nothing` is
        // `(fn text (row Console.Write) nothing)` and not a function returning
        // an effectful type.
        //
        // Folding it wrong cost every `[e]` in the depot: a row variable that
        // stays inside an `EffectfulTy` is not on an arrow, so
        // `parameterize-type` never sees a tail to mint an id for.
        T::Fun(a, b, _) => {
            let arg = Box::new(resolve_declared(syms, a)?);
            match &**b {
                T::Effect(effs, scopes, tail, inner, _) => Ty::Fun(
                    arg,
                    EffectRow {
                        labels: effs
                            .iter()
                            .enumerate()
                            .map(|(i, e)| {
                                (
                                    syms.text(*e).to_string(),
                                    scopes.get(i).cloned().unwrap_or_default(),
                                )
                            })
                            .collect(),
                        tail: tail.first().map_or(String::new(), |t| syms.text(*t).to_string()),
                        id: -1,
                    },
                    Box::new(resolve_declared(syms, inner)?),
                ),
                _ => Ty::Fun(arg, EffectRow::default(), Box::new(resolve_declared(syms, b)?)),
            }
        }
        // `[Console] Nothing` -- the effect row is what makes `opening` print
        // as `eff` rather than as its result type.
        // A standalone effect annotation stays an `EffectfulTy`, and its TAIL
        // is dropped -- `resolve-type-expr`'s own arm passes only effs and
        // scopes through.
        T::Effect(effs, scopes, _, inner, _) => Ty::Effectful(
            effs.clone(),
            scopes.clone(),
            Box::new(resolve_declared(syms, inner)?),
        ),
        // **A TYPE APPLICATION IS CURRIED, ONE ARGUMENT PER NODE.**
        // `apply-atype-args` (Ast/Desugarer.codex:343) wraps a fresh `AAppType`
        // around the base for each argument, so `(a, b)` is
        // `App(App(Tup2, [a]), [b])` and not `App(Tup2, [a, b])`. Matching only
        // a `Named` head therefore saw NOTHING with more than one argument:
        // every tuple in the depot resolved to nothing, `register_defs` minted
        // a bare variable in its place, and the signature lost both parameters.
        T::App(..) => {
            let (head, args) = flatten_app(t);
            let T::Named(n, _) = head else { return None };
            let rendered: Vec<Ty> =
                args.iter().map(|a| resolve_declared(syms, a)).collect::<Option<_>>()?;
            match (syms.text(*n), rendered.as_slice()) {
                ("List", [only]) => Ty::List(Box::new(only.clone())),
                _ => Ty::Constructed(*n, rendered),
            }
        }
        T::Linear(inner, _) => Ty::Linear(Box::new(resolve_declared(syms, inner)?)),
        _ => return None,
    })
}

/// `strip-forall-ty`: the body of a quantifier chain, with its ORIGINAL ids.
/// Not an instantiation -- the point of the tie is to meet the signature's own
/// variables, not fresh ones.
fn strip_forall(t: &Ty) -> Ty {
    match t {
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => strip_forall(b),
        other => other.clone(),
    }
}

/// The head of an application spine and every argument, left to right.
fn flatten_app(t: &crate::ast::TypeExpr) -> (&crate::ast::TypeExpr, Vec<&crate::ast::TypeExpr>) {
    use crate::ast::TypeExpr as T;
    let mut args: Vec<&T> = Vec::new();
    let mut cur = t;
    while let T::App(head, a, _) = cur {
        // Reversed at the end: the spine is walked outside in, so the LAST
        // argument is met first.
        args.extend(a.iter().rev());
        cur = head;
    }
    args.reverse();
    (cur, args)
}

/// Register every definition's declared type, in source order.
///
/// Upstream's `register-all-defs` mints a FRESH VARIABLE for a definition that
/// declares no type and binds the declared one otherwise. Both halves are here
/// because the fresh-variable count is graded, and skipping the mint would
/// report a smaller `next-id` than upstream for the same program.
pub fn register_defs(ch: &crate::ast::Chapter, st: &mut UnifyState) -> Vec<Binding> {
    let mut out = register_ctors(ch, st);
    for d in &ch.defs {
        let ty = match d.declared_type.first().and_then(|t| resolve_declared(&ch.syms, t)) {
            Some(t) => parameterize(&t, &ch.syms, st),
            None => st.fresh(),
        };
        out.push(Binding { name: d.name, ty });
    }
    out
}

/// A variant's constructors, as the functions they are.
///
/// `MkTup2 (a) (b)` inside `Tup2 (a) (b)` is `a -> b -> Tup2 a b`, and it is
/// PARAMETERISED like any other signature -- which is where the mint comes
/// from. **THE TYPE NAME ITSELF IS NOT.** `Box (a) = | MkBox (a)` costs one
/// fresh variable and not two, and `Two (a) = | MkL (a) | MkR (a)` costs two
/// and not three; a variant with no parameters costs nothing however many arms
/// it has. Measured on `codexcheck`.
///
/// A RECORD DECLARES NO FUNCTION. `P { px = 1 }` is a record expression, not an
/// application, so there is no constructor arrow to register and nothing here
/// to mint. If that turns out to cost a mint somewhere, it needs its own probe.
fn register_ctors(ch: &crate::ast::Chapter, st: &mut UnifyState) -> Vec<Binding> {
    use crate::ast::TypeDef;
    let mut out = Vec::new();
    for td in &ch.type_defs {
        let TypeDef::Variant(name, params, ctors, _) = td else { continue };
        let result = Ty::Constructed(*name, params.iter().map(|p| Ty::TypeCon(*p)).collect());
        for c in ctors {
            // Right to left: the spine is built inside out, so the first field
            // ends up the outermost argument.
            let mut ty = result.clone();
            for f in c.fields.iter().rev() {
                let Some(a) = resolve_declared(&ch.syms, f) else { continue };
                ty = Ty::Fun(Box::new(a), EffectRow::default(), Box::new(ty));
            }
            out.push(Binding { name: c.name, ty: parameterize(&ty, &ch.syms, st) });
        }
    }
    out
}

/// One parameter of a signature: the name it was written with, and the id it
/// was given.
struct ParamEntry {
    name: String,
    id: u32,
    is_row: bool,
}

/// `parameterize-type` (TypeChecker.codex:569): a signature's free names become
/// bound variables, and the type is wrapped in one quantifier per DISTINCT one.
///
/// **THIS MINTS, AT REGISTRATION, BEFORE ANY BODY IS WALKED.** `ident : List a
/// -> List a` costs one fresh variable here and one more when its own body is
/// checked, with no caller anywhere -- and `eff-id : (Integer -> [e] Integer)
/// -> [e] Integer` costs two ROWS the same way. Measured on `codexcheck`
/// against a monomorphic control that costs nothing.
///
/// A LOWERCASE INITIAL IS WHAT MAKES A NAME A PARAMETER. `a`, `elem` and
/// `alpha` all parameterise and cost two; an uppercase name that no type
/// definition declares is `CDX3008 Undefined type name` instead. Upstream's
/// `is-value-name` reads as `char-code 'e' .. char-code 'z'`, which in CCE is
/// the letters e to z and would exclude `a` -- the measurement says `a`
/// parameterises anyway, so something above it already settled the question and
/// the range is not the gate it looks like. Measured behaviour, not the
/// predicate.
fn parameterize(t: &Ty, syms: &SymTab, st: &mut UnifyState) -> Ty {
    let mut entries: Vec<ParamEntry> = Vec::new();
    let walked = param_walk(t, syms, st, &mut entries);
    // Entry 0 is the OUTERMOST quantifier: `wrap-forall-from-entries` recurses
    // before it wraps, so the first parameter found binds the whole type.
    entries.iter().rev().fold(walked, |inner, e| {
        if e.is_row {
            Ty::ForAllEff(e.id as i32, Box::new(inner))
        } else {
            Ty::ForAll(e.id, Box::new(inner))
        }
    })
}

fn param_of(name: &str, is_row: bool, st: &mut UnifyState, entries: &mut Vec<ParamEntry>) -> u32 {
    if let Some(e) = entries.iter().find(|e| e.name == name && e.is_row == is_row) {
        return e.id;
    }
    // The two counters again: a row parameter is minted off the row counter and
    // must not move `next-id`.
    let id = if is_row { st.fresh_row() as u32 } else { st.next_id };
    if !is_row {
        let _ = st.fresh();
    }
    entries.push(ParamEntry { name: name.to_string(), id, is_row });
    id
}

fn param_walk(t: &Ty, syms: &SymTab, st: &mut UnifyState, entries: &mut Vec<ParamEntry>) -> Ty {
    let lower = |n: Name| syms.text(n).chars().next().is_some_and(char::is_lowercase);
    match t {
        Ty::TypeCon(n) if lower(*n) => {
            Ty::Var(param_of(syms.text(*n), false, st, entries))
        }
        Ty::Constructed(n, args) if lower(*n) && args.is_empty() => {
            Ty::Var(param_of(syms.text(*n), false, st, entries))
        }
        // The parameter first, then the ROW, then the result -- the order the
        // ids come out in, and they are graded.
        Ty::Fun(p, row, r) => {
            let p2 = param_walk(p, syms, st, entries);
            let row2 = if row.tail.is_empty() || row.id >= 0 {
                row.clone()
            } else {
                let tail = row.tail.clone();
                EffectRow { id: param_of(&tail, true, st, entries) as i32, ..row.clone() }
            };
            let r2 = param_walk(r, syms, st, entries);
            Ty::Fun(Box::new(p2), row2, Box::new(r2))
        }
        Ty::List(e) => Ty::List(Box::new(param_walk(e, syms, st, entries))),
        Ty::LinkedList(e) => Ty::LinkedList(Box::new(param_walk(e, syms, st, entries))),
        Ty::Linear(e) => Ty::Linear(Box::new(param_walk(e, syms, st, entries))),
        Ty::Vector(n, e) => Ty::Vector(*n, Box::new(param_walk(e, syms, st, entries))),
        Ty::Effectful(effs, sc, r) => Ty::Effectful(
            effs.clone(),
            sc.clone(),
            Box::new(param_walk(r, syms, st, entries)),
        ),
        Ty::Constructed(n, args) => Ty::Constructed(
            *n,
            args.iter().map(|a| param_walk(a, syms, st, entries)).collect(),
        ),
        other => other.clone(),
    }
}

/// Register every definition, then infer every body.
///
/// TWO PASSES, and the order is upstream's: all names are bound before any
/// body is walked, which is what lets `fib` call itself. A one-pass checker
/// would find `fib` undefined inside its own body and mint a fresh variable
/// for it -- reaching a plausible answer with the wrong `next-id`.
pub fn check_chapter(ch: &crate::ast::Chapter) -> (Vec<Binding>, UnifyState) {
    let mut st = UnifyState::default();
    let bindings = register_defs(ch, &mut st);
    // Builtins first, then the chapter's own names on top: a chapter that
    // defines `max` shadows the builtin, which the golds show for that name.
    let mut env = builtin_env(&ch.syms);
    for b in &bindings {
        env.bind(b.name, b.ty.clone());
    }
    for d in &ch.defs {
        // A definition's parameters take their types from its declared arrow
        // spine, walked in order.
        // A DEFINITION'S PARAMETERS COME FROM ITS DECLARED ARROW, and mint
        // nothing. `bind-lambda-params` mints one per parameter, but it is for
        // LAMBDAS; a declared definition already has its parameter types.
        //
        // Minting here gave the right TOTAL by cancelling a second error --
        // starting next-id at 0 where upstream starts at 2 -- and the ids would
        // have been shifted by two all the way into the IR, where they are
        // printed as `(tvar N)`. Two wrongs summing to 8.
        // **`instantiate-collect`: A DEFINITION'S OWN BODY INSTANTIATES ITS OWN
        // SIGNATURE.** The body wants the opposite of a quantifier -- concrete
        // variables it can unify against -- so every parameter is minted a
        // second time here. That is the other half of what a type parameter
        // costs, and it is paid whether or not anything calls the definition.
        let own = bindings.iter().find(|b| b.name == d.name).map(|b| b.ty.clone());
        let instantiated = own.clone().map(|t| st.instantiate(&t));
        let mut spine = instantiated.clone();
        let mut saved = Vec::new();
        for p in &d.params {
            let arg = match spine {
                Some(Ty::Fun(a, _, r)) => {
                    spine = Some(*r);
                    *a
                }
                _ => {
                    spine = None;
                    st.fresh()
                }
            };
            saved.push(p.name.clone());
            env.bind(p.name, arg);
        }
        let body_ty = infer(&d.body, &mut env, &mut st);
        // **THE BODY MEETS THE DECLARED RESULT.** Without this a definition's
        // own signature decides nothing about what it computes, and an
        // inferred variable never learns what it is: `f : Integer -> List
        // Integer` with body `[]` left the element as `(tvar 2)` where the
        // oracle spells `int-default`. Nothing is minted here -- unification
        // binds, it does not allocate.
        //
        // An effectful result is peeled first: `opening : [Console] Nothing`
        // computes a `Nothing`, and the row is the caller's business.
        let want = match spine {
            Some(Ty::Effectful(_, _, inner)) => Some(*inner),
            other => other,
        };
        if let Some(w) = want {
            if !st.unify(&body_ty, &w) {
                st.unify_gaps += 1;
            }
        }
        // **A QUANTIFIED DEFINITION IS TIED BACK TO ITS OWN SIGNATURE**, after
        // the body -- `check-def-normal`'s `tied-state` (TypeChecker.codex:866)
        // unifies the instantiated type against `strip-forall-ty env-type`.
        //
        // For a type parameter both sides carry empty rows and nothing is
        // minted; for a ROW parameter the instantiated row and the signature's
        // row are two OPEN rows with different tails, and equating them is the
        // third row such a signature costs. Its position matters: it lands
        // after everything the body minted, not before.
        if let (Some(Ty::ForAll(..) | Ty::ForAllEff(..)), Some(inst)) = (own.clone(), instantiated)
        {
            let bare = strip_forall(&own.unwrap());
            if !st.unify(&inst, &bare) {
                st.unify_gaps += 1;
            }
        }
        for _ in saved {
            env.scope.pop();
        }
    }
    // The check/lower boundary, where upstream sorts too: everything below
    // this line looks entries up rather than appending them.
    st.sort_expr_types();
    (bindings, st)
}

/// The `--- check ---` section, in the harness's own format so it can be
/// diffed against `$CODEX_GOLDS/rungs/check.truth` directly.
pub fn section(syms: &SymTab, bindings: &[Binding], st: &UnifyState) -> String {
    let mut s = String::from("--- check ---\n");
    s.push_str(&format!("check-errors {}\n", st.errors));
    s.push_str(&format!("type-bindings {}\n", bindings.len()));
    for b in bindings {
        s.push_str(&format!("tb {} {}\n", syms.text(b.name), type_kind(syms, &b.ty)));
    }
    s.push_str(".\n");
    s.push_str(&format!("substitutions {}\n", st.substitutions.len()));
    s.push_str(&format!("next-id {}\n", st.next_id));
    // `CheckHarness.codex` prints this and `$CODEX_GOLDS/rungs/check.truth`
    // does not: the bank predates the row counter. `codexcheck` is the control
    // now, so the section is shaped to IT.
    s.push_str(&format!("next-row-id {}\n", st.next_row_id));
    s.push_str(&format!("expr-types {}\n", st.expr_types.len()));
    // The harness closes the section, and the gold's last line is this.
    s.push_str("---\n");
    s
}

/// Inference over one expression, threading the state.
///
/// MIRRORS `TypeCheckerInference.codex`'s ALLOCATION ORDER, not merely its
/// conclusions. `infer-application` (line 633) mints a fresh result variable
/// and then a fresh ROW id -- two counters, `next_id` and `next_row_id` -- and
/// a checker that reaches the same types while minting in a different order
/// reports a different `next-id` and is wrong against the gold, because those
/// ids are printed into the IR as `(tvar 41)`.
///
/// Every expression's type is recorded, because the IR carries one on nearly
/// every node and `expr-types` counts them.
pub fn infer(e: &crate::ast::Expr, env: &mut TyEnv<'_>, st: &mut UnifyState) -> Ty {
    use crate::ast::Expr as E;
    let t = match e {
        E::Lit(_, crate::ast::LiteralKind::IntLit, _) => {
            Ty::Integer(i64::MIN, i64::MAX, Overflow::Error)
        }
        E::Lit(_, crate::ast::LiteralKind::TextLit, _) => Ty::Text,
        E::Lit(_, crate::ast::LiteralKind::BoolLit, _) => Ty::Boolean,
        E::Lit(..) => Ty::Error,
        // `record-expr-type` has SEVEN call sites upstream and the one that
        // fires here is name inference. Counted on fib: 6 names in `fib`, 2 in
        // `double`, 3 in `opening` -- exactly the gold's `expr-types 11`.
        // Recording every expression instead gave 27.
        E::NameRef(n, sp) => {
            // INSTANTIATING A FORALL MINTS. `show` is
            // `ForAllTy 0 (FunTy (TypeVar 0) empty-row TextTy)`, and opening
            // applies it -- the third of fib's three missing mints.
            let raw = env.get(*n).cloned();
            let t = match raw {
                Some(r) => {
                    let inst = st.instantiate(&r);
                    st.open_spine_rows(&inst)
                }
                None => Ty::Error,
            };
            // **THE SPINE MINTS BEFORE THE APPLICATION AROUND IT MINTS
            // ANYTHING**, which is what puts a row id on the wire: in fib,
            // `print-line-uni` reaches the IR as
            // `(fn text nothing (row (labels (label "Console.Write" "")) "" 6))`
            // and 6 is where fib's own body left the counter.
            //
            // Measured, not reasoned: `print-line-uni (read-file-raw "f")` puts
            // Console.Write on row 0 and FileSystem.Read on row 1. Minting all
            // of an application's rows up front would have given the inner
            // builtin row 3, and minting them after would have given the OUTER
            // one the higher number. Only this order produces 0 and 1.
            //
            // `infer-name` (TypeCheckerInference.codex:158) records the INNER
            // type of an effectful name and hands the row to its caller: the
            // value side is what this wire spells.
            let rec = match t {
                Ty::Effectful(_, _, inner) => *inner,
                other => other,
            };
            st.record_expr_type(*sp, rec.clone());
            return rec;
        }
        // A comparison answers Boolean; arithmetic answers its operands'.
        // Neither mints, which is why fib's five applications are not the
        // whole of its next-id.
        E::Binary(l, op, r, _) => {
            let lt = infer(l, env, st);
            let _rt = infer(r, env, st);
            use crate::ast::BinaryOp::*;
            match op {
                OpEq | OpNotEq | OpLt | OpGt | OpLtEq | OpGtEq | OpAnd | OpBoolAnd | OpOr => {
                    Ty::Boolean
                }
                _ => lt,
            }
        }
        E::If(c, a, b, _) => {
            let _ = infer(c, env, st);
            let ta = infer(a, env, st);
            let _tb = infer(b, env, st);
            ta
        }
        // Mints a result variable and TWO row ids, after both halves are in.
        // The application's own row is minted by the name in function position
        // (see the NameRef arm); these two are the rest of the three an
        // application costs.
        E::Apply(f, a, _) => {
            let ft = infer(f, env, st);
            let at = infer(a, env, st);
            let ret = st.fresh();
            // **ONE ROW HERE, AND THE SECOND COMES FROM UNIFICATION.** An
            // application was measured at two rows and this minted both; with
            // `unify-row` in place the second is where upstream actually makes
            // it -- the function's arrow row meeting `(row-var call-row-id)`,
            // two open rows with different tails. Minting it here as well
            // counted it twice.
            let call_row = st.fresh_row();
            // `unify st (fr.inferred-type) (FunTy passed-ty (row-var call-row-id) ret-ty)`
            // -- and THIS is what decides an inferred type. `show`'s
            // instantiated variable meets the argument here and nowhere else.
            let want = Ty::Fun(
                Box::new(at),
                EffectRow { id: call_row, ..Default::default() },
                Box::new(ret.clone()),
            );
            if !st.unify(&ft, &want) {
                st.unify_gaps += 1;
            }
            // **THE FRESH VARIABLE, NOT THE ARROW'S RIGHT HALF.** Upstream
            // answers `ret-ty` and lets `deep-resolve` read it back later;
            // peeling the arrow instead answers the same type only while the
            // function's own type is already ground.
            ret
        }
        E::Act(stmts, _) => {
            let mut last = Ty::Nothing;
            for s in stmts {
                match s {
                    crate::ast::ActStmt::Exec(x, _) | crate::ast::ActStmt::Bind(_, x, _) => {
                        last = infer(x, env, st)
                    }
                }
            }
            last
        }
        E::Let(binds, body, _) => {
            for b in binds {
                let t = infer(&b.value, env, st);
                env.bind(b.name, t);
            }
            infer(body, env, st)
        }
        // **EVERY REMAINING FORM IS WALKED, EVEN WHERE THE TYPE IS NOT KNOWN.**
        // A `_ => Ty::Error` arm that did not recurse skipped whole subtrees in
        // silence: no name inside a lambda, a match arm, a record literal or a
        // list literal was ever visited, so none of them minted and none of
        // them was recorded. On `encode-hex`'s unit that was 98 fresh
        // variables, 18 rows and 22 expression types missing against
        // `codexcheck`, and the shortfall reached the wire as a row id 18 low
        // on the ONE definition the IR keeps.
        //
        // Answering the type is a separate question from making the walk. What
        // each of these mints has to be measured form by form the way the
        // application rule was; until then they recurse and mint nothing of
        // their own, which is a number that can be checked rather than a
        // subtree that cannot.
        E::Unary(x, _) => infer(x, env, st),
        E::Lazy(x, _) => infer(x, env, st),
        // **AN EMPTY LIST MINTS ONE VARIABLE AND RECORDS IT; A NON-EMPTY ONE
        // MINTS NOTHING.** `[]` has no element to read a type from, so the
        // element type is a fresh variable that unification decides from the
        // context -- and lowering reads it back at this span to spell
        // `(list-expr (elems) int-default)`. Measured on `codexcheck`:
        // `f (x) = []` is next-id 3 and expr-types 1 where `f (x) = [x]` is 2
        // and 1, on a body with no names in it at all.
        E::List(xs, sp) => {
            if xs.is_empty() {
                let e = st.fresh();
                st.record_expr_type(*sp, e.clone());
                return Ty::List(Box::new(e));
            }
            let mut elem = Ty::Error;
            for x in xs {
                elem = infer(x, env, st);
            }
            Ty::List(Box::new(elem))
        }
        // `bind-lambda-params` mints one variable per parameter -- a lambda,
        // unlike a declared definition, has nowhere else to get them from.
        E::Lambda(params, body, sp) => {
            let mut arg = Ty::Error;
            for p in params {
                arg = st.fresh();
                env.bind(*p, arg.clone());
            }
            let ret = infer(body, env, st);
            for _ in params {
                env.scope.pop();
            }
            let t = Ty::Fun(Box::new(arg), EffectRow::default(), Box::new(ret));
            st.record_expr_type(*sp, t.clone());
            return t;
        }
        E::Match(scrut, arms, _) | E::Induction(scrut, arms, _) => {
            let _ = infer(scrut, env, st);
            let mut last = Ty::Error;
            for a in arms {
                let bound = bind_pattern(&a.pattern, env, st);
                let _ = infer(&a.guard, env, st);
                last = infer(&a.body, env, st);
                for _ in 0..bound {
                    env.scope.pop();
                }
            }
            last
        }
        // A record literal is the other site `record-expr-type` is populated
        // from (Unifier.codex:131).
        E::Record(n, fields, sp) => {
            for f in fields {
                let _ = infer(&f.value, env, st);
            }
            let t = Ty::Record(*n, Vec::new());
            st.record_expr_type(*sp, t.clone());
            return t;
        }
        // The field's type is in the chapter's type definitions, which this
        // does not read yet. The RECORD is still walked.
        E::FieldAccess(r, _, _) => {
            let _ = infer(r, env, st);
            Ty::Error
        }
        E::FieldAssign(r, _, v, _) => {
            let _ = infer(r, env, st);
            let _ = infer(v, env, st);
            Ty::Nothing
        }
        E::Handle(h) => {
            let t = infer(&h.body, env, st);
            for c in &h.clauses {
                let _ = infer(&c.body, env, st);
            }
            t
        }
        E::WithTimeout(w) => infer(&w.body, env, st),
        // Three statement lists, all of them walked: the body, the retry
        // fallback and the failure arm are all program the checker sees.
        E::Try(t) => {
            let mut last = Ty::Nothing;
            for stmts in [&t.body, &t.fallback, &t.failure] {
                for stmt in stmts {
                    match stmt {
                        crate::ast::ActStmt::Exec(x, _) => last = infer(x, env, st),
                        crate::ast::ActStmt::Bind(n, x, _) => {
                            last = infer(x, env, st);
                            env.bind(*n, last.clone());
                        }
                    }
                }
            }
            last
        }
        E::Error(..) => Ty::Error,
    };
    t
}

/// A pattern's variables, bound to fresh variables for the arm's body. Returns
/// how many were pushed so the caller can pop exactly those.
fn bind_pattern(p: &crate::ast::Pat, env: &mut TyEnv<'_>, st: &mut UnifyState) -> usize {
    use crate::ast::Pat as P;
    match p {
        P::Var(n, _) => {
            let t = st.fresh();
            env.bind(*n, t);
            1
        }
        P::Ctor(_, subs, _) | P::Vec_(subs, _) => {
            subs.iter().map(|s| bind_pattern(s, env, st)).sum()
        }
        P::Lit(..) | P::Wild(_) => 0,
    }
}

/// Names in scope during inference.
pub struct TyEnv<'a> {
    /// Carried so inference can spell a type's name without every function
    /// here taking a table.
    pub syms: &'a SymTab,
    /// **Symbols, not text.** This is a linear scan on the hot path of
    /// inference, and it now compares four bytes.
    pub scope: Vec<(Sym, Ty)>,
}

impl<'a> TyEnv<'a> {
    pub fn new(syms: &'a SymTab) -> TyEnv<'a> {
        TyEnv { syms, scope: Vec::new() }
    }
    pub fn get(&self, n: Sym) -> Option<&Ty> {
        self.scope.iter().rev().find(|(k, _)| *k == n).map(|(_, v)| v)
    }
    pub fn bind(&mut self, n: Sym, t: Ty) {
        self.scope.push((n, t));
    }
}

/// Read a builtin's declared type back out of `BUILTIN_TYPES`.
///
/// The table holds a compact s-expression -- `(forall 0 (fn (tvar 0) empty
/// text))` -- because the IR spelling cannot express a forall and the checker
/// needs one. Forty lines and testable, where generated Rust constructor calls
/// would be neither readable in a diff nor checkable.
pub fn parse_ty(syms: &SymTab, s: &str) -> Option<Ty> {
    let (t, rest) = parse_one(syms, s.trim())?;
    if rest.trim().is_empty() { Some(t) } else { None }
}

/// The text of a parenthesised group and what follows it, parens balanced.
///
/// Needed because a row is a GROUP THAT CONTRIBUTES NO TYPE. Recursing into it
/// with `parse_one` cannot say that: the only "no type here" it can return is
/// `None`, which is also how it says "this does not parse" -- so `(row ...)`
/// killed the whole type and every effectful builtin was dropped from the
/// environment in silence. `print-line-uni` was absent for that reason, which
/// cost it the row its name is supposed to mint.
fn take_group(s: &str) -> Option<(&str, &str)> {
    let s = s.trim_start();
    if !s.starts_with('(') {
        return None;
    }
    let mut depth = 0usize;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some((&s[1..i], &s[i + 1..]));
                }
            }
            _ => {}
        }
    }
    None
}

/// `(row Console.Write)`, `(rowvar 0)` and `empty` as the wire's own record.
///
/// **`empty` AND `(rowvar N)` ARE NOT THE SAME ROW.** An empty row has no tail
/// and `open-spine-rows` mints one for it at every reference; a row variable
/// already carries the id its `foralleff` binds, and minting over it would put
/// a number on the wire that nothing else in the program agrees with.
fn parse_row(inner: &str) -> EffectRow {
    let mut it = inner.split_whitespace();
    let head = it.next().unwrap_or("");
    match head {
        "row" => EffectRow {
            labels: it.map(|w| (w.to_string(), String::new())).collect(),
            ..Default::default()
        },
        "rowvar" => EffectRow {
            id: it.next().and_then(|w| w.parse().ok()).unwrap_or(-1),
            ..Default::default()
        },
        _ => EffectRow::default(),
    }
}

fn parse_one<'a>(syms: &SymTab, s: &'a str) -> Option<(Ty, &'a str)> {
    let s = s.trim_start();
    if let Some(inner) = s.strip_prefix('(') {
        let (head, mut rest) = take_word(inner);
        let mut args: Vec<Ty> = Vec::new();
        let mut words: Vec<String> = Vec::new();
        let mut rows: Vec<EffectRow> = Vec::new();
        loop {
            let r = rest.trim_start();
            if let Some(after) = r.strip_prefix(')') {
                return Some((build(syms, head, &args, &words, &rows)?, after));
            }
            if r.starts_with('(') {
                // A row group is consumed whole and contributes a row, not a
                // type; anything else is an ordinary nested type.
                let is_row = take_group(r)
                    .map(|(inner, _)| {
                        let w = inner.split_whitespace().next().unwrap_or("");
                        w == "row" || w == "empty" || w == "rowvar"
                    })
                    .unwrap_or(false);
                if is_row {
                    let (inner, after) = take_group(r)?;
                    rows.push(parse_row(inner));
                    rest = after;
                    continue;
                }
                let (t, after) = parse_one(syms, r)?;
                args.push(t);
                rest = after;
            } else {
                let (w, after) = take_word(r);
                words.push(w.to_string());
                if w == "empty" {
                    rows.push(EffectRow::default());
                } else if let Some(t) = atom(w) {
                    args.push(t);
                }
                rest = after;
            }
        }
    }
    let (w, rest) = take_word(s);
    atom(w).map(|t| (t, rest))
}

fn take_word(s: &str) -> (&str, &str) {
    let s = s.trim_start();
    let end = s.find(|c: char| c.is_whitespace() || c == '(' || c == ')').unwrap_or(s.len());
    (&s[..end], &s[end..])
}

fn atom(w: &str) -> Option<Ty> {
    Some(match w {
        "int" => Ty::Integer(i64::MIN, i64::MAX, Overflow::Error),
        "text" => Ty::Text,
        "bool" => Ty::Boolean,
        "char" => Ty::Char,
        "nothing" => Ty::Nothing,
        "void" => Ty::Void,
        "error" => Ty::Error,
        "proof" => Ty::Proof,
        "real" => Ty::Real(RealWidth::F64, RealMode::Default),
        "real-trapping" => Ty::Real(RealWidth::F64, RealMode::Trapping),
        "real-saturating" => Ty::Real(RealWidth::F64, RealMode::Saturating),
        "real-approx" => Ty::Real(RealWidth::F32, RealMode::Default),
        "real-approx-trapping" => Ty::Real(RealWidth::F32, RealMode::Trapping),
        "real-approx-saturating" => Ty::Real(RealWidth::F32, RealMode::Saturating),
        _ => return None,
    })
}

fn build(syms: &SymTab, head: &str, args: &[Ty], words: &[String], rows: &[EffectRow]) -> Option<Ty> {
    Some(match head {
        // `(fn A ROW B)` -- the row contributes no Ty, so A and B are args 0/1,
        // and the row itself is CARRIED rather than defaulted away: its labels
        // are what the wire spells for an effectful builtin, and its id is what
        // the checker mints on the way past.
        "fn" => Ty::Fun(
            Box::new(args.first()?.clone()),
            rows.first().cloned().unwrap_or_default(),
            Box::new(args.get(1)?.clone()),
        ),
        "tvar" => Ty::Var(words.first()?.parse().ok()?),
        "forall" => Ty::ForAll(words.first()?.parse().ok()?, Box::new(args.first()?.clone())),
        "foralleff" => Ty::ForAllEff(words.first()?.parse().ok()?, Box::new(args.first()?.clone())),
        "list" => Ty::List(Box::new(args.first()?.clone())),
        "llist" => Ty::LinkedList(Box::new(args.first()?.clone())),
        "vec" => Ty::Vector(words.first()?.parse().ok()?, Box::new(args.first()?.clone())),
        "vec-mask" => Ty::VectorMask(words.first()?.parse().ok()?),
        "propeq" => Ty::PropEq(
            Box::new(args.first()?.clone()),
            Box::new(args.get(1)?.clone()),
        ),
        "tyapply" => Ty::TypeApply(
            Box::new(args.first()?.clone()),
            Box::new(args.get(1)?.clone()),
        ),
        // **A CONSTRUCTOR THIS CHAPTER NEVER SPELLS IS REFUSED, NOT DEFAULTED.**
        // The name is a `Sym` and interning one here would need a mutable
        // table the checker does not hold; `Sym::default()` would print some
        // other chapter's first name into a graded `tb` line. So a chapter
        // that calls `read-line` without ever naming `Maybe` loses the builtin
        // rather than gaining a wrong one, and the gap is visible.
        "ctd" => Ty::Constructed(syms.find(words.first()?)?, args.to_vec()),
        // The effect NAMES a builtin declares are not carried: `infer-name`
        // answers the inner type and hands the row to its caller, so they
        // never reach this wire through a reference. See the probe.
        "eff" => Ty::Effectful(Vec::new(), Vec::new(), Box::new(args.first()?.clone())),
        _ => return None,
    })
}

/// Every builtin whose declared type the probe could render, for the checker's
/// environment. Without these `show` resolves to ErrorTy and instantiating it
/// mints nothing -- which is one of the eight fresh variables fib expects.
pub fn builtin_env(syms: &SymTab) -> TyEnv<'_> {
    let mut env = TyEnv::new(syms);
    for (n, s) in crate::builtins::BUILTIN_TYPES {
        // A builtin the chapter never names cannot be what any symbol here
        // means, so it needs no binding.
        let (Some(sym), Some(t)) = (syms.find(n), parse_ty(syms, s)) else { continue };
        env.bind(sym, t);
    }
    env
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `(next_id, next_row_id)` after checking one chapter.
    fn counters(src: &str) -> (u32, i32) {
        let bytes = src.as_bytes();
        let parsed = crate::parser::parse(bytes);
        let mut dg = crate::desugar::Desugar::new(bytes);
        let ch = dg.chapter(&parsed.tree);
        let (_, st) = check_chapter(&ch);
        (st.next_id, st.next_row_id)
    }

    fn chapter(body: &str) -> String {
        format!("Chapter: T\n\nSection: S\n{body}")
    }

    /// **EVERY NUMBER HERE WAS READ OFF `codexcheck`, NOT REASONED OUT.**
    /// One probe per row, `codexcheck < probe.codex`, at
    /// `u56-candidate-sunday`. The rule they pin down:
    ///
    ///   * an APPLICATION mints exactly THREE row ids
    ///   * they are allocated OUTERMOST FIRST -- before recursing into the
    ///     function and the argument, not after
    ///   * a type variable is minted once per application and once per
    ///     `forall` quantifier instantiated
    ///
    /// The ordering is what the nesting rows prove. `print-line-uni` is the
    /// outermost application in all three of the last shapes and takes row 0
    /// in every one of them, however deep the argument goes; a checker that
    /// minted after recursing would give it 0, 3 and 6 instead.
    #[test]
    fn row_ids_are_three_per_application_outermost_first() {
        // No application anywhere: neither counter moves off its base.
        assert_eq!(counters(&chapter("  a : Integer\n  a = 1\n")), (2, 0));
        assert_eq!(counters(&chapter("  f : Integer -> Integer\n  f (x) = x\n")), (2, 0));

        // One application of a user function: three rows, one type variable.
        assert_eq!(
            counters(&chapter(
                "  f : Integer -> Integer\n  f (x) = x\n\n  \
                 h : Integer -> Integer\n  h (x) = f x\n"
            )),
            (3, 3)
        );

        // A builtin is no different: one application, three rows.
        let eff = |body: &str| {
            chapter(&format!("  opening : [Console] Nothing = act\n   {body}\n  end\n"))
        };
        assert_eq!(counters(&eff(r#"print-line-uni "a""#)), (3, 3));
        // Two applications, and `show` is `forall 0` -- so +2 vars for the
        // applications and +1 for the quantifier.
        assert_eq!(counters(&eff("print-line-uni (show 1)")), (5, 6));
        // Three applications, still one quantifier.
        assert_eq!(counters(&eff(r#"print-line-uni (show (text-length "xy"))"#)), (6, 9));
    }

    /// **A ROW IS MINTED PER ARROW IN THE RESULT SPINE, INNERMOST FIRST.**
    ///
    /// `open-spine-rows` (TypeCheckerInference.codex:188) recurses into the
    /// RESULT before minting for the arrow it is holding, so a two-parameter
    /// function costs TWO rows at every reference and a one-parameter function
    /// costs one. "One row per function-typed name" agrees with the oracle on
    /// every one-arrow subject and is wrong the moment a subject has two.
    ///
    /// Read off `codexcheck` at `u56-candidate-sunday`, one probe per row.
    #[test]
    fn a_row_is_minted_per_arrow_in_the_result_spine() {
        let one = "  f : Integer -> Integer\n  f (x) = x\n\n  \
                   h : Integer -> Integer\n  h (x) = f x\n";
        assert_eq!(counters(&chapter(one)), (3, 3));

        // Two arrows, saturated: two spine rows at the reference to `g`, then
        // two applications at two rows each.
        let two = "  g : Integer, Integer -> Integer\n  g (x) (y) = x\n\n  \
                   h : Integer -> Integer\n  h (x) = g x x\n";
        assert_eq!(counters(&chapter(two)), (4, 6));

        // A function-typed PARAMETER is not walked into: the spine is the
        // RESULT chain, so `double-it : (Integer -> Integer) -> Integer` mints
        // one row and not two.
        let partial = "  g : Integer, Integer -> Integer\n  g (x) (y) = x\n\n  \
                       h : Integer -> Integer\n  h (x) = double-it (g x)\n\n  \
                       double-it : (Integer -> Integer) -> Integer\n  \
                       double-it (k) = k 1\n";
        assert_eq!(counters(&chapter(partial)), (5, 10));
    }

    /// **A TYPE PARAMETER COSTS TWO FRESH VARIABLES AND A ROW PARAMETER TWO
    /// FRESH ROWS -- BEFORE ANYONE CALLS THE DEFINITION.**
    ///
    /// `parameterize-type` (TypeChecker.codex:569) mints one for each DISTINCT
    /// parameter when the signature is registered, and `instantiate-collect`
    /// mints another for each when the definition's OWN body is checked. Every
    /// reference afterwards instantiates and mints one more.
    ///
    /// Read off `codexcheck` at `u56-candidate-sunday`. The monomorphic
    /// control is what makes the numbers mean anything: `ident : List Integer
    /// -> List Integer` costs nothing at all, so the difference is
    /// parameterisation and not the shape of the definition.
    #[test]
    fn a_type_parameter_costs_two_before_anyone_calls_it() {
        let ident = "  ident : List a -> List a\n  ident (xs) = xs\n";
        // Registration and the definition's own body: two, with no caller.
        assert_eq!(counters(&chapter(ident)), (4, 0));

        // Distinct parameters, not occurrences: `a` appears twice above and
        // costs two, while `a` and `b` below cost four.
        let pair = "  pair : List a, List b -> List a\n  pair (xs) (ys) = xs\n";
        assert_eq!(counters(&chapter(pair)), (6, 0));

        // A caller adds one instantiation per parameter, on top of what the
        // application itself costs.
        let call = |n: usize| {
            let body = (0..n).fold("ys".to_string(), |acc, _| format!("ident ({acc})"));
            format!("{ident}\n  use : List Integer -> List Integer\n  use (ys) = {body}\n")
        };
        assert_eq!(counters(&chapter(&call(1))), (6, 3));
        assert_eq!(counters(&chapter(&call(2))), (8, 6));

        // The ROW parameter is the same rule on the other counter: `[e]` costs
        // two rows, and the body's one application and one spine cost three.
        let eff = "  eff-id : (Integer -> [e] Integer) -> [e] Integer\n  eff-id (g) = g 1\n";
        assert_eq!(counters(&chapter(eff)), (3, 5));
    }

    /// **A VARIANT'S CONSTRUCTORS ARE PARAMETERISED; THE TYPE NAME IS NOT.**
    ///
    /// `Box (a) = | MkBox (a)` costs ONE fresh variable, not two -- if the
    /// binding for `Box` itself were parameterised alongside `MkBox` it would
    /// be two, and `Two (a) = | MkL (a) | MkR (a)` would be three rather than
    /// the two it measures. A variant with no type parameters costs nothing at
    /// all, however many constructors it declares.
    ///
    /// Read off `codexcheck` at `u56-candidate-sunday`, against a chapter whose
    /// only definition is monomorphic so the difference is the type
    /// declaration alone.
    #[test]
    fn a_variant_mints_once_per_type_parameter_per_constructor() {
        let f = "\n  f : Integer -> Integer\n  f (n) = n\n";
        let with = |decl: &str| counters(&chapter(&format!("{decl}{f}")));

        assert_eq!(with(""), (2, 0));
        assert_eq!(with("  Box (a) =\n    | MkBox (a)\n"), (3, 0));
        assert_eq!(with("  Pair (a) (b) =\n    | MkPair (a) (b)\n"), (4, 0));
        assert_eq!(with("  Trip (a) (b) (c) =\n    | MkTrip (a) (b) (c)\n"), (5, 0));
        // Once per CONSTRUCTOR, so two arms naming the same parameter cost two.
        assert_eq!(with("  Two (a) =\n    | MkL (a)\n    | MkR (a)\n"), (4, 0));
        // No parameters, no mint -- the constructors are still declared.
        assert_eq!(with("  Mono =\n    | MkA\n    | MkB\n"), (2, 0));
    }

    /// The slice subject, whole, and the two neighbours that isolate the
    /// effectful half. `fib` alone is two recursive applications; each print
    /// adds three more (`print-line-uni`, `show`, `fib`), which is why the
    /// rows go 6 -> 15 -> 24 in steps of nine.
    #[test]
    fn fib_matches_the_oracle_on_both_counters() {
        let math = "  fib : Integer -> Integer\n  fib (n) =\n   if n <= 1 then n\n   \
                    else fib (n - 1) + fib (n - 2)\n";
        assert_eq!(counters(&chapter(math)), (4, 6));

        let with = |n: usize| {
            let prints: String = (0..n)
                .map(|i| format!("   print-line-uni (show (fib {}))\n", 20 + i))
                .collect();
            chapter(&format!("{math}\n  opening : [Console] Nothing = act\n{prints}  end\n"))
        };
        assert_eq!(counters(&with(1)), (8, 15));
        assert_eq!(counters(&with(2)), (12, 24));
    }
}
