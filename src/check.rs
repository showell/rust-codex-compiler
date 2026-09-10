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
    /// The type each PATTERN node was checked against, by span.
    ///
    /// **DELIBERATELY NOT `expr_types`.** That table is a graded counter --
    /// upstream's `expr-types` counts name references and the number is
    /// compared against `codexcheck` -- so putting patterns in it would break
    /// the one measurement that says the checker walks what upstream walks.
    /// This is a second table with no oracle, kept for one reason: lowering
    /// needs the field types of a destructure, and the checker already worked
    /// them out. See `bind_pattern`.
    pub pat_types: Vec<(u64, Ty)>,
    /// **A COUNT THAT CANNOT SAY WHAT IT COUNTED IS THE WEAKER THING.**
    /// `check-errors` is graded as a number, but a number that matches with the
    /// wrong diagnosis behind it is not agreement -- so the code travels with
    /// it. Upstream carries a whole bag (`add-unify-error st cdx-... "msg"
    /// span`); this is its two load-bearing fields.
    pub diags: Vec<Diag>,
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
/// Upstream's `is-synthetic-span` is `span.file-id == 0`. There is one file
/// here, so the marker is the LINE: source lines are 1-based, and only a span
/// this desugarer invented has line 0.
pub fn is_synthetic(sp: crate::ast::Span) -> bool {
    sp.line == 0
}

/// Upstream's key: the file id in the high bits, then offset and length. The
/// source is file 1. **A synthetic span is file 0**, as it is upstream, and
/// the desugarer numbers its invented nodes within that file, so a synthetic
/// key can never collide with a source one or with another synthetic one.
pub fn expr_type_key(sp: crate::ast::Span) -> u64 {
    let file = if is_synthetic(sp) { 0u64 } else { 1u64 << 48 };
    file + (sp.offset as u64) * 65536 + (sp.len.min(65535) as u64)
}

/// One diagnostic: upstream's code, and what it says.
#[derive(Clone, Debug)]
pub struct Diag {
    pub code: u16,
    pub message: String,
}

/// The `CdxCodes.codex` numbers we raise. **These are upstream's, not ours** --
/// a diagnostic is part of the wire a user reads, and inventing a number would
/// make two compilers disagree about what a program's problem IS while
/// agreeing that it has one.
pub struct Cdx;

impl Cdx {
    pub const TYPE_MISMATCH: u16 = 2001;
    pub const INFINITE_TYPE: u16 = 2010;
    pub const UNKNOWN_RECORD_FIELD: u16 = 2005;
    pub const FIELD_ON_UNIT_TYPE: u16 = 2095;
    pub const USE_AFTER_CONSUME: u16 = 2061;
    pub const MUTABLE_ALIAS: u16 = 2062;
    pub const LINEAR_UNUSED: u16 = 2063;
    pub const LINEAR_ESCAPE: u16 = 2065;
    pub const LINEAR_RETURN: u16 = 2066;
    pub const LINEAR_CAPTURE: u16 = 2067;
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
            pat_types: Vec::new(),
            diags: Vec::new(),
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

    /// `row-union` (Unifier.codex:377). **IT NEVER MINTS.** Two rows meeting
    /// as a compound expression's ambient effects is not the same event as two
    /// rows being unified: an empty side yields the other, identical sides
    /// yield themselves, and only when both are open with different tails does
    /// one tail get SUBSTITUTED to the other -- a substitution, not a fresh id.
    /// Getting that wrong would move `next-row-id` at every binary operator.
    fn row_union(&mut self, r1: &EffectRow, r2: &EffectRow) -> EffectRow {
        let a = self.resolve_row(r1);
        let b = self.resolve_row(r2);
        if a.labels.is_empty() && a.id < 0 {
            return b;
        }
        if b.labels.is_empty() && b.id < 0 {
            return a;
        }
        if a.labels == b.labels && a.id == b.id && a.tail == b.tail {
            return a;
        }
        let mut merged = a.labels.clone();
        merged.extend(b.labels.iter().cloned());
        if a.id < 0 {
            return EffectRow { labels: merged, tail: b.tail, id: b.id };
        }
        if b.id < 0 || a.id == b.id {
            return EffectRow { labels: merged, tail: a.tail, id: a.id };
        }
        self.add_row_subst(a.id, EffectRow { id: b.id, ..Default::default() });
        EffectRow { labels: merged, tail: b.tail, id: b.id }
    }

    /// `open-row-if-closed` (TypeCheckerInference.codex:529). **A LAMBDA MINTS
    /// A ROW ONLY WHEN ITS BODY'S IS CLOSED.** An application hands back an
    /// open row -- it minted a call row -- so `\u -> f x` costs nothing here
    /// while `\u -> n` costs one. Minting unconditionally is +1 per lambda
    /// over an effectful body, which is one character of IR (`"" 848` against
    /// `"" 847`) and no other visible symptom.
    fn open_row_if_closed(&mut self, row: &EffectRow) -> EffectRow {
        let r = self.resolve_row(row);
        if r.id >= 0 {
            return r;
        }
        EffectRow { labels: r.labels, tail: String::new(), id: self.fresh_row() }
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
    ///
    /// **A SYNTHETIC SPAN RECORDS NOTHING**, which is upstream's first line:
    /// `if is-synthetic-span sp then st`. The desugarer's derived definitions
    /// -- `__eq_<T>` for a self-recursive variant -- are built entirely from
    /// synthetic spans, so they mint type variables and contribute no
    /// expression types at all. That asymmetry is visible in the numbers:
    /// `encode-ini`'s unit matched on `expr-types` while `next-id` was short.
    pub fn record_expr_type(&mut self, sp: crate::ast::Span, t: Ty) {
        if is_synthetic(sp) {
            return;
        }
        self.expr_types.push((expr_type_key(sp), t));
    }

    /// What a pattern node was checked against. Recorded for EVERY pattern,
    /// where `record_expr_type` refuses a synthetic span: nothing counts
    /// these, and lowering reads them for every pattern node, the
    /// desugarer's invented ones included -- each of which has a span of its
    /// own for exactly this reason.
    pub fn record_pat_type(&mut self, sp: crate::ast::Span, t: Ty) {
        self.pat_types.push((expr_type_key(sp), t));
    }

    /// The type a pattern node was checked against, or None. Sorted by
    /// `sort_expr_types` alongside the expression table.
    pub fn pat_type_at(&self, sp: crate::ast::Span) -> Option<&Ty> {
        let k = expr_type_key(sp);
        let i = self.pat_types.partition_point(|(e, _)| *e < k);
        self.pat_types.get(i).filter(|(e, _)| *e == k).map(|(_, t)| t)
    }

    /// Sorted ONCE at the check/lower boundary, where upstream sorts it
    /// (`TypeChecker.codex:2343`), so the lookups lowering does are a binary
    /// search rather than a scan per node.
    pub fn sort_expr_types(&mut self) {
        self.expr_types.sort_by_key(|(k, _)| *k);
        self.pat_types.sort_by_key(|(k, _)| *k);
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

    /// `occurs-in` (subject 46189). **THE CHECK THAT KEEPS THE SUBSTITUTION
    /// ACYCLIC**, and the reason `deep_resolve` terminates.
    ///
    /// Without it, `unify` will happily bind `Var(3) := List (Var 3)`.
    /// `resolve` survives that -- it is bounded and follows one chain -- but
    /// `deep_resolve` walks STRUCTURE, so it resolves the element, finds
    /// `Var(3)`, resolves it to `List (Var 3)` again, and runs until the stack
    /// ends. Nineteen corpus units aborted this way, sixteen of them
    /// `linear-*`, and the one named `infinite-type` is what the name says.
    ///
    /// **THE ARM LIST IS DELIBERATELY NARROW.** An arrow, a list, a type
    /// application and a linear wrapper are walked; a sum, a record, a
    /// constructed type, a vector and a unit are NOT. That is upstream's list
    /// and not an omission here -- a cycle through a named type's arguments
    /// is not built by the arms that bind.
    ///
    /// `max-recursion-depth` is 1024 and exhausting it answers TRUE: the
    /// budget is spent refusing, not accepting.
    fn occurs_in(&self, var_id: u32, t: &Ty, depth: usize) -> bool {
        if depth >= 1024 {
            return true;
        }
        match self.resolve(t) {
            Ty::Var(id) => id == var_id,
            Ty::Fun(p, _, r) => {
                self.occurs_in(var_id, &p, depth + 1) || self.occurs_in(var_id, &r, depth + 1)
            }
            Ty::List(e) | Ty::LinkedList(e) => self.occurs_in(var_id, &e, depth + 1),
            Ty::TypeApply(f, a) => {
                self.occurs_in(var_id, &f, depth + 1) || self.occurs_in(var_id, &a, depth + 1)
            }
            Ty::Linear(i) => self.occurs_in(var_id, &i, depth + 1),
            _ => false,
        }
    }

    /// `add-unify-error`. The code is `Cdx::*`, which is upstream's own number.
    pub fn error(&mut self, code: u16, message: impl Into<String>) {
        self.diags.push(Diag { code, message: message.into() });
    }

    /// What `check-errors` publishes.
    pub fn errors(&self) -> usize {
        self.diags.len()
    }

    /// **A CONFLICT BETWEEN TWO FULLY-CONCRETE, DIFFERENT-HEAD TYPES IS THE
    /// PROGRAM'S ERROR, NOT THE UNIFIER'S IGNORANCE.** A `false` out of `unify`
    /// otherwise means only "this partial unifier could not decide" -- which is
    /// true when a variable is involved. But `Integer` meeting `Text`, with no
    /// variable on either side, is not indecision: the types genuinely differ,
    /// and upstream reports `CDX2001`. Reported here so `check-errors` can say
    /// NO to an ill-typed program instead of emitting best-effort IR that only
    /// the interpreter or the plug then refuses.
    ///
    /// **ONLY A PRIMITIVE MEETING A DIFFERENT PRIMITIVE IS REPORTED.** Integer,
    /// Real, Text, Boolean and Char are the heads upstream's unifier has no
    /// reconciling arm for. Every other concrete pair stays a gap, because
    /// upstream reconciles pairs this unifier does not model: a unit type
    /// against its base (`infer-arithmetic`'s UnitTy arms), a vector mask
    /// against Boolean (`infer-comparison`), a constructed wrapper against
    /// its payload. Reporting those invented 68 CDX2001s over the 1,269-unit
    /// corpus on programs the oracle compiles clean. Two Integers of different
    /// RANGES are one head and are reconciled by range handling. The env
    /// `CDX_MEASURE_CONFLICTS` prints every primitive conflict so the count
    /// stays checkable.
    fn report_conflict(&mut self, a: &Ty, b: &Ty) {
        let (ra, rb) = (self.deep_resolve(a), self.deep_resolve(b));
        let (Some(ha), Some(hb)) = (primitive_head(&ra), primitive_head(&rb)) else {
            return;
        };
        if ha == hb {
            return;
        }
        if std::env::var_os("CDX_MEASURE_CONFLICTS").is_some() {
            eprintln!("CONCRETE-CONFLICT {ra:?} vs {rb:?}");
        }
        self.error(Cdx::TYPE_MISMATCH, "Type mismatch");
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
        // **`linear` IS TRANSPARENT TO UNIFICATION, ON BOTH SIDES.**
        // `unify-at` (subject 46401) strips it after resolving and before it
        // looks at anything, so `Var(269)` meeting `Linear (Var 269)` is two
        // equal variables rather than a variable meeting a type that contains
        // it. Without the strip the occurs check reads that as an infinite
        // type and refuses -- two false `Infinite type` errors on
        // `linear-smoke` and two on `serial-line`, which the oracle reports
        // clean.
        let a = strip_linear(self.resolve(a));
        let b = strip_linear(self.resolve(b));
        match (&a, &b) {
            // An error type has already been reported once. Unifying against
            // it succeeds so one unknown name does not cascade.
            (Ty::Error, _) | (_, Ty::Error) => true,
            (Ty::Var(i), Ty::Var(j)) if i == j => true,
            // **THE HIGHER ID BINDS TO THE LOWER**, and two variables need no
            // occurs check because neither can contain the other yet
            // (subject 46410). Binding left-to-right instead builds chains
            // upstream never has, and a later unify reads one of them as a
            // cycle: `linear-smoke` and `serial-line` each reported two
            // `Infinite type` errors the oracle does not, with every mint
            // counter already matching.
            (Ty::Var(i), Ty::Var(j)) => {
                if i < j {
                    self.bind_var(*j, a.clone());
                } else {
                    self.bind_var(*i, b.clone());
                }
                true
            }
            // **AN INFINITE TYPE IS REFUSED, NOT BUILT.** Both binding arms ask
            // first (subject 46415 and 46518), and a hit is `cdx-infinite-type`
            // -- an error the program earned, not a gap in this file.
            (Ty::Var(i), _) => {
                if self.occurs_in(*i, &b, 0) {
                    self.error(Cdx::INFINITE_TYPE, "Infinite type");
                    return false;
                }
                self.bind_var(*i, b.clone());
                true
            }
            (_, Ty::Var(j)) => {
                if self.occurs_in(*j, &a, 0) {
                    self.error(Cdx::INFINITE_TYPE, "Infinite type");
                    return false;
                }
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
            (Ty::List(x), Ty::List(y))
            | (Ty::List(x), Ty::LinkedList(y))
            | (Ty::LinkedList(x), Ty::List(y))
            | (Ty::LinkedList(x), Ty::LinkedList(y)) => {
                let (x, y) = (x.clone(), y.clone());
                self.unify(&x, &y)
            }
            // **A NAMED TYPE UNIFIES ARGUMENT BY ARGUMENT, AND THE THREE
            // SPELLINGS OF A NAME ARE INTERCHANGEABLE.** `unify-structural`
            // (Unifier.codex:606) matches `ConstructedTy`, `SumTy` and
            // `RecordTy` against each other on the NAME and then unifies their
            // arguments -- a declared `Maybe a` reaches the checker as a sum,
            // a written `Maybe SignalEntry` as a constructed type, and they
            // are the same type.
            //
            // Without this arm the two fell through to `a == b`, which is
            // false, and `Just`'s instantiated `a` was never told it stood for
            // `SignalEntry`. Every field of every destructure over a
            // parametric type stayed a `(tvar N)`: nothing contradicted it,
            // and nothing downstream could use it.
            (Ty::Sum(n1, a1), Ty::Sum(n2, a2))
            | (Ty::Record(n1, a1), Ty::Record(n2, a2))
            | (Ty::Constructed(n1, a1), Ty::Constructed(n2, a2))
            | (Ty::Constructed(n1, a1), Ty::Sum(n2, a2))
            | (Ty::Sum(n1, a1), Ty::Constructed(n2, a2))
            | (Ty::Constructed(n1, a1), Ty::Record(n2, a2))
            | (Ty::Record(n1, a1), Ty::Constructed(n2, a2)) => {
                if n1 != n2 {
                    self.report_conflict(&a, &b);
                    return false;
                }
                let (a1, a2) = (a1.clone(), a2.clone());
                a1.iter().zip(a2.iter()).fold(true, |ok, (x, y)| self.unify(x, y) && ok)
            }
            (Ty::Effectful(e1, _, r1), Ty::Effectful(e2, _, r2)) => {
                if e1 != e2 {
                    self.report_conflict(&a, &b);
                    return false;
                }
                let (r1, r2) = (r1.clone(), r2.clone());
                self.unify(&r1, &r2)
            }
            (Ty::Unit(n1, x), Ty::Unit(n2, y)) if n1 == n2 => {
                let (x, y) = (x.clone(), y.clone());
                self.unify(&x, &y)
            }
            (Ty::Vector(w1, x), Ty::Vector(w2, y)) if w1 == w2 || *w1 < 0 || *w2 < 0 => {
                let (x, y) = (x.clone(), y.clone());
                self.unify(&x, &y)
            }
            (Ty::TypeApply(f1, x1), Ty::TypeApply(f2, x2)) => {
                let (f1, x1, f2, x2) = (f1.clone(), x1.clone(), f2.clone(), x2.clone());
                self.unify(&f1, &f2) && self.unify(&x1, &x2)
            }
            // A quantifier on either side is transparent to unification --
            // upstream recurses on the body without instantiating.
            (Ty::ForAll(_, x), _) | (Ty::ForAllEff(_, x), _) | (Ty::Linear(x), _) => {
                let (x, b) = (x.clone(), b.clone());
                self.unify(&x, &b)
            }
            (_, Ty::ForAll(_, y)) | (_, Ty::ForAllEff(_, y)) | (_, Ty::Linear(y)) => {
                let (a, y) = (a.clone(), y.clone());
                self.unify(&a, &y)
            }
            _ => {
                if a != b {
                    self.report_conflict(&a, &b);
                }
                a == b
            }
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
/// **THE CHAPTER'S OWN TYPE NAMES, AND WHAT A RECORD'S FIELDS ARE.**
///
/// `resolve-type-name tdm name` (TypeChecker.codex:13) looks a bare type name
/// up in this map; without it `Rgb` resolves to a bare type constructor, a
/// field access on it finds no field, and the fallback in `infer-expr`'s
/// `AFieldAccess` arm mints a fresh variable for every one -- 88 of them on
/// `encode-qoi`'s unit alone.
///
/// BUILT IN TWO PASSES, because a field's type may name another declaration:
/// the shells first, then the fields against them.
#[derive(Default)]
pub struct TypeDefs {
    by_name: std::collections::BTreeMap<Sym, Ty>,
    fields: std::collections::BTreeMap<Sym, Vec<(Sym, Ty)>>,
}

impl TypeDefs {
    pub fn new(ch: &crate::ast::Chapter) -> TypeDefs {
        use crate::ast::TypeDef;
        let mut td = TypeDefs::default();
        for d in &ch.type_defs {
            let (n, params, is_record) = match d {
                TypeDef::Record(n, ps, ..) => (n, ps, true),
                TypeDef::Variant(n, ps, ..) => (n, ps, false),
                // `build-type-def-map`'s `AUnitTypeDef` arm (subject 51723)
                // binds `UnitTy name <resolved base>`. **A UNIT IS NOT ITS
                // BASE AND IT IS NOT A BARE NAME**: binding `TypeCon` lost the
                // base entirely, so a field access through a unit wrapper
                // could not be told from one through a record, and CDX2095 had
                // nothing to fire on. Resolved against the map SO FAR, which
                // is upstream's partial accumulator.
                TypeDef::Unit(n, base, _) => {
                    let inner = resolve_declared(&ch.syms, &td, base).unwrap_or(Ty::Error);
                    td.by_name.insert(*n, Ty::Unit(*n, Box::new(inner)));
                    continue;
                }
            };
            // `build-type-def-map`'s `ty-args` are `ConstructedTy p []`, not
            // `TypeCon`. The two are the same thing to `param_walk`, and only
            // one of them is what the wire spells for an UNparameterised
            // reference to a generic record: `qsort-by` said `(tycon "a")`
            // where the oracle says the substituted variable.
            let args: Vec<Ty> = params.iter().map(|p| Ty::Constructed(*p, Vec::new())).collect();
            td.by_name
                .insert(*n, if is_record { Ty::Record(*n, args) } else { Ty::Sum(*n, args) });
        }
        for d in &ch.type_defs {
            let TypeDef::Record(n, _, fs, ..) = d else { continue };
            let fields = fs
                .iter()
                .filter_map(|f| Some((f.name, resolve_declared(&ch.syms, &td, &f.type_expr)?)))
                .collect();
            td.fields.insert(*n, fields);
        }
        td
    }

    /// The chapter's type declarations by name -- `build-type-def-map`, which
    /// the RESOLVE pass reads.
    pub fn declared(&self) -> &std::collections::BTreeMap<Sym, Ty> {
        &self.by_name
    }

    /// The type of one field of one record, or None where the name is not a
    /// record this chapter declares.
    pub fn field(&self, rec: Sym, field: Sym) -> Option<&Ty> {
        self.fields.get(&rec)?.iter().find(|(n, _)| *n == field).map(|(_, t)| t)
    }

    /// A record's fields in declaration order -- the mutable walk asks whether
    /// any of them reaches a mutable record, and `Ty::Record` does not carry
    /// them.
    pub fn record_fields(&self, rec: Sym) -> Option<&[(Sym, Ty)]> {
        self.fields.get(&rec).map(|f| f.as_slice())
    }

    /// Its SLOT, which the wire spells alongside the name: a field access is
    /// `(field-access OBJ "py/1" text)`, and the number is the field's position
    /// in the DECLARATION -- not in the expression that built the record.
    pub fn field_index(&self, rec: Sym, field: Sym) -> Option<usize> {
        self.fields.get(&rec)?.iter().position(|(n, _)| *n == field)
    }
}

pub fn resolve_declared(
    syms: &SymTab,
    tds: &TypeDefs,
    t: &crate::ast::TypeExpr,
) -> Option<Ty> {
    use crate::ast::TypeExpr as T;
    Some(match t {
        T::Named(n, _) => match syms.text(*n) {
            "Integer" => Ty::Integer(i64::MIN, i64::MAX, Overflow::Error),
            "Text" => Ty::Text,
            "Boolean" => Ty::Boolean,
            "Char" => Ty::Char,
            "Nothing" => Ty::Nothing,
            "Real" => Ty::Real(RealWidth::F64, RealMode::Default),
            "Proof" => Ty::Proof,
            // A name this chapter DECLARES resolves to what it declared.
            _ => tds.by_name.get(n).cloned().unwrap_or(Ty::TypeCon(*n)),
        },
        // **A CLAIM'S TYPE RESOLVES, AND IF IT DOES NOT THE DEFINITION MINTS.**
        // `claim flip-on : flip On === Off` declares a type; with no arm for
        // it `resolve_declared` answered None, `register_all_defs` fell
        // through to `st.fresh()`, and every `proof` in the chapter cost a
        // type variable upstream never spends -- exactly the +4 on
        // `normalize-eq`, which has four of them.
        //
        // `resolve-type-expr` is TOTAL upstream and answers `ErrorTy` for a
        // side it cannot resolve, so neither side may propagate a None here.
        T::PropEq(l, r, _) => Ty::PropEq(
            Box::new(resolve_declared(syms, tds, l).unwrap_or(Ty::Error)),
            Box::new(resolve_declared(syms, tds, r).unwrap_or(Ty::Error)),
        ),
        // `for all (xs : Lst a), ...` is flatly `ProofTy` -- upstream does not
        // look inside it (TypeChecker.codex:26).
        T::Forall(..) => Ty::Proof,
        // `Integer between 0 and 255` -- a record field's usual shape. Without
        // this arm every such field failed to resolve and the record was left
        // with no fields at all.
        T::BoundedInt(_, lo, hi, mode, _) => Ty::Integer(
            *lo,
            *hi,
            match mode {
                crate::ast::OverflowMode::Error => Overflow::Error,
                crate::ast::OverflowMode::Wrapping => Overflow::Wrapping,
                crate::ast::OverflowMode::Clamping => Overflow::Clamping,
            },
        ),
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
            let arg = Box::new(resolve_declared(syms, tds, a)?);
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
                    Box::new(resolve_declared(syms, tds, inner)?),
                ),
                _ => Ty::Fun(arg, EffectRow::default(), Box::new(resolve_declared(syms, tds, b)?)),
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
            Box::new(resolve_declared(syms, tds, inner)?),
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
                args.iter().map(|a| resolve_declared(syms, tds, a)).collect::<Option<_>>()?;
            resolve_applied(syms, *n, &args, rendered)
        }
        T::Linear(inner, _) => Ty::Linear(Box::new(resolve_declared(syms, tds, inner)?)),
        _ => return None,
    })
}

/// `resolve-applied-type` (TypeChecker.codex:63). **FOUR NAMES ARE NOT
/// CONSTRUCTORS**, and the wire spells each of them its own way: `List`,
/// `LinkedList`, `Real` and `Vector`.
///
/// `LinkedList` missing from here spelled 99 definitions of the compiler
/// `(ctd "LinkedList" (args T))` where every gold says `(llist T)` -- it is
/// the same shape as `List`, one arm below it, and the two are not
/// interchangeable anywhere else in the pipeline either.
///
/// The wrong-arity cases answer the CONTAINER with `ErrorTy` inside rather
/// than falling through to a constructor, so `List a b` stays a list.
fn resolve_applied(syms: &SymTab, n: Name, args: &[&crate::ast::TypeExpr], rendered: Vec<Ty>) -> Ty {
    match (syms.text(n), rendered.as_slice()) {
        ("List", [only]) => Ty::List(Box::new(only.clone())),
        ("List", _) => Ty::List(Box::new(Ty::Error)),
        ("LinkedList", [only]) => Ty::LinkedList(Box::new(only.clone())),
        ("LinkedList", _) => Ty::LinkedList(Box::new(Ty::Error)),
        ("Real", _) => resolve_real_quals(syms, n, args, rendered),
        // The length is a NAME, not a literal: `Vector 4 Real` parses `4` as
        // an identifier in type position, and its text is read as an integer.
        ("Vector", [_, elem]) => {
            let len = match args.first() {
                Some(crate::ast::TypeExpr::Named(w, _)) => {
                    crate::token::lit_text_to_integer(syms.text(*w))
                }
                _ => 0,
            };
            Ty::Vector(len, Box::new(elem.clone()))
        }
        ("Vector", _) => Ty::Vector(2, Box::new(Ty::Error)),
        _ => Ty::Constructed(n, rendered),
    }
}

/// `resolve-real-quals` (TypeChecker.codex:50). `Real approximate trapping` is
/// a Real, `Real a` is a constructor -- ONE argument that is not a qualifier
/// makes the whole application ordinary again.
fn resolve_real_quals(
    syms: &SymTab,
    n: Name,
    args: &[&crate::ast::TypeExpr],
    rendered: Vec<Ty>,
) -> Ty {
    if args.is_empty() {
        return Ty::Real(RealWidth::F64, RealMode::Default);
    }
    let (mut w, mut m, mut all) = (RealWidth::F64, RealMode::Default, true);
    for a in args {
        match a {
            crate::ast::TypeExpr::Named(word, _) => match syms.text(*word) {
                "approximate" => w = RealWidth::F32,
                "trapping" => m = RealMode::Trapping,
                "saturating" => m = RealMode::Saturating,
                _ => all = false,
            },
            _ => all = false,
        }
    }
    if all {
        Ty::Real(w, m)
    } else {
        Ty::Constructed(n, rendered)
    }
}

/// `strip-linear-ty` (subject 36545). The type under any number of `linear`
/// wrappers.
fn strip_linear(t: Ty) -> Ty {
    match t {
        Ty::Linear(inner) => strip_linear(*inner),
        other => other,
    }
}

/// `strip-forall-ty`: the body of a quantifier chain, with its ORIGINAL ids.
/// Not an instantiation -- the point of the tie is to meet the signature's own
/// variables, not fresh ones.
pub fn strip_forall(t: &Ty) -> Ty {
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
/// `build-undeclared-fun-type` (TypeChecker.codex:48787). The shape a
/// definition with no signature is checked against: a fresh variable for the
/// result, and one arrow per parameter.
///
/// **ONLY THE INNERMOST ARROW CARRIES A ROW**, and the parameters are minted
/// from the LAST one backwards -- `build-fun-type-loop` wraps the spine
/// outward with empty rows. The ids reach the wire as `(tvar N)`, so the order
/// is as load-bearing as the count.
/// `last-arrow-row`: the row on the arrow that RETURNS THE BODY, which for an
/// undeclared definition is the only arrow carrying an open row -- the ones
/// wrapped around it carry `empty-row`.
fn last_arrow_row(t: &Ty) -> EffectRow {
    match t {
        Ty::Fun(_, row, r) => match r.as_ref() {
            Ty::Fun(..) => last_arrow_row(r),
            _ => row.clone(),
        },
        _ => EffectRow::default(),
    }
}

fn build_undeclared_fun_type(st: &mut UnifyState, pcount: usize) -> Ty {
    let body = st.fresh();
    if pcount == 0 {
        return body;
    }
    let row = EffectRow { id: st.fresh_row(), ..Default::default() };
    let last = st.fresh();
    let mut acc = Ty::Fun(Box::new(last), row, Box::new(body));
    for _ in 0..pcount - 1 {
        let p = st.fresh();
        acc = Ty::Fun(Box::new(p), EffectRow::default(), Box::new(acc));
    }
    acc
}

pub fn register_defs(
    ch: &crate::ast::Chapter,
    tds: &TypeDefs,
    st: &mut UnifyState,
) -> Vec<Binding> {
    let mut out = register_ctors(ch, tds, st);
    // `register-effect-ops-of` (subject 50004). **AN EFFECT OPERATION IS A
    // NAME LIKE ANY OTHER**, and we bound none of them: `ch.effect_defs` was
    // read by nothing in this file, so `read-text d` in a chapter that
    // declares its own effect typed as an unknown name and minted nothing --
    // two rows short per call, across ten corpus units. The subject's effects
    // are builtins, which is why the self-host never showed it.
    //
    // **A NAME ALREADY BOUND WINS**, and the operation is skipped rather than
    // overwriting it; upstream raises CDX3001 for that collision elsewhere.
    for ed in &ch.effect_defs {
        for op in &ed.ops {
            if out.iter().any(|b| b.name == op.name) {
                continue;
            }
            if let Some(t) = resolve_declared(&ch.syms, tds, &op.type_expr) {
                out.push(Binding { name: op.name, ty: parameterize(&t, &ch.syms, st) });
            }
        }
    }
    for d in &ch.defs {
        let ty = match d.declared_type.first().and_then(|t| resolve_declared(&ch.syms, tds, t)) {
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
/// **A RECORD IS ITS OWN CONSTRUCTOR, AND IT IS PARAMETERISED TOO.** It costs
/// one fresh variable per distinct type parameter -- `R (a) (b) = record { x :
/// a, y : b }` costs two, `R = record { a : Integer }` costs none -- which is
/// the same rule a variant's constructors follow. Measured on `codexcheck`;
/// the note that stood here said a record declared no function and needed its
/// own probe, and this is that probe's answer.
///
/// So in both shapes it is exactly the CONSTRUCTORS that parameterise: a
/// variant's arms, and a record's single one, which is named after the type.
fn register_ctors(ch: &crate::ast::Chapter, tds: &TypeDefs, st: &mut UnifyState) -> Vec<Binding> {
    use crate::ast::TypeDef;
    let mut out = Vec::new();
    for td in &ch.type_defs {
        let (name, params, ctors) = match td {
            TypeDef::Variant(n, ps, cs, _) => (n, ps, cs),
            // **A RECORD'S NAME IS BOUND TO ITS CONSTRUCTOR ARROW**, not to
            // the record type: `build-record-ctor-type` folds the fields into
            // `f1 -> f2 -> ... -> R`, and `ARecordExpr` instantiates that to
            // get the field types. Binding the RecordTy itself reads back as
            // `rec:R` where the oracle says `fn`.
            TypeDef::Record(n, ps, fields, ..) => {
                let result = Ty::Record(*n, ps.iter().map(|p| Ty::TypeCon(*p)).collect());
                let ty = fields.iter().rev().fold(result, |acc, f| {
                    match resolve_declared(&ch.syms, tds, &f.type_expr) {
                        Some(a) => Ty::Fun(Box::new(a), EffectRow::default(), Box::new(acc)),
                        None => acc,
                    }
                });
                out.push(Binding { name: *n, ty: parameterize(&ty, &ch.syms, st) });
                continue;
            }
            // **A UNIT'S NAME IS ITS CONSTRUCTOR ARROW TOO**, and unlike a
            // record's it is NOT parameterised: `register-one-type-def`'s
            // `AUnitTypeDef` arm (subject 51788) is one `FunTy` and no
            // `parameterize-type`, so it mints nothing. Skipping it left
            // `Spot (Point { .. })` typing as a fresh variable, which is why
            // no field access through a unit wrapper could be recognised.
            TypeDef::Unit(n, base, _) => {
                if let Some(inner) = resolve_declared(&ch.syms, tds, base) {
                    out.push(Binding {
                        name: *n,
                        ty: Ty::Fun(
                            Box::new(inner.clone()),
                            EffectRow::default(),
                            Box::new(Ty::Unit(*n, Box::new(inner))),
                        ),
                    });
                }
                continue;
            }
        };
        // **A VARIANT WITH NO TYPE PARAMETERS ANSWERS THE SUM ITSELF.**
        // `register-one-type-def`: `result-ty = if list-length type-params == 0
        // then sum-ty else ConstructedTy name (params)`. It is why a nullary
        // constructor of `CharClass` binds as `sum:CharClass` and not
        // `con:CharClass`.
        let args: Vec<Ty> = params.iter().map(|p| Ty::TypeCon(*p)).collect();
        // **THE TYPE NAME IS BOUND TO THE SUM, ALWAYS**, and is NOT
        // parameterised -- `Box (a) = | MkBox (a)` costs one variable, not two.
        out.push(Binding { name: *name, ty: Ty::Sum(*name, args.clone()) });
        // **WHAT A CONSTRUCTOR ANSWERS IS CONDITIONAL, AND THAT IS SEPARATE.**
        // `register-one-type-def`: `result-ty = if list-length type-params == 0
        // then sum-ty else ConstructedTy name (params)`. It is why a nullary
        // constructor of `CharClass` binds as `sum:CharClass` and a
        // constructor of `Maybe (a)` as `con:Maybe`.
        let result = if params.is_empty() {
            Ty::Sum(*name, Vec::new())
        } else {
            Ty::Constructed(*name, args)
        };
        for c in ctors {
            // Right to left: the spine is built inside out, so the first field
            // ends up the outermost argument.
            let mut ty = result.clone();
            for f in c.fields.iter().rev() {
                let Some(a) = resolve_declared(&ch.syms, tds, f) else { continue };
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

/// `arith-result-ty` (subject 52402). **THE RIGHT TYPE WINS WHEN IT IS
/// CONTAINED IN THE LEFT**, and otherwise the left does.
///
/// Upstream's own reason, and it is a good one: an arithmetic result used to
/// be the left operand's type verbatim, which made the judgement depend on the
/// order the author wrote the operands in. `b.val + 1` over a 0..255 byte kept
/// 0..255 and compiled; `1 + b.val` -- the same sum -- took the literal's type,
/// which is the full i64 range, and was rejected. Reporting that a byte plus
/// one might be nine quintillion is not a judgement anyone can act on.
///
/// **THIS IS THE CHECKER'S ANSWER, NOT THE IR NODE'S.** `binary-result-ty` in
/// lowering still answers the LEFT operand's type, and the two disagreeing is
/// deliberate: `let slot = spill-base + st.spill-count` emits `(let "slot"
/// int-default ...)` and every reference to `slot` inside it carries
/// `(int 0 65535 ov-error)`. Read off `codexir` over a six-case matrix.
/// The head of a primitive type, or `None` for anything a reconciling rule
/// upstream might still accept. See `report_conflict`.
fn primitive_head(t: &Ty) -> Option<&'static str> {
    match t {
        Ty::Integer(..) => Some("Integer"),
        Ty::Real(..) => Some("Real"),
        Ty::Text => Some("Text"),
        Ty::Boolean => Some("Boolean"),
        Ty::Char => Some("Char"),
        _ => None,
    }
}

fn arith_result_ty(lt: &Ty, rt: &Ty) -> Ty {
    let (Ty::Integer(l_lo, l_hi, _), Ty::Integer(r_lo, r_hi, _)) = (lt, rt) else {
        return lt.clone();
    };
    if r_lo == l_lo && r_hi == l_hi {
        return lt.clone();
    }
    if r_lo >= l_lo && r_hi <= l_hi {
        rt.clone()
    } else {
        lt.clone()
    }
}

/// `lint-record-set` / `bind-record-set-value` (subject 52828), value side.
///
/// `f` is the applied function -- for the value argument that is
/// `__record-set obj "field"` -- and `ret` is the whole application's type,
/// which is the record's.
fn bind_record_set_value(
    f: &crate::ast::Expr,
    value_ty: &Ty,
    ret: &Ty,
    env: &TyEnv<'_>,
    st: &mut UnifyState,
) {
    use crate::ast::Expr as E;
    let E::Apply(inner, field_arg, _) = f else { return };
    let E::Apply(head, _, _) = &**inner else { return };
    let E::NameRef(n, _) = &**head else { return };
    if env.syms.text(*n) != "__record-set" {
        return;
    }
    let E::Lit(field, crate::ast::LiteralKind::TextLit, _) = &**field_arg else { return };
    let Some(fname) = env.syms.find(field) else { return };
    // `lookup-field-ty-for-lint`, over the RETURN type: the record being
    // written into.
    let field_ty = match st.deep_resolve(ret) {
        Ty::Record(rn, _) => env.type_defs.field(rn, fname).cloned(),
        Ty::Constructed(cn, cargs) => constructed_field(env, cn, &cargs, fname),
        _ => None,
    };
    let Some(ft) = field_ty else { return };
    if !crate::lowering_types::has_typevars(&st.deep_resolve(value_ty)) {
        return;
    }
    if !st.unify(&ft, value_ty) {
        st.unify_gaps += 1;
    }
}

/// `resolve-constructed-to-record` + `lookup-record-field` +
/// `apply-type-args-subst` (subject 53644), as one lookup.
///
/// The record's own type arguments and its field types have to be the SAME
/// variables for the substitution to mean anything, and the only place they
/// are is the record CONSTRUCTOR the environment holds: `parameterize-type`
/// walked the whole arrow at registration, so its i-th argument is the i-th
/// field's type and its result carries the matching arguments.
pub fn instantiate_field(ctor: &Ty, idx: usize, cargs: &[Ty]) -> Option<Ty> {
    let mut spine = strip_forall(ctor);
    let mut field = None;
    let mut i = 0;
    while let Ty::Fun(a, _, r) = spine {
        if i == idx {
            field = Some(*a);
        }
        spine = *r;
        i += 1;
    }
    let Ty::Record(_, rargs) = spine else { return None };
    let mut out = field?;
    // `apply-type-args-subst`: only where the declaration's argument is a
    // variable is there anything to substitute.
    for (g, c) in rargs.iter().zip(cargs) {
        if let Ty::Var(id) = g {
            out = subst_type_var(&out, *id, c);
        }
    }
    Some(out)
}

fn constructed_field(env: &TyEnv<'_>, n: Name, cargs: &[Ty], f: Name) -> Option<Ty> {
    let idx = env.type_defs.field_index(n, f)?;
    instantiate_field(env.get(n)?, idx, cargs)
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
/// definition declares is `CDX3008 Undefined type name` instead.
///
/// Upstream spells it `char-code 'e' .. char-code 'z'` (TypeChecker.codex:551),
/// which reads like "e through z" and is not: **CCE IS FREQUENCY-ORDERED**, so
/// its lowercase band is `etaoinshrdlcumwfgypbvkjxqz` -- `e` is code 13, the
/// FIRST letter, and `z` is 38, the LAST. The range is the whole lowercase
/// band, named by its endpoints. Reading it as an alphabetical span says `a` is
/// excluded, which is wrong and disagrees with every probe.
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
        // A record and a sum carry their arguments the same way a constructed
        // type does, and a walk that stopped at them left a record's own
        // parameters unbound -- which is every `R (a) = record { x : a }` in
        // the depot.
        Ty::Record(n, args) => {
            Ty::Record(*n, args.iter().map(|a| param_walk(a, syms, st, entries)).collect())
        }
        Ty::Sum(n, args) => {
            Ty::Sum(*n, args.iter().map(|a| param_walk(a, syms, st, entries)).collect())
        }
        other => other.clone(),
    }
}

/// Register every definition, then infer every body.
///
/// TWO PASSES, and the order is upstream's: all names are bound before any
/// body is walked, which is what lets `fib` call itself. A one-pass checker
/// would find `fib` undefined inside its own body and mint a fresh variable
/// for it -- reaching a plausible answer with the wrong `next-id`.
/// **The zonk-and-default phase.** Run once at the end of each definition, it
/// resolves every type variable the definition minted and DEFAULTS the ones
/// inference left ambiguous, so no unresolved type reaches lowering or a plug.
///
/// "Ambiguous" here is precise: a variable minted while checking this
/// definition (`def_var_start .. next_id`) that is still free AND is not one
/// the definition's own type binds. A variable the type binds is a generic and
/// is kept -- lowering spells it and a plug emits it as a comptime parameter.
/// A variable the type does NOT bind is an ORPHAN: nothing observes it (an
/// empty list's element, an unread binding's type), so its concrete identity is
/// irrelevant and a concrete default is what lets a strict plug size it.
///
/// The default is `int-default`. With no type classes there is no
/// class-directed defaulting to be cleverer than that; a provably-unobserved
/// value can take any concrete type, and int-default is one every plug emits.
///
/// This is phase ONE only. A free variable the type DOES bind but that is not a
/// proper `ForAll` -- an undeclared polymorphic function, a generic lifted
/// closure -- is a GENERALISATION problem, not an ambiguity, and is left for
/// the plug/monomorphisation phase; defaulting it here would wrongly make a
/// polymorphic definition monomorphic.
fn default_ambiguous_vars(st: &mut UnifyState, def_var_start: u32, own_type: Option<&Ty>) {
    let mut generics = std::collections::BTreeSet::new();
    if let Some(t) = own_type {
        collect_type_vars(&st.deep_resolve(t), &mut generics);
    }
    let int_default = Ty::Integer(i64::MIN, i64::MAX, Overflow::Error);
    for v in def_var_start..st.next_id {
        if !generics.contains(&v) && st.resolve(&Ty::Var(v)) == Ty::Var(v) {
            if !st.unify(&Ty::Var(v), &int_default) {
                st.unify_gaps += 1;
            }
        }
    }
}

/// Every type-variable id that appears in a type. Used to learn a
/// definition's own generics from its instantiated type, so that defaulting an
/// unconstrained variable leaves the generics alone.
fn collect_type_vars(t: &Ty, out: &mut std::collections::BTreeSet<u32>) {
    match t {
        Ty::Var(id) => { out.insert(*id); }
        Ty::List(a) | Ty::LinkedList(a) | Ty::Vector(_, a) | Ty::Unit(_, a)
        | Ty::Linear(a) | Ty::ForAll(_, a) | Ty::ForAllEff(_, a) => collect_type_vars(a, out),
        Ty::Fun(a, _, b) | Ty::PropEq(a, b) | Ty::TypeApply(a, b) => {
            collect_type_vars(a, out);
            collect_type_vars(b, out);
        }
        Ty::Sum(_, xs) | Ty::Record(_, xs) | Ty::Constructed(_, xs) => {
            for x in xs { collect_type_vars(x, out); }
        }
        Ty::Effectful(_, _, a) => collect_type_vars(a, out),
        _ => {}
    }
}

pub fn check_chapter(ch: &crate::ast::Chapter) -> (Vec<Binding>, UnifyState) {
    let (bindings, st, _) = check_chapter_full(ch);
    (bindings, st)
}

/// The checker's three outputs, which is what `lower-chapter` is handed: the
/// bindings, the unification state, and the type declarations -- a field
/// access has to be able to read them.
pub fn check_chapter_full(ch: &crate::ast::Chapter) -> (Vec<Binding>, UnifyState, TypeDefs) {
    let mut st = UnifyState::default();
    let tds = TypeDefs::new(ch);
    let bindings = register_defs(ch, &tds, &mut st);
    // Builtins first, then the chapter's own names on top: a chapter that
    // defines `max` shadows the builtin, which the golds show for that name.
    let mut env = builtin_env(&ch.syms, &tds);
    // Collected during the walk and appended after it, so a lookup by name
    // finds the instantiated type rather than the generalised one.
    // The registry the linear walk asks one question of: is the callee's k-th
    // parameter declared linear? It wants the REGISTERED type -- the one that
    // still carries the `linear` wrapper the author wrote -- so it is built
    // before the loop appends the instantiated ones.
    let lin_bindings: std::collections::BTreeMap<Sym, Ty> =
        bindings.iter().map(|b| (b.name, b.ty.clone())).collect();
    // `register-mutable-markers`: the `mutable` keyword the author wrote is on
    // the type declaration and nowhere else, so the walk that needs it has to
    // be handed it. Upstream binds a `"__mutable-" & name` marker into the type
    // environment; a set of names is the same fact without the string surgery.
    let mutables: std::collections::BTreeSet<Sym> = ch
        .type_defs
        .iter()
        .filter_map(|d| match d {
            crate::ast::TypeDef::Record(n, _, _, true, _) => Some(*n),
            _ => None,
        })
        .collect();
    let mut per_def: Vec<Binding> = Vec::new();
    for b in &bindings {
        env.bind(b.name, b.ty.clone());
    }
    for d in &ch.defs {
        // The first type-variable id this definition mints, so its own
        // unconstrained variables can be told from earlier definitions'.
        let def_var_start = st.next_id;
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
        // **A DEFINITION THAT DECLARES NOTHING IS BUILT A SHAPE, NOT HANDED
        // ITS REGISTRATION.** `resolve-declared-type` (TypeChecker.codex:48765)
        // splits on `list-length (def.declared-type) == 0`: the declared side
        // instantiates the signature, and the undeclared side calls
        // `build-undeclared-fun-type`, which mints a SECOND variable for the
        // result and an arrow spine for the parameters. The registration
        // variable is then tied to it -- `check-def-normal`'s `linked-state`
        // unifies `env-lookup rn` against the expected type -- so the two
        // describe the same definition and only one of them is a mint we were
        // making.
        //
        // Reusing the registration variable was one mint short per undeclared
        // definition, and one row short per undeclared definition WITH
        // parameters. `ringplug-source.codex` has two of them, both nullary,
        // which is exactly its `next-id` -2 with its rows already exact.
        let instantiated = if d.declared_type.is_empty() {
            let t = build_undeclared_fun_type(&mut st, d.params.len());
            if let Some(o) = own.clone() {
                if !st.unify(&o, &t) {
                    st.unify_gaps += 1;
                }
            }
            Some(t)
        } else {
            own.clone().map(|t| st.instantiate(&t))
        };
        // **WHAT LOWERING SPELLS FOR THIS DEFINITION IS THIS TYPE, NOT THE
        // GENERALISED ONE.** `check-def-normal` answers
        // `inferred-type = declared.expected-type` -- the INSTANTIATED type --
        // and `check-all-defs` accumulates those into the bindings lowering is
        // handed. The `forall` lives in the environment, for references.
        //
        // The oracle shows it directly: `ident : List a -> List a` reaches the
        // wire as `(fn (list (tvar 2)) (list (tvar 2)))`, carrying the variable
        // its own body was checked with, and its parameter as `(list (tvar 2))`.
        // A `forall` has no arrow to peel, which is why every polymorphic
        // definition in the corpus refused with "more params than its type has
        // arrows".
        if let Some(t) = instantiated.clone() {
            per_def.push(Binding { name: d.name, ty: t });
        }
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
            // `bind-def-params`' `bound-ty = strip-linear-ty param-ty`
            // (subject 48817). **THE DISCIPLINE IS NOT PART OF THE TYPE.**
            // `linear Point` binds as `Point`, so every later question about
            // the value -- is it a record, what is this field -- is asked of
            // the type it actually has. Whether the parameter was declared
            // linear is read from the SYNTAX by `linearity::check_def`, which
            // is why stripping here costs that pass nothing.
            env.bind(p.name, strip_linear(arg));
        }
        let (body_ty, body_row) = infer_row(&d.body, &mut env, &mut st);
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
        if let (Some(Ty::ForAll(..) | Ty::ForAllEff(..)), Some(inst)) =
            (own.clone(), instantiated.clone())
        {
            let bare = strip_forall(&own.unwrap());
            if !st.unify(&inst, &bare) {
                st.unify_gaps += 1;
            }
        }
        // **`row-tied`: AN UNDECLARED DEFINITION LEARNS ITS EFFECT ROW FROM ITS
        // BODY** (`check-def-normal`). The arrow `build_undeclared_fun_type`
        // built carries an OPEN row variable and nothing had ever told it what
        // the body performs, so it stayed unbound -- and `unify_row` mints
        // when it has to give an open row a tail. One row short per undeclared
        // definition whose body performs an application; `f (x) = show x` was
        // 4 rows against the oracle's 5, and it needed BOTH a parameter (or
        // there is no arrow to carry a row) and a call (or the body's row is
        // empty and binding it costs nothing).
        if d.declared_type.is_empty() {
            if let Some(t) = &instantiated {
                let lr = last_arrow_row(t);
                if !st.unify_row(&lr, &body_row) {
                    st.unify_gaps += 1;
                }
            }
        }
        // `check-all-defs`'s `lin-st = check-linearity-def def fresh-env
        // (r.state)` -- after the body is checked, before the params come off.
        crate::linearity::check_def(
            d,
            &crate::linearity::LinEnv {
                syms: &ch.syms,
                bindings: &lin_bindings,
                tds: &tds,
                mutables: &mutables,
            },
            &mut st,
        );
        // The zonk-and-default phase for this definition. See
        // `default_ambiguous_vars`.
        default_ambiguous_vars(&mut st, def_var_start, instantiated.as_ref());
        for _ in saved {
            env.scope.pop();
        }
    }
    // The check/lower boundary, where upstream sorts too: everything below
    // this line looks entries up rather than appending them.
    st.sort_expr_types();
    let mut bindings = bindings;
    bindings.extend(per_def);
    (bindings, st, tds)
}

/// The `--- check ---` section, in the harness's own format so it can be
/// diffed against `$CODEX_GOLDS/rungs/check.truth` directly.
pub fn section(syms: &SymTab, bindings: &[Binding], st: &UnifyState) -> String {
    let mut s = String::from("--- check ---\n");
    s.push_str(&format!("check-errors {}\n", st.errors()));
    // The code travels with the count: a gate comparing only the number cannot
    // tell a right answer from a right total with the wrong diagnosis in it.
    for d in &st.diags {
        s.push_str(&format!("CDX{} {}\n", d.code, d.message));
    }
    s.push_str(&format!("type-bindings {}\n", bindings.len()));
    for b in bindings {
        // **RESOLVED, because the binding is not the answer.** A definition
        // that declares no type is registered with a fresh variable and
        // unification binds it afterwards -- `zig-p-cx-poke-32` is a list, and
        // printing the raw binding called it `tvar`. That made the two
        // definitions in `ringplug-source` that declare no type look like
        // checker disagreements when the checker had them right and only this
        // line was behind.
        s.push_str(&format!(
            "tb {} {}\n",
            syms.text(b.name),
            type_kind(syms, &st.deep_resolve(&b.ty))
        ));
    }
    s.push_str(".\n");
    s.push_str(&format!("substitutions {}\n", st.substitutions.len()));
    s.push_str(&format!("next-id {}\n", st.next_id));
    // THIS LINE ONLY: `CheckHarness.codex` prints it and
    // `$CODEX_GOLDS/rungs/check.truth` does not, because the bank predates the
    // row counter. `codexcheck` is the control for it. Nothing else in this
    // section is shaped to the oracle over the gold -- `type-bindings` above
    // disagrees with BOTH today, and that is a defect, not a choice.
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
    infer_row(e, env, st).0
}

/// The walk, carrying what upstream's `CheckResult` carries: the inferred type
/// AND the expression's ambient effect row.
///
/// **THE ROW IS NOT DECORATION -- ONE SITE CONSUMES IT.** `open-row-if-closed`
/// at a lambda mints a row id only when the body's row is closed, so a checker
/// with no row channel has to mint unconditionally and runs one ahead. Every
/// other reader of these rows is `row-union`, which never mints, so propagating
/// them is free in both counters.
///
/// **CLOSED AND EMPTY IS THE DEFAULT** because that is `empty-row`, what
/// upstream answers for a literal, a name and a lambda. An arm that forgets to
/// set `row` therefore behaves as this checker did before it existed.
pub fn infer_row(
    e: &crate::ast::Expr,
    env: &mut TyEnv<'_>,
    st: &mut UnifyState,
) -> (Ty, EffectRow) {
    use crate::ast::Expr as E;
    let mut row = EffectRow::default();
    let t = match e {
        E::Lit(_, crate::ast::LiteralKind::IntLit, _) => {
            Ty::Integer(i64::MIN, i64::MAX, Overflow::Error)
        }
        E::Lit(_, crate::ast::LiteralKind::TextLit, _) => Ty::Text,
        E::Lit(_, crate::ast::LiteralKind::BoolLit, _) => Ty::Boolean,
        // `infer-literal`: a NumLit is `real-f64`, a CharLit is `CharTy`.
        // Answering `Error` here typed every `let` whose value STARTS with
        // a real literal -- `if c then 0.0 else x`, `0.0 - x` -- as `error`,
        // and every later read of that name carried it to the wire.
        E::Lit(_, crate::ast::LiteralKind::NumLit, _) => Ty::Real(RealWidth::F64, RealMode::Default),
        E::Lit(_, crate::ast::LiteralKind::CharLit, _) => Ty::Char,
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
            // **AN EFFECTFUL NAME HANDS ITS ROW UP, AND THAT ROW IS CLOSED.**
            // `make-row-from-names` (TypeChecker.codex:29) builds the labels and
            // sets `tail-id = -1`, so a lambda whose body is a bare effectful
            // name still mints one at `open-row-if-closed`. Only an application
            // opens a row.
            let rec = match t {
                Ty::Effectful(effs, scopes, inner) => {
                    row = EffectRow {
                        labels: effs
                            .iter()
                            .enumerate()
                            .map(|(i, e)| {
                                (
                                    env.syms.text(*e).to_string(),
                                    scopes.get(i).cloned().unwrap_or_default(),
                                )
                            })
                            .collect(),
                        tail: String::new(),
                        id: -1,
                    };
                    *inner
                }
                other => other,
            };
            st.record_expr_type(*sp, rec.clone());
            return (rec, row);
        }
        // A comparison answers Boolean; arithmetic answers its operands'.
        // Neither mints, which is why fib's five applications are not the
        // whole of its next-id.
        E::Binary(l, op, r, sp) => {
            let (lt, lrow) = infer_row(l, env, st);
            let (rt, rrow) = infer_row(r, env, st);
            row = st.row_union(&lrow, &rrow);
            use crate::ast::BinaryOp::*;
            // **`&` RECORDS AN EXPRESSION TYPE; NO OTHER OPERATOR DOES.**
            // `infer-and` (TypeCheckerInference.codex:414) records the LEFT
            // operand's resolved type at the binary's own span, because `&` is
            // one token doing two jobs -- boolean AND and text append -- and
            // the recorded type is the only thing that separates them
            // afterwards. Upstream's own note: an unrecorded boolean `&` is
            // indistinguishable from an expression nothing knows the type of,
            // and every reader treats the absence as the worst case.
            //
            // The key is offset AND length, so this cannot collide with its
            // own left operand's entry.
            if matches!(op, OpAnd) {
                let resolved = st.resolve(&lt);
                st.record_expr_type(*sp, resolved);
            }
            match op {
                // **EVERY BINARY OPERATOR UNIFIES ITS OPERANDS.** A faithful
                // port of `infer-binary-op` (TypeCheckerInference), and the
                // unification is how earned knowledge crosses the operator.
                // `List Text & (for x in xs -> ...)` binds the comprehension's
                // element variable to `Text` HERE and nowhere else: the map
                // builtin instantiated a fresh variable for the hoisted
                // lambda's return, and only the append meets it against the
                // left. Answering a type without unifying left that variable
                // free -- one `map-list` result on the self-host wire spelled
                // `(tvar N)` where the oracle spells `text`.
                //
                // Not modelled here, because upstream adds them AROUND these
                // same functions and the subject exercises none on the wire:
                // the real-equality and text-ordering bans, `infer-comparison`
                // 's VectorMask result, and `infer-arithmetic`'s UnitTy arms.

                // `infer-comparison`: the operands MEET, the answer is Boolean.
                OpEq | OpNotEq | OpLt | OpGt | OpLtEq | OpGtEq | OpDefEq
                | OpApproxEq | OpApproxEqExact => {
                    if !st.unify(&lt, &rt) { st.unify_gaps += 1; }
                    Ty::Boolean
                }
                // `infer-logical`: both operands MEET Boolean.
                OpOr | OpBoolAnd => {
                    if !st.unify(&lt, &Ty::Boolean) { st.unify_gaps += 1; }
                    if !st.unify(&rt, &Ty::Boolean) { st.unify_gaps += 1; }
                    Ty::Boolean
                }
                // `infer-arithmetic`: the operands MEET, the answer is the
                // tighter of the two (`arith-result-ty`). The `UnitTy` arms are
                // not modelled here yet.
                OpAdd | OpSub | OpMul | OpDiv | OpPow => {
                    if !st.unify(&lt, &rt) { st.unify_gaps += 1; }
                    arith_result_ty(&st.resolve(&lt), &st.resolve(&rt))
                }
                // `infer-and`: `&` is three operators, dispatched on the
                // RESOLVED left type -- Boolean is `infer-logical`, Text and
                // everything else are `infer-append`. The recorded expression
                // type above is what separates them for later readers.
                OpAnd => match st.resolve(&lt) {
                    Ty::Boolean => {
                        if !st.unify(&lt, &Ty::Boolean) { st.unify_gaps += 1; }
                        if !st.unify(&rt, &Ty::Boolean) { st.unify_gaps += 1; }
                        Ty::Boolean
                    }
                    Ty::Text => {
                        if !st.unify(&rt, &Ty::Text) { st.unify_gaps += 1; }
                        Ty::Text
                    }
                    other => {
                        if !st.unify(&lt, &rt) { st.unify_gaps += 1; }
                        other
                    }
                },
                // `infer-append`: the append token minus `&`'s boolean route --
                // Text unifies the right with Text, a List unifies the two.
                OpAppend => match st.resolve(&lt) {
                    Ty::Text => {
                        if !st.unify(&rt, &Ty::Text) { st.unify_gaps += 1; }
                        Ty::Text
                    }
                    other => {
                        if !st.unify(&lt, &rt) { st.unify_gaps += 1; }
                        other
                    }
                },
                // `infer-cons`: `x :: xs` unifies the right with `List lt`.
                OpCons => {
                    let list_ty = Ty::List(Box::new(lt.clone()));
                    if !st.unify(&rt, &list_ty) { st.unify_gaps += 1; }
                    list_ty
                }
            }
        }
        // **THE TWO ARMS MEET, AND THE CONDITION MEETS `Boolean`.**
        // `infer-if` (subject 52454) unifies both, and neither mints -- but
        // without the arms meeting, a polymorphic constructor in one of them
        // never learns what it stands for: `if n > 0 then Just "x" else None`
        // left `None` as `Maybe (tvar 307)` where the oracle says `Maybe Text`.
        //
        // The answer is the THEN arm's, not the union.
        E::If(c, a, b, _) => {
            let (ct, crow) = infer_row(c, env, st);
            if !st.unify(&ct, &Ty::Boolean) {
                st.unify_gaps += 1;
            }
            let (ta, arow) = infer_row(a, env, st);
            let (tb, brow) = infer_row(b, env, st);
            if !st.unify(&ta, &tb) {
                st.unify_gaps += 1;
            }
            let both = st.row_union(&crow, &arow);
            row = st.row_union(&both, &brow);
            ta
        }
        // Mints a result variable and TWO row ids, after both halves are in.
        // The application's own row is minted by the name in function position
        // (see the NameRef arm); these two are the rest of the three an
        // application costs.
        E::Apply(f, a, _) => {
            let (ft, frow) = infer_row(f, env, st);
            let (at, arow) = infer_row(a, env, st);
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
                Box::new(at.clone()),
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
            //
            // **AN APPLICATION'S ROW IS OPEN, AND THAT IS WHY A LAMBDA OVER ONE
            // MINTS NOTHING.** The call row goes into the union last, exactly
            // as `infer-application` (line 644) does it.
            // **`__record-set obj "field" value` NAMES ITS FIELD WITH A TEXT
            // LITERAL**, so ordinary application inference has nothing to
            // unify an undetermined value against -- the builtin's own type is
            // `R -> Text -> a -> R` and `a` meets only the value itself.
            // `bind-record-set-value` (subject 52869) ties them, and ONLY
            // while the value still carries variables: a bounded-integer field
            // handed a wider integer is the narrowing lint's business and
            // unification would refuse it.
            bind_record_set_value(f, &at, &ret, env, st);
            let halves = st.row_union(&frow, &arow);
            row = st.row_union(&halves, &EffectRow { id: call_row, ..Default::default() });
            ret
        }
        // **A `<-` BINDS ITS NAME, AND THE REST OF THE BLOCK CAN SEE IT.**
        // `infer-act-loop`'s `AActBindStmt` arm (TypeChecker.codex:53555) is
        // `env-bind-local env (name.value) (deep-resolve acc-st
        // (er.inferred-type))` -- the same rule `let` follows, and for the same
        // reason: bound raw, the name is a variable nothing can read a record
        // or an arrow out of.
        //
        // Discarding the name cost seven variables on the self-host, all of
        // them a field access whose object was bound this way: `here <-
        // fat16-cluster-entry-sectors ...` then `here.li-entries`. The object
        // resolved to nothing, so `AFieldAccess` fell to its `fresh-and-advance`
        // branch where upstream looked the field up and minted nothing. That
        // was the whole of the 3.44 MB unit's remaining `next-id` gap.
        //
        // `er.inferred-type` is already the VALUE side -- `infer-name` hands an
        // effectful name's row up separately -- so there is no row to peel here.
        E::Act(stmts, _) => {
            let mut last = Ty::Nothing;
            let mut bound = 0;
            for s in stmts {
                match s {
                    crate::ast::ActStmt::Exec(x, _) => {
                        let (t, srow) = infer_row(x, env, st);
                        last = t;
                        row = st.row_union(&row, &srow);
                    }
                    crate::ast::ActStmt::Bind(n, x, _) => {
                        let (t, srow) = infer_row(x, env, st);
                        row = st.row_union(&row, &srow);
                        let resolved = st.deep_resolve(&t);
                        env.bind(*n, resolved);
                        bound += 1;
                        last = t;
                    }
                }
            }
            // The block's names are the block's: `infer-act-loop` threads `env2`
            // through its own loop and hands the caller none of it.
            for _ in 0..bound {
                env.scope.pop();
            }
            st.deep_resolve(&last)
        }
        E::Let(binds, body, _) => {
            // **A LET'S BINDINGS ARE SCOPED TO ITS BODY**, and forgetting to
            // unwind them is not a local mistake: `check_chapter_full` pops N
            // entries for a definition's N parameters, so k leaked bindings
            // leave k PARAMETERS bound for every definition after this one.
            // `build-all-names-scope (top-names) (ctor-names) (builtins)` did
            // exactly that, and five later references to the global `builtins`
            // got that parameter's `List Text` instead of `List BuiltinSpec`.
            let mark = env.scope.len();
            for b in binds {
                let (t, brow) = infer_row(&b.value, env, st);
                // **A LET BINDS THE DEEP-RESOLVED TYPE, NOT THE INFERRED ONE.**
                // `infer-let-bindings` (TypeCheckerInference.codex:504) resolves
                // before it binds, and the difference is not cosmetic: binding
                // `f = list-at ts 0` raw leaves a bare variable in the
                // environment, so the later `f 0` finds no arrow and
                // `open-spine-rows` mints nothing where upstream mints for the
                // spine it can now see.
                let resolved = st.deep_resolve(&t);
                env.bind(b.name, resolved);
                row = st.row_union(&row, &brow);
            }
            let (t, body_row) = infer_row(body, env, st);
            row = st.row_union(&row, &body_row);
            env.scope.truncate(mark);
            t
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
        E::Unary(x, _) | E::Lazy(x, _) => {
            let (t, xrow) = infer_row(x, env, st);
            row = xrow;
            t
        }
        // **AN EMPTY LIST MINTS ONE VARIABLE AND RECORDS IT; A NON-EMPTY ONE
        // MINTS NOTHING.** `[]` has no element to read a type from, so the
        // element type is a fresh variable that unification decides from the
        // context -- and lowering reads it back at this span to spell
        // `(list-expr (elems) int-default)`. Measured on `codexcheck`:
        // `f (x) = []` is next-id 3 and expr-types 1 where `f (x) = [x]` is 2
        // and 1, on a body with no names in it at all.
        E::List(xs, sp) => {
            // **AN EMPTY LIST IS A BARE VARIABLE, NOT A LIST OF ONE.**
            // `infer-list` (TypeCheckerInference.codex:1249) answers
            // `fr-ty` and records `fr-ty` -- so `[]` is whatever the context
            // makes it, INCLUDING a `LinkedList`. Answering `ListTy fr-ty`
            // instead pinned the element rather than the container, and
            // lowering could no longer tell the two apart: forty empty lists
            // in the compiler reached the wire as `(list-expr (elems) T)`
            // where the oracle calls `__linked-list-empty`.
            if xs.is_empty() {
                let e = st.fresh();
                st.record_expr_type(*sp, e.clone());
                return (e, EffectRow::default());
            }
            let mut elem = Ty::Error;
            for x in xs {
                let (t, erow) = infer_row(x, env, st);
                elem = t;
                row = st.row_union(&row, &erow);
            }
            Ty::List(Box::new(elem))
        }
        // `bind-lambda-params` mints one variable per parameter -- a lambda,
        // unlike a declared definition, has nowhere else to get them from.
        E::Lambda(params, body, sp) => {
            let mut arg_tys = Vec::with_capacity(params.len());
            for p in params {
                let a = st.fresh();
                env.bind(*p, a.clone());
                arg_tys.push(a);
            }
            let (ret, body_row) = infer_row(body, env, st);
            for _ in params {
                env.scope.pop();
            }
            // **AND ONE ROW, AFTER THE BODY -- BUT ONLY IF THE BODY'S IS
            // CLOSED.** `open-row-if-closed` (TypeCheckerInference.codex:529)
            // reuses an already-open row and mints only when there is no tail.
            // A body that is an APPLICATION is already open, because the
            // application minted a call row; a body that is a name or an
            // arithmetic operator is not. The parameters' type variables come
            // BEFORE the body and this comes after, so the two counters move at
            // different moments and the order is graded.
            let lam_row = st.open_row_if_closed(&body_row);
            // **`wrap-fun-type` CURRIES, AND ONLY THE INNERMOST ARROW CARRIES
            // THE ROW** (TypeCheckerInference.codex:571) -- the outer ones are
            // built by `wrap-fun-type-loop` with `empty-row`. A three-parameter
            // lambda is three arrows, not one: collapsing them to the last
            // parameter alone made `\acc ch idx -> ...` type as
            // `(fn int-default int-default)` where the wire wants
            // `(fn int-default (fn char (fn int-default int-default)))`.
            let mut t = ret;
            for (i, a) in arg_tys.into_iter().enumerate().rev() {
                let row = if i + 1 == params.len() { lam_row.clone() } else { EffectRow::default() };
                t = Ty::Fun(Box::new(a), row, Box::new(t));
            }
            st.record_expr_type(*sp, t.clone());
            // A lambda's OWN ambient row is empty: the effects are the arrow's,
            // not the surrounding expression's (`infer-lambda`, line 543).
            return (t, EffectRow::default());
        }
        // **A MATCH MINTS ONE VARIABLE FOR ITS RESULT, AND THAT VARIABLE IS
        // ITS TYPE.** `infer-match` (TypeCheckerInference.codex:1305) mints it
        // straight after the scrutinee and before any arm, then unifies every
        // arm into it -- so the match answers the variable, not the last arm.
        // One per MATCH, not per arm and not per pattern variable: a two-field
        // destructure and a three-field one both cost the same one.
        // **AN INDUCTION PROOF IS WALKED LIKE A MATCH, AND THAT IS NOT WHAT
        // `infer-expr` DOES -- but it is what the COUNTERS say.**
        //
        // `infer-expr`'s `AInductionExpr` arm
        // (TypeCheckerInference.codex:1770) answers `ProofTy`, bags
        // `cdx-induction-unverified`, and returns the state untouched: it
        // mints nothing. Copying that faithfully made `induction-param` and
        // `induction-parse` mint FIVE type variables and THREE rows too FEW,
        // and the missing rows are visible on the wire -- their `opening`
        // came out with `Console.Write` row 466 where the oracle writes 469.
        //
        // The minting happens in a second pass we do not have:
        // `check-induction-def` -> `check-induction-ctors` ->
        // `check-induction-arm` (TypeChecker.codex:2845), the Stage 5 proof
        // system, which binds the forall's value binders and checks one
        // subgoal per constructor. Walking the arms as a match is not that
        // pass, but it happens to spend the same rows.
        //
        // **SO THIS IS A KNOWN APPROXIMATION, KEPT BECAUSE IT IS CLOSER.**
        // The residual is uniform -- next-id +4, expr-types +1 on both units
        // -- which is the shape a missing subsystem leaves, and the honest
        // fix is to implement it rather than to tune this arm.
        E::Match(scrut, arms, _) | E::Induction(scrut, arms, _) => {
            let (scrut_ty, srow) = infer_row(scrut, env, st);
            row = srow;
            let result = st.fresh();
            for a in arms {
                // The SCRUTINEE'S type, not nothing: `infer-plain-arm` passes
                // `scrut-ty` down, and that is what makes a destructured
                // field concrete instead of a variable.
                let bound = bind_pattern(&a.pattern, &scrut_ty, env, st);
                let (_, grow) = infer_row(&a.guard, env, st);
                row = st.row_union(&row, &grow);
                let (arm_ty, arow) = infer_row(&a.body, env, st);
                row = st.row_union(&row, &arow);
                if !st.unify(&arm_ty, &result) {
                    st.unify_gaps += 1;
                }
                for _ in 0..bound {
                    env.scope.pop();
                }
            }
            result
        }
        // A record literal is the other site `record-expr-type` is populated
        // from (Unifier.codex:131).
        //
        // **IT INSTANTIATES THE RECORD'S OWN CONSTRUCTOR BEFORE IT LOOKS AT A
        // FIELD.** `ARecordExpr` (TypeCheckerInference.codex:1678) reads the
        // name out of the environment, instantiates it, and only then infers
        // the field values -- so a record carrying a type parameter costs one
        // fresh variable at every USE, not just at its declaration. What is
        // recorded at the span is the RESULT type, the constructor's arrows
        // peeled off.
        E::Record(n, fields, sp) => {
            let raw = env.get(*n).cloned().unwrap_or(Ty::Error);
            let inst = st.instantiate(&raw);
            // **THE EXPECTED FIELD TYPES ARE THE INSTANTIATED CONSTRUCTOR'S
            // ARGUMENTS, NOT THE DECLARED TABLE'S.** A record with a type
            // parameter has a different field type at every use, and the
            // constructor is the only place that difference exists: its arrow
            // chain was just instantiated, `TypeDefs` still holds `a`.
            // Argument i of the chain is field i of the DECLARATION, which is
            // what `field_index` answers -- the expression may name them in any
            // order.
            let mut declared = Vec::new();
            let mut result = inst;
            while let Ty::Fun(a, _, r) = result {
                declared.push(*a);
                result = *r;
            }
            let rec_name = match &result {
                Ty::Record(rn, _) | Ty::Constructed(rn, _) | Ty::Sum(rn, _) => *rn,
                _ => *n,
            };
            for f in fields {
                let (ft, frow) = infer_row(&f.value, env, st);
                // **AND THIS IS WHERE AN EMPTY LIST LEARNS ITS ELEMENT TYPE.**
                // `infer-and-unify-record-fields` (line 1996) unifies each value
                // against its field's type. Without it `R { tags = [] }` reaches
                // the IR as `(list-expr (elems) (tvar 352))` where upstream
                // spells `text`: the fresh variable the empty list minted is
                // never told what it is.
                if let Some(want) =
                    env.type_defs.field_index(rec_name, f.name).and_then(|i| declared.get(i))
                {
                    let want = want.clone();
                    if !st.unify(&ft, &want) {
                        st.unify_gaps += 1;
                    }
                }
                row = st.row_union(&row, &frow);
            }
            st.record_expr_type(*sp, result.clone());
            return (result, row);
        }
        // `infer-expr`'s `AFieldAccess` arm (TypeCheckerInference.codex:1629)
        // falls to `fresh-and-advance` for a receiver that is not a record --
        // including a bare type variable and a variant.
        E::FieldAccess(r, f, _) => {
            let obj = infer(r, env, st);
            // **A SUCCESSFUL LOOKUP MINTS NOTHING.** The arm looks the field up
            // when the object resolves to a record and falls to
            // `fresh-and-advance` in every other case; minting either way put
            // 88 extra variables on `encode-qoi`'s unit, one per field access
            // in the two chapters that declare records.
            // **A CONSTRUCTED RECEIVER INSTANTIATES THE FIELD.**
            // `SortPartition a` reached here as a `ConstructedTy` carrying the
            // caller's own argument, and reading the DECLARED field type past
            // it answered `List a` with `a` still the declaration's name --
            // which then unified with the enclosing definition's type variable
            // and pinned it. `qsort-by`'s four parameters spelled
            // `(tycon "a")` where the oracle spells `(tvar 28)`.
            //
            // A `RecordTy` receiver already carries its own arguments and
            // upstream reads the field straight out of it, with no
            // substitution -- the two arms are not the same rule.
            //
            // **A FIELD THE RECORD DOES NOT HAVE IS AN ERROR, NOT A FRESH
            // VARIABLE.** Upstream answers `ErrorTy` and raises CDX2005; we
            // minted, which both hid the defect and moved `next-id` by one per
            // occurrence. Same for a UNIT receiver, which has no fields at all
            // -- the wrapper is a distinct type -- and answers CDX2095.
            // Everything else, a bare type variable and a variant included,
            // still falls to `fresh-and-advance`.
            let name = env.syms.text(*f).to_string();
            match st.deep_resolve(&obj) {
                Ty::Record(n, _) => match env.type_defs.field(n, *f).cloned() {
                    Some(t) => t,
                    None => {
                        st.error(Cdx::UNKNOWN_RECORD_FIELD, format!(
                            "Record type has no field '{name}'"));
                        Ty::Error
                    }
                },
                // A CONSTRUCTED RECEIVER THAT IS NOT A RECORD IS NOT AN ERROR:
                // the two failures look alike from `constructed_field` and are
                // not the same, so the record has to be resolved first.
                Ty::Constructed(n, cargs) => match env.type_defs.declared().get(&n) {
                    Some(Ty::Record(..)) => match constructed_field(env, n, &cargs, *f) {
                        Some(t) => t,
                        None => {
                            st.error(Cdx::UNKNOWN_RECORD_FIELD, format!(
                                "Record type '{}' has no field '{name}'", env.syms.text(n)));
                            Ty::Error
                        }
                    },
                    _ => st.fresh(),
                },
                Ty::Unit(n, _) => {
                    st.error(Cdx::FIELD_ON_UNIT_TYPE, format!(
                        "'{}' is a unit type, not a record: the wrapper is a distinct type of its own and has no field '{name}'. A unit over a record has no accessor and is not accepted where the record is expected, so the field cannot be reached through it -- use the record directly, or declare the unit over a primitive",
                        env.syms.text(n)));
                    Ty::Error
                }
                _ => st.fresh(),
            }
        }
        // **A STORE EVALUATES TO THE RECORD IT WROTE INTO**, and the value is
        // MET AGAINST THE FIELD'S DECLARED TYPE. Answering `Nothing` and
        // unifying nothing left a polymorphic value uninstantiated:
        // `st.dirty-slots = __list-with-capacity 4096` reached the wire as
        // `(list (tvar 84988))` where the field says `List Integer`.
        E::FieldAssign(r, f, v, _) => {
            let obj = infer(r, env, st);
            let vt = infer(v, env, st);
            let name = env.syms.text(*f).to_string();
            // The assign side asks the same question of the receiver as the
            // access side (subject 53722): a UNIT wrapper is a distinct type
            // with no fields, and the field cannot be reached through it.
            let field_ty = match st.deep_resolve(&obj) {
                Ty::Record(n, _) => env.type_defs.field(n, *f).cloned(),
                Ty::Constructed(n, cargs) => constructed_field(env, n, &cargs, *f),
                Ty::Unit(n, _) => {
                    st.error(Cdx::FIELD_ON_UNIT_TYPE, format!(
                        "'{}' is a unit type, not a record: the wrapper is a distinct type of its own and has no field '{name}'. A unit over a record has no accessor and is not accepted where the record is expected, so the field cannot be reached through it -- use the record directly, or declare the unit over a primitive",
                        env.syms.text(n)));
                    None
                }
                _ => None,
            };
            if let Some(ft) = field_ty {
                if !st.unify(&vt, &ft) {
                    st.unify_gaps += 1;
                }
            }
            obj
        }
        // `infer-handle-clauses` (subject). **A CLAUSE BINDS ITS PARAMETERS
        // AND ITS RESUME**, and both mint: `bind-lambda-params` one per
        // parameter, then one more for the resume continuation. Binding
        // nothing left `resume` an unknown name, so the wire spelled its type
        // as whatever the enclosing expression suggested rather than the
        // `(fn <op result> <handle result>)` it is -- the resume's type is
        // learned by UNIFICATION at the call sites inside the clause body,
        // which is why a bare fresh variable is the right thing to bind.
        //
        // The handle answers the BODY's type; the clauses only contribute
        // their effect rows.
        E::Handle(h) => {
            let (t, body_row) = infer_row(&h.body, env, st);
            row = body_row;
            for c in &h.clauses {
                let mark = env.scope.len();
                for p in &c.params {
                    let a = st.fresh();
                    env.bind(*p, a);
                }
                let rs = st.fresh();
                env.bind(c.resume_name, rs);
                let (_, crow) = infer_row(&c.body, env, st);
                while env.scope.len() > mark {
                    env.scope.pop();
                }
                row = st.row_union(&row, &crow);
            }
            t
        }
        E::WithTimeout(w) => infer(&w.body, env, st),
        // Three statement lists, all of them walked: the body, the retry
        // fallback and the failure arm are all program the checker sees.
        E::Try(t) => {
            let mut last = Ty::Nothing;
            let mark = env.scope.len();
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
            env.scope.truncate(mark);
            last
        }
        E::Error(..) => Ty::Error,
    };
    (t, row)
}

/// A pattern's variables, bound for the arm's body. Returns how many were
/// pushed so the caller can pop exactly those.
///
/// **A CONSTRUCTOR PATTERN INSTANTIATES THE CONSTRUCTOR, NOT ITS VARIABLES.**
/// One mint per QUANTIFIER of the constructor's own type, and each sub-pattern
/// takes its type from the corresponding instantiated FIELD.
///
/// Minting one per bound variable instead agrees on `Just (x)` -- one
/// quantifier, one variable -- and is wrong wherever the two differ: `None`
/// binds nothing and still mints, `Left (x)` on `Either (a) (b)` binds one and
/// mints two. Five definitions in `Foreword Maybe`, one `None` arm each, and
/// the unit came out five variables low.
///
/// `expected` is the type the enclosing pattern decided for this position;
/// only where there is none does a variable mint one of its own.
/// `bind-pattern` (TypeCheckerInference.codex:1448).
///
/// **THE SCRUTINEE'S TYPE COMES IN**, and that is the whole of it. A variable
/// pattern binds what it was handed and mints nothing; a constructor pattern
/// instantiates the constructor and UNIFIES ITS RETURN TYPE WITH THE
/// SCRUTINEE, which is what teaches the minted variable what it stands for.
///
/// Without that unification `Just`'s `a` stays the variable instantiation
/// minted and every field of every destructure is a `(tvar N)` -- correct in
/// the sense that nothing contradicts it, and useless to everything
/// downstream. Lowering then has to work the field type out for itself from
/// the constructor declaration and the scrutinee (`pattern-type-subst`,
/// `apply-ctor-subst`, `pair-tvars`, `subst-tvars`), which is upstream's own
/// answer to a checker that ALSO has this unification -- they need it because
/// their lowering pass can only look types up by span and a pattern is not an
/// expression. Ours records what the checker knew, so it does not.
///
/// The one place a variable is minted is where the constructor's arrow spine
/// RUNS OUT before the sub-patterns do -- an arity error in the program, and
/// upstream still gives each surplus field a variable rather than stopping.
fn bind_pattern(
    p: &crate::ast::Pat,
    ty: &Ty,
    env: &mut TyEnv<'_>,
    st: &mut UnifyState,
) -> usize {
    use crate::ast::Pat as P;
    st.record_pat_type(pat_span(p), ty.clone());
    match p {
        P::Var(n, _) => {
            env.bind(*n, ty.clone());
            1
        }
        P::Ctor(name, subs, _) => {
            // `Cons` and `Nil` over the BUILTIN list are not constructors in
            // the environment -- the list type is not a sum -- so they are
            // matched against the element type directly.
            if let Ty::List(elem) = st.deep_resolve(ty) {
                let n = env.syms.text(*name);
                if n == "Nil" {
                    return 0;
                }
                if n == "Cons" && subs.len() == 2 {
                    let tail = Ty::List(elem.clone());
                    return bind_pattern(&subs[0], &elem, env, st)
                        + bind_pattern(&subs[1], &tail, env, st);
                }
            }
            let ctor_ty = match env.get(*name).cloned() {
                Some(bound) => {
                    let inst = st.instantiate(&bound);
                    // `strip-fun-args`: what the constructor RETURNS, which is
                    // the type the scrutinee must have.
                    let mut ret = inst.clone();
                    loop {
                        match ret {
                            Ty::Fun(_, _, r) => ret = *r,
                            Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => ret = *b,
                            _ => break,
                        }
                    }
                    if !st.unify(&ret, ty) {
                        st.unify_gaps += 1;
                    }
                    inst
                }
                // Not in scope. Upstream bags a CDX error and binds the
                // fields against `ErrorTy`, which mints one apiece below.
                None => Ty::Error,
            };
            let mut spine = ctor_ty;
            let mut bound = 0;
            for sub in subs {
                let field = match spine {
                    Ty::Fun(a, _, r) => {
                        spine = *r;
                        *a
                    }
                    other => {
                        spine = other;
                        st.fresh()
                    }
                };
                bound += bind_pattern(sub, &field, env, st);
            }
            bound
        }
        P::Vec_(subs, _) => {
            let elem = match st.deep_resolve(ty) {
                Ty::Vector(_, e) => *e,
                _ => Ty::Error,
            };
            subs.iter().map(|s| bind_pattern(s, &elem, env, st)).sum()
        }
        P::Lit(..) | P::Wild(_) => 0,
    }
}

/// Names in scope during inference.
pub struct TyEnv<'a> {
    /// Carried so inference can spell a type's name without every function
    /// here taking a table.
    pub syms: &'a SymTab,
    /// The chapter's type declarations, for the one question inference asks of
    /// them: what type does this field of this record have.
    pub type_defs: &'a TypeDefs,
    /// **Symbols, not text.** This is a linear scan on the hot path of
    /// inference, and it now compares four bytes.
    pub scope: Vec<(Sym, Ty)>,
}

impl<'a> TyEnv<'a> {
    pub fn new(syms: &'a SymTab, type_defs: &'a TypeDefs) -> TyEnv<'a> {
        TyEnv { syms, type_defs, scope: Vec::new() }
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

/// The names `builtin_env` binds, and nothing else.
///
/// **`binder-free` ASKS THE BUILTINS TOO.** Its `base` is the checker's whole
/// binding list, so `is IrTry (max) ...` -- a pattern variable named after the
/// builtin `max` -- is a SHADOW and is emitted `max_1`. Answering from the
/// chapter's own definitions alone left nine definitions of the compiler
/// spelling the unshadowed name.
pub fn builtin_names(syms: &SymTab) -> Vec<Sym> {
    crate::builtins::BUILTIN_TYPES
        .iter()
        .filter_map(|(n, s)| {
            let sym = syms.find(n)?;
            parse_ty(syms, s).map(|_| sym)
        })
        .collect()
}

/// Every builtin whose declared type the probe could render, for the checker's
/// environment. Without these `show` resolves to ErrorTy and instantiating it
/// mints nothing -- which is one of the eight fresh variables fib expects.
pub fn builtin_env<'a>(syms: &'a SymTab, type_defs: &'a TypeDefs) -> TyEnv<'a> {
    let mut env = TyEnv::new(syms, type_defs);
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
    /// A definition with NO declared type costs TWO variables, not one.
    ///
    /// Registration mints the first; `build-undeclared-fun-type` mints the
    /// second for the result, plus one ROW and one variable per parameter, and
    /// `check-def-normal` unifies the two. Read off `codexcheck` on these four
    /// probes, and off `ringplug-source.codex`, whose two undeclared
    /// definitions are exactly its `next-id` -2.
    #[test]
    fn an_undeclared_definition_costs_two_variables() {
        assert_eq!(counters(&chapter("  a : Integer\n  a = 7\n")), (2, 0));
        assert_eq!(counters(&chapter("  a = 7\n")), (4, 0));
        assert_eq!(counters(&chapter("  a (x) = x\n")), (5, 1));
        assert_eq!(counters(&chapter("  a (x) (y) = x\n")), (6, 1));
    }

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
    /// Re-read off `codexcheck` at `8570fba1` (Update 57), against a chapter
    /// whose only definition is monomorphic so the difference is the type
    /// declaration alone.
    ///
    /// **EVERY ROW ROSE AT U56 AND THE DECLARATION RULE DID NOT CHANGE.** The
    /// `td-eq-safe` guard means each of these variants now also carries a
    /// generated `__eq_<T>`, and that definition mints on its own account. The
    /// rule above still reads off the DIFFERENCES: `Box` over the bare
    /// chapter is 7, `Pair` 12, `Trip` 17 -- still one more per type parameter
    /// per constructor, on top of a constant the equality costs.
    #[test]
    fn a_variant_mints_once_per_type_parameter_per_constructor() {
        let f = "\n  f : Integer -> Integer\n  f (n) = n\n";
        let with = |decl: &str| counters(&chapter(&format!("{decl}{f}")));

        assert_eq!(with(""), (2, 0));
        assert_eq!(with("  Box (a) =\n    | MkBox (a)\n"), (9, 0));
        assert_eq!(with("  Pair (a) (b) =\n    | MkPair (a) (b)\n"), (14, 0));
        assert_eq!(with("  Trip (a) (b) (c) =\n    | MkTrip (a) (b) (c)\n"), (19, 0));
        // Once per CONSTRUCTOR, so two arms naming the same parameter cost two.
        assert_eq!(with("  Two (a) =\n    | MkL (a)\n    | MkR (a)\n"), (13, 0));
        // No parameters, no mint of its own -- but the generated equality costs.
        assert_eq!(with("  Mono =\n    | MkA\n    | MkB\n"), (5, 0));
    }

    /// **A CONSTRUCTOR PATTERN INSTANTIATES THE CONSTRUCTOR, NOT ITS
    /// VARIABLES.** One mint per QUANTIFIER of the constructor's type, and the
    /// sub-patterns take their types from the instantiated fields.
    ///
    /// Minting one per bound variable instead agrees on `Just (x)` -- one
    /// quantifier, one variable -- and is wrong wherever the two differ: a
    /// NULLARY constructor binds nothing and still mints (`None` on
    /// `Maybe (a)`), and `Left (x)` on `Either (a) (b)` binds one and mints
    /// two. A wildcard arm mints nothing at all.
    ///
    /// Re-read off `codexcheck` at `8570fba1` (Update 57). Every row rose by
    /// the constant `Maybe`'s or `Either`'s generated `__eq_` costs under
    /// `td-eq-safe`; the DIFFERENCES the rule is about are unchanged.
    #[test]
    fn a_constructor_pattern_instantiates_the_constructor() {
        let maybe = "  Maybe (a) =\n    | Just (a)\n    | None\n\n";
        let either = "  Either (a) (b) =\n    | Left (a)\n    | Right (b)\n\n";
        let f = |decl: &str, arms: &str| {
            counters(&chapter(&format!(
                "{decl}  f : {} -> Boolean\n  f (m) = when m\n{arms}",
                if decl == maybe { "Maybe a" } else { "Either a b" }
            )))
        };
        // `Just (x)` mints one and binds one; `None` mints one and binds none.
        assert_eq!(f(maybe, "    is Just (x) -> True\n    is None -> False\n"), (18, 0));
        // A wildcard is not a constructor and costs nothing.
        assert_eq!(f(maybe, "    is Just (x) -> True\n    is otherwise -> False\n"), (17, 0));
        // Two quantifiers, one bound variable, twice.
        assert_eq!(f(either, "    is Left (x) -> True\n    is Right (y) -> False\n"), (30, 0));
        // The same constructor twice costs the same twice.
        assert_eq!(
            f(maybe, "    is Just (x) -> True\n    is Just (y) -> False\n    is None -> False\n"),
            (19, 0)
        );
    }

    /// **A RECURSIVE SUM COSTS FAR MORE THAN ITS SHAPE SUGGESTS**, because a
    /// `SumTy` carries its whole CONSTRUCTOR LIST and a self-referencing field
    /// pulls that list back into the type `parameterize-type` walks.
    ///
    /// `build-type-def-map` resolves a constructor's fields against the PARTIAL
    /// map -- the entries built so far, not this one -- so the self-reference
    /// stays a small `ConstructedTy` there. But `build-ctor-type`
    /// (TypeChecker.codex:4278) then resolves the same fields against the FULL
    /// map, and `N` now looks up to the finished `SumTy` with every constructor
    /// and every field type in it.
    ///
    /// Re-read off `codexcheck` at `8570fba1` (Update 57). Only the two
    /// non-recursive controls moved: under `td-eq-safe` they now get a derived
    /// definition too, so they are no longer controls for "no derived
    /// definition" -- they are controls for "derived WITHOUT a self-reference
    /// to pull the constructor list back in". Every self-recursive row below
    /// is unchanged, because those already had one at U55.
    #[test]
    fn a_recursive_sum_pulls_its_own_constructor_list_in() {
        let f = "\n  f : Integer -> Integer\n  f (n) = n\n";
        let with = |decl: &str| counters(&chapter(&format!("{decl}{f}"))).0;

        // The non-recursive controls. These DO get a derived definition now,
        // but no self-reference, so the constructor list is not pulled back in
        // and the cost stays far below the recursive rows of the same shape.
        assert_eq!(with("  N a =\n    | E\n    | L (a)\n"), 13);
        assert_eq!(with("  N =\n    | E\n    | L (Integer)\n"), 5);

        // One self-naming arm, and a whole `__eq_N` appears. With no type
        // parameters the cost is exactly the matches it contains: one over
        // `__ex`, and one over `__ey` per constructor.
        assert_eq!(with("  N =\n    | B (N)\n"), 4);
        assert_eq!(with("  N =\n    | E\n    | B (N)\n"), 5);
        assert_eq!(with("  N =\n    | E\n    | B (N)\n    | C (N)\n"), 6);
        // Two self-naming FIELDS in one constructor are still one arm.
        assert_eq!(with("  N =\n    | E\n    | B (N) (N)\n"), 5);

        // A type parameter multiplies it: every constructor pattern in the
        // derived body instantiates that constructor's own quantifier.
        assert_eq!(with("  N a =\n    | B (N a)\n"), 9);
        assert_eq!(with("  N a =\n    | E\n    | B (N a)\n"), 13);
        assert_eq!(with("  N a =\n    | E\n    | L (a)\n    | B (N a)\n"), 17);
        assert_eq!(with("  N a b =\n    | E\n    | B (N a b)\n"), 21);
        // Through a `List`, which is the shape the depot actually writes.
        assert_eq!(with("  N a =\n    | E\n    | B (List (N a))\n"), 13);
    }

    /// **A LAMBDA MINTS ONE ROW, AFTER ITS BODY.** `infer-lambda` ends with
    /// `open-row-if-closed` (TypeCheckerInference.codex:529), which mints when
    /// the body's effect row has no tail -- and a pure body's never does. The
    /// type variables for its parameters are minted BEFORE the body, by
    /// `bind-lambda-params`, so the two counters move at different moments.
    ///
    /// Read off `codexcheck`: one lambda costs one row, two cost two, and
    /// `next-id` does not move either way.
    #[test]
    fn a_lambda_mints_one_row_after_its_body() {
        let ap = "  ap : (Integer -> Integer), Integer -> Integer\n  ap (g) (x) = g x\n\n";
        let one = format!("{ap}  f : Integer -> Integer\n  f (n) = ap (\\y -> y) n\n");
        assert_eq!(counters(&chapter(&one)), (6, 10));

        let two = format!(
            "{ap}  f : Integer -> Integer\n  f (n) = ap (\\y -> y) (ap (\\z -> z) n)\n"
        );
        assert_eq!(counters(&chapter(&two)), (9, 17));
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

/// A pattern node's own span.
fn pat_span(p: &crate::ast::Pat) -> crate::ast::Span {
    use crate::ast::Pat as P;
    match p {
        P::Var(_, s) | P::Lit(_, _, s) | P::Ctor(_, _, s) | P::Wild(s) | P::Vec_(_, s) => *s,
    }
}

/// What a definition with no signature costs, measured against `codexcheck`.
///
/// `UnifyState::default` starts at `next_id = 2`, so these totals include the
/// two slots upstream's `empty-unification-state` starts with. The
/// registration variable is the first; `build_undeclared_fun_type` mints the
/// rest.
#[cfg(test)]
mod undeclared_definition_cost {
    fn counts(src: &str) -> (u32, i32) {
        let bytes = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&bytes);
        let mut dg = crate::desugar::Desugar::new(&bytes);
        let ch = dg.chapter(&parsed.tree);
        let (_, st) = super::check_chapter(&ch);
        (st.next_id, st.next_row_id)
    }

    #[test]
    fn a_nullary_definition_costs_two_variables_and_no_row() {
        assert_eq!(counts("Chapter: P\nSection: S\n  a = 7\n"), (4, 0));
    }

    #[test]
    fn each_parameter_adds_a_variable_and_the_spine_adds_one_row() {
        assert_eq!(counts("Chapter: P\nSection: S\n  a (x) = x\n"), (5, 1));
        assert_eq!(counts("Chapter: P\nSection: S\n  a (x) (y) = x\n"), (6, 1));
    }

    #[test]
    fn a_declared_definition_costs_nothing_beyond_its_registration() {
        assert_eq!(counts("Chapter: P\nSection: S\n  a : Integer\n  a = 7\n"), (2, 0));
    }
}

/// A `<-` bind is visible to the rest of its block.
///
/// The subject is `Fat16`: `here <- fat16-cluster-entry-sectors ...` followed
/// by `here.li-entries`. Discarding the name left the object unresolved, so
/// the field access minted where upstream looked the field up.
#[cfg(test)]
mod act_bind_is_in_scope {
    const SRC: &str = "Chapter: P\nSection: S\n  R = record { ra : Integer, rb : Integer }\n  mkr : Integer -> [Console] R\n  mkr (x) = act\n    print-line-uni \"hi\"\n    R { ra = x, rb = x }\n  end\n  f : Integer -> [Console] Integer\n  f (x) = act\n    r <- mkr x\n    r.ra\n  end\n";

    #[test]
    fn a_field_access_on_a_bound_name_mints_nothing() {
        let bytes = SRC.as_bytes().to_vec();
        let parsed = crate::parser::parse(&bytes);
        let mut dg = crate::desugar::Desugar::new(&bytes);
        let ch = dg.chapter(&parsed.tree);
        let (_, st) = super::check_chapter(&ch);
        // `codexcheck` on this unit: next-id 4, next-row-id 6, expr-types 7.
        // It was 5 while the bind was discarded.
        assert_eq!((st.next_id, st.next_row_id, st.expr_types.len()), (4, 6, 7));
    }
}

/// The four applied types that are not constructors.
///
/// `resolve-applied-type` gives `List`, `LinkedList`, `Real` and `Vector` each
/// their own `CodexType`; everything else is a `ConstructedTy`. `LinkedList`
/// missing from that list spelled 99 definitions of the compiler
/// `(ctd "LinkedList" (args T))` where the oracle says `(llist T)`.
#[cfg(test)]
mod applied_types_that_are_not_constructors {
    use super::{RealMode, RealWidth, Ty};

    /// The declared parameter type of the chapter's last definition.
    fn param_ty(decl: &str) -> Ty {
        let src = format!("Chapter: P\nSection: S\n  f : {decl} -> Integer\n  f (x) = 1\n");
        let bytes = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&bytes);
        let mut dg = crate::desugar::Desugar::new(&bytes);
        let ch = dg.chapter(&parsed.tree);
        let tds = super::TypeDefs::new(&ch);
        let t = ch.defs.last().expect("one definition").declared_type.first().expect("a type");
        match super::resolve_declared(&ch.syms, &tds, t).expect("resolved") {
            Ty::Fun(p, _, _) => *p,
            other => panic!("not an arrow: {other:?}"),
        }
    }

    #[test]
    fn a_linked_list_is_not_a_constructor() {
        assert_eq!(param_ty("LinkedList Text"), Ty::LinkedList(Box::new(Ty::Text)));
        assert_eq!(param_ty("List Text"), Ty::List(Box::new(Ty::Text)));
    }

    #[test]
    fn the_wrong_arity_keeps_the_container_and_loses_the_element() {
        assert_eq!(param_ty("List Text Text"), Ty::List(Box::new(Ty::Error)));
        assert_eq!(param_ty("LinkedList Text Text"), Ty::LinkedList(Box::new(Ty::Error)));
    }

    #[test]
    fn every_argument_to_real_must_be_a_qualifier() {
        assert_eq!(param_ty("Real approximate"), Ty::Real(RealWidth::F32, RealMode::Default));
        assert_eq!(
            param_ty("Real approximate trapping"),
            Ty::Real(RealWidth::F32, RealMode::Trapping)
        );
        assert_eq!(param_ty("Real saturating"), Ty::Real(RealWidth::F64, RealMode::Saturating));
        // `Real a` is an application of a name that happens to be `Real`.
        assert!(matches!(param_ty("Real a"), Ty::Constructed(..)));
    }

    #[test]
    fn a_vector_reads_its_length_out_of_a_name() {
        assert_eq!(param_ty("Vector 4 Real"), Ty::Vector(4, Box::new(Ty::Real(RealWidth::F64, RealMode::Default))));
    }
}

/// A `let` inside one definition must not be visible in the next.
///
/// The leak is not local. `check_chapter_full` pops as many entries as the
/// definition had PARAMETERS, so k bindings left behind by the body pop k
/// parameters instead -- and those parameters stay bound for the rest of the
/// chapter, shadowing globals of the same name.
#[cfg(test)]
mod a_let_does_not_outlive_its_definition {
    #[test]
    fn a_parameter_does_not_shadow_a_global_in_a_later_definition() {
        // `holder` has a parameter named `table`, and a `let` in its body: one
        // leaked binding, one parameter left bound. `after` then reads the
        // global `table` and must still see `List Text`, not `Integer`.
        let src = "Chapter: T\nSection: S\n  table : List Text\n  table = []\n\n  holder : Integer -> Integer\n  holder (table) = let x = table in x\n\n  after : Integer -> Integer\n  after (n) = list-length table\n";
        let bytes = src.as_bytes();
        let parsed = crate::parser::parse(bytes);
        let mut dg = crate::desugar::Desugar::new(bytes);
        let ch = dg.chapter(&parsed.tree);
        let (bindings, st, _) = super::check_chapter_full(&ch);
        let after = ch.defs.iter().find(|d| ch.syms.text(d.name) == "after").expect("after");
        // The body is `list-length table`; the argument's recorded type is the
        // global's.
        let crate::ast::Expr::Apply(_, arg, _) = &after.body else { panic!("not an apply") };
        let crate::ast::Expr::NameRef(_, sp) = &**arg else { panic!("not a name") };
        assert_eq!(
            st.expr_type_at(*sp).map(|t| crate::ir_text::render_ty(&ch.syms, t)),
            Some("(list text)".to_string())
        );
        let _ = bindings;
    }
}

/// What an UNDECLARED definition's arrow learns from its body.
#[cfg(test)]
mod an_undeclared_definition_learns_its_row_from_its_body {
    fn rows(src: &str) -> i32 {
        let bytes = src.as_bytes();
        let parsed = crate::parser::parse(bytes);
        let mut dg = crate::desugar::Desugar::new(bytes);
        let ch = dg.chapter(&parsed.tree);
        super::check_chapter_full(&ch).1.next_row_id
    }

    /// **THE ARROW `build_undeclared_fun_type` BUILDS CARRIES AN OPEN ROW, AND
    /// SOMETHING HAS TO TELL IT WHAT THE BODY PERFORMS.** `check-def-normal`'s
    /// `row-tied` unifies that row with the body's; without it the row stayed
    /// unbound and `unify_row` never had to mint it a tail.
    ///
    /// It takes BOTH a parameter -- or there is no arrow to carry a row -- and
    /// a call, or the body's row is empty and binding it is free. Those are the
    /// oracle's numbers, one probe each.
    #[test]
    fn it_takes_a_parameter_and_a_call_together() {
        let chapter = |d: &str| {
            format!("Chapter: R\n\nSection: S\n\n  {d}\n\n  opening : Text = \"z\"\n")
        };
        // Neither alone moves a row.
        assert_eq!(rows(&chapter("f (x) = x")), 1);
        assert_eq!(rows(&chapter("f = show 1")), 3);
        // Together they do, and this is the one that was short.
        assert_eq!(rows(&chapter("f (x) = show x")), 5);
        // A DECLARED definition is unaffected: its row is its author's.
        assert_eq!(rows(&chapter("g : Integer -> Text\n  g (x) = show x")), 3);
    }
}

/// A field the record does not have.
#[cfg(test)]
mod a_missing_field_is_diagnosed_not_minted {
    fn diags(src: &str) -> (Vec<u16>, u32) {
        let bytes = src.as_bytes();
        let parsed = crate::parser::parse(bytes);
        let mut dg = crate::desugar::Desugar::new(bytes);
        let ch = dg.chapter(&parsed.tree);
        let (_, st, _) = super::check_chapter_full(&ch);
        (st.diags.iter().map(|d| d.code).collect(), st.next_id)
    }

    /// **A MISSING FIELD IS AN ERROR, AND ERRORS DO NOT MINT.** We answered
    /// `fresh-and-advance` and said nothing, which both hid the defect and
    /// moved `next-id` by one per occurrence; upstream answers `ErrorTy` and
    /// raises CDX2005 (subject 53637). The `next_id` half is the half a
    /// diagnostics-only test would miss.
    #[test]
    fn a_missing_field_raises_cdx2005_and_mints_nothing() {
        let good = "Chapter: T\n\nSection: S\n  Pt = record {\n    x : Integer\n  }\n\n  f : Pt -> Integer\n  f (p) = p.x\n";
        let bad = "Chapter: T\n\nSection: S\n  Pt = record {\n    x : Integer\n  }\n\n  f : Pt -> Integer\n  f (p) = p.z\n";
        let (gc, gid) = diags(good);
        let (bc, bid) = diags(bad);
        assert_eq!(gc, Vec::<u16>::new());
        assert_eq!(bc, vec![super::Cdx::UNKNOWN_RECORD_FIELD]);
        assert_eq!(gid, bid, "the error path minted a variable the good path did not");
    }
}

/// The tighter of the two operand types, and the order-independence it buys.
///
/// The six cases are `codexir`'s answers, not ours: a record with two bounded
/// fields, `let slot = <a op b> in ...`, read off the emitted IR.
#[cfg(test)]
mod arithmetic_answers_the_tighter_type {
    use super::{arith_result_ty, Overflow, Ty};

    fn int(lo: i64, hi: i64) -> Ty {
        Ty::Integer(lo, hi, Overflow::Error)
    }
    const FULL: fn() -> Ty = || Ty::Integer(i64::MIN, i64::MAX, Overflow::Error);

    #[test]
    fn the_right_wins_only_when_it_is_contained_in_the_left() {
        // Nested either way round: the tighter one, whichever side it is on.
        assert_eq!(arith_result_ty(&int(0, 65535), &int(10, 20)), int(10, 20));
        assert_eq!(arith_result_ty(&int(10, 20), &int(0, 65535)), int(10, 20));
        assert_eq!(arith_result_ty(&int(0, 100), &int(0, 50)), int(0, 50));
        assert_eq!(arith_result_ty(&int(0, 50), &int(0, 100)), int(0, 50));
        // OVERLAPPING BUT NOT NESTED: the left, both ways. This is the case
        // that says the rule is containment and not width.
        assert_eq!(arith_result_ty(&int(0, 100), &int(50, 200)), int(0, 100));
        assert_eq!(arith_result_ty(&int(50, 200), &int(0, 100)), int(50, 200));
    }

    #[test]
    fn a_literal_does_not_widen_the_byte_it_is_added_to() {
        // Upstream's own example: `b.val + 1` and `1 + b.val` must agree, and
        // an integer literal carries the FULL i64 range.
        assert_eq!(arith_result_ty(&int(0, 255), &FULL()), int(0, 255));
        assert_eq!(arith_result_ty(&FULL(), &int(0, 255)), int(0, 255));
    }

    #[test]
    fn anything_that_is_not_two_integers_is_the_left() {
        assert_eq!(arith_result_ty(&Ty::Text, &int(0, 5)), Ty::Text);
        assert_eq!(arith_result_ty(&int(0, 5), &Ty::Text), int(0, 5));
    }
}

/// The three rules that keep unification from building a type it cannot print.
///
/// Written after the fact and they should not have been: the var-var
/// orientation was changed on a reading of the source with no test behind it,
/// and it turned out not to be the fix for anything. It is upstream's rule and
/// it stays, but pinned rather than assumed.
#[cfg(test)]
mod unification_stays_acyclic {
    use super::{Ty, UnifyState};

    /// `unify-resolved` (subject 46410): `if id-a < id-b then add-subst id-b a
    /// else add-subst id-a b` -- the HIGHER id binds to the lower, whichever
    /// side it arrived on.
    #[test]
    fn the_higher_variable_binds_to_the_lower() {
        for (l, r) in [(5u32, 2u32), (2, 5)] {
            let mut st = UnifyState::default();
            while st.next_id <= 5 {
                let _ = st.fresh();
            }
            assert!(st.unify(&Ty::Var(l), &Ty::Var(r)));
            assert_eq!(st.resolve(&Ty::Var(5)), Ty::Var(2), "5 should follow to 2 ({l} ~ {r})");
            assert_eq!(st.resolve(&Ty::Var(2)), Ty::Var(2), "2 stays the representative");
        }
    }

    /// `unify-at` (subject 46401) strips `linear` from BOTH sides before it
    /// looks at anything, so a variable meeting itself under the wrapper is
    /// two equal variables and not a cycle.
    #[test]
    fn linear_is_transparent_to_unification() {
        for flip in [false, true] {
            let mut st = UnifyState::default();
            let v = st.fresh();
            let wrapped = Ty::Linear(Box::new(v.clone()));
            let ok = if flip { st.unify(&wrapped, &v) } else { st.unify(&v, &wrapped) };
            assert!(ok, "linear should be transparent (flip={flip})");
            assert_eq!(st.errors(), 0, "and it is not an infinite type (flip={flip})");
        }
    }

    /// `occurs-in` (subject 46189). A variable inside the type it is being
    /// bound to is `CDX2010 Infinite type` -- refused, not built. Building it
    /// does not fail here; it fails in `deep_resolve`, which walks structure
    /// and never terminates.
    #[test]
    fn a_variable_inside_its_own_binding_is_refused() {
        for flip in [false, true] {
            let mut st = UnifyState::default();
            let v = st.fresh();
            let cyclic = Ty::List(Box::new(v.clone()));
            let ok = if flip { st.unify(&cyclic, &v) } else { st.unify(&v, &cyclic) };
            assert!(!ok, "an infinite type is refused (flip={flip})");
            assert_eq!(st.errors(), 1, "and it is reported (flip={flip})");
            assert_eq!(st.diags[0].code, super::Cdx::INFINITE_TYPE, "as CDX2010");
            // The substitution is still walkable, which is the point.
            assert_eq!(st.deep_resolve(&v), v);
        }
    }

    /// The arm list is narrow ON PURPOSE: a sum, a record, a constructed type,
    /// a vector and a unit are not walked. Upstream's list, not an omission.
    #[test]
    fn a_named_types_arguments_are_not_walked() {
        let mut st = UnifyState::default();
        let v = st.fresh();
        let n = crate::symbol::SymTab::default().intern("");
        assert!(st.unify(&v, &Ty::Constructed(n, vec![v.clone()])));
        assert_eq!(st.errors(), 0);
    }

    /// **A CONCRETE-HEAD MISMATCH IS `CDX2001`.** Two fully-resolved types with
    /// different head constructors -- Integer meeting Text -- are a type error
    /// the program earned, reported rather than swallowed as a gap that ships
    /// best-effort IR only the interpreter or plug then refuses.
    #[test]
    fn a_concrete_head_mismatch_is_a_type_mismatch() {
        let int = Ty::Integer(i64::MIN, i64::MAX, super::Overflow::Error);
        let mut st = UnifyState::default();
        assert!(!st.unify(&int, &Ty::Text), "Integer and Text do not unify");
        assert_eq!(st.errors(), 1, "and it is reported");
        assert_eq!(st.diags[0].code, super::Cdx::TYPE_MISMATCH, "as CDX2001");
    }

    /// **TWO INTEGERS OF DIFFERENT RANGES ARE NOT A TYPE ERROR.** A byte meeting
    /// the full i64 range is reconciled by the checker's range handling, not
    /// reported -- the exclusion that keeps the self-host at check-errors 0.
    #[test]
    fn differently_ranged_integers_are_not_a_type_mismatch() {
        let byte = Ty::Integer(0, 255, super::Overflow::Error);
        let wide = Ty::Integer(i64::MIN, i64::MAX, super::Overflow::Error);
        let mut st = UnifyState::default();
        let _ = st.unify(&byte, &wide);
        assert_eq!(st.errors(), 0, "a range mismatch is not a type error");
    }

    /// **A MISMATCH THAT STILL HOLDS A VARIABLE IS A GAP, NOT AN ERROR.** A name
    /// mismatch between `Maybe Integer` and `Either <var>` is the partial
    /// unifier's ignorance -- a later unification could still decide the
    /// variable -- so it is not a `CDX2001`.
    #[test]
    fn a_mismatch_involving_a_variable_is_not_reported() {
        let mut st = UnifyState::default();
        let v = st.fresh();
        let mut syms = crate::symbol::SymTab::default();
        let maybe =
            Ty::Constructed(syms.intern("Maybe"), vec![Ty::Integer(0, 0, super::Overflow::Error)]);
        let either = Ty::Constructed(syms.intern("Either"), vec![v]);
        assert!(!st.unify(&maybe, &either), "different names do not unify");
        assert_eq!(st.errors(), 0, "but a variable is present, so it is a gap");
    }
}
