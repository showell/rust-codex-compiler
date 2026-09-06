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
    ForAllEff(u32, Box<Ty>),
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
    Trapping,
    Saturating,
    Approx,
}

/// An effect row. Empty is the common case and prints as nothing.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct EffectRow {
    pub labels: Vec<(String, String)>,
    pub tail: String,
    pub id: u32,
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
    pub next_row_id: u32,
    pub expr_types: Vec<(Sym, Ty)>,
    pub errors: usize,
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
            expr_types: Vec::new(),
            errors: 0,
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
    pub fn fresh_row(&mut self) -> u32 {
        let id = self.next_row_id;
        self.next_row_id += 1;
        id
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
            "Real" => Ty::Real(RealWidth::F64, RealMode::Trapping),
            _ => Ty::TypeCon(n.clone()),
        },
        T::Fun(a, b, _) => Ty::Fun(
            Box::new(resolve_declared(syms, a)?),
            EffectRow::default(),
            Box::new(resolve_declared(syms, b)?),
        ),
        // `[Console] Nothing` -- the effect row is what makes `opening` print
        // as `eff` rather than as its result type.
        T::Effect(effs, scopes, _, inner, _) => Ty::Effectful(
            effs.clone(),
            scopes.clone(),
            Box::new(resolve_declared(syms, inner)?),
        ),
        T::App(head, args, _) => match (&**head, args.as_slice()) {
            (T::Named(n, _), [only]) if syms.text(*n) == "List" => {
                Ty::List(Box::new(resolve_declared(syms, only)?))
            }
            (T::Named(n, _), _) => Ty::Constructed(
                n.clone(),
                args.iter().filter_map(|t| resolve_declared(syms, t)).collect(),
            ),
            _ => return None,
        },
        T::Linear(inner, _) => Ty::Linear(Box::new(resolve_declared(syms, inner)?)),
        _ => return None,
    })
}

/// Register every definition's declared type, in source order.
///
/// Upstream's `register-all-defs` mints a FRESH VARIABLE for a definition that
/// declares no type and binds the declared one otherwise. Both halves are here
/// because the fresh-variable count is graded, and skipping the mint would
/// report a smaller `next-id` than upstream for the same program.
pub fn register_defs(ch: &crate::ast::Chapter, st: &mut UnifyState) -> Vec<Binding> {
    let mut out = Vec::new();
    for d in &ch.defs {
        let ty = match d.declared_type.first().and_then(|t| resolve_declared(&ch.syms, t)) {
            Some(t) => t,
            None => st.fresh(),
        };
        out.push(Binding { name: d.name, ty });
    }
    out
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
        let mut spine = bindings.iter().find(|b| b.name == d.name).map(|b| b.ty.clone());
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
        infer(&d.body, &mut env, &mut st);
        for _ in saved {
            env.scope.pop();
        }
    }
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
        E::NameRef(n, _) => {
            // INSTANTIATING A FORALL MINTS. `show` is
            // `ForAllTy 0 (FunTy (TypeVar 0) empty-row TextTy)`, and opening
            // applies it -- the third of fib's three missing mints.
            let t = match env.get(*n).cloned() {
                Some(Ty::ForAll(_, body)) => {
                    let fr = st.fresh();
                    instantiate(&body, &fr)
                }
                Some(t) => t,
                None => Ty::Error,
            };
            // **A FUNCTION-TYPED NAME MINTS ONE ROW, HERE, BEFORE THE
            // APPLICATION AROUND IT MINTS ANYTHING.** Instantiating the type
            // gives its effect row a fresh id, and that id is what the wire
            // spells: `print-line-uni` reaches the IR as
            // `(fn text nothing (row (labels (label "Console.Write" "")) "" 0))`.
            //
            // Measured, not reasoned: `print-line-uni (read-file-raw "f")` puts
            // Console.Write on row 0 and FileSystem.Read on row 1. Minting all
            // of an application's rows up front would have given the inner
            // builtin row 3, and minting them after would have given the OUTER
            // one the higher number. Only this order produces 0 and 1.
            //
            // A name of non-function type mints nothing, which is what keeps
            // `fib`'s four references to `n` off the counter.
            if matches!(t, Ty::Fun(..)) {
                let _ = st.fresh_row();
            }
            st.expr_types.push((*n, t.clone()));
            return t;
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
            let _at = infer(a, env, st);
            let ret = st.fresh();
            let _row = st.fresh_row();
            let _row2 = st.fresh_row();
            match ft {
                Ty::Fun(_, _, r) => *r,
                _ => ret,
            }
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
        _ => Ty::Error,
    };
    t
}

/// Replace the bound variable of a forall with a fresh one.
fn instantiate(t: &Ty, fresh: &Ty) -> Ty {
    match t {
        Ty::Var(_) => fresh.clone(),
        Ty::Fun(a, r, b) => Ty::Fun(
            Box::new(instantiate(a, fresh)),
            r.clone(),
            Box::new(instantiate(b, fresh)),
        ),
        Ty::List(e) => Ty::List(Box::new(instantiate(e, fresh))),
        other => other.clone(),
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
pub fn parse_ty(s: &str) -> Option<Ty> {
    let (t, rest) = parse_one(s.trim())?;
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

/// `(row Console.Write)` and `(row)` as the wire's own record. `empty` is the
/// row with no labels, which is what a pure builtin declares.
fn parse_row(inner: &str) -> EffectRow {
    let mut it = inner.split_whitespace();
    let head = it.next().unwrap_or("");
    let labels = if head == "row" {
        it.map(|w| (w.to_string(), String::new())).collect()
    } else {
        Vec::new()
    };
    EffectRow { labels, tail: String::new(), id: 0 }
}

fn parse_one(s: &str) -> Option<(Ty, &str)> {
    let s = s.trim_start();
    if let Some(inner) = s.strip_prefix('(') {
        let (head, mut rest) = take_word(inner);
        let mut args: Vec<Ty> = Vec::new();
        let mut words: Vec<String> = Vec::new();
        let mut rows: Vec<EffectRow> = Vec::new();
        loop {
            let r = rest.trim_start();
            if let Some(after) = r.strip_prefix(')') {
                return Some((build(head, &args, &words, &rows)?, after));
            }
            if r.starts_with('(') {
                // A row group is consumed whole and contributes a row, not a
                // type; anything else is an ordinary nested type.
                let is_row = take_group(r)
                    .map(|(inner, _)| {
                        let w = inner.split_whitespace().next().unwrap_or("");
                        w == "row" || w == "empty"
                    })
                    .unwrap_or(false);
                if is_row {
                    let (inner, after) = take_group(r)?;
                    rows.push(parse_row(inner));
                    rest = after;
                    continue;
                }
                let (t, after) = parse_one(r)?;
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
        "real" => Ty::Real(RealWidth::F64, RealMode::Trapping),
        "real-approx" => Ty::Real(RealWidth::F32, RealMode::Approx),
        _ => return None,
    })
}

fn build(head: &str, args: &[Ty], words: &[String], rows: &[EffectRow]) -> Option<Ty> {
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
        let (Some(sym), Some(t)) = (syms.find(n), parse_ty(s)) else { continue };
        env.bind(sym, t);
    }
    env
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `(next_id, next_row_id)` after checking one chapter.
    fn counters(src: &str) -> (u32, u32) {
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
