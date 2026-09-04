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
pub fn type_kind(t: &Ty) -> String {
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
        Ty::Sum(n, _) => format!("sum:{n}"),
        Ty::Record(n, _) => format!("rec:{n}"),
        Ty::Constructed(n, _) => format!("con:{n}"),
        Ty::TypeCon(n) => format!("tycon:{n}"),
        _ => "other".into(),
    }
}

/// One name bound to one type, in the order the checker registered it.
#[derive(Clone, Debug)]
pub struct Binding {
    pub name: String,
    pub ty: Ty,
}

/// The state the checker threads, and the three numbers the gold grades.
///
/// `next_id` is NOT `substitutions.len()`, and the gold shows them equal at 8
/// only by coincidence on this subject. They count different things: how many
/// fresh variables were minted, and how many of them were resolved.
#[derive(Debug, Default)]
pub struct UnifyState {
    pub substitutions: Vec<(u32, Ty)>,
    pub next_id: u32,
    /// Row ids are a SEPARATE counter from type-variable ids. `next-id` in the
    /// gold counts only the latter, so minting a row must not advance it.
    pub next_row_id: u32,
    pub expr_types: Vec<(String, Ty)>,
    pub errors: usize,
}

impl UnifyState {
    /// Mint a fresh type variable. ORDER MATTERS: the gold records how many
    /// were minted, so a checker that reaches the same answer by a different
    /// route reports a different number and is wrong here.
    pub fn fresh(&mut self) -> Ty {
        let id = self.next_id;
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
pub fn resolve_declared(t: &crate::ast::TypeExpr) -> Option<Ty> {
    use crate::ast::TypeExpr as T;
    Some(match t {
        T::Named(n, _) => match n.as_str() {
            "Integer" => Ty::Integer(i64::MIN, i64::MAX, Overflow::Error),
            "Text" => Ty::Text,
            "Boolean" => Ty::Boolean,
            "Char" => Ty::Char,
            "Nothing" => Ty::Nothing,
            "Real" => Ty::Real(RealWidth::F64, RealMode::Trapping),
            _ => Ty::TypeCon(n.clone()),
        },
        T::Fun(a, b, _) => Ty::Fun(
            Box::new(resolve_declared(a)?),
            EffectRow::default(),
            Box::new(resolve_declared(b)?),
        ),
        // `[Console] Nothing` -- the effect row is what makes `opening` print
        // as `eff` rather than as its result type.
        T::Effect(effs, scopes, _, inner, _) => Ty::Effectful(
            effs.clone(),
            scopes.clone(),
            Box::new(resolve_declared(inner)?),
        ),
        T::App(head, args, _) => match (&**head, args.as_slice()) {
            (T::Named(n, _), [only]) if n == "List" => {
                Ty::List(Box::new(resolve_declared(only)?))
            }
            (T::Named(n, _), _) => Ty::Constructed(
                n.clone(),
                args.iter().filter_map(resolve_declared).collect(),
            ),
            _ => return None,
        },
        T::Linear(inner, _) => Ty::Linear(Box::new(resolve_declared(inner)?)),
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
        let ty = match d.declared_type.first().and_then(resolve_declared) {
            Some(t) => t,
            None => st.fresh(),
        };
        out.push(Binding { name: d.name.clone(), ty });
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
    let mut env = builtin_env();
    for b in &bindings {
        env.bind(&b.name, b.ty.clone());
    }
    for d in &ch.defs {
        // A definition's parameters take their types from its declared arrow
        // spine, walked in order.
        // A PARAMETER BINDS TO A FRESH VARIABLE, not to the declared type's
        // argument. `bind-lambda-params` (TypeCheckerInference.codex:567) mints
        // one per parameter and unification ties it to the declaration
        // afterwards. Reading the type off the declared spine reaches the same
        // conclusion and mints nothing, which is how fib's next-id came out 5
        // instead of 8 -- the two parameters are two of the missing three.
        let mut saved = Vec::new();
        for p in &d.params {
            let fr = st.fresh();
            saved.push(p.name.clone());
            env.bind(&p.name, fr);
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
pub fn section(bindings: &[Binding], st: &UnifyState) -> String {
    let mut s = String::from("--- check ---\n");
    s.push_str(&format!("check-errors {}\n", st.errors));
    s.push_str(&format!("type-bindings {}\n", bindings.len()));
    for b in bindings {
        s.push_str(&format!("tb {} {}\n", b.name, type_kind(&b.ty)));
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
pub fn infer(e: &crate::ast::Expr, env: &mut TyEnv, st: &mut UnifyState) -> Ty {
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
            let t = match env.get(n).cloned() {
                Some(Ty::ForAll(_, body)) => {
                    let fr = st.fresh();
                    instantiate(&body, &fr)
                }
                Some(t) => t,
                None => Ty::Error,
            };
            st.expr_types.push((n.clone(), t.clone()));
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
        // The one site that mints, and it mints TWICE: a result variable and a
        // row id, in that order.
        E::Apply(f, a, _) => {
            let ft = infer(f, env, st);
            let _at = infer(a, env, st);
            let ret = st.fresh();
            let _row = st.fresh_row();
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
                env.bind(&b.name, t);
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
#[derive(Default)]
pub struct TyEnv {
    pub scope: Vec<(String, Ty)>,
}

impl TyEnv {
    pub fn get(&self, n: &str) -> Option<&Ty> {
        self.scope.iter().rev().find(|(k, _)| k == n).map(|(_, v)| v)
    }
    pub fn bind(&mut self, n: &str, t: Ty) {
        self.scope.push((n.to_string(), t));
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

fn parse_one(s: &str) -> Option<(Ty, &str)> {
    let s = s.trim_start();
    if let Some(inner) = s.strip_prefix('(') {
        let (head, mut rest) = take_word(inner);
        let mut args: Vec<Ty> = Vec::new();
        let mut words: Vec<String> = Vec::new();
        loop {
            let r = rest.trim_start();
            if let Some(after) = r.strip_prefix(')') {
                return Some((build(head, &args, &words)?, after));
            }
            if r.starts_with('(') {
                let (t, after) = parse_one(r)?;
                args.push(t);
                rest = after;
            } else {
                let (w, after) = take_word(r);
                words.push(w.to_string());
                if let Some(t) = atom(w) {
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

fn build(head: &str, args: &[Ty], words: &[String]) -> Option<Ty> {
    Some(match head {
        // `(fn A ROW B)` -- the row contributes no Ty, so A and B are args 0/1.
        "fn" => Ty::Fun(
            Box::new(args.first()?.clone()),
            EffectRow::default(),
            Box::new(args.get(1)?.clone()),
        ),
        "tvar" => Ty::Var(words.first()?.parse().ok()?),
        "forall" => Ty::ForAll(words.first()?.parse().ok()?, Box::new(args.first()?.clone())),
        "foralleff" => Ty::ForAllEff(words.first()?.parse().ok()?, Box::new(args.first()?.clone())),
        "list" => Ty::List(Box::new(args.first()?.clone())),
        "eff" => Ty::Effectful(Vec::new(), Vec::new(), Box::new(args.first()?.clone())),
        "row" | "empty" => return None,
        _ => return None,
    })
}

/// Every builtin whose declared type the probe could render, for the checker's
/// environment. Without these `show` resolves to ErrorTy and instantiating it
/// mints nothing -- which is one of the eight fresh variables fib expects.
pub fn builtin_env() -> TyEnv {
    let mut env = TyEnv::default();
    for (n, s) in crate::builtins::BUILTIN_TYPES {
        if let Some(t) = parse_ty(s) {
            env.bind(n, t);
        }
    }
    env
}
