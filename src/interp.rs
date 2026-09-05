//! A tree-walking interpreter over the desugared AST.
//!
//! **It has no type checker and does not need one.** A value knows what it is,
//! so `a + b` looks at the two values in hand; the checker's job is to prove
//! ahead of time that they will be the right ones. What this buys is an oracle
//! the type checker cannot be: a wrong SHAPE -- `a - b` for `b - a`, `+` and
//! `*` at the same precedence, `|>` with its operands the wrong way round --
//! is almost always well-typed, and shows up here as a wrong number.
//!
//! Where a declared type genuinely changes behaviour, it is READ, because a
//! declared type is syntax. `Score { v = 250 }` where the field is `Integer
//! between 0 and 100 clamping` evaluates to 100, and the bound comes from the
//! record's own definition. Inferred types are the ones we do not have.
//!
//! Anything unimplemented raises an error that NAMES it. A silent wrong answer
//! would make the whole exercise worthless.
//!
//! **What it walks is `Code`, not `Expr`** -- see `crate::code`. The chapter is
//! compiled once into a form where a local is a frame slot, a global is an
//! index, a literal is already a value and an application spine is already
//! flat, so nothing here resolves a name or parses a literal while the program
//! is running.

use crate::ast::*;
use crate::code::{Arm, Code, Compiler, Names, PatCode, Stmt};
use crate::symbol::{Sym, SymTab};
use std::collections::HashMap;
use std::fmt::Write as _;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Real(f64),
    Text(Rc<String>),
    Char(char),
    Bool(bool),
    List(Rc<Vec<Value>>),
    /// A record literal: its type name and its fields. A name is a four-byte
    /// `Sym`, so building a record copies nothing and this variant is the
    /// smallest thing that can carry two.
    /// A RECORD IS SHARED AND MUTABLE, because Codex's is.
    ///
    /// `st.offset = stop` is a field ASSIGNMENT and it writes through: the
    /// compiler's lexer ends `scan-ident-rest` with
    ///
    ///     in let __seq = st.offset = stop
    ///     in let __seq = st.column = new-col
    ///     in st
    ///
    /// and returns the same `st` it was handed, expecting the two assignments
    /// to be visible in it. This arm used to build a NEW record and return it,
    /// so the sequence threw the update away and the scanner re-read the same
    /// character forever -- `"x"` lexed in 692 steps and `"xy"` never finished.
    ///
    /// The alternative was to rebind the assigned NAME for the rest of the
    /// sequence, which is cheaper and covers all 49 sites in the checkout,
    /// every one of which assigns through a plain local. It was rejected
    /// because it cannot be made to FAIL LOUDLY when a second binding aliases
    /// the same record: at the moment of assignment the record is already held
    /// by the environment and by the evaluator, so a reference count cannot
    /// separate an innocent alias from a live one. An interpreter whose answer
    /// depends on how a program NAMES a value, silently, is worse than a slower
    /// one.
    ///
    /// `Rc<RefCell<..>>` is still one pointer, so `Value` stays 16 bytes -- the
    /// property that made `Rc<str>` cost 16% does not apply here.
    Record(Sym, Rc<RefCell<Vec<(Sym, Value)>>>),
    /// A variant constructor, saturated or not.
    Ctor(Sym, Rc<Vec<Value>>),
    Fun(Rc<Closure>),
    /// `Nothing` and friends -- a nullary name we do not otherwise know.
    Unit,
}

/// What a saturated closure RUNS.
///
/// A constructor and a builtin used to be encoded as a `NameRef` holding
/// `__ctor:`/`__builtin:` and the name -- which meant a `format!` on every
/// reference and a `to_string` on every call to take the prefix back off.
/// Naming the three cases allocates nothing.
#[derive(Clone, Debug)]
pub enum Body {
    /// A definition's or a lambda's compiled body.
    Code(Rc<Code>),
    /// A variant constructor: the arguments ARE the value.
    Ctor(Sym),
    /// A compiler builtin, resolved to its name once.
    Builtin(&'static str),
}

#[derive(Debug)]
pub struct Closure {
    /// How many arguments saturate it. The parameters have NAMES in the
    /// source and none here: `crate::code` turned every reference to one into
    /// a slot in this call's frame, so the run never asks what they were.
    pub arity: usize,
    pub body: Body,
    pub env: Env,
    pub applied: Vec<Value>,
}

pub type Env = Rc<Scope>;

/// One frame: the values, positionally.
///
/// A call binds its whole parameter list at once; a `let` binding, an `act`
/// bind and a match arm's captures each get a frame of their own, in the order
/// the compiler counted them. A name never appears, so a lookup is `hops`
/// pointer hops and an index -- no comparison, no hashing, no allocation.
#[derive(Debug)]
pub struct Scope {
    vals: Vec<Value>,
    parent: Option<Env>,
}

impl Scope {
    fn root() -> Env {
        Rc::new(Scope { vals: Vec::new(), parent: None })
    }
    fn get(&self, hops: u32, slot: u32) -> Option<Value> {
        let mut here = self;
        for _ in 0..hops {
            here = here.parent.as_deref()?;
        }
        here.vals.get(slot as usize).cloned()
    }
    fn push(parent: &Env, vals: Vec<Value>) -> Env {
        Rc::new(Scope { vals, parent: Some(parent.clone()) })
    }
}

pub struct Error(pub String);

/// What evaluating an expression in TAIL POSITION produced.
///
/// **Codex has no loop construct: iteration IS tail recursion.**
/// `scan-ident-end source (offset + 1) len` recurses once per byte of the
/// source, so on the compiler's own 2.98 MB that is millions of frames deep.
/// Cobblestone's zig emitter turns a self-call into a `while (true)` for the
/// same reason. An interpreter that recurses per iteration needs a stack frame
/// per byte and cannot finish; one that LOOPS needs one.
enum Step {
    Done(Value),
    /// A saturated call to make next, in place of the one that just returned.
    Call(Rc<Closure>, Vec<Value>),
}

type R<T> = Result<T, Error>;

fn err<T>(msg: impl Into<String>) -> R<T> {
    Err(Error(msg.into()))
}

/// Stamp a location on an error that does not have one. The innermost frame
/// wins, which is the one a reader wants.
fn at(e: Error, sp: Span) -> Error {
    if e.0.starts_with('L') {
        e
    } else {
        Error(format!("L{}C{}: {}", sp.line, sp.col, e.0))
    }
}

/// A record field whose declared type carries a bound, and what to do at it.
#[derive(Clone, Copy, Debug)]
pub struct FieldBound {
    pub lo: i64,
    pub hi: i64,
    pub mode: OverflowMode,
}

pub struct Interp {
    /// Every top-level function, constructor and builtin of one argument or
    /// more, as a ready value. `Code::Global` indexes this, so a reference is
    /// an index and a refcount.
    globals: Vec<Value>,
    /// The compiled bodies of the definitions that take NO parameters. A
    /// reference evaluates one; Codex is pure, so that is a cost and not a
    /// meaning.
    const_defs: Vec<Rc<Code>>,
    /// The value of each nullary that has already been forced, and whether it
    /// is one we are allowed to keep.
    ///
    /// **A nullary is re-evaluated at every mention, and that is a whole
    /// complexity class on the tables this compiler is pointed at.** Measured
    /// on safari's `build-world`: one mention costs about 350,000 steps, two
    /// cost 700,000, exactly linear. `pose-rest-polys` is 2,198 records rebuilt
    /// per mention. The game's own port notes record the same shape from the
    /// other side -- PORTING_NOTES B13, a nullary emits as a FUNCTION in zig
    /// and allocates per call, per frame.
    ///
    /// Codex bindings are pure, so forcing one twice can only cost. THE GUARD
    /// IS THE EFFECT ROW AND NOTHING ELSE: `opening : [Console] Nothing` is
    /// also a nullary, and an act performed once is not an act performed twice.
    /// A definition with no annotation at all is not cached either, because
    /// what is not declared is not known here -- the checker infers, this pass
    /// does not.
    ///
    /// This is a place the Rust arm deliberately does BETTER than the zig,
    /// rather than the same. The output is identical because the language is
    /// pure; only the work differs.
    const_cache: Vec<Option<Value>>,
    const_cacheable: Vec<bool>,
    /// `opening`, compiled in the empty environment.
    opening: Option<Rc<Code>>,
    /// `Type.field -> bound`, and the ONE thing resolution cannot do ahead of
    /// time. A record literal names its type, so its bounds are attached at
    /// compile time; a field ASSIGNMENT names only the field, and which record
    /// it lands on is whatever the left-hand side evaluates to.
    bounds: HashMap<(Sym, Sym), FieldBound>,
    /// Spells a name when one has to be printed: an error, or `show`.
    syms: SymTab,
    /// The empty environment, shared: every top-level closure closes over it.
    root: Env,
    /// Names defined in more than one chapter of a bundled unit.
    /// `drive-unit.codex` has two `bar-quad`s -- one over `ScreenPt` and one
    /// over `RiderPt` -- and keeping only the last silently gave the wrong one
    /// to every caller of the other. Reported, not used: resolving them is
    /// `crate::code`'s job and it happens before the run.
    pub collisions: Vec<String>,
    pub out: String,
    /// How much work the run did, which is the only speed number that is not
    /// about this machine on this day.
    pub steps: u64,
    depth: u32,
    limit: u64,
    /// THE ALLOCATOR'S BOOKKEEPING, AND NOTHING IS ALLOCATED.
    ///
    /// The compiler manages its own memory: a bump heap with a deck growing
    /// under it, `__heap-advance` to reserve, `__heap-restore` to give back,
    /// and `phase-compact` -- which is exactly `__heap-restore (__deck-pos)` --
    /// between phases. On bare metal and in the plugs that is real. Here the
    /// host allocator does the job, so these two counters carry the ARITHMETIC
    /// and none of the memory.
    ///
    /// They are not zero and they are not constant, because the compiler asks
    /// them questions. `deck-short-of ceiling band` is
    /// `__deck-pos + band >= ceiling`, and `heap-short-of` the same over
    /// `__heap-save`, so a position frozen at zero would answer those two the
    /// way a machine with no memory left does, or the way one with infinite
    /// memory does, depending on the ceiling -- and neither is the answer a
    /// real run gives. Moving them the way a bump allocator moves them is the
    /// cheapest model that gets those two predicates right.
    ///
    /// **WHAT THIS ARM THEREFORE CANNOT SEE.** Every defect the deck bracket
    /// has produced upstream -- a lifetime error, a value read after the
    /// bracket reclaimed it, a tag read out of raw memory -- is invisible from
    /// here, because nothing here reclaims anything. Agreement between this arm
    /// and bare metal is evidence about the SEMANTICS and silence about the
    /// memory discipline. Do not let a green line be read as covering both.
    heap_pos: i64,
    deck_pos: i64,
    /// Each constructor's position in its own variant declaration, which is
    /// what `variant-tag` answers.
    tags: HashMap<Sym, i64>,
}

/// The default budget for ONE program: effectively none.
///
/// A step limit exists to bound a SWEEP, where one runaway program would
/// otherwise own the machine. Applying a sweep's budget to a single run makes
/// the tool refuse work it could do -- `ride-unit` simulates a whole ride and
/// legitimately needs hundreds of millions of steps.
const STEP_LIMIT: u64 = u64::MAX;
/// Codex recursion is unbounded and ours is a Rust call stack, so a runaway
/// program has to be caught by a counter rather than by the operating system:
/// a stack overflow aborts the process and takes the whole sweep with it.
const DEPTH_LIMIT: u32 = 20_000;

impl Interp {
    /// Build the tables, then compile the chapter against them.
    ///
    /// **Every index is handed out before any body is compiled**, because a
    /// body may name a definition that comes after it -- so the globals vector
    /// is sized and filled in two passes rather than one.
    pub fn new(ch: &Chapter) -> Interp {
        let root = Scope::root();
        let mut names = Names::default();
        let mut globals: Vec<Value> = Vec::new();

        // Pass 1: an index for every definition, and who owns each name.
        let mut fun_defs: Vec<(u32, &Def)> = Vec::new();
        let mut const_defs_src: Vec<&Def> = Vec::new();
        let mut owners: HashMap<Sym, Vec<&str>> = HashMap::new();
        for d in &ch.defs {
            let slugs = owners.entry(d.name).or_default();
            if !slugs.contains(&d.chapter_slug.as_str()) {
                slugs.push(d.chapter_slug.as_str());
            }
            let key = (d.chapter_slug.clone(), d.name.clone());
            if d.params.is_empty() {
                let i = const_defs_src.len() as u32;
                const_defs_src.push(d);
                names.consts.insert(d.name, i);
                names.by_chapter_const.insert(key, i);
            } else {
                let i = globals.len() as u32;
                globals.push(Value::Unit);
                fun_defs.push((i, d));
                names.funs.insert(d.name, i);
                names.by_chapter_fun.insert(key, i);
            }
        }
        let mut collisions: Vec<String> = owners
            .iter()
            .filter(|(_, s)| s.len() > 1)
            .map(|(n, _)| ch.syms.text(*n).to_string())
            .collect();
        collisions.sort();
        names.colliding =
            owners.iter().filter(|(_, s)| s.len() > 1).map(|(n, _)| *n).collect();

        // Record field bounds, and a slot for every constructor.
        let mut ctors: Vec<(u32, Sym, usize)> = Vec::new();
        let mut tags: HashMap<Sym, i64> = HashMap::new();
        for t in &ch.type_defs {
            match t {
                TypeDef::Record(name, _, fields, ..) => {
                    for f in fields {
                        if let TypeExpr::BoundedInt(_, lo, hi, mode, _) = &f.type_expr {
                            names.bounds.insert(
                                (*name, f.name),
                                FieldBound { lo: *lo, hi: *hi, mode: *mode },
                            );
                        }
                    }
                }
                TypeDef::Variant(_, _, cs, _) => {
                    for (tag, c) in cs.iter().enumerate() {
                        let i = globals.len() as u32;
                        globals.push(Value::Unit);
                        names.ctors.insert(c.name, i);
                        // THE TAG IS THE CONSTRUCTOR'S POSITION IN ITS OWN
                        // DECLARATION, which is what `variant-tag` answers and
                        // what the unifier compares. It is only correct if this
                        // walk keeps the declared order, so it reads the order
                        // rather than sorting or hashing.
                        tags.insert(c.name, tag as i64);
                        ctors.push((i, c.name, c.fields.len()));
                    }
                }
                TypeDef::Unit(..) => {}
            }
        }

        // The arity comes from the compiler's own table, not from a list here:
        // a builtin applied to the wrong number of arguments would otherwise be
        // a silent partial application rather than a call.
        //
        // **`Some(0)` IS NOT `None` AND NEITHER IS ONE.** Both used to be read
        // as "declares no type" and given an arity of one, so `get-ticks :
        // Integer` -- a value -- became a function of one argument, and a
        // reference to it bound a `Fun` where an Integer belonged. Nothing
        // failed there: it failed fifteen lines away, in `keys-collision`, as
        // ``builtin `bit-and` is not interpreted yet (given a function, an
        // integer)`` -- a wrong-arity bug wearing a missing-feature message.
        for (name, arity) in crate::builtins::BUILTINS {
            match arity {
                None => {
                    if let Some(s) = ch.syms.find(name) {
                        names.builtin_undeclared.insert(s, name);
                    }
                }
                Some(0) => {
                    if let Some(s) = ch.syms.find(name) {
                        names.builtin_nullary.insert(s, name);
                    }
                }
                Some(arity) => {
                    // A builtin the chapter never names cannot be what any
                    // symbol here means, so it needs no slot.
                    let Some(sym) = ch.syms.find(name) else { continue };
                    let i = globals.len() as u32;
                    globals.push(Value::Fun(Rc::new(Closure {
                        arity,
                        body: Body::Builtin(name),
                        env: root.clone(),
                        applied: Vec::new(),
                    })));
                    names.builtin_funs.insert(sym, i);
                }
            }
        }

        // Constructors are FIXED for the run, so their values are built here
        // and every reference clones one refcount.
        for (i, name, arity) in ctors {
            let rc = name;
            globals[i as usize] = if arity == 0 {
                Value::Ctor(rc, Rc::new(Vec::new()))
            } else {
                Value::Fun(Rc::new(Closure {
                    arity,
                    body: Body::Ctor(rc),
                    env: root.clone(),
                    applied: Vec::new(),
                }))
            };
        }

        // Pass 2: compile. The tables are complete, so a body can name
        // anything the unit defines regardless of where it sits.
        let mut const_defs: Vec<Rc<Code>> = Vec::with_capacity(const_defs_src.len());
        let mut const_cacheable: Vec<bool> = Vec::with_capacity(const_defs_src.len());
        for d in &const_defs_src {
            const_defs.push(Rc::new(Compiler::body(&names, &ch.syms, &d.chapter_slug, &d.body)));
            const_cacheable.push(match d.declared_type.first() {
                Some(t) => !mentions_effect(t),
                None => false,
            });
        }
        for (i, d) in &fun_defs {
            globals[*i as usize] = Value::Fun(Rc::new(Closure {
                arity: d.params.len(),
                body: Body::Code(Rc::new(Compiler::def(&names, &ch.syms, d))),
                env: root.clone(),
                applied: Vec::new(),
            }));
        }
        // The entry point runs in the EMPTY environment, whatever it declares,
        // which is what the walker did. Last definition of the name wins, as
        // it does everywhere else.
        let opening = ch
            .defs
            .iter()
            .rev()
            .find(|d| Some(d.name) == ch.syms.find("opening"))
            .map(|d| Rc::new(Compiler::body(&names, &ch.syms, &d.chapter_slug, &d.body)));

        Interp {
            globals,
            const_cache: vec![None; const_defs.len()],
            const_cacheable,
            const_defs,
            opening,
            bounds: names.bounds,
            syms: ch.syms.clone(),
            root,
            collisions,
            out: String::new(),
            steps: 0,
            depth: 0,
            limit: STEP_LIMIT,
            heap_pos: 0,
            deck_pos: 0,
            tags,
        }
    }

    /// Bound this run to a number of steps. The sweep sets one; a single run
    /// does not.
    pub fn with_budget(mut self, steps: u64) -> Self {
        self.limit = steps;
        self
    }

    /// Run `opening`, the entry point every Codex program has.
    pub fn run(&mut self) -> R<()> {
        let Some(open) = self.opening.clone() else {
            return err("no `opening` definition to run");
        };
        let env = self.root.clone();
        self.eval(&open, &env)?;
        Ok(())
    }

    fn eval(&mut self, c: &Code, env: &Env) -> R<Value> {
        self.steps += 1;
        if self.steps > self.limit {
            return err("step limit reached; the program did not finish");
        }
        self.depth += 1;
        if self.depth > DEPTH_LIMIT {
            self.depth -= 1;
            return err("recursion limit reached");
        }
        let r = self.eval_inner(c, env);
        self.depth -= 1;
        r
    }

    fn eval_inner(&mut self, c: &Code, env: &Env) -> R<Value> {
        match c {
            Code::Const(v) => Ok(v.clone()),
            Code::Local(hops, slot) => env
                .get(*hops, *slot)
                .ok_or_else(|| Error(format!("internal: no local at ({hops}, {slot})"))),
            Code::Global(i) => Ok(self.globals[*i as usize].clone()),
            Code::ConstDef(i) => {
                let i = *i as usize;
                if let Some(v) = &self.const_cache[i] {
                    return Ok(v.clone());
                }
                let body = self.const_defs[i].clone();
                let root = self.root.clone();
                let v = self.eval(&body, &root)?;
                // Only after it returns: a self-referential nullary must still
                // recurse to its own error rather than see a half-built answer.
                if self.const_cacheable[i] {
                    self.const_cache[i] = Some(v.clone());
                }
                Ok(v)
            }
            Code::NullaryBuiltin(name) => self.builtin(name, Vec::new()),
            Code::Fail(msg) => Err(Error(msg.clone())),
            Code::Unsupported(msg) => err(*msg),
            Code::Apply(head, args) => match self.apply_spine(head, args, env, false)? {
                Step::Done(v) => Ok(v),
                Step::Call(c, applied) => self.call(c, applied),
            },
            Code::Binary(l, op, r) => {
                // `and` and `or` SHORT-CIRCUIT, and programs depend on it for
                // safety rather than speed:
                //
                //   list-length c.segs > 0 and list-at c.segs (... - 1) == s
                //
                // evaluates `list-at` on an empty list if the right operand is
                // taken eagerly. `&` is short-circuited too when its left is a
                // boolean -- for text, lists and integers it is not a
                // conjunction at all, and the left says which.
                let a = self.eval(l, env)?;
                match (op, &a) {
                    (BinaryOp::OpBoolAnd | BinaryOp::OpAnd, Value::Bool(false)) => {
                        return Ok(Value::Bool(false))
                    }
                    (BinaryOp::OpOr, Value::Bool(true)) => return Ok(Value::Bool(true)),
                    _ => {}
                }
                let b = self.eval(r, env)?;
                binary(&self.syms, *op, a, b)
            }
            Code::Unary(x) => match self.eval(x, env)? {
                Value::Int(i) => Ok(Value::Int(-i)),
                Value::Real(f) => Ok(Value::Real(-f)),
                v => err(format!("negation of {}", type_name(&v))),
            },
            Code::If(c, t, f) => match self.eval(c, env)? {
                Value::Bool(true) => self.eval(t, env),
                Value::Bool(false) => self.eval(f, env),
                v => err(format!("`if` on {}", type_name(&v))),
            },
            Code::Let(vals, body) => {
                let mut env = env.clone();
                for v in vals {
                    let v = self.eval(v, &env)?;
                    env = Scope::push(&env, vec![v]);
                }
                self.eval(body, &env)
            }
            // The body is already shared: a lambda evaluated a million times
            // bumps a refcount rather than copying its tree.
            Code::Lambda(l) => Ok(Value::Fun(Rc::new(Closure {
                arity: l.arity,
                body: Body::Code(l.body.clone()),
                env: env.clone(),
                applied: Vec::new(),
            }))),
            Code::Match(scrut, arms) => {
                let v = self.eval(scrut, env)?;
                self.match_arms(&v, arms, env)
            }
            Code::List(xs) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.eval(x, env)?);
                }
                Ok(Value::List(Rc::new(out)))
            }
            Code::Record(name, fields) => {
                let mut out = Vec::with_capacity(fields.len());
                for f in fields {
                    let mut v = self.eval(&f.value, env)?;
                    // The declared bound is syntax, so it is applied here.
                    if let (Value::Int(i), Some(b)) = (&v, &f.bound) {
                        v = Value::Int(apply_bound(*i, b));
                    }
                    out.push((f.name.clone(), v));
                }
                Ok(Value::Record(name.clone(), Rc::new(RefCell::new(out))))
            }
            Code::FieldAccess(obj, field, sp) => match self.eval(obj, env)? {
                Value::Record(name, fs) => fs
                    .borrow()
                    .iter()
                    .find(|(n, _)| n == field)
                    .map(|(_, v)| v.clone())
                    .ok_or_else(|| {
                        Error(format!(
                            "L{}C{}: `{}` has no field `{}` (it has {})",
                            sp.line,
                            sp.col,
                            self.syms.text(name),
                            self.syms.text(*field),
                            fs.borrow()
                                .iter()
                                .map(|(n, _)| self.syms.text(*n))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ))
                    }),
                v => err(format!(
                    "L{}C{}: field `{}` read from {}",
                    sp.line,
                    sp.col,
                    self.syms.text(*field),
                    type_name(&v)
                )),
            },
            Code::Act(stmts) => {
                let mut env = env.clone();
                let mut last = Value::Unit;
                for s in stmts {
                    match s {
                        Stmt::Exec(e) => last = self.eval(e, &env)?,
                        Stmt::Bind(e) => {
                            let v = self.eval(e, &env)?;
                            env = Scope::push(&env, vec![v]);
                            last = Value::Unit;
                        }
                    }
                }
                Ok(last)
            }
            Code::Lazy(inner) => self.eval(inner, env),
            Code::FieldAssign(rec, field, val) => {
                let base = self.eval(rec, env)?;
                let v = self.eval(val, env)?;
                match base {
                    Value::Record(name, fs) => {
                        let bound = self.bounds.get(&(name, *field));
                        let v = match (&v, bound) {
                            (Value::Int(i), Some(b)) => Value::Int(apply_bound(*i, b)),
                            _ => v,
                        };
                        {
                            // The borrow is scoped so that nothing re-enters
                            // the evaluator while it is held -- `v` is already
                            // a value and the bound is already applied.
                            let mut out = fs.borrow_mut();
                            match out.iter_mut().find(|(n, _)| n == field) {
                                Some(slot) => slot.1 = v,
                                None => out.push((*field, v)),
                            }
                        }
                        // THE SAME RECORD, not a copy of it. Every other
                        // binding that reaches this one sees the assignment,
                        // which is what the compiler's `in ... in st` relies on.
                        Ok(Value::Record(name, fs))
                    }
                    v => err(format!("field assignment on {}", type_name(&v))),
                }
            }
        }
    }

    /// Run a saturated closure, looping on every tail call rather than
    /// recursing. Non-tail calls still nest, which is what a call stack is
    /// for; this is only about the ones that do not need to.
    fn call(&mut self, mut c: Rc<Closure>, mut applied: Vec<Value>) -> R<Value> {
        loop {
            let body = match &c.body {
                Body::Ctor(name) => return Ok(Value::Ctor(name.clone(), Rc::new(applied))),
                Body::Builtin(name) => {
                    let name = *name;
                    return self.builtin(name, applied);
                }
                Body::Code(b) => b.clone(),
            };
            let env = Scope::push(&c.env, applied);
            match self.eval_tail(&body, &env)? {
                Step::Done(v) => return Ok(v),
                Step::Call(next, args) => {
                    c = next;
                    applied = args;
                }
            }
        }
    }

    /// Evaluate, but hand a tail call BACK instead of making it.
    ///
    /// The tail positions are the ones that cannot do any work after the call
    /// returns: both branches of an `if`, the body of a `let`, an arm's body,
    /// and the last statement of an `act`.
    fn eval_tail(&mut self, c: &Code, env: &Env) -> R<Step> {
        self.steps += 1;
        if self.steps > self.limit {
            return err("step limit reached; the program did not finish");
        }
        match c {
            Code::If(c, t, f) => match self.eval(c, env)? {
                Value::Bool(true) => self.eval_tail(t, env),
                Value::Bool(false) => self.eval_tail(f, env),
                v => err(format!("`if` on {}", type_name(&v))),
            },
            Code::Let(vals, body) => {
                let mut env = env.clone();
                for v in vals {
                    let v = self.eval(v, &env)?;
                    env = Scope::push(&env, vec![v]);
                }
                self.eval_tail(body, &env)
            }
            Code::Match(scrut, arms) => {
                let v = self.eval(scrut, env)?;
                for a in arms.iter() {
                    let mut vals = Vec::with_capacity(a.nvars);
                    if !matches_pat(&v, &a.pat, &mut vals) {
                        continue;
                    }
                    let arm_env = Scope::push(env, vals);
                    if let Value::Bool(false) = self.eval(&a.guard, &arm_env)? {
                        continue;
                    }
                    return self.eval_tail(&a.body, &arm_env);
                }
                err("no match arm applied")
            }
            Code::Act(stmts) => {
                let mut env = env.clone();
                for (i, s) in stmts.iter().enumerate() {
                    let last = i + 1 == stmts.len();
                    match s {
                        Stmt::Exec(e) if last => return self.eval_tail(e, &env),
                        Stmt::Exec(e) => {
                            self.eval(e, &env)?;
                        }
                        Stmt::Bind(e) => {
                            let v = self.eval(e, &env)?;
                            env = Scope::push(&env, vec![v]);
                        }
                    }
                }
                Ok(Step::Done(Value::Unit))
            }
            Code::Apply(head, args) => self.apply_spine(head, args, env, true),
            _ => Ok(Step::Done(self.eval(c, env)?)),
        }
    }

    /// Apply a whole spine, gathering the arguments for one call instead of
    /// building a closure per argument.
    ///
    /// **Application is curried -- `f a b c` is three nested `Apply` nodes --
    /// but the call is not.** Taking them one at a time allocated an
    /// intermediate closure, its argument vector and a clone of every argument
    /// already applied, per argument: `map-list-loop` has five parameters, so
    /// every one of its calls built four closures it then threw away. The
    /// spine itself is flattened by `crate::code`, once, rather than re-walked
    /// into a fresh `Vec` on every application.
    ///
    /// **The ORDER is unchanged, and that is the whole constraint.** Arguments
    /// are still evaluated left to right, and a call that saturates PART WAY
    /// down the spine still runs before the arguments after it are evaluated
    /// -- `f a b` where `f` takes one argument runs `f a` before `b`.
    ///
    /// `tail` says whether the caller can loop on the last call rather than
    /// nesting; only `eval_tail` can.
    fn apply_spine(
        &mut self,
        head: &Code,
        args: &[(Code, Span)],
        env: &Env,
        tail: bool,
    ) -> R<Step> {
        // The nodes are still there and still evaluated; only the closures in
        // between are gone. Counting them keeps `steps` a measure of the
        // PROGRAM's work rather than of this interpreter's shape, so a rate
        // before this change and one after it are the same number.
        self.steps += args.len() as u64 - 1;
        let mut f = self.eval(head, env)?;
        let mut i = 0;
        while i < args.len() {
            let fun = match &f {
                Value::Fun(c) => Some(c.clone()),
                _ => None,
            };
            let Some(c) = fun.filter(|c| c.arity > c.applied.len()) else {
                // A constructor takes its fields one at a time, and anything
                // else is an error the one-argument path words properly.
                let (a, sp) = &args[i];
                let arg = self.eval(a, env)?;
                f = self.apply(f, arg).map_err(|e| at(e, *sp))?;
                i += 1;
                continue;
            };
            let take = (c.arity - c.applied.len()).min(args.len() - i);
            let mut applied = Vec::with_capacity(c.arity);
            applied.extend_from_slice(&c.applied);
            let sp = args[i + take - 1].1;
            for (a, _) in &args[i..i + take] {
                applied.push(self.eval(a, env)?);
            }
            i += take;
            if applied.len() < c.arity {
                f = Value::Fun(Rc::new(Closure {
                    arity: c.arity,
                    body: c.body.clone(),
                    env: c.env.clone(),
                    applied,
                }));
            } else if tail && i == args.len() {
                return Ok(Step::Call(c, applied));
            } else {
                f = self.call(c, applied).map_err(|e| at(e, sp))?;
            }
        }
        Ok(Step::Done(f))
    }

    /// Apply one argument. A saturated closure comes back as a pending call so
    /// the caller can loop on it; everything else is finished here.
    fn apply_step(&mut self, f: Value, arg: Value) -> R<Step> {
        if let Value::Ctor(n, fields) = &f {
            let mut out = (**fields).clone();
            out.push(arg);
            return Ok(Step::Done(Value::Ctor(n.clone(), Rc::new(out))));
        }
        let Value::Fun(c) = f else {
            return err(format!("applied {} to an argument", type_name(&f)));
        };
        let mut applied = c.applied.clone();
        applied.push(arg);
        if applied.len() < c.arity {
            return Ok(Step::Done(Value::Fun(Rc::new(Closure {
                arity: c.arity,
                body: c.body.clone(),
                env: c.env.clone(),
                applied,
            }))));
        }
        Ok(Step::Call(c, applied))
    }

    fn apply(&mut self, f: Value, arg: Value) -> R<Value> {
        match self.apply_step(f, arg)? {
            Step::Done(v) => Ok(v),
            Step::Call(c, applied) => self.call(c, applied),
        }
    }

    fn match_arms(&mut self, v: &Value, arms: &[Arm], env: &Env) -> R<Value> {
        for a in arms {
            let mut vals = Vec::with_capacity(a.nvars);
            if !matches_pat(v, &a.pat, &mut vals) {
                continue;
            }
            let env = Scope::push(env, vals);
            match self.eval(&a.guard, &env)? {
                Value::Bool(false) => continue,
                _ => return self.eval(&a.body, &env),
            }
        }
        err("no match arm applied")
    }

    fn builtin(&mut self, name: &str, args: Vec<Value>) -> R<Value> {
        use Value::*;
        let text = |s: String| Ok(Text(Rc::new(s)));
        match (name, args.as_slice()) {
            // -- console ------------------------------------------------------
            ("print-line-uni" | "print-line", [v]) => {
                // Spelled BEFORE the write: `show` reads the table and the
                // write takes the output buffer, and they are the same `self`.
                let line = show(&self.syms, v);
                let _ = writeln!(self.out, "{line}");
                Ok(Unit)
            }
            ("print-uni" | "print", [v]) => {
                let part = show(&self.syms, v);
                let _ = write!(self.out, "{part}");
                Ok(Unit)
            }

            // -- text ---------------------------------------------------------
            ("show" | "integer-to-text", [v]) => text(show(&self.syms, v)),
            ("text-length", [Text(t)]) => Ok(Int(t.len() as i64)),
            ("char-at", [Text(t), Int(i)]) => t
                .as_bytes()
                .get(*i as usize)
                .map(|b| Char(*b as char))
                .ok_or_else(|| Error(format!("char-at {i} past the end"))),
            // `char-code-at` indexes BYTES, and `char-code` is the private
            // frequency alphabet -- not ASCII. `char-code 'A'` is 41.
            ("char-code-at", [Text(t), Int(i)]) => Ok(Int(t
                .as_bytes()
                .get(*i as usize)
                .map(|b| char_code(*b))
                .unwrap_or(0))),
            ("char-code", [Char(c)]) => Ok(Int(char_code(*c as u8))),
            ("code-to-char", [Int(c)]) => Ok(Char(code_to_char(*c))),
            ("char-to-text" | "char-encode", [Char(c)]) => text(c.to_string()),
            ("substring", [Text(t), Int(start), Int(len)]) => {
                let b = t.as_bytes();
                let s = (*start).clamp(0, b.len() as i64) as usize;
                let e = (s + (*len).max(0) as usize).min(b.len());
                text(String::from_utf8_lossy(&b[s..e]).into_owned())
            }
            ("text-contains", [Text(a), Text(b)]) => Ok(Bool(a.contains(&**b))),
            ("text-starts-with", [Text(a), Text(b)]) => Ok(Bool(a.starts_with(&**b))),
            ("text-ends-with", [Text(a), Text(b)]) => Ok(Bool(a.ends_with(&**b))),
            ("text-replace", [Text(a), Text(b), Text(c)]) => text(a.replace(&**b, c)),
            ("text-to-integer", [Text(t)]) => Ok(Int(t.trim().parse().unwrap_or(0))),
            // `text-compare` is over CCE bytes, which is char-code order and
            // not ASCII order.
            ("text-compare", [Text(a), Text(b)]) => {
                let (x, y) = (crate::preamble::cce_key(a), crate::preamble::cce_key(b));
                Ok(Int(match x.cmp(&y) {
                    std::cmp::Ordering::Less => -1,
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Greater => 1,
                }))
            }
            // THESE THREE ARE RANGES ON THE CHAR-CODE, not Unicode classes,
            // and the emitter is the oracle for them. Each is a `sub`, a `cmp`
            // and a `setbe` -- an UNSIGNED window on the frequency alphabet:
            //
            //   is-whitespace   (c - 1)  <= 1   ->  1..=2    newline, space
            //   is-digit        (c - 3)  <= 9   ->  3..=12   the ten digits
            //   is-letter       (c - 13) <= 51  ->  13..=64  lower then upper
            //                or (c - 97) <= 30  ->  97..=127 the extended band
            //
            // Rust's `is_alphabetic` and `is_ascii_digit` agree on ASCII, but
            // only because the alphabet was built that way -- they agree by
            // coincidence and disagree above it. `is-whitespace` is the one
            // that shows it: a tab and a carriage return are NOT whitespace
            // here, because the alphabet gives them no code at all.
            ("is-letter", [Char(c)]) => {
                let k = char_code(*c as u8);
                Ok(Bool((13..=64).contains(&k) || (97..=127).contains(&k)))
            }
            ("is-digit", [Char(c)]) => Ok(Bool((3..=12).contains(&char_code(*c as u8)))),
            ("is-whitespace", [Char(c)]) => {
                Ok(Bool((1..=2).contains(&char_code(*c as u8))))
            }
            // `List Integer -> Text`, the bytes as written.
            ("raw-bytes-to-text", [List(xs)]) => {
                let bytes: Vec<u8> =
                    xs.iter().map(|v| if let Int(i) = v { *i as u8 } else { 0 }).collect();
                text(String::from_utf8_lossy(&bytes).into_owned())
            }

            // -- lists --------------------------------------------------------
            ("list-length", [List(xs)]) => Ok(Int(xs.len() as i64)),
            ("list-at", [List(xs), Int(i)]) => (*i >= 0)
                .then(|| xs.get(*i as usize).cloned())
                .flatten()
                .ok_or_else(|| Error(format!("list-at {i} of a {}-element list", xs.len()))),
            // `list-snoc` and `list-push` are ONE operation: the zig emitter
            // gives both the same `cx_ll_push(l, v)`, an append at the end.
            ("list-push" | "list-snoc", [List(xs), v]) => {
                let mut out = (**xs).clone();
                out.push(v.clone());
                Ok(List(Rc::new(out)))
            }
            ("list-insert-at", [List(xs), Int(i), v]) => {
                let mut out = (**xs).clone();
                let i = *i;
                if i < 0 || i as usize > out.len() {
                    return err(format!("list-insert-at {i} of a {}-element list", out.len()));
                }
                out.insert(i as usize, v.clone());
                Ok(List(Rc::new(out)))
            }
            // The capacity is an allocation hint upstream -- `cx_ll_empty` then
            // `ensureTotalCapacityPrecise` -- and the LIST IS EMPTY. It is
            // load-bearing over there for a reason that cannot exist here: a
            // reallocation inside emit-all-defs' save/restore bracket lands in
            // scratch the bracket reclaims. Nothing here reclaims anything.
            ("__list-with-capacity", [Int(_)]) => Ok(List(Rc::new(Vec::new()))),
            ("list-set-at", [List(xs), Int(i), v]) => {
                let mut out = (**xs).clone();
                let i = *i as usize;
                if i >= out.len() {
                    return err(format!("list-set-at {i} past the end"));
                }
                out[i] = v.clone();
                Ok(List(Rc::new(out)))
            }

            // -- arithmetic ---------------------------------------------------
            // `negate : forall a. a -> a` -- polymorphic upstream, and the one
            // arithmetic builtin that is. `abs`, `max` and `min` are Integer
            // only, and stay that way.
            ("negate", [Int(i)]) => Ok(Int(-i)),
            ("negate", [Real(f)]) => Ok(Real(-f)),
            ("abs", [Int(i)]) => Ok(Int(i.abs())),
            ("max", [Int(a), Int(b)]) => Ok(Int(*a.max(b))),
            ("min", [Int(a), Int(b)]) => Ok(Int(*a.min(b))),
            ("int-mod", [Int(a), Int(b)]) if *b != 0 => Ok(Int(a.rem_euclid(*b))),
            ("int-rem", [Int(a), Int(b)]) if *b != 0 => Ok(Int(a % b)),
            ("int-mod" | "int-rem", [Int(_), Int(_)]) => err("modulo by zero"),
            ("bit-and", [Int(a), Int(b)]) => Ok(Int(a & b)),
            ("bit-or", [Int(a), Int(b)]) => Ok(Int(a | b)),
            ("bit-xor", [Int(a), Int(b)]) => Ok(Int(a ^ b)),
            ("bit-not", [Int(a)]) => Ok(Int(!a)),
            ("bit-shl", [Int(a), Int(b)]) => Ok(Int(((*a as u64) << (*b as u32 & 63)) as i64)),
            ("bit-shr" | "bit-shru", [Int(a), Int(b)]) => {
                Ok(Int(((*a as u64) >> (*b as u32 & 63)) as i64))
            }
            ("text-split", [Text(t), Text(sep)]) => Ok(List(Rc::new(
                if sep.is_empty() {
                    vec![Text(t.clone())]
                } else {
                    t.split(&**sep).map(|p| Text(Rc::new(p.to_string()))).collect()
                },
            ))),

            // -- reals --------------------------------------------------------
            // ONE ARM FOR EIGHT NAMES WAS WRONG ABOUT FIVE OF THEM. Only the
            // two `*-from-int` take an Integer; the rest take a REAL, so the
            // arm never matched and they failed as "no rule for (a real)".
            // `to-real` is not a builtin at all. The declared types:
            //
            //   real-from-int              Integer -> f64
            //   real-approx-from-int       Integer -> f32   <- NARROWS
            //   to-real-approx             f64     -> f32   <- NARROWS
            //   to-real-trapping           f64     -> f64-trapping
            //   to-real-saturating         f64     -> f64-saturating
            //   to-real-approx-trapping    f32     -> f32-trapping
            //   to-real-approx-saturating  f32     -> f32-saturating
            //
            // The trapping and saturating ones change the OVERFLOW MODE and
            // not the value, so they are the identity here; the two that end
            // in f32 must round through f32 or a large value comes back with
            // digits an f32 cannot hold.
            ("real-from-int", [Int(i)]) => Ok(Real(*i as f64)),
            ("real-approx-from-int", [Int(i)]) => Ok(Real(*i as f32 as f64)),
            ("to-real-approx", [Real(f)]) => Ok(Real(*f as f32 as f64)),
            // The `from-real-*` direction WIDENS or drops an overflow mode --
            // `from-real-approx : f32 -> f64`, `from-real-trapping :
            // f64-trapping -> f64`. Every Real here is already an f64, and the
            // f32 ones arrived rounded, so each is the identity on the value.
            (
                "from-real-approx"
                | "from-real-approx-trapping"
                | "from-real-approx-saturating"
                | "from-real-trapping"
                | "from-real-saturating",
                [Real(f)],
            ) => Ok(Real(*f)),
            (
                "to-real-trapping"
                | "to-real-saturating"
                | "to-real-approx-trapping"
                | "to-real-approx-saturating",
                [Real(f)],
            ) => Ok(Real(*f)),
            ("real-approx-to-int", [Real(f)]) => Ok(Int(*f as i64)),
            ("real-approx-to-bits", [Real(f)]) => Ok(Int((*f as f32).to_bits() as i64)),
            ("bits-to-real-approx", [Int(i)]) => Ok(Real(f32::from_bits(*i as u32) as f64)),
            ("real-to-int", [Real(f)]) => Ok(Int(*f as i64)),
            ("real-to-bits", [Real(f)]) => Ok(Int(f.to_bits() as i64)),
            ("bits-to-real", [Int(i)]) => Ok(Real(f64::from_bits(*i as u64))),

            // -- compiler intrinsics ------------------------------------------
            // `__narrow` is a codegen hint: it tells the emitter a value fits
            // a narrower machine type. At the value level it is the identity.
            ("__narrow", [v]) => Ok(v.clone()),

            // -- the allocator, as arithmetic ---------------------------------
            // See `heap_pos` on the struct for why these move rather than
            // answering a constant, and for what this arm consequently cannot
            // see. `__heap-advance` and `__heap-restore` are declared to answer
            // Nothing and the compiler binds their results only to sequence
            // them, so Unit is the whole of it.
            // THE HOST IS A HOSTED ONE. `hosted-kind` is 1 in the zig, wasm and
            // C# plugs and 0 in the bare-metal code generators, and it guards
            // the memory work a hosted target has no business doing -- the
            // check compact above all. A tree walker is as hosted as it gets.
            ("hosted-kind", []) => Ok(Int(1)),
            // AN IDENTITY FOR A VALUE THAT HAS NO ADDRESS.
            //
            // Upstream emits `address-of` as the identity -- the value with no
            // load -- so an Integer answers itself, and measured on real x86 a
            // payload-free constructor is BOXED and answers its own heap
            // pointer, 24 bytes from its neighbour. The compiler uses it for
            // ABSENCE: `address-of x == 0` is how ten tests in `Types/Unifier`
            // ask whether there is a value at all.
            //
            // So an integer answers itself and everything else answers a
            // stable non-zero id. The pointer inside the `Rc` is exactly that,
            // and now that records are shared it has the right property too:
            // two names for one record answer the same id, as they do on bare
            // metal. What it is NOT is bare metal's number, and nothing may
            // compare it across arms or embed it in output.
            ("address-of", [Int(i)]) => Ok(Int(*i)),
            ("address-of", [Record(_, fs)]) => Ok(Int(Rc::as_ptr(fs) as i64)),
            ("address-of", [List(xs)]) => Ok(Int(Rc::as_ptr(xs) as *const u8 as i64)),
            ("address-of", [Ctor(_, fs)]) => Ok(Int(Rc::as_ptr(fs) as *const u8 as i64)),
            ("address-of", [Text(t)]) => Ok(Int(Rc::as_ptr(t) as *const u8 as i64)),
            ("address-of", [Unit]) => Ok(Int(0)),
            // The tag the unifier reads. Upstream's `mcopy-type` read this out
            // of raw memory and took a payload word for it, which was the root
            // of issue 126; here it is the declaration order and cannot be
            // anything else.
            ("variant-tag", [Ctor(n, _)]) => Ok(Int(*self.tags.get(n).unwrap_or(&0))),
            ("variant-tag", [Int(i)]) => Ok(Int(*i)),
            ("tag-equal", [Ctor(a, _), Ctor(b, _)]) => Ok(Bool(a == b)),
            ("text-concat-list", [List(xs)]) => {
                let mut out = String::new();
                for x in xs.iter() {
                    match x {
                        Text(t) => out.push_str(t),
                        other => return err(format!("text-concat-list over {}", type_name(other))),
                    }
                }
                Ok(Text(Rc::new(out)))
            }
            // The deck bracket: everything allocated between them is scratch
            // the exit reclaims. Nothing here reclaims anything, so the bracket
            // is a pair of no-ops -- which is exactly why this arm cannot see
            // a value that outlives one.
            ("__deck-enter", []) | ("__deck-exit", []) => Ok(Unit),
            // A LINKED LIST IS A LIST HERE, and the call sites make that sound:
            // `__linked-list-push` ANSWERS the new list and every caller in the
            // compiler rebinds it -- `__linked-list-push acc (...)` threaded as
            // an accumulator. The mutation is the emitter's optimisation of a
            // functional interface, not the interface.
            ("__linked-list-empty", [Int(_)]) => Ok(List(Rc::new(Vec::new()))),
            ("__linked-list-push", [List(xs), v]) => {
                let mut out = (**xs).clone();
                out.push(v.clone());
                Ok(List(Rc::new(out)))
            }
            ("__linked-list-to-list", [List(xs)]) => Ok(List(xs.clone())),

            ("__heap-save", []) => Ok(Int(self.heap_pos)),
            ("__deck-pos", []) => Ok(Int(self.deck_pos)),
            ("__heap-advance", [Int(n)]) => {
                self.heap_pos += *n;
                Ok(Unit)
            }
            ("__heap-restore", [Int(p)]) => {
                self.heap_pos = *p;
                Ok(Unit)
            }
            ("__deck-set", [Int(p)]) => {
                self.deck_pos = *p;
                Ok(Unit)
            }
            // `__record-set` is how a mutable record is updated: record, field
            // NAME as text, value.
            ("__record-set", [Record(n, fs), Text(field), v]) => {
                // Same mutation as `Code::FieldAssign`, with the field named
                // by a VALUE rather than by the source.
                let mut out = fs.borrow_mut();
                // **The field is named by a VALUE here, not by the source**, so
                // this is the one place a name is not already in the table --
                // and the one reason the interpreter keeps a mutable one. A
                // field named by a text nothing else mentions is a new symbol.
                let n = *n;
                let key = self.syms.intern(field);
                let bound = self.bounds.get(&(n, key));
                let v = match (v, bound) {
                    (Int(i), Some(b)) => Int(apply_bound(*i, b)),
                    _ => v.clone(),
                };
                match out.iter_mut().find(|(k, _)| *k == key) {
                    Some(slot) => slot.1 = v,
                    None => out.push((key, v)),
                }
                drop(out);
                Ok(Record(n, fs.clone()))
            }

            // NOT "is not interpreted yet" -- this arm cannot tell an absent
            // builtin from one that is here and was handed the wrong things,
            // and asserting the first hid the second. `bit-and` reached here
            // as ``not interpreted yet (given a function, an integer)`` while
            // being fully implemented; the argument types are the finding and
            // they go in front.
            _ => err(format!(
                "builtin `{name}` has no rule for ({})",
                args.iter().map(type_name).collect::<Vec<_>>().join(", ")
            )),
        }
    }
}

/// `float-to-ordinal`: a float's bits as a monotonically ordered integer, so
/// that subtracting two of them counts the representable values between --
/// ULPs. Negative floats have their low 63 bits flipped and one added, which
/// is what turns sign-magnitude into two's complement order.
fn ordinal(f: f64) -> i64 {
    let bits = f.to_bits() as i64;
    if bits < 0 {
        (bits ^ 0x7FFF_FFFF_FFFF_FFFF).wrapping_add(1)
    } else {
        bits
    }
}

/// `char-code`, the private frequency-ordered alphabet. NOT ASCII.
fn char_code(b: u8) -> i64 {
    if (b as usize) < crate::charcode::CHAR_CODE.len() {
        crate::charcode::CHAR_CODE[b as usize] as i64
    } else {
        0
    }
}

fn code_to_char(code: i64) -> char {
    crate::charcode::CHAR_CODE
        .iter()
        .position(|c| *c as i64 == code && code != 0)
        .map(|b| b as u8 as char)
        .unwrap_or('\0')
}

fn apply_bound(v: i64, b: &FieldBound) -> i64 {
    match b.mode {
        OverflowMode::Clamping => v.clamp(b.lo, b.hi),
        OverflowMode::Wrapping => {
            let span = b.hi - b.lo + 1;
            if span <= 0 {
                v
            } else {
                b.lo + (v - b.lo).rem_euclid(span)
            }
        }
        // `error` is a compile-time refusal, not a runtime one.
        OverflowMode::Error => v,
    }
}

pub(crate) fn literal(text: &str, kind: LiteralKind) -> R<Value> {
    match kind {
        // `#FFFF` is hexadecimal. The lexer scans it as one integer literal,
        // hash and all.
        LiteralKind::IntLit => {
            let clean = text.replace('_', "");
            match clean.strip_prefix('#') {
                // THROUGH u64, NOT i64. `#8000000000000000` is sixteen digits
                // and sets the sign bit, which `i64::from_str_radix` refuses as
                // out of range -- so the one literal a program writes to mean
                // "the most negative integer" was the one that would not parse.
                // A hexadecimal literal names a BIT PATTERN, and the pattern is
                // 64 bits wide either way round.
                Some(hex) => u64::from_str_radix(hex, 16)
                    .map(|u| Value::Int(u as i64))
                    .map_err(|_| Error(format!("bad hex literal `{text}`"))),
                None => clean
                    .parse()
                    .map(Value::Int)
                    .map_err(|_| Error(format!("bad integer literal `{text}`"))),
            }
        }
        LiteralKind::NumLit => text
            .replace('_', "")
            .parse()
            .map(Value::Real)
            .map_err(|_| Error(format!("bad number literal `{text}`"))),
        LiteralKind::BoolLit => Ok(Value::Bool(text == "True")),
        LiteralKind::TextLit => Ok(Value::Text(Rc::new(unescape(text)))),
        LiteralKind::CharLit => Ok(Value::Char(unescape(text).chars().next().unwrap_or('\0'))),
    }
}

/// A text literal arrives with its quotes and escapes as written.
fn unescape(raw: &str) -> String {
    let body = raw.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or_else(|| {
        raw.strip_prefix('\'').and_then(|s| s.strip_suffix('\'')).unwrap_or(raw)
    });
    let mut out = String::with_capacity(body.len());
    let mut it = body.chars();
    while let Some(c) = it.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match it.next() {
            Some('n') => out.push('\n'),
            Some('\\') => out.push('\\'),
            Some('"') => out.push('"'),
            Some('\'') => out.push('\''),
            Some(other) => out.push(other),
            None => {}
        }
    }
    out
}

fn binary(syms: &SymTab, op: BinaryOp, a: Value, b: Value) -> R<Value> {
    use BinaryOp::*;
    use Value::*;
    Ok(match (op, &a, &b) {
        (OpAdd, Int(x), Int(y)) => Int(x + y),
        (OpSub, Int(x), Int(y)) => Int(x - y),
        (OpMul, Int(x), Int(y)) => Int(x * y),
        (OpDiv, Int(x), Int(y)) if *y != 0 => Int(x / y),
        (OpDiv, Int(_), Int(_)) => return err("division by zero"),
        (OpPow, Int(x), Int(y)) => Int(x.pow(*y as u32)),
        (OpAdd, Real(x), Real(y)) => Real(x + y),
        (OpSub, Real(x), Real(y)) => Real(x - y),
        (OpMul, Real(x), Real(y)) => Real(x * y),
        (OpDiv, Real(x), Real(y)) => Real(x / y),
        (OpLt, Int(x), Int(y)) => Bool(x < y),
        (OpGt, Int(x), Int(y)) => Bool(x > y),
        (OpLtEq, Int(x), Int(y)) => Bool(x <= y),
        (OpGtEq, Int(x), Int(y)) => Bool(x >= y),
        (OpLt, Real(x), Real(y)) => Bool(x < y),
        (OpGt, Real(x), Real(y)) => Bool(x > y),
        (OpLtEq, Real(x), Real(y)) => Bool(x <= y),
        (OpGtEq, Real(x), Real(y)) => Bool(x >= y),
        (OpPow, Real(x), Real(y)) => Real(x.powf(*y)),
        (OpBoolAnd, Bool(x), Bool(y)) => Bool(*x && *y),
        (OpOr, Bool(x), Bool(y)) => Bool(*x || *y),
        // `~` and `~0` are ULP comparisons, not tolerances. `float-to-ordinal`
        // maps a float's bits to a monotonic integer -- flip the low 63 bits
        // and add one when negative -- and then `~` asks for a difference of
        // at most 4 and `~0` for exactly 0. Nothing about the operator says
        // "four"; it is a constant in the emitter.
        (OpApproxEq, Real(x), Real(y)) => Bool((ordinal(*x) - ordinal(*y)).abs() <= 4),
        (OpApproxEqExact, Real(x), Real(y)) => Bool(ordinal(*x) == ordinal(*y)),
        (OpEq, _, _) => Bool(equal(&a, &b)),
        (OpNotEq, _, _) => Bool(!equal(&a, &b)),
        (OpDefEq, _, _) => Bool(equal(&a, &b)),
        // `&` is one operator with four meanings, chosen by what it is given.
        (OpAnd | OpAppend, Text(x), Text(y)) => Text(Rc::new(format!("{x}{y}"))),
        (OpAnd | OpAppend, Text(x), _) => Text(Rc::new(format!("{x}{}", show(syms, &b)))),
        (OpAnd | OpAppend, _, Text(y)) => Text(Rc::new(format!("{}{y}", show(syms, &a)))),
        (OpAnd | OpAppend, List(x), List(y)) => {
            let mut out = (**x).clone();
            out.extend(y.iter().cloned());
            List(Rc::new(out))
        }
        (OpAnd, Bool(x), Bool(y)) => Bool(*x && *y),
        (OpAnd, Int(x), Int(y)) => Int(x & y),
        (OpOr, Int(x), Int(y)) => Int(x | y),
        (OpCons, _, List(y)) => {
            let mut out = vec![a.clone()];
            out.extend(y.iter().cloned());
            List(Rc::new(out))
        }
        _ => {
            return err(format!(
                "{:?} on {} and {}",
                op,
                type_name(&a),
                type_name(&b)
            ))
        }
    })
}

fn equal(a: &Value, b: &Value) -> bool {
    use Value::*;
    match (a, b) {
        (Int(x), Int(y)) => x == y,
        (Real(x), Real(y)) => x == y,
        (Text(x), Text(y)) => x == y,
        (Char(x), Char(y)) => x == y,
        (Bool(x), Bool(y)) => x == y,
        (Unit, Unit) => true,
        (List(x), List(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| equal(p, q))
        }
        (Ctor(n, x), Ctor(m, y)) => {
            n == m && x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| equal(p, q))
        }
        (Record(n, x), Record(m, y)) => {
            let (x, y) = (x.borrow(), y.borrow());
            n == m
                && x.len() == y.len()
                && x.iter().zip(y.iter()).all(|(p, q)| p.0 == q.0 && equal(&p.1, &q.1))
        }
        _ => false,
    }
}

/// Match, pushing each bound value in the order the compiler counted the
/// pattern's variables -- which is what makes a slot implicit rather than
/// named. A failing sub-pattern leaves a partly filled frame behind, and it is
/// thrown away with the arm.
fn matches_pat(v: &Value, p: &PatCode, vals: &mut Vec<Value>) -> bool {
    match p {
        PatCode::Wild => true,
        PatCode::Var => {
            vals.push(v.clone());
            true
        }
        PatCode::Lit(l) => equal(v, l),
        PatCode::BadLit => false,
        PatCode::Ctor(name, subs) => match v {
            Value::Ctor(n, fields) if *n == *name => {
                subs.len() == fields.len()
                    && subs.iter().zip(fields.iter()).all(|(s, f)| matches_pat(f, s, vals))
            }
            // A one-field constructor pattern over a bare value is how the
            // tuple patterns land after desugaring.
            Value::Record(n, fields) if *n == *name => {
                let fields = fields.borrow();
                subs.len() == fields.len()
                    && subs.iter().zip(fields.iter()).all(|(s, f)| matches_pat(&f.1, s, vals))
            }
            _ => false,
        },
        PatCode::Vec_(subs) => match v {
            Value::List(xs) => {
                subs.len() == xs.len()
                    && subs.iter().zip(xs.iter()).all(|(s, x)| matches_pat(x, s, vals))
            }
            _ => false,
        },
    }
}

pub fn show(syms: &SymTab, v: &Value) -> String {
    match v {
        Value::Int(i) => i.to_string(),
        Value::Real(f) => format!("{f}"),
        Value::Text(t) => (**t).clone(),
        Value::Char(c) => c.to_string(),
        Value::Bool(b) => if *b { "True" } else { "False" }.to_string(),
        Value::Unit => String::new(),
        Value::List(xs) => {
            let inner: Vec<String> = xs.iter().map(|x| show(syms, x)).collect();
            format!("[{}]", inner.join(", "))
        }
        Value::Ctor(n, fs) if fs.is_empty() => syms.text(*n).to_string(),
        Value::Ctor(n, fs) => {
            let inner: Vec<String> = fs.iter().map(|x| show(syms, x)).collect();
            format!("{} {}", syms.text(*n), inner.join(" "))
        }
        Value::Record(n, fs) => {
            let inner: Vec<String> = fs
                .borrow()
                .iter()
                .map(|(k, v)| format!("{} = {}", syms.text(*k), show(syms, v)))
                .collect();
            format!("{} {{ {} }}", syms.text(*n), inner.join(", "))
        }
        Value::Fun(_) => "<function>".to_string(),
    }
}

fn type_name(v: &Value) -> &'static str {
    match v {
        Value::Int(_) => "an integer",
        Value::Real(_) => "a real",
        Value::Text(_) => "a text",
        Value::Char(_) => "a char",
        Value::Bool(_) => "a boolean",
        Value::List(_) => "a list",
        Value::Record(..) => "a record",
        Value::Ctor(..) => "a constructor",
        Value::Fun(_) => "a function",
        Value::Unit => "nothing",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **A variant that grows `Value` costs more than the allocations it can
    /// save**, and this number is the record of learning that the hard way.
    ///
    /// It was 24 bytes when a record's type name was an `Rc<String>`. Interning
    /// those names as `Rc<str>` removed 1.59 million allocations from one
    /// safari unit and ran 16% SLOWER, because `Rc<str>` is a FAT pointer: it
    /// took the largest variant from 16 bytes to 24 and this enum from 24 to
    /// 32, and every step moves `Value`s. `Rc<String>` kept it thin and won 6%.
    /// Symbols then took the largest variant -- `Record(Sym, Rc<Vec<..>>)` --
    /// down to 12, and the enum to 16. Two words.
    #[test]
    fn value_is_two_words() {
        assert_eq!(std::mem::size_of::<Value>(), 16);
    }

    /// Run a whole chapter and answer what it printed.
    ///
    /// The tests below are all about ONE construct -- assignment to a record
    /// field -- because it is the one the compiler's own lexer is built out of
    /// and the one nothing else in this ecosystem uses. safari's port, judge
    /// and specs contain ZERO field assignments across 54 chapters, which is
    /// why 2,351 graded values on three arms never touched this path.
    fn out(src: &str) -> String {
        let src = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&src);
        let mut dg = crate::desugar::Desugar::new(&src);
        let ch = dg.chapter(&parsed.tree);
        let mut it = Interp::new(&ch);
        it.run().unwrap_or_else(|e| panic!("{}", e.0));
        it.out
    }

    const BOX: &str = "Chapter: T\n\nSection: S\n\n  Box = record {\n    n : Integer,\n    m : Integer\n  }\n\n";

    /// **The bug that interpreting Cobblestone's lexer found.** A field
    /// assignment writes THROUGH: the record the caller holds sees it, because
    /// `scan-ident-rest` assigns `st.offset` and then returns the same `st`.
    #[test]
    fn a_field_assignment_is_visible_in_the_caller() {
        let src = format!(
            "{BOX}  bump : Box -> Box\n  bump (b) =\n    let __seq = b.n = 99\n    in b\n\n\
             Section: E\n\n  opening : [Console] Nothing = act\n                 let a = Box {{ n = 1, m = 2 }}\n    in let r = bump a\n                 in print-line-uni (show (r.n) & \" \" & show (a.n) & \" \" & show (a.m))\n  end\n"
        );
        assert_eq!(out(&src).trim(), "99 99 2");
    }

    /// The field name is the token AFTER the dot, and a trailing newline is not
    /// it. Taking the last non-trivia token gave the assignment a field named
    /// "\n" -- the record grew a second, nameless field and the real one kept
    /// its value. Two fields here so a mis-named write cannot land on the right
    /// one by luck.
    #[test]
    fn the_assigned_field_is_the_one_after_the_dot() {
        let src = format!(
            "{BOX}Section: E\n\n  opening : [Console] Nothing = act\n                 let a = Box {{ n = 1, m = 2 }}\n    in let __seq = a.m = 7\n                 in print-line-uni (show a)\n  end\n"
        );
        assert_eq!(out(&src).trim(), "Box { n = 1, m = 7 }");
    }

    /// Records are SHARED, so two names for one record both see the write.
    /// This is the property the rebind-the-name alternative could not give and
    /// could not fail loudly about.
    #[test]
    fn two_names_for_one_record_see_the_same_write() {
        let src = format!(
            "{BOX}Section: E\n\n  opening : [Console] Nothing = act\n                 let a = Box {{ n = 1, m = 2 }}\n    in let b = a\n                 in let __seq = a.n = 5\n                 in print-line-uni (show (b.n))\n  end\n"
        );
        assert_eq!(out(&src).trim(), "5");
    }

    /// A record LITERAL is a fresh record every time, so sharing is not
    /// accidental: two literals with the same fields are two records.
    #[test]
    fn two_literals_are_two_records() {
        let src = format!(
            "{BOX}Section: E\n\n  opening : [Console] Nothing = act\n                 let a = Box {{ n = 1, m = 2 }}\n    in let b = Box {{ n = 1, m = 2 }}\n                 in let __seq = a.n = 5\n                 in print-line-uni (show (b.n))\n  end\n"
        );
        assert_eq!(out(&src).trim(), "1");
    }

    /// `scan-ident-rest` in miniature: a tail-recursive scanner that advances
    /// by assigning a field and returning the record it was handed. Before the
    /// fix this did not terminate.
    #[test]
    fn a_scanner_that_advances_by_assignment_terminates() {
        let src = format!(
            "{BOX}  step : Box -> Box\n  step (b) =\n                 if b.n >= b.m then b\n                 else let __seq = b.n = b.n + 1\n    in step b\n\n             Section: E\n\n  opening : [Console] Nothing = act\n                 let a = Box {{ n = 0, m = 40 }}\n    in print-line-uni (show ((step a).n))\n  end\n"
        );
        assert_eq!(out(&src).trim(), "40");
    }

    /// The allocator is arithmetic here: advance moves the position, restore
    /// puts it back, and `deck-short-of`'s two operands answer accordingly.
    #[test]
    fn the_heap_position_moves_and_comes_back() {
        let src = "Chapter: T\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 let a = __heap-save\n    in let __x = __heap-advance 1000\n                 in let b = __heap-save\n    in let __y = __heap-restore a\n                 in let c = __heap-save\n                 in print-line-uni (show a & \" \" & show b & \" \" & show c)\n  end\n";
        assert_eq!(out(src).trim(), "0 1000 0");
    }
}

/// Does this type carry an effect row anywhere inside it?
///
/// Recursive rather than a look at the head, because `[Console] Nothing` is the
/// shape that matters here but an effect can sit under a `Forall` or to the
/// right of an arrow, and a nullary whose type says it performs anything must
/// not be cached. Wrong in the safe direction costs a rebuild; wrong in the
/// other direction silently drops an effect.
fn mentions_effect(t: &TypeExpr) -> bool {
    match t {
        TypeExpr::Effect(..) => true,
        TypeExpr::Named(..) => false,
        TypeExpr::Fun(a, b, _) => mentions_effect(a) || mentions_effect(b),
        TypeExpr::App(h, args, _) => mentions_effect(h) || args.iter().any(mentions_effect),
        TypeExpr::BoundedInt(a, ..) => mentions_effect(a),
        TypeExpr::PropEq(a, b, _) => mentions_effect(a) || mentions_effect(b),
        TypeExpr::Constrained(_, _, a, _) => mentions_effect(a),
        TypeExpr::Linear(a, _) => mentions_effect(a),
        TypeExpr::Forall(_, a, b, _) => mentions_effect(a) || mentions_effect(b),
    }
}
