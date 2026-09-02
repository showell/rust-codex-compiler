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

use crate::ast::*;
use std::collections::HashMap;
use std::fmt::Write as _;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Real(f64),
    Text(Rc<String>),
    Char(char),
    Bool(bool),
    List(Rc<Vec<Value>>),
    /// A record literal: its type name and its fields.
    Record(Rc<String>, Rc<Vec<(String, Value)>>),
    /// A variant constructor, saturated or not.
    Ctor(Rc<String>, Rc<Vec<Value>>),
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
    /// A definition's or a lambda's body.
    Expr(Rc<Expr>),
    /// A variant constructor: the arguments ARE the value.
    Ctor(Rc<String>),
    /// A compiler builtin, resolved to its name once.
    Builtin(&'static str),
}

#[derive(Debug)]
pub struct Closure {
    /// SHARED with every partial application of the same function. Cloning a
    /// `Vec<String>` once per argument applied was the largest single caller
    /// of `malloc` in the profile.
    pub params: Rc<Vec<Name>>,
    pub body: Body,
    pub env: Env,
    pub applied: Vec<Value>,
    /// The chapter this closure's body was written in, when it came from a
    /// top-level definition. A name that COLLIDES across chapters resolves to
    /// the one in the same chapter as the reference, so a body has to know
    /// where it lives. INTERNED: a call installs it, and that has to be a
    /// refcount rather than a copy of the text.
    pub slug: Option<Rc<str>>,
}

pub type Env = Rc<Scope>;

/// What one frame binds.
///
/// A CALL binds the closure's whole parameter list at once, and the closure
/// already owns that list -- so the frame SHARES it and carries the values
/// beside it, instead of cloning a `String` per parameter per call. A `let`,
/// an `act` bind and a match arm's captures name themselves and stay pairs.
#[derive(Debug)]
enum Frame {
    Call(Rc<Vec<Name>>, Vec<Value>),
    Binds(Vec<(Name, Value)>),
}

/// A frame binds one to three names. A `HashMap` per call spends more on
/// hashing and on its allocation than a linear scan of a `Vec` ever costs, and
/// a call is the hottest thing an interpreter does.
#[derive(Debug)]
pub struct Scope {
    frame: Frame,
    parent: Option<Env>,
}

impl Scope {
    fn root() -> Env {
        Rc::new(Scope { frame: Frame::Binds(Vec::new()), parent: None })
    }
    fn get(&self, n: &str) -> Option<Value> {
        let mut here = self;
        loop {
            // Later bindings shadow earlier ones in the same frame.
            match &here.frame {
                Frame::Call(names, vals) => {
                    if let Some(i) = names.iter().rposition(|k| k == n) {
                        if let Some(v) = vals.get(i) {
                            return Some(v.clone());
                        }
                    }
                }
                Frame::Binds(vars) => {
                    if let Some((_, v)) = vars.iter().rev().find(|(k, _)| k == n) {
                        return Some(v.clone());
                    }
                }
            }
            match &here.parent {
                Some(p) => here = p,
                None => return None,
            }
        }
    }
    fn child(parent: &Env, vars: Vec<(Name, Value)>) -> Env {
        Rc::new(Scope { frame: Frame::Binds(vars), parent: Some(parent.clone()) })
    }
    fn one(parent: &Env, name: Name, v: Value) -> Env {
        Rc::new(Scope { frame: Frame::Binds(vec![(name, v)]), parent: Some(parent.clone()) })
    }
    /// The frame a saturated call runs in: the closure's own parameter list,
    /// shared, and one value per name.
    fn call(parent: &Env, names: Rc<Vec<Name>>, vals: Vec<Value>) -> Env {
        Rc::new(Scope { frame: Frame::Call(names, vals), parent: Some(parent.clone()) })
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
struct FieldBound {
    lo: i64,
    hi: i64,
    mode: OverflowMode,
}

pub struct Interp {
    /// Top-level definitions by name, and their arity.
    defs: HashMap<Name, Rc<Def>>,
    /// `Type.field -> bound`, read from the record definitions.
    bounds: HashMap<(String, String), FieldBound>,
    /// Which constructors exist, and how many fields each takes.
    ctors: HashMap<String, usize>,
    /// Every top-level function as a ready closure, built ONCE. Rebuilding one
    /// per reference deep-copied the body on every call to every function,
    /// which is the single most expensive thing an interpreter can do.
    funs: HashMap<Name, Value>,
    by_chapter_fun: HashMap<(String, String), Value>,
    /// Every builtin and every constructor as a ready value, built ONCE. A
    /// reference used to build a fresh `Vec<String>` of parameter names, a
    /// `format!`ed marker and two `Rc`s -- every time.
    builtin_funs: HashMap<&'static str, Value>,
    ctor_funs: HashMap<String, Value>,
    /// The empty environment, shared: every top-level closure closes over it.
    root: Env,
    /// `(chapter, name) -> definition`, for the names defined in more than one
    /// chapter of a bundled unit. `drive-unit.codex` has two `bar-quad`s --
    /// one over `ScreenPt` and one over `RiderPt` -- and keeping only the last
    /// silently gave the wrong one to every caller of the other.
    by_chapter: HashMap<(String, String), Rc<Def>>,
    /// The chapter whose body is currently running.
    cur_slug: Rc<str>,
    pub collisions: Vec<String>,
    /// The same set, for the test every lookup makes.
    colliding: std::collections::HashSet<String>,
    pub out: String,
    /// How much work the run did, which is the only speed number that is not
    /// about this machine on this day.
    pub steps: u64,
    depth: u32,
    limit: u64,
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
    pub fn new(ch: &Chapter) -> Interp {
        let root = Scope::root();
        let mut it = Interp {
            defs: HashMap::new(),
            bounds: HashMap::new(),
            ctors: HashMap::new(),
            funs: HashMap::new(),
            by_chapter_fun: HashMap::new(),
            builtin_funs: HashMap::new(),
            ctor_funs: HashMap::new(),
            root: root.clone(),
            by_chapter: HashMap::new(),
            cur_slug: Rc::from(""),
            collisions: Vec::new(),
            colliding: Default::default(),
            out: String::new(),
            steps: 0,
            depth: 0,
            limit: STEP_LIMIT,
        };
        let mut owners: HashMap<String, Vec<String>> = HashMap::new();
        for d in &ch.defs {
            let rc = Rc::new(d.clone());
            it.defs.insert(d.name.clone(), rc.clone());
            it.by_chapter.insert((d.chapter_slug.clone(), d.name.clone()), rc);
            let slugs = owners.entry(d.name.clone()).or_default();
            if !slugs.contains(&d.chapter_slug) {
                slugs.push(d.chapter_slug.clone());
            }
        }
        it.collisions = owners
            .into_iter()
            .filter(|(_, s)| s.len() > 1)
            .map(|(n, _)| n)
            .collect();
        it.collisions.sort();
        it.colliding = it.collisions.iter().cloned().collect();
        // Chapter slugs are interned here, once per chapter rather than once
        // per closure, because a call installs one.
        let mut slugs: HashMap<&str, Rc<str>> = HashMap::new();
        for d in &ch.defs {
            if d.params.is_empty() {
                continue;
            }
            let slug = slugs
                .entry(d.chapter_slug.as_str())
                .or_insert_with(|| Rc::from(d.chapter_slug.as_str()))
                .clone();
            let f = Value::Fun(Rc::new(Closure {
                params: Rc::new(d.params.iter().map(|p| p.name.clone()).collect()),
                body: Body::Expr(Rc::new(d.body.clone())),
                env: root.clone(),
                applied: Vec::new(),
                slug: Some(slug),
            }));
            it.funs.insert(d.name.clone(), f.clone());
            it.by_chapter_fun.insert((d.chapter_slug.clone(), d.name.clone()), f);
        }
        for t in &ch.type_defs {
            match t {
                TypeDef::Record(name, _, fields, ..) => {
                    for f in fields {
                        if let TypeExpr::BoundedInt(_, lo, hi, mode, _) = &f.type_expr {
                            it.bounds.insert(
                                (name.clone(), f.name.clone()),
                                FieldBound { lo: *lo, hi: *hi, mode: *mode },
                            );
                        }
                    }
                }
                TypeDef::Variant(_, _, ctors, _) => {
                    for c in ctors {
                        it.ctors.insert(c.name.clone(), c.fields.len());
                    }
                }
                TypeDef::Unit(..) => {}
            }
        }
        // Constructors and builtins are FIXED for the run, so their closures
        // are built here and every reference clones a `Value` -- which is one
        // refcount -- rather than rebuilding one.
        let ctors: Vec<(String, usize)> = it.ctors.iter().map(|(n, a)| (n.clone(), *a)).collect();
        for (name, arity) in ctors {
            let rc = Rc::new(name.clone());
            let v = if arity == 0 {
                Value::Ctor(rc, Rc::new(Vec::new()))
            } else {
                Value::Fun(Rc::new(Closure {
                    params: Rc::new((0..arity).map(|i| format!("__f{i}")).collect()),
                    body: Body::Ctor(rc),
                    env: root.clone(),
                    applied: Vec::new(),
                    slug: None,
                }))
            };
            it.ctor_funs.insert(name, v);
        }
        // The arity comes from the compiler's own table, not from a list here:
        // a builtin applied to the wrong number of arguments would otherwise be
        // a silent partial application rather than a call.
        for (name, arity) in crate::builtins::BUILTINS {
            // An arity of 0 means the entry declares no type; treat it as one
            // argument, the way the old per-reference path did.
            let arity = if arity == 0 { 1 } else { arity };
            it.builtin_funs.insert(
                name,
                Value::Fun(Rc::new(Closure {
                    params: Rc::new((0..arity).map(|i| format!("__a{i}")).collect()),
                    body: Body::Builtin(name),
                    env: root.clone(),
                    applied: Vec::new(),
                    slug: None,
                })),
            );
        }
        it
    }

    /// Bound this run to a number of steps. The sweep sets one; a single run
    /// does not.
    pub fn with_budget(mut self, steps: u64) -> Self {
        self.limit = steps;
        self
    }

    /// Run `opening`, the entry point every Codex program has.
    pub fn run(&mut self) -> R<()> {
        let Some(open) = self.defs.get("opening").cloned() else {
            return err("no `opening` definition to run");
        };
        self.cur_slug = Rc::from(open.chapter_slug.as_str());
        let env = self.root.clone();
        self.eval(&open.body, &env)?;
        Ok(())
    }

    fn eval(&mut self, e: &Expr, env: &Env) -> R<Value> {
        self.steps += 1;
        if self.steps > self.limit {
            return err("step limit reached; the program did not finish");
        }
        self.depth += 1;
        if self.depth > DEPTH_LIMIT {
            self.depth -= 1;
            return err("recursion limit reached");
        }
        let r = self.eval_inner(e, env);
        self.depth -= 1;
        r
    }

    fn eval_inner(&mut self, e: &Expr, env: &Env) -> R<Value> {
        match e {
            Expr::Lit(text, kind, _) => literal(text, *kind),
            Expr::NameRef(n, _) => self.lookup(n, env),
            Expr::Apply(..) => match self.apply_spine(e, env, false)? {
                Step::Done(v) => Ok(v),
                Step::Call(c, applied) => self.call(c, applied),
            },
            Expr::Binary(l, op, r, _) => {
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
                binary(*op, a, b)
            }
            Expr::Unary(x, _) => match self.eval(x, env)? {
                Value::Int(i) => Ok(Value::Int(-i)),
                Value::Real(f) => Ok(Value::Real(-f)),
                v => err(format!("negation of {}", type_name(&v))),
            },
            Expr::If(c, t, f, _) => match self.eval(c, env)? {
                Value::Bool(true) => self.eval(t, env),
                Value::Bool(false) => self.eval(f, env),
                v => err(format!("`if` on {}", type_name(&v))),
            },
            Expr::Let(binds, body, _) => {
                let mut env = env.clone();
                for b in binds {
                    let v = self.eval(&b.value, &env)?;
                    env = Scope::one(&env, b.name.clone(), v);
                }
                self.eval(body, &env)
            }
            // The body is already shared: a lambda evaluated a million times
            // bumps a refcount rather than copying its tree.
            Expr::Lambda(params, body, _) => Ok(Value::Fun(Rc::new(Closure {
                params: Rc::new(params.clone()),
                body: Body::Expr(body.clone()),
                env: env.clone(),
                applied: Vec::new(),
                slug: Some(self.cur_slug.clone()),
            }))),
            Expr::Match(scrut, arms, _) | Expr::Induction(scrut, arms, _) => {
                let v = self.eval(scrut, env)?;
                self.match_arms(&v, arms, env)
            }
            Expr::List(xs, _) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.eval(x, env)?);
                }
                Ok(Value::List(Rc::new(out)))
            }
            Expr::Record(name, fields, _) => {
                let mut out = Vec::with_capacity(fields.len());
                for f in fields {
                    let mut v = self.eval(&f.value, env)?;
                    // The declared bound is syntax, so it is applied here.
                    if let (Value::Int(i), Some(b)) =
                        (&v, self.bounds.get(&(name.clone(), f.name.clone())))
                    {
                        v = Value::Int(apply_bound(*i, b));
                    }
                    out.push((f.name.clone(), v));
                }
                Ok(Value::Record(Rc::new(name.clone()), Rc::new(out)))
            }
            Expr::FieldAccess(obj, field, sp) => match self.eval(obj, env)? {
                Value::Record(name, fs) => fs
                    .iter()
                    .find(|(n, _)| n == field)
                    .map(|(_, v)| v.clone())
                    .ok_or_else(|| {
                        Error(format!(
                            "L{}C{}: `{name}` has no field `{field}` (it has {})",
                            sp.line,
                            sp.col,
                            fs.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>().join(", ")
                        ))
                    }),
                v => err(format!(
                    "L{}C{}: field `{field}` read from {}",
                    sp.line,
                    sp.col,
                    type_name(&v)
                )),
            },
            Expr::Act(stmts, _) => {
                let mut env = env.clone();
                let mut last = Value::Unit;
                for s in stmts {
                    match s {
                        ActStmt::Exec(e, _) => last = self.eval(e, &env)?,
                        ActStmt::Bind(n, e, _) => {
                            let v = self.eval(e, &env)?;
                            env = Scope::one(&env, n.clone(), v);
                            last = Value::Unit;
                        }
                    }
                }
                Ok(last)
            }
            Expr::Lazy(inner, _) => self.eval(inner, env),
            Expr::FieldAssign(rec, field, val, _) => {
                let base = self.eval(rec, env)?;
                let v = self.eval(val, env)?;
                match base {
                    Value::Record(name, fs) => {
                        let mut out: Vec<(String, Value)> = (*fs).clone();
                        let bound = self.bounds.get(&((*name).clone(), field.clone()));
                        let v = match (&v, bound) {
                            (Value::Int(i), Some(b)) => Value::Int(apply_bound(*i, b)),
                            _ => v,
                        };
                        match out.iter_mut().find(|(n, _)| n == field) {
                            Some(slot) => slot.1 = v,
                            None => out.push((field.clone(), v)),
                        }
                        Ok(Value::Record(name, Rc::new(out)))
                    }
                    v => err(format!("field assignment on {}", type_name(&v))),
                }
            }
            Expr::Error(why, _) => err(format!("the desugarer could not translate {why}")),
            Expr::Handle(..) => err("effect handlers are not interpreted yet"),
            Expr::WithTimeout(..) => err("with-timeout is not interpreted yet"),
            Expr::Try(..) => err("trying blocks are not interpreted yet"),
        }
    }

    fn lookup(&mut self, n: &str, env: &Env) -> R<Value> {
        if let Some(v) = env.get(n) {
            return Ok(v);
        }
        // The same chapter wins for a name defined in more than one -- but
        // ASK ONLY WHEN IT COLLIDES. Building the (chapter, name) key
        // allocated two Strings on every reference to every name, and almost
        // no name collides.
        let by_chapter = self.colliding.contains(n).then(|| {
            let key = (self.cur_slug.to_string(), n.to_string());
            (self.by_chapter_fun.get(&key).cloned(), self.by_chapter.get(&key).cloned())
        });
        if let Some((Some(f), _)) = &by_chapter {
            return Ok(f.clone());
        }
        if let Some(f) = self.funs.get(n) {
            return Ok(f.clone());
        }
        let same_chapter = by_chapter.and_then(|(_, d)| d);
        if let Some(d) = same_chapter.or_else(|| self.defs.get(n).cloned()) {
            if d.params.is_empty() {
                // A constant, evaluated on each reference. Codex is pure, so
                // this is a cost and not a semantic difference.
                let root = self.root.clone();
                return self.eval(&d.body, &root);
            }
            return Ok(Value::Fun(Rc::new(Closure {
                params: Rc::new(d.params.iter().map(|p| p.name.clone()).collect()),
                body: Body::Expr(Rc::new(d.body.clone())),
                env: self.root.clone(),
                applied: Vec::new(),
                slug: Some(Rc::from(d.chapter_slug.as_str())),
            })));
        }
        if let Some(c) = self.ctor_funs.get(n) {
            return Ok(c.clone());
        }
        if let Some(b) = self.builtin_funs.get(n) {
            return Ok(b.clone());
        }
        // A capitalised unknown is a nullary constructor the type definitions
        // did not mention -- `Nothing`, `True` from another chapter.
        if n.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            return Ok(Value::Ctor(Rc::new(n.to_string()), Rc::new(Vec::new())));
        }
        err(format!("undefined name `{n}`"))
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
                Body::Expr(b) => b.clone(),
            };
            let env = Scope::call(&c.env, c.params.clone(), applied);
            let next_slug = c.slug.clone().unwrap_or_else(|| self.cur_slug.clone());
            let saved = std::mem::replace(&mut self.cur_slug, next_slug);
            let stepped = self.eval_tail(&body, &env);
            self.cur_slug = saved;
            match stepped? {
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
    fn eval_tail(&mut self, e: &Expr, env: &Env) -> R<Step> {
        self.steps += 1;
        if self.steps > self.limit {
            return err("step limit reached; the program did not finish");
        }
        match e {
            Expr::If(c, t, f, _) => match self.eval(c, env)? {
                Value::Bool(true) => self.eval_tail(t, env),
                Value::Bool(false) => self.eval_tail(f, env),
                v => err(format!("`if` on {}", type_name(&v))),
            },
            Expr::Let(binds, body, _) => {
                let mut env = env.clone();
                for b in binds {
                    let v = self.eval(&b.value, &env)?;
                    env = Scope::one(&env, b.name.clone(), v);
                }
                self.eval_tail(body, &env)
            }
            Expr::Match(scrut, arms, _) | Expr::Induction(scrut, arms, _) => {
                let v = self.eval(scrut, env)?;
                for a in arms {
                    let mut vars = Vec::new();
                    if !matches_pat(&v, &a.pattern, &mut vars) {
                        continue;
                    }
                    let arm_env = Scope::child(env, vars);
                    if let Value::Bool(false) = self.eval(&a.guard, &arm_env)? {
                        continue;
                    }
                    return self.eval_tail(&a.body, &arm_env);
                }
                err("no match arm applied")
            }
            Expr::Act(stmts, _) => {
                let mut env = env.clone();
                for (i, s) in stmts.iter().enumerate() {
                    let last = i + 1 == stmts.len();
                    match s {
                        ActStmt::Exec(e, _) if last => return self.eval_tail(e, &env),
                        ActStmt::Exec(e, _) => {
                            self.eval(e, &env)?;
                        }
                        ActStmt::Bind(n, e, _) => {
                            let v = self.eval(e, &env)?;
                            env = Scope::one(&env, n.clone(), v);
                        }
                    }
                }
                Ok(Step::Done(Value::Unit))
            }
            Expr::Apply(..) => self.apply_spine(e, env, true),
            _ => Ok(Step::Done(self.eval(e, env)?)),
        }
    }

    /// Evaluate a whole application SPINE, gathering the arguments for one
    /// call instead of building a closure per argument.
    ///
    /// **Application is curried -- `f a b c` is three nested `Apply` nodes --
    /// but the call is not.** Taking them one at a time allocated an
    /// intermediate closure, its argument vector and a clone of every argument
    /// already applied, per argument: `map-list-loop` has five parameters, so
    /// every one of its calls built four closures it then threw away.
    ///
    /// **The ORDER is unchanged, and that is the whole constraint.** Arguments
    /// are still evaluated left to right, and a call that saturates PART WAY
    /// down the spine still runs before the arguments after it are evaluated
    /// -- `f a b` where `f` takes one argument runs `f a` before `b`.
    ///
    /// `tail` says whether the caller can loop on the last call rather than
    /// nesting; only `eval_tail` can.
    fn apply_spine(&mut self, e: &Expr, env: &Env, tail: bool) -> R<Step> {
        // Down the left spine to the head. Each argument keeps the span of the
        // application that CONSUMES it, so an error still names the innermost
        // application rather than the outermost.
        let mut args: Vec<(&Expr, Span)> = Vec::new();
        let mut head = e;
        while let Expr::Apply(f, a, sp) = head {
            args.push((a, *sp));
            head = f;
        }
        args.reverse();
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
            let Some(c) = fun.filter(|c| c.params.len() > c.applied.len()) else {
                // A constructor takes its fields one at a time, and anything
                // else is an error the one-argument path words properly.
                let (a, sp) = args[i];
                let arg = self.eval(a, env)?;
                f = self.apply(f, arg).map_err(|e| at(e, sp))?;
                i += 1;
                continue;
            };
            let take = (c.params.len() - c.applied.len()).min(args.len() - i);
            let mut applied = c.applied.clone();
            let sp = args[i + take - 1].1;
            for (a, _) in &args[i..i + take] {
                applied.push(self.eval(a, env)?);
            }
            i += take;
            if applied.len() < c.params.len() {
                f = Value::Fun(Rc::new(Closure {
                    params: c.params.clone(),
                    body: c.body.clone(),
                    env: c.env.clone(),
                    applied,
                    slug: c.slug.clone(),
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
        if applied.len() < c.params.len() {
            return Ok(Step::Done(Value::Fun(Rc::new(Closure {
                params: c.params.clone(),
                body: c.body.clone(),
                env: c.env.clone(),
                applied,
                slug: c.slug.clone(),
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

    fn match_arms(&mut self, v: &Value, arms: &[MatchArm], env: &Env) -> R<Value> {
        for a in arms {
            let mut vars = Vec::new();
            if !matches_pat(v, &a.pattern, &mut vars) {
                continue;
            }
            let env = Scope::child(env, vars);
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
                let _ = writeln!(self.out, "{}", show(v));
                Ok(Unit)
            }
            ("print-uni" | "print", [v]) => {
                let _ = write!(self.out, "{}", show(v));
                Ok(Unit)
            }

            // -- text ---------------------------------------------------------
            ("show" | "integer-to-text", [v]) => text(show(v)),
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
            ("is-letter", [Char(c)]) => Ok(Bool(c.is_alphabetic())),
            ("is-digit", [Char(c)]) => Ok(Bool(c.is_ascii_digit())),

            // -- lists --------------------------------------------------------
            ("list-length", [List(xs)]) => Ok(Int(xs.len() as i64)),
            ("list-at", [List(xs), Int(i)]) => (*i >= 0)
                .then(|| xs.get(*i as usize).cloned())
                .flatten()
                .ok_or_else(|| Error(format!("list-at {i} of a {}-element list", xs.len()))),
            ("list-push", [List(xs), v]) => {
                let mut out = (**xs).clone();
                out.push(v.clone());
                Ok(List(Rc::new(out)))
            }
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
            ("negate", [Int(i)]) => Ok(Int(-i)),
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
            (
                "to-real-approx"
                | "to-real-approx-trapping"
                | "to-real-approx-saturating"
                | "to-real-trapping"
                | "to-real-saturating"
                | "to-real"
                | "real-from-int"
                | "real-approx-from-int",
                [Int(i)],
            ) => Ok(Real(*i as f64)),
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
            ("deck-record" | "__heap-save" | "__deck-pos", [v]) => Ok(v.clone()),
            // `__record-set` is how a mutable record is updated: record, field
            // NAME as text, value.
            ("__record-set", [Record(n, fs), Text(field), v]) => {
                let mut out = (**fs).clone();
                let bound = self.bounds.get(&((**n).clone(), (**field).clone()));
                let v = match (v, bound) {
                    (Int(i), Some(b)) => Int(apply_bound(*i, b)),
                    _ => v.clone(),
                };
                match out.iter_mut().find(|(k, _)| k == &**field) {
                    Some(slot) => slot.1 = v,
                    None => out.push(((**field).clone(), v)),
                }
                Ok(Record(n.clone(), Rc::new(out)))
            }

            _ => err(format!(
                "builtin `{name}` is not interpreted yet (given {})",
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

fn literal(text: &str, kind: LiteralKind) -> R<Value> {
    match kind {
        // `#FFFF` is hexadecimal. The lexer scans it as one integer literal,
        // hash and all.
        LiteralKind::IntLit => {
            let clean = text.replace('_', "");
            match clean.strip_prefix('#') {
                Some(hex) => i64::from_str_radix(hex, 16)
                    .map(Value::Int)
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

fn binary(op: BinaryOp, a: Value, b: Value) -> R<Value> {
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
        (OpAnd | OpAppend, Text(x), _) => Text(Rc::new(format!("{x}{}", show(&b)))),
        (OpAnd | OpAppend, _, Text(y)) => Text(Rc::new(format!("{}{y}", show(&a)))),
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
            n == m
                && x.len() == y.len()
                && x.iter().zip(y.iter()).all(|(p, q)| p.0 == q.0 && equal(&p.1, &q.1))
        }
        _ => false,
    }
}

fn matches_pat(v: &Value, p: &Pat, vars: &mut Vec<(Name, Value)>) -> bool {
    match p {
        Pat::Wild(_) => true,
        Pat::Var(n, _) => {
            vars.push((n.clone(), v.clone()));
            true
        }
        Pat::Lit(text, kind, _) => literal(text, *kind).map(|l| equal(v, &l)).unwrap_or(false),
        Pat::Ctor(name, subs, _) => match v {
            Value::Ctor(n, fields) if **n == *name => {
                subs.len() == fields.len()
                    && subs.iter().zip(fields.iter()).all(|(s, f)| matches_pat(f, s, vars))
            }
            // A one-field constructor pattern over a bare value is how the
            // tuple patterns land after desugaring.
            Value::Record(n, fields) if **n == *name => {
                subs.len() == fields.len()
                    && subs.iter().zip(fields.iter()).all(|(s, f)| matches_pat(&f.1, s, vars))
            }
            _ => false,
        },
        Pat::Vec_(subs, _) => match v {
            Value::List(xs) => {
                subs.len() == xs.len()
                    && subs.iter().zip(xs.iter()).all(|(s, x)| matches_pat(x, s, vars))
            }
            _ => false,
        },
    }
}

pub fn show(v: &Value) -> String {
    match v {
        Value::Int(i) => i.to_string(),
        Value::Real(f) => format!("{f}"),
        Value::Text(t) => (**t).clone(),
        Value::Char(c) => c.to_string(),
        Value::Bool(b) => if *b { "True" } else { "False" }.to_string(),
        Value::Unit => String::new(),
        Value::List(xs) => {
            let inner: Vec<String> = xs.iter().map(show).collect();
            format!("[{}]", inner.join(", "))
        }
        Value::Ctor(n, fs) if fs.is_empty() => (**n).clone(),
        Value::Ctor(n, fs) => {
            let inner: Vec<String> = fs.iter().map(show).collect();
            format!("{} {}", n, inner.join(" "))
        }
        Value::Record(n, fs) => {
            let inner: Vec<String> = fs.iter().map(|(k, v)| format!("{k} = {}", show(v))).collect();
            format!("{} {{ {} }}", n, inner.join(", "))
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
