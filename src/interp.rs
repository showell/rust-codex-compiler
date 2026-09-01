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

#[derive(Debug)]
pub struct Closure {
    pub params: Vec<Name>,
    pub body: Rc<Expr>,
    pub env: Env,
    pub applied: Vec<Value>,
}

pub type Env = Rc<Scope>;

#[derive(Debug)]
pub struct Scope {
    vars: HashMap<Name, Value>,
    parent: Option<Env>,
}

impl Scope {
    fn root() -> Env {
        Rc::new(Scope { vars: HashMap::new(), parent: None })
    }
    fn get(&self, n: &str) -> Option<Value> {
        self.vars.get(n).cloned().or_else(|| self.parent.as_ref().and_then(|p| p.get(n)))
    }
    fn child(parent: &Env, vars: HashMap<Name, Value>) -> Env {
        Rc::new(Scope { vars, parent: Some(parent.clone()) })
    }
}

pub struct Error(pub String);

type R<T> = Result<T, Error>;

fn err<T>(msg: impl Into<String>) -> R<T> {
    Err(Error(msg.into()))
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
    pub out: String,
    steps: u64,
}

const STEP_LIMIT: u64 = 200_000_000;

impl Interp {
    pub fn new(ch: &Chapter) -> Interp {
        let mut it = Interp {
            defs: HashMap::new(),
            bounds: HashMap::new(),
            ctors: HashMap::new(),
            out: String::new(),
            steps: 0,
        };
        for d in &ch.defs {
            it.defs.insert(d.name.clone(), Rc::new(d.clone()));
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
        it
    }

    /// Run `opening`, the entry point every Codex program has.
    pub fn run(&mut self) -> R<()> {
        let Some(open) = self.defs.get("opening").cloned() else {
            return err("no `opening` definition to run");
        };
        let env = Scope::root();
        self.eval(&open.body, &env)?;
        Ok(())
    }

    fn eval(&mut self, e: &Expr, env: &Env) -> R<Value> {
        self.steps += 1;
        if self.steps > STEP_LIMIT {
            return err("step limit reached; the program did not finish");
        }
        match e {
            Expr::Lit(text, kind, _) => literal(text, *kind),
            Expr::NameRef(n, _) => self.lookup(n, env),
            Expr::Apply(f, a, _) => {
                let func = self.eval(f, env)?;
                let arg = self.eval(a, env)?;
                self.apply(func, arg)
            }
            Expr::Binary(l, op, r, _) => {
                let a = self.eval(l, env)?;
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
                    env = Scope::child(&env, [(b.name.clone(), v)].into_iter().collect());
                }
                self.eval(body, &env)
            }
            Expr::Lambda(params, body, _) => Ok(Value::Fun(Rc::new(Closure {
                params: params.clone(),
                body: Rc::new((**body).clone()),
                env: env.clone(),
                applied: Vec::new(),
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
            Expr::FieldAccess(obj, field, _) => match self.eval(obj, env)? {
                Value::Record(_, fs) => fs
                    .iter()
                    .find(|(n, _)| n == field)
                    .map(|(_, v)| v.clone())
                    .ok_or_else(|| Error(format!("no field `{field}`"))),
                v => err(format!("field access on {}", type_name(&v))),
            },
            Expr::Act(stmts, _) => {
                let mut env = env.clone();
                let mut last = Value::Unit;
                for s in stmts {
                    match s {
                        ActStmt::Exec(e, _) => last = self.eval(e, &env)?,
                        ActStmt::Bind(n, e, _) => {
                            let v = self.eval(e, &env)?;
                            env = Scope::child(&env, [(n.clone(), v)].into_iter().collect());
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
        if let Some(d) = self.defs.get(n).cloned() {
            if d.params.is_empty() {
                // A constant, evaluated on each reference. Codex is pure, so
                // this is a cost and not a semantic difference.
                let root = Scope::root();
                return self.eval(&d.body, &root);
            }
            return Ok(Value::Fun(Rc::new(Closure {
                params: d.params.iter().map(|p| p.name.clone()).collect(),
                body: Rc::new(d.body.clone()),
                env: Scope::root(),
                applied: Vec::new(),
            })));
        }
        if let Some(arity) = self.ctors.get(n).copied() {
            if arity == 0 {
                return Ok(Value::Ctor(Rc::new(n.to_string()), Rc::new(Vec::new())));
            }
            return Ok(Value::Fun(Rc::new(Closure {
                params: (0..arity).map(|i| format!("__f{i}")).collect(),
                body: Rc::new(Expr::NameRef(format!("__ctor:{n}"), Span::default())),
                env: Scope::root(),
                applied: Vec::new(),
            })));
        }
        if is_builtin(n) {
            return Ok(Value::Fun(Rc::new(Closure {
                params: builtin_params(n),
                body: Rc::new(Expr::NameRef(format!("__builtin:{n}"), Span::default())),
                env: Scope::root(),
                applied: Vec::new(),
            })));
        }
        // A capitalised unknown is a nullary constructor the type definitions
        // did not mention -- `Nothing`, `True` from another chapter.
        if n.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            return Ok(Value::Ctor(Rc::new(n.to_string()), Rc::new(Vec::new())));
        }
        err(format!("undefined name `{n}`"))
    }

    fn apply(&mut self, f: Value, arg: Value) -> R<Value> {
        let Value::Fun(c) = f else {
            return err(format!("applied {} to an argument", type_name(&f)));
        };
        let mut applied = c.applied.clone();
        applied.push(arg);
        if applied.len() < c.params.len() {
            return Ok(Value::Fun(Rc::new(Closure {
                params: c.params.clone(),
                body: c.body.clone(),
                env: c.env.clone(),
                applied,
            })));
        }
        // Saturated. A synthetic body names a constructor or a builtin.
        if let Expr::NameRef(marker, _) = &*c.body {
            if let Some(name) = marker.strip_prefix("__ctor:") {
                return Ok(Value::Ctor(Rc::new(name.to_string()), Rc::new(applied)));
            }
            if let Some(name) = marker.strip_prefix("__builtin:") {
                return self.builtin(name, applied);
            }
        }
        let vars: HashMap<Name, Value> =
            c.params.iter().cloned().zip(applied.into_iter()).collect();
        let env = Scope::child(&c.env, vars);
        let body = c.body.clone();
        self.eval(&body, &env)
    }

    fn match_arms(&mut self, v: &Value, arms: &[MatchArm], env: &Env) -> R<Value> {
        for a in arms {
            let mut vars = HashMap::new();
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
        match (name, args.as_slice()) {
            ("print-line-uni", [v]) => {
                let _ = writeln!(self.out, "{}", show(v));
                Ok(Value::Unit)
            }
            ("show", [v]) => Ok(Value::Text(Rc::new(show(v)))),
            ("list-length", [Value::List(xs)]) => Ok(Value::Int(xs.len() as i64)),
            ("list-at", [Value::List(xs), Value::Int(i)]) => xs
                .get(*i as usize)
                .cloned()
                .ok_or_else(|| Error(format!("list-at {i} past the end"))),
            ("text-length", [Value::Text(t)]) => Ok(Value::Int(t.chars().count() as i64)),
            ("negate", [Value::Int(i)]) => Ok(Value::Int(-i)),
            _ => err(format!("builtin `{name}` is not interpreted yet")),
        }
    }
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
        LiteralKind::IntLit => text
            .replace('_', "")
            .parse()
            .map(Value::Int)
            .map_err(|_| Error(format!("bad integer literal `{text}`"))),
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
        (OpBoolAnd, Bool(x), Bool(y)) => Bool(*x && *y),
        (OpOr, Bool(x), Bool(y)) => Bool(*x || *y),
        (OpEq, _, _) => Bool(equal(&a, &b)),
        (OpNotEq, _, _) => Bool(!equal(&a, &b)),
        (OpDefEq, _, _) => Bool(equal(&a, &b)),
        // `&` appends text to text and list to list, and the operator does
        // not say which.
        (OpAppend, Text(x), Text(y)) => Text(Rc::new(format!("{x}{y}"))),
        (OpAppend, Text(x), _) => Text(Rc::new(format!("{x}{}", show(&b)))),
        (OpAppend, _, Text(y)) => Text(Rc::new(format!("{}{y}", show(&a)))),
        (OpAppend, List(x), List(y)) => {
            let mut out = (**x).clone();
            out.extend(y.iter().cloned());
            List(Rc::new(out))
        }
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

fn matches_pat(v: &Value, p: &Pat, vars: &mut HashMap<Name, Value>) -> bool {
    match p {
        Pat::Wild(_) => true,
        Pat::Var(n, _) => {
            vars.insert(n.clone(), v.clone());
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

fn is_builtin(n: &str) -> bool {
    matches!(
        n,
        "print-line-uni" | "show" | "list-length" | "list-at" | "text-length" | "negate"
    )
}

fn builtin_params(n: &str) -> Vec<Name> {
    let arity = match n {
        "list-at" => 2,
        _ => 1,
    };
    (0..arity).map(|i| format!("__a{i}")).collect()
}
