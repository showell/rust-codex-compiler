//! The interpreter's RUN FORM: the desugared AST with everything that is fixed
//! before the run starts already worked out.
//!
//! The tree-walker used to re-derive, on every step, what could not change. A
//! name was resolved by walking a scope chain comparing `String`s and then
//! missing into five `HashMap`s; an application spine was re-walked and its
//! arguments gathered into a fresh `Vec`; a literal was re-parsed from its
//! text, allocating; a record field's declared bound was fetched under a key
//! built out of two `String` clones. On `drive_main` that was about a fifth of
//! the run, and none of it is a function of the program's INPUT.
//!
//! So a chapter is compiled ONCE into `Code`, where
//!
//! * a local is `(hops, slot)` -- how many frames out, and where in that one;
//! * a global is an index into a table of ready values;
//! * a literal is already a `Value`;
//! * an application spine is already flat;
//! * a record field's bound is already attached, and its type name is one
//!   shared `Rc` rather than a fresh `String` per record built.
//!
//! **Chapter-collision resolution becomes STATIC**, which is what retires
//! `cur_slug` and the save/restore around every call: a name defined in two
//! chapters of one bundled unit resolves against the chapter its REFERENCE was
//! written in, and that is known here. It was a dynamic read of the running
//! chapter before, which agreed with this everywhere it was reachable except
//! inside a nullary definition's body, where it read the CALLER's chapter.
//!
//! **Nothing is folded, dropped or reordered**, and that is deliberate. One
//! `Code` node stands for one `Expr` node, an always-`True` guard is still
//! evaluated, and `Lazy` still costs its step -- so `steps` counts the same
//! work it counted before and steps-per-second stays comparable across this
//! change. Making the interpreter do LESS is a separate question from making
//! it do the same thing faster, and mixing the two makes the number lie.

use crate::ast::*;
use crate::interp::{literal, FieldBound, Value};
use crate::symbol::{Sym, SymTab};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// A lambda's fixed part: arity and compiled body, shared by every closure the
/// lambda expression makes.
#[derive(Debug)]
pub struct Lam {
    pub arity: usize,
    pub body: Rc<Code>,
}

/// One match arm, with its pattern's bindings turned into frame slots.
#[derive(Debug)]
pub struct Arm {
    pub pat: PatCode,
    /// How many values the pattern binds. The frame is exactly this wide, and
    /// the slots are in the order the pattern walk pushes them.
    pub nvars: usize,
    /// Always present: an unguarded arm carries `True`, and it is still
    /// evaluated. See the note about step parity above.
    pub guard: Code,
    pub body: Code,
}

#[derive(Debug)]
pub struct RecField {
    pub name: Sym,
    pub value: Code,
    /// The declared bound, read out of the record definition here rather than
    /// looked up under a two-`String` key on every record built.
    pub bound: Option<FieldBound>,
}

#[derive(Debug)]
pub enum Stmt {
    /// Binds one name: pushes a frame of one slot.
    Bind(Code),
    Exec(Code),
}

#[derive(Debug)]
pub enum PatCode {
    Wild,
    /// Binds the value at the next slot. Which slot is implied by the walk
    /// order, which is the same order the matcher pushes in.
    Var,
    Lit(Value),
    /// A literal that does not parse. The walker swallowed the error and never
    /// matched; so does this.
    BadLit,
    Ctor(Sym, Vec<PatCode>),
    Vec_(Vec<PatCode>),
}

#[derive(Debug)]
pub enum Code {
    Const(Value),
    /// Frames out, then slot within that frame.
    Local(u32, u32),
    /// An index into the interpreter's table of ready values: a top-level
    /// function, a constructor, or a builtin of one argument or more.
    Global(u32),
    /// A definition with no parameters. Its body is evaluated at every
    /// reference; Codex is pure, so that is a cost and not a meaning.
    ConstDef(u32),
    /// A builtin whose declared type is not an arrow: the reference IS the
    /// call, and there is no closure to hand back.
    NullaryBuiltin(&'static str),
    /// A name that did not resolve, or a literal that did not parse. The
    /// message is built here and raised only if this is ever evaluated --
    /// which is exactly when the walker raised it.
    Fail(String),
    /// A whole application spine, flat: the head and every argument, each with
    /// the span of the application that CONSUMES it.
    Apply(Box<Code>, Vec<(Code, Span)>),
    /// The flag says `+`, `-` and `*` WRAP: the operation's type, worked out
    /// at compile time (`Static::arith`), is a `wrapping` band. Where it is
    /// false they trap on overflow.
    Binary(Box<Code>, BinaryOp, Box<Code>, bool),
    Unary(Box<Code>),
    If(Box<Code>, Box<Code>, Box<Code>),
    /// Each binding gets its own frame, pushed in order, so a binding is in
    /// scope for the later ones and for the body but not for its own value.
    Let(Vec<Code>, Box<Code>),
    Lambda(Rc<Lam>),
    Match(Box<Code>, Rc<Vec<Arm>>),
    List(Vec<Code>),
    /// The type name is shared, not rebuilt per record.
    Record(Sym, Vec<RecField>),
    FieldAccess(Box<Code>, Sym, Span),
    Act(Vec<Stmt>),
    FieldAssign(Box<Code>, Sym, Box<Code>),
    Lazy(Box<Code>),
    /// `deck-record x`: an EXTENT around the evaluation of `x`.
    ///
    /// Its Codex definition is the identity, and that is only true because no
    /// emitter ever runs it -- `emit-deck-record-wrapper` compiles it to
    /// `__deck-enter, the body, __deck-exit`. An arm that ran the identity
    /// instead would never open an extent, and every guarded copy would then
    /// measure the BIVY against a ceiling the bivy parks on the instant the
    /// reservation is made.
    DeckRecord(Box<Code>),
    /// A form the interpreter does not do, with upstream's wording.
    Unsupported(&'static str),
}

/// The tables a name is resolved against.
///
/// Built once by the interpreter, read only here, and dropped when compilation
/// finishes -- none of it survives into the run, which is the point. The
/// values are INDICES: the interpreter holds the ready values in one vector
/// and the compiled bodies of the nullary definitions in another.
#[derive(Default)]
pub struct Names {
    /// Names defined in more than one chapter of this unit. Almost none are,
    /// and asking only about these is what keeps the chapter question off the
    /// common path.
    pub colliding: HashSet<Sym>,
    pub by_chapter_fun: HashMap<(String, Sym), u32>,
    pub by_chapter_const: HashMap<(String, Sym), u32>,
    pub funs: HashMap<Sym, u32>,
    pub consts: HashMap<Sym, u32>,
    pub ctors: HashMap<Sym, u32>,
    pub builtin_funs: HashMap<Sym, u32>,
    pub builtin_nullary: HashMap<Sym, &'static str>,
    pub builtin_undeclared: HashMap<Sym, &'static str>,
    pub bounds: HashMap<(Sym, Sym), FieldBound>,
    /// The record types, so a declared type can say it names one.
    pub records: HashSet<Sym>,
    /// A function's arity and declared result, by its global index.
    pub results: HashMap<u32, (usize, Static)>,
    /// A nullary definition's declared type, by its index.
    pub const_types: HashMap<u32, Static>,
}

/// What compilation knows of a value's type: as much as it takes to say
/// whether `+`, `-` and `*` on it wrap.
///
/// Upstream reads that off the checker's types, and this arm has none. So it
/// follows the checker's rules where an Integer's band and mode come from: a
/// declared parameter, result or record field, a `let` of one, and arithmetic
/// over them. Everything else is `Other`, which on the left of an operation
/// traps, as a literal or a builtin's plain `Integer` does upstream.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Static {
    Int { lo: i64, hi: i64, wraps: bool },
    Record(Sym),
    Other,
}

impl Static {
    /// `int-ty-default`: a plain `Integer`, and an integer literal's type.
    pub const INTEGER: Static = Static::Int { lo: i64::MIN, hi: i64::MAX, wraps: false };

    /// A declared type, through its effects and linearity.
    pub fn of(t: &TypeExpr, names: &Names, syms: &SymTab) -> Static {
        match t {
            TypeExpr::BoundedInt(_, lo, hi, mode, _) => {
                Static::Int { lo: *lo, hi: *hi, wraps: *mode == OverflowMode::Wrapping }
            }
            TypeExpr::Named(n, _) if names.records.contains(n) => Static::Record(*n),
            TypeExpr::Named(n, _) if syms.text(*n) == "Integer" => Static::INTEGER,
            TypeExpr::Effect(.., inner, _) | TypeExpr::Linear(inner, _) => Static::of(inner, names, syms),
            _ => Static::Other,
        }
    }

    /// `arith-result-ty`: an operation has its left operand's type, unless
    /// the right operand's band is narrower and inside it. So a `wrapping`
    /// left operand keeps `h * k + v` wrapping across the `+`.
    fn arith(l: Static, r: Static) -> Static {
        match (l, r) {
            (Static::Int { lo: ll, hi: lh, .. }, Static::Int { lo: rl, hi: rh, .. })
                if (rl, rh) != (ll, lh) && rl >= ll && rh <= lh =>
            {
                r
            }
            _ => l,
        }
    }

    fn wraps(self) -> bool {
        matches!(self, Static::Int { wraps: true, .. })
    }
}

/// A definition's declared parameter types, one for each parameter it names,
/// and its declared result. Without a declaration, or where the declaration
/// has fewer arrows than parameters, nothing is known.
pub fn signature(d: &Def, names: &Names, syms: &SymTab) -> (Vec<Static>, Static) {
    let unknown = || (vec![Static::Other; d.params.len()], Static::Other);
    let Some(mut t) = d.declared_type.first() else { return unknown() };
    let mut params = Vec::with_capacity(d.params.len());
    for _ in &d.params {
        let TypeExpr::Fun(a, b, _) = t else { return unknown() };
        params.push(Static::of(a, names, syms));
        t = b;
    }
    (params, Static::of(t, names, syms))
}

/// Compiles one definition's body.
///
/// `slug` is the chapter the body was WRITTEN in, which is what a colliding
/// name resolves against. `frames` mirrors, exactly, the frames the run will
/// push: one for a call's parameters, one for a lambda's, one per `let`
/// binding, one per `act` bind, and one per match arm -- including an arm
/// whose pattern binds nothing, because the run pushes that one too. Each name
/// in a frame carries what is known of its type.
pub struct Compiler<'a> {
    names: &'a Names,
    /// For the questions a symbol cannot answer itself: is this name
    /// capitalised, what does a builtin call itself, and is a type `Integer`.
    syms: &'a SymTab,
    slug: &'a str,
    frames: Vec<Vec<(Sym, Static)>>,
}

impl<'a> Compiler<'a> {
    pub fn new(names: &'a Names, syms: &'a SymTab, slug: &'a str) -> Compiler<'a> {
        Compiler { names, syms, slug, frames: Vec::new() }
    }

    /// A definition's body, under a frame holding its parameters.
    pub fn def(names: &'a Names, syms: &'a SymTab, d: &'a Def) -> Code {
        let mut c = Compiler::new(names, syms, d.chapter_slug.as_str());
        let (params, _) = signature(d, names, syms);
        c.frames.push(d.params.iter().map(|p| p.name).zip(params).collect());
        c.expr(&d.body)
    }

    /// A body evaluated in the empty environment: a nullary definition, and
    /// `opening` itself.
    pub fn body(names: &'a Names, syms: &'a SymTab, slug: &'a str, e: &'a Expr) -> Code {
        Compiler::new(names, syms, slug).expr(e)
    }

    pub fn expr(&mut self, e: &'a Expr) -> Code {
        self.typed(e).0
    }

    /// An expression's code, and what is known of its type.
    fn typed(&mut self, e: &'a Expr) -> (Code, Static) {
        match e {
            Expr::Lit(text, kind, _) => {
                let code = match literal(text, *kind) {
                    Ok(v) => Code::Const(v),
                    Err(e) => Code::Fail(e.0),
                };
                (code, if *kind == LiteralKind::IntLit { Static::INTEGER } else { Static::Other })
            }
            Expr::NameRef(n, _) => match self.local(*n) {
                Some(local) => local,
                None => {
                    let code = self.name(*n);
                    let t = match code {
                        Code::ConstDef(i) => self.names.const_types.get(&i).copied().unwrap_or(Static::Other),
                        _ => Static::Other,
                    };
                    (code, t)
                }
            },
            Expr::Apply(..) => {
                // Down the left spine to the head, once and for all. Each
                // argument keeps the span of the application that consumes it,
                // so an error still names the innermost one.
                let mut args: Vec<(&'a Expr, Span)> = Vec::new();
                let mut head = e;
                while let Expr::Apply(f, a, sp) = head {
                    args.push((a, *sp));
                    head = f;
                }
                args.reverse();
                // The one application this compiler does not compile as one.
                if args.len() == 1 {
                    if let Expr::NameRef(n, _) = head {
                        if self.syms.text(*n) == "deck-record" {
                            let (x, t) = self.typed(args[0].0);
                            return (Code::DeckRecord(Box::new(x)), t);
                        }
                    }
                }
                let h = self.expr(head);
                // A function given all its arguments has its declared result.
                let t = match &h {
                    Code::Global(g) => match self.names.results.get(g) {
                        Some(&(arity, t)) if arity == args.len() => t,
                        _ => Static::Other,
                    },
                    _ => Static::Other,
                };
                let mut out = Vec::with_capacity(args.len());
                for (a, sp) in args {
                    out.push((self.expr(a), sp));
                }
                (Code::Apply(Box::new(h), out), t)
            }
            Expr::Binary(l, op, r, _) => {
                let (a, lt) = self.typed(l);
                let (b, rt) = self.typed(r);
                let t = match op {
                    BinaryOp::OpAdd | BinaryOp::OpSub | BinaryOp::OpMul | BinaryOp::OpDiv | BinaryOp::OpPow => {
                        Static::arith(lt, rt)
                    }
                    _ => Static::Other,
                };
                (Code::Binary(Box::new(a), *op, Box::new(b), t.wraps()), t)
            }
            Expr::Unary(x, _) => {
                let (x, t) = self.typed(x);
                (Code::Unary(Box::new(x)), t)
            }
            // The checker gives an `if` its `then` branch's type.
            Expr::If(c, t, f, _) => {
                let c = self.expr(c);
                let (t, ty) = self.typed(t);
                let f = self.expr(f);
                (Code::If(Box::new(c), Box::new(t), Box::new(f)), ty)
            }
            Expr::Let(binds, body, _) => {
                let mut vals = Vec::with_capacity(binds.len());
                for b in binds {
                    let (v, t) = self.typed(&b.value);
                    vals.push(v);
                    self.frames.push(vec![(b.name, t)]);
                }
                let (body, t) = self.typed(body);
                self.frames.truncate(self.frames.len() - binds.len());
                (Code::Let(vals, Box::new(body)), t)
            }
            Expr::Lambda(params, body, _) => {
                self.frames.push(params.iter().map(|p| (*p, Static::Other)).collect());
                let b = self.expr(body);
                self.frames.pop();
                (Code::Lambda(Rc::new(Lam { arity: params.len(), body: Rc::new(b) })), Static::Other)
            }
            // The checker unifies every arm with a fresh result, which the
            // first arm's body binds.
            Expr::Match(s, arms, _) | Expr::Induction(s, arms, _) => {
                let scrut = self.expr(s);
                let mut out = Vec::with_capacity(arms.len());
                let mut t = Static::Other;
                for (i, a) in arms.iter().enumerate() {
                    let (arm, at) = self.arm(a);
                    if i == 0 {
                        t = at;
                    }
                    out.push(arm);
                }
                (Code::Match(Box::new(scrut), Rc::new(out)), t)
            }
            Expr::List(xs, _) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.expr(x));
                }
                (Code::List(out), Static::Other)
            }
            Expr::Record(name, fields, _) => {
                let mut out = Vec::with_capacity(fields.len());
                for f in fields {
                    let bound = self.names.bounds.get(&(*name, f.name)).copied();
                    out.push(RecField { name: f.name, value: self.expr(&f.value), bound });
                }
                (Code::Record(*name, out), Static::Record(*name))
            }
            Expr::FieldAccess(o, f, sp) => {
                let (o, ot) = self.typed(o);
                let t = match ot {
                    Static::Record(r) => match self.names.bounds.get(&(r, *f)) {
                        Some(b) => Static::Int { lo: b.lo, hi: b.hi, wraps: b.mode == OverflowMode::Wrapping },
                        None => Static::Other,
                    },
                    _ => Static::Other,
                };
                (Code::FieldAccess(Box::new(o), *f, *sp), t)
            }
            Expr::Act(stmts, _) => {
                let mut out = Vec::with_capacity(stmts.len());
                let mut pushed = 0;
                for s in stmts {
                    match s {
                        ActStmt::Exec(e, _) => out.push(Stmt::Exec(self.expr(e))),
                        ActStmt::Bind(n, e, _) => {
                            let (c, t) = self.typed(e);
                            out.push(Stmt::Bind(c));
                            self.frames.push(vec![(*n, t)]);
                            pushed += 1;
                        }
                    }
                }
                self.frames.truncate(self.frames.len() - pushed);
                (Code::Act(out), Static::Other)
            }
            Expr::Lazy(i, _) => (Code::Lazy(Box::new(self.expr(i))), Static::Other),
            Expr::FieldAssign(r, f, v, _) => {
                let name = *f;
                let base = self.expr(r);
                let val = self.expr(v);
                (Code::FieldAssign(Box::new(base), name, Box::new(val)), Static::Other)
            }
            Expr::Error(why, _) => {
                (Code::Fail(format!("the desugarer could not translate {why}")), Static::Other)
            }
            Expr::Handle(..) => (Code::Unsupported("effect handlers are not interpreted yet"), Static::Other),
            Expr::WithTimeout(..) => (Code::Unsupported("with-timeout is not interpreted yet"), Static::Other),
            Expr::Try(..) => (Code::Unsupported("trying blocks are not interpreted yet"), Static::Other),
        }
    }

    /// An arm, and its body's type.
    fn arm(&mut self, a: &'a MatchArm) -> (Arm, Static) {
        let mut vars: Vec<Sym> = Vec::new();
        let pat = pat_code(&a.pattern, &mut vars);
        let nvars = vars.len();
        self.frames.push(vars.into_iter().map(|v| (v, Static::Other)).collect());
        let guard = self.expr(&a.guard);
        let (body, t) = self.typed(&a.body);
        self.frames.pop();
        (Arm { pat, nvars, guard, body }, t)
    }

    /// A local, innermost frame first. Later bindings shadow earlier ones in
    /// the same frame, which is why this takes the LAST match in a frame.
    fn local(&self, n: Sym) -> Option<(Code, Static)> {
        for (hops, f) in self.frames.iter().rev().enumerate() {
            if let Some(slot) = f.iter().rposition(|k| k.0 == n) {
                return Some((Code::Local(hops as u32, slot as u32), f[slot].1));
            }
        }
        None
    }

    /// The resolution order is the walker's, case for case. Changing it here
    /// changes which definition a colliding name means.
    fn name(&self, n: Sym) -> Code {
        if let Some((c, _)) = self.local(n) {
            return c;
        }
        let colliding = self.names.colliding.contains(&n);
        let key = || (self.slug.to_string(), n);
        if colliding {
            if let Some(&g) = self.names.by_chapter_fun.get(&key()) {
                return Code::Global(g);
            }
        }
        if let Some(&g) = self.names.funs.get(&n) {
            return Code::Global(g);
        }
        if colliding {
            if let Some(&c) = self.names.by_chapter_const.get(&key()) {
                return Code::ConstDef(c);
            }
        }
        if let Some(&c) = self.names.consts.get(&n) {
            return Code::ConstDef(c);
        }
        if let Some(&g) = self.names.ctors.get(&n) {
            return Code::Global(g);
        }
        if let Some(&g) = self.names.builtin_funs.get(&n) {
            return Code::Global(g);
        }
        if let Some(name) = self.names.builtin_nullary.get(&n).copied() {
            return Code::NullaryBuiltin(name);
        }
        // A capitalised unknown is a nullary constructor the type definitions
        // did not mention -- `Nothing`, `True` from another chapter. BEFORE
        // the undeclared-builtin refusal on purpose: `True`, `False` and
        // `Nothing` are three of the eight that declare no type, and they are
        // constructors rather than anything to call.
        if self.syms.text(n).chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            // A payload-free constructor folded at COMPILE time has a
            // literal's lifetime -- built once, never freed -- so it gets a
            // literal's address rather than one off a heap that does not
            // exist yet.
            let addr = crate::bump::intern_literal(8);
            return Code::Const(Value::Ctor(n, Rc::new(crate::interp::Cell { addr, cached: std::cell::Cell::new(false), v: Vec::new() })));
        }
        if let Some(name) = self.names.builtin_undeclared.get(&n).copied() {
            return Code::Fail(format!(
                "builtin `{name}` declares no type, so its arity is not known"
            ));
        }
        Code::Fail(format!("undefined name `{}`", self.syms.text(n)))
    }
}

/// The slots a pattern binds are its `Var`s in walk order, and the matcher
/// pushes in exactly this order -- which is what makes the slot implicit.
fn pat_code(p: &Pat, vars: &mut Vec<Sym>) -> PatCode {
    match p {
        Pat::Wild(_) => PatCode::Wild,
        Pat::Var(n, _) => {
            vars.push(*n);
            PatCode::Var
        }
        Pat::Lit(text, kind, _) => match literal(text, *kind) {
            Ok(v) => PatCode::Lit(v),
            Err(_) => PatCode::BadLit,
        },
        Pat::Ctor(name, subs, _) => {
            PatCode::Ctor(*name, subs.iter().map(|s| pat_code(s, vars)).collect())
        }
        Pat::Vec_(subs, _) => PatCode::Vec_(subs.iter().map(|s| pat_code(s, vars)).collect()),
    }
}
