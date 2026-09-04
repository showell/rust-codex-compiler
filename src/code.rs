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
    Binary(Box<Code>, BinaryOp, Box<Code>),
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
}

/// Compiles one definition's body.
///
/// `slug` is the chapter the body was WRITTEN in, which is what a colliding
/// name resolves against. `frames` mirrors, exactly, the frames the run will
/// push: one for a call's parameters, one for a lambda's, one per `let`
/// binding, one per `act` bind, and one per match arm -- including an arm
/// whose pattern binds nothing, because the run pushes that one too.
pub struct Compiler<'a> {
    names: &'a Names,
    /// Only for the two questions a symbol cannot answer itself: is this name
    /// capitalised, and what does a builtin call itself.
    syms: &'a SymTab,
    slug: &'a str,
    frames: Vec<Vec<Sym>>,
}

impl<'a> Compiler<'a> {
    pub fn new(names: &'a Names, syms: &'a SymTab, slug: &'a str) -> Compiler<'a> {
        Compiler { names, syms, slug, frames: Vec::new() }
    }

    /// A definition's body, under a frame holding its parameters.
    pub fn def(names: &'a Names, syms: &'a SymTab, d: &'a Def) -> Code {
        let mut c = Compiler::new(names, syms, d.chapter_slug.as_str());
        c.frames.push(d.params.iter().map(|p| p.name).collect());
        c.expr(&d.body)
    }

    /// A body evaluated in the empty environment: a nullary definition, and
    /// `opening` itself.
    pub fn body(names: &'a Names, syms: &'a SymTab, slug: &'a str, e: &'a Expr) -> Code {
        Compiler::new(names, syms, slug).expr(e)
    }

    pub fn expr(&mut self, e: &'a Expr) -> Code {
        match e {
            Expr::Lit(text, kind, _) => match literal(text, *kind) {
                Ok(v) => Code::Const(v),
                Err(e) => Code::Fail(e.0),
            },
            Expr::NameRef(n, _) => self.name(*n),
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
                let h = self.expr(head);
                let mut out = Vec::with_capacity(args.len());
                for (a, sp) in args {
                    out.push((self.expr(a), sp));
                }
                Code::Apply(Box::new(h), out)
            }
            Expr::Binary(l, op, r, _) => {
                let a = self.expr(l);
                let b = self.expr(r);
                Code::Binary(Box::new(a), *op, Box::new(b))
            }
            Expr::Unary(x, _) => Code::Unary(Box::new(self.expr(x))),
            Expr::If(c, t, f, _) => {
                let c = self.expr(c);
                let t = self.expr(t);
                let f = self.expr(f);
                Code::If(Box::new(c), Box::new(t), Box::new(f))
            }
            Expr::Let(binds, body, _) => {
                let mut vals = Vec::with_capacity(binds.len());
                for b in binds {
                    vals.push(self.expr(&b.value));
                    self.frames.push(vec![b.name]);
                }
                let body = self.expr(body);
                self.frames.truncate(self.frames.len() - binds.len());
                Code::Let(vals, Box::new(body))
            }
            Expr::Lambda(params, body, _) => {
                self.frames.push(params.iter().copied().collect());
                let b = self.expr(body);
                self.frames.pop();
                Code::Lambda(Rc::new(Lam { arity: params.len(), body: Rc::new(b) }))
            }
            Expr::Match(s, arms, _) | Expr::Induction(s, arms, _) => {
                let scrut = self.expr(s);
                let mut out = Vec::with_capacity(arms.len());
                for a in arms {
                    out.push(self.arm(a));
                }
                Code::Match(Box::new(scrut), Rc::new(out))
            }
            Expr::List(xs, _) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.expr(x));
                }
                Code::List(out)
            }
            Expr::Record(name, fields, _) => {
                let mut out = Vec::with_capacity(fields.len());
                for f in fields {
                    let bound = self.names.bounds.get(&(*name, f.name)).copied();
                    out.push(RecField { name: f.name, value: self.expr(&f.value), bound });
                }
                Code::Record(*name, out)
            }
            Expr::FieldAccess(o, f, sp) => Code::FieldAccess(Box::new(self.expr(o)), *f, *sp),
            Expr::Act(stmts, _) => {
                let mut out = Vec::with_capacity(stmts.len());
                let mut pushed = 0;
                for s in stmts {
                    match s {
                        ActStmt::Exec(e, _) => out.push(Stmt::Exec(self.expr(e))),
                        ActStmt::Bind(n, e, _) => {
                            out.push(Stmt::Bind(self.expr(e)));
                            self.frames.push(vec![*n]);
                            pushed += 1;
                        }
                    }
                }
                self.frames.truncate(self.frames.len() - pushed);
                Code::Act(out)
            }
            Expr::Lazy(i, _) => Code::Lazy(Box::new(self.expr(i))),
            Expr::FieldAssign(r, f, v, _) => {
                let name = *f;
                let base = self.expr(r);
                let val = self.expr(v);
                Code::FieldAssign(Box::new(base), name, Box::new(val))
            }
            Expr::Error(why, _) => {
                Code::Fail(format!("the desugarer could not translate {why}"))
            }
            Expr::Handle(..) => Code::Unsupported("effect handlers are not interpreted yet"),
            Expr::WithTimeout(..) => Code::Unsupported("with-timeout is not interpreted yet"),
            Expr::Try(..) => Code::Unsupported("trying blocks are not interpreted yet"),
        }
    }

    fn arm(&mut self, a: &'a MatchArm) -> Arm {
        let mut vars: Vec<Sym> = Vec::new();
        let pat = pat_code(&a.pattern, &mut vars);
        let nvars = vars.len();
        self.frames.push(vars);
        let guard = self.expr(&a.guard);
        let body = self.expr(&a.body);
        self.frames.pop();
        Arm { pat, nvars, guard, body }
    }

    /// A local, innermost frame first. Later bindings shadow earlier ones in
    /// the same frame, which is why this takes the LAST match in a frame.
    fn local(&self, n: Sym) -> Option<Code> {
        for (hops, f) in self.frames.iter().rev().enumerate() {
            if let Some(slot) = f.iter().rposition(|k| *k == n) {
                return Some(Code::Local(hops as u32, slot as u32));
            }
        }
        None
    }

    /// The resolution order is the walker's, case for case. Changing it here
    /// changes which definition a colliding name means.
    fn name(&self, n: Sym) -> Code {
        if let Some(c) = self.local(n) {
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
            return Code::Const(Value::Ctor(n, Rc::new(Vec::new())));
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
