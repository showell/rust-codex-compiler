//! The concrete syntax tree: lossless by construction, not by inspection.
//!
//! Cobblestone's `SyntaxNodes.codex` defines an AST -- `Expr`, `Def`,
//! `TypeExpr` -- and throws trivia away. We keep a green tree underneath that
//! covers every byte, and read the AST off it. That is the one place this
//! project deliberately does not copy upstream: the linting goal wants a tree
//! that can answer "what did the author actually write, spaces and all", and
//! retrofitting one later is a rewrite.
//!
//! **The invariant is structural.** A [`Builder`] can only ever consume the
//! next token in the lexer's stream, so a finished tree holds every token
//! exactly once, in order, and the source rebuilds by concatenation. There is
//! no way to write a parser against this API that silently drops a subtree --
//! the token would still be sitting in the stream, and [`Builder::finish`]
//! refuses to hand back a tree that has not reached the end.

use crate::token::Token;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NodeKind {
    Document,
    /// `Chapter: Name`
    ChapterHeader,
    /// `Section: Name`
    SectionHeader,
    /// `cites Foreword chapter Maybe`
    Cites,
    /// `grounds Device.Port, Device.Block`
    Grounds,
    /// `quotes ..`
    Quotes,
    /// A whole definition: its annotation line, its equation line, its body.
    Def,
    /// `name : Type`
    TypeAnnotation,
    /// The left of the `=`: the name and its parameter groups.
    DefEquation,
    /// One `(param)`.
    ParamGroup,
    /// A type expression. Not yet given internal structure.
    TypeExpr,
    /// `Name = record { .. }` / `Name = | A | B`
    TypeDef,
    /// A run of body tokens the expression parser has not been written for
    /// yet. It is a NAMED placeholder and is counted in the dump, because a
    /// body silently swallowed would look exactly like a body understood.
    UnparsedBody,

    // Expressions. The vocabulary is Cobblestone's `Expr`, one node kind per
    // variant, so the tree can be read as their AST without a mapping table.
    Lit,
    Name,
    App,
    Bin,
    Unary,
    Paren,
    Tuple,
    ListLit,
    RecordLit,
    RecordField,
    FieldAccess,
    FieldAssign,
    IfExpr,
    LetExpr,
    LetBinding,
    MatchExpr,
    MatchArm,
    Pattern,
    ActBlock,
    ActBind,
    Lambda,
    TryExpr,
    HandleExpr,
    HandleClause,
    WithTimeout,
    LazyExpr,
    ForExpr,
    Revised,
    Induction,
    Selector,
    /// An expression position that held something unreadable. Its tokens stay
    /// in the tree; only the shape is lost.
    ErrExpr,
    /// A prose block's continuation lines. A line at column 2 is prose and the
    /// lexer has already made it trivia; the lines UNDER it, indented past the
    /// top-level column, continue it and are not code.
    ProseBlock,
    /// Trivia and stray tokens that belong to no construct, kept so the tree
    /// still covers the file.
    Loose,
    /// A construct that failed to parse. Its tokens are still here.
    Error,
}

pub enum Child {
    Node(Node),
    Token(Token),
}

pub struct Node {
    pub kind: NodeKind,
    pub children: Vec<Child>,
}

impl Node {
    pub fn tokens(&self) -> impl Iterator<Item = &Token> {
        // Depth-first, left to right, which is source order by construction.
        let mut stack: Vec<&Child> = self.children.iter().rev().collect();
        std::iter::from_fn(move || {
            while let Some(c) = stack.pop() {
                match c {
                    Child::Token(t) => return Some(t),
                    Child::Node(n) => stack.extend(n.children.iter().rev()),
                }
            }
            None
        })
    }

    pub fn children_of(&self, kind: NodeKind) -> impl Iterator<Item = &Node> {
        self.children.iter().filter_map(move |c| match c {
            Child::Node(n) if n.kind == kind => Some(n),
            _ => None,
        })
    }

    pub fn count(&self, kind: NodeKind) -> usize {
        self.children_of(kind).count()
    }

    /// The shape, with tokens and trivia dropped: `(Bin (Name) (Bin (Name)
    /// (Name)))`. Precedence and associativity are claims about SHAPE, and a
    /// test that checked tokens would pass whatever tree they were hung on.
    pub fn shape(&self) -> String {
        let mut out = String::new();
        self.write_shape(&mut out);
        out
    }

    fn write_shape(&self, out: &mut String) {
        out.push('(');
        out.push_str(&format!("{:?}", self.kind));
        for c in &self.children {
            if let Child::Node(n) = c {
                out.push(' ');
                n.write_shape(out);
            }
        }
        out.push(')');
    }

    /// Every node of `kind` anywhere below here, in source order.
    pub fn descendants(&self, kind: NodeKind) -> Vec<&Node> {
        let mut out = Vec::new();
        let mut stack: Vec<&Node> = vec![self];
        // Walk children in order so the result is source order, not reverse.
        let mut queue: Vec<&Node> = Vec::new();
        while let Some(n) = stack.pop() {
            queue.push(n);
            for c in n.children.iter().rev() {
                if let Child::Node(sub) = c {
                    stack.push(sub);
                }
            }
        }
        queue.sort_by_key(|n| n.tokens().next().map(|t| t.offset).unwrap_or(u32::MAX));
        for n in queue {
            if n.kind == kind {
                out.push(n);
            }
        }
        out
    }
}

/// Builds a tree that cannot lose a token.
pub struct Builder {
    stream: Vec<Token>,
    at: usize,
    stack: Vec<Node>,
}

impl Builder {
    pub fn new(stream: Vec<Token>) -> Self {
        Builder {
            stream,
            at: 0,
            stack: vec![Node { kind: NodeKind::Document, children: Vec::new() }],
        }
    }

    pub fn start(&mut self, kind: NodeKind) {
        self.stack.push(Node { kind, children: Vec::new() });
    }

    pub fn end(&mut self) {
        let done = self.stack.pop().expect("end() without start()");
        self.stack
            .last_mut()
            .expect("end() past the document node")
            .children
            .push(Child::Node(done));
    }

    /// Consume the next token of the stream into the open node. This is the
    /// ONLY way a token enters the tree, which is what makes losslessness a
    /// property of the API rather than a test.
    pub fn eat(&mut self) -> Option<Token> {
        let t = *self.stream.get(self.at)?;
        self.at += 1;
        self.stack.last_mut().unwrap().children.push(Child::Token(t));
        Some(t)
    }

    pub fn consumed(&self) -> usize {
        self.at
    }

    /// Remember where the open node's children currently end.
    ///
    /// A Pratt parser only learns what it was building AFTER it has built the
    /// pieces: the left operand is parsed before the operator that will own it.
    /// So `checkpoint` marks a position and [`Builder::wrap_from`] later folds
    /// everything added since into a node. Tokens are still only ever consumed
    /// in order, so the coverage guarantee is untouched.
    pub fn checkpoint(&self) -> usize {
        self.stack.last().unwrap().children.len()
    }

    /// Fold every child added since `cp` into one node of `kind`.
    pub fn wrap_from(&mut self, cp: usize, kind: NodeKind) {
        let top = self.stack.last_mut().unwrap();
        let taken: Vec<Child> = top.children.drain(cp..).collect();
        top.children.push(Child::Node(Node { kind, children: taken }));
    }

    pub fn finish(mut self) -> Result<Node, String> {
        if self.at != self.stream.len() {
            return Err(format!(
                "{} of {} tokens reached the tree; a parser stopped early",
                self.at,
                self.stream.len()
            ));
        }
        if self.stack.len() != 1 {
            return Err(format!("{} nodes still open", self.stack.len() - 1));
        }
        Ok(self.stack.pop().unwrap())
    }
}
