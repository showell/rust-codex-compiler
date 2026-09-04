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
    /// `1 Minute = 60 Second` -- a unit conversion, which publishes an
    /// annotation and is not a definition however much it looks like one.
    Conversion,
    /// A whole definition: its annotation line, its equation line, its body.
    Def,
    /// `name : Type`
    TypeAnnotation,
    /// The left of the `=`: the name and its parameter groups.
    DefEquation,
    /// One `(param)`.
    ParamGroup,
    /// A type expression, and its shapes.
    TypeExpr,
    /// `A, B -> C`. Built right-nested, one parameter per node, from both the
    /// comma and the arrow.
    FunType,
    /// `Maybe a`, `Vector 4 Integer` -- a type applied to arguments.
    AppType,
    NamedType,
    ParenType,
    TupleType,
    /// `[Console] Nothing` -- an effect row in front of a return type.
    EffectType,
    /// `Integer between 0 and 255 wrapping`
    BoundedIntType,
    /// `linear T` / `mutable T`
    LinearType,
    /// `forall (a : K), T`
    ForAllType,
    /// `A === B` in type position: a propositional equality.
    PropEqType,
    /// `Showable a => a -> Text` -- a class constraint in front of a type. The
    /// IR emits the BODY alone, so the constraint is transparent there.
    ConstrainedType,
    /// `A * B`, `A + B` -- type-level arithmetic on bounded integers.
    ArithType,
    /// `punctual [budget] <name> : ...` -- a modifier on the definition that
    /// follows it, kept INSIDE that definition so the association is
    /// structural rather than "the next sibling".
    Punctual,
    /// `claim <name> : <prop>` in front of the definition that proves it.
    Claim,
    /// `bounded <class> <name>` in front of a definition -- the same shape as
    /// `punctual`, publishing `(ann "bounded" <name> <class>)`.
    Bounded,
    /// The `qed` that closes a proof.
    Qed,
    /// Two statements joined -- upstream's `SeqExpr`. Only a FIELD ASSIGNMENT
    /// can be the left of one.
    SeqExpr,
    /// `effect Audio where <op> : <type> ...`
    EffectDef,
    /// `class [Super => ] Name where <method> : <type> ...`
    ClassDef,
    /// The `Super =>` in front of a class's own name.
    Superclass,
    /// `instance Class Type where <method> (p) = <expr> ...`
    InstanceDef,
    InstanceMethod,
    /// One `<op> : <type>` of an effect declaration.
    EffectOp,
    /// `Name = record { .. }` / `Name = | A | B`
    TypeDef,
    /// The `a b` / `(a) (b)` after a type definition's name.
    TypeParams,
    RecordBody,
    RecordFieldDef,
    VariantBody,
    VariantCtor,
    /// One `(T)` of a constructor.
    CtorField,
    /// A constructor's `: T`, which fixes its result type.
    CtorReturn,
    /// `= unit T`
    UnitBody,
    /// `= unit family Millimeter`, and its `Member = <factor>` lines.
    UnitFamilyBody,
    UnitFamilyMember,
    /// `deriving Show, Eq, Ord`
    Deriving,
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
    /// A match arm's `when guard`, between its patterns and its arrow.
    Guard,

    // Patterns. Cobblestone's `Pat` has six variants; `ParenPat` is ours,
    // because the tree is lossless and the parentheses of `(x)` have to live
    // somewhere, and `ErrPat` is ours because upstream's catch-all folds a
    // token it did not understand into the same `WildPat` the author wrote.
    VarPat,
    LitPat,
    CtorPat,
    WildPat,
    TuplePat,
    ParenPat,
    VecPat,
    ErrPat,
    ActBlock,
    /// `name <- expr` in an act block.
    ActBind,
    /// A bare expression statement in an act block.
    ActStmt,
    /// `trying`'s three statement lists.
    TryBody,
    TryFallback,
    TryFailure,
    /// `[Console, Device.Block]` in front of a `with-timeout`.
    EffectRow,
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

    /// The tokens this node holds DIRECTLY, not those inside its child nodes.
    /// A class declaration's header is its direct tokens; its methods are
    /// nodes, and reading them all together names the class after a method.
    pub fn own_tokens(&self) -> impl Iterator<Item = &Token> {
        self.children.iter().filter_map(|c| match c {
            Child::Token(t) => Some(t),
            Child::Node(_) => None,
        })
    }

    /// This node's child nodes, in source order.
    pub fn child_nodes(&self) -> Vec<&Node> {
        self.children
            .iter()
            .filter_map(|c| match c {
                Child::Node(n) => Some(n),
                Child::Token(_) => None,
            })
            .collect()
    }

    /// How many child NODES this node has, of any kind.
    pub fn count_any_node(&self) -> usize {
        self.children.iter().filter(|c| matches!(c, Child::Node(_))).count()
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

    /// How many nodes of `kind` are anywhere below here.
    ///
    /// [`Node::descendants`] collects and then SORTS, which is right when the
    /// caller wants them in source order and pure waste when it only wants the
    /// number. A dozen of those per file is what took the coverage sweep from
    /// six seconds to fifteen.
    pub fn count_descendants(&self, kind: NodeKind) -> usize {
        let mut n = 0;
        let mut stack: Vec<&Node> = vec![self];
        while let Some(node) = stack.pop() {
            if node.kind == kind {
                n += 1;
            }
            for c in &node.children {
                if let Child::Node(sub) = c {
                    stack.push(sub);
                }
            }
        }
        n
    }

    /// Every node of `kind` anywhere below here, in source order.
    ///
    /// **The filter comes before the sort, and that is the whole cost story.**
    /// Collecting every node in the subtree and sorting THAT before filtering
    /// meant asking a chapter for its definitions sorted the entire tree -- and
    /// the key is not cheap either, since `tokens()` builds a stack to find the
    /// first one, so the sort allocated per comparison. On a 2.7 MB resolved
    /// unit this one call was about a sixth of the whole front end.
    ///
    /// The sort survives because it is not quite a no-op: the walk is
    /// pre-order, which IS source order, except that a node holding no tokens
    /// sorts last rather than staying where the walk found it. Sorting the
    /// matches alone gives the same answer as sorting everything and then
    /// filtering -- equal keys keep their walk order either way -- for a sort
    /// over the handful that matched instead of every node there is.
    pub fn descendants(&self, kind: NodeKind) -> Vec<&Node> {
        let mut out: Vec<&Node> = Vec::new();
        let mut stack: Vec<&Node> = vec![self];
        while let Some(n) = stack.pop() {
            if n.kind == kind {
                out.push(n);
            }
            for c in n.children.iter().rev() {
                if let Child::Node(sub) = c {
                    stack.push(sub);
                }
            }
        }
        out.sort_by_cached_key(|n| n.tokens().next().map(|t| t.offset).unwrap_or(u32::MAX));
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

    /// The kind of the node sitting at `cp`, if a node is there. Used to
    /// refuse a chained arrow without re-parsing what was just built.
    pub fn kind_at(&self, cp: usize) -> Option<NodeKind> {
        match self.stack.last()?.children.get(cp)? {
            Child::Node(n) => Some(n.kind),
            Child::Token(_) => None,
        }
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
