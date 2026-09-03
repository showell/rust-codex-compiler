//! The AST the desugarer produces: Cobblestone's `AstNodes.codex`, variant for
//! variant, so the tree can be read against that file without a mapping table.
//!
//! It is deliberately SMALLER than the CST. Six of the parse tree's forms have
//! no node here at all and are rewritten instead -- a tuple becomes `MkTupN`
//! applied to its elements, `for x in xs -> b` becomes `map-list (\x -> b) xs`,
//! a parenthesis disappears, `not x` becomes `x == False`, `a |> f` becomes
//! `f a` with the operands SWAPPED, and a statement sequence becomes a `let`
//! binding named `__seq`. That is what desugaring IS, and it is why the AST
//! cannot be read back as the source: the CST is where the source still lives.
//!
//! Application is CURRIED here -- `AApplyExpr` takes one argument -- so `f a b`
//! is two nodes.

/// `record { value : Text }`. A name is not a token: the desugarer has already
/// taken the text, and some names (`__seq`, `__rev`, `MkTup3`) were never
/// written by anybody.
use std::rc::Rc;

pub type Name = String;

/// Line, column, offset and length, as `SourceSpan` carries them.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Span {
    pub line: u32,
    pub col: u32,
    pub offset: u32,
    pub len: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiteralKind {
    IntLit,
    NumLit,
    TextLit,
    CharLit,
    BoolLit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    OpAdd,
    OpSub,
    OpMul,
    OpDiv,
    OpPow,
    OpEq,
    OpNotEq,
    OpLt,
    OpGt,
    OpLtEq,
    OpGtEq,
    OpDefEq,
    OpAppend,
    OpCons,
    OpAnd,
    OpBoolAnd,
    OpOr,
    OpApproxEq,
    OpApproxEqExact,
}

#[derive(Clone, Debug)]
pub struct LetBind {
    pub name: Name,
    pub value: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct MatchArm {
    pub pattern: Pat,
    pub body: Expr,
    /// Always present: an unguarded arm carries a `True` literal, which is
    /// what lets the checker treat every arm the same way.
    pub guard: Expr,
    pub span: Span,
    /// Which `|`-group this arm was fanned out of. Upstream duplicates the
    /// body once per alternative pattern and keeps them related by this.
    pub alt_group: u32,
}

#[derive(Clone, Debug)]
pub struct FieldExpr {
    pub name: Name,
    pub value: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ActStmt {
    Bind(Name, Expr, Span),
    Exec(Expr, Span),
}

#[derive(Clone, Debug)]
pub struct HandleClause {
    pub op_name: Name,
    pub params: Vec<Name>,
    pub resume_name: Name,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Lit(String, LiteralKind, Span),
    NameRef(Name, Span),
    Apply(Rc<Expr>, Rc<Expr>, Span),
    Binary(Rc<Expr>, BinaryOp, Rc<Expr>, Span),
    Unary(Rc<Expr>, Span),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>, Span),
    Let(Vec<LetBind>, Rc<Expr>, Span),
    Lambda(Vec<Name>, Rc<Expr>, Span),
    Match(Rc<Expr>, Vec<MatchArm>, Span),
    List(Vec<Expr>, Span),
    Record(Name, Vec<FieldExpr>, Span),
    FieldAccess(Rc<Expr>, Name, Span),
    Act(Vec<ActStmt>, Span),
    Handle(Name, Rc<Expr>, Vec<HandleClause>, Span),
    WithTimeout(String, Vec<Name>, Vec<String>, Rc<Expr>, Span),
    Try(i64, Vec<ActStmt>, Vec<ActStmt>, Vec<ActStmt>, Span),
    FieldAssign(Rc<Expr>, Name, Rc<Expr>, Span),
    Lazy(Rc<Expr>, Span),
    Error(String, Span),
    Induction(Rc<Expr>, Vec<MatchArm>, Span),
}

#[derive(Clone, Debug)]
pub enum Pat {
    Var(Name, Span),
    Lit(String, LiteralKind, Span),
    Ctor(Name, Vec<Pat>, Span),
    Wild(Span),
    Vec_(Vec<Pat>, Span),
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
    Named(Name, Span),
    Fun(Rc<TypeExpr>, Rc<TypeExpr>, Span),
    App(Rc<TypeExpr>, Vec<TypeExpr>, Span),
    Effect(Vec<Name>, Vec<String>, Vec<Name>, Rc<TypeExpr>, Span),
    BoundedInt(Rc<TypeExpr>, i64, i64, OverflowMode, Span),
    PropEq(Rc<TypeExpr>, Rc<TypeExpr>, Span),
    Constrained(Name, Name, Rc<TypeExpr>, Span),
    Linear(Rc<TypeExpr>, Span),
    Forall(Name, Rc<TypeExpr>, Rc<TypeExpr>, Span),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OverflowMode {
    Error,
    Wrapping,
    Clamping,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: Name,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Def {
    pub name: Name,
    pub params: Vec<Param>,
    /// Zero or one. A definition may carry no annotation, and the checker
    /// infers; the list is how upstream spells `Maybe` here.
    pub declared_type: Vec<TypeExpr>,
    pub body: Expr,
    pub chapter_slug: String,
    pub span: Span,
    /// This definition PROVES a `claim`, and the claim sits inside it. A proof
    /// is entered by the checker, never called, so nothing reads it and it is
    /// alive anyway -- the one fact that separates a proposition from a corpse.
    pub is_claim: bool,
}

#[derive(Clone, Debug)]
pub struct RecordFieldDef {
    pub name: Name,
    pub type_expr: TypeExpr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct VariantCtorDef {
    pub name: Name,
    pub fields: Vec<TypeExpr>,
    pub return_type: Vec<TypeExpr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TypeDef {
    Record(Name, Vec<Name>, Vec<RecordFieldDef>, bool, Span),
    Variant(Name, Vec<Name>, Vec<VariantCtorDef>, Span),
    Unit(Name, TypeExpr, Span),
}

#[derive(Clone, Debug)]
pub struct EffectOpDef {
    pub name: Name,
    pub type_expr: TypeExpr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct EffectDef {
    pub name: Name,
    pub ops: Vec<EffectOpDef>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct ClassDef {
    pub name: Name,
    pub methods: Vec<EffectOpDef>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct InstanceMethodDef {
    pub name: Name,
    pub params: Vec<Name>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct InstanceDef {
    pub class_name: Name,
    pub type_name: Name,
    pub methods: Vec<InstanceMethodDef>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct CitesDecl {
    pub quire: Name,
    pub chapter_name: Name,
    pub selected_names: Vec<Name>,
    pub citing_chapter: String,
    pub span: Span,
}

impl Expr {
    /// Walk every expression under this one, self included.
    ///
    /// `dyn` rather than a generic on purpose: the closures nest through act
    /// statements and match arms, and a generic parameter makes the compiler
    /// instantiate `walk` inside itself without end.
    pub fn walk(&self, f: &mut dyn FnMut(&Expr)) {
        f(self);
        fn arms(xs: &[MatchArm], f: &mut dyn FnMut(&Expr)) {
            for a in xs {
                a.body.walk(f);
                a.guard.walk(f);
            }
        }
        fn stmts(xs: &[ActStmt], f: &mut dyn FnMut(&Expr)) {
            for s in xs {
                match s {
                    ActStmt::Bind(_, e, _) | ActStmt::Exec(e, _) => e.walk(f),
                }
            }
        }
        match self {
            Expr::Lit(..) | Expr::NameRef(..) | Expr::Error(..) => {}
            Expr::Apply(a, b, _) | Expr::Binary(a, _, b, _) => {
                a.walk(f);
                b.walk(f);
            }
            Expr::Unary(a, _) | Expr::Lazy(a, _) | Expr::FieldAccess(a, _, _) => a.walk(f),
            Expr::If(a, b, c, _) => {
                a.walk(f);
                b.walk(f);
                c.walk(f);
            }
            Expr::FieldAssign(a, _, b, _) => {
                a.walk(f);
                b.walk(f);
            }
            Expr::Let(bs, body, _) => {
                for b in bs {
                    b.value.walk(f);
                }
                body.walk(f);
            }
            Expr::Lambda(_, b, _) => b.walk(f),
            Expr::Match(s, a, _) | Expr::Induction(s, a, _) => {
                s.walk(f);
                arms(a, f);
            }
            Expr::List(xs, _) => {
                for x in xs {
                    x.walk(f);
                }
            }
            Expr::Record(_, fs, _) => {
                for fe in fs {
                    fe.value.walk(f);
                }
            }
            Expr::Act(ss, _) => stmts(ss, f),
            Expr::Handle(_, b, cs, _) => {
                b.walk(f);
                for c in cs {
                    c.body.walk(f);
                }
            }
            Expr::WithTimeout(_, _, _, b, _) => b.walk(f),
            Expr::Try(_, a, b, c, _) => {
                stmts(a, f);
                stmts(b, f);
                stmts(c, f);
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Chapter {
    pub name: Name,
    pub defs: Vec<Def>,
    pub type_defs: Vec<TypeDef>,
    pub effect_defs: Vec<EffectDef>,
    pub class_defs: Vec<ClassDef>,
    pub instance_defs: Vec<InstanceDef>,
    pub citations: Vec<CitesDecl>,
    pub ground_effects: Vec<String>,
    pub chapter_title: String,
    pub prose: String,
    pub prose_blocks: Vec<String>,
    pub annotations: Vec<(String, String, String)>,
    pub section_titles: Vec<String>,
    pub rt_names: Vec<String>,
    pub rt_budgets: Vec<i64>,
    pub conversions: Vec<String>,
    pub span: Span,
}
