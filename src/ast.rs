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
use crate::symbol::{Sym, SymTab};
use std::rc::Rc;

/// A name is an interned `Sym`, not a `String` -- see `crate::symbol` for why,
/// and for the one catch: the text is only readable through the `SymTab` that
/// interned it, which `Chapter` carries.
pub type Name = Sym;

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

/// The three forms that carry the most and appear the least.
///
/// **An enum is as large as its largest variant, and `Expr` is moved by every
/// pass over 6.58M nodes.** These three held 96, 96 and 72 bytes of payload
/// where nothing else exceeded 64, so they set the size of every node in the
/// tree -- including the two `Expr`s inlined in each of 17,618 match arms.
/// Boxed, they cost one pointer here and one allocation on the rare occasions
/// they actually appear. The fields are unchanged, so this is still
/// `AstNodes.codex` variant for variant.
#[derive(Clone, Debug)]
pub struct HandleExpr {
    pub effect: Name,
    pub body: Rc<Expr>,
    pub clauses: Vec<HandleClause>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct WithTimeoutExpr {
    pub timeout: String,
    pub effects: Vec<Name>,
    /// Always empty today: nothing constructs it and nothing reads it. Kept
    /// because the upstream node has it.
    pub labels: Vec<String>,
    pub body: Rc<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct TryExpr {
    pub count: i64,
    pub body: Vec<ActStmt>,
    pub fallback: Vec<ActStmt>,
    pub failure: Vec<ActStmt>,
    pub span: Span,
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
    Handle(Box<HandleExpr>),
    WithTimeout(Box<WithTimeoutExpr>),
    Try(Box<TryExpr>),
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
            Expr::Handle(h) => {
                h.body.walk(f);
                for c in &h.clauses {
                    c.body.walk(f);
                }
            }
            Expr::WithTimeout(w) => w.body.walk(f),
            Expr::Try(t) => {
                stmts(&t.body, f);
                stmts(&t.fallback, f);
                stmts(&t.failure, f);
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Chapter {
    /// The table every `Name` in this chapter indexes. It travels with the
    /// tree because a `Sym` read against the wrong table is a wrong name.
    pub syms: SymTab,
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

#[cfg(test)]
mod tests {
    use super::*;

    /// **An enum is as large as its largest variant, and every pass moves
    /// `Expr`s** -- 6,575,252 of them over the corpus, two of them inlined in
    /// each of 17,618 match arms. `Handle`, `WithTimeout` and `Try` held 72,
    /// 96 and 96 bytes of payload where nothing else exceeded 64, so three of
    /// the rarest forms in the language set the size of the whole tree. They
    /// are boxed; this is the guard that keeps them that way. 104 bytes then,
    /// 72 once they were boxed, 56 once a `Name` became a four-byte `Sym`.
    #[test]
    fn expr_does_not_grow() {
        assert!(
            std::mem::size_of::<Expr>() <= 56,
            "Expr is {} bytes; a variant grew",
            std::mem::size_of::<Expr>()
        );
    }
}
