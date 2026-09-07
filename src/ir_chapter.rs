//! The IR tree -- `IR/IRChapter.codex`, variant for variant.
//!
//! ## Why there is a tree at all
//!
//! Lowering used to emit TEXT directly, and it got a long way on that: every
//! node's spelling is a function of its children's spellings and its own type,
//! so a recursive `Expr -> String` reached twenty-four of the curated
//! twenty-eight.
//!
//! It cannot reach the last four, and the reason is not a missing node form.
//! **The golds are POST-PIPELINE.** `fold-constants`, `inline-leaf-calls` and
//! `inline-single-caller` REWRITE the lowered program -- a leaf function's body
//! is substituted at its call sites -- and `ir-prune-unreachable-roots` then
//! drops the definitions nothing references any more. `sb-length`,
//! `signal-delivered-count`, `fused-lt`: the gold has neither the call nor the
//! definition, and we had both. A pass that rewrites a program needs the
//! program, and a string is not one.
//!
//! So this is the layer the passes work on, and emission moves to `ir_text.rs`
//! where it belongs.
//!
//! ## What is here and what is not
//!
//! The variants lowering can actually build. `IrHandle`, `IrWithTimeout`,
//! `IrFork`, `IrAwait` and `IrTry` are upstream's and are NOT here, because
//! lowering refuses those forms today -- a pass cannot mishandle a node that
//! cannot exist, and a variant nothing constructs is a floor nobody is
//! standing on. They come back with the lowering that builds them.
//!
//! ## The type is ON the node
//!
//! `ir-expr-type` is total upstream and total here: every expression knows its
//! own type, which is what lets a pass substitute one expression for another
//! and still emit correct text. A literal is the exception that proves it --
//! `IrIntLit` carries no type field because its type is `int-default` by
//! construction.

use crate::ast::Span;
use crate::check::Ty;
use crate::symbol::Sym;

/// `IRBinaryOp`. **The operator is decided at LOWERING, not at emission**:
/// `add-int`, `add-num` and `add-vec` are three operators for one source `+`,
/// and which one it is depends on the operand type, which lowering has and a
/// later pass would have to work out again.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IrBinOp {
    AddInt,
    SubInt,
    MulInt,
    DivInt,
    AddNum,
    SubNum,
    MulNum,
    DivNum,
    Eq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    And,
    Or,
    AppendText,
    AppendList,
    ConsList,
    ApproxEq,
    ApproxEqExact,
}

impl IrBinOp {
    /// The atom `ir-emit-binop` writes.
    pub fn atom(self) -> &'static str {
        match self {
            IrBinOp::AddInt => "add-int",
            IrBinOp::SubInt => "sub-int",
            IrBinOp::MulInt => "mul-int",
            IrBinOp::DivInt => "div-int",
            IrBinOp::AddNum => "add-num",
            IrBinOp::SubNum => "sub-num",
            IrBinOp::MulNum => "mul-num",
            IrBinOp::DivNum => "div-num",
            IrBinOp::Eq => "eq",
            IrBinOp::NotEq => "ne",
            IrBinOp::Lt => "lt",
            IrBinOp::Gt => "gt",
            IrBinOp::LtEq => "le",
            IrBinOp::GtEq => "ge",
            IrBinOp::And => "and",
            IrBinOp::Or => "or",
            IrBinOp::AppendText => "append-text",
            IrBinOp::AppendList => "append-list",
            IrBinOp::ConsList => "cons-list",
            IrBinOp::ApproxEq => "approx-eq",
            IrBinOp::ApproxEqExact => "approx-eq-exact",
        }
    }
}

#[derive(Clone, Debug)]
pub struct IrParam {
    pub name: Sym,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct IrBranch {
    pub pattern: IrPat,
    pub body: IrExpr,
    pub guard: IrExpr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct IrFieldVal {
    pub name: Sym,
    pub value: IrExpr,
}

#[derive(Clone, Debug)]
pub enum IrActStmt {
    Bind(Sym, Ty, IrExpr, Span),
    Exec(IrExpr, Span),
}

impl IrActStmt {
    pub fn expr(&self) -> &IrExpr {
        match self {
            IrActStmt::Bind(_, _, e, _) | IrActStmt::Exec(e, _) => e,
        }
    }
}

/// `IRPat`. **A CONSTRUCTOR PATTERN CARRIES THE SCRUTINEE'S TYPE**, not its
/// own result type, and each sub-pattern carries the field's.
#[derive(Clone, Debug)]
pub enum IrPat {
    Var(Sym, Ty, Span),
    Lit(String, Ty, Span),
    Ctor(Sym, Vec<IrPat>, Ty, Span),
    Wild(Span),
    Vec_(Vec<IrPat>, Ty, Span),
}

#[derive(Clone, Debug)]
pub enum IrExpr {
    /// No type field: an integer literal is `int-default` by construction.
    IntLit(i64, Span),
    /// The f64's BITS read as a signed integer, not the decimal written.
    NumLit(i64, Span),
    /// The literal AS THE SOURCE SPELLED IT, quotes included -- see
    /// `ir_text::emit_expr`.
    TextLit(String, Span),
    BoolLit(bool, Span),
    /// The CHAR-CODE, not the byte and not the codepoint.
    CharLit(i64, Span),
    Name(Sym, Ty, Span),
    Binary(IrBinOp, Box<IrExpr>, Box<IrExpr>, Ty, Span),
    Negate(Box<IrExpr>, Ty, Span),
    If(Box<IrExpr>, Box<IrExpr>, Box<IrExpr>, Ty, Span),
    Let(Sym, Ty, Box<IrExpr>, Box<IrExpr>, Span),
    Apply(Box<IrExpr>, Box<IrExpr>, Ty, Span),
    Lambda(Vec<IrParam>, Box<IrExpr>, Ty, Span),
    /// The type is the ELEMENT's, which is what the wire carries.
    List(Vec<IrExpr>, Ty, Span),
    Match(Box<IrExpr>, Vec<IrBranch>, Ty, Span),
    Act(Vec<IrActStmt>, Ty, Span),
    Record(Sym, Vec<IrFieldVal>, Ty, Span),
    /// The field name and its SLOT are spelled together as `"py/1"`, so the
    /// slot is resolved at lowering and carried here as part of the name.
    FieldAccess(Box<IrExpr>, String, Ty, Span),
    /// **The type is the RECORD's**: a store evaluates to what it wrote into.
    FieldStore(Box<IrExpr>, String, Box<IrExpr>, Ty, Span),
}

impl IrExpr {
    /// `ir-expr-type` (IRChapter.codex:170). TOTAL, which is the property the
    /// passes depend on: substituting one expression for another is sound only
    /// if both can say what they are.
    pub fn ty(&self) -> Ty {
        use IrExpr as E;
        match self {
            E::IntLit(..) => Ty::Integer(i64::MIN, i64::MAX, crate::check::Overflow::Error),
            E::NumLit(..) => {
                Ty::Real(crate::check::RealWidth::F64, crate::check::RealMode::Default)
            }
            E::TextLit(..) => Ty::Text,
            E::BoolLit(..) => Ty::Boolean,
            E::CharLit(..) => Ty::Char,
            E::Name(_, t, _)
            | E::Binary(_, _, _, t, _)
            | E::Negate(_, t, _)
            | E::If(_, _, _, t, _)
            | E::Apply(_, _, t, _)
            | E::Lambda(_, _, t, _)
            | E::Match(_, _, t, _)
            | E::Act(_, t, _)
            | E::Record(_, _, t, _)
            | E::FieldAccess(_, _, t, _)
            | E::FieldStore(_, _, _, t, _) => t.clone(),
            // **A LIST'S NODE TYPE IS NOT THE TYPE IT CARRIES.** The wire
            // spells the ELEMENT type after `(list-expr (elems ...) T)`, so
            // the node's own type is one `list` around it.
            E::List(_, elem, _) => Ty::List(Box::new(elem.clone())),
            // A let evaluates to its body.
            E::Let(_, _, _, body, _) => body.ty(),
        }
    }

    pub fn span(&self) -> Span {
        use IrExpr as E;
        match self {
            E::IntLit(_, s)
            | E::NumLit(_, s)
            | E::TextLit(_, s)
            | E::BoolLit(_, s)
            | E::CharLit(_, s)
            | E::Name(_, _, s)
            | E::Binary(_, _, _, _, s)
            | E::Negate(_, _, s)
            | E::If(_, _, _, _, s)
            | E::Let(_, _, _, _, s)
            | E::Apply(_, _, _, s)
            | E::Lambda(_, _, _, s)
            | E::List(_, _, s)
            | E::Match(_, _, _, s)
            | E::Act(_, _, s)
            | E::Record(_, _, _, s)
            | E::FieldAccess(_, _, _, s)
            | E::FieldStore(_, _, _, _, s) => *s,
        }
    }

    /// Every direct sub-expression, in the order the passes visit them.
    ///
    /// **A branch's BODY comes before its GUARD**, which is `lift-branches`'
    /// order and not the order the source writes them. It is load-bearing:
    /// lambda lifting numbers `__lam_N` in visit order.
    pub fn children(&self) -> Vec<&IrExpr> {
        use IrExpr as E;
        match self {
            E::IntLit(..)
            | E::NumLit(..)
            | E::TextLit(..)
            | E::BoolLit(..)
            | E::CharLit(..)
            | E::Name(..) => vec![],
            E::Binary(_, l, r, _, _) | E::FieldStore(l, _, r, _, _) => vec![l, r],
            E::Apply(f, a, _, _) => vec![f, a],
            E::Let(_, _, v, b, _) => vec![v, b],
            E::Negate(x, _, _) | E::FieldAccess(x, _, _, _) | E::Lambda(_, x, _, _) => vec![x],
            E::If(c, t, e, _, _) => vec![c, t, e],
            E::List(xs, _, _) => xs.iter().collect(),
            E::Record(_, fs, _, _) => fs.iter().map(|f| &f.value).collect(),
            E::Act(ss, _, _) => ss.iter().map(|s| s.expr()).collect(),
            E::Match(sc, bs, _, _) => {
                let mut v = vec![&**sc];
                for b in bs {
                    v.push(&b.body);
                    v.push(&b.guard);
                }
                v
            }
        }
    }

    /// The whole tree, pre-order.
    pub fn walk(&self, f: &mut impl FnMut(&IrExpr)) {
        f(self);
        for c in self.children() {
            c.walk(f);
        }
    }
}

/// `IRDef`. `is-punctual` and `wcet-budget` are upstream's and are emitted as
/// the trailing `0 0` of every `(def ...)`; nothing here sets them, so they are
/// not carried as fields that would only ever hold zero.
#[derive(Clone, Debug)]
pub struct IrDef {
    pub name: Sym,
    pub params: Vec<IrParam>,
    pub ty: Ty,
    pub body: IrExpr,
    pub chapter_slug: String,
    pub span: Span,
}
