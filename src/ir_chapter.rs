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
//! The variants lowering can actually build. `IrWithTimeout`, `IrFork`,
//! `IrAwait` and `IrTry` are upstream's and are NOT here, because lowering
//! refuses those forms today -- a pass cannot mishandle a node that cannot
//! exist, and a variant nothing constructs is a floor nobody is standing on.
//! They come back with the lowering that builds them, as `IrHandle` did.
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
    /// `int-rem a b` lowers to a binary (`lower-int-rem-apply`).
    RemInt,
    AddNum,
    SubNum,
    MulNum,
    DivNum,
    AddRealApprox,
    SubRealApprox,
    MulRealApprox,
    DivRealApprox,
    AddRealTrapping,
    SubRealTrapping,
    MulRealTrapping,
    DivRealTrapping,
    AddRealSaturating,
    SubRealSaturating,
    MulRealSaturating,
    DivRealSaturating,
    AddVec,
    SubVec,
    MulVec,
    DivVec,
    LtVec,
    GtVec,
    LtEqVec,
    GtEqVec,
    /// **ALWAYS `pow-int`, WHATEVER THE OPERANDS.** `lower-binary`'s `is OpPow
    /// -> IrPowInt` has no Real arm, and the oracle spells `pow-int` for
    /// `pow-on-real` too. The refusal a float exponent deserves is raised at
    /// x86 emit (`cdx-pow-on-float`), not here.
    PowInt,
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
    /// `bin-op-atom-typed`. **THE OVERFLOW MODE IS PART OF THE OPERATOR'S
    /// NAME**, for the three integer operations that can overflow: over a
    /// wrapping integer `+`, `-` and `*` are spelled `add-int-wrapping`,
    /// `sub-int-wrapping` and `mul-int-wrapping`. Nothing else changes.
    ///
    /// The type asked is the BINARY NODE'S OWN, not either operand's.
    pub fn atom_typed(self, ty: &Ty) -> &'static str {
        if int_ty_wraps(ty) {
            match self {
                IrBinOp::AddInt => return "add-int-wrapping",
                IrBinOp::SubInt => return "sub-int-wrapping",
                IrBinOp::MulInt => return "mul-int-wrapping",
                _ => {}
            }
        }
        self.atom()
    }

    /// The atom `ir-emit-binop` writes.
    pub fn atom(self) -> &'static str {
        match self {
            IrBinOp::AddInt => "add-int",
            IrBinOp::SubInt => "sub-int",
            IrBinOp::MulInt => "mul-int",
            IrBinOp::DivInt => "div-int",
            IrBinOp::RemInt => "rem-int",
            IrBinOp::AddNum => "add-num",
            IrBinOp::SubNum => "sub-num",
            IrBinOp::MulNum => "mul-num",
            IrBinOp::DivNum => "div-num",
            IrBinOp::AddRealApprox => "add-real-approx",
            IrBinOp::SubRealApprox => "sub-real-approx",
            IrBinOp::MulRealApprox => "mul-real-approx",
            IrBinOp::DivRealApprox => "div-real-approx",
            IrBinOp::AddRealTrapping => "add-real-trapping",
            IrBinOp::SubRealTrapping => "sub-real-trapping",
            IrBinOp::MulRealTrapping => "mul-real-trapping",
            IrBinOp::DivRealTrapping => "div-real-trapping",
            IrBinOp::AddRealSaturating => "add-real-saturating",
            IrBinOp::SubRealSaturating => "sub-real-saturating",
            IrBinOp::MulRealSaturating => "mul-real-saturating",
            IrBinOp::DivRealSaturating => "div-real-saturating",
            IrBinOp::AddVec => "add-vec",
            IrBinOp::SubVec => "sub-vec",
            IrBinOp::MulVec => "mul-vec",
            IrBinOp::DivVec => "div-vec",
            IrBinOp::LtVec => "lt-vec",
            IrBinOp::GtVec => "gt-vec",
            IrBinOp::LtEqVec => "le-vec",
            IrBinOp::GtEqVec => "ge-vec",
            IrBinOp::PowInt => "pow-int",
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

/// `IRHandleClause`. **THE PARAMETER NAMES ARE CARRIED TWICE ON PURPOSE**:
/// once as `params`, which the wire spells, and once inside `body`, which
/// `wrap-clause-body-in-lambda` wraps in an `IrLambda` over the same names.
/// A clause with no parameters is not wrapped.
#[derive(Clone, Debug)]
pub struct IrHandleClause {
    pub op_name: String,
    pub params: Vec<Sym>,
    pub resume_name: Sym,
    pub body: IrExpr,
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

impl IrExpr {
    /// `set-ir-expr-type` (subject 36797). **AN ALLOW-LIST, NOT A WALK.**
    /// Half the IR cannot hold a type -- a literal has no field for one -- so
    /// the arms that can are named and everything else is returned unchanged.
    pub fn with_ty(self, new: Ty) -> IrExpr {
        use IrExpr as E;
        match self {
            E::Name(n, _, s) => E::Name(n, new, s),
            E::Apply(f, a, _, s) => E::Apply(f, a, new, s),
            E::Let(n, _, v, b, s) => E::Let(n, new, v, b, s),
            E::If(c, t, e, _, s) => E::If(c, t, e, new, s),
            E::Match(sc, bs, _, s) => E::Match(sc, bs, new, s),
            E::Act(ss, _, s) => E::Act(ss, new, s),
            E::Record(n, fs, _, s) => E::Record(n, fs, new, s),
            E::FieldAccess(r, f, _, s) => E::FieldAccess(r, f, new, s),
            other => other,
        }
    }
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

/// `int-ty-wraps`. A unit type answers for what is inside it.
fn int_ty_wraps(ty: &Ty) -> bool {
    match ty {
        Ty::Integer(_, _, m) => *m == crate::check::Overflow::Wrapping,
        Ty::Unit(_, inner) => int_ty_wraps(inner),
        _ => false,
    }
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
    /// `(handle EFF BODY (clauses ...) TYPE)`. The effect is a NAME on the
    /// wire, not a type.
    Handle(String, Box<IrExpr>, Vec<IrHandleClause>, Ty, Span),
    /// `(with-timeout SECS (effs ..) (scopes ..) BODY TYPE)`.
    WithTimeout(i64, Vec<String>, Vec<String>, Box<IrExpr>, Ty, Span),
    /// `(try MAX (body ..) (fallback ..) (fail ..) TYPE)`. Three statement
    /// lists, all of them real program.
    Try(i64, Vec<IrActStmt>, Vec<IrActStmt>, Vec<IrActStmt>, Ty, Span),
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
            | E::FieldStore(_, _, _, t, _)
            | E::Handle(_, _, _, t, _)
            | E::WithTimeout(_, _, _, _, t, _)
            | E::Try(_, _, _, _, t, _) => t.clone(),
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
            | E::FieldStore(_, _, _, _, s)
            | E::Handle(_, _, _, _, s)
            | E::WithTimeout(_, _, _, _, _, s)
            | E::Try(_, _, _, _, _, s) => *s,
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
            E::Handle(_, b, cs, _, _) => {
                let mut v = vec![&**b];
                v.extend(cs.iter().map(|c| &c.body));
                v
            }
            E::WithTimeout(_, _, _, b, _, _) => vec![b],
            E::Try(_, b, fb, fl, _, _) => b
                .iter()
                .chain(fb)
                .chain(fl)
                .map(|s| s.expr())
                .collect(),
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

/// `IRDef`.
#[derive(Clone, Debug)]
pub struct IrDef {
    pub name: Sym,
    pub params: Vec<IrParam>,
    pub ty: Ty,
    pub body: IrExpr,
    pub chapter_slug: String,
    pub span: Span,
    /// The trailing two fields of the emitted `(def ...)`. They come off the
    /// `punctual` modifier the parser read; upstream recovers them at lowering
    /// by looking the definition's NAME up in the chapter's `rt-names`.
    pub is_punctual: bool,
    pub wcet_budget: i64,
    /// The parameters declared `linear`, by name. **THIS IS THE ONLY PLACE
    /// LINEARITY REACHES THE WIRE**: it is carried the length of the pipeline
    /// and consumed at x86 emit for noalias slots, and until upstream printed
    /// it `linear T` and `T` produced byte-identical IR (subject 57984).
    pub unique_params: Vec<Sym>,
}

/// The overflow mode is part of the operator's NAME.
#[cfg(test)]
mod wrapping_is_in_the_operator {
    use super::{int_ty_wraps, IrBinOp};
    use crate::check::{Overflow, Ty};

    const WRAP: Ty = Ty::Integer(i64::MIN, i64::MAX, Overflow::Wrapping);
    const PLAIN: Ty = Ty::Integer(i64::MIN, i64::MAX, Overflow::Error);

    #[test]
    fn only_the_three_that_can_overflow_are_respelled() {
        assert_eq!(IrBinOp::MulInt.atom_typed(&WRAP), "mul-int-wrapping");
        assert_eq!(IrBinOp::AddInt.atom_typed(&WRAP), "add-int-wrapping");
        assert_eq!(IrBinOp::SubInt.atom_typed(&WRAP), "sub-int-wrapping");
        assert_eq!(IrBinOp::DivInt.atom_typed(&WRAP), "div-int");
        assert_eq!(IrBinOp::Lt.atom_typed(&WRAP), "lt");
        assert_eq!(IrBinOp::MulInt.atom_typed(&PLAIN), "mul-int");
    }

    #[test]
    fn a_unit_answers_for_what_is_inside_it() {
        let sym = crate::symbol::SymTab::default().intern("Meter");
        assert!(int_ty_wraps(&Ty::Unit(sym, Box::new(WRAP))));
        assert!(!int_ty_wraps(&Ty::Unit(sym, Box::new(PLAIN))));
    }
}
