//! The AST to the IR tree -- `IR/Lowering.codex`.
//!
//! This walks the desugared AST and builds what it can TYPE WITH CERTAINTY,
//! from three sources and no inference: a definition's own declared type, the
//! builtin table's declared types, and the checker's recorded answers.
//!
//! ## It refuses rather than guesses, and that is the whole design
//!
//! Every function here returns the REASON it could not lower a node. A guessed
//! type is not a partial answer -- it is a wrong answer that reads exactly like
//! a right one until someone diffs 900 bytes of nested s-expressions. A bare
//! `None` once told us the corpus refused 1,008 of 1,012 units and nothing
//! about which missing piece would buy the most, so the next node form got
//! picked by guessing; a reason turns that into a histogram.
//!
//! ## The wire's type comes from the EXPECTATION
//!
//! `lower-expr` carries an expected type down from the definition's declared
//! return type, and most nodes publish THAT rather than something read back
//! out of their children. `guarded-field` is the argument in one line: its
//! then-branch emits `(int 0 15 ov-error)`, its else-branch `(int-lit 0)`, and
//! the `if` around them `int-default`. Three types, all correct, none
//! derivable from the others. See `lowering_types.rs` for the arithmetic that
//! reconciles the expectation with what was actually lowered.
//!
//! ## Types are read by SPAN, never by name
//!
//! `lookup-expr-type (ctx.ust) sp`. Not a shortcut: `fib` appears twice in its
//! own body and the checker recorded a different row id at each occurrence, so
//! a lookup by name would have to pick one and would be wrong about the other.

use crate::ast::{BinaryOp, Expr, LiteralKind, Pat};
use crate::check::{Binding, Ty, TypeDefs, UnifyState};
use crate::ir_chapter::{
    IrActStmt, IrBinOp, IrBranch, IrDef, IrExpr, IrFieldVal, IrParam, IrPat,
};
use crate::ir_text::render_ty;
use crate::lowering_types as lt;
use crate::symbol::{Sym, SymTab};
use std::collections::BTreeMap;

/// The types lowering needs and the checker's answers, for one chapter.
///
/// **A NAME IS READ OUT OF `expr-types` BY SPAN**, and `bindings` is the
/// fallback `lower-name-normal` reaches for when the span is synthetic and the
/// checker therefore recorded nothing -- plus the `(def ...)` headers.
pub struct Lower<'a> {
    /// **BEHIND A CELL BECAUSE LOWERING MINTS NAMES.** `binder-fresh` spells a
    /// shadowing `let max` as `max_1`, and that name is in no source. Reads
    /// borrow for a line at a time; the only writer is `bind_local`.
    pub syms: &'a std::cell::RefCell<SymTab>,
    st: &'a UnifyState,
    /// The chapter's type declarations. Lowering asks them two things the
    /// checker did not record: a field's TYPE and its SLOT, which the wire
    /// spells as `"py/1"`.
    tds: &'a TypeDefs,
    bindings: BTreeMap<Sym, Ty>,
    /// `__linked-list-empty`, which `lower-empty-list` CALLS and no source
    /// need ever name. Interned into the table before lowering starts, since
    /// a `Sym` is an index into the table that made it.
    ll_empty: Sym,
    /// `base`, for `binder-free` alone: every name the checker had a type for,
    /// the BUILTINS included. Being in here is what makes a binder a shadow.
    base: std::collections::BTreeSet<Sym>,
    /// `overlay` -- what is in scope right here, keyed by the EMITTED name,
    /// innermost last. A stack rather than upstream's persistent list: the
    /// walk is strictly depth-first and a binding is visible in exactly one
    /// subtree, so pushing on the way in and truncating on the way out is the
    /// same set at every point.
    overlay: std::cell::RefCell<Vec<(Sym, Ty)>>,
    /// `binders` -- source name to emitted name, innermost last. Separate
    /// from the overlay because a rename must be found by the name the SOURCE
    /// wrote while the shadow test must be answered about the name we would
    /// EMIT.
    binders: std::cell::RefCell<Vec<(Sym, Sym)>>,
}

impl<'a> Lower<'a> {
    pub fn new(
        syms: &'a std::cell::RefCell<SymTab>,
        bindings: &[Binding],
        st: &'a UnifyState,
        tds: &'a TypeDefs,
        ll_empty: Sym,
    ) -> Lower<'a> {
        let mut base: std::collections::BTreeSet<Sym> =
            crate::check::builtin_names(&syms.borrow()).into_iter().collect();
        base.extend(bindings.iter().map(|b| b.name));
        Lower {
            syms,
            st,
            tds,
            bindings: bindings.iter().map(|b| (b.name, b.ty.clone())).collect(),
            ll_empty,
            base,
            overlay: std::cell::RefCell::new(Vec::new()),
            binders: std::cell::RefCell::new(Vec::new()),
        }
    }

    /// The text of a name. One borrow, one line.
    fn text(&self, n: Sym) -> String {
        self.syms.borrow().text(n).to_string()
    }

    /// `lookup-overlay`: the innermost binding of an EMITTED name.
    fn overlay_ty(&self, n: Sym) -> Option<Ty> {
        self.overlay.borrow().iter().rev().find(|(m, _)| *m == n).map(|(_, t)| t.clone())
    }

    /// `bound-name` (subject 55194): what a source name is EMITTED as here.
    /// Unrenamed names are not in the table, so the fallback is the name.
    pub fn bound_name(&self, n: Sym) -> Sym {
        self.binders.borrow().iter().rev().find(|(src, _)| *src == n).map_or(n, |(_, e)| *e)
    }

    /// `binder-free` (subject 55199): neither in the overlay nor in the base.
    fn binder_free(&self, n: Sym) -> bool {
        self.overlay_ty(n).is_none() && !self.base.contains(&n)
    }

    /// `bind-local` (subject 55228). Answers the name to EMIT, which is the
    /// source name unless it is already taken -- then `binder-fresh` counts
    /// upward from `_1` until it is not.
    fn bind_local(&self, n: Sym, t: Ty) -> Sym {
        let emitted = if self.binder_free(n) {
            n
        } else {
            let base = self.text(n);
            let mut k = 1u32;
            loop {
                let cand = self.syms.borrow_mut().intern(&format!("{base}_{k}"));
                if self.binder_free(cand) {
                    break cand;
                }
                k += 1;
            }
        };
        self.overlay.borrow_mut().push((emitted, t));
        self.binders.borrow_mut().push((n, emitted));
        emitted
    }

    /// A parameter of the DEFINITION, which `bind-params-to-ctx` pushes
    /// straight onto the overlay: no rename and no binder entry, so a
    /// definition's own parameter is never re-spelled.
    fn bind_param(&self, n: Sym, t: Ty) {
        self.overlay.borrow_mut().push((n, t));
    }

    /// How deep the scopes are, to unwind back to.
    fn mark(&self) -> (usize, usize) {
        (self.overlay.borrow().len(), self.binders.borrow().len())
    }

    fn release(&self, (o, b): (usize, usize)) {
        self.overlay.borrow_mut().truncate(o);
        self.binders.borrow_mut().truncate(b);
    }

    /// The type the checker recorded at this exact source position, resolved
    /// through the substitutions. A HALF-resolved type reaches the wire as
    /// `(tvar 4)` where the oracle spells `int-default`, so the walk is the
    /// deep one.
    fn at(&self, sp: crate::ast::Span) -> Option<Ty> {
        self.st.expr_type_at(sp).map(|t| self.st.deep_resolve(t))
    }

    /// `lookup-expr-type` (Unifier.codex:46165), which is TOTAL: its first
    /// line is `if is-synthetic-span sp then ErrorTy`, and a key it does not
    /// hold answers `ErrorTy` too.
    ///
    /// **THE ABSENCE IS AN ANSWER, NOT A FAILURE.** Every caller upstream
    /// dispatches on `is ErrorTy | NoExpectTy`, so a refusal here is not a
    /// stricter version of the same rule -- it is a different rule, and it
    /// stopped the self-host lowering at one comprehension.
    fn recorded(&self, sp: crate::ast::Span) -> Ty {
        self.at(sp).unwrap_or(Ty::Error)
    }
}

/// One definition. `absorb-outer-lambdas` is applied here rather than in the
/// lifting pass: a definition written `f = \x -> ...` carries that lambda's
/// parameters as its OWN, and the lambda is never lifted.
pub fn lower_def(d: &crate::ast::Def, cx: &Lower) -> Result<IrDef, String> {
    let name = d.name;
    let bound = match cx.bindings.get(&name) {
        // **THE CHECKER'S BINDING, NOT THE DECLARATION.** They agree wherever
        // a definition declares a type, and only the checker has an answer
        // where one does not.
        Some(t) => cx.st.deep_resolve(t),
        None => return Err(format!("`{}` was never bound by the checker", cx.text(name))),
    };
    let mut own: Vec<Sym> = d.params.iter().map(|p| p.name).collect();
    let mut body_expr: &Expr = &d.body;
    while let Expr::Lambda(ps, inner, _) = body_expr {
        own.extend(ps.iter().copied());
        body_expr = inner;
    }
    // Parameter types come from walking the bound arrow spine, which is the
    // only place they are written down.
    // **THE SCOPE STARTS EMPTY FOR EVERY DEFINITION.** A refusal leaves the
    // stack wherever it stopped, so this is a reset rather than an assertion.
    cx.release((0, 0));
    let mut rest = bound.clone();
    let mut params = Vec::new();
    // `linear-param-names` (subject 55885) walks the DECLARED parameters only:
    // a lambda's own parameters are not the definition's, and cannot be
    // declared linear.
    let mut unique_params: Vec<Sym> = Vec::new();
    for (i, p) in own.iter().enumerate() {
        let (arg, res) = match rest {
            Ty::Fun(a, _, r) => (*a, *r),
            _ => {
                return Err(format!(
                    "`{}` has more params than its type has arrows",
                    cx.text(name)
                ))
            }
        };
        if i < d.params.len() && matches!(arg, Ty::Linear(_)) {
            unique_params.push(*p);
        }
        cx.bind_param(*p, arg.clone());
        params.push(IrParam { name: *p, ty: arg, span: d.span });
        rest = res;
    }
    let body = expr(body_expr, &rest, cx).map_err(|r| format!("{}: {r}", cx.text(name)))?;
    Ok(IrDef {
        name,
        params,
        ty: bound,
        body,
        chapter_slug: d.chapter_slug.clone(),
        span: d.span,
        is_punctual: d.is_punctual,
        wcet_budget: d.wcet_budget,
        unique_params,
    })
}

/// One expression, or the REASON it was refused.
pub fn expr(e: &Expr, want: &Ty, cx: &Lower) -> Result<IrExpr, String> {
    match e {
        Expr::Lit(v, LiteralKind::IntLit, s) => {
            Ok(IrExpr::IntLit(crate::token::lit_text_to_integer(v), *s))
        }
        // Decoded by the desugarer; `ir-quote` re-encodes it at the wire.
        Expr::Lit(v, LiteralKind::TextLit, s) => Ok(IrExpr::TextLit(v.clone(), *s)),
        Expr::Lit(v, LiteralKind::BoolLit, s) => Ok(IrExpr::BoolLit(v == "True", *s)),
        // **THE f64's BITS, READ AS A SIGNED INTEGER**, not the decimal the
        // source wrote. Rust's own `parse` is correctly rounded and upstream's
        // conversion is not (issue 125: correct to 15 significant digits,
        // wrong above 2^53), so this is a place the two arms may legitimately
        // disagree and a difference here is a finding, not a defect.
        Expr::Lit(v, LiteralKind::NumLit, s) => {
            let bits =
                v.parse::<f64>().map_err(|_| format!("`{v}` is not a Real literal"))?.to_bits();
            Ok(IrExpr::NumLit(bits as i64, *s))
        }
        // `lower-literal` is `IrCharLit (text-to-integer text)`, and the
        // text IS the char-code by now -- the desugarer put it there.
        Expr::Lit(v, LiteralKind::CharLit, s) => {
            Ok(IrExpr::CharLit(crate::token::lit_text_to_integer(v), *s))
        }
        // `(negate X TYPE)`, and the type is the OPERAND's -- negating does
        // not change it. `-n` is this; `0 - n` is a `binary sub-int`, and the
        // two are different nodes on the wire even where a reader would call
        // them the same expression.
        Expr::Unary(x, s) => {
            let x = expr(x, &Ty::NoExpect, cx)?;
            let t = x.ty();
            Ok(IrExpr::Negate(Box::new(x), t, *s))
        }
        // `lower-name-normal` (IR/Lowering.codex:54520) is a THREE-LEVEL
        // fallback, and only the first level was here.
        //
        // **THE RECORDED ANSWER IS ABSENT FOR A SYNTHETIC SPAN, AND THE
        // DESUGARER MAKES THOSE** -- `MkTupN`, `__rev`, `__narrow`,
        // `__record-set`, the lambda and applications around a
        // comprehension's `map-list`. `lookup-expr-type`'s own first line is
        // `if is-synthetic-span sp then ErrorTy`. Refusing here is what
        // stopped the whole 3.44 MB self-host from lowering, on one
        // comprehension in `tco-ensure-temps`.
        //
        // The `map-list` NAME is not one of them: upstream stamps it with the
        // loop variable's span, so the checker records it and the first
        // level answers. Our desugarer stamped it synthetic until 1354fec,
        // which is why this fallback used to carry every comprehension.
        //
        // Upstream falls back to the name's BINDING, stripped of its forall,
        // and then to the expectation. Neither is a guess: the binding is the
        // checker's own answer for the name, and the expectation is what the
        // caller of this node already committed to.
        Expr::NameRef(n, s) => {
            // `lower-name-normal` strips the quantifiers off BOTH answers,
            // the recorded one included -- a `(forall 39 ...)` on a name is
            // the signature's binder and not part of what the name is here.
            //
            // The NAME is `bound-name`'s: a reference to a binder that was
            // re-spelled has to be re-spelled with it.
            let rn = cx.bound_name(*n);
            let t = match cx.at(*s) {
                Some(t) => crate::check::strip_forall(&t),
                None => match cx.overlay_ty(rn).or_else(|| cx.bindings.get(n).cloned()) {
                    Some(raw) => crate::check::strip_forall(&cx.st.deep_resolve(&raw)),
                    None => want.clone(),
                },
            };
            Ok(IrExpr::Name(rn, t, *s))
        }
        // `lower-apply-normal` (Lowering.codex:612). **THE CALLEE'S PARAMETER
        // IS THE ARGUMENT'S EXPECTATION**, and the return is then INSTANTIATED
        // by matching that parameter against what the argument turned out to
        // be. Both halves were missing: every argument was lowered with no
        // expectation at all, so a lambda handed to `map-list` had nothing to
        // peel its parameters from and reached the wire with `error` in each
        // slot -- seventy lifted lambdas in the compiler.
        //
        // Upstream never refuses here. A callee whose type is not an arrow
        // peels to `ErrorTy` and the node takes the expectation, or the
        // checker's recorded answer, instead.
        // `lower-apply`: two builtins applied to two arguments lower to
        // their own shapes -- `int-rem a b` is a `rem-int` binary and
        // `compare a b` dispatches on the left operand's type
        // (`lower-int-rem-apply`, `lower-compare-apply`).
        Expr::Apply(f, a, s) if special_apply_name(f, cx).is_some() => {
            let (name, a1) = special_apply_name(f, cx).expect("guarded");
            let int_default = Ty::Integer(i64::MIN, i64::MAX, crate::check::Overflow::Error);
            if name == "int-rem" {
                let l = expr(&a1, &int_default, cx)?;
                let r = expr(a, &int_default, cx)?;
                return Ok(IrExpr::Binary(IrBinOp::RemInt, Box::new(l), Box::new(r), want.clone(), *s));
            }
            let l = expr(&a1, &Ty::NoExpect, cx)?;
            let r = expr(a, &Ty::NoExpect, cx)?;
            let lt = cx.st.deep_resolve(&l.ty());
            let tn = type_name_of(&lt, cx);
            let helper = if tn.is_empty() || is_primitive_type_name(&tn) {
                None
            } else {
                cx.syms.borrow().find(&format!("__compare_{tn}")).and_then(|h| {
                    cx.overlay_ty(h).or_else(|| cx.bindings.get(&h).cloned()).map(|t| (h, t))
                })
            };
            return Ok(match helper {
                Some((h, raw)) => {
                    let fty = crate::check::strip_forall(&cx.st.deep_resolve(&raw));
                    let inner = IrExpr::Apply(
                        Box::new(IrExpr::Name(h, fty.clone(), *s)),
                        Box::new(l),
                        peel_fun_return(&fty),
                        *s,
                    );
                    IrExpr::Apply(Box::new(inner), Box::new(r), int_default, *s)
                }
                None => lower_compare_prim(&lt, l, r, cx, *s),
            });
        }
        Expr::Apply(f, a, s) => {
            let f = expr(f, &Ty::NoExpect, cx)?;
            let fty = f.ty();
            let arg_ty = peel_fun_param(&fty);
            let ret_ty = peel_fun_return(&fty);
            let a = expr(a, &arg_ty, cx)?;
            let resolved = lt::subst_from_arg(&arg_ty, &a.ty(), &ret_ty);
            let res = match resolved {
                Ty::Error | Ty::NoExpect => expected_or_recorded(want, cx, *s),
                other => other,
            };
            Ok(IrExpr::Apply(Box::new(f), Box::new(a), res, *s))
        }
        // **THE OPERATOR NAME DEPENDS ON THE OPERAND TYPE** -- `add-int`,
        // `add-num` and `add-vec` are three names for one source `+` -- so
        // this needs the operands typed first and refuses where it cannot
        // tell.
        // `lower-expr-at`'s `ABinaryExpr` arm lowers BOTH operands with the
        // binary's own expectation, and a builtin binary (`rem-int`) then
        // carries it -- `boolean` under an `==`.
        Expr::Binary(l, op, r, s) => {
            let l = expr(l, want, cx)?;
            let r = expr(r, want, cx)?;
            let lty = l.ty();
            // `lower-binary-maybe-eq` (IR/Lowering.codex:653): `==` and `/=`
            // ask `lower-eq-dispatch` FIRST, and only an operand type with no
            // generated helper falls through to the `binary eq` below.
            let (l, r) = match op {
                BinaryOp::OpEq | BinaryOp::OpNotEq => match eq_dispatch(&lty, l, r, cx, *s) {
                    Ok(call) if *op == BinaryOp::OpEq => return Ok(call),
                    // `/=` is `if call then False else True`, never a `not`.
                    Ok(call) => {
                        return Ok(IrExpr::If(
                            Box::new(call),
                            Box::new(IrExpr::BoolLit(false, *s)),
                            Box::new(IrExpr::BoolLit(true, *s)),
                            Ty::Boolean,
                            *s,
                        ))
                    }
                    Err(operands) => operands,
                },
                _ => (l, r),
            };
            // **THE RESULT IS THE LEFT OPERAND'S TYPE, AND TWO INTEGERS OF
            // DIFFERENT BOUNDS ARE COMPATIBLE.** `b + 1` over
            // `Integer between 0 and 255` answers `(int 0 255 ov-error)` and
            // `1 + b` answers `int-default` -- the rule is simply the LEFT.
            // Requiring the two to be EQUAL refused every arithmetic touching
            // a bounded declaration, which the depot writes constantly.
            // **THERE IS NO AGREEMENT CHECK, BECAUSE UPSTREAM HAS NONE.**
            // `binary-result-type` (IR/Lowering.codex:54225) reads the
            // operator, the LEFT type and the expectation, and never compares
            // the two sides. A check that the two agreed was here, and it
            // earned its keep while the operand types were the thing being
            // got right -- but it is not this layer's rule, and on the
            // self-host it refused two constructs that are simply not
            // symmetric: `a :: List a`, and a `for ... in` comprehension
            // appended to a concrete list, whose element type is a variable
            // upstream carries just as happily.
            //
            // What replaced it is a stronger gate, not a weaker one: the whole
            // 3.44 MB unit is now lowered and diffed against `codexir`, which
            // compares every node instead of the two at one operator.
            // **INTEGER IS THE DEFAULT, NOT A REFUSAL.** `lower-bin-op`
            // (IR/Lowering.codex:54201) tests vector, then the three Real
            // modes, then number, and ends `else IrMulInt` -- so an operand
            // type it cannot read still gets an operator. Refusing instead
            // sank `catmull-rom`, whose left operand lowers to `error`.
            //
            // The vector and Real-mode arms are not modelled here yet; when
            // they are, they go BEFORE the Real test, in upstream's order.
            // `lower-bin-op` (LoweringTypes.codex:206), on the left type with
            // its unit stripped: a vector, a saturating real, a trapping
            // real, an approximate real, a real, or an integer.
            let bty = strip_unit(&lty);
            let arith = |int: IrBinOp, num: IrBinOp, appr: IrBinOp, trap: IrBinOp, sat: IrBinOp, vec: IrBinOp| -> IrBinOp {
                use crate::check::{RealMode, RealWidth};
                match &bty {
                    Ty::Vector(..) => vec,
                    Ty::Real(_, RealMode::Saturating) => sat,
                    Ty::Real(_, RealMode::Trapping) => trap,
                    Ty::Real(RealWidth::F32, _) => appr,
                    Ty::Real(..) => num,
                    _ => int,
                }
            };
            let cmp = |scalar: IrBinOp, vec: IrBinOp| -> IrBinOp {
                if matches!(bty, Ty::Vector(..)) { vec } else { scalar }
            };
            let (name, ty) = match op {
                BinaryOp::OpAdd => (arith(IrBinOp::AddInt, IrBinOp::AddNum, IrBinOp::AddRealApprox, IrBinOp::AddRealTrapping, IrBinOp::AddRealSaturating, IrBinOp::AddVec), lty.clone()),
                BinaryOp::OpSub => (arith(IrBinOp::SubInt, IrBinOp::SubNum, IrBinOp::SubRealApprox, IrBinOp::SubRealTrapping, IrBinOp::SubRealSaturating, IrBinOp::SubVec), lty.clone()),
                BinaryOp::OpMul => (arith(IrBinOp::MulInt, IrBinOp::MulNum, IrBinOp::MulRealApprox, IrBinOp::MulRealTrapping, IrBinOp::MulRealSaturating, IrBinOp::MulVec), lty.clone()),
                BinaryOp::OpDiv => (arith(IrBinOp::DivInt, IrBinOp::DivNum, IrBinOp::DivRealApprox, IrBinOp::DivRealTrapping, IrBinOp::DivRealSaturating, IrBinOp::DivVec), lty.clone()),
                // NOT `arith`: upstream has no Real arm for `^`.
                BinaryOp::OpPow => (IrBinOp::PowInt, lty.clone()),
                BinaryOp::OpEq => (IrBinOp::Eq, Ty::Boolean),
                BinaryOp::OpNotEq => (IrBinOp::NotEq, Ty::Boolean),
                BinaryOp::OpLt => (cmp(IrBinOp::Lt, IrBinOp::LtVec), Ty::Boolean),
                BinaryOp::OpGt => (cmp(IrBinOp::Gt, IrBinOp::GtVec), Ty::Boolean),
                BinaryOp::OpLtEq => (cmp(IrBinOp::LtEq, IrBinOp::LtEqVec), Ty::Boolean),
                BinaryOp::OpGtEq => (cmp(IrBinOp::GtEq, IrBinOp::GtEqVec), Ty::Boolean),
                // **ONE TOKEN, THREE ATOMS.** `&` is `and` over Booleans,
                // `append-text` over Text and `append-list` over a List, and
                // the OPERAND type is what picks. `and` the keyword is only
                // ever logical.
                BinaryOp::OpAnd | BinaryOp::OpAppend => match &lty {
                    Ty::Boolean => (IrBinOp::And, Ty::Boolean),
                    Ty::Text => (IrBinOp::AppendText, lty.clone()),
                    Ty::List(_) => (IrBinOp::AppendList, lty.clone()),
                    other => return Err(format!("`&` on `{}`", render_ty(&cx.syms.borrow(), other))),
                },
                // `binary-result-type`: the EXPECTATION when it is a list,
                // and a list of the left operand otherwise.
                BinaryOp::OpCons => (
                    IrBinOp::ConsList,
                    match cx.st.deep_resolve(want) {
                        t @ Ty::List(_) => t,
                        _ => Ty::List(Box::new(lty.clone())),
                    },
                ),
                // `binary-result-type` groups these with the comparisons:
                // Boolean, or a vector mask over a vector.
                BinaryOp::OpApproxEq => (IrBinOp::ApproxEq, Ty::Boolean),
                BinaryOp::OpApproxEqExact => (IrBinOp::ApproxEqExact, Ty::Boolean),
                BinaryOp::OpBoolAnd => (IrBinOp::And, Ty::Boolean),
                BinaryOp::OpOr => (IrBinOp::Or, Ty::Boolean),
                other => return Err(format!("binary op {other:?}")),
            };
            Ok(IrExpr::Binary(name, Box::new(l), Box::new(r), ty, *s))
        }
        // **THE BRANCHES DO NOT HAVE TO AGREE, AND USUALLY DO NOT.** The
        // checker unified them; the wire did not.
        Expr::If(c, th, el, s) => {
            // `lower-expr-at c BooleanTy`: the condition's expectation is
            // Boolean, and a binary in it carries that on the wire.
            let c = expr(c, &Ty::Boolean, cx)?;
            let resolved = cx.st.deep_resolve(want);
            let t0 = expr(th, &resolved, cx)?;
            let tty = t0.ty();
            // The then-branch's type becomes the else-branch's expectation
            // only when nothing above had one to give.
            let hint = if lt::has_error(&resolved) { tty.clone() } else { resolved };
            let el = expr(el, &hint, cx)?;
            let ety = el.ty();
            let ty = lt::branch_recorded(&lt::merge(&hint, &ety), &lt::if_witness(&tty, &ety));
            // A then-branch lowered against an expectation that turned out to
            // be an error is lowered AGAIN, now that there is a real one.
            let th = if lt::has_error(&tty) && !lt::has_error(&ty) {
                expr(th, &ty, cx)?
            } else {
                t0
            };
            Ok(IrExpr::If(Box::new(c), Box::new(th), Box::new(el), ty, *s))
        }
        // `(list-expr (elems ...) ELEM)` -- the trailing type is the ELEMENT's,
        // checked against golds carrying text and nested-list elements rather
        // than assumed from the integer cases.
        Expr::List(xs, s) if xs.is_empty() => Ok(empty_list(want, cx, *s)),
        Expr::List(xs, s) => {
            // `lower-nonempty-list` (Lowering.codex:1376). The element type
            // comes from the EXPECTATION where there is one, and from the
            // first element only where there is not -- and every element is
            // then lowered AGAINST it. Ours lowered each with no expectation
            // and refused when they disagreed, which is neither the same
            // answer nor a stricter version of it.
            let from_context = match cx.st.deep_resolve(want) {
                Ty::List(e) => *e,
                _ => Ty::Error,
            };
            let elem = if lt::has_error(&from_context) {
                expr(&xs[0], &Ty::NoExpect, cx)?.ty()
            } else if !lt::has_typevars(&from_context) {
                from_context
            } else {
                // `list-elem-witnessed`: the first element may say what the
                // context's variable stands for, but only if it is a witness
                // worth having.
                let w = expr(&xs[0], &Ty::NoExpect, cx)?.ty();
                if lt::has_error(&w) || lt::admits_widening(&w) { from_context } else { w }
            };
            let mut parts = Vec::new();
            for x in xs {
                parts.push(expr(x, &elem, cx)?);
            }
            Ok(IrExpr::List(parts, elem, *s))
        }
        // `(let "n" TYPE VALUE BODY)`, nested one deep per binding, and the
        // let's own type is the BODY's -- a let evaluates to its body. The
        // bound values get no expectation; the body inherits the let's.
        Expr::Let(binds, body, s) => {
            // **THE BINDINGS ARE SEQUENTIAL.** `lower-let-rest` binds each one
            // before lowering the next, so the second value sees the first --
            // and each name is `bind-local`'d, which is where a shadowing
            // `let __seq` becomes `__seq_1`.
            let mark = cx.mark();
            let mut heads = Vec::new();
            for b in binds {
                let v = expr(&b.value, &Ty::NoExpect, cx)?;
                let ty = cx.st.deep_resolve(&v.ty());
                let emitted = cx.bind_local(b.name, ty.clone());
                heads.push((emitted, ty, v));
            }
            let mut out = expr(body, want, cx)?;
            cx.release(mark);
            for (n, ty, v) in heads.into_iter().rev() {
                out = IrExpr::Let(n, ty, Box::new(v), Box::new(out), *s);
            }
            Ok(out)
        }
        // `(act (stmts S...) TYPE)`, and the block's type is the type of what
        // it ENDS with -- an act evaluates to its last statement, the same way
        // a let evaluates to its body. Upstream's row arithmetic decides what
        // the EFFECT of the block is; this is the value side.
        Expr::Act(stmts, s) => {
            let mark = cx.mark();
            let parts = act_stmts(stmts, 0, want, cx)?;
            cx.release(mark);
            let ty = act_block_type(&parts, want);
            Ok(IrExpr::Act(parts, ty, *s))
        }
        // `lower-handle` (subject). **THE HANDLE'S TYPE IS THE EXPECTATION,
        // falling back to the body's** -- `chain-ret-or` -- because a handler
        // discharges an effect without changing the value the body computes.
        Expr::Handle(h) => {
            let body = expr(&h.body, want, cx)?;
            let ty = match want {
                Ty::Error | Ty::NoExpect => body.ty(),
                other => other.clone(),
            };
            let mut cs = Vec::new();
            for c in &h.clauses {
                let b = expr(&c.body, want, cx)?;
                cs.push(crate::ir_chapter::IrHandleClause {
                    op_name: cx.text(c.op_name),
                    params: c.params.clone(),
                    resume_name: c.resume_name,
                    body: wrap_clause_body(&c.params, b, c.span),
                    span: c.span,
                });
            }
            Ok(IrExpr::Handle(cx.text(h.effect), Box::new(body), cs, ty, h.span))
        }
        // `(with-timeout SECS (effs ..) (scopes ..) BODY TYPE)`. The scopes
        // list is always empty today, as it is in the AST.
        Expr::WithTimeout(w) => {
            let body = expr(&w.body, want, cx)?;
            let ty = match want {
                Ty::Error | Ty::NoExpect => body.ty(),
                other => other.clone(),
            };
            Ok(IrExpr::WithTimeout(
                w.timeout.parse().unwrap_or(0),
                w.effects.iter().map(|e| cx.text(*e)).collect(),
                w.labels.clone(),
                Box::new(body),
                ty,
                w.span,
            ))
        }
        // **THE TRY'S TYPE COMES FROM ITS BODY BLOCK**, not from the fallback
        // or the failure arm: `act-block-type body-ir ty`, the same rule an
        // ordinary act block follows.
        Expr::Try(t) => {
            let body = act_stmts(&t.body, 0, want, cx)?;
            let fb = act_stmts(&t.fallback, 0, want, cx)?;
            let fail = act_stmts(&t.failure, 0, want, cx)?;
            let ty = act_block_type(&body, want);
            Ok(IrExpr::Try(t.count, body, fb, fail, ty, t.span))
        }
        Expr::Record(n, fields, s) => {
            // The checker's recorded answer first -- it is the better one, and
            // it is what makes this arm short. But `record-expr-type` SKIPS A
            // SYNTHETIC SPAN, so a record the desugarer built has none, and
            // refusing there took six type-class chapters with it.
            //
            // `lower-record` (subject) never reads a span: it looks the
            // constructor up and strips its arrows, and falls back to the
            // expectation. That is the fallback, not a refusal.
            let ty = cx
                .at(*s)
                .or_else(|| cx.bindings.get(n).map(strip_fun_args))
                .unwrap_or_else(|| want.clone());
            let mut fs = Vec::new();
            for f in fields {
                fs.push(IrFieldVal { name: f.name, value: expr(&f.value, &Ty::NoExpect, cx)? });
            }
            Ok(IrExpr::Record(*n, fs, ty, *s))
        }
        // `(field-access OBJ "py/1" TYPE)` -- the field's name AND its slot in
        // the declaration. The checker records no type here, so both the type
        // and the slot are read back out of the type declarations.
        Expr::FieldAccess(r, f, s) => {
            let r = expr(r, &Ty::NoExpect, cx)?;
            // `deep-resolve` then strip the wrappers that are not part of the
            // shape (subject 54312-54317): an effect row, a `forall`, and the
            // linear marker all sit OVER a record without changing whether it
            // is one.
            let rty = strip_receiver(&cx.st.deep_resolve(&r.ty()), cx);
            // **LOWERING NEVER REFUSES A FIELD ACCESS.** Upstream answers the
            // EXPECTATION twice over -- `is otherwise -> ty` at 54334 and
            // again at 54339 -- and spells the field bare, because
            // `ir-resolve-field-index` answers -1 for a non-record receiver
            // and `ir-field-with-index` then omits the `/N`. A receiver whose
            // type did not resolve is the checker's diagnostic to raise
            // (CDX2005, CDX2095); refusing here loses the whole chapter and
            // says nothing the checker did not already know.
            let Some(name) = record_sym(&rty) else {
                return Ok(IrExpr::FieldAccess(
                    Box::new(r),
                    cx.text(*f),
                    want.clone(),
                    *s,
                ));
            };
            let (Some(fty), Some(slot)) = (cx.tds.field(name, *f), cx.tds.field_index(name, *f))
            else {
                return Ok(IrExpr::FieldAccess(
                    Box::new(r),
                    cx.text(*f),
                    want.clone(),
                    *s,
                ));
            };
            // **A CONSTRUCTED RECEIVER INSTANTIATES THE FIELD HERE TOO.** The
            // declared type says `List a` and the receiver says which `a`;
            // taking the declaration alone left `qsort-by`'s recursive call
            // reading `(list (tycon "a"))`.
            let fty = match &rty {
                Ty::Constructed(_, cargs) if !cargs.is_empty() => cx
                    .bindings
                    .get(&name)
                    .and_then(|c| crate::check::instantiate_field(c, slot, cargs))
                    .unwrap_or_else(|| fty.clone()),
                _ => fty.clone(),
            };
            let fty = cx.st.deep_resolve(&fty);
            // `instantiate-receiver-ty` + `set-ir-expr-type` (subject 54331).
            // **THE NODE UNDER A FIELD ACCESS IS RETYPED TO THE RECORD**, with
            // the constructed type's own arguments carried onto it. A receiver
            // that already IS a record is left alone.
            let r = match &rty {
                Ty::Constructed(n, cargs)
                    if matches!(cx.tds.declared().get(n),
                                Some(Ty::Record(_, ra)) if ra.len() == cargs.len()) =>
                {
                    r.with_ty(Ty::Record(*n, cargs.clone()))
                }
                _ => r,
            };
            Ok(IrExpr::FieldAccess(
                Box::new(r),
                format!("{}/{}", cx.text(*f), slot),
                fty,
                *s,
            ))
        }
        // **THE TYPE IS THE RECORD'S, NOT THE FIELD'S** -- `AFieldAssignExpr`
        // builds `IrFieldStore rec-ir (field.value) val-ir rec-ty s`, so a
        // store evaluates to the record it wrote into. That is what makes the
        // `let __seq` the desugarer wraps it in sequenceable.
        Expr::FieldAssign(r, f, v, s) => {
            let r = expr(r, &Ty::NoExpect, cx)?;
            let rty = r.ty();
            let name = record_name(&rty, cx, "field store into")?;
            let Some(slot) = cx.tds.field_index(name, *f) else {
                return Err(format!(
                    "`{}` has no field `{}` here",
                    cx.text(name),
                    cx.text(*f)
                ));
            };
            let v = expr(v, &Ty::NoExpect, cx)?;
            Ok(IrExpr::FieldStore(
                Box::new(r),
                format!("{}/{}", cx.text(*f), slot),
                Box::new(v),
                rty,
                *s,
            ))
        }
        // `(match SC (branches (branch PAT BODY GUARD) ...) TYPE)`. Every arm
        // carries a guard -- an unguarded one carries `(bool-lit true)`, which
        // the desugarer put there.
        Expr::Match(scrut, arms, s) => {
            let sc = expr(scrut, &Ty::NoExpect, cx)?;
            // **THE PATTERN BINDS BEFORE THE PATTERN LOWERS.**
            // `bind-pattern-to-ctx` runs first and the arm's pattern, body and
            // guard all see it -- which is how a pattern variable that shadows
            // (`is IrTry (max) ...`, over the builtin `max`) gets re-spelled
            // consistently in the pattern and in the body that reads it. Each
            // arm starts from the OUTER scope, not the previous arm's.
            let mut branches = Vec::new();
            for a in arms {
                let mark = cx.mark();
                bind_pattern(&a.pattern, cx)?;
                let pat = pattern(&a.pattern, cx)?;
                let body = expr(&a.body, want, cx)?;
                let guard = expr(&a.guard, &Ty::Boolean, cx)?;
                cx.release(mark);
                branches.push(IrBranch { pattern: pat, body, guard, span: a.span });
            }
            if branches.is_empty() {
                return Err("a match with no arms".into());
            }
            // With an expectation, the match IS that -- taught whatever its
            // type variables by the first arm that can speak. Without one,
            // `infer-match-type` takes the first arm body that has an answer
            // at all, which is a WEAKER test: a bounded integer is no witness
            // but it is an answer.
            let bodies: Vec<Ty> = branches.iter().map(|b| b.body.ty()).collect();
            let ty = if lt::has_error(want) {
                bodies.iter().find(|b| !lt::has_error(b)).cloned().unwrap_or(Ty::Error)
            } else {
                lt::branch_recorded(want, &lt::match_witness(bodies.iter()))
            };
            Ok(IrExpr::Match(Box::new(sc), branches, ty, *s))
        }
        // A lambda is lowered as a lambda and LIFTED afterwards, which is
        // upstream's order and not an accident of convenience: lifting numbers
        // `__lam_N` over a finished tree, and a lowering that lifted as it went
        // would have to be idempotent to survive the `if` arm above lowering a
        // branch twice.
        Expr::Lambda(ps, body, s) => {
            let mut params: Vec<Sym> = ps.clone();
            let mut inner: &Expr = body;
            while let Expr::Lambda(ips, ib, _) = inner {
                params.extend(ips.iter().copied());
                inner = ib;
            }
            // `expected-or-recorded-ty`: what the context wants, and only
            // where it wants nothing does the recorded type answer.
            //
            // **THE PARAMETERS PEEL OFF THE STRIPPED TYPE AND THE NODE KEEPS
            // THE UNSTRIPPED ONE.** A polymorphic callee's parameter arrives
            // still inside its `forall`, and peeling that as if it were an
            // arrow answers `error` for every slot.
            let expected = expected_or_recorded(want, cx, *s);
            let stripped = crate::check::strip_forall(&expected);
            // **`peel-fun-param` ANSWERS `ErrorTy` FOR ANYTHING THAT IS NOT AN
            // ARROW**, and `get-lambda-return` does the same
            // (IR/Lowering.codex:55108). Upstream says why in its own prose:
            // "when nothing above expects a type there is nothing to peel ...
            // and the arrow is recorded with a failure atom in each position".
            //
            // So a lambda whose expectation and recorded type are both absent
            // still lowers, with `error` in every parameter slot. Refusing
            // instead is a different rule, and the one that stopped a
            // `for r in temps -> r` -- whose lambda the desugarer gives a
            // synthetic span, so nothing recorded a type for it.
            // `bind-lambda-to-ctx` binds each parameter for the body, and
            // `lower-lambda-params` names them `bound-name` -- so a lambda
            // parameter that shadows is re-spelled like any other binder.
            let mark = cx.mark();
            let mut ret = stripped;
            let mut ir_params = Vec::new();
            for p in &params {
                let pt = peel_fun_param(&ret);
                let emitted = cx.bind_local(*p, pt.clone());
                ir_params.push(IrParam { name: emitted, ty: pt, span: *s });
                ret = peel_fun_return(&ret);
            }
            let b = expr(inner, &ret, cx)?;
            cx.release(mark);
            let lam_ty = lambda_recorded(&ret, &b.ty(), &expected);
            Ok(IrExpr::Lambda(ir_params, Box::new(b), lam_ty, *s))
        }
        // **A PROOF IS ERASED TO `0`.** `lower-expr-at`'s own arm
        // (IR/Lowering.codex:54365) is
        // `is AInductionExpr (scrut) (arms) (s) -> deck-record (IrIntLit 0 s)`
        // -- an induction term carries no runtime value, so nothing of it
        // reaches the wire and the arms are not walked at all.
        Expr::Induction(_, _, s) => Ok(IrExpr::IntLit(0, *s)),
        other => Err(node_kind(other).to_string()),
    }
}

/// `lower-eq-dispatch` (IR/Lowering.codex:664). **AN EQUALITY ON A TYPE THE
/// DESUGARER GENERATED `__eq_<T>` FOR IS A CALL TO IT**, not a `binary eq`.
/// The desugarer mints one helper per type NAME; this arm reads its
/// EXISTENCE -- overlay first, then the checker's bindings, exactly
/// `lookup-type-split` -- and finding it is the whole proof that the operand
/// is such a type. Without this arm every generated helper is dead on
/// arrival: the definition is emitted, nothing names it, and pruning takes it
/// off the wire. The self-host oracle names `__eq_TokenKind` sixteen times.
///
/// A type WITH ARGUMENTS is called by an INSTANTIATED name, `__eq_Box@Integer`,
/// spelled by `eq-helper-name-inst` from the site's actuals, and its type is
/// built from the operand rather than read off the helper, whose own field
/// stays at the declaration's type variable. `codexir` puts that name on the
/// wire and attaches NO definition for it; matching the wire is the job here.
///
/// `eq-site-actuals` reads actuals off a `ConstructedTy` ONLY: a `SumTy` with
/// arguments still has them, so `has-args` is true and the type is the
/// operand's, but the name is the bare one.
///
/// The answer is `Err` with the operands handed back when there is no helper,
/// so the caller can still build the `binary` from them.
fn eq_dispatch(
    lty: &Ty,
    l: IrExpr,
    r: IrExpr,
    cx: &Lower,
    s: crate::ast::Span,
) -> Result<IrExpr, (IrExpr, IrExpr)> {
    let resolved = cx.st.deep_resolve(lty);
    let tn = type_name_of(&resolved, cx);
    if tn.is_empty() {
        return Err((l, r));
    }
    let bare = format!("__eq_{tn}");
    // `lookup-type-split` answers `ErrorTy` for a name it does not hold, and
    // the arm reads `ErrorTy | NoExpectTy` as "no helper".
    let probe = cx
        .syms
        .borrow()
        .find(&bare)
        .and_then(|n| cx.overlay_ty(n).or_else(|| cx.bindings.get(&n).cloned()))
        .filter(|t| !matches!(t, Ty::Error | Ty::NoExpect));
    let Some(probe) = probe else {
        return Err((l, r));
    };
    let stripped = strip_unit(&resolved);
    let (hname, fty) = if eq_type_has_args(&stripped) {
        let arrow = |ret: Ty| {
            Ty::Fun(Box::new(stripped.clone()), crate::check::EffectRow::default(), Box::new(ret))
        };
        (eq_helper_name_inst(&tn, &eq_site_actuals(&stripped), cx), arrow(arrow(Ty::Boolean)))
    } else {
        (bare, crate::check::strip_forall(&cx.st.deep_resolve(&probe)))
    };
    let hsym = cx.syms.borrow_mut().intern(&hname);
    let inner = IrExpr::Apply(
        Box::new(IrExpr::Name(hsym, fty.clone(), s)),
        Box::new(l),
        peel_fun_return(&fty),
        s,
    );
    Ok(IrExpr::Apply(Box::new(inner), Box::new(r), Ty::Boolean, s))
}

/// `type-name-of` (IR/Lowering.codex:695): the bare name, arguments DISCARDED,
/// and `""` for anything without one -- a unit type included, so `==` on a
/// unit type never reaches its own generated helper.
/// `int-rem` or `compare` applied to its first argument, when the callee
/// is that name applied once.
fn special_apply_name(f: &Expr, cx: &Lower) -> Option<(&'static str, Expr)> {
    let Expr::Apply(inner, a1, _) = f else { return None };
    let Expr::NameRef(n, _) = &**inner else { return None };
    let which = match cx.syms.borrow().text(*n) {
        "int-rem" => "int-rem",
        "compare" => "compare",
        _ => return None,
    };
    Some((which, (**a1).clone()))
}

/// `is-primitive-type-name`.
fn is_primitive_type_name(n: &str) -> bool {
    matches!(n, "Integer" | "Real" | "Text" | "Boolean" | "Char" | "Nothing" | "List")
}

/// `lower-compare-prim`: `text-compare` on Text, and `gen-int-compare` --
/// two lets and two ifs answering -1, 1 or 0 -- on anything else.
fn lower_compare_prim(lt: &Ty, l: IrExpr, r: IrExpr, cx: &Lower, sp: crate::ast::Span) -> IrExpr {
    let int_default = Ty::Integer(i64::MIN, i64::MAX, crate::check::Overflow::Error);
    if matches!(lt, Ty::Text) {
        let tc = cx.syms.borrow_mut().intern("text-compare");
        let fty = Ty::Fun(
            Box::new(Ty::Text),
            crate::check::EffectRow::default(),
            Box::new(Ty::Fun(Box::new(Ty::Text), crate::check::EffectRow::default(), Box::new(int_default.clone()))),
        );
        let inner = IrExpr::Apply(Box::new(IrExpr::Name(tc, fty.clone(), sp)), Box::new(l), peel_fun_return(&fty), sp);
        return IrExpr::Apply(Box::new(inner), Box::new(r), int_default, sp);
    }
    let (na, nb) = {
        let mut syms = cx.syms.borrow_mut();
        (syms.intern("__cmpa"), syms.intern("__cmpb"))
    };
    let name = |n| IrExpr::Name(n, int_default.clone(), sp);
    let lit = |v| IrExpr::IntLit(v, sp);
    let cmp = |op| IrExpr::Binary(op, Box::new(name(na)), Box::new(name(nb)), Ty::Boolean, sp);
    let inner_if = IrExpr::If(Box::new(cmp(IrBinOp::Gt)), Box::new(lit(1)), Box::new(lit(0)), int_default.clone(), sp);
    let outer_if = IrExpr::If(Box::new(cmp(IrBinOp::Lt)), Box::new(lit(-1)), Box::new(inner_if), int_default.clone(), sp);
    IrExpr::Let(
        na,
        int_default.clone(),
        Box::new(l),
        Box::new(IrExpr::Let(nb, int_default.clone(), Box::new(r), Box::new(outer_if), sp)),
        sp,
    )
}

fn type_name_of(t: &Ty, cx: &Lower) -> String {
    match t {
        Ty::Integer(..) => "Integer".into(),
        Ty::Real(..) => "Real".into(),
        Ty::Text => "Text".into(),
        Ty::Boolean => "Boolean".into(),
        Ty::Char => "Char".into(),
        Ty::Nothing => "Nothing".into(),
        Ty::List(_) | Ty::LinkedList(_) => "List".into(),
        Ty::Constructed(n, _) | Ty::Record(n, _) | Ty::Sum(n, _) => cx.text(*n),
        _ => String::new(),
    }
}

/// `strip-unit-ty` (Types/CodexType.codex:133).
fn strip_unit(t: &Ty) -> Ty {
    match t {
        Ty::Unit(_, inner) => strip_unit(inner),
        other => other.clone(),
    }
}

/// `eq-type-has-args` (IR/Lowering.codex:684).
fn eq_type_has_args(t: &Ty) -> bool {
    match t {
        Ty::Constructed(_, a) | Ty::Sum(_, a) | Ty::Record(_, a) => !a.is_empty(),
        _ => false,
    }
}

/// `eq-site-actuals` (Emit/X86_64.codex:2954): a `ConstructedTy`'s arguments
/// and nothing else's.
fn eq_site_actuals(t: &Ty) -> Vec<Ty> {
    match t {
        Ty::Constructed(_, a) => a.clone(),
        _ => Vec::new(),
    }
}

/// `eq-helper-name-inst` (Emit/X86_64.codex:2949): `__eq_<T>` with no
/// actuals, else `__eq_<T>@` and the actuals' keys joined by `,`.
fn eq_helper_name_inst(tn: &str, actuals: &[Ty], cx: &Lower) -> String {
    if actuals.is_empty() {
        return format!("__eq_{tn}");
    }
    let keys: Vec<String> = actuals.iter().map(|a| eq_key_of(a, cx)).collect();
    format!("__eq_{tn}@{}", keys.join(","))
}

/// `eq-key-of` (Emit/X86_64.codex:2918): the instance key of one actual.
/// Integers of every bound share one key; a Real's is its WIDTH; a type
/// variable is `#` and its id; anything else is `?`.
fn eq_key_of(t: &Ty, cx: &Lower) -> String {
    let wrap = |a: &[Ty]| -> String {
        if a.is_empty() {
            String::new()
        } else {
            let keys: Vec<String> = a.iter().map(|x| eq_key_of(x, cx)).collect();
            format!("[{}]", keys.join(","))
        }
    };
    match strip_unit(t) {
        Ty::Text => "Text".into(),
        Ty::Boolean => "Boolean".into(),
        Ty::Char => "Char".into(),
        Ty::Integer(..) => "Integer".into(),
        Ty::Real(w, _) => match w {
            crate::check::RealWidth::F32 => "Real32".into(),
            crate::check::RealWidth::F64 => "Real64".into(),
        },
        Ty::List(e) => format!("List[{}]", eq_key_of(&e, cx)),
        Ty::LinkedList(e) => format!("LinkedList[{}]", eq_key_of(&e, cx)),
        Ty::Sum(n, a) | Ty::Record(n, a) | Ty::Constructed(n, a) => {
            format!("{}{}", cx.text(n), wrap(&a))
        }
        Ty::Var(id) => format!("#{id}"),
        _ => "?".into(),
    }
}

/// `peel-fun-param` (Types/CodexTypeHelpers.codex:4). The argument side of an
/// arrow, LOOKING THROUGH quantifiers, and `ErrorTy` for anything else.
fn peel_fun_param(t: &Ty) -> Ty {
    match t {
        Ty::Fun(p, _, _) => (**p).clone(),
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => peel_fun_param(b),
        _ => Ty::Error,
    }
}

/// `peel-fun-return` (Types/CodexTypeHelpers.codex:12).
fn peel_fun_return(t: &Ty) -> Ty {
    match t {
        Ty::Fun(_, _, r) => (**r).clone(),
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => peel_fun_return(b),
        _ => Ty::Error,
    }
}

/// `lower-act-stmts-acc` (subject 55787), from `i` to the end.
///
/// **EVERY STATEMENT IS HANDED THE BLOCK'S OWN EXPECTATION.** That reads
/// oddly and is what upstream passes down.
///
/// **A `let` STATEMENT SWALLOWS THE REST OF THE BLOCK.** It is not one
/// statement among several: the binding has to be in scope for what follows,
/// so the remaining statements become an `act` inside the let's body. Leaving
/// them as siblings puts the same expressions in the same order and gives the
/// binding nowhere to live.
fn act_stmts(
    stmts: &[crate::ast::ActStmt],
    from: usize,
    want: &Ty,
    cx: &Lower,
) -> Result<Vec<IrActStmt>, String> {
    let mut parts = Vec::new();
    for (k, st) in stmts.iter().enumerate().skip(from) {
        match st {
            crate::ast::ActStmt::Exec(Expr::Let(binds, body, ls), sp2) => {
                parts.push(IrActStmt::Exec(
                    act_let(binds, 0, body, stmts, k, want, cx, *ls)?,
                    *sp2,
                ));
                return Ok(parts);
            }
            crate::ast::ActStmt::Exec(e, sp2) => {
                parts.push(IrActStmt::Exec(expr(e, want, cx)?, *sp2));
            }
            // A `<-` binds for the rest of the block, and the type it binds is
            // what is INSIDE the effect.
            crate::ast::ActStmt::Bind(n, e, sp2) => {
                let x = expr(e, want, cx)?;
                let vt = peel_effectful(&x.ty());
                let emitted = cx.bind_local(*n, vt.clone());
                parts.push(IrActStmt::Bind(emitted, vt, x, *sp2));
            }
        }
    }
    Ok(parts)
}

/// `lower-act-let` (subject 55821): the let, then the rest of the block as an
/// `act` inside it -- or just the let's own body where nothing follows.
fn act_let(
    binds: &[crate::ast::LetBind],
    j: usize,
    body: &Expr,
    stmts: &[crate::ast::ActStmt],
    i: usize,
    want: &Ty,
    cx: &Lower,
    sp: crate::ast::Span,
) -> Result<IrExpr, String> {
    let Some(b) = binds.get(j) else {
        // A let whose body is another let keeps going: the whole chain binds
        // before the block's remainder is reached.
        if let Expr::Let(binds2, body2, ls2) = body {
            return act_let(binds2, 0, body2, stmts, i, want, cx, *ls2);
        }
        let body_ir = expr(body, want, cx)?;
        let rest = act_stmts(stmts, i + 1, want, cx)?;
        if rest.is_empty() {
            return Ok(body_ir);
        }
        let bsp = body_ir.span();
        let bty = body_ir.ty();
        let mut inner = vec![IrActStmt::Exec(body_ir, bsp)];
        inner.extend(rest);
        let ty = act_block_type(&inner, &bty);
        return Ok(IrExpr::Act(inner, ty, sp));
    };
    let v = expr(&b.value, &Ty::NoExpect, cx)?;
    let ty = cx.st.deep_resolve(&v.ty());
    let emitted = cx.bind_local(b.name, ty.clone());
    Ok(IrExpr::Let(
        emitted,
        ty,
        Box::new(v),
        Box::new(act_let(binds, j + 1, body, stmts, i, want, cx, sp)?),
        sp,
    ))
}

/// `act-block-type` (subject 55775): what the block ENDS with.
fn act_block_type(stmts: &[IrActStmt], fallback: &Ty) -> Ty {
    match stmts.last() {
        Some(IrActStmt::Exec(e, _)) => e.ty(),
        Some(IrActStmt::Bind(_, t, _, _)) => t.clone(),
        None => fallback.clone(),
    }
}

/// `peel-effectful-ty` (subject 54578). What a `[Console] Nothing` computes.
fn peel_effectful(t: &Ty) -> Ty {
    match t {
        Ty::Effectful(_, _, inner) => peel_effectful(inner),
        other => other.clone(),
    }
}

/// `expected-or-recorded-ty` (Lowering.codex:748). The context's expectation,
/// and only where there is none does the checker's own answer at this span
/// stand in.
///
/// The test is on the type ITSELF being the sentinel, not on
/// `ty-has-error` -- a `List <error>` is an expectation upstream keeps.
fn expected_or_recorded(ty: &Ty, cx: &Lower, sp: crate::ast::Span) -> Ty {
    match ty {
        Ty::Error | Ty::NoExpect => cx.recorded(sp),
        other => other.clone(),
    }
}

/// `lambda-recorded-ty` (Lowering.codex:767).
///
/// A lambda records the type it was HANDED, which at a polymorphic call still
/// carries the callee's variables. Where the body came out concrete, those
/// variables are the ones the body just answered: `\t -> copy-sx-text b t`
/// handed `(fn (tvar 39) (tvar 40))` records `(fn (tvar 39) text)`, and the
/// call site's `subst-type-vars-from-arg` can then learn something from it.
fn lambda_recorded(declared_ret: &Ty, body_ty: &Ty, ty: &Ty) -> Ty {
    if !lt::has_typevars(ty) || lt::has_typevars(body_ty) {
        return ty.clone();
    }
    lt::subst_from_arg(declared_ret, body_ty, ty)
}

/// `lower-empty-list` (Lowering.codex:1359). **`[]` IS NOT ALWAYS A LIST.**
///
/// Its type is the bare variable the checker minted, so what it stands for is
/// whatever the context taught it. A `LinkedList` there is not a list literal
/// at all -- upstream emits a CALL to the `__linked-list-empty` builtin,
/// applied to a zero, and only a `ListTy` reaches the wire as `(list-expr
/// (elems) T)`. A third answer, neither of those, is an empty list of
/// `ErrorTy` rather than a refusal.
fn empty_list(want: &Ty, cx: &Lower, s: crate::ast::Span) -> IrExpr {
    // `empty-list-element-source`: the expectation when it already names a
    // container, and otherwise whatever the checker recorded at this span.
    let resolved = match cx.st.deep_resolve(want) {
        t @ (Ty::List(_) | Ty::LinkedList(_)) => t,
        _ => cx.recorded(s),
    };
    match resolved {
        Ty::LinkedList(e) => {
            let ll = Ty::LinkedList(e);
            let fun = Ty::Fun(
                Box::new(Ty::Integer(i64::MIN, i64::MAX, crate::check::Overflow::Error)),
                crate::check::EffectRow::default(),
                Box::new(ll.clone()),
            );
            IrExpr::Apply(
                Box::new(IrExpr::Name(cx.ll_empty, fun, s)),
                Box::new(IrExpr::IntLit(0, s)),
                ll,
                s,
            )
        }
        Ty::List(e) => IrExpr::List(Vec::new(), *e, s),
        _ => IrExpr::List(Vec::new(), Ty::Error, s),
    }
}

/// `wrap-clause-body-in-lambda` (subject). **A CLAUSE WITH PARAMETERS IS A
/// LAMBDA OVER THEM, and its parameters are spelled TWICE** -- once in the
/// clause's own `(params ...)` and once in the lambda the body becomes. That
/// is upstream's shape, not a redundancy we introduced. A clause with no
/// parameters is not wrapped at all.
///
/// Every parameter is typed `int-default`, which is upstream's placeholder
/// here and not an inference: the clause's real parameter types live in the
/// effect declaration.
fn wrap_clause_body(params: &[Sym], body: IrExpr, sp: crate::ast::Span) -> IrExpr {
    if params.is_empty() {
        return body;
    }
    let int = Ty::Integer(i64::MIN, i64::MAX, crate::check::Overflow::Error);
    let ty = params.iter().fold(body.ty(), |acc, _| {
        Ty::Fun(Box::new(int.clone()), crate::check::EffectRow::default(), Box::new(acc))
    });
    let ps = params.iter().map(|p| crate::ir_chapter::IrParam { name: *p, ty: int.clone(), span: sp }).collect();
    IrExpr::Lambda(ps, Box::new(body), ty, sp)
}

/// `strip-fun-args`: the type a constructor arrow ANSWERS, which for a record
/// constructor is the record.
fn strip_fun_args(t: &Ty) -> Ty {
    match t {
        Ty::Fun(_, _, r) => strip_fun_args(r),
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => strip_fun_args(b),
        other => other.clone(),
    }
}

/// `stripped-rec-ty` (subject 54313): the wrappers a receiver may wear that do
/// not change whether it is a record.
fn strip_receiver(t: &Ty, cx: &Lower) -> Ty {
    match t {
        Ty::Effectful(_, _, ret) => cx.st.deep_resolve(ret),
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => cx.st.deep_resolve(b),
        Ty::Linear(inner) => cx.st.deep_resolve(inner),
        other => other.clone(),
    }
}

/// The record or constructed type's name, if it is one.
fn record_sym(t: &Ty) -> Option<Sym> {
    match t {
        Ty::Record(n, _) | Ty::Constructed(n, _) => Some(*n),
        _ => None,
    }
}

/// The record or constructed type's name, or the reason this is neither.
fn record_name(t: &Ty, cx: &Lower, what: &str) -> Result<Sym, String> {
    match t {
        Ty::Record(n, _) | Ty::Constructed(n, _) => Ok(*n),
        other => Err(format!("{what} `{}`, which is not a record", render_ty(&cx.syms.borrow(), other))),
    }
}

/// One pattern. **THE TYPE ON A PATTERN NODE IS THE CHECKER'S ANSWER FOR
/// THAT NODE**, read by span, for every pattern including the ones the
/// desugarer invented. Upstream's `lower-pattern` rebuilds it instead -- the
/// scrutinee's type for the top pattern, `ctor-field-type-in-ctx` for a
/// sub-pattern -- because its checker keeps no answer a pattern can be
/// looked up by. Ours does (`check::bind_pattern` records one per node), so
/// rebuilding would be a second derivation of a fact already in hand, and it
/// went wrong the one time it was tried here: the reconstruction was written
/// to cover invented patterns, which had no answer only because they shared
/// one span. A pattern with no answer is a refusal, not a fallback.
fn pattern(p: &Pat, cx: &Lower) -> Result<IrPat, String> {
    match p {
        Pat::Wild(s) => Ok(IrPat::Wild(*s)),
        Pat::Var(n, s) => Ok(IrPat::Var(cx.bound_name(*n), pat_ty(*s, cx)?, *s)),
        Pat::Lit(v, _, s) => Ok(IrPat::Lit(v.clone(), pat_ty(*s, cx)?, *s)),
        Pat::Ctor(n, subs, s) => {
            let mut out = Vec::new();
            for sub in subs {
                out.push(pattern(sub, cx)?);
            }
            Ok(IrPat::Ctor(*n, out, pat_ty(*s, cx)?, *s))
        }
        Pat::Vec_(..) => Err("vector pattern".into()),
    }
}

/// The checker's answer for a pattern node, resolved. A HALF-resolved type
/// reaches the wire as `(tvar 4)` where the oracle spells `int-default`.
fn pat_ty(sp: crate::ast::Span, cx: &Lower) -> Result<Ty, String> {
    match cx.st.pat_type_at(sp) {
        Some(t) => Ok(cx.st.deep_resolve(t)),
        None => Err(format!("no checker answer for the pattern at {}:{}", sp.line, sp.col)),
    }
}

/// `bind-pattern-to-ctx` (subject 55367). Every variable a pattern binds,
/// into the arm's scope, before anything in the arm is lowered, with the
/// type `pattern` will put on the node.
fn bind_pattern(p: &Pat, cx: &Lower) -> Result<(), String> {
    match p {
        Pat::Var(n, s) => {
            cx.bind_local(*n, pat_ty(*s, cx)?);
        }
        Pat::Ctor(_, subs, _) | Pat::Vec_(subs, _) => {
            for sub in subs {
                bind_pattern(sub, cx)?;
            }
        }
        Pat::Wild(_) | Pat::Lit(..) => {}
    }
    Ok(())
}

/// The variant's name, for the refusal histogram.
fn node_kind(e: &Expr) -> &'static str {
    match e {
        Expr::Lit(..) => "Lit",
        Expr::NameRef(..) => "NameRef",
        Expr::Apply(..) => "Apply",
        Expr::Binary(..) => "Binary",
        Expr::Unary(..) => "Unary",
        Expr::If(..) => "If",
        Expr::Let(..) => "Let",
        Expr::Lambda(..) => "Lambda",
        Expr::Match(..) => "Match",
        Expr::List(..) => "List",
        Expr::Record(..) => "Record",
        Expr::FieldAccess(..) => "FieldAccess",
        Expr::Act(..) => "Act",
        Expr::Handle(..) => "Handle",
        Expr::WithTimeout(..) => "WithTimeout",
        Expr::Try(..) => "Try",
        Expr::FieldAssign(..) => "FieldAssign",
        Expr::Lazy(..) => "Lazy",
        Expr::Error(..) => "Error",
        Expr::Induction(..) => "Induction",
    }
}
