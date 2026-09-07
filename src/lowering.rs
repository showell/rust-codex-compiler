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

use crate::ast::{BinaryOp, Chapter, Expr, LiteralKind, Pat};
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
    pub syms: &'a SymTab,
    st: &'a UnifyState,
    /// The chapter's type declarations. Lowering asks them two things the
    /// checker did not record: a field's TYPE and its SLOT, which the wire
    /// spells as `"py/1"`.
    tds: &'a TypeDefs,
    bindings: BTreeMap<Sym, Ty>,
}

impl<'a> Lower<'a> {
    pub fn new(
        ch: &'a Chapter,
        bindings: &[Binding],
        st: &'a UnifyState,
        tds: &'a TypeDefs,
    ) -> Lower<'a> {
        Lower {
            syms: &ch.syms,
            st,
            tds,
            bindings: bindings.iter().map(|b| (b.name, b.ty.clone())).collect(),
        }
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
        None => return Err(format!("`{}` was never bound by the checker", cx.syms.text(name))),
    };
    let mut own: Vec<Sym> = d.params.iter().map(|p| p.name).collect();
    let mut body_expr: &Expr = &d.body;
    while let Expr::Lambda(ps, inner, _) = body_expr {
        own.extend(ps.iter().copied());
        body_expr = inner;
    }
    // Parameter types come from walking the bound arrow spine, which is the
    // only place they are written down.
    let mut rest = bound.clone();
    let mut params = Vec::new();
    for p in &own {
        let (arg, res) = match rest {
            Ty::Fun(a, _, r) => (*a, *r),
            _ => {
                return Err(format!(
                    "`{}` has more params than its type has arrows",
                    cx.syms.text(name)
                ))
            }
        };
        params.push(IrParam { name: *p, ty: arg, span: d.span });
        rest = res;
    }
    let body = expr(body_expr, &rest, cx).map_err(|r| format!("{}: {r}", cx.syms.text(name)))?;
    Ok(IrDef {
        name,
        params,
        ty: bound,
        body,
        chapter_slug: d.chapter_slug.clone(),
        span: d.span,
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
        // DESUGARER MAKES THOSE.** `for r in temps -> r` becomes a `map-list`
        // application whose name node the checker never saw a source position
        // for, so `record-expr-type` skipped it -- `lookup-expr-type`'s own
        // first line is `if is-synthetic-span sp then ErrorTy`. Refusing here
        // is what stopped the whole 3.44 MB self-host from lowering, on one
        // comprehension in `tco-ensure-temps`.
        //
        // Upstream falls back to the name's BINDING, stripped of its forall,
        // and then to the expectation. Neither is a guess: the binding is the
        // checker's own answer for the name, and the expectation is what the
        // caller of this node already committed to.
        Expr::NameRef(n, s) => {
            let t = match cx.at(*s) {
                Some(t) => t,
                None => match cx.bindings.get(n) {
                    Some(raw) => crate::check::strip_forall(&cx.st.deep_resolve(raw)),
                    None => want.clone(),
                },
            };
            Ok(IrExpr::Name(*n, t, *s))
        }
        Expr::Apply(f, a, s) => {
            let f = expr(f, &Ty::NoExpect, cx)?;
            let a = expr(a, &Ty::NoExpect, cx)?;
            // The result of applying one argument is the arrow's right half. A
            // non-arrow here is an over-application, a real error and not
            // something to paper over with the same type back.
            let res = match f.ty() {
                Ty::Fun(_, _, r) => *r,
                other => {
                    return Err(format!("applying a non-arrow `{}`", render_ty(cx.syms, &other)))
                }
            };
            Ok(IrExpr::Apply(Box::new(f), Box::new(a), res, *s))
        }
        // **THE OPERATOR NAME DEPENDS ON THE OPERAND TYPE** -- `add-int`,
        // `add-num` and `add-vec` are three names for one source `+` -- so
        // this needs the operands typed first and refuses where it cannot
        // tell.
        Expr::Binary(l, op, r, s) => {
            let l = expr(l, &Ty::NoExpect, cx)?;
            let r = expr(r, &Ty::NoExpect, cx)?;
            let lty = l.ty();
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
            let arith = |int: IrBinOp, num: IrBinOp| -> Result<IrBinOp, String> {
                match &lty {
                    Ty::Integer(..) => Ok(int),
                    Ty::Real(..) => Ok(num),
                    other => {
                        Err(format!("{} on `{}`", int.atom(), render_ty(cx.syms, other)))
                    }
                }
            };
            let (name, ty) = match op {
                BinaryOp::OpAdd => (arith(IrBinOp::AddInt, IrBinOp::AddNum)?, lty.clone()),
                BinaryOp::OpSub => (arith(IrBinOp::SubInt, IrBinOp::SubNum)?, lty.clone()),
                BinaryOp::OpMul => (arith(IrBinOp::MulInt, IrBinOp::MulNum)?, lty.clone()),
                BinaryOp::OpDiv => (arith(IrBinOp::DivInt, IrBinOp::DivNum)?, lty.clone()),
                BinaryOp::OpEq => (IrBinOp::Eq, Ty::Boolean),
                BinaryOp::OpNotEq => (IrBinOp::NotEq, Ty::Boolean),
                BinaryOp::OpLt => (IrBinOp::Lt, Ty::Boolean),
                BinaryOp::OpGt => (IrBinOp::Gt, Ty::Boolean),
                BinaryOp::OpLtEq => (IrBinOp::LtEq, Ty::Boolean),
                BinaryOp::OpGtEq => (IrBinOp::GtEq, Ty::Boolean),
                // **ONE TOKEN, THREE ATOMS.** `&` is `and` over Booleans,
                // `append-text` over Text and `append-list` over a List, and
                // the OPERAND type is what picks. `and` the keyword is only
                // ever logical.
                BinaryOp::OpAnd | BinaryOp::OpAppend => match &lty {
                    Ty::Boolean => (IrBinOp::And, Ty::Boolean),
                    Ty::Text => (IrBinOp::AppendText, lty.clone()),
                    Ty::List(_) => (IrBinOp::AppendList, lty.clone()),
                    other => return Err(format!("`&` on `{}`", render_ty(cx.syms, other))),
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
                BinaryOp::OpBoolAnd => (IrBinOp::And, Ty::Boolean),
                BinaryOp::OpOr => (IrBinOp::Or, Ty::Boolean),
                other => return Err(format!("binary op {other:?}")),
            };
            Ok(IrExpr::Binary(name, Box::new(l), Box::new(r), ty, *s))
        }
        // **THE BRANCHES DO NOT HAVE TO AGREE, AND USUALLY DO NOT.** The
        // checker unified them; the wire did not.
        Expr::If(c, th, el, s) => {
            let c = expr(c, &Ty::NoExpect, cx)?;
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
        Expr::List(xs, s) => {
            // An empty list has no element to read a type from: the type is
            // the variable the checker minted for it, so `[]` in a call to
            // `list-length` spells `(list-expr (elems) int-default)`.
            if xs.is_empty() {
                let e = cx.at(*s).ok_or("empty list literal with no recorded element type")?;
                return Ok(IrExpr::List(Vec::new(), e, *s));
            }
            let mut parts = Vec::new();
            let mut elem: Option<Ty> = None;
            for x in xs {
                let x = expr(x, &Ty::NoExpect, cx)?;
                let xty = x.ty();
                match &elem {
                    None => elem = Some(xty),
                    Some(e) if *e == xty => {}
                    Some(e) => {
                        return Err(format!(
                            "list elements disagree: `{}` vs `{}`",
                            render_ty(cx.syms, e),
                            render_ty(cx.syms, &xty)
                        ))
                    }
                }
                parts.push(x);
            }
            Ok(IrExpr::List(parts, elem.unwrap(), *s))
        }
        // `(let "n" TYPE VALUE BODY)`, nested one deep per binding, and the
        // let's own type is the BODY's -- a let evaluates to its body. The
        // bound values get no expectation; the body inherits the let's.
        Expr::Let(binds, body, s) => {
            let mut heads = Vec::new();
            for b in binds {
                let v = expr(&b.value, &Ty::NoExpect, cx)?;
                heads.push((b.name, v.ty(), v));
            }
            let mut out = expr(body, want, cx)?;
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
            let mut parts = Vec::new();
            let mut last = Ty::Nothing;
            for st in stmts {
                match st {
                    crate::ast::ActStmt::Exec(e, sp2) => {
                        let x = expr(e, &Ty::NoExpect, cx)?;
                        last = x.ty();
                        parts.push(IrActStmt::Exec(x, *sp2));
                    }
                    crate::ast::ActStmt::Bind(n, e, sp2) => {
                        let x = expr(e, &Ty::NoExpect, cx)?;
                        last = x.ty();
                        parts.push(IrActStmt::Bind(*n, x.ty(), x, *sp2));
                    }
                }
            }
            Ok(IrExpr::Act(parts, last, *s))
        }
        Expr::Record(n, fields, s) => {
            let ty = cx
                .at(*s)
                .ok_or_else(|| format!("no recorded type for record `{}`", cx.syms.text(*n)))?;
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
            let name = record_name(&r.ty(), cx, "field access on")?;
            let (Some(fty), Some(slot)) = (cx.tds.field(name, *f), cx.tds.field_index(name, *f))
            else {
                return Err(format!(
                    "`{}` has no field `{}` here",
                    cx.syms.text(name),
                    cx.syms.text(*f)
                ));
            };
            let fty = cx.st.deep_resolve(fty);
            Ok(IrExpr::FieldAccess(
                Box::new(r),
                format!("{}/{}", cx.syms.text(*f), slot),
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
                    cx.syms.text(name),
                    cx.syms.text(*f)
                ));
            };
            let v = expr(v, &Ty::NoExpect, cx)?;
            Ok(IrExpr::FieldStore(
                Box::new(r),
                format!("{}/{}", cx.syms.text(*f), slot),
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
            let sty = sc.ty();
            let mut branches = Vec::new();
            for a in arms {
                let pat = pattern(&a.pattern, &sty, cx)?;
                let body = expr(&a.body, want, cx)?;
                let guard = expr(&a.guard, &Ty::NoExpect, cx)?;
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
            let lam_ty = if lt::has_error(want) {
                cx.recorded(*s)
            } else {
                cx.st.deep_resolve(want)
            };
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
            let mut ret = lam_ty.clone();
            let mut ir_params = Vec::new();
            for p in &params {
                let (a, r) = match ret {
                    Ty::Fun(a, _, r) => (*a, *r),
                    _ => (Ty::Error, Ty::Error),
                };
                ir_params.push(IrParam { name: *p, ty: a, span: *s });
                ret = r;
            }
            let b = expr(inner, &ret, cx)?;
            Ok(IrExpr::Lambda(ir_params, Box::new(b), lam_ty, *s))
        }
        other => Err(node_kind(other).to_string()),
    }
}

/// The record or constructed type's name, or the reason this is neither.
fn record_name(t: &Ty, cx: &Lower, what: &str) -> Result<Sym, String> {
    match t {
        Ty::Record(n, _) | Ty::Constructed(n, _) => Ok(*n),
        other => Err(format!("{what} `{}`, which is not a record", render_ty(cx.syms, other))),
    }
}

/// One pattern.
///
/// **THIS IS SHORT BECAUSE THE CHECKER'S ANSWER WAS KEPT.** Upstream's
/// lowering rebuilds a destructured field's type from the constructor
/// declaration and the scrutinee -- `pattern-type-subst`, `apply-ctor-subst`,
/// `ctor-ret-tyargs`, `pair-tvars`, `subst-tvars`. It has to: its lowering
/// pass reads types only by span out of `expr-types`, and a pattern is not an
/// expression, so its own checker's answer is unreachable from there. Ours
/// records it in `pat_types` (see `check::bind_pattern`), so the field type is
/// a lookup and the substitution machinery is never written.
fn pattern(p: &Pat, scrut: &Ty, cx: &Lower) -> Result<IrPat, String> {
    let want = |sp: crate::ast::Span| -> Ty {
        cx.st.pat_type_at(sp).map_or_else(|| scrut.clone(), |t| cx.st.deep_resolve(t))
    };
    match p {
        Pat::Wild(s) => Ok(IrPat::Wild(*s)),
        Pat::Var(n, s) => Ok(IrPat::Var(*n, want(*s), *s)),
        Pat::Lit(v, _, s) => Ok(IrPat::Lit(v.clone(), want(*s), *s)),
        Pat::Ctor(n, subs, s) => {
            let mut out = Vec::new();
            for sub in subs {
                out.push(pattern(sub, &Ty::Error, cx)?);
            }
            Ok(IrPat::Ctor(*n, out, want(*s), *s))
        }
        Pat::Vec_(..) => Err("vector pattern".into()),
    }
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
