//! The proof normalizer and the induction planner -- upstream's `Section:
//! Proof Normalizer` (TypeChecker.codex:101) and `Section: Induction
//! Checking` (:2828).
//!
//! **COMPUTED ONCE, AFTER DESUGARING, WHILE THE SYMBOL TABLE IS STILL
//! WRITABLE.** A normalized term names things no source spelled -- the `7`
//! that `1 + 2 * 3` reduces to, the `Cons` a list primitive builds, the
//! `__lemma-0` a cited claim becomes -- and a `Ty` names by symbol. The
//! checker holds the table read-only, so the plan is built here and read
//! there by definition index.
//!
//! A claim's declared equality is a pair of TERMS spelled in type position:
//! `flip On === On` resolves to two constructed types whose names are a
//! definition and a constructor. `normalize` unfolds the definitions,
//! reduces matches on known constructors, folds literal arithmetic and the
//! list primitives, and answers a constructed type again, so `Refl` meets
//! `Off === On` and CDX2001 says so. A side that is not a term -- `Integer`,
//! `List Text` -- is left as it is.

use std::collections::BTreeMap;

use crate::ast::{BinaryOp, Chapter, Def, Expr, LiteralKind, MatchArm, Name, Pat, Span, TypeDef, TypeExpr};
use crate::check::{expr_type_key, resolve_declared, Binding, Cdx, Ty, TypeDefs, UnifyState};
use crate::symbol::SymTab;

/// `proof-norm-fuel`.
pub const FUEL: i64 = 100_000;

#[derive(Clone, Debug, Default)]
pub struct ProofPlan {
    /// `register-all-defs`'s `normalize-prop-eq`: a definition whose declared
    /// type is an equality, with both sides normalized.
    pub declared: BTreeMap<usize, Ty>,
    /// `def-is-induction`: a for-all claim proved by `induction on`.
    pub inductions: BTreeMap<usize, InductionPlan>,
}

#[derive(Clone, Debug, Default)]
pub struct InductionPlan {
    /// `bind-forall-value-binders`: each `for all (n : T)` binds `n : T`.
    pub binders: Vec<(Name, Ty)>,
    /// One per constructor of the induction variable's type, in declaration
    /// order.
    pub cases: Vec<InductionCase>,
    /// `induction-unproven`: the claim is not a variant-typed for-all
    /// equality, so it is accepted as an axiom (a warning upstream).
    pub unproven: bool,
}

#[derive(Clone, Debug)]
pub struct InductionCase {
    pub ctor: Name,
    /// `None` is `induction-missing-arm`: CDX2070.
    pub arm: Option<ArmPlan>,
}

#[derive(Clone, Debug)]
pub struct ArmPlan {
    /// The pattern binds fewer names than the constructor has fields:
    /// `induction-unproven-st`, nothing checked.
    pub unproven: bool,
    /// `PropEqTy subL subR`, both sides normalized with the constructor
    /// application substituted for the induction variable.
    pub subgoal: Ty,
    /// The field variables at their field types, then each inductive
    /// hypothesis at its equality, then each cited claim as `__lemma-N`.
    pub binds: Vec<(Name, Ty)>,
    /// The arm's body with cited claims replaced by their lemma names.
    pub body: Expr,
}

// ---------------------------------------------------------------------------
// Terms: the expression shapes `normalize-aterm` walks, named by text.

#[derive(Clone, Debug, PartialEq)]
enum Term {
    Name(String),
    App(Box<Term>, Box<Term>),
    Match(Box<Term>, Vec<Arm>),
    If(Box<Term>, Box<Term>, Box<Term>),
    Let(Vec<(String, Term)>, Box<Term>),
    Lit(String, LiteralKind),
    Binary(Box<Term>, BinaryOp, Box<Term>),
    Unary(Box<Term>),
    /// Every other form: not normal, and substitution does not enter it.
    Other,
}

#[derive(Clone, Debug, PartialEq)]
struct Arm {
    pat: TPat,
    body: Term,
}

#[derive(Clone, Debug, PartialEq)]
enum TPat {
    Var(String),
    Ctor(String, Vec<TPat>),
    Other,
}

struct TDef {
    name: String,
    params: Vec<String>,
    body: Term,
}

fn term_of(e: &Expr, syms: &SymTab) -> Term {
    match e {
        Expr::Lit(s, k, _) => Term::Lit(s.clone(), *k),
        Expr::NameRef(n, _) => Term::Name(syms.text(*n).to_string()),
        Expr::Apply(f, a, _) => Term::App(Box::new(term_of(f, syms)), Box::new(term_of(a, syms))),
        Expr::Binary(l, op, r, _) => Term::Binary(Box::new(term_of(l, syms)), *op, Box::new(term_of(r, syms))),
        Expr::Unary(x, _) => Term::Unary(Box::new(term_of(x, syms))),
        Expr::If(c, t, el, _) => {
            Term::If(Box::new(term_of(c, syms)), Box::new(term_of(t, syms)), Box::new(term_of(el, syms)))
        }
        Expr::Let(binds, body, _) => Term::Let(
            binds.iter().map(|b| (syms.text(b.name).to_string(), term_of(&b.value, syms))).collect(),
            Box::new(term_of(body, syms)),
        ),
        Expr::Match(sc, arms, _) => Term::Match(
            Box::new(term_of(sc, syms)),
            arms.iter().map(|a| Arm { pat: tpat_of(&a.pattern, syms), body: term_of(&a.body, syms) }).collect(),
        ),
        _ => Term::Other,
    }
}

fn tpat_of(p: &Pat, syms: &SymTab) -> TPat {
    match p {
        Pat::Var(n, _) => TPat::Var(syms.text(*n).to_string()),
        Pat::Ctor(n, subs, _) => TPat::Ctor(syms.text(*n).to_string(), subs.iter().map(|s| tpat_of(s, syms)).collect()),
        _ => TPat::Other,
    }
}

fn tdefs_of(defs: &[Def], syms: &SymTab) -> Vec<TDef> {
    defs.iter()
        .map(|d| TDef {
            name: syms.text(d.name).to_string(),
            params: d.params.iter().map(|p| syms.text(p.name).to_string()).collect(),
            body: term_of(&d.body, syms),
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Between a type and a term.

/// `is-term-ctype`: a constructed type whose arguments are all terms. A bare
/// `TypeCon` is what `resolve_declared` answers for a name no type declares,
/// and it is upstream's `ConstructedTy n []`.
fn is_term_ctype(t: &Ty) -> bool {
    match t {
        Ty::Constructed(_, args) => args.iter().all(is_term_ctype),
        Ty::TypeCon(_) => true,
        _ => false,
    }
}

fn ctype_to_aterm(t: &Ty, syms: &SymTab) -> Term {
    match t {
        Ty::Constructed(n, args) => args.iter().fold(Term::Name(syms.text(*n).to_string()), |acc, a| {
            Term::App(Box::new(acc), Box::new(ctype_to_aterm(a, syms)))
        }),
        Ty::TypeCon(n) => Term::Name(syms.text(*n).to_string()),
        _ => Term::Name("__nonterm".to_string()),
    }
}

fn is_aterm_normal(e: &Term) -> bool {
    match e {
        Term::Name(_) => true,
        Term::App(f, a) => is_aterm_normal(f) && is_aterm_normal(a),
        _ => false,
    }
}

fn aterm_to_codextype(e: &Term, syms: &mut SymTab) -> Ty {
    match e {
        Term::Name(n) => Ty::Constructed(syms.intern(n), Vec::new()),
        Term::App(f, a) => match aterm_to_codextype(f, syms) {
            Ty::Constructed(n, mut args) => {
                args.push(aterm_to_codextype(a, syms));
                Ty::Constructed(n, args)
            }
            _ => Ty::Constructed(syms.intern("__stuck"), Vec::new()),
        },
        _ => Ty::Constructed(syms.intern("__stuck"), Vec::new()),
    }
}

/// `normalize-codextype`: a term is normalized and read back; anything else,
/// or a term that gets stuck, is answered unchanged.
fn normalize_codextype(defs: &[TDef], t: &Ty, syms: &mut SymTab) -> Ty {
    if !is_term_ctype(t) {
        return t.clone();
    }
    let nf = normalize_aterm(defs, &ctype_to_aterm(t, syms), FUEL);
    if is_aterm_normal(&nf) {
        aterm_to_codextype(&nf, syms)
    } else {
        t.clone()
    }
}

fn normalize_prop_eq(defs: &[TDef], t: &Ty, syms: &mut SymTab) -> Ty {
    match t {
        Ty::PropEq(l, r) => Ty::PropEq(
            Box::new(normalize_codextype(defs, l, syms)),
            Box::new(normalize_codextype(defs, r, syms)),
        ),
        _ => t.clone(),
    }
}

// ---------------------------------------------------------------------------
// `normalize-aterm` and its helpers.

fn find_def<'a>(defs: &'a [TDef], nm: &str) -> Option<&'a TDef> {
    defs.iter().find(|d| d.name == nm)
}

fn normalize_aterm(defs: &[TDef], e: &Term, fuel: i64) -> Term {
    if fuel <= 0 {
        return e.clone();
    }
    match e {
        Term::Name(n) => match find_def(defs, n) {
            Some(d) if d.params.is_empty() => normalize_aterm(defs, &d.body, fuel - 1),
            _ => e.clone(),
        },
        Term::App(..) => normalize_app(defs, e, fuel),
        Term::Match(sc, arms) => normalize_match(defs, sc, arms, fuel),
        Term::If(c, t, el) => {
            let c2 = normalize_aterm(defs, c, fuel);
            match &c2 {
                Term::Lit(txt, LiteralKind::BoolLit) => {
                    if txt == "True" {
                        normalize_aterm(defs, t, fuel - 1)
                    } else {
                        normalize_aterm(defs, el, fuel - 1)
                    }
                }
                _ => Term::If(Box::new(c2), t.clone(), el.clone()),
            }
        }
        Term::Let(binds, body) => {
            let sub: Vec<(String, Term)> = binds.clone();
            normalize_aterm(defs, &subst_expr(&sub, body), fuel - 1)
        }
        _ => e.clone(),
    }
}

fn is_arith_op_name(t: &str) -> bool {
    matches!(t, "+" | "-" | "*" | "/")
}

fn is_int_literal_text(t: &str) -> bool {
    let digits = t.strip_prefix('-').unwrap_or(t);
    !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
}

fn aterm_name_text(e: &Term) -> &str {
    match e {
        Term::Name(n) => n,
        _ => "",
    }
}

fn arith_fold_value(op: &str, x: i64, y: i64) -> i64 {
    match op {
        "+" => x.wrapping_add(y),
        "-" => x.wrapping_sub(y),
        "*" => x.wrapping_mul(y),
        _ => x.wrapping_div(y),
    }
}

fn build_app_spine(head: &Term, args: &[Term]) -> Term {
    args.iter().fold(head.clone(), |acc, a| Term::App(Box::new(acc), Box::new(a.clone())))
}

fn normalize_arith(defs: &[TDef], op: &str, head: &Term, args: &[Term], fuel: i64) -> Term {
    let a = normalize_aterm(defs, &args[0], fuel);
    let b = normalize_aterm(defs, &args[1], fuel);
    let (at, bt) = (aterm_name_text(&a).to_string(), aterm_name_text(&b).to_string());
    if is_int_literal_text(&at) && is_int_literal_text(&bt) {
        let y: i64 = bt.parse().unwrap_or(0);
        if op == "/" && y == 0 {
            return build_app_spine(head, &[a, b]);
        }
        let x: i64 = at.parse().unwrap_or(0);
        return Term::Name(arith_fold_value(op, x, y).to_string());
    }
    build_app_spine(head, &[a, b])
}

fn is_list_prim_name(t: &str) -> bool {
    matches!(t, "list-length" | "list-push" | "list-snoc" | "list-at" | "list-set-at" | "list-insert-at" | "&")
}

fn app_head(e: &Term) -> &Term {
    match e {
        Term::App(f, _) => app_head(f),
        _ => e,
    }
}

fn app_args(e: &Term) -> Vec<Term> {
    match e {
        Term::App(f, a) => {
            let mut v = app_args(f);
            v.push((**a).clone());
            v
        }
        _ => Vec::new(),
    }
}

fn aterm_ctor_name(e: &Term) -> &str {
    aterm_name_text(app_head(e))
}

fn list_prim_nil(e: &Term) -> bool {
    aterm_ctor_name(e) == "Nil" && app_args(e).is_empty()
}

fn list_prim_cons(e: &Term) -> bool {
    aterm_ctor_name(e) == "Cons" && app_args(e).len() == 2
}

fn cons_head_of(e: &Term) -> Term {
    app_args(e)[0].clone()
}

fn cons_tail_of(e: &Term) -> Term {
    app_args(e)[1].clone()
}

fn int_name_term(n: i64) -> Term {
    Term::Name(n.to_string())
}

fn name_term(s: &str) -> Term {
    Term::Name(s.to_string())
}

fn cons_term(h: Term, t: Term) -> Term {
    build_app_spine(&name_term("Cons"), &[h, t])
}

fn normalize_list_prim(defs: &[TDef], op: &str, head: &Term, args: &[Term], fuel: i64) -> Term {
    match (op, args.len()) {
        ("list-length", 1) => normalize_list_length(defs, head, args, fuel),
        ("list-push" | "list-snoc", 2) => normalize_list_push(defs, head, args, fuel),
        ("list-at", 2) => normalize_list_at(defs, head, args, fuel),
        ("list-set-at", 3) => normalize_list_set_at(defs, head, args, fuel),
        ("list-insert-at", 3) => normalize_list_insert_at(defs, head, args, fuel),
        ("&", 2) => normalize_list_append(defs, head, args, fuel),
        _ => rebuild_app(defs, head, args, fuel),
    }
}

fn normalize_list_length(defs: &[TDef], head: &Term, args: &[Term], fuel: i64) -> Term {
    let a = normalize_aterm(defs, &args[0], fuel);
    if list_prim_nil(&a) {
        int_name_term(0)
    } else if list_prim_cons(&a) {
        let rest = build_app_spine(head, &[cons_tail_of(&a)]);
        normalize_aterm(defs, &build_app_spine(&name_term("+"), &[int_name_term(1), rest]), fuel - 1)
    } else {
        build_app_spine(head, &[a])
    }
}

fn normalize_list_push(defs: &[TDef], head: &Term, args: &[Term], fuel: i64) -> Term {
    let a = normalize_aterm(defs, &args[0], fuel);
    let x = normalize_aterm(defs, &args[1], fuel);
    if list_prim_nil(&a) {
        build_app_spine(&name_term("Cons"), &[x, name_term("Nil")])
    } else if list_prim_cons(&a) {
        let rest = normalize_aterm(defs, &build_app_spine(head, &[cons_tail_of(&a), x]), fuel - 1);
        build_app_spine(&name_term("Cons"), &[cons_head_of(&a), rest])
    } else {
        build_app_spine(head, &[a, x])
    }
}

fn normalize_list_at(defs: &[TDef], head: &Term, args: &[Term], fuel: i64) -> Term {
    let a = normalize_aterm(defs, &args[0], fuel);
    let ix = normalize_aterm(defs, &args[1], fuel);
    let it = aterm_name_text(&ix).to_string();
    if list_prim_cons(&a) && is_int_literal_text(&it) {
        let n: i64 = it.parse().unwrap_or(0);
        if n == 0 {
            cons_head_of(&a)
        } else if n > 0 {
            normalize_aterm(defs, &build_app_spine(head, &[cons_tail_of(&a), int_name_term(n - 1)]), fuel - 1)
        } else {
            build_app_spine(head, &[a, ix])
        }
    } else {
        build_app_spine(head, &[a, ix])
    }
}

fn normalize_list_set_at(defs: &[TDef], head: &Term, args: &[Term], fuel: i64) -> Term {
    let a = normalize_aterm(defs, &args[0], fuel);
    let ix = normalize_aterm(defs, &args[1], fuel);
    let v = normalize_aterm(defs, &args[2], fuel);
    let it = aterm_name_text(&ix).to_string();
    if list_prim_cons(&a) && is_int_literal_text(&it) {
        let n: i64 = it.parse().unwrap_or(0);
        if n == 0 {
            cons_term(v, cons_tail_of(&a))
        } else if n > 0 {
            let rest = normalize_aterm(
                defs,
                &build_app_spine(head, &[cons_tail_of(&a), int_name_term(n - 1), v]),
                fuel - 1,
            );
            cons_term(cons_head_of(&a), rest)
        } else {
            build_app_spine(head, &[a, ix, v])
        }
    } else {
        build_app_spine(head, &[a, ix, v])
    }
}

fn normalize_list_insert_at(defs: &[TDef], head: &Term, args: &[Term], fuel: i64) -> Term {
    let a = normalize_aterm(defs, &args[0], fuel);
    let ix = normalize_aterm(defs, &args[1], fuel);
    let v = normalize_aterm(defs, &args[2], fuel);
    let it = aterm_name_text(&ix).to_string();
    if (list_prim_nil(&a) || list_prim_cons(&a)) && is_int_literal_text(&it) {
        let n: i64 = it.parse().unwrap_or(0);
        if n == 0 {
            cons_term(v, a)
        } else if n > 0 && list_prim_cons(&a) {
            let rest = normalize_aterm(
                defs,
                &build_app_spine(head, &[cons_tail_of(&a), int_name_term(n - 1), v]),
                fuel - 1,
            );
            cons_term(cons_head_of(&a), rest)
        } else {
            build_app_spine(head, &[a, ix, v])
        }
    } else {
        build_app_spine(head, &[a, ix, v])
    }
}

fn normalize_list_append(defs: &[TDef], head: &Term, args: &[Term], fuel: i64) -> Term {
    let a = normalize_aterm(defs, &args[0], fuel);
    let b = normalize_aterm(defs, &args[1], fuel);
    if list_prim_nil(&a) {
        b
    } else if list_prim_cons(&a) {
        let rest = normalize_aterm(defs, &build_app_spine(head, &[cons_tail_of(&a), b]), fuel - 1);
        cons_term(cons_head_of(&a), rest)
    } else {
        build_app_spine(head, &[a, b])
    }
}

fn normalize_app(defs: &[TDef], e: &Term, fuel: i64) -> Term {
    let head = app_head(e).clone();
    let args = app_args(e);
    let Term::Name(n) = &head else { return rebuild_app(defs, &head, &args, fuel) };
    if is_arith_op_name(n) && args.len() == 2 {
        return normalize_arith(defs, n, &head, &args, fuel);
    }
    if is_list_prim_name(n) {
        return normalize_list_prim(defs, n, &head, &args, fuel);
    }
    match find_def(defs, n) {
        Some(d) if d.params.len() == args.len() => {
            let fv = collect_arg_names(&args);
            let body2 = rename_binders_for(&d.body, &fv, fuel);
            let sub: Vec<(String, Term)> = d.params.iter().cloned().zip(args.iter().cloned()).collect();
            let unfolded = normalize_aterm(defs, &subst_expr(&sub, &body2), fuel - 1);
            if is_aterm_normal(&unfolded) {
                unfolded
            } else {
                rebuild_app(defs, &head, &args, fuel)
            }
        }
        _ => rebuild_app(defs, &head, &args, fuel),
    }
}

fn collect_arg_names(args: &[Term]) -> Vec<String> {
    let mut acc = Vec::new();
    for a in args {
        aexpr_names(a, &mut acc);
    }
    acc
}

fn aexpr_names(e: &Term, acc: &mut Vec<String>) {
    match e {
        Term::Name(n) => acc.push(n.clone()),
        Term::App(f, a) => {
            aexpr_names(f, acc);
            aexpr_names(a, acc);
        }
        _ => {}
    }
}

/// `rename-binders-for`: a match arm whose pattern binds a name free in the
/// arguments is renamed apart, `x` to `x~<fuel>`.
fn rename_binders_for(e: &Term, fv: &[String], fuel: i64) -> Term {
    match e {
        Term::Match(sc, arms) => Term::Match(
            Box::new(rename_binders_for(sc, fv, fuel)),
            arms.iter()
                .map(|arm| {
                    let colliding: Vec<String> =
                        pat_vars(&arm.pat).into_iter().filter(|v| fv.contains(v)).collect();
                    if colliding.is_empty() {
                        Arm { pat: arm.pat.clone(), body: rename_binders_for(&arm.body, fv, fuel) }
                    } else {
                        let sub: Vec<(String, Term)> = colliding
                            .iter()
                            .map(|n| (n.clone(), Term::Name(format!("{n}~{fuel}"))))
                            .collect();
                        Arm {
                            pat: rename_pat_vars(&arm.pat, &colliding, fuel),
                            body: subst_expr(&sub, &rename_binders_for(&arm.body, fv, fuel)),
                        }
                    }
                })
                .collect(),
        ),
        Term::App(f, a) => {
            Term::App(Box::new(rename_binders_for(f, fv, fuel)), Box::new(rename_binders_for(a, fv, fuel)))
        }
        Term::If(c, t, el) => Term::If(
            Box::new(rename_binders_for(c, fv, fuel)),
            Box::new(rename_binders_for(t, fv, fuel)),
            Box::new(rename_binders_for(el, fv, fuel)),
        ),
        _ => e.clone(),
    }
}

fn rename_pat_vars(p: &TPat, colliding: &[String], fuel: i64) -> TPat {
    match p {
        TPat::Var(n) if colliding.contains(n) => TPat::Var(format!("{n}~{fuel}")),
        TPat::Ctor(cn, subs) => {
            TPat::Ctor(cn.clone(), subs.iter().map(|s| rename_pat_vars(s, colliding, fuel)).collect())
        }
        _ => p.clone(),
    }
}

fn rebuild_app(defs: &[TDef], head: &Term, args: &[Term], fuel: i64) -> Term {
    let normalized: Vec<Term> = args.iter().map(|a| normalize_aterm(defs, a, fuel)).collect();
    build_app_spine(head, &normalized)
}

fn normalize_match(defs: &[TDef], sc: &Term, arms: &[Arm], fuel: i64) -> Term {
    let sc2 = normalize_aterm(defs, sc, fuel);
    if let Term::Name(cn) = app_head(&sc2) {
        let cargs = app_args(&sc2);
        if let Some(arm) = arms.iter().find(|a| matches!(&a.pat, TPat::Ctor(pn, subs) if pn == cn && subs.len() == cargs.len())) {
            let sub = ctorpat_to_subst(&arm.pat, &cargs);
            return normalize_aterm(defs, &subst_expr(&sub, &arm.body), fuel - 1);
        }
    }
    Term::Match(Box::new(sc2), arms.to_vec())
}

fn ctorpat_to_subst(p: &TPat, cargs: &[Term]) -> Vec<(String, Term)> {
    match p {
        TPat::Ctor(_, subs) => subs
            .iter()
            .zip(cargs.iter())
            .filter_map(|(s, c)| match s {
                TPat::Var(vn) => Some((vn.clone(), c.clone())),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

fn subst_expr(sub: &[(String, Term)], e: &Term) -> Term {
    match e {
        Term::Name(n) => sub.iter().find(|(k, _)| k == n).map_or_else(|| e.clone(), |(_, v)| v.clone()),
        Term::App(f, a) => Term::App(Box::new(subst_expr(sub, f)), Box::new(subst_expr(sub, a))),
        Term::Match(sc, arms) => Term::Match(
            Box::new(subst_expr(sub, sc)),
            arms.iter()
                .map(|arm| {
                    let inner = remove_shadowed(sub, &pat_vars(&arm.pat));
                    Arm { pat: arm.pat.clone(), body: subst_expr(&inner, &arm.body) }
                })
                .collect(),
        ),
        Term::If(c, t, el) => Term::If(
            Box::new(subst_expr(sub, c)),
            Box::new(subst_expr(sub, t)),
            Box::new(subst_expr(sub, el)),
        ),
        Term::Binary(l, op, r) => Term::Binary(Box::new(subst_expr(sub, l)), *op, Box::new(subst_expr(sub, r))),
        Term::Unary(x) => Term::Unary(Box::new(subst_expr(sub, x))),
        Term::Let(binds, body) => {
            let names: Vec<String> = binds.iter().map(|(n, _)| n.clone()).collect();
            Term::Let(
                binds.iter().map(|(n, v)| (n.clone(), subst_expr(sub, v))).collect(),
                Box::new(subst_expr(&remove_shadowed(sub, &names), body)),
            )
        }
        _ => e.clone(),
    }
}

fn remove_shadowed(sub: &[(String, Term)], names: &[String]) -> Vec<(String, Term)> {
    sub.iter().filter(|(k, _)| !names.contains(k)).cloned().collect()
}

fn pat_vars(p: &TPat) -> Vec<String> {
    match p {
        TPat::Var(n) => vec![n.clone()],
        TPat::Ctor(_, subs) => subs.iter().flat_map(pat_vars).collect(),
        TPat::Other => Vec::new(),
    }
}

// ---------------------------------------------------------------------------
// The plan.

/// Build the chapter's plan. Interns the names normalization invents.
pub fn prepare(ch: &mut Chapter) -> ProofPlan {
    let tds = TypeDefs::new(ch);
    let Chapter { syms, defs, type_defs, .. } = ch;
    let tdefs = tdefs_of(defs, syms);
    let mut plan = ProofPlan::default();
    for (i, d) in defs.iter().enumerate() {
        let Some(te) = d.declared_type.first() else { continue };
        if let Some(t @ Ty::PropEq(..)) = resolve_declared(syms, &tds, te) {
            let normalized = normalize_prop_eq(&tdefs, &t, syms);
            if std::env::var_os("CDX_TRACE_PROOF").is_some() {
                eprintln!("PROOF-DECL {} : {} => {}", syms.text(d.name), desc(&t, syms), desc(&normalized, syms));
            }
            plan.declared.insert(i, normalized);
        }
        if def_is_induction(d) {
            plan.inductions.insert(i, induction_plan(d, defs, type_defs, &tds, &tdefs, syms));
        }
    }
    plan
}

/// A type with its names spelled, for the trace.
pub fn desc(t: &Ty, syms: &SymTab) -> String {
    match t {
        Ty::Constructed(n, args) if args.is_empty() => syms.text(*n).to_string(),
        Ty::Constructed(n, args) => {
            let inner: Vec<String> = args.iter().map(|a| desc(a, syms)).collect();
            format!("{}[{}]", syms.text(*n), inner.join(", "))
        }
        Ty::TypeCon(n) => format!("tycon:{}", syms.text(*n)),
        Ty::PropEq(a, b) => format!("({} === {})", desc(a, syms), desc(b, syms)),
        Ty::List(e) => format!("List[{}]", desc(e, syms)),
        other => format!("{other:?}"),
    }
}

/// `def-is-induction`: declared as a for-all, proved by `induction on`.
fn def_is_induction(d: &Def) -> bool {
    matches!(d.declared_type.first(), Some(TypeExpr::Forall(..))) && matches!(d.body, Expr::Induction(..))
}

fn forall_binder_type<'a>(fa: &'a TypeExpr, name: Name) -> &'a TypeExpr {
    match fa {
        TypeExpr::Forall(v, vt, p, _) => {
            if *v == name {
                vt
            } else {
                forall_binder_type(p, name)
            }
        }
        _ => fa,
    }
}

fn forall_innermost_prop(fa: &TypeExpr) -> &TypeExpr {
    match fa {
        TypeExpr::Forall(_, _, p, _) => forall_innermost_prop(p),
        _ => fa,
    }
}

/// `bind-forall-value-binders`, in binder order.
fn forall_binders(fa: &TypeExpr, syms: &SymTab, tds: &TypeDefs) -> Vec<(Name, Ty)> {
    let mut out = Vec::new();
    let mut cur = fa;
    while let TypeExpr::Forall(v, vt, p, _) = cur {
        out.push((*v, resolve_declared(syms, tds, vt).unwrap_or(Ty::Error)));
        cur = p;
    }
    out
}

/// A constructor as the induction sees it: its name and its field types.
struct CtorShape {
    name: Name,
    fields: Vec<Ty>,
}

/// `sumty-of` + the constructor list: a declared variant's constructors, or
/// the builtin list's `Nil` and `Cons`.
fn ctors_of(t: &Ty, type_defs: &[TypeDef], tds: &TypeDefs, syms: &mut SymTab) -> Option<(String, Vec<CtorShape>)> {
    match t {
        Ty::Sum(n, _) | Ty::Constructed(n, _) => {
            let name = *n;
            let td = type_defs.iter().find_map(|d| match d {
                TypeDef::Variant(vn, _, ctors, _) if *vn == name => Some(ctors),
                _ => None,
            })?;
            let shapes = td
                .iter()
                .map(|c| CtorShape {
                    name: c.name,
                    fields: c.fields.iter().map(|f| resolve_declared(syms, tds, f).unwrap_or(Ty::Error)).collect(),
                })
                .collect();
            Some((syms.text(name).to_string(), shapes))
        }
        Ty::List(elem) | Ty::LinkedList(elem) => {
            let nil = syms.intern("Nil");
            let cons = syms.intern("Cons");
            Some((
                "List".to_string(),
                vec![
                    CtorShape { name: nil, fields: Vec::new() },
                    CtorShape { name: cons, fields: vec![(**elem).clone(), Ty::List(elem.clone())] },
                ],
            ))
        }
        _ => None,
    }
}

fn ctype_head_name(t: &Ty, syms: &SymTab) -> String {
    match t {
        Ty::Constructed(n, _) | Ty::Sum(n, _) | Ty::Record(n, _) => syms.text(*n).to_string(),
        Ty::List(_) | Ty::LinkedList(_) => "List".to_string(),
        _ => String::new(),
    }
}

/// `subst-ctype-name`: every bare `nm` in the type becomes `repl`.
fn subst_ctype_name(nm: &str, repl: &Ty, t: &Ty, syms: &SymTab) -> Ty {
    match t {
        Ty::Constructed(n, args) => {
            if syms.text(*n) == nm && args.is_empty() {
                repl.clone()
            } else {
                Ty::Constructed(*n, args.iter().map(|a| subst_ctype_name(nm, repl, a, syms)).collect())
            }
        }
        Ty::TypeCon(n) if syms.text(*n) == nm => repl.clone(),
        _ => t.clone(),
    }
}

fn ctorpat_var_names(p: &Pat) -> Vec<Name> {
    match p {
        Pat::Ctor(_, subs, _) => subs
            .iter()
            .filter_map(|s| match s {
                Pat::Var(n, _) => Some(*n),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

fn induction_plan(
    d: &Def,
    defs: &[Def],
    type_defs: &[TypeDef],
    tds: &TypeDefs,
    tdefs: &[TDef],
    syms: &mut SymTab,
) -> InductionPlan {
    let unproven = InductionPlan { unproven: true, ..Default::default() };
    let Expr::Induction(scrut, arms, _) = &d.body else { return unproven };
    let Expr::NameRef(iv, _) = &**scrut else { return unproven };
    let fa = &d.declared_type[0];
    let binders = forall_binders(fa, syms, tds);
    let var_ty = resolve_declared(syms, tds, forall_binder_type(fa, *iv)).unwrap_or(Ty::Error);
    let TypeExpr::PropEq(lhs_te, rhs_te, _) = forall_innermost_prop(fa) else { return unproven };
    let lhs = resolve_declared(syms, tds, lhs_te).unwrap_or(Ty::Error);
    let rhs = resolve_declared(syms, tds, rhs_te).unwrap_or(Ty::Error);
    let Some((tname, ctors)) = ctors_of(&var_ty, type_defs, tds, syms) else { return unproven };
    let ind_var = syms.text(*iv).to_string();
    let mut cases = Vec::new();
    for c in &ctors {
        let arm = arms.iter().find(|a| matches!(&a.pattern, Pat::Ctor(pn, _, _) if *pn == c.name));
        let Some(arm) = arm else {
            cases.push(InductionCase { ctor: c.name, arm: None });
            continue;
        };
        cases.push(InductionCase {
            ctor: c.name,
            arm: Some(arm_plan(arm, c, &tname, &ind_var, &lhs, &rhs, defs, tds, tdefs, syms)),
        });
    }
    InductionPlan { binders, cases, unproven: false }
}

/// `check-induction-arm`, up to the inference: the subgoal, the bindings and
/// the elaborated body.
#[allow(clippy::too_many_arguments)]
fn arm_plan(
    arm: &MatchArm,
    c: &CtorShape,
    tname: &str,
    ind_var: &str,
    lhs: &Ty,
    rhs: &Ty,
    defs: &[Def],
    tds: &TypeDefs,
    tdefs: &[TDef],
    syms: &mut SymTab,
) -> ArmPlan {
    let m = c.fields.len();
    let pat_vars = ctorpat_var_names(&arm.pattern);
    if pat_vars.len() < m {
        return ArmPlan { unproven: true, subgoal: Ty::Proof, binds: Vec::new(), body: arm.body.clone() };
    }
    let ctor_app = Ty::Constructed(c.name, pat_vars[..m].iter().map(|v| Ty::Constructed(*v, Vec::new())).collect());
    let sub_l = normalize_codextype(tdefs, &subst_ctype_name(ind_var, &ctor_app, lhs, syms), syms);
    let sub_r = normalize_codextype(tdefs, &subst_ctype_name(ind_var, &ctor_app, rhs, syms), syms);
    let subgoal = Ty::PropEq(Box::new(sub_l), Box::new(sub_r));
    let mut binds: Vec<(Name, Ty)> = pat_vars[..m].iter().copied().zip(c.fields.iter().cloned()).collect();
    // `bind-ihs`: a recursive field gets a hypothesis, bound to the next
    // pattern name after the fields.
    let mut cursor = 0;
    for j in 0..m {
        if ctype_head_name(&c.fields[j], syms) != tname {
            continue;
        }
        let fv_term = Ty::Constructed(pat_vars[j], Vec::new());
        let ih_l = normalize_codextype(tdefs, &subst_ctype_name(ind_var, &fv_term, lhs, syms), syms);
        let ih_r = normalize_codextype(tdefs, &subst_ctype_name(ind_var, &fv_term, rhs, syms), syms);
        if m + cursor < pat_vars.len() {
            binds.push((pat_vars[m + cursor], Ty::PropEq(Box::new(ih_l), Box::new(ih_r))));
            cursor += 1;
        }
    }
    let mut ctr = 0;
    let body = elab_claim_apps(&arm.body, defs, tds, tdefs, syms, &mut ctr, &mut binds);
    ArmPlan { unproven: false, subgoal, binds, body }
}

/// `elab-claim-apps`: an application of a for-all claim becomes a lemma
/// name bound to the claim instantiated at those arguments.
fn elab_claim_apps(
    e: &Expr,
    defs: &[Def],
    tds: &TypeDefs,
    tdefs: &[TDef],
    syms: &mut SymTab,
    ctr: &mut usize,
    binds: &mut Vec<(Name, Ty)>,
) -> Expr {
    let Expr::Apply(f, a, s) = e else { return e.clone() };
    if let Expr::NameRef(nm, _) = expr_head(e) {
        if let Some(claim) = find_claim_def(defs, *nm) {
            let args = expr_args(e);
            let inst = instantiate_claim(claim, &args, tds, tdefs, syms);
            let fresh = syms.intern(&format!("__lemma-{ctr}"));
            *ctr += 1;
            binds.push((fresh, inst));
            return Expr::NameRef(fresh, *s);
        }
    }
    let rf = elab_claim_apps(f, defs, tds, tdefs, syms, ctr, binds);
    let ra = elab_claim_apps(a, defs, tds, tdefs, syms, ctr, binds);
    Expr::Apply(std::rc::Rc::new(rf), std::rc::Rc::new(ra), *s)
}

fn expr_head(e: &Expr) -> &Expr {
    match e {
        Expr::Apply(f, _, _) => expr_head(f),
        _ => e,
    }
}

fn expr_args(e: &Expr) -> Vec<Expr> {
    match e {
        Expr::Apply(f, a, _) => {
            let mut v = expr_args(f);
            v.push((**a).clone());
            v
        }
        _ => Vec::new(),
    }
}

fn find_claim_def(defs: &[Def], name: Name) -> Option<&Def> {
    defs.iter().find(|d| d.name == name && matches!(d.declared_type.first(), Some(TypeExpr::Forall(..))))
}

/// `instantiate-claim`: the claim's equality with each binder replaced by the
/// argument written for it, both sides normalized.
fn instantiate_claim(claim: &Def, sargs: &[Expr], tds: &TypeDefs, tdefs: &[TDef], syms: &mut SymTab) -> Ty {
    let fa = &claim.declared_type[0];
    let TypeExpr::PropEq(l, r, _) = forall_innermost_prop(fa) else { return Ty::Proof };
    let mut sub_l = resolve_declared(syms, tds, l).unwrap_or(Ty::Error);
    let mut sub_r = resolve_declared(syms, tds, r).unwrap_or(Ty::Error);
    let mut cur = fa;
    let mut i = 0;
    while let TypeExpr::Forall(v, _, p, _) = cur {
        if i >= sargs.len() {
            break;
        }
        let term = aexpr_to_cterm(&sargs[i], syms);
        let vname = syms.text(*v).to_string();
        sub_l = subst_ctype_name(&vname, &term, &sub_l, syms);
        sub_r = subst_ctype_name(&vname, &term, &sub_r, syms);
        cur = p;
        i += 1;
    }
    Ty::PropEq(
        Box::new(normalize_codextype(tdefs, &sub_l, syms)),
        Box::new(normalize_codextype(tdefs, &sub_r, syms)),
    )
}

fn aexpr_to_cterm(e: &Expr, syms: &mut SymTab) -> Ty {
    match e {
        Expr::NameRef(n, _) => Ty::Constructed(*n, Vec::new()),
        Expr::Apply(f, a, _) => match aexpr_to_cterm(f, syms) {
            Ty::Constructed(n, mut args) => {
                args.push(aexpr_to_cterm(a, syms));
                Ty::Constructed(n, args)
            }
            _ => Ty::Constructed(syms.intern("__nonterm"), Vec::new()),
        },
        _ => Ty::Constructed(syms.intern("__nonterm"), Vec::new()),
    }
}

// ---------------------------------------------------------------------------
// After every definition is checked: `Section: Proof Acyclicity` and
// `check-proof-grammar` (TypeChecker.codex:2207, :2344).

/// `type-mentions-proof`: a definition is proof-relevant when its CHECKED
/// type mentions `Proof` or an equality anywhere. Fuel-capped, and answers
/// yes on exhaustion, so a pathological type errs toward checking.
fn type_mentions_proof(t: &Ty, fuel: i32, tds: &TypeDefs) -> bool {
    if fuel <= 0 {
        return true;
    }
    match t {
        Ty::Proof | Ty::PropEq(..) => true,
        Ty::Fun(p, _, r) => type_mentions_proof(p, fuel - 1, tds) || type_mentions_proof(r, fuel - 1, tds),
        Ty::List(e) | Ty::LinkedList(e) | Ty::Linear(e) | Ty::Vector(_, e) | Ty::Unit(_, e) => {
            type_mentions_proof(e, fuel - 1, tds)
        }
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) | Ty::Effectful(_, _, b) => type_mentions_proof(b, fuel - 1, tds),
        Ty::TypeApply(f, a) => type_mentions_proof(f, fuel - 1, tds) || type_mentions_proof(a, fuel - 1, tds),
        Ty::Constructed(_, args) | Ty::Sum(_, args) => args.iter().any(|a| type_mentions_proof(a, fuel - 1, tds)),
        Ty::Record(n, args) => {
            args.iter().any(|a| type_mentions_proof(a, fuel - 1, tds))
                || tds
                    .record_fields(*n)
                    .is_some_and(|fs| fs.iter().any(|(_, ft)| type_mentions_proof(ft, fuel - 1, tds)))
        }
        _ => false,
    }
}

fn span_of(e: &Expr) -> Span {
    match e {
        Expr::Lit(_, _, s)
        | Expr::NameRef(_, s)
        | Expr::Apply(_, _, s)
        | Expr::Binary(_, _, _, s)
        | Expr::Unary(_, s)
        | Expr::If(_, _, _, s)
        | Expr::Let(_, _, s)
        | Expr::Lambda(_, _, s)
        | Expr::Match(_, _, s)
        | Expr::List(_, s)
        | Expr::Record(_, _, s)
        | Expr::FieldAccess(_, _, s)
        | Expr::Act(_, s)
        | Expr::FieldAssign(_, _, _, s)
        | Expr::Lazy(_, s)
        | Expr::Error(_, s)
        | Expr::Induction(_, _, s) => *s,
        Expr::Handle(h) => h.span,
        Expr::WithTimeout(w) => w.span,
        Expr::Try(t) => t.span,
    }
}

/// `collect-rt-mentions` with the empty self: every proof-relevant name the
/// body mentions, itself included, each once.
fn proof_mentions(body: &Expr, names: &[Name]) -> Vec<Name> {
    let mut acc: Vec<Name> = Vec::new();
    body.walk(&mut |e| {
        if let Expr::NameRef(n, _) = e {
            if names.contains(n) && !acc.contains(n) {
                acc.push(*n);
            }
        }
    });
    acc
}

fn reaches(edges: &[(Name, Vec<Name>)], from: Name, target: Name, visited: &mut Vec<Name>) -> bool {
    if from == target {
        return true;
    }
    if visited.contains(&from) {
        return false;
    }
    visited.push(from);
    edges
        .iter()
        .find(|(n, _)| *n == from)
        .is_some_and(|(_, calls)| calls.iter().any(|c| reaches(edges, *c, target, visited)))
}

/// `pg-form-name`: what a disallowed proof term is.
fn form_name(e: &Expr) -> &'static str {
    match e {
        Expr::If(..) => "an if-expression",
        Expr::Match(..) => "a when-expression (a proof recurses only through 'induction')",
        Expr::Lambda(..) => "a lambda",
        Expr::Act(..) => "an act block",
        Expr::Binary(..) => "a binary-operator expression",
        Expr::Unary(..) => "a unary-operator expression",
        Expr::List(..) => "a list literal",
        Expr::Record(..) => "a record literal",
        Expr::FieldAccess(..) => "a field access",
        Expr::Try(..) => "a try expression",
        Expr::Handle(..) => "a handle expression",
        Expr::WithTimeout(..) => "a with-timeout expression",
        Expr::FieldAssign(..) => "a field assignment",
        Expr::Lazy(..) => "a lazy expression",
        _ => "a non-proof expression",
    }
}

struct Grammar<'a> {
    st: &'a UnifyState,
    tds: &'a TypeDefs,
    errs: Vec<String>,
}

impl Grammar<'_> {
    /// `pg-is-prop`: the recorded type of this expression mentions a proof.
    fn is_prop(&self, e: &Expr) -> bool {
        let key = expr_type_key(span_of(e));
        let Ok(i) = self.st.expr_types.binary_search_by_key(&key, |(k, _)| *k) else { return false };
        let t = self.st.deep_resolve(&self.st.expr_types[i].1);
        type_mentions_proof(&t, 64, self.tds)
    }

    /// `check-proof-term`.
    fn term(&mut self, e: &Expr) {
        match e {
            Expr::NameRef(..) => {}
            Expr::Apply(f, a, _) => {
                self.term(f);
                if self.is_prop(a) {
                    self.term(a);
                }
            }
            Expr::Induction(_, arms, _) => {
                for arm in arms {
                    self.term(&arm.body);
                }
            }
            Expr::Let(binds, body, _) => {
                self.term(body);
                for b in binds {
                    if self.is_prop(&b.value) {
                        self.term(&b.value);
                    }
                }
            }
            other => self.errs.push(format!(
                "proof term uses a disallowed form: {}. A proof body may only be a proof builtin (Refl, sym, trans, cong, app-cong, assume), an inductive hypothesis, a cited claim, an 'induction' expression, or a let of proof terms. To assert this equality without proof, use 'assume'.",
                form_name(other)
            )),
        }
    }
}

/// `check-proof-cycles` then `check-proof-grammar`, over the checked types.
pub fn check_proof_rules(ch: &Chapter, per_def: &[Binding], tds: &TypeDefs, st: &mut UnifyState) {
    let names: Vec<Name> = ch
        .defs
        .iter()
        .filter(|d| {
            per_def
                .iter()
                .find(|b| b.name == d.name)
                .is_some_and(|b| type_mentions_proof(&st.deep_resolve(&b.ty), 64, tds))
        })
        .map(|d| d.name)
        .collect();
    if names.is_empty() {
        return;
    }
    let edges: Vec<(Name, Vec<Name>)> = ch
        .defs
        .iter()
        .filter(|d| names.contains(&d.name))
        .map(|d| (d.name, proof_mentions(&d.body, &names)))
        .collect();
    for (name, calls) in &edges {
        let mut visited = Vec::new();
        if calls.iter().any(|c| reaches(&edges, *c, *name, &mut visited)) {
            st.error(
                Cdx::CIRCULAR_PROOF,
                format!(
                    "circular proof: '{}' justifies itself, directly or through other proof definitions or cited lemmas; a proof term cannot assume its own conclusion. Recursion in a proof is only sound through structural induction, and lemma chains must be acyclic. To assert this equality without proof, use 'assume'.",
                    ch.syms.text(*name)
                ),
            );
        }
    }
    st.sort_expr_types();
    let mut errs = Vec::new();
    for d in ch.defs.iter().filter(|d| names.contains(&d.name)) {
        let mut g = Grammar { st, tds, errs: Vec::new() };
        g.term(&d.body);
        errs.extend(g.errs);
    }
    for m in errs {
        st.error(Cdx::NON_GRAMMATICAL_PROOF, m);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(s: &str) -> Term {
        Term::Name(s.to_string())
    }

    fn app(head: &str, args: &[Term]) -> Term {
        build_app_spine(&n(head), args)
    }

    #[test]
    fn literal_arithmetic_folds_with_precedence_already_in_the_tree() {
        // `1 + 2 * 3`, applied as upstream's type parser applies it.
        let t = app("+", &[n("1"), app("*", &[n("2"), n("3")])]);
        assert_eq!(normalize_aterm(&[], &t, FUEL), n("7"));
    }

    #[test]
    fn a_definition_unfolds_and_a_match_on_a_constructor_reduces() {
        let flip = TDef {
            name: "flip".into(),
            params: vec!["b".into()],
            body: Term::Match(
                Box::new(n("b")),
                vec![
                    Arm { pat: TPat::Ctor("On".into(), vec![]), body: n("Off") },
                    Arm { pat: TPat::Ctor("Off".into(), vec![]), body: n("On") },
                ],
            ),
        };
        assert_eq!(normalize_aterm(&[flip], &app("flip", &[n("On")]), FUEL), n("Off"));
    }

    #[test]
    fn list_at_walks_a_cons_spine() {
        let xs = app("Cons", &[n("5"), app("Cons", &[n("6"), n("Nil")])]);
        assert_eq!(normalize_aterm(&[], &app("list-at", &[xs, n("1")]), FUEL), n("6"));
    }

    #[test]
    fn a_stuck_term_keeps_its_shape() {
        let t = app("reverse", &[n("aa")]);
        assert_eq!(normalize_aterm(&[], &t, FUEL), t);
    }
}
