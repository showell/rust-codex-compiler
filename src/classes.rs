//! Type-class desugaring after the dictionaries exist -- upstream's
//! `rewrite-constrained-defs` and `insert-dicts-at-call-sites`
//! (Ast/Desugarer.codex:1052-1440).
//!
//! A definition declared `C a => T` is rewritten by how many instances `C`
//! has: with one, the constraint is simply dropped; with more, the
//! definition takes a dictionary parameter `__C-dict : CDict a` first and
//! each method call `m x` becomes `(__C-dict.m-impl) x`. The derived
//! classes `Show` and `Ord` take instead a dictionary that IS the method,
//! `__d-Show-a : a -> Text`, and a `show x` on a parameter of the type
//! variable's type becomes `__d-Show-a x`. Every call of a rewritten
//! definition then passes its dictionary first: `__dict-of-C` for a class,
//! `__dderiv-Show` or `__dderiv-Ord` for the derived ones.

use std::rc::Rc;

use crate::ast::{ActStmt, Chapter, Def, Expr, LetBind, MatchArm, Name, Param, TypeExpr};
use crate::symbol::SymTab;

fn is_derived_class(name: &str) -> bool {
    matches!(name, "Show" | "Ord")
}

fn derived_method(cls: &str) -> &'static str {
    if cls == "Show" {
        "show"
    } else {
        "compare"
    }
}

fn synthetic() -> crate::ast::Span {
    crate::ast::Span::default()
}

fn named(syms: &mut SymTab, s: &str) -> TypeExpr {
    TypeExpr::Named(syms.intern(s), synthetic())
}

/// `derived-dict-type`: `a -> Text` for Show, `a, a -> Integer` for Ord.
fn derived_dict_type(cls: &str, tv: Name, syms: &mut SymTab) -> TypeExpr {
    let var = || TypeExpr::Named(tv, synthetic());
    if cls == "Show" {
        TypeExpr::Fun(Rc::new(var()), Rc::new(named(syms, "Text")), synthetic())
    } else {
        TypeExpr::Fun(
            Rc::new(var()),
            Rc::new(TypeExpr::Fun(Rc::new(var()), Rc::new(named(syms, "Integer")), synthetic())),
            synthetic(),
        )
    }
}

/// `first-param-is-tyvar`.
fn first_param_is_tyvar(body: &TypeExpr, tv: Name) -> bool {
    matches!(body, TypeExpr::Fun(p, _, _) if matches!(&**p, TypeExpr::Named(n, _) if *n == tv))
}

/// `collect-tyvar-param-names`: the parameters whose declared type is the
/// type variable.
fn tyvar_param_names(ty: &TypeExpr, params: &[Param], tv: Name) -> Vec<Name> {
    let mut out = Vec::new();
    let mut cur = ty;
    let mut i = 0;
    while let TypeExpr::Fun(p, r, _) = cur {
        if i >= params.len() {
            break;
        }
        if matches!(&**p, TypeExpr::Named(n, _) if *n == tv) {
            out.push(params[i].name);
        }
        cur = r;
        i += 1;
    }
    out
}

/// One rewrite over an expression's spine, applied to the forms upstream's
/// walks visit; a form they do not visit is left as it is.
struct Rewrite<'a> {
    on_apply: &'a dyn Fn(&Expr, &Expr, &Expr, crate::ast::Span) -> Option<Expr>,
    /// Upstream's derived walk descends into matches and act blocks; the
    /// class-method walk does not.
    deep: bool,
}

impl Rewrite<'_> {
    fn expr(&self, e: &Expr) -> Expr {
        match e {
            Expr::Apply(f, a, sp) => {
                let new_arg = self.expr(a);
                if let Some(out) = (self.on_apply)(e, f, &new_arg, *sp) {
                    return out;
                }
                match &**f {
                    Expr::NameRef(..) => Expr::Apply(f.clone(), Rc::new(new_arg), *sp),
                    _ => Expr::Apply(Rc::new(self.expr(f)), Rc::new(new_arg), *sp),
                }
            }
            Expr::Binary(l, op, r, sp) => Expr::Binary(Rc::new(self.expr(l)), *op, Rc::new(self.expr(r)), *sp),
            Expr::If(c, t, el, sp) => Expr::If(Rc::new(self.expr(c)), Rc::new(self.expr(t)), Rc::new(self.expr(el)), *sp),
            Expr::Let(binds, body, sp) => Expr::Let(
                binds.iter().map(|b| LetBind { name: b.name, value: self.expr(&b.value), span: b.span }).collect(),
                Rc::new(self.expr(body)),
                *sp,
            ),
            Expr::Match(sc, arms, sp) if self.deep => Expr::Match(
                Rc::new(self.expr(sc)),
                arms.iter()
                    .map(|a| MatchArm {
                        pattern: a.pattern.clone(),
                        body: self.expr(&a.body),
                        guard: a.guard.clone(),
                        span: a.span,
                        alt_group: a.alt_group,
                    })
                    .collect(),
                *sp,
            ),
            Expr::Act(stmts, sp) if self.deep => Expr::Act(
                stmts
                    .iter()
                    .map(|s| match s {
                        ActStmt::Exec(x, sp) => ActStmt::Exec(self.expr(x), *sp),
                        ActStmt::Bind(n, x, sp) => ActStmt::Bind(*n, self.expr(x), *sp),
                    })
                    .collect(),
                *sp,
            ),
            _ => e.clone(),
        }
    }
}

fn synth_def(syms: &mut SymTab, name: &str, params: &[&str], declared: TypeExpr, body: Expr) -> Def {
    Def {
        name: syms.intern(name),
        params: params.iter().map(|p| Param { name: syms.intern(p), span: synthetic() }).collect(),
        declared_type: vec![declared],
        body,
        chapter_slug: String::new(),
        origin: String::new(),
        span: synthetic(),
        is_claim: false,
        is_punctual: false,
        wcet_budget: 0,
        bounded_class: None,
    }
}

fn apply1(syms: &mut SymTab, f: &str, a: &str) -> Expr {
    Expr::Apply(
        Rc::new(Expr::NameRef(syms.intern(f), synthetic())),
        Rc::new(Expr::NameRef(syms.intern(a), synthetic())),
        synthetic(),
    )
}

/// `prim-show-wrapper`: `__show_T : T -> Text`, `__show_T (__w) = show __w`.
fn prim_show_wrapper(syms: &mut SymTab, tn: &str) -> Def {
    let declared = TypeExpr::Fun(Rc::new(named(syms, tn)), Rc::new(named(syms, "Text")), synthetic());
    let body = apply1(syms, "show", "__w");
    synth_def(syms, &format!("__show_{tn}"), &["__w"], declared, body)
}

/// `prim-compare-wrapper`: `__compare_T : T, T -> Integer`,
/// `__compare_T (__wx) (__wy) = compare __wx __wy`.
fn prim_compare_wrapper(syms: &mut SymTab, tn: &str) -> Def {
    let declared = TypeExpr::Fun(
        Rc::new(named(syms, tn)),
        Rc::new(TypeExpr::Fun(Rc::new(named(syms, tn)), Rc::new(named(syms, "Integer")), synthetic())),
        synthetic(),
    );
    let inner = apply1(syms, "compare", "__wx");
    let body = Expr::Apply(Rc::new(inner), Rc::new(Expr::NameRef(syms.intern("__wy"), synthetic())), synthetic());
    synth_def(syms, &format!("__compare_{tn}"), &["__wx", "__wy"], declared, body)
}

const PRIM_WRAPPER_TYPES: [&str; 4] = ["Integer", "Boolean", "Text", "Real"];

/// `rewrite-constrained-defs`, then `insert-dicts-at-call-sites`, then
/// `prepend-prim-wrappers`: a chapter with a definition that takes a
/// derived dictionary gets `__show_T` (or `__compare_T`) over the four
/// primitive types ahead of its own definitions, the compare wrappers
/// before the show wrappers. Upstream tests the constraint on the
/// pre-rewrite list, but the two paths that keep the definition drop the
/// constraint in place, so only the dictionary path leaves one to find.
pub fn apply(ch: &mut Chapter) {
    let Chapter { syms, defs, class_defs, instance_defs, .. } = ch;
    let instance_count = |cls: Name| instance_defs.iter().filter(|i| i.class_name == cls).count();
    // (definition, the dictionary its callers pass)
    let mut info: Vec<(Name, Name)> = Vec::new();
    let (mut has_show, mut has_ord) = (false, false);
    for d in defs.iter_mut() {
        let Some(TypeExpr::Constrained(cls, tv, body, _)) = d.declared_type.first().cloned() else { continue };
        let cls_text = syms.text(cls).to_string();
        let tv_text = syms.text(tv).to_string();
        if is_derived_class(&cls_text) {
            if !first_param_is_tyvar(&body, tv) {
                d.declared_type = vec![(*body).clone()];
                continue;
            }
            // `rewrite-derived-constrained`.
            let dict_param = syms.intern(&format!("__d-{cls_text}-{tv_text}"));
            let dict_ty = derived_dict_type(&cls_text, tv, syms);
            let method = syms.intern(derived_method(&cls_text));
            let tvp = tyvar_param_names(&body, &d.params, tv);
            let on_apply = |_: &Expr, f: &Expr, new_arg: &Expr, sp: crate::ast::Span| -> Option<Expr> {
                let Expr::NameRef(n, _) = f else { return None };
                if *n != method {
                    return None;
                }
                let arg_is_tyvar = matches!(new_arg, Expr::NameRef(a, _) if tvp.contains(a));
                Some(if arg_is_tyvar {
                    Expr::Apply(Rc::new(Expr::NameRef(dict_param, synthetic())), Rc::new(new_arg.clone()), sp)
                } else {
                    Expr::Apply(Rc::new(f.clone()), Rc::new(new_arg.clone()), sp)
                })
            };
            let body_expr = Rewrite { on_apply: &on_apply, deep: true }.expr(&d.body);
            d.body = body_expr;
            d.params.insert(0, Param { name: dict_param, span: synthetic() });
            d.declared_type = vec![TypeExpr::Fun(Rc::new(dict_ty), body.clone(), synthetic())];
            info.push((d.name, syms.intern(&format!("__dderiv-{cls_text}"))));
            if cls_text == "Show" {
                has_show = true;
            } else {
                has_ord = true;
            }
            continue;
        }
        if instance_count(cls) == 1 {
            d.declared_type = vec![(*body).clone()];
            continue;
        }
        // A class with several instances: the dictionary parameter and the
        // method calls through it.
        let dict_param = syms.intern(&format!("__{cls_text}-dict"));
        let methods: Vec<Name> = class_defs
            .iter()
            .filter(|c| c.name == cls)
            .flat_map(|c| c.methods.iter().map(|m| m.name))
            .collect();
        let impls: Vec<(Name, Name)> =
            methods.iter().map(|m| (*m, syms.intern(&format!("{}-impl", syms.text(*m))))).collect();
        let on_apply = |_: &Expr, f: &Expr, new_arg: &Expr, sp: crate::ast::Span| -> Option<Expr> {
            let Expr::NameRef(n, _) = f else { return None };
            let (_, field) = impls.iter().find(|(m, _)| m == n)?;
            let dict_ref = Expr::NameRef(dict_param, synthetic());
            let access = Expr::FieldAccess(Rc::new(dict_ref), *field, sp);
            Some(Expr::Apply(Rc::new(access), Rc::new(new_arg.clone()), sp))
        };
        let body_expr = Rewrite { on_apply: &on_apply, deep: false }.expr(&d.body);
        d.body = body_expr;
        d.params.insert(0, Param { name: dict_param, span: synthetic() });
        let dict_ty = TypeExpr::App(
            Rc::new(named(syms, &format!("{cls_text}Dict"))),
            vec![TypeExpr::Named(tv, synthetic())],
            synthetic(),
        );
        d.declared_type = vec![TypeExpr::Fun(Rc::new(dict_ty), body.clone(), synthetic())];
        // `collect-constrained-names` records a caller-side dictionary only
        // for a class with several instances; a class with none takes the
        // parameter and no caller passes one.
        if instance_count(cls) > 1 {
            info.push((d.name, syms.intern(&format!("__dict-of-{cls_text}"))));
        }
    }
    if !info.is_empty() {
        // `insert-dict-refs`: a call of a rewritten definition passes its
        // dictionary first.
        let on_apply = |_: &Expr, f: &Expr, new_arg: &Expr, sp: crate::ast::Span| -> Option<Expr> {
            let Expr::NameRef(n, _) = f else { return None };
            let (_, dict) = info.iter().find(|(d, _)| d == n)?;
            let with_dict = Expr::Apply(Rc::new(f.clone()), Rc::new(Expr::NameRef(*dict, synthetic())), sp);
            Some(Expr::Apply(Rc::new(with_dict), Rc::new(new_arg.clone()), sp))
        };
        let rw = Rewrite { on_apply: &on_apply, deep: true };
        for d in defs.iter_mut() {
            d.body = rw.expr(&d.body);
        }
    }
    let mut front: Vec<Def> = Vec::new();
    if has_ord {
        front.extend(PRIM_WRAPPER_TYPES.iter().map(|tn| prim_compare_wrapper(syms, tn)));
    }
    if has_show {
        front.extend(PRIM_WRAPPER_TYPES.iter().map(|tn| prim_show_wrapper(syms, tn)));
    }
    if !front.is_empty() {
        front.append(defs);
        *defs = front;
    }
}
