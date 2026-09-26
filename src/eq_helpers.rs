//! The structural equality helpers the IR asks for -- upstream's
//! `eq-helper-defs` (Emit/X86_64.codex, "Recursive Structural Equality
//! Helpers"), which `eq-attach-helpers` (opening.codex) appends to the IR
//! between the lambda lift and the prune.
//!
//! Lowering names a helper wherever `==` meets a generic or recursive type:
//! `__eq_Box@Text`, `__eq_List@Integer`. This pass mints the definitions: it
//! collects every helper the IR names (and every `==` whose operand needs
//! one), closes over the helpers those helpers' own fields need, and builds
//! each as an ordinary two-parameter definition. A list helper is two
//! definitions, an entry that compares lengths and a loop over an index.
//!
//! **THE ORDER IS PART OF THE WIRE.** The helpers are appended in the order
//! the collection meets them, and the collection walks the IR exactly as
//! `eq-collect-expr` does (a branch's body before its guard, a call's
//! function before its argument), so this walk is written out rather than
//! borrowed from `IrExpr::children`.
//!
//! U64's generic equality adds DICTIONARY-TAKING helpers, `__eqd_<T>`: the
//! helper for T at SLOT actuals (type variables at the top of the id range,
//! which no checker id reaches), taking one dictionary `__eqdict<i>` per slot
//! and comparing a field at slot i by calling it (`eqd-*`). Lowering names
//! one wherever a constrained body compares a type that holds its variable.

use std::collections::BTreeMap;

use crate::ast::Span;
use crate::check::{strip_forall, Binding, EffectRow, Ty, TypeDefs};
use crate::ir_chapter::{IrActStmt, IrBinOp, IrBranch, IrDef, IrExpr, IrParam, IrPat};
use crate::symbol::{Sym, SymTab};

/// `eq-rec-fuel`: the bound on a malformed type graph, not on this walk.
const FUEL: i64 = 64;

/// `eqd-slot-base`.
const SLOT_BASE: u32 = 4294967040;

fn slot_ty(i: usize) -> Ty {
    Ty::Var(SLOT_BASE + i as u32)
}

/// `eqd-slot-index`.
fn slot_index(t: &Ty) -> Option<u32> {
    match t {
        Ty::Var(id) if *id >= SLOT_BASE => Some(id - SLOT_BASE),
        _ => None,
    }
}

/// `eqd-mentions-slot`.
fn mentions_slot(t: &Ty, fuel: i64) -> bool {
    if fuel <= 0 {
        return false;
    }
    if slot_index(t).is_some() {
        return true;
    }
    match t {
        Ty::List(e) => mentions_slot(e, fuel - 1),
        Ty::Constructed(_, a) | Ty::Sum(_, a) | Ty::Record(_, a) => a.iter().any(|x| mentions_slot(x, fuel - 1)),
        _ => false,
    }
}

/// `eqd-type-args`.
fn eqd_type_args(t: &Ty) -> Vec<Ty> {
    match t {
        Ty::List(e) => vec![(**e).clone()],
        Ty::Constructed(_, a) | Ty::Sum(_, a) | Ty::Record(_, a) => a.clone(),
        _ => Vec::new(),
    }
}

/// `eqd-dict-ty`.
fn dict_ty(t: &Ty) -> Ty {
    fun(t.clone(), fun(t.clone(), Ty::Boolean))
}

/// `eqd-operand-ty`: the parameter of the last arrow before `Boolean`.
fn eqd_operand_ty(t: &Ty, fuel: i64) -> Ty {
    if fuel <= 0 {
        return Ty::Error;
    }
    match t {
        Ty::Fun(p, _, r) => match &**r {
            Ty::Fun(_, _, r2) if matches!(**r2, Ty::Boolean) => (**p).clone(),
            Ty::Fun(..) => eqd_operand_ty(r, fuel - 1),
            _ => Ty::Error,
        },
        _ => Ty::Error,
    }
}

fn syn() -> Span {
    Span::default()
}

fn int_default() -> Ty {
    Ty::Integer(i64::MIN, i64::MAX, crate::check::Overflow::Error)
}

fn fun(a: Ty, r: Ty) -> Ty {
    Ty::Fun(Box::new(a), EffectRow::default(), Box::new(r))
}

fn strip_unit(t: &Ty) -> Ty {
    match t {
        Ty::Unit(_, b) => strip_unit(b),
        other => other.clone(),
    }
}

/// A type resolved against the chapter's declarations, as
/// `resolve-to-sum-with-defs` answers it: a sum with its constructors, a
/// record with its fields, each field at the declaration's own variables.
#[derive(Clone)]
enum Resolved {
    Sum { name: Sym, args: Vec<Ty>, formals: Vec<Ty>, ctors: Vec<(Sym, Vec<Ty>)> },
    Record { name: Sym, formals: Vec<Ty>, fields: Vec<(Sym, Ty)> },
    List(Ty),
    Other,
}

/// `EqHelperReq`.
#[derive(Clone)]
struct Req {
    /// `eq-req-is-dict`: its first actual is slot 0.
    dict: bool,
    /// `eq-req-name`: the INSTANTIATED name, which is the key.
    key: String,
    /// The type the helper's parameters take.
    ty: Ty,
    actuals: Vec<Ty>,
    kind: Resolved,
}

struct Cx<'a> {
    syms: &'a SymTab,
    tds: &'a TypeDefs,
    types: BTreeMap<Sym, Ty>,
}

impl Cx<'_> {
    fn text(&self, n: Sym) -> String {
        self.syms.text(n).to_string()
    }

    /// `resolve-to-sum-with-defs`, over the chapter's declarations and the
    /// constructors' checked types.
    fn resolve(&self, t: &Ty) -> Resolved {
        match strip_unit(t) {
            Ty::List(e) => Resolved::List(*e),
            Ty::Sum(n, args) | Ty::Constructed(n, args) | Ty::Record(n, args) => {
                if let Some(cs) = self.tds.ctors(n) {
                    // Each constructor's type is quantified on its own, so
                    // `Just` and `None` name the parameter by different
                    // variables: every constructor's fields are put in the
                    // FIRST one's variables, position by position.
                    let mut formals: Option<Vec<Ty>> = None;
                    let mut ctors = Vec::new();
                    for c in cs {
                        let Some(ct) = self.types.get(c) else { return Resolved::Other };
                        let (fields, result) = spine(ct);
                        let rargs = match &result {
                            Ty::Sum(_, r) | Ty::Constructed(_, r) => r.clone(),
                            _ => Vec::new(),
                        };
                        let canon = formals.get_or_insert_with(|| rargs.clone()).clone();
                        let fields = if rargs == canon { fields } else { subst_fields(&fields, &rargs, &canon) };
                        ctors.push((*c, fields));
                    }
                    let formals = formals.unwrap_or_default();
                    Resolved::Sum { name: n, args, formals, ctors }
                } else if let Some(fs) = self.tds.record_fields(n) {
                    let names: Vec<Sym> = fs.iter().map(|(f, _)| *f).collect();
                    let Some(ct) = self.types.get(&n) else { return Resolved::Other };
                    let (tys, result) = spine(ct);
                    let formals = match result {
                        Ty::Record(_, rargs) | Ty::Constructed(_, rargs) => rargs,
                        _ => Vec::new(),
                    };
                    Resolved::Record { name: n, formals, fields: names.into_iter().zip(tys).collect() }
                } else {
                    Resolved::Other
                }
            }
            _ => Resolved::Other,
        }
    }

    /// `eq-key-of`.
    fn key_of(&self, t: &Ty) -> String {
        let wrap = |a: &[Ty]| -> String {
            if a.is_empty() {
                String::new()
            } else {
                format!("[{}]", a.iter().map(|x| self.key_of(x)).collect::<Vec<_>>().join(","))
            }
        };
        match strip_unit(t) {
            Ty::Text => "Text".into(),
            Ty::Boolean => "Boolean".into(),
            Ty::Char => "Char".into(),
            Ty::Integer(..) => "Integer".into(),
            Ty::Real(crate::check::RealWidth::F32, _) => "Real32".into(),
            Ty::Real(..) => "Real64".into(),
            Ty::List(e) => format!("List[{}]", self.key_of(&e)),
            Ty::LinkedList(e) => format!("LinkedList[{}]", self.key_of(&e)),
            Ty::Sum(n, a) | Ty::Record(n, a) | Ty::Constructed(n, a) => format!("{}{}", self.text(n), wrap(&a)),
            Ty::Var(id) => format!("#{id}"),
            _ => "?".into(),
        }
    }

    /// `eq-helper-name-inst`.
    fn name_inst(&self, sn: &str, actuals: &[Ty]) -> String {
        if actuals.is_empty() {
            format!("__eq_{sn}")
        } else {
            format!("__eq_{sn}@{}", actuals.iter().map(|a| self.key_of(a)).collect::<Vec<_>>().join(","))
        }
    }

    /// `eq-ty-reaches`.
    fn reaches(&self, t: &Ty, target: Sym, seen: &mut Vec<Sym>, fuel: i64) -> bool {
        if fuel <= 0 {
            return true;
        }
        match self.resolve(t) {
            Resolved::Sum { name, ctors, .. } => {
                if name == target {
                    return true;
                }
                if seen.contains(&name) {
                    return false;
                }
                seen.push(name);
                ctors.iter().any(|(_, fs)| fs.iter().any(|f| self.reaches(f, target, seen, fuel - 1)))
            }
            _ => false,
        }
    }

    /// `eq-sum-is-recursive`.
    fn is_recursive(&self, sn: Sym, ctors: &[(Sym, Vec<Ty>)]) -> bool {
        let mut seen = vec![sn];
        ctors.iter().any(|(_, fs)| fs.iter().any(|f| self.reaches(f, sn, &mut seen, FUEL - 1)))
    }

    /// `eq-needs-inst-helper`.
    fn needs_inst(&self, sn: Sym, ctors: &[(Sym, Vec<Ty>)], actuals: &[Ty]) -> bool {
        self.is_recursive(sn, ctors) || !actuals.is_empty()
    }
}

/// An arrow's parameter types and its final result, quantifiers dropped.
fn spine(t: &Ty) -> (Vec<Ty>, Ty) {
    let mut cur = strip_forall(t);
    let mut ps = Vec::new();
    while let Ty::Fun(a, _, r) = cur {
        ps.push(*a);
        cur = *r;
    }
    (ps, cur)
}

/// `eq-site-actuals`: the actuals a site's type spells, read off a
/// constructed type or a list only.
fn site_actuals(t: &Ty) -> Vec<Ty> {
    match t {
        Ty::Constructed(_, a) => a.clone(),
        Ty::List(e) => vec![(**e).clone()],
        _ => Vec::new(),
    }
}

/// `subst-field-type` over `eq-subst-deep`: a declaration's variable, by
/// position among the formals, becomes the matching actual, through
/// constructed types and lists.
fn subst_deep(t: &Ty, formals: &[Ty], actuals: &[Ty], fuel: i64) -> Ty {
    if fuel <= 0 {
        return t.clone();
    }
    match t {
        Ty::Var(_) => match formals.iter().position(|f| f == t) {
            Some(i) if i < actuals.len() => actuals[i].clone(),
            _ => t.clone(),
        },
        Ty::Constructed(n, a) if !a.is_empty() => {
            Ty::Constructed(*n, a.iter().map(|x| subst_deep(x, formals, actuals, fuel - 1)).collect())
        }
        Ty::Sum(n, a) if !a.is_empty() => Ty::Sum(*n, a.iter().map(|x| subst_deep(x, formals, actuals, fuel - 1)).collect()),
        Ty::Record(n, a) if !a.is_empty() => {
            Ty::Record(*n, a.iter().map(|x| subst_deep(x, formals, actuals, fuel - 1)).collect())
        }
        Ty::List(e) => Ty::List(Box::new(subst_deep(e, formals, actuals, fuel - 1))),
        Ty::LinkedList(e) => Ty::LinkedList(Box::new(subst_deep(e, formals, actuals, fuel - 1))),
        other => other.clone(),
    }
}

/// `eq-subst-fields`.
fn subst_fields(fs: &[Ty], formals: &[Ty], actuals: &[Ty]) -> Vec<Ty> {
    if actuals.is_empty() {
        fs.to_vec()
    } else {
        fs.iter().map(|f| subst_deep(f, formals, actuals, FUEL)).collect()
    }
}

struct Collector<'a, 'b> {
    cx: &'a Cx<'b>,
    reqs: Vec<Req>,
}

impl Collector<'_, '_> {
    fn has(&self, key: &str) -> bool {
        self.reqs.iter().any(|r| r.key == key)
    }

    /// `eq-note-site`.
    fn note_site(&mut self, ty: &Ty, fuel: i64) {
        if fuel <= 0 {
            return;
        }
        if mentions_slot(ty, fuel) {
            self.note_slotted(ty, fuel);
            return;
        }
        let actuals = site_actuals(ty);
        let resolved = self.cx.resolve(ty);
        match &resolved {
            Resolved::Sum { name, args, ctors, .. } => {
                if self.cx.needs_inst(*name, ctors, &actuals) {
                    let key = self.cx.name_inst(&self.cx.text(*name), &actuals);
                    if !self.has(&key) {
                        let sty = strip_unit(ty);
                        let sty = match sty {
                            Ty::Constructed(n, a) => Ty::Sum(n, a),
                            other => other,
                        };
                        self.reqs.push(Req { dict: false, key, ty: sty, actuals, kind: resolved.clone() });
                    }
                } else {
                    self.site_ctors(&ctors.clone(), fuel - 1, &args.clone(), &actuals);
                }
            }
            Resolved::List(e) => {
                let key = self.cx.name_inst("List", std::slice::from_ref(e));
                if !self.has(&key) {
                    self.reqs.push(Req { dict: false, key, ty: Ty::List(Box::new(e.clone())), actuals: vec![e.clone()], kind: resolved.clone() });
                    self.note_site(&e.clone(), fuel - 1);
                }
            }
            Resolved::Record { name, .. } => {
                if actuals.is_empty() {
                    return;
                }
                let key = self.cx.name_inst(&self.cx.text(*name), &actuals);
                if !self.has(&key) {
                    self.reqs.push(Req { dict: false, key, ty: Ty::Record(*name, actuals.clone()), actuals, kind: resolved.clone() });
                }
            }
            Resolved::Other => {}
        }
    }

    /// `eqd-request`: the canonical `__eqd_<T>`, at slots 0..k-1.
    fn eqd_request(&mut self, t: &Ty) {
        let resolved = self.cx.resolve(t);
        match &resolved {
            Resolved::List(_) => {
                let key = "__eqd_List".to_string();
                if !self.has(&key) {
                    let s0 = slot_ty(0);
                    self.reqs.push(Req { dict: true, key, ty: Ty::List(Box::new(s0.clone())), actuals: vec![s0.clone()], kind: Resolved::List(s0) });
                }
            }
            Resolved::Sum { name, formals, .. } | Resolved::Record { name, formals, .. } => {
                let key = format!("__eqd_{}", self.cx.text(*name));
                if formals.is_empty() || self.has(&key) {
                    return;
                }
                let slots: Vec<Ty> = (0..formals.len()).map(slot_ty).collect();
                let ty = match &resolved {
                    Resolved::Sum { .. } => Ty::Sum(*name, slots.clone()),
                    _ => Ty::Record(*name, slots.clone()),
                };
                self.reqs.push(Req { dict: true, key, ty, actuals: slots, kind: resolved.clone() });
            }
            Resolved::Other => {}
        }
    }

    /// `eqd-note-slotted`: request the type's own `__eqd_`, and note its
    /// slot-free arguments as ordinary sites.
    fn note_slotted(&mut self, ty: &Ty, fuel: i64) {
        if slot_index(ty).is_some() {
            return;
        }
        self.eqd_request(ty);
        for a in eqd_type_args(ty) {
            if !mentions_slot(&a, FUEL) {
                self.note_site(&a, fuel - 1);
            }
        }
    }

    /// `eq-site-ctors` over `eq-site-fields`.
    fn site_ctors(&mut self, ctors: &[(Sym, Vec<Ty>)], fuel: i64, formals: &[Ty], actuals: &[Ty]) {
        for (_, fs) in ctors {
            for f in subst_fields(fs, formals, actuals) {
                self.note_site(&f, fuel);
            }
        }
    }

    fn is_inst_name(&self, n: Sym) -> bool {
        let t = self.cx.syms.text(n);
        t.starts_with("__eq_") && t.contains('@')
    }

    /// `eq-collect-expr`.
    fn expr(&mut self, e: &IrExpr) {
        use IrExpr as E;
        match e {
            E::IntLit(..) | E::NumLit(..) | E::TextLit(..) | E::BoolLit(..) | E::CharLit(..) => {}
            E::Name(n, ty, _) => {
                if self.is_inst_name(*n) {
                    if let Ty::Fun(p, _, _) = strip_forall(ty) {
                        self.note_site(&p, FUEL);
                    }
                } else if self.cx.syms.text(*n).starts_with("__eqd_") {
                    self.eqd_request(&eqd_operand_ty(ty, FUEL));
                }
            }
            E::Binary(op, l, r, _, _) => {
                if matches!(op, IrBinOp::Eq | IrBinOp::NotEq) {
                    self.note_site(&l.ty(), FUEL);
                }
                self.expr(l);
                self.expr(r);
            }
            E::Negate(x, ..) => self.expr(x),
            E::If(c, t, el, ..) => {
                self.expr(c);
                self.expr(t);
                self.expr(el);
            }
            E::Let(_, _, v, b, _) => {
                self.expr(v);
                self.expr(b);
            }
            E::Apply(f, a, ..) => {
                if let E::Name(n, _, _) = &**f {
                    if self.is_inst_name(*n) {
                        self.note_site(&a.ty(), FUEL);
                    }
                }
                self.expr(f);
                self.expr(a);
            }
            E::Lambda(_, body, ..) => self.expr(body),
            E::List(es, ..) => es.iter().for_each(|x| self.expr(x)),
            E::Match(sc, bs, ..) => {
                self.expr(sc);
                for b in bs {
                    self.expr(&b.body);
                    self.expr(&b.guard);
                }
            }
            E::Act(ss, ..) => self.stmts(ss),
            E::Handle(_, h, cs, ..) => {
                self.expr(h);
                cs.iter().for_each(|c| self.expr(&c.body));
            }
            E::WithTimeout(_, _, _, body, ..) => self.expr(body),
            E::Record(_, fs, ..) => fs.iter().for_each(|f| self.expr(&f.value)),
            E::FieldAccess(r, ..) => self.expr(r),
            E::FieldStore(r, _, v, ..) => {
                self.expr(r);
                self.expr(v);
            }
            E::Try(_, body, fb, fail, ..) => {
                self.stmts(body);
                self.stmts(fb);
                self.stmts(fail);
            }
        }
    }

    fn stmts(&mut self, ss: &[IrActStmt]) {
        ss.iter().for_each(|s| self.expr(s.expr()));
    }

    /// `eq-close-reqs`: a worklist over a list that grows as it is walked.
    fn close(&mut self) {
        let mut i = 0;
        while i < self.reqs.len() {
            let r = self.reqs[i].clone();
            match &r.kind {
                Resolved::Record { formals, fields, .. } => {
                    let tys: Vec<Ty> = fields.iter().map(|(_, t)| t.clone()).collect();
                    for f in subst_fields(&tys, formals, &r.actuals) {
                        self.note_site(&f, FUEL);
                    }
                }
                Resolved::Sum { formals, ctors, .. } => {
                    self.site_ctors(ctors, FUEL, formals, &r.actuals);
                }
                _ => {}
            }
            i += 1;
        }
    }
}

struct Builder<'a, 'b> {
    cx: &'a Cx<'b>,
    syms: &'a mut SymTab,
}

impl Builder<'_, '_> {
    fn sym(&mut self, s: &str) -> Sym {
        self.syms.intern(s)
    }

    fn name(&mut self, n: &str, ty: Ty) -> IrExpr {
        IrExpr::Name(self.sym(n), ty, syn())
    }

    fn call2(&mut self, n: &str, opty: &Ty, l: IrExpr, r: IrExpr) -> IrExpr {
        let hty = fun(opty.clone(), fun(opty.clone(), Ty::Boolean));
        let inner = IrExpr::Apply(Box::new(self.name(n, hty)), Box::new(l), fun(opty.clone(), Ty::Boolean), syn());
        IrExpr::Apply(Box::new(inner), Box::new(r), Ty::Boolean, syn())
    }

    /// `eqd-dict-params` / `eqd-dict-args`: one dictionary per slot.
    fn dict_params(req: &Req) -> Vec<(String, Ty)> {
        if !req.dict {
            return Vec::new();
        }
        req.actuals.iter().map(|a| (format!("__eqdict{}", slot_index(a).unwrap_or(0)), dict_ty(a))).collect()
    }

    fn dict_args(&mut self, req: &Req) -> Vec<IrExpr> {
        Self::dict_params(req).into_iter().map(|(n, t)| self.name(&n, t)).collect()
    }

    /// `eqd-concrete-dict`: the dictionary for a slot-free type.
    fn concrete_dict(&mut self, t: &Ty) -> IrExpr {
        let nm = match self.cx.resolve(t) {
            Resolved::List(e) => Some(self.cx.name_inst("List", &[e])),
            Resolved::Sum { name, .. } | Resolved::Record { name, .. } => {
                let acts = site_actuals(t);
                Some(if acts.is_empty() { format!("__eq_{}", self.cx.text(name)) } else { self.cx.name_inst(&self.cx.text(name), &acts) })
            }
            Resolved::Other => match strip_unit(t) {
                Ty::Integer(..) => Some("__eq_Integer".into()),
                Ty::Text => Some("__eq_Text".into()),
                Ty::Boolean => Some("__eq_Boolean".into()),
                Ty::Char => Some("__eq_Char".into()),
                _ => None,
            },
        };
        match nm {
            Some(n) => self.name(&n, dict_ty(t)),
            None => self.name("__eqd-no-equality", dict_ty(t)),
        }
    }

    /// `eqd-arg-dict`.
    fn arg_dict(&mut self, t: &Ty) -> IrExpr {
        match slot_index(t) {
            Some(i) => self.name(&format!("__eqdict{i}"), dict_ty(t)),
            None => self.concrete_dict(t),
        }
    }

    /// `eqd-helper-ref`.
    fn helper_ref(&mut self, tn: &str, dicts: Vec<IrExpr>, t: &Ty) -> IrExpr {
        let mut full = dict_ty(t);
        for d in dicts.iter().rev() {
            full = fun(d.ty(), full);
        }
        let mut f = self.name(&format!("__eqd_{tn}"), full.clone());
        let mut fty = full;
        for d in dicts {
            let rty = match &fty {
                Ty::Fun(_, _, r) => (**r).clone(),
                other => other.clone(),
            };
            f = IrExpr::Apply(Box::new(f), Box::new(d), rty.clone(), syn());
            fty = rty;
        }
        f
    }

    /// `eqd-field-eq`: a field whose type holds a slot, through a dictionary.
    fn eqd_field_eq(&mut self, fty: &Ty, l: IrExpr, r: IrExpr) -> IrExpr {
        let dict = if slot_index(fty).is_some() {
            self.arg_dict(fty)
        } else {
            let tn = match self.cx.resolve(fty) {
                Resolved::List(_) => "List".to_string(),
                Resolved::Sum { name, .. } | Resolved::Record { name, .. } => self.cx.text(name),
                Resolved::Other => String::new(),
            };
            let args: Vec<IrExpr> = eqd_type_args(fty).iter().map(|a| self.arg_dict(a)).collect();
            self.helper_ref(&tn, args, fty)
        };
        let inner = IrExpr::Apply(Box::new(dict), Box::new(l), fun(fty.clone(), Ty::Boolean), syn());
        IrExpr::Apply(Box::new(inner), Box::new(r), Ty::Boolean, syn())
    }

    /// `eq-helper-field-eq`.
    fn field_eq(&mut self, fty: &Ty, l: IrExpr, r: IrExpr) -> IrExpr {
        if mentions_slot(fty, FUEL) {
            return self.eqd_field_eq(fty, l, r);
        }
        let plain = |l, r| IrExpr::Binary(IrBinOp::Eq, Box::new(l), Box::new(r), Ty::Boolean, syn());
        match self.cx.resolve(fty) {
            Resolved::List(e) => {
                let hname = self.cx.name_inst("List", &[e]);
                let resolved = strip_unit(fty);
                self.call2(&hname, &resolved, l, r)
            }
            Resolved::Sum { name, ctors, .. } => {
                let actuals = site_actuals(fty);
                if self.cx.needs_inst(name, &ctors, &actuals) {
                    let hname = self.cx.name_inst(&self.cx.text(name), &actuals);
                    self.call2(&hname, fty, l, r)
                } else {
                    plain(l, r)
                }
            }
            Resolved::Record { name, .. } => {
                let actuals = site_actuals(fty);
                if actuals.is_empty() {
                    plain(l, r)
                } else {
                    let hname = self.cx.name_inst(&self.cx.text(name), &actuals);
                    self.call2(&hname, fty, l, r)
                }
            }
            Resolved::Other => plain(l, r),
        }
    }

    /// `eq-helper-field-conj`: the fields' comparisons joined by `and`, the
    /// last one bare, `True` for none.
    fn conj(&mut self, fs: &[Ty], i: usize) -> IrExpr {
        if i >= fs.len() {
            return IrExpr::BoolLit(true, syn());
        }
        let l = self.name(&format!("__eqx{i}"), fs[i].clone());
        let r = self.name(&format!("__eqy{i}"), fs[i].clone());
        let one = self.field_eq(&fs[i].clone(), l, r);
        if i + 1 >= fs.len() {
            one
        } else {
            let rest = self.conj(fs, i + 1);
            IrExpr::Binary(IrBinOp::And, Box::new(one), Box::new(rest), Ty::Boolean, syn())
        }
    }

    fn pats(&mut self, fs: &[Ty], prefix: &str) -> Vec<IrPat> {
        fs.iter().enumerate().map(|(i, f)| IrPat::Var(self.sym(&format!("{prefix}{i}")), f.clone(), syn())).collect()
    }

    fn branch(pattern: IrPat, body: IrExpr) -> IrBranch {
        IrBranch { pattern, body, guard: IrExpr::BoolLit(true, syn()), span: syn() }
    }

    fn def(&mut self, req: &Req, name: &str, params: Vec<(&str, Ty)>, body: IrExpr) -> IrDef {
        let mut all: Vec<(String, Ty)> = Self::dict_params(req);
        all.extend(params.into_iter().map(|(n, t)| (n.to_string(), t)));
        IrDef {
            name: self.sym(name),
            params: all.into_iter().map(|(n, t)| IrParam { name: self.syms.intern(&n), ty: t, span: syn() }).collect(),
            ty: Ty::Boolean,
            body,
            chapter_slug: String::new(),
            origin: String::new(),
            span: syn(),
            is_punctual: false,
            wcet_budget: 0,
            unique_params: Vec::new(),
        }
    }

    /// `eq-helper-def`: a match on `__eqa` whose every arm matches `__eqb`
    /// against the same constructor and compares the fields.
    fn sum_def(&mut self, req: &Req) -> IrDef {
        let Resolved::Sum { formals, ctors, .. } = &req.kind else { unreachable!() };
        let cs: Vec<(Sym, Vec<Ty>)> = ctors.iter().map(|(c, fs)| (*c, subst_fields(fs, formals, &req.actuals))).collect();
        let sty = req.ty.clone();
        let mut outer = Vec::new();
        for (c, fs) in &cs {
            let ypats = self.pats(fs, "__eqy");
            let conj = self.conj(fs, 0);
            let eqb = self.name("__eqb", sty.clone());
            let inner = IrExpr::Match(
                Box::new(eqb),
                vec![
                    Self::branch(IrPat::Ctor(*c, ypats, sty.clone(), syn()), conj),
                    Self::branch(IrPat::Wild(syn()), IrExpr::BoolLit(false, syn())),
                ],
                Ty::Boolean,
                syn(),
            );
            let xpats = self.pats(fs, "__eqx");
            outer.push(Self::branch(IrPat::Ctor(*c, xpats, sty.clone(), syn()), inner));
        }
        let eqa = self.name("__eqa", sty.clone());
        let body = IrExpr::Match(Box::new(eqa), outer, Ty::Boolean, syn());
        self.def(req, &req.key, vec![("__eqa", sty.clone()), ("__eqb", sty)], body)
    }

    /// `eq-record-helper-def`: the fields' comparisons, by field access.
    fn record_def(&mut self, req: &Req) -> IrDef {
        let Resolved::Record { formals, fields, .. } = &req.kind else { unreachable!() };
        let tys: Vec<Ty> = fields.iter().map(|(_, t)| t.clone()).collect();
        let tys = subst_fields(&tys, formals, &req.actuals);
        let rty = req.ty.clone();
        // The wire spells a field with its SLOT, `"left/0"`, as lowering does.
        let names: Vec<String> = fields.iter().enumerate().map(|(i, (f, _))| format!("{}/{i}", self.cx.text(*f))).collect();
        let body = self.record_conj(&names, &tys, &rty, 0);
        self.def(req, &req.key, vec![("__eqa", rty.clone()), ("__eqb", rty)], body)
    }

    fn record_conj(&mut self, names: &[String], tys: &[Ty], rty: &Ty, i: usize) -> IrExpr {
        if i >= tys.len() {
            return IrExpr::BoolLit(true, syn());
        }
        let a = self.name("__eqa", rty.clone());
        let b = self.name("__eqb", rty.clone());
        let l = IrExpr::FieldAccess(Box::new(a), names[i].clone(), tys[i].clone(), syn());
        let r = IrExpr::FieldAccess(Box::new(b), names[i].clone(), tys[i].clone(), syn());
        let one = self.field_eq(&tys[i].clone(), l, r);
        if i + 1 >= tys.len() {
            one
        } else {
            let rest = self.record_conj(names, tys, rty, i + 1);
            IrExpr::Binary(IrBinOp::And, Box::new(one), Box::new(rest), Ty::Boolean, syn())
        }
    }

    fn call1(&mut self, n: &str, aty: &Ty, rty: &Ty, x: IrExpr) -> IrExpr {
        let f = self.name(n, fun(aty.clone(), rty.clone()));
        IrExpr::Apply(Box::new(f), Box::new(x), rty.clone(), syn())
    }

    /// `eq-list-loop-call`: `<loop> xs ys i n`.
    fn loop_call(&mut self, req: &Req, xs: IrExpr, ys: IrExpr, i: IrExpr, n: IrExpr) -> IrExpr {
        let lty = req.ty.clone();
        let int = int_default();
        let t3 = fun(int.clone(), fun(int.clone(), Ty::Boolean));
        let t2 = fun(lty.clone(), t3.clone());
        let t1 = fun(lty, t2.clone());
        let dicts = self.dict_args(req);
        let mut t0 = t1;
        for d in dicts.iter().rev() {
            t0 = fun(d.ty(), t0);
        }
        let mut f = self.name(&format!("{}__loop", req.key), t0.clone());
        let mut fty = t0;
        for d in dicts {
            let rty = match &fty {
                Ty::Fun(_, _, r) => (**r).clone(),
                other => other.clone(),
            };
            f = IrExpr::Apply(Box::new(f), Box::new(d), rty.clone(), syn());
            fty = rty;
        }
        let a1 = IrExpr::Apply(Box::new(f), Box::new(xs), t2, syn());
        let a2 = IrExpr::Apply(Box::new(a1), Box::new(ys), t3, syn());
        let a3 = IrExpr::Apply(Box::new(a2), Box::new(i), fun(int, Ty::Boolean), syn());
        IrExpr::Apply(Box::new(a3), Box::new(n), Ty::Boolean, syn())
    }

    /// `eq-list-helper-def` and `eq-list-loop-def`: the entry compares the
    /// lengths and hands off; the loop compares one element pair and calls
    /// itself.
    fn list_defs(&mut self, req: &Req) -> (IrDef, IrDef) {
        let lty = req.ty.clone();
        let int = int_default();
        let a = self.name("__eqa", lty.clone());
        let lena = self.call1("list-length", &lty, &int, a);
        let b = self.name("__eqb", lty.clone());
        let lenb = self.call1("list-length", &lty, &int, b);
        let same = IrExpr::Binary(IrBinOp::Eq, Box::new(lena), Box::new(lenb), Ty::Boolean, syn());
        let a2 = self.name("__eqa", lty.clone());
        let len_again = self.call1("list-length", &lty, &int, a2);
        let (xs, ys) = (self.name("__eqa", lty.clone()), self.name("__eqb", lty.clone()));
        let walk = self.loop_call(req, xs, ys, IrExpr::IntLit(0, syn()), len_again);
        let entry = IrExpr::If(Box::new(same), Box::new(walk), Box::new(IrExpr::BoolLit(false, syn())), Ty::Boolean, syn());
        let entry = self.def(req, &req.key, vec![("__eqa", lty.clone()), ("__eqb", lty.clone())], entry);

        let ety = match &lty {
            Ty::List(e) => (**e).clone(),
            _ => Ty::Error,
        };
        let i = self.name("__eqi", int.clone());
        let n = self.name("__eqn", int.clone());
        let done = IrExpr::Binary(IrBinOp::GtEq, Box::new(i.clone()), Box::new(n.clone()), Ty::Boolean, syn());
        let at = |s: &mut Self, list: &str| {
            let xs = s.name(list, lty.clone());
            let f = s.name("list-at", fun(lty.clone(), fun(int.clone(), ety.clone())));
            let inner = IrExpr::Apply(Box::new(f), Box::new(xs), fun(int.clone(), ety.clone()), syn());
            IrExpr::Apply(Box::new(inner), Box::new(i.clone()), ety.clone(), syn())
        };
        let lhs = at(self, "__eqa");
        let rhs = at(self, "__eqb");
        let one = self.field_eq(&ety, lhs, rhs);
        let next_i = IrExpr::Binary(IrBinOp::AddInt, Box::new(i.clone()), Box::new(IrExpr::IntLit(1, syn())), int.clone(), syn());
        let (xs, ys) = (self.name("__eqa", lty.clone()), self.name("__eqb", lty.clone()));
        let next = self.loop_call(req, xs, ys, next_i, n.clone());
        let inner_if = IrExpr::If(Box::new(one), Box::new(next), Box::new(IrExpr::BoolLit(false, syn())), Ty::Boolean, syn());
        let body = IrExpr::If(Box::new(done), Box::new(IrExpr::BoolLit(true, syn())), Box::new(inner_if), Ty::Boolean, syn());
        let lp = self.def(
            req,
            &format!("{}__loop", req.key),
            vec![("__eqa", lty.clone()), ("__eqb", lty), ("__eqi", int.clone()), ("__eqn", int)],
            body,
        );
        (entry, lp)
    }
}

/// `eq-attach-helpers`: the definitions with every equality helper they
/// need appended, in the order `eq-helper-defs` builds them.
pub fn attach(defs: Vec<IrDef>, syms: &mut SymTab, tds: &TypeDefs, bindings: &[Binding]) -> Vec<IrDef> {
    let reqs = {
        let cx = Cx { syms, tds, types: bindings.iter().map(|b| (b.name, b.ty.clone())).collect() };
        let mut col = Collector { cx: &cx, reqs: Vec::new() };
        for d in &defs {
            col.expr(&d.body);
        }
        col.close();
        col.reqs
    };
    if reqs.is_empty() {
        return defs;
    }
    let table = syms.clone();
    let cx = Cx { syms: &table, tds, types: bindings.iter().map(|b| (b.name, b.ty.clone())).collect() };
    let mut b = Builder { cx: &cx, syms };
    let mut out = defs;
    for req in &reqs {
        match &req.kind {
            Resolved::List(_) => {
                let (entry, lp) = b.list_defs(req);
                out.push(entry);
                out.push(lp);
            }
            Resolved::Record { .. } => out.push(b.record_def(req)),
            Resolved::Sum { .. } => out.push(b.sum_def(req)),
            Resolved::Other => {}
        }
    }
    out
}
