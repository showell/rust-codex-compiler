//! The name resolver's duplicate rules and the type-name walk, before any
//! definition is checked -- upstream's `Semantics/NameResolver.codex`
//! (CDX3001) and `check-all-type-arities` (TypeChecker.codex:4407: CDX3008,
//! CDX2032).
//!
//! Upstream resolves each chapter on its own, so a definition name that two
//! chapters of one unit both use is two definitions, not a duplicate; the
//! walk here groups definitions by the chapter they were written in. A
//! constructor or an effect operation carries no chapter, so those are
//! compared within their own type or effect only, which is the narrower
//! reading and invents nothing.

use std::collections::BTreeSet;

use crate::ast::{Chapter, Expr, Name, TypeDef, TypeExpr};
use crate::check::{Cdx, TypeDefs, UnifyState};
use crate::symbol::SymTab;

pub fn check(ch: &Chapter, tds: &TypeDefs, st: &mut UnifyState) {
    duplicates(ch, st);
    type_names(ch, tds, st);
}

fn dup(st: &mut UnifyState, msg: String) {
    st.error(Cdx::DUPLICATE_DEFINITION, msg);
}

/// `collect-top-level-names`, `check-type-name-dup`, `collect-variant-ctors`,
/// `collect-ops-of-effect`, `scope-add-clause-params`/`add-lambda-params`
/// and `resolve-let-binds`, in that order.
fn duplicates(ch: &Chapter, st: &mut UnifyState) {
    let syms = &ch.syms;
    let mut seen: BTreeSet<(&str, Name)> = BTreeSet::new();
    for d in &ch.defs {
        if !seen.insert((d.chapter_slug.as_str(), d.name)) {
            dup(st, format!("Duplicate definition: {}", syms.text(d.name)));
        }
    }
    let mut types: BTreeSet<Name> = BTreeSet::new();
    for td in &ch.type_defs {
        let (n, ctors) = match td {
            TypeDef::Record(n, ..) | TypeDef::Unit(n, ..) => (*n, None),
            TypeDef::Variant(n, _, cs, _) => (*n, Some(cs)),
        };
        if !types.insert(n) {
            dup(st, format!("Duplicate type definition: '{}' is already defined", syms.text(n)));
        }
        if let Some(cs) = ctors {
            let mut ctor_seen: BTreeSet<Name> = BTreeSet::new();
            for c in cs {
                if !ctor_seen.insert(c.name) {
                    dup(st, format!("Duplicate constructor: '{}' is already defined", syms.text(c.name)));
                }
            }
        }
    }
    for ed in &ch.effect_defs {
        let mut ops: BTreeSet<Name> = BTreeSet::new();
        for op in &ed.ops {
            if !ops.insert(op.name) {
                dup(st, format!("Effect operation '{}' conflicts with existing name", syms.text(op.name)));
            }
        }
    }
    for d in &ch.defs {
        params(d.params.iter().map(|p| p.name), syms, st);
        d.body.walk(&mut |e| match e {
            Expr::Lambda(ps, _, _) => params(ps.iter().copied(), syms, st),
            Expr::Handle(h) => {
                for c in &h.clauses {
                    params(std::iter::once(c.resume_name).chain(c.params.iter().copied()), syms, st);
                }
            }
            Expr::Let(binds, _, _) => {
                let mut seen: BTreeSet<Name> = BTreeSet::new();
                for b in binds {
                    if !seen.insert(b.name) {
                        dup(st, format!("Duplicate binding: '{}'", syms.text(b.name)));
                    }
                }
            }
            _ => {}
        });
    }
}

fn params(names: impl Iterator<Item = Name>, syms: &SymTab, st: &mut UnifyState) {
    let mut seen: BTreeSet<Name> = BTreeSet::new();
    for n in names {
        if !seen.insert(n) {
            dup(st, format!("Duplicate parameter: '{}'", syms.text(n)));
        }
    }
}

/// `check-all-type-arities`: every declared signature, then every type
/// definition's fields.
fn type_names(ch: &Chapter, tds: &TypeDefs, st: &mut UnifyState) {
    for d in &ch.defs {
        if let Some(t) = d.declared_type.first() {
            walk_type(t, ch, tds, st);
        }
    }
    for td in &ch.type_defs {
        match td {
            TypeDef::Variant(_, _, ctors, _) => {
                for c in ctors {
                    for f in &c.fields {
                        walk_type(f, ch, tds, st);
                    }
                }
            }
            TypeDef::Record(_, _, fields, _, _) => {
                for f in fields {
                    walk_type(&f.type_expr, ch, tds, st);
                }
            }
            TypeDef::Unit(_, base, _) => walk_type(base, ch, tds, st),
        }
    }
}

/// `builtin-type-name`.
fn builtin_type_name(name: &str) -> bool {
    matches!(
        name,
        "Integer" | "Real" | "Text" | "Boolean" | "Char" | "Nothing" | "Proof" | "List" | "LinkedList" | "Vector"
    )
}

/// `type-name-known`: a lowercase name is a parameter, a builtin is known,
/// and anything else must be declared in the unit.
fn type_name_known(n: Name, ch: &Chapter, tds: &TypeDefs) -> bool {
    let name = ch.syms.text(n);
    match name.chars().next() {
        None => true,
        Some(c) if !c.is_ascii_uppercase() => true,
        _ => builtin_type_name(name) || tds.has(n),
    }
}

fn check_exists(n: Name, ch: &Chapter, tds: &TypeDefs, st: &mut UnifyState) {
    if !type_name_known(n, ch, tds) {
        st.error(Cdx::UNDEFINED_TYPE_NAME, format!("Undefined type name: {}", ch.syms.text(n)));
    }
}

/// `expected-arity-for`: `List` and `LinkedList` take one; a declared record
/// or variant takes its parameters; anything else is not checked.
fn expected_arity(n: Name, ch: &Chapter) -> Option<usize> {
    match ch.syms.text(n) {
        "List" | "LinkedList" => Some(1),
        _ => ch.type_defs.iter().find_map(|td| match td {
            TypeDef::Record(rn, ps, ..) | TypeDef::Variant(rn, ps, ..) if *rn == n => Some(ps.len()),
            _ => None,
        }),
    }
}

/// `check-arity-in-expr`. An equality, a for-all, a bounded integer and a
/// constraint are not walked, as upstream's `otherwise` arm has it.
fn walk_type(t: &TypeExpr, ch: &Chapter, tds: &TypeDefs, st: &mut UnifyState) {
    match t {
        TypeExpr::Named(n, _) => check_exists(*n, ch, tds, st),
        TypeExpr::App(..) => {
            let (head, args) = flatten(t);
            if let TypeExpr::Named(n, _) = head {
                check_exists(*n, ch, tds, st);
                if let Some(expected) = expected_arity(*n, ch) {
                    if args.len() != expected {
                        st.error(
                            Cdx::TYPE_ARITY,
                            format!(
                                "Type '{}' expects {} type argument(s), got {}",
                                ch.syms.text(*n),
                                expected,
                                args.len()
                            ),
                        );
                    }
                }
            }
            for a in args {
                walk_type(a, ch, tds, st);
            }
        }
        TypeExpr::Fun(p, r, _) => {
            walk_type(p, ch, tds, st);
            walk_type(r, ch, tds, st);
        }
        TypeExpr::Effect(_, _, _, ret, _) => walk_type(ret, ch, tds, st),
        TypeExpr::Linear(inner, _) => walk_type(inner, ch, tds, st),
        _ => {}
    }
}

/// `flatten-app`: the head under nested applications, and every argument
/// in order.
fn flatten(t: &TypeExpr) -> (&TypeExpr, Vec<&TypeExpr>) {
    match t {
        TypeExpr::App(ctor, args, _) => {
            let (head, mut inner) = flatten(ctor);
            inner.extend(args.iter());
            (head, inner)
        }
        other => (other, Vec::new()),
    }
}
