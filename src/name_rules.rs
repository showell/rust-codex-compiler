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
    type_syntax(ch, st);
    duplicates(ch, st);
    type_names(ch, tds, st);
}

/// Upstream's type PARSER refuses these; this parser reads them and the
/// rule is applied over the type expressions instead, with the parser's
/// codes, which halt the driver as a parse error does.
fn type_syntax(ch: &Chapter, st: &mut UnifyState) {
    for d in &ch.defs {
        if let Some(t) = d.declared_type.first() {
            walk_syntax(t, ch, st);
        }
    }
    for td in &ch.type_defs {
        match td {
            TypeDef::Variant(_, _, ctors, _) => {
                for c in ctors {
                    for f in &c.fields {
                        walk_syntax(f, ch, st);
                    }
                }
            }
            TypeDef::Record(_, _, fields, _, _) => {
                for f in fields {
                    walk_syntax(&f.type_expr, ch, st);
                }
            }
            TypeDef::Unit(_, base, _) => walk_syntax(base, ch, st),
        }
    }
}

/// `bounds-are-hw-width`: a wrapping band is exactly one hardware width.
fn bounds_are_hw_width(lo: i64, hi: i64) -> bool {
    matches!(
        (lo, hi),
        (0, 255)
            | (-128, 127)
            | (0, 65535)
            | (-32768, 32767)
            | (0, 4294967295)
            | (-2147483648, 2147483647)
            | (i64::MIN, i64::MAX)
    )
}

fn walk_syntax(t: &TypeExpr, ch: &Chapter, st: &mut UnifyState) {
    match t {
        TypeExpr::Effect(_, _, tail, ret, _) => {
            // `[e, f]`: at most one row variable (CDX1120); `[e.Write]`: a
            // row variable takes no dotted sub-effect (CDX1121).
            if tail.len() > 1 {
                st.error(
                    Cdx::EFFECT_ROW_TWO_TAILS,
                    format!(
                        "an effect row may name at most one row variable; found '{}' after an earlier row variable",
                        ch.syms.text(tail[1])
                    ),
                );
            }
            for v in tail {
                let text = ch.syms.text(*v);
                if let Some(dot) = text.find('.') {
                    st.error(
                        Cdx::EFFECT_ROW_TAIL_DECORATED,
                        format!("a row variable is a bare lowercase identifier; '{}' cannot take a dotted sub-effect", &text[..dot]),
                    );
                }
            }
            walk_syntax(ret, ch, st);
        }
        TypeExpr::BoundedInt(_, lo, hi, crate::ast::OverflowMode::Wrapping, _) => {
            if !bounds_are_hw_width(*lo, *hi) {
                st.error(
                    Cdx::WRAPPING_BAND_NOT_HW_WIDTH,
                    format!("a wrapping band must be exactly its hardware width, and {lo} to {hi} is not: the store wraps at the width, so the field can hold a value outside the declared range"),
                );
            }
        }
        TypeExpr::Fun(p, r, _) => {
            walk_syntax(p, ch, st);
            walk_syntax(r, ch, st);
        }
        TypeExpr::App(ctor, args, _) => {
            walk_syntax(ctor, ch, st);
            for a in args {
                walk_syntax(a, ch, st);
            }
        }
        TypeExpr::Linear(inner, _) | TypeExpr::Constrained(_, _, inner, _) => walk_syntax(inner, ch, st),
        TypeExpr::Forall(_, vt, p, _) => {
            walk_syntax(vt, ch, st);
            walk_syntax(p, ch, st);
        }
        TypeExpr::PropEq(l, r, _) => {
            walk_syntax(l, ch, st);
            walk_syntax(r, ch, st);
        }
        _ => {}
    }
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
        let (n, ctors, span) = match td {
            TypeDef::Record(n, _, _, _, sp) | TypeDef::Unit(n, _, sp) => (*n, None, *sp),
            TypeDef::Variant(n, _, cs, sp) => (*n, Some(cs), *sp),
        };
        // The desugarer's own type definitions (a class's dictionary) are
        // not the program's, and it may build one more than once.
        if crate::check::is_synthetic(span) {
            continue;
        }
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
