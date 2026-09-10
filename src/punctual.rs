//! The punctuality checks -- upstream's `check-rt-no-lambda`,
//! `check-rt-no-alloc`, `check-rt-calls`, `has-self-call` and
//! `check-rt-cycles` (TypeChecker.codex:1330ff, :2818, :2400).
//!
//! A `punctual` definition promises bounded execution. Its body may hold
//! no lambda (CDX6003); may not allocate -- a heap-allocating builtin, a
//! concatenation that is not boolean, a record or list literal (CDX6002);
//! may call only other punctual definitions and a short list of builtins,
//! and only by name (CDX6001); and may not recurse, directly or through
//! other punctual definitions (CDX6005).

use crate::ast::{ActStmt, BinaryOp, Chapter, Expr, HandleClause, MatchArm, Name};
use crate::check::{expr_type_key, Cdx, Ty, UnifyState};
use crate::symbol::SymTab;

fn is_rt_unsafe_name(n: &str) -> bool {
    matches!(n, "__alloc" | "list-push" | "list-concat" | "__list-with-capacity" | "__linked-list-push")
}

fn is_rt_safe_builtin(n: &str) -> bool {
    matches!(
        n,
        "list-at"
            | "list-length"
            | "text-length"
            | "text-at"
            | "array-at"
            | "array-length"
            | "bit-and"
            | "bit-or"
            | "bit-xor"
            | "bit-shl"
            | "bit-shr"
            | "bit-shru"
            | "bit-not"
            | "int-mod"
            | "int-rem"
            | "abs"
            | "min"
            | "max"
    )
}

/// Every child expression, in upstream's walk order, for the three walks
/// that treat every form alike below the form they refuse.
fn children<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match e {
        Expr::If(c, t, el, _) => {
            out.push(c);
            out.push(t);
            out.push(el);
        }
        Expr::Let(bs, b, _) => {
            for x in bs {
                out.push(&x.value);
            }
            out.push(b);
        }
        Expr::Apply(f, a, _) => {
            out.push(f);
            out.push(a);
        }
        Expr::Binary(l, _, r, _) => {
            out.push(l);
            out.push(r);
        }
        Expr::Unary(x, _) | Expr::Lazy(x, _) | Expr::FieldAccess(x, _, _) => out.push(x),
        Expr::Match(sc, arms, _) | Expr::Induction(sc, arms, _) => {
            out.push(sc);
            arms_children(arms, out);
        }
        Expr::List(xs, _) => out.extend(xs.iter()),
        Expr::Record(_, fs, _) => out.extend(fs.iter().map(|f| &f.value)),
        Expr::Act(stmts, _) => stmt_children(stmts, out),
        Expr::Try(t) => {
            stmt_children(&t.body, out);
            stmt_children(&t.fallback, out);
            stmt_children(&t.failure, out);
        }
        Expr::Handle(h) => {
            out.push(&h.body);
            clause_children(&h.clauses, out);
        }
        Expr::WithTimeout(w) => out.push(&w.body),
        Expr::FieldAssign(r, _, v, _) => {
            out.push(r);
            out.push(v);
        }
        Expr::Lambda(..) | Expr::Lit(..) | Expr::NameRef(..) | Expr::Error(..) => {}
    }
}

fn arms_children<'a>(arms: &'a [MatchArm], out: &mut Vec<&'a Expr>) {
    for a in arms {
        out.push(&a.guard);
        out.push(&a.body);
    }
}

fn stmt_children<'a>(stmts: &'a [ActStmt], out: &mut Vec<&'a Expr>) {
    for s in stmts {
        match s {
            ActStmt::Exec(e, _) | ActStmt::Bind(_, e, _) => out.push(e),
        }
    }
}

fn clause_children<'a>(cls: &'a [HandleClause], out: &mut Vec<&'a Expr>) {
    for c in cls {
        out.push(&c.body);
    }
}

/// `check-rt-no-lambda`.
fn no_lambda(e: &Expr, fname: &str, st: &mut UnifyState) {
    if let Expr::Lambda(..) = e {
        st.error(Cdx::RT_CLOSURE, format!("punctual function '{fname}' contains a lambda or closure"));
        return;
    }
    let mut kids = Vec::new();
    children(e, &mut kids);
    for k in kids {
        no_lambda(k, fname, st);
    }
}

/// `check-rt-no-alloc`. The children first where upstream walks them first
/// (a binary's operands), the form's own refusal first for a record or a
/// list literal.
fn no_alloc(e: &Expr, fname: &str, syms: &SymTab, st: &mut UnifyState) {
    match e {
        Expr::NameRef(n, _) => {
            if is_rt_unsafe_name(syms.text(*n)) {
                st.error(
                    Cdx::RT_HEAP_ALLOC,
                    format!("[HardRealtime] function '{fname}' uses heap-allocating builtin '{}'", syms.text(*n)),
                );
            }
        }
        Expr::Binary(l, op, r, sp) => {
            no_alloc(l, fname, syms, st);
            no_alloc(r, fname, syms, st);
            match op {
                BinaryOp::OpAppend => st.error(
                    Cdx::RT_HEAP_ALLOC,
                    format!("[HardRealtime] function '{fname}' uses text concatenation (&)"),
                ),
                BinaryOp::OpAnd => {
                    // `expr-type-scan` at the binary's span: `&` on booleans
                    // is logic, on anything else concatenation.
                    let key = expr_type_key(*sp);
                    let recorded = st.expr_types.iter().find(|(k, _)| *k == key).map(|(_, t)| st.deep_resolve(t));
                    if !matches!(recorded, Some(Ty::Boolean) | Some(Ty::Error)) {
                        st.error(
                            Cdx::RT_HEAP_ALLOC,
                            format!("[HardRealtime] function '{fname}' uses concatenation (&), which allocates"),
                        );
                    }
                }
                _ => {}
            }
        }
        Expr::Record(n, fs, _) => {
            st.error(
                Cdx::RT_HEAP_ALLOC,
                format!("[HardRealtime] function '{fname}' constructs record '{}' (heap allocation)", syms.text(*n)),
            );
            for f in fs {
                no_alloc(&f.value, fname, syms, st);
            }
        }
        Expr::List(xs, _) => {
            st.error(Cdx::RT_HEAP_ALLOC, format!("[HardRealtime] function '{fname}' builds a list literal (heap allocation)"));
            for x in xs {
                no_alloc(x, fname, syms, st);
            }
        }
        Expr::Lambda(..) => {}
        _ => {
            let mut kids = Vec::new();
            children(e, &mut kids);
            for k in kids {
                no_alloc(k, fname, syms, st);
            }
        }
    }
}

/// `check-rt-calls`: the argument first, then the callee by name.
fn calls(e: &Expr, fname: &str, rt: &[Name], syms: &SymTab, st: &mut UnifyState) {
    match e {
        Expr::Apply(f, a, _) => {
            calls(a, fname, rt, syms, st);
            match &**f {
                Expr::NameRef(n, _) => {
                    if !(rt.contains(n) || is_rt_safe_builtin(syms.text(*n))) {
                        st.error(
                            Cdx::RT_CALLS_UNSAFE,
                            format!("punctual function '{fname}' calls '{}' which is not punctual", syms.text(*n)),
                        );
                    }
                }
                Expr::Apply(..) => calls(f, fname, rt, syms, st),
                _ => {
                    st.error(
                        Cdx::RT_CALLS_UNSAFE,
                        format!("punctual function '{fname}' calls through a computed head; a punctual call must name its callee"),
                    );
                    calls(f, fname, rt, syms, st);
                }
            }
        }
        Expr::Lambda(..) => {}
        _ => {
            let mut kids = Vec::new();
            children(e, &mut kids);
            for k in kids {
                calls(k, fname, rt, syms, st);
            }
        }
    }
}

/// `has-self-call`: any mention of the definition's own name.
fn has_self_call(e: &Expr, me: Name) -> bool {
    let mut found = false;
    e.walk(&mut |x| {
        if let Expr::NameRef(n, _) = x {
            if *n == me {
                found = true;
            }
        }
    });
    found
}

/// Per definition, after linearity: the three walks and the self call.
pub fn check_def(d: &crate::ast::Def, rt: &[Name], syms: &SymTab, st: &mut UnifyState) {
    if !d.is_punctual {
        return;
    }
    let fname = syms.text(d.name).to_string();
    no_lambda(&d.body, &fname, st);
    no_alloc(&d.body, &fname, syms, st);
    calls(&d.body, &fname, rt, syms, st);
    if has_self_call(&d.body, d.name) {
        st.error(Cdx::RT_UNBOUNDED_RECURSION, format!("punctual function '{fname}' is self-recursive"));
    }
}

/// `check-rt-cycles`, over the whole chapter: a punctual definition that
/// reaches itself through other punctual definitions.
pub fn check_cycles(ch: &Chapter, st: &mut UnifyState) {
    let rt: Vec<Name> = ch.defs.iter().filter(|d| d.is_punctual).map(|d| d.name).collect();
    if rt.is_empty() {
        return;
    }
    let edges: Vec<(Name, Vec<Name>)> = ch
        .defs
        .iter()
        .filter(|d| d.is_punctual)
        .map(|d| {
            let mut calls: Vec<Name> = Vec::new();
            d.body.walk(&mut |e| {
                if let Expr::NameRef(n, _) = e {
                    if *n != d.name && rt.contains(n) && !calls.contains(n) {
                        calls.push(*n);
                    }
                }
            });
            (d.name, calls)
        })
        .collect();
    fn reaches(edges: &[(Name, Vec<Name>)], cur: Name, target: Name, visited: &mut Vec<Name>) -> bool {
        if cur == target {
            return true;
        }
        if visited.contains(&cur) {
            return false;
        }
        visited.push(cur);
        edges.iter().find(|(n, _)| *n == cur).is_some_and(|(_, ns)| ns.iter().any(|n| reaches(edges, *n, target, visited)))
    }
    for (name, calls) in &edges {
        let mut visited = Vec::new();
        if calls.iter().any(|c| reaches(&edges, *c, *name, &mut visited)) {
            st.error(
                Cdx::RT_UNBOUNDED_RECURSION,
                format!("punctual function '{}' is mutually recursive through another punctual function; bounded execution cannot be proven", ch.syms.text(*name)),
            );
        }
    }
}
