//! **A CALL TO A FORWARDER THAT CALLS BACK IS WRITTEN AS THE CALL IT MAKES.**
//!
//! Roc turns a function's tail call to itself into a loop, but not two
//! functions that call each other, so a pair of them grows the stack by two
//! frames a step. Codex writes such a pair when a definition hands off to a
//! small one whose whole body is a call back: GlobeDemo's `gtris` draws a
//! triangle and calls `gtris-next`, which is `gtris` with the next indices, once
//! for every visible triangle, and a browser's stack is spent before the first
//! frame.
//!
//! So where a definition `g` calls a forwarder `f` whose body is one call to
//! `g`, the call is written as `f`'s body with the arguments in place, and `g`
//! calls itself. `f` is still emitted, unchanged, for any other caller.
//!
//! An argument that is a name or a literal takes its parameter's place. Any
//! other argument is bound first, in order, under the parameter's own name, so
//! it is still evaluated once and before the call: GlobeDemo's first argument to
//! `gtris-next` is the sum of eighteen `gpu-mem-write`s that `gtris-next` never
//! reads. A call whose bindings would capture a name the call site already
//! means, or that an argument reads, is left as it is.

use crate::check::Ty;
use crate::ir_chapter::{IrDef, IrExpr};
use crate::ir_passes::{
    apply_args, apply_root, declared_return, has_bounded_boundary, once_binder_free, once_free_escapes, rewrite,
    subst_once, Candidate,
};
use crate::lowering_types as lt;
use crate::symbol::Sym;

/// Every definition, each call to a forwarder that calls it back written as
/// the call the forwarder makes.
pub fn call_back_directly(defs: &[IrDef]) -> Vec<IrDef> {
    let forwarders: Vec<(Sym, Candidate)> = defs.iter().filter_map(|f| forwarder(f, defs)).collect();
    if forwarders.is_empty() {
        return defs.to_vec();
    }
    defs.iter()
        .map(|g| {
            let cands: Vec<Candidate> =
                forwarders.iter().filter(|(to, _)| *to == g.name).map(|(_, c)| c.clone()).collect();
            if cands.is_empty() {
                return g.clone();
            }
            let mut bound: Vec<Sym> = g.params.iter().map(|p| p.name).collect();
            let body = rewrite(&g.body, &cands, &mut bound, &call_back_site);
            IrDef { body, ..g.clone() }
        })
        .collect()
}

/// `f` forwards to `g` when its whole body is one call to `g`, another
/// definition, with as many arguments as `g` has parameters and nothing in them
/// that binds a name, and `f`'s signature is neither generic nor bounded (a
/// bounded one is guarded where it is entered).
fn forwarder(f: &IrDef, defs: &[IrDef]) -> Option<(Sym, Candidate)> {
    let to = apply_root(&f.body)?;
    let g = defs.iter().find(|d| d.name == to && d.name != f.name)?;
    let args = apply_args(&f.body);
    if f.params.is_empty() || args.is_empty() || args.len() != g.params.len() {
        return None;
    }
    if !once_binder_free(&f.body) || has_bounded_boundary(f) {
        return None;
    }
    let ptys: Vec<Ty> = f.params.iter().map(|p| p.ty.clone()).collect();
    let rty = declared_return(f);
    if ptys.iter().chain(std::iter::once(&rty)).any(lt::has_typevars) {
        return None;
    }
    let params = f.params.iter().map(|p| p.name).collect();
    Some((to, Candidate { name: f.name, params, ptys, rty, body: f.body.clone() }))
}

/// A call to a forwarder, written as its body. See the module's note.
fn call_back_site(e: &IrExpr, cands: &[Candidate], bound: &[Sym]) -> IrExpr {
    let Some(root) = apply_root(e) else { return e.clone() };
    if bound.contains(&root) {
        return e.clone();
    }
    let Some(c) = cands.iter().find(|c| c.name == root) else { return e.clone() };
    let args = apply_args(e);
    if args.len() != c.params.len() || once_free_escapes(&c.body, &c.params, bound) {
        return e.clone();
    }
    let mut lets: Vec<(Sym, Ty, IrExpr)> = Vec::new();
    let mut place: Vec<IrExpr> = Vec::with_capacity(args.len());
    for (i, a) in args.iter().enumerate() {
        if duplicable(a) {
            place.push((*a).clone());
        } else {
            let p = c.params[i];
            if bound.contains(&p) {
                return e.clone();
            }
            lets.push((p, c.ptys[i].clone(), (*a).clone()));
            place.push(IrExpr::Name(p, c.ptys[i].clone(), e.span()));
        }
    }
    if args.iter().any(|a| lets.iter().any(|(p, ..)| reads(a, *p))) {
        return e.clone();
    }
    let refs: Vec<&IrExpr> = place.iter().collect();
    let mut out = subst_once(&c.body, &c.params, &refs, &[], &[]);
    for (p, t, v) in lets.into_iter().rev() {
        out = IrExpr::Let(p, t, Box::new(v), Box::new(out), e.span());
    }
    out
}

/// A name or a literal: it costs nothing and does nothing, so it may stand in
/// its parameter's every place.
fn duplicable(e: &IrExpr) -> bool {
    matches!(
        e,
        IrExpr::Name(..) | IrExpr::IntLit(..) | IrExpr::NumLit(..) | IrExpr::BoolLit(..) | IrExpr::CharLit(..) | IrExpr::TextLit(..)
    )
}

fn reads(e: &IrExpr, n: Sym) -> bool {
    let mut found = false;
    e.walk(&mut |x| {
        if let IrExpr::Name(m, _, _) = x {
            found |= *m == n;
        }
    });
    found
}

#[cfg(test)]
mod tests {
    use super::call_back_directly;
    use crate::ir_chapter::{IrDef, IrExpr};
    use crate::symbol::SymTab;

    fn lowered(src: &str) -> (SymTab, Vec<IrDef>) {
        let src = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&src);
        let mut dg = crate::desugar::Desugar::new(&src);
        let ch = dg.chapter(&parsed.tree);
        let (bindings, st, tds) = crate::check::check_chapter_full(&ch);
        let low = crate::ir::lower_whole(&ch, &bindings, &st, &tds).expect("the chapter lowers");
        (low.syms, low.defs)
    }

    fn body<'a>(defs: &'a [IrDef], syms: &SymTab, name: &str) -> &'a IrExpr {
        &defs.iter().find(|d| syms.text(d.name) == name).expect("the definition").body
    }

    fn names(e: &IrExpr, syms: &SymTab, name: &str) -> bool {
        let mut found = false;
        e.walk(&mut |x| {
            if let IrExpr::Name(n, _, _) = x {
                found |= syms.text(*n) == name;
            }
        });
        found
    }

    fn binds(e: &IrExpr, syms: &SymTab, name: &str) -> bool {
        let mut found = false;
        e.walk(&mut |x| {
            if let IrExpr::Let(n, ..) = x {
                found |= syms.text(*n) == name;
            }
        });
        found
    }

    /// GlobeDemo's shape: `step` ignores its first argument, which is not a
    /// name, and calls `down` back with the next values.
    const PAIR: &str = "Chapter: T\n\nSection: S\n\n  down : Integer, Integer -> Integer\n  down (n) (acc) = if n <= 0 then acc else step (acc * 2) n acc\n\n  step : Integer, Integer, Integer -> Integer\n  step (w) (n) (acc) = down (n - 1) (acc + 1)\n\n  opening : [Console] Nothing = act\n    print-line-uni (show (down 5 0))\n  end\n";

    #[test]
    fn a_call_to_a_forwarder_that_calls_back_becomes_a_call_to_itself() {
        let (syms, defs) = lowered(PAIR);
        let out = call_back_directly(&defs);
        let down = body(&out, &syms, "down");
        assert!(names(down, &syms, "down"), "down calls itself");
        assert!(!names(down, &syms, "step"), "down no longer calls step");
        assert!(binds(down, &syms, "w"), "the argument step ignores is still bound, and so evaluated");
        assert_eq!(format!("{:?}", body(&out, &syms, "step")), format!("{:?}", body(&defs, &syms, "step")));
    }

    #[test]
    fn a_binding_that_would_capture_a_local_leaves_the_call_as_it_is() {
        let src = PAIR.replace(
            "down (n) (acc) = if n <= 0 then acc else step (acc * 2) n acc",
            "down (n) (acc) = let w = acc in if n <= 0 then w else step (acc * 2) n acc",
        );
        let (syms, defs) = lowered(&src);
        let out = call_back_directly(&defs);
        assert!(names(body(&out, &syms, "down"), &syms, "step"), "w already means something where step is called");
    }
}
