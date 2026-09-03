//! Does our code still call the compiler's functions with the right number of
//! arguments?
//!
//! THIS IS THE MOST EXPENSIVE RECURRING FAILURE IN THE LADDER, and it is
//! expensive because Codex does not report it. Codex curries, so a call given
//! too few arguments is not an error -- it is a FUNCTION VALUE. The program
//! stays well-formed and the type error surfaces one line later, against
//! whatever consumed the value, naming neither the call nor the argument it
//! wanted:
//!
//! ```text
//! CDX2001: Type mismatch: Rec:IRChapter vs Fun     (at run-ir-pipeline)
//! ```
//!
//! `lower-chapter` moved three Updates running -- 8 parameters at U53, 9 at U54
//! (`rename`), 11 at U55 with a tuple return -- and each move was found by a
//! rung dying an hour into a run rather than by reading the release.
//!
//! The check is mechanical, so it should be mechanical: index every definition
//! in the compiler by its declared parameter count, walk every application in
//! our own harnesses, and report where the two disagree.
//!
//! ## Why under-application is reported and over-application is fatal
//!
//! PARTIAL APPLICATION IS LEGAL AND DELIBERATE. `map-list (f x) xs` passes a
//! partially applied function on purpose, and a checker that called that an
//! error would be switched off within a day. So an under-applied call is
//! reported with its shortfall and the reader decides -- except in ARGUMENT
//! POSITION, where a value is what was wanted anyway, and those are dropped.
//!
//! Over-application is different: applying more arguments than a definition
//! takes cannot be intentional unless the definition returns a function, which
//! the declared type would have to say. It is reported separately.
//!
//! ## What it does not know
//!
//! A definition's parameter count comes from its `params` list, which is the
//! spelling `f (a) (b) = ...`. A definition written point-free -- `f = g h` --
//! has zero parameters here and an arity its TYPE knows about. Those are
//! skipped rather than guessed at, and counted in the summary so the number
//! skipped is visible rather than silent.

use crate::ast::{Chapter, Def, Expr};
use std::collections::{BTreeMap, BTreeSet};

/// One definition's declared shape, as the tree spells it.
#[derive(Clone, Debug)]
pub struct Declared {
    pub params: usize,
    /// Where it is defined, for the report.
    pub path: String,
    /// A definition with no parameter list tells us nothing about arity.
    pub point_free: bool,
}

/// name -> declared shape. A name defined twice with the SAME arity is fine
/// (the tree legitimately has several); defined twice with DIFFERENT arities it
/// is dropped, because a call site cannot be graded against an ambiguity.
pub fn index(chapters: &[(String, Chapter)]) -> BTreeMap<String, Declared> {
    let mut out: BTreeMap<String, Declared> = BTreeMap::new();
    let mut ambiguous: BTreeSet<String> = BTreeSet::new();
    for (path, ch) in chapters {
        for d in &ch.defs {
            let dec = Declared {
                params: d.params.len(),
                path: path.clone(),
                point_free: d.params.is_empty() && !d.declared_type.is_empty(),
            };
            match out.get(&d.name) {
                Some(prev) if prev.params != dec.params => {
                    ambiguous.insert(d.name.clone());
                }
                Some(_) => {}
                None => {
                    out.insert(d.name.clone(), dec);
                }
            }
        }
    }
    for n in ambiguous {
        out.remove(&n);
    }
    out
}

/// One application we found in our own source.
#[derive(Clone, Debug)]
pub struct Call {
    pub name: String,
    pub applied: usize,
    pub line: u32,
    /// True when the spine sits where a VALUE is wanted -- as an argument to
    /// another call, or on the right of a binary operator. A short call there
    /// is ordinary partial application, not drift.
    pub in_arg_position: bool,
}

/// Every application in a chapter, keyed to the head of its spine.
///
/// `f a b c` parses as `Apply(Apply(Apply(f,a),b),c)`, so a naive walk sees the
/// same spine three times at three different lengths and reports two phantom
/// short calls for every real call. Only the OUTERMOST node of a spine is
/// recorded, and the walk then descends into the arguments rather than back
/// down the head chain.
pub fn calls(ch: &Chapter) -> Vec<Call> {
    let mut out = Vec::new();
    for d in &ch.defs {
        // A definition's own parameters, its lambdas and its let-bindings are
        // LOCAL. A local named as a tree definition is shadowing, and grading
        // its call sites against the tree's arity is how a checker earns a
        // reputation for crying wolf.
        let mut bound: BTreeSet<String> = d.params.iter().map(|p| p.name.clone()).collect();
        collect_binders(&d.body, &mut bound);
        scan(&d.body, &bound, &mut out);
    }
    out
}

fn collect_binders(e: &Expr, out: &mut BTreeSet<String>) {
    e.walk(&mut |x| match x {
        Expr::Lambda(ns, _, _) => out.extend(ns.iter().cloned()),
        Expr::Let(bs, _, _) => out.extend(bs.iter().map(|b| b.name.clone())),
        _ => {}
    });
}

/// Two passes over pointers, because a spine cannot be recognised locally.
///
/// `f a b c` is `Apply(Apply(Apply(f,a),b),c)`, and `walk` visits all three
/// nodes. Pass one marks every node that appears as the HEAD of an enclosing
/// application -- those are interior to a spine and must not be reported -- and
/// every node that appears where a VALUE is wanted. Pass two reports the nodes
/// pass one did not mark as interior.
fn addr(e: &Expr) -> usize {
    e as *const Expr as usize
}

fn scan(body: &Expr, bound: &BTreeSet<String>, out: &mut Vec<Call>) {
    let mut interior: BTreeSet<usize> = BTreeSet::new();
    let mut value_pos: BTreeSet<usize> = BTreeSet::new();
    body.walk(&mut |x| match x {
        Expr::Apply(f, a, _) => {
            interior.insert(addr(f));
            value_pos.insert(addr(a));
        }
        Expr::Binary(a, _, b, _) => {
            value_pos.insert(addr(a));
            value_pos.insert(addr(b));
        }
        Expr::List(xs, _) => {
            for k in xs {
                value_pos.insert(addr(k));
            }
        }
        _ => {}
    });
    body.walk(&mut |x| {
        if !matches!(x, Expr::Apply(..)) || interior.contains(&addr(x)) {
            return;
        }
        let mut head = x;
        let mut applied = 0usize;
        while let Expr::Apply(f, _, _) = head {
            applied += 1;
            head = f;
        }
        if let Expr::NameRef(n, sp) = head {
            if !bound.contains(n) {
                out.push(Call {
                    name: n.clone(),
                    applied,
                    line: sp.line,
                    in_arg_position: value_pos.contains(&addr(x)),
                });
            }
        }
    });
}

/// A call whose argument count disagrees with the definition it names.
pub struct Drift {
    pub call: Call,
    pub declared: usize,
    pub defined_at: String,
}

pub fn compare(
    calls: &[Call],
    ix: &BTreeMap<String, Declared>,
    include_partial: bool,
) -> (Vec<Drift>, Vec<Drift>, usize) {
    let (mut short, mut over, mut skipped) = (Vec::new(), Vec::new(), 0usize);
    for c in calls {
        let Some(d) = ix.get(&c.name) else { continue };
        if d.point_free || d.params == 0 {
            skipped += 1;
            continue;
        }
        if c.applied == d.params {
            continue;
        }
        let dr = Drift { call: c.clone(), declared: d.params, defined_at: d.path.clone() };
        if c.applied > d.params {
            over.push(dr);
        } else if include_partial || !c.in_arg_position {
            short.push(dr);
        }
    }
    (short, over, skipped)
}

/// The definitions a caller is most likely to care about: the driver's phases.
/// Not a filter by default -- a list to sort the report by, so the expensive
/// ones are read first.
pub fn is_driver_phase(name: &str) -> bool {
    name.starts_with("compile-")
        || matches!(
            name,
            "lower-chapter"
                | "check-chapter"
                | "scope-achapter"
                | "resolve-chapter"
                | "resolve-chapter-with-citations"
                | "run-ir-pipeline"
                | "lift-lambdas"
                | "desugar-document"
                | "parse-document"
                | "scan-document"
                | "tokenize"
                | "emit-ir-chapter"
                | "ir-prune-unreachable-roots"
        )
}

pub fn chapter_of(d: &Def) -> &str {
    &d.chapter_slug
}
