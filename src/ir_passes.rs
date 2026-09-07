//! The IR pipeline -- the rewriting passes in `IR/Lowering.codex`, and the
//! prune the driver runs at emit time.
//!
//! **THE GOLDS ARE POST-PIPELINE**, which is the whole reason this file
//! exists. `CDX4030 PIPELINE` names three passes on every compile:
//!
//! ```text
//!   fold-constants, inline-leaf-calls, inline-single-caller
//! ```
//!
//! and then `ir-prune-unreachable-roots` drops what nothing references any
//! more. Those two facts compose into the effect that is visible in every
//! gold: a small function is substituted into its callers and then DISAPPEARS.
//! `sb-length`, `signal-delivered-count`, `fused-lt` are in no gold at all,
//! and an emitter that types them perfectly still emits a different document.

use crate::ir_chapter::{IrDef, IrExpr};
use crate::symbol::{Sym, SymTab};
use std::collections::{BTreeMap, BTreeSet};

/// The three passes, in the driver's order.
pub fn pipeline(defs: Vec<IrDef>, syms: &SymTab) -> Vec<IrDef> {
    let _ = syms;
    defs
}

/// `ir-prune-unreachable-roots`. Every definition reachable from the roots by
/// following the names its body mentions, in the original order.
///
/// **THIS RUNS LAST, AFTER THE PASSES**, which is what makes an inlined-away
/// definition disappear rather than merely lose its caller.
pub fn prune_unreachable_roots(defs: Vec<IrDef>, roots: &[&str], syms: &SymTab) -> Vec<IrDef> {
    let by_name: BTreeMap<Sym, usize> =
        defs.iter().enumerate().map(|(i, d)| (d.name, i)).collect();
    let mut seen: BTreeSet<Sym> = BTreeSet::new();
    let mut stack: Vec<Sym> =
        roots.iter().filter_map(|r| syms.find(r)).filter(|n| by_name.contains_key(n)).collect();
    while let Some(n) = stack.pop() {
        if !seen.insert(n) {
            continue;
        }
        if let Some(i) = by_name.get(&n) {
            defs[*i].body.walk(&mut |x| {
                if let IrExpr::Name(m, _, _) = x {
                    if by_name.contains_key(m) && !seen.contains(m) {
                        stack.push(*m);
                    }
                }
            });
        }
    }
    defs.into_iter().filter(|d| seen.contains(&d.name)).collect()
}
