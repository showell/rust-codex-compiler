//! Where a chapter could be cut, when counting components says nothing.
//!
//! `cohesion` answers "are these two halves connected at all", and for a
//! chapter like Camera that is the whole question. For `Render` -- 108 of 111
//! definitions in one component -- it is silent, and the silence is honest:
//! there is no disconnection to find. A big chapter is rarely two programs. It
//! is one program with seams in it.
//!
//! **A seam has an exact definition and it is the dominator tree.** Root a
//! directed graph at everything OUTSIDE the chapter reaches, and `f` dominates
//! the set of definitions reachable only through `f`. Peel that set and `f` is
//! the only edge you cut, by construction -- you do not search for a small cut,
//! you read it off. A definition dominating forty others is a chapter waiting
//! to be extracted with `f` as its one exported name.
//!
//! **The roots are the chapter's real interface**, and the cross-chapter index
//! is what makes them knowable: a definition read by another chapter is an
//! entry point, and everything else is interior. Getting this wrong in the
//! obvious way -- rooting at every definition -- makes every node dominate only
//! itself and reports nothing.
//!
//! **Mutual recursion is atomic**, so strongly connected components are
//! condensed first. Two functions that call each other cannot be separated,
//! and a 40-function cycle is a cohesion fact the dominator tree should not be
//! asked to paper over -- it is reported as itself.

use std::collections::{BTreeMap, BTreeSet};

pub struct Seam {
    /// The definition that is the cut point.
    pub head: usize,
    /// Everything reachable only through it, excluding the head.
    pub owns: Vec<usize>,
}

pub struct Seams {
    /// Node -> the SCC it belongs to. Nodes in one SCC are inseparable.
    pub scc_of: Vec<usize>,
    /// SCCs with more than one member, as member lists.
    pub cycles: Vec<Vec<usize>>,
    /// Cut points, largest owned set first.
    pub seams: Vec<Seam>,
    /// Definitions another chapter reads: the chapter's real interface.
    pub roots: Vec<usize>,
}

/// Tarjan, iterative -- these graphs are small but a chapter is allowed to
/// recurse deeply and a stack overflow in an analysis tool is a bad trade.
fn sccs(n: usize, succ: &[Vec<usize>]) -> Vec<usize> {
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut comp = vec![usize::MAX; n];
    let mut next_index = 0usize;
    let mut next_comp = 0usize;

    for start in 0..n {
        if index[start] != usize::MAX {
            continue;
        }
        // (node, next child to visit)
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some((v, ci)) = work.pop() {
            if ci == 0 {
                index[v] = next_index;
                low[v] = next_index;
                next_index += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            let mut recursed = false;
            for (k, &w) in succ[v].iter().enumerate().skip(ci) {
                if index[w] == usize::MAX {
                    work.push((v, k + 1));
                    work.push((w, 0));
                    recursed = true;
                    break;
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
            }
            if recursed {
                continue;
            }
            if low[v] == index[v] {
                while let Some(w) = stack.pop() {
                    on_stack[w] = false;
                    comp[w] = next_comp;
                    if w == v {
                        break;
                    }
                }
                next_comp += 1;
            }
            if let Some(&(p, _)) = work.last() {
                low[p] = low[p].min(low[v]);
            }
        }
    }
    comp
}

/// Cooper-Harvey-Kennedy over a reverse-postorder numbering. Node `n` is the
/// virtual root; it points at every entry the outside world can reach.
fn dominators(n: usize, succ: &[Vec<usize>], root: usize) -> Vec<usize> {
    // Reverse postorder from the root.
    let mut order: Vec<usize> = Vec::new();
    let mut seen = vec![false; n + 1];
    let mut work: Vec<(usize, usize)> = vec![(root, 0)];
    seen[root] = true;
    while let Some((v, ci)) = work.pop() {
        if ci < succ[v].len() {
            work.push((v, ci + 1));
            let w = succ[v][ci];
            if !seen[w] {
                seen[w] = true;
                work.push((w, 0));
            }
        } else {
            order.push(v);
        }
    }
    order.reverse();
    let mut rpo = vec![usize::MAX; n + 1];
    for (i, &v) in order.iter().enumerate() {
        rpo[v] = i;
    }

    let mut pred: Vec<Vec<usize>> = vec![Vec::new(); n + 1];
    for v in 0..=n {
        for &w in &succ[v] {
            pred[w].push(v);
        }
    }

    let mut idom = vec![usize::MAX; n + 1];
    idom[root] = root;
    let mut changed = true;
    while changed {
        changed = false;
        for &v in order.iter().skip(1) {
            let mut new_idom = usize::MAX;
            for &p in &pred[v] {
                if rpo[p] == usize::MAX || idom[p] == usize::MAX {
                    continue;
                }
                new_idom = if new_idom == usize::MAX {
                    p
                } else {
                    // intersect
                    let (mut a, mut b) = (p, new_idom);
                    while a != b {
                        while rpo[a] > rpo[b] {
                            a = idom[a];
                        }
                        while rpo[b] > rpo[a] {
                            b = idom[b];
                        }
                    }
                    a
                };
            }
            if new_idom != usize::MAX && idom[v] != new_idom {
                idom[v] = new_idom;
                changed = true;
            }
        }
    }
    idom
}

/// `edges` are (caller, callee) inside the chapter. `roots` are the
/// definitions some other chapter reads.
pub fn analyse(n: usize, edges: &[(usize, usize)], roots: &[usize]) -> Seams {
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n + 1];
    for &(a, b) in edges {
        succ[a].push(b);
    }
    for s in succ.iter_mut() {
        s.sort_unstable();
        s.dedup();
    }

    let scc_of = sccs(n, &succ[..n]);
    let mut members: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (v, &c) in scc_of.iter().enumerate() {
        members.entry(c).or_default().push(v);
    }
    let cycles: Vec<Vec<usize>> =
        members.values().filter(|m| m.len() > 1).cloned().collect();

    // The virtual root is node n. A chapter with no external readers is an
    // entry chapter or dead; rooting at everything then is the honest default
    // and simply reports no seams.
    let root = n;
    succ[root] = if roots.is_empty() { (0..n).collect() } else { roots.to_vec() };

    let idom = dominators(n, &succ, root);
    let mut owned: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for v in 0..n {
        // Walk up the dominator tree, attributing v to every strict dominator
        // that is a real definition rather than the virtual root.
        let mut d = idom[v];
        let mut guard = 0;
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        while d != usize::MAX && d != root && seen.insert(d) && guard < n + 2 {
            if d != v {
                owned.entry(d).or_default().push(v);
            }
            d = idom[d];
            guard += 1;
        }
    }

    let mut seams: Vec<Seam> = owned
        .into_iter()
        .map(|(head, mut owns)| {
            owns.sort_unstable();
            Seam { head, owns }
        })
        .filter(|s| !s.owns.is_empty())
        .collect();
    seams.sort_by(|a, b| b.owns.len().cmp(&a.owns.len()).then(a.head.cmp(&b.head)));

    Seams { scc_of, cycles, seams, roots: roots.to_vec() }
}
