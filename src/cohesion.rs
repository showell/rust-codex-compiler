//! Is a chapter doing one job or two?
//!
//! Take the chapter's own definitions as vertices and its own calls as edges,
//! **drop every edge that leaves the chapter**, and count connected
//! components. Two components with no path between them are not a cohesion
//! smell; they are two programs sharing a file.
//!
//! WITHIN a chapter is the tractable half of this question and that is why it
//! is the half built first. A cross-chapter call graph needs cite resolution
//! and rename overrides -- the phases this front end has not finished -- but
//! inside one chapter a name is either a top-level definition of that chapter
//! or it is not, and `scope::resolve_refs` already knows which, under the same
//! `let`, `induction on` and pattern-binder rules the scope rung is graded on.
//!
//! **The graph is UNDIRECTED here, deliberately.** "Can these two halves be
//! separated" is a question about reachability in either direction; a helper
//! called by both halves joins them however the arrows point.
//!
//! **`Section:` is the author's own answer to the same question**, so it is
//! reported beside ours. Three shapes are worth the reading:
//!
//! * a component spanning two sections -- the sections are mislabelled, or one
//!   of them is not a real division;
//! * a section split across components -- it is a label, not a structure;
//! * components that ARE the sections -- the chapter is honest, and that was
//!   worth learning cheaply.
//!
//! **A CONSTANT IS NOT A JOB.** A definition with no parameters is a datum,
//! and a chapter of nothing but data -- `Pond` is seven constants and no
//! calls -- has one component per definition and one job. The count is
//! arithmetically right and analytically empty, so constants are CLASSIFIED
//! rather than dropped: a component with no parameterised definition in it is
//! marked `data`, and a chapter with no parameterised definition at all is
//! marked `data` outright and does not report a split. Hiding them under a
//! threshold would have said the same thing less honestly and would have
//! taken real findings with it.
//!
//! **WHAT A SINGLE-DEFINITION COMPONENT DOES NOT TELL YOU, and it is the
//! reading to be careful with.** A function that calls nothing in its own
//! chapter is not thereby independent -- it may delegate entirely outward, to
//! `Num` or `DeviceMath` or a builtin. `Geom`'s six components are six things
//! that do not touch each other HERE, which is a true statement about this
//! file and not yet a statement about six jobs. The intra-chapter graph
//! cannot separate "independent" from "leaf that delegates", and the
//! cross-chapter graph is what would. Until that exists, read a chapter of
//! singletons as a utility bag -- which is itself worth knowing, and is what
//! `Geom` and `Trig` turn out to be.
//!
//! NO SIZE CUTOFF, and that is a decision rather than an omission. A
//! three-function component looks like noise and is often the opposite: in a
//! small chapter somebody put two things together deliberately, and the reason
//! they thought the two belonged is the thing worth recovering. Small
//! components are also the ones a reader can confirm or refute by eye, which
//! makes them this tool's own calibration set.

use crate::ast::Chapter;
use crate::cst::{Node, NodeKind};
use crate::preamble::header_text;
use crate::scope;
use std::collections::HashMap;

/// One connected component of a chapter's internal call graph.
pub struct Component {
    /// Definition indices, ascending -- source order, because `Chapter.defs`
    /// is in source order.
    pub defs: Vec<usize>,
    /// Every section the component's definitions fall in, in source order and
    /// deduplicated. More than one means the component straddles.
    pub sections: Vec<String>,
    /// No definition here takes a parameter: the component is data, and its
    /// isolation says nothing about cohesion.
    pub data_only: bool,
}

pub struct Cohesion {
    pub chapter: String,
    pub def_names: Vec<String>,
    /// Per definition, the section it was written in. Empty when the chapter
    /// declares no sections at all.
    pub def_section: Vec<String>,
    pub components: Vec<Component>,
    /// Intra-chapter edges as (caller, callee) index pairs, deduplicated,
    /// self-calls dropped. Kept so a caller can print the graph rather than
    /// only the verdict.
    pub edges: Vec<(usize, usize)>,
    /// Per definition, whether it takes parameters. A constant is a datum,
    /// not a job.
    pub is_fn: Vec<bool>,
    /// The chapter declares no parameterised definition at all -- it is a
    /// table, and a component count over it is not a cohesion reading.
    pub data_chapter: bool,
    /// Definitions no other definition in the chapter calls, and that call
    /// nothing in it. Isolated vertices are single-def components; this is
    /// the same set, named, because it reads differently.
    pub isolated: Vec<usize>,
    /// Per definition, the source lines of the BLOCK that moves when the
    /// definition moves: the definition itself plus the prose written above
    /// it, back to where the previous definition ended.
    ///
    /// Prose above a definition is about that definition, so it travels with
    /// it -- which is what `split_chapter.py` already does by hand and what
    /// makes a size here comparable to "how long will the new chapter be".
    /// The FIRST definition is the exception and gets its own extent only:
    /// the prose above it is the chapter's opening, and it stays behind.
    pub def_lines: Vec<u32>,
    /// Per definition, the byte range of that same block, so a tool can MOVE it
    /// rather than re-find it by matching text. Blocks never overlap and never
    /// cross a `Section:` header -- the header belongs to the chapter, not to
    /// the definition under it.
    pub def_span: Vec<(u32, u32)>,
}

/// Which section each definition was written in: the last `Section:` header at
/// a lower offset. Sections are a parse-level fact and the AST does not carry
/// them per definition, so this reads the CST directly.
fn sections_by_offset(tree: &Node, src: &[u8]) -> Vec<(u32, String)> {
    let mut out: Vec<(u32, String)> = Vec::new();
    for n in tree.descendants(NodeKind::SectionHeader) {
        if let Some(t) = n.tokens().next() {
            out.push((t.offset, header_text(n, src)));
        }
    }
    out.sort_by_key(|(o, _)| *o);
    out
}

/// The line extent of each definition's block, keyed by the offset of the
/// definition's NAME token so it can be joined to the AST's `Def`s.
///
/// The CST is lossless, so a `Def` node's first and last tokens bracket exactly
/// what the author wrote for it. Blocks partition the chapter: one ends where
/// the next begins.
fn def_blocks(tree: &Node) -> Vec<(u32, u32, u32)> {
    // Where a `Section:` header sits, a block cannot start before it: the header
    // introduces the chapter's own division and stays behind when a definition
    // is moved out.
    let mut heads: Vec<u32> = Vec::new();
    for n in tree.descendants(NodeKind::SectionHeader) {
        let mut last = None;
        for t in n.tokens() {
            last = Some(t);
        }
        if let Some(t) = last {
            heads.push(t.offset + t.len);
        }
    }

    let mut out: Vec<(u32, u32, u32)> = Vec::new();
    let mut prev_end_line = 0u32;
    let mut prev_end_off = 0u32;
    for n in tree.descendants(NodeKind::Def) {
        let mut toks = n.tokens();
        let Some(first) = toks.next() else { continue };
        // THE PROSE AFTER A DEFINITION IS INSIDE ITS NODE, not the next one's.
        // The tree is lossless and every token belongs to something, so the
        // paragraph a reader sees as an introduction to the definition BELOW is
        // parked at the tail of the definition above. Taking the node's last
        // token as the end therefore attributes prose backwards -- which moved
        // the parts table's own introduction out from under it, and left it
        // stranded above an unrelated definition.
        //
        // The end of a definition is its last token that is not prose or
        // layout. Everything between that and the next definition's code is
        // the next one's, which is what a reader means by "the prose above it".
        let mut last = first;
        for t in n.tokens() {
            if !matches!(
                t.kind,
                crate::token::Kind::ProseText
                    | crate::token::Kind::SkippedProse
                    | crate::token::Kind::Spaces
                    | crate::token::Kind::Newline
                    | crate::token::Kind::Indent
                    | crate::token::Kind::Dedent
                    | crate::token::Kind::Unmapped
            ) {
                last = t;
            }
        }
        // Nested definitions do not exist, but `descendants` cannot know that,
        // so a node starting inside the previous one is skipped rather than
        // counted twice.
        if !out.is_empty() && first.line < prev_end_line {
            continue;
        }
        let lines = if out.is_empty() {
            last.line.saturating_sub(first.line) + 1
        } else {
            last.line.saturating_sub(prev_end_line)
        };
        // The block reaches back over the prose above the definition, stopping
        // at whichever came last: the previous definition or a section header.
        let mut start = if out.is_empty() { first.offset } else { prev_end_off };
        for &h in &heads {
            if h > start && h <= first.offset {
                start = h;
            }
        }
        let end = last.offset + last.len;
        out.push((start, end, lines));
        // Keyed for lookup by the NAME token, which is inside the block.
        prev_end_line = last.line;
        prev_end_off = end;
    }
    out
}

/// The block a name token at `offset` belongs to: the last one that starts at
/// or before it. A `Def`'s name is inside its own node, so this cannot reach
/// past it.
fn block_at(blocks: &[(u32, u32, u32)], offset: u32) -> (u32, u32, u32) {
    let mut cur = (0u32, 0u32, 0u32);
    for &b in blocks {
        if b.0 <= offset {
            cur = b;
        } else {
            break;
        }
    }
    cur
}

fn section_for(sections: &[(u32, String)], offset: u32) -> String {
    let mut cur = String::new();
    for (o, name) in sections {
        if *o <= offset {
            cur = name.clone();
        } else {
            break;
        }
    }
    cur
}

pub fn analyse(ch: &Chapter, tree: &Node, src: &[u8]) -> Cohesion {
    let n = ch.defs.len();
    let def_names: Vec<String> = ch.defs.iter().map(|d| d.name.clone()).collect();
    let is_fn: Vec<bool> = ch.defs.iter().map(|d| !d.params.is_empty()).collect();
    let data_chapter = !is_fn.iter().any(|&f| f);

    // A name may be defined twice in one chapter -- that is CDX3001 and the
    // resolver reports it. The graph takes the FIRST, so a duplicate does not
    // silently become a second vertex nothing points at.
    let mut index: HashMap<&str, usize> = HashMap::new();
    for (i, name) in def_names.iter().enumerate() {
        index.entry(name.as_str()).or_insert(i);
    }

    let (_, refs) = scope::resolve_refs(ch);

    let mut edges: Vec<(usize, usize)> = Vec::new();
    for (i, names) in refs.iter().enumerate() {
        for name in names {
            if let Some(&j) = index.get(name.as_str()) {
                if i != j {
                    edges.push((i, j));
                }
            }
        }
    }
    edges.sort_unstable();
    edges.dedup();

    // Union-find over the undirected graph.
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(parent: &mut Vec<usize>, mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    for &(a, b) in &edges {
        let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
        if ra != rb {
            parent[ra] = rb;
        }
    }

    let blocks = def_blocks(tree);
    let found: Vec<(u32, u32, u32)> =
        ch.defs.iter().map(|d| block_at(&blocks, d.span.offset)).collect();
    let def_lines: Vec<u32> = found.iter().map(|b| b.2).collect();
    let def_span: Vec<(u32, u32)> = found.iter().map(|b| (b.0, b.1)).collect();

    let sections = sections_by_offset(tree, src);
    let def_section: Vec<String> = if sections.is_empty() {
        vec![String::new(); n]
    } else {
        ch.defs.iter().map(|d| section_for(&sections, d.span.offset)).collect()
    };

    let mut groups: HashMap<usize, Vec<usize>> = HashMap::new();
    for i in 0..n {
        let r = find(&mut parent, i);
        groups.entry(r).or_default().push(i);
    }
    let mut components: Vec<Component> = groups
        .into_values()
        .map(|mut defs| {
            defs.sort_unstable();
            let mut secs: Vec<String> = Vec::new();
            for &i in &defs {
                let s = &def_section[i];
                if !secs.contains(s) {
                    secs.push(s.clone());
                }
            }
            let data_only = !defs.iter().any(|&i| is_fn[i]);
            Component { defs, sections: secs, data_only }
        })
        .collect();
    // Largest first, then by first definition, so the ordering is total and
    // does not depend on the hash map.
    components.sort_by(|a, b| {
        b.defs.len().cmp(&a.defs.len()).then(a.defs[0].cmp(&b.defs[0]))
    });

    let mut touched = vec![false; n];
    for &(a, b) in &edges {
        touched[a] = true;
        touched[b] = true;
    }
    let isolated: Vec<usize> = (0..n).filter(|&i| !touched[i]).collect();

    Cohesion {
        chapter: ch.name.clone(),
        def_names,
        def_section,
        is_fn,
        data_chapter,
        components,
        edges,
        isolated,
        def_lines,
        def_span,
    }
}
