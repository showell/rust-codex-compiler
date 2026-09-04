//! Who reads this name, and which chapter defines it -- across a whole tree.
//!
//! **This is a grep replacement, and it exists because grep cannot do the job
//! in this language.** Codex is literate: the prose lives in the same file as
//! the code, so `grep near` finds the near plane, "near zero" and "near-plane
//! clipping" and has no way to tell them apart. Codex names also carry hyphens,
//! and `-` is not a word character, so `grep -w near` matches inside
//! `clip-near`. Every usage table built by hand for the Camera split had to be
//! rebuilt twice for those two reasons before it was right.
//!
//! **It needs no cite resolution, and that is not a shortcut.**
//! `PORTING_NOTES` B5: "chapters share ONE FLAT NAMESPACE inside a bundle" --
//! CDX3001 refuses a bundle holding two definitions of one name. So within any
//! bundle a name has exactly one definition, and the index can map name to
//! chapter directly. Where a name IS defined twice in the tree, that is two
//! chapters that never share a bundle -- every entry chapter defines `opening`
//! -- and the index reports the ambiguity rather than choosing.
//!
//! **Types and constructors count as definitions**, because a cite is as often
//! for `Vec3` or `ScreenPt` as for a function. The resolver's walk does not
//! see them: a record literal's type name is deliberately not resolved and
//! type annotations are not expressions. So they are collected here, by a
//! second and much simpler walk that needs no scope -- a type name cannot be
//! shadowed by a local.

use crate::symbol::SymTab;
use crate::ast::*;
use std::collections::{BTreeMap, BTreeSet};

/// What one chapter defines and what it reads.
pub struct ChapterRefs {
    pub chapter: String,
    pub path: String,
    /// Value definitions, type definitions and constructors, all of which
    /// occupy the one flat namespace.
    pub defines: BTreeSet<String>,
    /// Every name read that this chapter does not itself define.
    pub reads: BTreeSet<String>,
    /// Every name read, INCLUDING the ones this chapter defines itself. The
    /// field above answers "what does this chapter need from elsewhere"; this
    /// one answers "is this name read at all", which is a different question
    /// and the one dead code turns on. A definition only its own chapter calls
    /// is alive; a definition nothing calls, its own chapter included, is not.
    pub reads_all: BTreeSet<String>,
    /// Names that appear only in an EFFECT ROW (`[Console] Nothing`). They are
    /// reads -- `who` and `dead` must see them -- but a bundle does NOT carry a
    /// chapter for them: an effect is grounded by the plug, and the real driver
    /// subject uses `[Console]` without bundling core/Console.codex and
    /// compiles. `bundle` subtracts this set for that reason.
    pub effect_reads: BTreeSet<String>,
    /// name -> what kind of definition it is. A dead record and a dead
    /// function do not read the same way to someone deciding whether to delete.
    pub kinds: BTreeMap<String, &'static str>,
    /// name -> the source line it is defined on, for jumping to it.
    pub lines: BTreeMap<String, u32>,
    /// Definitions that PROVE a claim. The checker enters them and no
    /// definition calls them, so they are read by nothing and alive anyway.
    pub claims: BTreeSet<String>,
    /// (reader, read) with self-references dropped. Keeping the reader is what
    /// lets a caller ask "is this read by anything STILL ALIVE", which is a
    /// stronger question than "is this read at all" -- the callees of a dead
    /// function are dead too, and only the pairs can see that.
    pub edges: BTreeSet<(String, String)>,
}

pub struct Index {
    pub chapters: Vec<ChapterRefs>,
    /// name -> the chapters defining it. More than one is legal across the
    /// tree and illegal inside one bundle.
    pub defined_in: BTreeMap<String, Vec<usize>>,
    /// name -> the chapters reading it.
    pub read_in: BTreeMap<String, Vec<usize>>,
    /// name -> the chapters reading it, self-reads included. See `reads_all`.
    pub read_anywhere: BTreeMap<String, Vec<usize>>,
}

/// A TYPE VARIABLE IS NOT A REFERENCE, and Codex tells them apart by case.
/// Type names are capitalised -- `Fat16Volume`, `IRChapter`, `Maybe` -- and a
/// lowercase name in type position is the `a` of `List a` or the variable a
/// `forall` bound. Collecting those as reads makes every generic chapter look
/// like it depends on definitions called `a`, `b` and `c`, which is what a
/// bundle check reported on a bundle that compiles.
///
/// Checked against the whole checkout before relying on it: no chapter declares
/// a lowercase record or variant.
thread_local! {
    /// Effect-row names seen while walking one chapter. A thread-local keeps
    /// `type_names`' signature -- it has eleven call sites -- and this is a
    /// single-threaded tool.
    static EFFECT_SEEN: std::cell::RefCell<BTreeSet<String>> =
        std::cell::RefCell::new(BTreeSet::new());
}

fn type_names(syms: &SymTab, t: &TypeExpr, out: &mut BTreeSet<String>) {
    match t {
        TypeExpr::Named(n, _) => {
            let n = syms.text(*n);
            if !n.starts_with(|c: char| c.is_lowercase()) {
                out.insert(n.to_string());
            }
        }
        TypeExpr::Fun(a, b, _) | TypeExpr::PropEq(a, b, _) => {
            type_names(syms, a, out);
            type_names(syms, b, out);
        }
        TypeExpr::App(c, args, _) => {
            type_names(syms, c, out);
            for a in args {
                type_names(syms, a, out);
            }
        }
        // AN EFFECT ROW NAMES CHAPTERS. `[Console] Nothing` reads `Console`,
        // which core/Console.codex defines, and dropping the row made `xref who
        // Console` answer "read by NOTHING" across 1,501 files that write it --
        // and put Display, Microphone and Sensors in `dead`'s delete list.
        TypeExpr::Effect(names, _, _, r, _) => {
            for n in names {
                let n = syms.text(*n);
                if !n.starts_with(|c: char| c.is_lowercase()) {
                    out.insert(n.to_string());
                    EFFECT_SEEN.with(|e| e.borrow_mut().insert(n.to_string()));
                }
            }
            type_names(syms, r, out)
        }
        TypeExpr::BoundedInt(b, ..) | TypeExpr::Linear(b, _) => type_names(syms, b, out),
        TypeExpr::Constrained(_, _, b, _) => type_names(syms, b, out),
        TypeExpr::Forall(_, v, b, _) => {
            type_names(syms, v, out);
            type_names(syms, b, out);
        }
    }
}

/// Record-literal type names and constructor patterns: the two places a name
/// is used that the resolver's expression walk deliberately skips.
fn ctor_and_record_names(syms: &SymTab, e: &Expr, out: &mut BTreeSet<String>) {
    let mut kids: Vec<&Expr> = Vec::new();
    match e {
        Expr::Record(n, fs, _) => {
            out.insert(syms.text(*n).to_string());
            for f in fs {
                kids.push(&f.value);
            }
        }
        Expr::Apply(a, b, _) | Expr::Binary(a, _, b, _) | Expr::FieldAssign(a, _, b, _) => {
            kids.push(a);
            kids.push(b);
        }
        Expr::Unary(a, _) | Expr::Lazy(a, _) | Expr::FieldAccess(a, _, _) => kids.push(a),
        Expr::If(a, b, c, _) => {
            kids.push(a);
            kids.push(b);
            kids.push(c);
        }
        Expr::Let(binds, body, _) => {
            for b in binds {
                kids.push(&b.value);
            }
            kids.push(body);
        }
        Expr::Lambda(_, body, _) => kids.push(body),
        Expr::WithTimeout(wt) => kids.push(&wt.body),
        Expr::Match(scrut, arms, _) | Expr::Induction(scrut, arms, _) => {
            kids.push(scrut);
            for a in arms {
                pat_names(syms, &a.pattern, out);
                kids.push(&a.guard);
                kids.push(&a.body);
            }
        }
        Expr::List(xs, _) => kids.extend(xs.iter()),
        Expr::Act(ss, _) => {
            for s in ss {
                match s {
                    ActStmt::Exec(x, _) | ActStmt::Bind(_, x, _) => kids.push(x),
                }
            }
        }
        Expr::Handle(h) => {
            kids.push(&h.body);
            for c in &h.clauses {
                kids.push(&c.body);
            }
        }
        Expr::Try(t) => {
            for region in [&t.body, &t.fallback, &t.failure] {
                for s in region {
                    match s {
                        ActStmt::Exec(x, _) | ActStmt::Bind(_, x, _) => kids.push(x),
                    }
                }
            }
        }
        Expr::Lit(..) | Expr::NameRef(..) | Expr::Error(..) => {}
    }
    for k in kids {
        ctor_and_record_names(syms, k, out);
    }
}

fn pat_names(syms: &SymTab, p: &Pat, out: &mut BTreeSet<String>) {
    match p {
        Pat::Ctor(n, subs, _) => {
            out.insert(syms.text(*n).to_string());
            for s in subs {
                pat_names(syms, s, out);
            }
        }
        Pat::Vec_(subs, _) => {
            for s in subs {
                pat_names(syms, s, out);
            }
        }
        Pat::Var(..) | Pat::Lit(..) | Pat::Wild(_) => {}
    }
}

pub fn chapter_refs(ch: &Chapter, path: &str) -> ChapterRefs {
    EFFECT_SEEN.with(|e| e.borrow_mut().clear());
    let mut kinds: BTreeMap<String, &'static str> = BTreeMap::new();
    let mut lines: BTreeMap<String, u32> = BTreeMap::new();
    let mut defines: BTreeSet<String> = ch.defs.iter().map(|d| ch.syms.text(d.name).to_string()).collect();
    let mut claims: BTreeSet<String> = BTreeSet::new();
    for d in &ch.defs {
        kinds.insert(
            ch.syms.text(d.name).to_string(),
            if d.is_claim {
                "proof"
            } else if d.params.is_empty() {
                "constant"
            } else {
                "function"
            },
        );
        lines.insert(ch.syms.text(d.name).to_string(), d.span.line);
        if d.is_claim {
            claims.insert(ch.syms.text(d.name).to_string());
        }
    }
    for t in &ch.type_defs {
        let (n, sp) = match t {
            TypeDef::Record(n, _, _, _, sp) => (n, sp),
            TypeDef::Unit(n, _, sp) => (n, sp),
            TypeDef::Variant(n, _, _, sp) => (n, sp),
        };
        kinds.insert(ch.syms.text(*n).to_string(), "type");
        lines.insert(ch.syms.text(*n).to_string(), sp.line);
        if let TypeDef::Variant(_, _, cs, _) = t {
            for c in cs {
                kinds.insert(ch.syms.text(c.name).to_string(), "constructor");
                lines.insert(ch.syms.text(c.name).to_string(), c.span.line);
            }
        }
    }
    for t in &ch.type_defs {
        match t {
            TypeDef::Record(n, ..) => {
                defines.insert(ch.syms.text(*n).to_string());
            }
            TypeDef::Unit(n, ..) => {
                defines.insert(ch.syms.text(*n).to_string());
            }
            TypeDef::Variant(n, _, cs, _) => {
                defines.insert(ch.syms.text(*n).to_string());
                for c in cs {
                    defines.insert(ch.syms.text(c.name).to_string());
                }
            }
        }
    }
    // A3: their SIGNATURES are reads, and were walked nowhere. GpuEffect's
    // `kernel-launch : KernelDescriptor, LaunchConfig, ... -> [Gpu.Compute] Nothing`
    // reads three types from two other chapters, and `xref bundle` called that
    // file complete.
    let mut sig_reads: BTreeSet<String> = BTreeSet::new();
    for e in &ch.effect_defs {
        for o in &e.ops {
            type_names(&ch.syms, &o.type_expr, &mut sig_reads);
        }
    }
    for c in &ch.class_defs {
        for m in &c.methods {
            type_names(&ch.syms, &m.type_expr, &mut sig_reads);
        }
    }
    for e in &ch.effect_defs {
        defines.insert(ch.syms.text(e.name).to_string());
        kinds.insert(ch.syms.text(e.name).to_string(), "effect");
        lines.insert(ch.syms.text(e.name).to_string(), e.span.line);
        for o in &e.ops {
            defines.insert(ch.syms.text(o.name).to_string());
            kinds.insert(ch.syms.text(o.name).to_string(), "effect op");
            lines.insert(ch.syms.text(o.name).to_string(), o.span.line);
        }
    }
    for c in &ch.class_defs {
        defines.insert(ch.syms.text(c.name).to_string());
        kinds.insert(ch.syms.text(c.name).to_string(), "class");
        lines.insert(ch.syms.text(c.name).to_string(), c.span.line);
        for m in &c.methods {
            defines.insert(ch.syms.text(m.name).to_string());
            kinds.insert(ch.syms.text(m.name).to_string(), "class method");
            lines.insert(ch.syms.text(m.name).to_string(), m.span.line);
        }
    }

    let mut reads: BTreeSet<String> = sig_reads.clone();
    // Reads ATTRIBUTED TO THEIR READER, so a definition's reference to itself
    // can be dropped. A self-recursive function that nothing calls is dead, and
    // counting its own recursive call as a read makes it immortal: that is
    // exactly what hid `emit-zig-apply-args`, which calls only itself and
    // `emit-zig-expr`, from the first version of this.
    let mut by_reader: BTreeSet<(String, String)> = BTreeSet::new();
    for e in &ch.effect_defs {
        for o in &e.ops {
            let mut mine = BTreeSet::new();
            type_names(&ch.syms, &o.type_expr, &mut mine);
            for n in mine {
                by_reader.insert((ch.syms.text(o.name).to_string(), n));
            }
        }
    }
    for c in &ch.class_defs {
        for m in &c.methods {
            let mut mine = BTreeSet::new();
            type_names(&ch.syms, &m.type_expr, &mut mine);
            for n in mine {
                by_reader.insert((ch.syms.text(m.name).to_string(), n));
            }
        }
    }
    let (_, per_def) = crate::scope::resolve_refs(ch);
    for (i, names) in per_def.into_iter().enumerate() {
        let reader = ch.defs.get(i).map(|d| ch.syms.text(d.name).to_string()).unwrap_or_default();
        for n in names {
            reads.insert(n.clone());
            by_reader.insert((reader.clone(), n));
        }
    }
    for d in &ch.defs {
        let mut mine: BTreeSet<String> = BTreeSet::new();
        for t in &d.declared_type {
            type_names(&ch.syms, t, &mut mine);
        }
        ctor_and_record_names(&ch.syms, &d.body, &mut mine);
        for n in mine {
            reads.insert(n.clone());
            by_reader.insert((ch.syms.text(d.name).to_string(), n));
        }
    }
    // A type definition's own field and constructor types are references too:
    // `RiderPt = record { right : Real }` reads `Real`, and a variant's
    // payloads reach other chapters' types.
    for t in &ch.type_defs {
        let mut mine: BTreeSet<String> = BTreeSet::new();
        let owner = match t {
            TypeDef::Record(n, _, fs, ..) => {
                for f in fs {
                    type_names(&ch.syms, &f.type_expr, &mut mine);
                }
                ch.syms.text(*n).to_string()
            }
            TypeDef::Variant(n, _, cs, _) => {
                for c in cs {
                    for f in &c.fields {
                        type_names(&ch.syms, f, &mut mine);
                    }
                    for r in &c.return_type {
                        type_names(&ch.syms, r, &mut mine);
                    }
                }
                ch.syms.text(*n).to_string()
            }
            TypeDef::Unit(n, inner, _) => {
                type_names(&ch.syms, inner, &mut mine);
                ch.syms.text(*n).to_string()
            }
        };
        for n in mine {
            reads.insert(n.clone());
            by_reader.insert((owner.clone(), n));
        }
    }

    // A recursive type or function reads only itself; that is not a reader.
    let reads_all: BTreeSet<String> =
        by_reader.iter().filter(|(r, n)| r != n).map(|(_, n)| n.clone()).collect();
    for d in &defines {
        reads.remove(d);
    }
    for n in &defines {
        kinds.entry(n.clone()).or_insert("other");
    }
    ChapterRefs {
        chapter: ch.syms.text(ch.name).to_string(),
        path: path.to_string(),
        defines,
        reads,
        reads_all,
        kinds,
        lines,
        claims,
        effect_reads: EFFECT_SEEN.with(|e| e.borrow().clone()),
        edges: by_reader.into_iter().filter(|(r, n)| r != n).collect(),
    }
}

pub fn build(chapters: Vec<ChapterRefs>) -> Index {
    let mut defined_in: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    let mut read_in: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    let mut read_anywhere: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (i, c) in chapters.iter().enumerate() {
        for n in &c.defines {
            defined_in.entry(n.clone()).or_default().push(i);
        }
        for n in &c.reads {
            read_in.entry(n.clone()).or_default().push(i);
        }
        for n in &c.reads_all {
            read_anywhere.entry(n.clone()).or_default().push(i);
        }
    }
    Index { chapters, defined_in, read_in, read_anywhere }
}
