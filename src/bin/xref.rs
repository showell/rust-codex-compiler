//! Who reads this name, and which chapter defines it.
//!
//!     xref who <name> <dir>...      every chapter reading it, and its definer
//!     xref chapter <Name> <dir>...  what one chapter reads, grouped by definer
//!     xref dangling <dir>...        names read that nothing in the tree defines
//!     xref dead <dir>...            definitions nothing in the tree reads
//!     xref bundle <subject.codex> <dir>...   names a BUNDLE reads and does not define
//!     xref arity <ours> <compiler-dir>...    OUR calls whose argument count no longer matches
//!
//! The grep replacement. See `xref.rs` for why grep cannot do this in a
//! literate language whose names carry hyphens.
//!
//! `dead` is the inverse of `dangling`, and it counts TYPES AND CONSTRUCTORS
//! and constants, not just functions: the resolver's walk does not see a record
//! literal's type name or a type annotation, and a dead record reads exactly
//! like a live one to anything that only follows calls.
//!
//! **Two things keep it honest.** A name read only by its own chapter is
//! ALIVE, so the reads it consults are `reads_all`, which the ordinary
//! cross-chapter view deliberately drops. And a name no Codex reads can still
//! be load-bearing from outside the language: `zig-prelude` is read by nothing
//! here and `build/check-zig-prelude-surface.ps1` derives a gate from its
//! source text. So every non-`.codex` file under the scanned tree is searched
//! for the name, shallowly, and a hit moves the finding to a second list that
//! says DO NOT DELETE rather than dropping it.
//!
//! **It does not decide, and it cannot see prose.** Deleting a definition
//! deletes the paragraph above it, which may explain something still alive.
//! Where that paragraph names another definition, the report says so and says
//! where to look. Read the diff.

use codexc::desugar::Desugar;
use codexc::parser;
use codexc::xref::{self, ChapterRefs, Index};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (mode, arg, paths): (&str, Option<&str>, &[String]) = match args.first().map(String::as_str)
    {
        Some("who") if args.len() >= 3 => ("who", Some(&args[1]), &args[2..]),
        Some("chapter") if args.len() >= 3 => ("chapter", Some(&args[1]), &args[2..]),
        Some("dangling") if args.len() >= 2 => ("dangling", None, &args[1..]),
        Some("dead") if args.len() >= 2 => ("dead", None, &args[1..]),
        Some("bundle") if args.len() >= 2 => ("bundle", Some(&args[1]), &args[2..]),
        Some("arity") if args.len() >= 3 => ("arity", Some(&args[1]), &args[2..]),
        _ => {
            eprintln!("usage: xref who <name> <dir>...");
            eprintln!("       xref chapter <Name> <dir>...");
            eprintln!("       xref dangling <dir>...");
            eprintln!("       xref dead <dir>...  [--roots a,b,c] [--in <path substring>] [--all-files]");
            eprintln!("       xref bundle <subject.codex> <dir>...");
            eprintln!("       xref arity <ours.codex|dir> <compiler-dir>...  [--partial] [--phases]");
            return ExitCode::from(2);
        }
    };

    // `--roots` names definitions that are entered from outside the language
    // and so are alive however few Codex readers they have. `opening` is every
    // entry chapter's, and is always one.
    let mut roots: std::collections::BTreeSet<String> =
        ["opening"].iter().map(|s| s.to_string()).collect();
    let mut paths: Vec<String> = paths.to_vec();
    if let Some(i) = paths.iter().position(|a| a == "--roots") {
        if i + 1 < paths.len() {
            roots.extend(paths[i + 1].split(',').map(|s| s.trim().to_string()));
        }
        paths.drain(i..(i + 2).min(paths.len()));
    }
    let mut only: Option<String> = None;
    if let Some(i) = paths.iter().position(|a| a == "--in") {
        if i + 1 < paths.len() {
            only = Some(paths[i + 1].clone());
        }
        paths.drain(i..(i + 2).min(paths.len()));
    }
    let mut all_files = false;
    if let Some(i) = paths.iter().position(|a| a == "--all-files") {
        all_files = true;
        paths.remove(i);
    }
    // Partial application is legal, so a short call in ARGUMENT position is
    // ordinary and dropped. `--partial` shows those too, for the reader chasing
    // one specific name.
    let mut partial = false;
    if let Some(i) = paths.iter().position(|a| a == "--partial") {
        partial = true;
        paths.remove(i);
    }
    // The driver's phase functions are the ones that have actually cost us
    // time; `--phases` reports nothing else.
    let mut phases_only = false;
    if let Some(i) = paths.iter().position(|a| a == "--phases") {
        phases_only = true;
        paths.remove(i);
    }
    let paths = &paths[..];

    let mut files: Vec<PathBuf> = Vec::new();
    for p in paths {
        collect(Path::new(p), &mut files);
    }
    files.sort();
    let mut chapters: Vec<ChapterRefs> = Vec::new();
    let mut full: Vec<PathBuf> = Vec::new();
    for f in &files {
        let Ok(src) = std::fs::read(f) else { continue };
        let parsed = parser::parse(&src);
        let mut dg = Desugar::new(&src);
        let ch = dg.chapter(&parsed.tree);
        if ch.name.is_empty() {
            continue;
        }
        chapters.push(xref::chapter_refs(&ch, &short(f)));
        full.push(f.clone());
    }
    let ix = xref::build(chapters);

    match mode {
        "who" => who(&ix, arg.unwrap()),
        "chapter" => chapter(&ix, arg.unwrap()),
        "dead" => dead(&ix, &full, paths, &roots, only.as_deref(), all_files),
        "bundle" => return bundle(arg.unwrap(), &ix, paths),
        "arity" => return arity_mode(arg.unwrap(), paths, partial, phases_only),
        _ => dangling(&ix),
    }
    ExitCode::SUCCESS
}

fn who(ix: &Index, name: &str) {
    match ix.defined_in.get(name) {
        None => println!("{name}: DEFINED NOWHERE in this tree"),
        Some(ds) => {
            for &i in ds {
                println!("{name}: defined in {} ({})", ix.chapters[i].chapter, ix.chapters[i].path);
            }
            // Two definers is legal across a tree and illegal inside one
            // bundle -- every entry chapter defines `opening`. Say so rather
            // than picking.
            if ds.len() > 1 {
                println!("  ^ {} definitions; these chapters never share a bundle", ds.len());
            }
        }
    }
    let readers = ix.read_in.get(name).cloned().unwrap_or_default();
    if readers.is_empty() {
        println!("  read by NOTHING");
        return;
    }
    println!("  read by {} chapters:", readers.len());
    for i in readers {
        println!("    {:<22} {}", ix.chapters[i].chapter, ix.chapters[i].path);
    }
}

fn chapter(ix: &Index, name: &str) {
    // A CHAPTER IS NOT A FILE. One chapter may span several files, each a PAGE
    // carrying `Page N of M` at its foot -- `Zig Emitter` is four of them. This
    // took the FIRST page and reported it as the whole chapter: 194 definitions
    // where the chapter has 421, and the missing pages then showed up as a
    // foreign definer, so the chapter appeared to read itself from outside.
    let pages: Vec<usize> =
        (0..ix.chapters.len()).filter(|&i| ix.chapters[i].chapter == name).collect();
    if pages.is_empty() {
        eprintln!("no chapter named {name}");
        return;
    }
    let mut defines: std::collections::BTreeSet<&str> = Default::default();
    let mut reads: std::collections::BTreeSet<&str> = Default::default();
    for &i in &pages {
        defines.extend(ix.chapters[i].defines.iter().map(String::as_str));
        reads.extend(ix.chapters[i].reads.iter().map(String::as_str));
    }
    let where_: Vec<&str> = pages.iter().map(|&i| ix.chapters[i].path.as_str()).collect();
    if pages.len() == 1 {
        println!("{} ({}) defines {}, reads {}", name, where_[0], defines.len(), reads.len());
    } else {
        println!(
            "{} defines {}, reads {} -- {} pages: {}",
            name,
            defines.len(),
            reads.len(),
            pages.len(),
            where_.join(", ")
        );
    }
    let mut by_definer: std::collections::BTreeMap<String, Vec<&str>> = Default::default();
    let mut unknown: Vec<&str> = Vec::new();
    for n in reads {
        // A name this chapter defines on ANY page is its own, not a foreign
        // read, however many files the chapter is spread across.
        if defines.contains(n) {
            continue;
        }
        match ix.defined_in.get(n) {
            Some(ds) if !ds.is_empty() => {
                by_definer.entry(ix.chapters[ds[0]].chapter.clone()).or_default().push(n)
            }
            _ => unknown.push(n),
        }
    }
    for (definer, names) in by_definer {
        println!("  from {definer}:");
        for line in wrap(&names, 68) {
            println!("        {line}");
        }
    }
    if !unknown.is_empty() {
        // Builtins and the foreword live outside the scanned tree, so this is
        // a list to read and not a list of errors.
        println!("  outside this tree ({}): builtins, foreword, type names", unknown.len());
    }
}

fn dangling(ix: &Index) {
    for (name, readers) in &ix.read_in {
        if !ix.defined_in.contains_key(name) {
            let who: Vec<&str> =
                readers.iter().map(|&i| ix.chapters[i].chapter.as_str()).collect();
            println!("{:<28} {}", name, who.join(" "));
        }
    }
}

fn wrap(names: &[&str], width: usize) -> Vec<String> {
    let mut out = Vec::new();
    let mut line = String::new();
    for n in names {
        if !line.is_empty() && line.len() + 1 + n.len() > width {
            out.push(std::mem::take(&mut line));
        }
        if !line.is_empty() {
            line.push(' ');
        }
        line.push_str(n);
    }
    if !line.is_empty() {
        out.push(line);
    }
    out
}

fn short(p: &Path) -> String {
    let parts: Vec<_> = p.components().collect();
    let keep = parts.len().saturating_sub(2);
    parts[keep..].iter().map(|c| c.as_os_str().to_string_lossy()).collect::<Vec<_>>().join("/")
}

fn collect(p: &Path, out: &mut Vec<PathBuf>) {
    if p.is_dir() {
        let Ok(rd) = std::fs::read_dir(p) else { return };
        for e in rd.flatten() {
            collect(&e.path(), out);
        }
    } else if p.extension().is_some_and(|e| e == "codex") {
        out.push(p.to_path_buf());
    }
}

/// Definitions nothing in the tree reads.
///
/// A finding is only as good as the tree it was measured over: scan
/// `codex/plugs/zig` alone and every name looks dead, because the readers are
/// elsewhere. So the ANALYSIS is always the whole set of directories given, and
/// `--in <substring>` filters only what gets REPORTED. Narrowing the scan and
/// narrowing the report are different things, and only one of them is safe.
fn dead(
    ix: &Index,
    full: &[PathBuf],
    scan_dirs: &[String],
    roots: &std::collections::BTreeSet<String>,
    only: Option<&str>,
    all_files: bool,
) {
    use std::collections::BTreeSet;

    // Alive = read by something ALIVE. Not "read at all": the callees of a dead
    // function are dead too, so the answer is a fixed point rather than one
    // pass over in-degrees. Iterating found 3 corpses in the zig plug where a
    // single pass found 1.
    //
    // A DEAD CYCLE STILL SURVIVES THIS. Two definitions that call only each
    // other read each other, so each keeps the other alive and the pair is
    // never reached. Catching that needs the strongly connected components and
    // is not attempted here; the report says so rather than implying the list
    // is complete.
    let mut alive: BTreeSet<&str> = ix.defined_in.keys().map(String::as_str).collect();
    let mut proofs = 0usize;
    for c in &ix.chapters {
        proofs += c.claims.len();
    }
    let edges: Vec<(&str, &str)> = ix
        .chapters
        .iter()
        .flat_map(|c| c.edges.iter().map(|(r, n)| (r.as_str(), n.as_str())))
        .collect();
    let immortal: BTreeSet<&str> = ix
        .chapters
        .iter()
        .flat_map(|c| c.claims.iter().map(String::as_str))
        .chain(roots.iter().map(String::as_str))
        .collect();
    loop {
        let mut read_by_live: BTreeSet<&str> = BTreeSet::new();
        for (r, n) in &edges {
            if alive.contains(r) {
                read_by_live.insert(n);
            }
        }
        let doomed: Vec<&str> = alive
            .iter()
            .copied()
            .filter(|n| !read_by_live.contains(n) && !immortal.contains(n))
            .collect();
        if doomed.is_empty() {
            break;
        }
        for n in doomed {
            alive.remove(n);
        }
    }

    let mut findings: Vec<(usize, &str)> = Vec::new();
    for (i, c) in ix.chapters.iter().enumerate() {
        for n in &c.defines {
            if alive.contains(n.as_str()) {
                continue;
            }
            if only.is_some_and(|f| !c.path.contains(f)) {
                continue;
            }
            findings.push((i, n.as_str()));
        }
    }
    findings.sort();

    // Every file under the tree that could plausibly NAME a Codex definition as
    // an identifier -- a gate deriving its answer from Codex source text is a
    // real reader no Codex analysis can see (`zig-prelude` and
    // check-zig-prelude-surface.ps1). Expected-output and prose files are NOT
    // that: they mention names the way this sentence does. `--all-files` widens
    // it when you want to see every mention.
    const CODEISH: &[&str] =
        &["ps1", "py", "sh", "js", "mjs", "json", "ts", "psm1", "bat", "cmd", "rs", "zig"];
    let mut outside: Vec<(PathBuf, String)> = Vec::new();
    for d in scan_dirs {
        collect_other(Path::new(d), &mut outside, if all_files { None } else { Some(CODEISH) });
    }

    let all_names: BTreeSet<&str> = ix.defined_in.keys().map(String::as_str).collect();

    let mut safe: Vec<String> = Vec::new();
    let mut held: Vec<String> = Vec::new();
    for (i, name) in &findings {
        let c = &ix.chapters[*i];
        let kind = c.kinds.get(*name).copied().unwrap_or("other");
        let line = c.lines.get(*name).copied().unwrap_or(0);
        let mut row = format!("  {kind:<13} {name:<34} {}:{}", c.path, line);

        // Prose above a definition travels with it. Where that paragraph names
        // something still alive, deleting it costs an explanation of the
        // survivor rather than of the corpse -- so say where to look.
        if let Some(f) = full.get(*i) {
            let m = prose_mentions(f, name, &all_names);
            if !m.is_empty() {
                row.push_str(&format!("\n      prose also names: {}", m.join(" ")));
            }
        }

        let hits: Vec<String> = outside
            .iter()
            .filter(|(_, body)| names_it(body, name))
            .map(|(p, _)| short(p))
            .take(6)
            .collect();
        if hits.is_empty() {
            safe.push(row);
        } else {
            row.push_str(&format!("\n      named outside Codex by: {}", hits.join(" ")));
            held.push(row);
        }
    }

    if safe.is_empty() && held.is_empty() {
        println!("nothing unread{}", only.map(|f| format!(" under `{f}`")).unwrap_or_default());
    }
    if !safe.is_empty() {
        println!("UNREAD, and named in no other file -- candidates ({}):", safe.len());
        for r in &safe {
            println!("{r}");
        }
    }
    if !held.is_empty() {
        println!("\nUNREAD BY CODEX, BUT NAMED OUTSIDE IT -- look before deleting ({}):", held.len());
        for r in &held {
            println!("{r}");
        }
    }
    println!(
        "\n{} chapters, {} non-Codex files searched, {} proofs skipped (the checker enters them).",
        ix.chapters.len(),
        outside.len(),
        proofs
    );
    println!("Roots taken as alive: {}.", roots.iter().cloned().collect::<Vec<_>>().join(" "));
    println!("READ THE DIFF: a definition's prose sits above it and goes with it.");
    println!("Not found here: a dead CYCLE -- definitions that call only each other.");
}

/// Does `body` name `n` as an identifier rather than inside a longer one?
///
/// This is the whole reason `xref` exists, applied to the files it does not
/// parse: `sub` is inside `subject`, and `-` is not a word character, so a
/// plain `contains` reported every `run.ps1` in the tree as a reader of `sub`.
fn names_it(body: &str, n: &str) -> bool {
    // AN EMPTY NEEDLE MATCHES EVERYWHERE AND ADVANCES BY ONE BYTE, which walks
    // into the middle of a multi-byte character and PANICS on the next slice.
    // The checkout produces empty definition names (a `bounded` declaration
    // parses one), so this is reachable, and an abort is worse than any wrong
    // answer this tool could give.
    if n.is_empty() {
        return false;
    }
    let bs = body.as_bytes();
    let mut from = 0usize;
    while let Some(rel) = body[from..].find(n) {
        let i = from + rel;
        let j = i + n.len();
        let before = if i == 0 { None } else { Some(bs[i - 1]) };
        let after = bs.get(j).copied();
        let boundary = |c: Option<u8>| match c {
            None => true,
            Some(b) => !(b.is_ascii_alphanumeric() || b == b'-' || b == b'_'),
        };
        if boundary(before) && boundary(after) {
            return true;
        }
        // Advance to the next CHARACTER boundary, not the next byte.
        from = i + 1;
        while from < body.len() && !body.is_char_boundary(from) {
            from += 1;
        }
    }
    false
}

/// The names of OTHER definitions appearing in the prose that would go with
/// this one. Cheap and deliberately over-eager: a pointer at the diff, not a
/// verdict.
fn prose_mentions(
    file: &Path,
    name: &str,
    all: &std::collections::BTreeSet<&str>,
) -> Vec<String> {
    let Ok(src) = std::fs::read_to_string(file) else { return Vec::new() };
    let mut prose: Vec<&str> = Vec::new();
    let mut seen = false;
    for line in src.lines() {
        if line.starts_with("  ") && line.trim_start().starts_with(name) {
            seen = true;
            break;
        }
        if line.starts_with("  ") && !line.trim().is_empty() {
            prose.clear(); // code ends the run of prose above
        } else {
            prose.push(line);
        }
    }
    if !seen {
        return Vec::new();
    }
    let text = prose.join("\n");
    let mut out: Vec<String> = Vec::new();
    for n in all {
        if *n != name && n.len() > 3 && names_it(&text, n) {
            out.push((*n).to_string());
        }
    }
    out.truncate(6);
    out
}

fn collect_other(p: &Path, out: &mut Vec<(PathBuf, String)>, exts: Option<&[&str]>) {
    if p.is_dir() {
        let Ok(rd) = std::fs::read_dir(p) else { return };
        for e in rd.flatten() {
            collect_other(&e.path(), out, exts);
        }
        return;
    }
    let Some(ext) = p.extension().and_then(|e| e.to_str()) else { return };
    if ext == "codex" {
        return;
    }
    if exts.is_some_and(|list| !list.contains(&ext)) {
        return;
    }
    if let Ok(body) = std::fs::read_to_string(p) {
        out.push((p.to_path_buf(), body));
    }
}

/// What a BUNDLE reads and does not define -- the missing cites, before a guest.
///
/// A bundled subject is one file holding every chapter, so the parser reads it
/// as a single chapter whose `reads` set is exactly "named, not supplied here".
/// That is the whole computation; the rest is filtering builtins out of it and
/// saying WHICH file in the tree would answer each name, because "add
/// IR/Passes.codex" is the actionable form of "run-ir-pipeline is missing".
///
/// **It answers names, not types.** A bundle this calls complete can still fail
/// to compile on a shape. It shrinks the guest loop; it does not replace it.
/// Measured 2026-09-03: bundling the driver into a rung subject took three
/// guest compiles -- about nine minutes -- to discover a list this prints in
/// under a second.
fn bundle(subject: &str, ix: &Index, tree: &[String]) -> ExitCode {
    use std::collections::{BTreeMap, BTreeSet};

    let Ok(src) = std::fs::read(subject) else {
        eprintln!("cannot read {subject}");
        return ExitCode::from(2);
    };
    let parsed = parser::parse(&src);
    let mut dg = Desugar::new(&src);
    let ch = dg.chapter(&parsed.tree);
    let refs = xref::chapter_refs(&ch, subject);

    // A builtin is supplied by the language, not by a chapter, so a bundle never
    // carries one. THE LIST COMES FROM THE TREE rather than from our own table:
    // `Types/Builtins.codex` spells each one as `bs-name = "..."`, and our
    // compiled-in copy is already behind it -- U55's `hosted-kind` is in the
    // checkout and not in `builtins.rs`, which would have read as a missing
    // cite forever. The compiled-in table stays as the floor for a tree that
    // has no such chapter.
    let mut builtin_owned: BTreeSet<String> =
        codexc::builtins::BUILTINS.iter().map(|(n, _)| n.to_string()).collect();
    let mut from_tree = 0usize;
    for d in tree {
        let mut fs: Vec<PathBuf> = Vec::new();
        collect(Path::new(d), &mut fs);
        for f in fs {
            if !f.ends_with("Types/Builtins.codex") {
                continue;
            }
            let Ok(body) = std::fs::read_to_string(&f) else { continue };
            for seg in body.split("bs-name = \"").skip(1) {
                if let Some(n) = seg.split('"').next() {
                    if builtin_owned.insert(n.to_string()) {
                        from_tree += 1;
                    }
                }
            }
        }
    }
    let builtins: BTreeSet<&str> = builtin_owned.iter().map(String::as_str).collect();
    // Primitive type names are spelled by the type language and defined by no
    // chapter. THE LIST ONLY APPLIES TO NAMES THE TREE DOES NOT DEFINE, which
    // is the fix for a false clean: `Maybe`, `Just` and `None` were on it and
    // are `foreword/core/Maybe.codex`, so a bundle using `Just` without
    // carrying that chapter was reported complete and then failed in a guest.
    // A name the tree DOES define is never a primitive, whatever it is called.
    const PRIMS: &[&str] = &[
        "Integer", "Real", "Text", "Boolean", "Char", "Nothing", "List", "Vector",
        "LinkedList", "Type", "Effect", "Prop", "Refl",
    ];

    // A BUILTIN IS ALWAYS FILTERED, even where a chapter also defines the name.
    // `text-split`, `text-length` and `text-to-integer` are builtins AND are
    // defined by chapters somewhere in the tree; requiring those chapters made
    // three subjects that compile clean report as incomplete.
    let defined_somewhere = |n: &str| ix.defined_in.get(n).is_some_and(|d| !d.is_empty());
    let mut missing: Vec<&str> = refs
        .reads
        .iter()
        .map(String::as_str)
        .filter(|n| !builtins.contains(n))
        .filter(|n| !refs.effect_reads.contains(*n))
        .filter(|n| defined_somewhere(n) || !PRIMS.contains(n))
        .collect();
    missing.sort();

    if missing.is_empty() {
        println!("{}: {} definitions, nothing read that it does not define \
({} builtins known, {} learned from the tree)",
                 short(Path::new(subject)), refs.defines.len(), builtins.len(), from_tree);
        return ExitCode::SUCCESS;
    }

    // Group by the file that would answer, so the report is a list of chapters
    // to add rather than a list of names to look up one at a time.
    let mut by_file: BTreeMap<String, Vec<&str>> = BTreeMap::new();
    let mut nowhere: Vec<&str> = Vec::new();
    for n in &missing {
        match ix.defined_in.get(*n) {
            Some(ds) if !ds.is_empty() => {
                let paths: Vec<&str> =
                    ds.iter().map(|&i| ix.chapters[i].path.as_str()).collect();
                by_file.entry(paths.join(" | ")).or_default().push(n);
            }
            _ => nowhere.push(n),
        }
    }

    println!("{}: {} definitions, {} names read and not defined",
             short(Path::new(subject)), refs.defines.len(), missing.len());
    println!("({} builtins known, {} of them learned from the tree)\n",
             builtins.len(), from_tree);
    for (file, names) in &by_file {
        println!("  ADD {file}");
        for line in wrap(names, 68) {
            println!("        {line}");
        }
    }
    if !nowhere.is_empty() {
        println!("\n  DEFINED NOWHERE in the tree searched ({}):", nowhere.len());
        for line in wrap(&nowhere, 68) {
            println!("        {line}");
        }
        println!("  (a builtin this tool does not know, or a genuine dangling name)");
    }
    ExitCode::from(1)
}


/// OUR calls against THEIR signatures.
///
/// The subject is our side -- a harness file, or a directory of them -- and the
/// remaining paths are the compiler checkout that owns the definitions. Both
/// are parsed; nothing is compiled and no guest runs, so this is seconds
/// against an Update rather than the hour a rung takes to die.
fn arity_mode(ours: &str, tree: &[String], partial: bool, phases_only: bool) -> ExitCode {
    let load = |p: &Path| -> Vec<(String, codexc::ast::Chapter)> {
        let mut fs: Vec<PathBuf> = Vec::new();
        collect(p, &mut fs);
        fs.sort();
        let mut out = Vec::new();
        for f in fs {
            let Ok(src) = std::fs::read(&f) else { continue };
            let parsed = parser::parse(&src);
            let mut dg = Desugar::new(&src);
            let ch = dg.chapter(&parsed.tree);
            if ch.name.is_empty() {
                continue;
            }
            out.push((short(&f), ch));
        }
        out
    };

    let mut theirs: Vec<(String, codexc::ast::Chapter)> = Vec::new();
    for d in tree {
        theirs.extend(load(Path::new(d)));
    }
    if theirs.is_empty() {
        eprintln!("no chapters under {}", tree.join(" "));
        return ExitCode::from(2);
    }
    let ix = codexc::arity::index(&theirs);

    // A BUNDLED SUBJECT IS NOT OUR SOURCE. `ast/<m>-subject.codex` is generated
    // by concatenating the compiler's own chapters with a harness, so it
    // DEFINES everything it calls -- and the "a name we define is ours" filter
    // below then drops every call in the directory. Pointed at `ast/` that read
    // "0 call(s) graded in 46 of our chapter(s)" and called it ok, which is the
    // exact shape of green this tool exists to refuse.
    let mine: Vec<(String, codexc::ast::Chapter)> = load(Path::new(ours))
        .into_iter()
        .filter(|(p, _)| !p.ends_with("-subject.codex"))
        .collect();
    if mine.is_empty() {
        eprintln!("no chapters at {ours} (bundled *-subject.codex files are skipped: \
                   they are generated, and they define what they call)");
        return ExitCode::from(2);
    }

    // A name OUR side defines is ours, whatever the tree also calls it. Grading
    // our own definitions against the compiler's arity is how a name collision
    // becomes a false alarm.
    let ours_defines: std::collections::BTreeSet<String> =
        mine.iter().flat_map(|(_, c)| c.defs.iter().map(|d| d.name.clone())).collect();

    let (mut short_all, mut over_all, mut skipped) = (Vec::new(), Vec::new(), 0usize);
    let mut per_file: Vec<(String, usize)> = Vec::new();
    for (path, ch) in &mine {
        let cs: Vec<codexc::arity::Call> = codexc::arity::calls(ch)
            .into_iter()
            .filter(|c| !ours_defines.contains(&c.name))
            .filter(|c| !phases_only || codexc::arity::is_driver_phase(&c.name))
            .collect();
        per_file.push((path.clone(), cs.len()));
        let (s, o, k) = codexc::arity::compare(&cs, &ix, partial);
        skipped += k;
        for d in s {
            short_all.push((path.clone(), d));
        }
        for d in o {
            over_all.push((path.clone(), d));
        }
    }

    let graded: usize = per_file.iter().map(|(_, n)| n).sum();
    println!(
        "{} definition(s) indexed from the checkout; {} call(s) graded in {} of our chapter(s)",
        ix.len(),
        graded,
        mine.len()
    );

    // A definition with no parameter list has no arity to check. Saying how
    // many were skipped keeps the clean sheet honest: a run that graded nothing
    // and a run that graded everything both print no findings.
    if skipped > 0 {
        println!("  ({skipped} call(s) skipped: the definition is point-free, so its arity is in its TYPE)");
    }

    let sort = |v: &mut Vec<(String, codexc::arity::Drift)>| {
        v.sort_by(|a, b| {
            codexc::arity::is_driver_phase(&b.1.call.name)
                .cmp(&codexc::arity::is_driver_phase(&a.1.call.name))
                .then(a.1.call.name.cmp(&b.1.call.name))
                .then(a.0.cmp(&b.0))
                .then(a.1.call.line.cmp(&b.1.call.line))
        })
    };
    sort(&mut over_all);
    sort(&mut short_all);

    if !over_all.is_empty() {
        println!("\nOVER-APPLIED -- more arguments than the definition takes:");
        for (path, d) in &over_all {
            println!(
                "  {}:{}  {} applied to {}, declared {}   [{}]",
                path, d.call.line, d.call.name, d.call.applied, d.declared, d.defined_at
            );
        }
    }

    if !short_all.is_empty() {
        println!("\nUNDER-APPLIED -- fewer arguments than the definition takes:");
        println!("  In Codex this is a VALUE, not an error. Where it is not deliberate, the type");
        println!("  error lands one line later against whatever consumed it.");
        for (path, d) in &short_all {
            let star = if codexc::arity::is_driver_phase(&d.call.name) { " <-- driver phase" } else { "" };
            println!(
                "  {}:{}  {} applied to {}, declared {}   [{}]{}",
                path, d.call.line, d.call.name, d.call.applied, d.declared, d.defined_at, star
            );
        }
    }

    // GRADING NOTHING IS NOT PASSING. A filter that swallowed every call and a
    // codebase that is genuinely correct print the same clean sheet otherwise.
    if graded == 0 {
        println!(
            "\nREFUSING: 0 calls graded. Nothing here applies a name the checkout defines --\n\
             check the subject path, and note that generated *-subject.codex bundles are\n\
             skipped because they define what they call."
        );
        return ExitCode::from(2);
    }

    if over_all.is_empty() && short_all.is_empty() {
        println!("\nok  every call matches the arity the checkout declares");
        return ExitCode::SUCCESS;
    }
    println!(
        "\n{} over-applied, {} under-applied",
        over_all.len(),
        short_all.len()
    );
    ExitCode::from(1)
}
