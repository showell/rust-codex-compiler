//! Who reads this name, and which chapter defines it.
//!
//!     xref who <name> <dir>...      every chapter reading it, and its definer
//!     xref chapter <Name> <dir>...  what one chapter reads, grouped by definer
//!     xref dangling <dir>...        names read that nothing in the tree defines
//!     xref dead <dir>...            definitions nothing in the tree reads
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
        _ => {
            eprintln!("usage: xref who <name> <dir>...");
            eprintln!("       xref chapter <Name> <dir>...");
            eprintln!("       xref dangling <dir>...");
            eprintln!("       xref dead <dir>...  [--roots a,b,c] [--in <path substring>] [--all-files]");
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
    let Some(me) = ix.chapters.iter().position(|c| c.chapter == name) else {
        eprintln!("no chapter named {name}");
        return;
    };
    let c = &ix.chapters[me];
    println!("{} ({}) defines {}, reads {}", c.chapter, c.path, c.defines.len(), c.reads.len());
    let mut by_definer: std::collections::BTreeMap<String, Vec<&str>> = Default::default();
    let mut unknown: Vec<&str> = Vec::new();
    for n in &c.reads {
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
        from = i + 1;
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
