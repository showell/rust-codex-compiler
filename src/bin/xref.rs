//! Who reads this name, and which chapter defines it.
//!
//!     xref who <name> <dir>...      every chapter reading it, and its definer
//!     xref chapter <Name> <dir>...  what one chapter reads, grouped by definer
//!     xref dangling <dir>...        names read that nothing in the tree defines
//!
//! The grep replacement. See `xref.rs` for why grep cannot do this in a
//! literate language whose names carry hyphens.

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
        _ => {
            eprintln!("usage: xref who <name> <dir>...");
            eprintln!("       xref chapter <Name> <dir>...");
            eprintln!("       xref dangling <dir>...");
            return ExitCode::from(2);
        }
    };

    let mut files: Vec<PathBuf> = Vec::new();
    for p in paths {
        collect(Path::new(p), &mut files);
    }
    files.sort();
    let mut chapters: Vec<ChapterRefs> = Vec::new();
    for f in &files {
        let Ok(src) = std::fs::read(f) else { continue };
        let parsed = parser::parse(&src);
        let mut dg = Desugar::new(&src);
        let ch = dg.chapter(&parsed.tree);
        if ch.name.is_empty() {
            continue;
        }
        chapters.push(xref::chapter_refs(&ch, &short(f)));
    }
    let ix = xref::build(chapters);

    match mode {
        "who" => who(&ix, arg.unwrap()),
        "chapter" => chapter(&ix, arg.unwrap()),
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
