//! Where a chapter could be cut, when counting components says nothing.
//!
//!     seams <Chapter> <dir>...
//!
//! Prints the chapter's real interface (what other chapters read), any
//! mutually recursive group (which cannot be cut at all), and then every
//! definition that DOMINATES a set of others -- the set reachable only through
//! it, which is exactly what peeling it off would take with it.

use codexc::cohesion;
use codexc::desugar::Desugar;
use codexc::parser;
use codexc::seams;
use codexc::xref::{self, ChapterRefs};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 2 {
        eprintln!("usage: seams <Chapter> <dir>...");
        return ExitCode::from(2);
    }
    let want = &args[0];
    let mut files: Vec<PathBuf> = Vec::new();
    for p in &args[1..] {
        collect(Path::new(p), &mut files);
    }
    files.sort();

    let mut refs: Vec<ChapterRefs> = Vec::new();
    let mut target: Option<(codexc::ast::Chapter, PathBuf, Vec<u8>)> = None;
    for f in &files {
        let Ok(src) = std::fs::read(f) else { continue };
        let parsed = parser::parse(&src);
        let mut dg = Desugar::new(&src);
        let ch = dg.chapter(&parsed.tree);
        if ch.syms.text(ch.name).is_empty() {
            continue;
        }
        refs.push(xref::chapter_refs(&ch, &f.to_string_lossy()));
        if ch.syms.text(ch.name) == want {
            target = Some((ch, f.clone(), src));
        }
    }
    let Some((ch, path, src)) = target else {
        eprintln!("no chapter named {want} under those paths");
        return ExitCode::from(2);
    };
    let ix = xref::build(refs);

    // The interface: a definition some OTHER chapter reads.
    let outside: std::collections::BTreeSet<&str> = ix
        .chapters
        .iter()
        .filter(|c| c.chapter != ch.syms.text(ch.name))
        .flat_map(|c| c.reads.iter().map(String::as_str))
        .collect();

    let parsed = parser::parse(&src);
    let c = cohesion::analyse(&ch, &parsed.tree, &src);
    let roots: Vec<usize> = (0..c.def_names.len())
        .filter(|&i| outside.contains(c.def_names[i].as_str()))
        .collect();

    let s = seams::analyse(c.def_names.len(), &c.edges, &roots);

    println!("{} ({})", ch.syms.text(ch.name), path.display());
    println!("  {} definitions, {} internal calls", c.def_names.len(), c.edges.len());
    println!("\n  INTERFACE — read by another chapter ({}):", roots.len());
    for line in wrap(&roots.iter().map(|&i| c.def_names[i].as_str()).collect::<Vec<_>>(), 68) {
        println!("      {line}");
    }

    if s.cycles.is_empty() {
        println!("\n  No mutual recursion: every group below can be cut.");
    } else {
        println!("\n  MUTUALLY RECURSIVE — inseparable ({} groups):", s.cycles.len());
        for g in &s.cycles {
            let names: Vec<&str> = g.iter().map(|&i| c.def_names[i].as_str()).collect();
            println!("      [{}] {}", g.len(), names.join(" "));
        }
    }

    println!("\n  SEAMS — <name> owns N definitions reachable only through it:");
    let mut shown = 0;
    for seam in &s.seams {
        if seam.owns.len() < 2 {
            continue;
        }
        shown += 1;
        let secs = section_span(&c, &seam.owns);
        println!(
            "\n    {} owns {} — {}",
            c.def_names[seam.head], seam.owns.len(), secs
        );
        let names: Vec<&str> = seam.owns.iter().map(|&i| c.def_names[i].as_str()).collect();
        for line in wrap(&names, 66) {
            println!("          {line}");
        }
    }
    if shown == 0 {
        println!("    none — every definition is reachable from two or more entries.");
    }
    ExitCode::SUCCESS
}

fn section_span(c: &cohesion::Cohesion, defs: &[usize]) -> String {
    let mut secs: Vec<&str> = Vec::new();
    for &i in defs {
        let s = c.def_section[i].as_str();
        if !s.is_empty() && !secs.contains(&s) {
            secs.push(s);
        }
    }
    if secs.is_empty() { "(no section)".into() } else { secs.join(" + ") }
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
