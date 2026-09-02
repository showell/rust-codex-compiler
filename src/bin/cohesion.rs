//! Is a chapter doing one job or two?
//!
//!     cohesion <file.codex|dir>...      one line per chapter, then the splits
//!     cohesion --graph <file.codex>     the chapter's own call edges
//!
//! The summary line is the whole point of the default mode: a chapter with one
//! component is finished business, and the reader should be able to skip it in
//! one glance. Everything after `SPLIT` is a chapter whose definitions fall
//! into groups that never call each other.
//!
//! It reports and does not decide. There is no size cutoff and no ranking by
//! interestingness -- see `cohesion.rs` for why.

use codexc::cohesion::{self, Cohesion};
use codexc::desugar::Desugar;
use codexc::parser;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let graph = args.first().map(String::as_str) == Some("--graph");
    let paths = if graph { &args[1..] } else { &args[..] };
    if paths.is_empty() {
        eprintln!("usage: cohesion <file.codex|dir>...");
        eprintln!("       cohesion --graph <file.codex>");
        return ExitCode::from(2);
    }

    let mut files: Vec<PathBuf> = Vec::new();
    for p in paths {
        collect(Path::new(p), &mut files);
    }
    files.sort();
    if files.is_empty() {
        eprintln!("no .codex files under {}", paths.join(" "));
        return ExitCode::from(2);
    }

    let out = std::io::stdout();
    let mut w = BufWriter::new(out.lock());
    let mut split = 0usize;
    let mut reports: Vec<(PathBuf, Cohesion)> = Vec::new();

    for f in &files {
        let Ok(src) = std::fs::read(f) else {
            let _ = writeln!(w, "{}: cannot read", f.display());
            continue;
        };
        let parsed = parser::parse(&src);
        let mut dg = Desugar::new(&src);
        let ch = dg.chapter(&parsed.tree);
        if ch.defs.is_empty() {
            continue;
        }
        let c = cohesion::analyse(&ch, &parsed.tree, &src);
        if graph {
            print_graph(&mut w, f, &c);
        } else {
            let n = c.components.len();
            let nfn = c.is_fn.iter().filter(|&&b| b).count();
            // A table of constants is one job however many components the
            // arithmetic finds, so it is named and not counted as a split.
            let is_split = n > 1 && !c.data_chapter;
            if is_split {
                split += 1;
            }
            let _ = writeln!(
                w,
                "{:<40} defs {:>4} ({:>3} fn)  edges {:>5}  components {:>3}{}",
                short(f),
                c.def_names.len(),
                nfn,
                c.edges.len(),
                n,
                if c.data_chapter { "  data" } else if is_split { "  SPLIT" } else { "" }
            );
            reports.push((f.clone(), c));
        }
    }

    if graph {
        return ExitCode::SUCCESS;
    }

    // The detail, after every summary line, so the summary can be read as a
    // block and the interesting chapters read afterwards.
    for (f, c) in &reports {
        if c.components.len() < 2 || c.data_chapter {
            continue;
        }
        let _ = writeln!(w, "\n=== {} — {} ({} components)", short(f), c.chapter, c.components.len());
        for (k, comp) in c.components.iter().enumerate() {
            let secs = comp
                .sections
                .iter()
                .map(|s| if s.is_empty() { "(no section)".to_string() } else { s.clone() })
                .collect::<Vec<_>>()
                .join(" + ");
            let _ = writeln!(
                w,
                "  [{}] {} defs{} — {}",
                k + 1,
                comp.defs.len(),
                if comp.data_only { " (data)" } else { "" },
                secs
            );
            let names: Vec<&str> =
                comp.defs.iter().map(|&i| c.def_names[i].as_str()).collect();
            for line in wrap(&names, 72) {
                let _ = writeln!(w, "        {line}");
            }
        }
        // A section split across components is the author's own division
        // disagreeing with the calls, and it reads differently from the
        // component view, so it is said separately rather than inferred.
        let mut seen: Vec<&str> = Vec::new();
        for s in &c.def_section {
            if !s.is_empty() && !seen.contains(&s.as_str()) {
                seen.push(s.as_str());
            }
        }
        for s in seen {
            let mut in_comps: Vec<usize> = Vec::new();
            for (k, comp) in c.components.iter().enumerate() {
                if comp.defs.iter().any(|&i| c.def_section[i] == s) {
                    in_comps.push(k + 1);
                }
            }
            if in_comps.len() > 1 {
                let list =
                    in_comps.iter().map(usize::to_string).collect::<Vec<_>>().join(", ");
                let _ = writeln!(w, "  section `{s}` spans components {list}");
            }
        }
    }

    if !reports.is_empty() {
        let _ = writeln!(
            w,
            "\n{} chapters, {} split into groups that never call each other.",
            reports.len(),
            split
        );
    }
    ExitCode::SUCCESS
}

fn print_graph<W: Write>(w: &mut W, f: &Path, c: &Cohesion) {
    let _ = writeln!(w, "# {} — {}", short(f), c.chapter);
    for (i, name) in c.def_names.iter().enumerate() {
        let s = &c.def_section[i];
        let _ = writeln!(w, "def {name}{}", if s.is_empty() { String::new() } else { format!("  [{s}]") });
    }
    for &(a, b) in &c.edges {
        let _ = writeln!(w, "call {} -> {}", c.def_names[a], c.def_names[b]);
    }
    for &i in &c.isolated {
        let _ = writeln!(w, "isolated {}", c.def_names[i]);
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
    // Two trailing components: enough to tell `port/Sky.codex` from
    // `judge/SkyCheck.codex` without a column of identical prefix.
    let parts: Vec<_> = p.components().collect();
    let keep = parts.len().saturating_sub(2);
    parts[keep..]
        .iter()
        .map(|c| c.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
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
