//! The ladder's `desugar.truth` format.
//!
//!     desugardump truth <file.codex>
//!
//! It is CUMULATIVE: the parse-level dump, then `--- desugar ---`, then the
//! AST-level one. And it is one subject, at the declaration layer, so passing
//! it says the desugarer produced the right NUMBER of definitions with the
//! right names, parameters, positions and slugs -- and nothing at all about
//! what it did to a single expression. The expression shape has no oracle
//! before the type checker; that is not a gap in this tool.

use codexc::ast;
use codexc::cst::NodeKind;
use codexc::desugar::Desugar;
use codexc::parser;
use codexc::preamble::header_text;
use codexc::token::Kind;
use std::io::{BufWriter, Write};
use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("truth") if args.len() == 2 => truth(Path::new(&args[1])),
        Some("cover") if args.len() >= 2 => cover(&args[1..]),
        _ => {
            eprintln!("usage: desugardump truth <file.codex>");
            eprintln!("       desugardump cover <path>...");
            ExitCode::from(2)
        }
    }
}

fn truth(path: &Path) -> ExitCode {
    let Ok(src) = std::fs::read(path) else {
        eprintln!("{}: cannot read", path.display());
        return ExitCode::from(2);
    };
    let parsed = parser::parse(&src);
    let lexed = codexc::lexer::tokenize(&src);
    let tree = &parsed.tree;
    let chapter = tree
        .descendants(NodeKind::ChapterHeader)
        .last()
        .map(|n| header_text(n, &src))
        .unwrap_or_default();

    let out = std::io::stdout();
    let mut w = BufWriter::new(out.lock());
    let _ = writeln!(w, "lex-tokens {}", lexed.codex_tokens().count());
    let _ = writeln!(w, "lex-errors {}", lexed.errors.len());
    let _ = writeln!(w, "chapter |{chapter}|");

    // The parse-level half, the same rows `parse.truth` carries.
    let defs = tree.descendants(NodeKind::Def);
    let _ = writeln!(w, "defs {}", defs.len());
    for d in &defs {
        let eq = d.children_of(NodeKind::DefEquation).next();
        let tok = eq
            .and_then(|e| named(e, &src))
            .or_else(|| d.children_of(NodeKind::TypeAnnotation).next().and_then(|a| named(a, &src)));
        let Some((line, col, name)) = tok else { continue };
        let params = eq.map(|e| e.count(NodeKind::ParamGroup)).unwrap_or(0);
        let anns = d.count(NodeKind::TypeAnnotation);
        let _ = writeln!(w, "def {name} params {params} anns {anns} L{line}C{col} slug {chapter}");
    }
    let _ = writeln!(w, ".");
    let _ = writeln!(w, "parse-errors {}", parsed.errors.len());

    let mut dg = Desugar::new(&src);
    let ch = dg.chapter(tree);
    let _ = writeln!(w, "--- desugar ---");
    let _ = writeln!(w, "dr-sat 0");
    let _ = writeln!(w, "a-name |{}|", ch.name);
    let _ = writeln!(w, "a-chapter-title |{}|", ch.chapter_title);
    let _ = writeln!(w, "a-prose-len {}", ch.prose.len());
    let _ = writeln!(w, "a-defs {}", ch.defs.len());
    for d in &ch.defs {
        let _ = writeln!(
            w,
            "adef {} params {} dtype {} L{}C{} slug {}",
            d.name,
            d.params.len(),
            d.declared_type.len(),
            d.span.line,
            d.span.col,
            d.chapter_slug
        );
    }
    let _ = writeln!(w, ".");
    let _ = writeln!(w, "a-type-defs {}", ch.type_defs.len());
    let _ = writeln!(w, "a-effect-defs {}", ch.effect_defs.len());
    let _ = writeln!(w, "a-class-defs {}", ch.class_defs.len());
    let _ = writeln!(w, "a-instance-defs {}", ch.instance_defs.len());
    let _ = writeln!(w, "a-citations {}", ch.citations.len());
    let _ = writeln!(w, "a-ground-effects {}", ch.ground_effects.len());
    let _ = writeln!(w, "a-prose-blocks {}", ch.prose_blocks.len());
    let _ = writeln!(w, "a-annotations {}", ch.annotations.len());
    let _ = writeln!(w, "a-sections {}", ch.section_titles.len());
    for s in &ch.section_titles {
        let _ = writeln!(w, "a-section {s}");
    }
    let _ = writeln!(w, ".");
    let _ = writeln!(w, "a-rt-names {}", ch.rt_names.len());
    let _ = writeln!(w, "a-conversions {}", ch.conversions.len());
    let _ = writeln!(w, "---");
    let _: &ast::Chapter = &ch;
    ExitCode::SUCCESS
}

/// Desugar every definition in every file, and count what came out.
///
/// **`desugar.truth` would pass a desugarer that answered `Error` for every
/// expression**, because it inspects the declaration layer alone. This is the
/// baseline-free half: how many AST expression nodes exist at all, and how
/// many are the error node -- which carries the NAME of the CST kind it could
/// not translate, so a gap says what it is rather than that it happened.
fn cover(roots: &[String]) -> ExitCode {
    let mut files = Vec::new();
    for r in roots {
        collect(Path::new(r), &mut files);
    }
    files.sort();
    let (mut nodes, mut errs, mut defs) = (0usize, 0usize, 0usize);
    let mut by_cause: std::collections::HashMap<String, usize> = Default::default();
    let (mut secs, mut bytes) = (0f64, 0usize);
    for f in &files {
        let Ok(src) = std::fs::read(f) else { continue };
        let parsed = parser::parse(&src);
        let t0 = std::time::Instant::now();
        let mut dg = Desugar::new(&src);
        let ch = dg.chapter(&parsed.tree);
        secs += t0.elapsed().as_secs_f64();
        bytes += src.len();
        defs += ch.defs.len();
        for d in &ch.defs {
            d.body.walk(&mut |e| {
                nodes += 1;
                if let ast::Expr::Error(why, _) = e {
                    errs += 1;
                    *by_cause.entry(why.clone()).or_default() += 1;
                }
            });
        }
    }
    println!("{} files, {defs} definitions desugared", files.len());
    println!("{nodes} AST expression nodes, {errs} of them the error node ({:.3}%)",
             100.0 * errs as f64 / nodes.max(1) as f64);
    println!("desugar: {bytes} bytes in {secs:.3}s, {:.1} MB/s",
             bytes as f64 / secs.max(1e-9) / 1_048_576.0);
    let mut ranked: Vec<_> = by_cause.into_iter().collect();
    ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    for (why, n) in ranked.iter().take(12) {
        println!("  {n} x could not translate {why}");
    }
    if errs == 0 && nodes > 0 {
        println!("DESUGARED: every expression in every definition became an AST node");
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn collect(root: &Path, out: &mut Vec<std::path::PathBuf>) {
    if root.is_file() {
        out.push(root.to_path_buf());
        return;
    }
    let Ok(rd) = std::fs::read_dir(root) else { return };
    for e in rd.flatten() {
        let p = e.path();
        if p.is_dir() {
            if p.file_name().is_some_and(|n| n == ".git") {
                continue;
            }
            collect(&p, out);
        } else if p.extension().is_some_and(|x| x == "codex") {
            out.push(p);
        }
    }
}

fn named(n: &codexc::cst::Node, src: &[u8]) -> Option<(u32, u32, String)> {
    n.tokens()
        .find(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
        .map(|t| (t.line, t.col, String::from_utf8_lossy(t.text(src)).into_owned()))
}
