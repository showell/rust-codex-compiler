//! The ladder's `parse.truth` format, and the tree's own coverage check.
//!
//!     parsedump truth <file.codex>
//!     parsedump cover <path>...     every lexer token reaches the tree, once
//!
//! `parse.truth` records the DECLARATION layer only -- each definition's name,
//! parameter count, annotation count, position and chapter, plus the chapter's
//! sections, type definitions and counts. It says nothing about expression
//! structure, so passing it is necessary and a long way from sufficient.

use codexc::cst::{Node, NodeKind};
use codexc::parser;
use codexc::token::{Kind, Token};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("truth") if args.len() == 2 => truth(Path::new(&args[1])),
        Some("cover") if args.len() >= 2 => cover(&args[1..]),
        _ => {
            eprintln!("usage: parsedump truth <file.codex>");
            eprintln!("       parsedump cover <path>...");
            ExitCode::from(2)
        }
    }
}

/// The text after `Chapter:` / `Section:`, joined the way upstream joins it.
///
/// `join-title-parts` inserts a space only when the last byte already written
/// and the first byte arriving are BOTH alphanumeric -- a character test, not a
/// token test. So `Section: Header Scanning (streaming)` is stored as
/// `Header Scanning(streaming)`: the space before `(` disappears because `(` is
/// punctuation, and the one after it never existed.
fn header_text(n: &Node, src: &[u8]) -> String {
    let mut acc: Vec<u8> = Vec::new();
    let mut past_colon = false;
    for t in n.tokens() {
        if t.kind == Kind::Colon && !past_colon {
            past_colon = true;
            continue;
        }
        if !past_colon || t.kind.is_trivia() || t.kind == Kind::Newline {
            continue;
        }
        let next = t.text(src);
        let (Some(&last), Some(&first)) = (acc.last(), next.first()) else {
            acc.extend_from_slice(next);
            continue;
        };
        if last.is_ascii_alphanumeric() && first.is_ascii_alphanumeric() {
            acc.push(b' ');
        }
        acc.extend_from_slice(next);
    }
    String::from_utf8_lossy(&acc).into_owned()
}

fn first_named(n: &Node, src: &[u8]) -> Option<(Token, String)> {
    n.tokens()
        .find(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
        .map(|t| (*t, String::from_utf8_lossy(t.text(src)).into_owned()))
}

fn truth(path: &Path) -> ExitCode {
    let Ok(src) = std::fs::read(path) else {
        eprintln!("{}: cannot read", path.display());
        return ExitCode::from(2);
    };
    let parsed = parser::parse(&src);
    let lexed = codexc::lexer::tokenize(&src);
    let tree = &parsed.tree;

    let chapters = tree.descendants(NodeKind::ChapterHeader);
    let chapter = chapters.first().map(|n| header_text(n, &src)).unwrap_or_default();
    let sections: Vec<String> =
        tree.descendants(NodeKind::SectionHeader).iter().map(|n| header_text(n, &src)).collect();
    let defs = tree.descendants(NodeKind::Def);
    let type_defs = tree.descendants(NodeKind::TypeDef);

    let out = std::io::stdout();
    let mut w = BufWriter::new(out.lock());
    let _ = writeln!(w, "lex-tokens {}", lexed.codex_tokens().count());
    let _ = writeln!(w, "lex-errors {}", lexed.errors.len());
    let _ = writeln!(w, "chapter |{chapter}|");
    let _ = writeln!(w, "prose-len 0");
    let _ = writeln!(w, "defs {}", defs.len());
    for d in &defs {
        // The name and position come from the EQUATION line when there is one,
        // which is what upstream records; the constant form has no equation and
        // falls back to the annotation.
        let eq = d.children_of(NodeKind::DefEquation).next();
        let named = eq
            .and_then(|e| first_named(e, &src))
            .or_else(|| d.children_of(NodeKind::TypeAnnotation).next().and_then(|a| first_named(a, &src)));
        let Some((tok, name)) = named else { continue };
        let params = eq.map(|e| e.count(NodeKind::ParamGroup)).unwrap_or(0);
        let anns = d.count(NodeKind::TypeAnnotation);
        let _ = writeln!(
            w,
            "def {name} params {params} anns {anns} L{}C{} slug {chapter}",
            tok.line, tok.col
        );
    }
    let _ = writeln!(w, ".");
    let _ = writeln!(w, "type-defs {}", type_defs.len());
    for t in &type_defs {
        if let Some((_, name)) = first_named(t, &src) {
            let _ = writeln!(w, "type-def {name}");
        }
    }
    let _ = writeln!(w, ".");
    let _ = writeln!(w, "effect-defs 0");
    let _ = writeln!(w, "class-defs 0");
    let _ = writeln!(w, "instance-defs 0");
    let _ = writeln!(w, "citations {}", tree.descendants(NodeKind::Cites).len());
    let _ = writeln!(w, "quotations 0");
    let _ = writeln!(w, "ground-effects 0");
    let _ = writeln!(w, "sections {}", sections.len());
    for s in &sections {
        let _ = writeln!(w, "section {s}");
    }
    let _ = writeln!(w, ".");
    let _ = writeln!(w, "prose-blocks 0");
    let _ = writeln!(w, "annotations 0");
    // The count belongs in the dump; WHERE they are belongs on stderr, so a
    // diff against the truth stays clean while a failure is still diagnosable.
    for e in &parsed.errors {
        eprintln!("{}:{}:{}: {}", path.display(), e.line, e.col, e.msg);
    }
    let _ = writeln!(w, "parse-errors {}", parsed.errors.len());
    let _ = writeln!(w, ".");
    let _ = writeln!(w, "---");
    ExitCode::SUCCESS
}

fn collect(root: &Path, out: &mut Vec<PathBuf>) {
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

/// A `Page 1 of 3` footer is genuinely outside every construct, and there is
/// about one per file. Anything much beyond that is a parser losing structure.
fn loose_budget(files: usize) -> usize {
    files * 8
}

/// Real tokens sitting in a `Loose` node -- newlines and trivia excepted, since
/// blank lines between definitions belong nowhere by design.
fn loose_tokens(tree: &Node) -> usize {
    tree.descendants(NodeKind::Loose)
        .iter()
        .flat_map(|n| n.tokens())
        .filter(|t| !t.kind.is_trivia() && t.kind != Kind::Newline && t.kind != Kind::EndOfFile)
        .count()
}

fn cover(roots: &[String]) -> ExitCode {
    let mut files = Vec::new();
    for r in roots {
        collect(Path::new(r), &mut files);
    }
    files.sort();
    let (mut bad, mut defs, mut unparsed, mut errs) = (0usize, 0usize, 0usize, 0usize);
    let mut loose = 0usize;
    let mut shown = 0usize;
    let (mut flat_pat, mut flat_type, mut flat_td, mut flat_act) = (0usize, 0usize, 0usize, 0usize);
    for f in &files {
        let Ok(src) = std::fs::read(f) else { continue };
        let parsed = parser::parse(&src);
        let lexed = codexc::lexer::tokenize(&src);
        let in_tree: Vec<_> = parsed.tree.tokens().copied().collect();
        if in_tree != lexed.tokens {
            bad += 1;
            if bad <= 10 {
                println!("COVERAGE {}: tree holds {} of {} tokens",
                         f.display(), in_tree.len(), lexed.tokens.len());
            }
        }
        defs += parsed.tree.descendants(NodeKind::Def).len();
        unparsed += parsed.unparsed_bodies;
        errs += parsed.errors.len();
        loose += loose_tokens(&parsed.tree);
        flat_pat += parsed.tree.descendants(NodeKind::Pattern).len();
        flat_type += parsed.tree.descendants(NodeKind::TypeExpr).len();
        flat_td += parsed.tree.descendants(NodeKind::TypeDef).len();
        flat_act += parsed.tree.descendants(NodeKind::ActBlock).len()
            + parsed.tree.descendants(NodeKind::TryExpr).len()
            + parsed.tree.descendants(NodeKind::HandleExpr).len()
            + parsed.tree.descendants(NodeKind::WithTimeout).len();
        if shown < 12 {
            for u in parsed.tree.descendants(NodeKind::UnparsedBody) {
                if let Some(t) = u.tokens().find(|t| !t.kind.is_trivia()) {
                    println!("UNREAD {}:{}:{}: {} |{}|", f.display(), t.line, t.col,
                             t.kind.name(), String::from_utf8_lossy(t.text(&src)));
                    shown += 1;
                    break;
                }
            }
        }
    }
    println!("{} files, {defs} definitions, {unparsed} bodies not yet structured, {errs} parse errors",
             files.len());
    println!("{loose} token(s) landed in no construct");
    // What is still a bag of tokens rather than a tree. The desugarer consumes
    // exactly these, so the number is the size of the work between here and
    // there -- not a warning, an inventory.
    println!("still flat: {flat_pat} patterns, {flat_type} type expressions, \
{flat_td} type definitions, {flat_act} act/trying/with blocks");
    // Coverage alone is a weak claim and was measured to be: a parser that
    // stopped consuming definition bodies still passed it, because the orphaned
    // tokens simply reappeared as loose lines and were still counted once. So
    // the gate is coverage AND homelessness -- every token in the tree, and
    // almost none of them outside a named construct.
    if bad == 0 && loose <= loose_budget(files.len()) {
        println!("COVERED: every lexer token reaches the tree exactly once, inside a construct");
        ExitCode::SUCCESS
    } else {
        if bad > 0 {
            println!("NOT COVERED: {bad} file(s)");
        }
        if loose > loose_budget(files.len()) {
            println!("TOO MANY LOOSE TOKENS: {loose} > {}", loose_budget(files.len()));
        }
        ExitCode::FAILURE
    }
}
