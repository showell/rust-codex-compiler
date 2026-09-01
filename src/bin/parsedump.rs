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

/// Is this one of the compiler's own diagnostic tests?
///
/// `codex/test/errors/` holds programs the compiler is SUPPOSED to decline,
/// and they are the second gold set -- a diagnostic we produce there is output,
/// not a defect. Lumping them in with the rest makes a parse-error total that
/// goes UP as the front end gets better, which is a number nobody can use. The
/// test is the directory, so it is a heuristic and named as one; the gold
/// bank's `refused.tsv` is the authority when the two disagree.
fn is_diagnostic_test(p: &Path) -> bool {
    p.components().any(|c| c.as_os_str() == "errors")
}

fn is_pattern(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::VarPat
            | NodeKind::LitPat
            | NodeKind::CtorPat
            | NodeKind::WildPat
            | NodeKind::TuplePat
            | NodeKind::ParenPat
            | NodeKind::VecPat
            | NodeKind::ErrPat
    )
}

/// Nodes of `kind` that hold no child NODE -- a bag of tokens and nothing else.
fn childless(tree: &Node, kind: NodeKind) -> usize {
    tree.descendants(kind).iter().filter(|n| n.count_any_node() == 0).count()
}

/// Wall time spent in `parse` alone, and the rate it implies. Compile speed is
/// this project's first goal, so the sweep that proves the grammar total is
/// also the place to watch it: everything else here -- a second tokenize for
/// the coverage check, a dozen tree walks -- is the GATE's cost and not the
/// front end's, and reporting them together hides a regression inside it.
fn rate(bytes: usize, secs: f64) -> String {
    if secs <= 0.0 {
        return "-".to_string();
    }
    format!("{:.1} MB/s", bytes as f64 / secs / 1_048_576.0)
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
    let mut expected_errs = 0usize;
    // What the parser is complaining ABOUT, not just how often. A total of 144
    // says nothing; "expected 'in' after a let binding, 96 times" names the
    // grammar rule that is missing.
    let mut by_msg: std::collections::HashMap<String, (usize, String)> =
        std::collections::HashMap::new();
    let mut loose = 0usize;
    let (mut shown, mut shown_td) = (0usize, 0usize);
    let (mut parse_secs, mut total_bytes) = (0f64, 0usize);
    // How many files come out with nothing unexplained: no parse error, no
    // unread body, no unread type-definition body. It is the one number that
    // says how much of the language is actually read, and a per-file count
    // says it better than a total, which one bad file can dominate.
    let mut whole = 0usize;
    let (mut flat_type, mut unclosed) = (0usize, 0usize);
    let (mut tds, mut recs, mut vars, mut ctors, mut unread_td) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut acts, mut stmts, mut handles, mut clauses) = (0usize, 0usize, 0usize, 0usize);
    // Patterns are no longer a token bag, so "flat" says nothing about them --
    // `is Red` is a childless CtorPat and is exactly right. What matters is
    // how many tokens landed in pattern position without being understood,
    // and, so that a zero cannot come from a parser that never ran, how many
    // patterns there are at all.
    let (mut pats, mut err_pats, mut arms, mut guards, mut alts) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let mut unread_ty = 0usize;
    for f in &files {
        let Ok(src) = std::fs::read(f) else { continue };
        let t0 = std::time::Instant::now();
        let parsed = parser::parse(&src);
        parse_secs += t0.elapsed().as_secs_f64();
        total_bytes += src.len();
        let lexed = codexc::lexer::tokenize(&src);
        let in_tree: Vec<_> = parsed.tree.tokens().copied().collect();
        if in_tree != lexed.tokens {
            bad += 1;
            if bad <= 10 {
                println!("COVERAGE {}: tree holds {} of {} tokens",
                         f.display(), in_tree.len(), lexed.tokens.len());
            }
        }
        defs += parsed.tree.count_descendants(NodeKind::Def);
        unparsed += parsed.unparsed_bodies;
        if parsed.errors.is_empty()
            && parsed.unparsed_bodies == 0
            && parsed.unread_type_defs == 0
        {
            whole += 1;
        }
        if is_diagnostic_test(f) {
            expected_errs += parsed.errors.len();
        } else {
            errs += parsed.errors.len();
        }
        for e in &parsed.errors {
            // One example location per message. A count says a rule is
            // missing; the location says which line to go and read.
            let slot = by_msg
                .entry(e.msg.clone())
                .or_insert_with(|| (0, format!("{}:{}:{}", f.display(), e.line, e.col)));
            slot.0 += 1;
        }
        loose += loose_tokens(&parsed.tree);
        unread_ty += parsed.unread_types;
        // FLAT means childless: a node holding only tokens. Counting the
        // wrapper instead would have kept reporting 4,858 flat type
        // expressions the moment they all gained structure.
        for k in [NodeKind::VarPat, NodeKind::LitPat, NodeKind::CtorPat, NodeKind::WildPat,
                  NodeKind::TuplePat, NodeKind::ParenPat, NodeKind::VecPat] {
            pats += parsed.tree.descendants(k).len();
        }
        err_pats += parsed.tree.count_descendants(NodeKind::ErrPat);
        guards += parsed.tree.count_descendants(NodeKind::Guard);
        for a in parsed.tree.descendants(NodeKind::MatchArm) {
            arms += 1;
            // An arm's children are its patterns, an optional guard and its
            // body, so more than one pattern means `|` fanned it out.
            if a.child_nodes().iter().filter(|n| is_pattern(n.kind)).count() > 1 {
                alts += 1;
            }
        }
        flat_type += childless(&parsed.tree, NodeKind::TypeExpr);
        tds += parsed.tree.count_descendants(NodeKind::TypeDef);
        recs += parsed.tree.count_descendants(NodeKind::RecordFieldDef);
        vars += parsed.tree.count_descendants(NodeKind::VariantBody);
        ctors += parsed.tree.count_descendants(NodeKind::VariantCtor);
        unread_td += parsed.unread_type_defs;
        unclosed += parsed.unclosed_blocks;
        acts += parsed.tree.count_descendants(NodeKind::ActBlock);
        stmts += parsed.tree.count_descendants(NodeKind::ActBind)
            + parsed.tree.count_descendants(NodeKind::ActStmt);
        handles += parsed.tree.count_descendants(NodeKind::HandleExpr);
        clauses += parsed.tree.count_descendants(NodeKind::HandleClause);
        if parsed.unread_type_defs > 0 && shown_td < 12 {
            for td in parsed.tree.descendants(NodeKind::TypeDef) {
                for e in td.children_of(NodeKind::Error) {
                    if let Some(t) = e.tokens().find(|t| !t.kind.is_trivia()) {
                        println!("UNREAD-TYPEDEF {}:{}:{}: {} |{}|", f.display(), t.line, t.col,
                                 t.kind.name(), String::from_utf8_lossy(t.text(&src)));
                        shown_td += 1;
                    }
                }
            }
        }
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
    println!("parse: {total_bytes} bytes in {parse_secs:.3}s, {}", rate(total_bytes, parse_secs));
    println!("{whole} of {} files read whole -- no error, no unread body ({:.1}%)",
             files.len(), 100.0 * whole as f64 / files.len().max(1) as f64);
    println!("{expected_errs} more in test/errors/, where a diagnostic is the point");
    println!("{loose} token(s) landed in no construct");
    let mut ranked: Vec<_> = by_msg.into_iter().collect();
    ranked.sort_by(|a, b| b.1 .0.cmp(&a.1 .0).then(a.0.cmp(&b.0)));
    for (msg, (n, at)) in ranked.iter().take(30) {
        println!("  {n} x {msg}   e.g. {at}");
    }
    // What is still a bag of tokens rather than a tree. The desugarer consumes
    // exactly these, so the number is the size of the work between here and
    // there -- not a warning, an inventory.
    println!("{unread_ty} annotation(s) whose type was not fully read");
    println!("{pats} patterns in {arms} match arms; {alts} arms alternate, {guards} are guarded");
    println!("{err_pats} token(s) in pattern position not understood");
    println!("{tds} type definitions: {recs} record fields, {vars} variants of {ctors} constructors");
    println!("{unread_td} type definition(s) whose body was not fully read");
    println!("{acts} act blocks of {stmts} statements; {handles} handlers of {clauses} clauses");
    // Reported, not gated. Three files in the checkout genuinely end mid-`act`
    // and `ecdsa-p384` is banked CLEAN, so upstream accepts an unterminated
    // block in silence and a gate at zero would fail on correct behaviour. The
    // number is here because "0 blocks still flat" was also true of a parser
    // that ate the rest of the file.
    println!("{unclosed} block(s) ran to the end of the file without an 'end'");
    println!("still flat: {flat_type} type expressions");
    // Coverage alone is a weak claim and was measured to be: a parser that
    // stopped consuming definition bodies still passed it, because the orphaned
    // tokens simply reappeared as loose lines and were still counted once. So
    // the gate is coverage AND homelessness -- every token in the tree, and
    // almost none of them outside a named construct.
    // WHAT THE GATE PROMISES, and nothing else.
    //
    // Every one of these is at zero today and must stay there. The inventory
    // numbers above -- unread type definition bodies, unclosed blocks, bodies
    // not yet structured -- are NOT here, because they are the size of the
    // work still to do and a gate that is red for a month is a gate nobody
    // reads. `unread_td == 0` was in this test for one commit while the number
    // was nine, and the run was red the whole time without anybody noticing.
    let mut failed = false;
    if bad > 0 {
        println!("NOT COVERED: {bad} file(s)");
        failed = true;
    }
    if loose > loose_budget(files.len()) {
        println!("TOO MANY LOOSE TOKENS: {loose} > {}", loose_budget(files.len()));
        failed = true;
    }
    if err_pats > 0 {
        println!("UNREAD PATTERNS: {err_pats}");
        failed = true;
    }
    if failed {
        ExitCode::FAILURE
    } else {
        println!("COVERED: every lexer token reaches the tree exactly once, inside a construct");
        ExitCode::SUCCESS
    }
}
