//! The two lexer gates, and nothing else.
//!
//!     lexdump truth <file.codex>       the ladder's lex.truth format, on stdout
//!     lexdump lossless <path>...       every byte accounted for, no gold needed
//!
//! `truth` is diffed against `ast/lex.truth` from a ladder rebank. `lossless`
//! needs no oracle at all: the source is its own answer, so it runs over the
//! whole Cobblestone checkout today.

use codexc::lexer;
use codexc::token::Kind;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("truth") if args.len() == 2 => truth(Path::new(&args[1])),
        Some("lossless") if args.len() >= 2 => lossless(&args[1..]),
        _ => {
            eprintln!("usage: lexdump truth <file.codex>");
            eprintln!("       lexdump lossless <path>...");
            ExitCode::from(2)
        }
    }
}

fn truth(path: &Path) -> ExitCode {
    let src = match std::fs::read(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{}: {e}", path.display());
            return ExitCode::from(2);
        }
    };
    let lexed = lexer::tokenize(&src);
    let out = std::io::stdout();
    let mut w = BufWriter::new(out.lock());

    let toks: Vec<_> = lexed.codex_tokens().collect();
    let _ = writeln!(w, "tokens {}", toks.len());
    for t in &toks {
        let _ = write!(w, "{} {}+{} L{}C{}", t.kind.name(), t.offset, t.len, t.line, t.col);
        // The harness prints no text for these four, and Indent/Dedent are
        // never constructed, so in practice it is Newline and EndOfFile.
        let silent = matches!(t.kind, Kind::Newline | Kind::Indent | Kind::Dedent | Kind::EndOfFile);
        if silent {
            let _ = writeln!(w);
        } else {
            let _ = w.write_all(b" |");
            let _ = w.write_all(t.text(&src));
            let _ = writeln!(w, "|");
        }
    }
    let _ = writeln!(w, "---");
    let _ = writeln!(w, "errors {}", lexed.errors.len());
    ExitCode::SUCCESS
}

fn collect_codex(root: &Path, out: &mut Vec<PathBuf>) {
    if root.is_file() {
        out.push(root.to_path_buf());
        return;
    }
    let Ok(entries) = std::fs::read_dir(root) else { return };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            if p.file_name().is_some_and(|n| n == ".git") {
                continue;
            }
            collect_codex(&p, out);
        } else if p.extension().is_some_and(|x| x == "codex") {
            out.push(p);
        }
    }
}

fn lossless(roots: &[String]) -> ExitCode {
    let mut files = Vec::new();
    for r in roots {
        collect_codex(Path::new(r), &mut files);
    }
    files.sort();

    let mut bytes = 0usize;
    let mut tokens = 0usize;
    let mut bad = 0usize;
    // ErrorToken is not a losslessness failure -- upstream emits it too -- but
    // a file full of them means the byte-level dispatch is wrong, so it is
    // counted and reported rather than hidden.
    let mut with_error_tokens = 0usize;

    for f in &files {
        let Ok(src) = std::fs::read(f) else { continue };
        let lexed = lexer::tokenize(&src);
        bytes += src.len();
        tokens += lexed.tokens.len();
        if let Some(at) = lexed.lossless_gap(&src) {
            bad += 1;
            if bad <= 20 {
                println!("GAP {}: first unaccounted byte at offset {at}", f.display());
            }
        }
        if lexed.tokens.iter().any(|t| t.kind == Kind::ErrorToken) {
            with_error_tokens += 1;
        }
    }

    println!("{} files, {bytes} bytes, {tokens} tokens", files.len());
    println!("{with_error_tokens} file(s) contain an ErrorToken");
    if bad == 0 {
        println!("LOSSLESS: every byte of every file lands in exactly one token");
        ExitCode::SUCCESS
    } else {
        println!("NOT LOSSLESS: {bad} file(s)");
        ExitCode::FAILURE
    }
}
