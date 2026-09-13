//! Resolve a Codex file's cites into a self-contained unit, without asking
//! another toolchain where anything is.
//!
//!     bundle one <root.codex> [out.codex]   one unit, or stdout
//!
//! The checkout is the one the program names: the tree it lives in, or the
//! `checkout` line of the `quires.tsv` above it (see `bundle::project_of`).
//! Cited chapters are written as `Quire--Name`; the program's own chapter keeps
//! its header.

use codexc::bundle;
use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("one") if args.len() == 2 || args.len() == 3 => one(&args[1], args.get(2)),
        _ => {
            eprintln!("usage: bundle one <root.codex> [out.codex]");
            ExitCode::from(2)
        }
    }
}

fn one(root: &str, out: Option<&String>) -> ExitCode {
    let b = match bundle::resolve(Path::new(root)) {
        Ok(b) => b,
        Err(why) => {
            eprintln!("REFUSED: {why}");
            return ExitCode::from(2);
        }
    };
    for c in &b.complaints {
        eprintln!("{c}");
    }
    // **A UNIT WITH A CARRIAGE RETURN IN IT CANNOT BE COMPILED, so it is not
    // written.** The bytes are kept as they were read -- this bundler does not
    // quietly rewrite its input -- which leaves refusing as the only honest
    // answer: `codexir` halts with CDX1000 on an unmapped byte inside a type,
    // and a `Chapter:` line ending in CRLF carries the return into the chapter
    // NAME, so a cite for `FFT` cannot match the `FFT\r` that is present.
    if b.text.contains('\r') {
        eprintln!("REFUSED: the unit carries a carriage return and cannot be compiled; \
                   normalise the source before bundling");
        return ExitCode::from(2);
    }
    match out {
        Some(p) => {
            if let Err(e) = std::fs::write(p, &b.text) {
                eprintln!("REFUSED: cannot write {p}: {e}");
                return ExitCode::from(2);
            }
        }
        None => {
            let stdout = std::io::stdout();
            let _ = stdout.lock().write_all(b.text.as_bytes());
        }
    }
    // An unresolved cite is a broken unit however cheerfully it was written.
    if b.complaints.iter().any(|c| c.is_broken()) {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}
