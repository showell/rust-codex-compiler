//! The CHECK rung's section, for diffing against the gold.
//!
//!     checkdump check <file.codex>    print the `--- check ---` section
//!
//! Deliberately prints even when the counts are wrong. The three unification
//! numbers cannot be right until inference exists, and a tool that refused
//! until then would give no signal while it was being built; a diff that says
//! "substitutions 0 against 8" says exactly how far there is to go.
use codexc::{check, desugar::Desugar, parser};
use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("lower") if args.len() == 2 => {
            let Ok(src) = std::fs::read(Path::new(&args[1])) else {
                eprintln!("cannot read {}", args[1]);
                return ExitCode::from(2);
            };
            let parsed = parser::parse(&src);
            let mut dg = Desugar::new(&src);
            let ch = dg.chapter(&parsed.tree);
            let out = std::io::stdout();
            let _ = write!(
                out.lock(),
                "{}",
                codexc::ir::lower_section(&ch, &codexc::ir::IR_EMIT_ROOTS)
            );
            ExitCode::SUCCESS
        }
        Some("check") if args.len() == 2 => {
            let Ok(src) = std::fs::read(Path::new(&args[1])) else {
                eprintln!("cannot read {}", args[1]);
                return ExitCode::from(2);
            };
            let parsed = parser::parse(&src);
            let mut dg = Desugar::new(&src);
            let ch = dg.chapter(&parsed.tree);
            let (bindings, st) = check::check_chapter(&ch);
            let out = std::io::stdout();
            let _ = write!(out.lock(), "{}", check::section(&ch.syms, &bindings, &st));
            ExitCode::SUCCESS
        }
        _ => {
            eprintln!("usage: checkdump check <file.codex>");
            eprintln!("       checkdump lower <file.codex>");
            ExitCode::from(2)
        }
    }
}
