//! Roc from a Codex unit.
//!
//!     rocemit <unit.codex>        the Roc program on stdout, or REFUSED on stderr
//!
//! The same road as `irdump whole` -- resolve, parse, desugar, check, lower --
//! and then `roc_emit` instead of the IR text. Exit 2 on a refusal.

use codexc::parser;
use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [path] = args.as_slice() else {
        eprintln!("usage: rocemit <unit.codex>");
        return ExitCode::from(2);
    };
    match emit(Path::new(path)) {
        Ok(text) => {
            let out = std::io::stdout();
            let _ = out.lock().write_all(text.as_bytes());
            ExitCode::SUCCESS
        }
        Err(why) => {
            eprintln!("REFUSED: {why}");
            ExitCode::from(2)
        }
    }
}

fn emit(path: &Path) -> Result<String, String> {
    let src = codexc::bundle::load(path)?;
    let parsed = parser::parse(&src);
    if !parsed.lex_errors.is_empty() || !parsed.diagnostics.is_empty() {
        let mut st = codexc::check::UnifyState::default();
        for d in &parsed.lex_errors {
            st.error(codexc::check::lex_code(d.code), d.msg);
        }
        for (code, msg) in &parsed.diagnostics {
            st.error(*code, msg.clone());
        }
        if let Some(halt) = codexc::ir::codegen_halted(&st) {
            return Err(halt);
        }
    }
    let mut dg = codexc::desugar::Desugar::new(&src);
    let ch = dg.chapter(&parsed.tree);
    let (bindings, st, tds) = codexc::check::check_chapter_full(&ch);
    if let Some(halt) = codexc::ir::codegen_halted(&st) {
        return Err(halt);
    }
    let low = codexc::ir::lower_chapter(&ch, &bindings, &st, &tds, &codexc::ir::IR_EMIT_ROOTS)?;
    codexc::roc_emit::emit_program(&ch, &tds, &low.syms, &low.defs)
}
