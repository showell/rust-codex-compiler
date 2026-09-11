//! Roc from a Codex unit.
//!
//!     rocemit <unit.codex> <dir>      one type module per chapter, whole, and
//!                                     the spec's app, written into <dir>; the
//!                                     app's file name on stdout
//!
//! The same road as `irdump whole` -- resolve, parse, desugar, check, lower --
//! and then `roc_emit` instead of the IR text. Exit 2 on a refusal.

use codexc::parser;
use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.as_slice() {
        [path, dir] => emit(Path::new(path), Path::new(dir)),
        _ => {
            eprintln!("usage: rocemit <unit.codex> <dir>");
            return ExitCode::from(2);
        }
    };
    match result {
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

fn emit(path: &Path, dir: &Path) -> Result<String, String> {
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
    // **A MODULE IS THE WHOLE CHAPTER, AS WRITTEN.** The driver's prune and
    // its inlining pipeline are the IR wire's rules; a chapter module that
    // fifty apps import wants every definition and one text.
    let low = codexc::ir::lower_whole(&ch, &bindings, &st, &tds)?;
    let files = codexc::roc_emit::emit_modules(&ch, &tds, &low.syms, &low.defs)?;
    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    // The directory holds ONLY this unit's modules: a file from an earlier
    // emission of a chapter that has since gone would still be imported.
    for entry in std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?.flatten() {
        if entry.path().extension().is_some_and(|x| x == "roc") {
            let _ = std::fs::remove_file(entry.path());
        }
    }
    let mut app = None;
    for (name, text) in &files {
        std::fs::write(dir.join(name), text).map_err(|e| format!("{name}: {e}"))?;
        if text.contains("\nmain! = ") {
            app = Some(name.clone());
        }
    }
    let app = app.ok_or("no app among the emitted modules")?;
    Ok(format!("{app}\n"))
}
