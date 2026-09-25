//! Roc from a Codex unit.
//!
//!     rocemit <unit.codex> <dir>      one module per chapter, and the spec's
//!                                     app, written into <dir>: the
//!                                     definitions the opening can reach
//!     rocemit --by-reach <unit.codex> <dir>
//!
//! **PRUNED LIKE UPSTREAM, BY DEFAULT.** Every upstream backend emits what
//! `ir-prune-unreachable-roots` keeps: the definitions reachable from
//! `ir-emit-roots` (`opening` first). Emitting every cited chapter whole meant
//! one definition a program never calls could refuse it: U62's GopXhci timer
//! code refused `fat32-parse`, and U62's e1000/ne2k copy loops thirty-odd
//! network tests, none of which call them. A unit with no `opening` is a
//! library and has no root, so it stays whole.
//!
//! There used to be a reason to emit whole chapters: one chapter module shared
//! by several emitted apps had to read the same in each. The one caller that
//! did that (roc-apps canvas_apps/safari/emitted.sh) is retired; safari's Roc is
//! source now.
//!
//! Two lines on stdout: the app's file name, or `library` for a unit with
//! no opening, and a digest of everything written.
//!
//! `--by-reach` picks the threaded state from what the opening can reach, not
//! from every definition in the unit's chapters. It is for a platform whose
//! host stops a read or write at an address it does not back (roc-apps
//! framebuffer): a program can reach a device through a memory address no
//! builtin names, which only the host can see.
//!
//! The same road as `irdump whole` -- resolve, parse, desugar, check, lower --
//! and then `roc_emit` instead of the IR text. Exit 2 on a refusal.

use codexc::parser;
use std::io::Write;
use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let by_reach = args.iter().any(|a| a == "--by-reach");
    let whole = args.iter().any(|a| a == "--whole");
    let rest: Vec<&String> = args.iter().filter(|a| *a != "--by-reach" && *a != "--whole").collect();
    let result = match rest.as_slice() {
        [path, dir] => emit(Path::new(path), Path::new(dir), by_reach, whole),
        _ => {
            eprintln!("usage: rocemit [--by-reach] [--whole] <unit.codex> <dir>");
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

fn emit(path: &Path, dir: &Path, by_reach: bool, whole: bool) -> Result<String, String> {
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
    // The driver's inlining pipeline is the IR wire's and is not run here;
    // its PRUNE is every backend's, and is (see the top of this file).
    let mut low = codexc::ir::lower_whole(&ch, &bindings, &st, &tds)?;
    let has_opening = low.syms.find("opening").is_some_and(|o| low.defs.iter().any(|d| d.name == o));
    if has_opening && !whole {
        // **EVERY `__eq_<T>` IS A ROOT.** Upstream's lowering calls the
        // instantiated helper by name (COMPILER-44), so its prune sees the
        // reference; ours lowers `==` to a `Binary` node and roc_emit builds
        // each type's equality from the `__eq_` definitions by name, so
        // nothing here names them. Pruned, `==` on a record of such a type no
        // longer compiled in Roc ("type does not support equality").
        let eq: Vec<String> = low
            .defs
            .iter()
            .map(|d| low.syms.text(d.name).to_string())
            .filter(|n| n.starts_with("__eq_"))
            .collect();
        let roots: Vec<&str> = codexc::ir::IR_EMIT_ROOTS.iter().copied().chain(eq.iter().map(String::as_str)).collect();
        let defs = std::mem::take(&mut low.defs);
        low.defs = codexc::ir_passes::prune_unreachable_roots(defs, &roots, &low.syms);
    }
    // A test's codex-vm flags sit beside it as `.vmargs`; a unit that brings
    // them asks for the machine's devices.
    let vm_flags = path.with_extension("vmargs").exists();
    // Codex writes a list in place; make every later read of it, here and
    // in the callers, read the version the write answered
    // (docs/list-versions.md).
    let defs = std::mem::take(&mut low.defs);
    let (defs, unversioned) = codexc::list_versions::apply(defs, &mut low.syms);
    low.defs = defs;
    if !whole {
        if let Some((n, why)) = unversioned.first() {
            return Err(format!("`{}`: {why}", low.syms.text(*n)));
        }
    }
    let (files, notes) =
        codexc::roc_emit::emit_modules(&ch, &tds, &low.syms, &low.defs, vm_flags, by_reach, whole, &unversioned)?;
    for n in &notes {
        eprintln!("{n}");
    }
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
    // **THE DIGEST IS PRINTED HERE BECAUSE THE FILES ARE ALREADY IN HAND.**
    // A harness that wants to know whether this emission differs from the
    // last one would otherwise read every file back and hash it, which for
    // a thousand units is a thousand extra processes; this costs nothing.
    let mut digest: u64 = 0xcbf29ce484222325;
    for (name, text) in &files {
        for b in name.as_bytes().iter().chain(text.as_bytes()) {
            digest ^= *b as u64;
            digest = digest.wrapping_mul(0x100000001b3);
        }
    }
    let app = app.unwrap_or_else(|| "library".to_string());
    Ok(format!("{app}\n{digest:016x}\n"))
}
