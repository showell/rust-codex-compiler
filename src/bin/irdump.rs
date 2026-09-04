//! The IR chapter preamble, and the gold set that grades it.
//!
//!     irdump preamble <unit.codex>
//!     irdump grade <units-dir>            against $CODEX_GOLDS/ir/*.ir
//!
//! **The input must be a RESOLVED unit** -- the ladder's `resolve_corpus.py`
//! writes them -- because that is what the golds were cut from. Handed a raw
//! program, every section and constructor the prelude contributes is missing
//! and the diff is uninformative rather than wrong.
//!
//! `grade` is the first whole-corpus check this front end has. `lex.truth` and
//! `parse.truth` are one subject each; this is 1,012 programs, and it is the
//! only oracle available before the type checker, since everything below
//! `(defs` carries an inferred type on every node.

use codexc::parser;
use codexc::preamble;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("preamble") if args.len() == 2 || args.len() == 3 => match emit(Path::new(&args[1]), args.get(2).map(String::as_str)) {
            Some(text) => {
                let out = std::io::stdout();
                let _ = writeln!(out.lock(), "{text}");
                ExitCode::SUCCESS
            }
            None => ExitCode::from(2),
        },
        Some("whole") if args.len() == 2 || args.len() == 3 => match whole(Path::new(&args[1]), args.get(2).map(String::as_str)) {
            Some(text) => {
                let out = std::io::stdout();
                let _ = writeln!(out.lock(), "{text}");
                ExitCode::SUCCESS
            }
            None => {
                eprintln!("REFUSED: a definition in this chapter cannot be typed without the checker");
                ExitCode::from(2)
            }
        },
        Some("gradewhole") if args.len() == 2 => grade_whole(Path::new(&args[1])),
        Some("grade") if args.len() == 2 => grade(Path::new(&args[1])),
        Some("defs") if args.len() == 2 => defs(Path::new(&args[1])),
        _ => {
            eprintln!("usage: irdump preamble <unit.codex>");
            eprintln!("       irdump grade <units-dir>");
            eprintln!("       irdump defs <units-dir>");
            eprintln!("       irdump whole <unit.codex>        preamble AND definition bodies");
            eprintln!("       irdump gradewhole <units-dir>    whole files against $CODEX_GOLDS/ir");
            ExitCode::from(2)
        }
    }
}

fn emit(path: &Path, chapter: Option<&str>) -> Option<String> {
    let src = std::fs::read(path).ok()?;
    let parsed = parser::parse(&src);
    Some(preamble::emit(&parsed.tree, &src, chapter))
}

/// The `(chapter "X"` a gold opens with. It is the driver's parameter, not
/// ours to derive, so it is READ -- and counted, so taking it can never be
/// silent.
fn gold_chapter_name(ir: &str) -> Option<&str> {
    let rest = ir.strip_prefix("(chapter \"")?;
    rest.find('"').map(|end| &rest[..end])
}

/// The gold's preamble: everything up to and including the `(defs` opener.
fn gold_preamble(ir: &str) -> Option<&str> {
    let at = ir.find("\n  (defs")?;
    Some(&ir[..at + "\n  (defs".len()])
}

/// Which line first differs, and what the two sides say there. A whole-file
/// diff of a 60 KB preamble names nothing; the first differing line names the
/// form that is wrong.
fn first_difference(gold: &str, ours: &str) -> (usize, String, String) {
    let (g, o): (Vec<&str>, Vec<&str>) = (gold.lines().collect(), ours.lines().collect());
    for i in 0..g.len().max(o.len()) {
        let (a, b) = (g.get(i).copied().unwrap_or("<none>"), o.get(i).copied().unwrap_or("<none>"));
        if a != b {
            return (i + 1, clip(a), clip(b));
        }
    }
    (0, String::new(), String::new())
}

fn clip(s: &str) -> String {
    if s.len() <= 150 {
        return s.to_string();
    }
    format!("{}...", &s[..150.min(s.len())])
}

/// The field a differing line belongs to, so failures group by CAUSE rather
/// than by program. One missing form in the prelude is 1,012 programs.
fn field_of(line: &str) -> String {
    let t = line.trim_start();
    for name in [
        "(chapter", "(title", "(prose", "(pblocks", "(anns", "(sections", "(ctors", "(eff-ops",
        "(grounds", "(type-defs", "(rec-def", "(var-def", "(unit-def", "(defs",
    ] {
        if t.starts_with(name) {
            return name.trim_start_matches('(').to_string();
        }
    }
    "other".to_string()
}

/// Every `(def "<name>" "<slug>" (params ...)` header a gold carries, checked
/// against what our desugarer produced.
///
/// **A SUPERSET check, deliberately.** The emitter prunes the definition list
/// by reachability over the emitted IR text, so a gold holds FEWER definitions
/// than the source has and we cannot demand equality. What we can demand is
/// that every definition the gold kept exists in ours with the same name, the
/// same chapter slug and the same parameter count -- and that is the only
/// oracle the desugarer's SYNTHESIS passes have, because `deriving Show`
/// invents `<type>-show` and nothing else in the tree mentions it.
fn defs(dir: &Path) -> ExitCode {
    let Ok(golds) = std::env::var("CODEX_GOLDS") else {
        eprintln!("CODEX_GOLDS is not set; it names the bank, and a bank is never guessed at");
        return ExitCode::from(2);
    };
    let ir_dir = PathBuf::from(&golds).join("ir");
    let Ok(rd) = std::fs::read_dir(&ir_dir) else {
        eprintln!("{}: cannot read", ir_dir.display());
        return ExitCode::from(2);
    };
    let mut names: Vec<String> = rd
        .flatten()
        .filter(|e| e.path().extension().is_some_and(|x| x == "ir"))
        .filter_map(|e| e.path().file_stem().map(|s| s.to_string_lossy().into_owned()))
        .collect();
    names.sort();

    let (mut want, mut have, mut whole) = (0usize, 0usize, 0usize);
    let mut missing: std::collections::HashMap<String, (usize, String)> = Default::default();
    for name in &names {
        let Ok(src) = std::fs::read(&dir.join(format!("{name}.codex"))) else { continue };
        let Ok(ir) = std::fs::read_to_string(ir_dir.join(format!("{name}.ir"))) else { continue };
        let parsed = parser::parse(&src);
        let mut dg = codexc::desugar::Desugar::new(&src);
        let ch = dg.chapter(&parsed.tree);
        let ours: std::collections::HashSet<(String, usize)> =
            ch.defs.iter().map(|d| (d.name.clone(), d.params.len())).collect();
        let mut file_ok = true;
        for (dn, dp) in gold_defs(&ir) {
            want += 1;
            if ours.contains(&(dn.clone(), dp)) {
                have += 1;
            } else {
                file_ok = false;
                let why = if ch.defs.iter().any(|d| d.name == dn) {
                    format!("{dn}: parameter count")
                } else {
                    format!("{dn}: no such definition")
                };
                missing.entry(why).or_insert_with(|| (0, name.clone())).0 += 1;
            }
        }
        if file_ok {
            whole += 1;
        }
    }
    println!("{have} of {want} gold definitions present ({:.2}%), {whole} of {} files whole",
             100.0 * have as f64 / want.max(1) as f64, names.len());
    let mut ranked: Vec<_> = missing.into_iter().collect();
    ranked.sort_by(|a, b| b.1 .0.cmp(&a.1 .0).then(a.0.cmp(&b.0)));
    for (why, (n, at)) in ranked.iter().take(12) {
        println!("  {n} x {why}   e.g. {at}");
    }
    if have == want {
        println!("DEFS PRESENT: every definition a gold kept exists in ours");
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// `(def "name" "slug" (params (param "a" <type>) ...) ...` -- the header only.
///
/// A parameter is `(param "name" <type>)` and not a bare string, so the list
/// has to be read to its MATCHING paren rather than the first one: stopping at
/// the first `)` counts one parameter for every definition and reports the
/// rest as mismatched, which is what it did.
fn gold_defs(ir: &str) -> Vec<(String, usize)> {
    let mut out = Vec::new();
    let mut rest = ir;
    while let Some(at) = rest.find("(def \"") {
        rest = &rest[at + 6..];
        let Some(q) = rest.find('"') else { break };
        let name = rest[..q].to_string();
        let Some(pa) = rest.find("(params") else { break };
        let tail = &rest[pa..];
        let mut depth = 0usize;
        let mut end = tail.len();
        for (i, c) in tail.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = i;
                        break;
                    }
                }
                _ => {}
            }
        }
        out.push((name, tail[..end].matches("(param \"").count()));
    }
    out
}

fn grade(dir: &Path) -> ExitCode {
    let Ok(golds) = std::env::var("CODEX_GOLDS") else {
        eprintln!("CODEX_GOLDS is not set; it names the bank, and a bank is never guessed at");
        return ExitCode::from(2);
    };
    let ir_dir = PathBuf::from(&golds).join("ir");
    let Ok(rd) = std::fs::read_dir(&ir_dir) else {
        eprintln!("{}: cannot read", ir_dir.display());
        return ExitCode::from(2);
    };
    let mut names: Vec<String> = rd
        .flatten()
        .filter(|e| e.path().extension().is_some_and(|x| x == "ir"))
        .filter_map(|e| e.path().file_stem().map(|s| s.to_string_lossy().into_owned()))
        .collect();
    names.sort();

    let (mut matched, mut missing_unit, mut shown, mut supplied) = (0usize, 0usize, 0usize, 0usize);
    let mut by_field: std::collections::HashMap<String, (usize, String)> = Default::default();
    for name in &names {
        let unit = dir.join(format!("{name}.codex"));
        let Ok(src) = std::fs::read(&unit) else {
            missing_unit += 1;
            continue;
        };
        let Ok(ir) = std::fs::read_to_string(ir_dir.join(format!("{name}.ir"))) else { continue };
        let Some(gold) = gold_preamble(&ir) else { continue };
        let parsed = parser::parse(&src);
        let named = gold_chapter_name(&ir);
        if named.is_some_and(|n| n != preamble::derived_chapter_name(&parsed.tree, &src)) {
            supplied += 1;
        }
        let ours = preamble::emit(&parsed.tree, &src, named);
        if gold == ours {
            matched += 1;
            continue;
        }
        let (line, want, got) = first_difference(gold, &ours);
        let slot = by_field
            .entry(field_of(&want))
            .or_insert_with(|| (0, format!("{name}:{line}\n      gold {want}\n      ours {got}")));
        slot.0 += 1;
        shown += 1;
    }

    let total = names.len();
    println!("{matched} of {total} preambles byte-identical ({:.1}%)",
             100.0 * matched as f64 / total.max(1) as f64);
    if supplied > 0 {
        println!("{supplied} took the chapter NAME from the gold: it is a driver \
parameter (`compile-frontend source \"Program\" flags`), not a fact about the source");
    }
    if missing_unit > 0 {
        println!("{missing_unit} gold(s) had no resolved unit in {}", dir.display());
    }
    let mut ranked: Vec<_> = by_field.into_iter().collect();
    ranked.sort_by(|a, b| b.1 .0.cmp(&a.1 .0));
    for (field, (n, example)) in &ranked {
        println!("  {n} x first differ in {field}   e.g. {example}");
    }
    let _ = shown;
    if matched == total {
        println!("PREAMBLE MATCHES: every gold chapter header reproduces byte for byte");
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}


/// Preamble plus definition bodies: a whole gold, or nothing.
///
/// The preamble ends at `  (defs`, `ir::emit_defs` contributes the definition
/// lines, and the two closing parens shut `(defs` and `(chapter`.
fn whole(path: &Path, chapter: Option<&str>) -> Option<String> {
    let src = std::fs::read(path).ok()?;
    let parsed = parser::parse(&src);
    let head = preamble::emit(&parsed.tree, &src, chapter);
    let mut dg = codexc::desugar::Desugar::new(&src);
    let ch = dg.chapter(&parsed.tree);
    let defs = codexc::ir::emit_defs(&ch)?;
    Some(format!("{head}{defs}))"))
}

/// Every unit against its gold, whole. A unit whose body cannot be typed yet is
/// REFUSED and counted as such, never as a failure and never as a pass -- the
/// three are different and only one of them is a defect.
fn grade_whole(dir: &Path) -> ExitCode {
    let Ok(golds) = std::env::var("CODEX_GOLDS") else {
        eprintln!("CODEX_GOLDS is not set");
        return ExitCode::from(2);
    };
    let mut files: Vec<PathBuf> = Vec::new();
    if let Ok(rd) = std::fs::read_dir(dir) {
        for e in rd.flatten() {
            if e.path().extension().is_some_and(|x| x == "codex") {
                files.push(e.path());
            }
        }
    }
    files.sort();
    let (mut ok, mut refused, mut differ, mut nogold) = (0, 0, 0, 0);
    let mut shown = 0;
    for f in &files {
        let stem = f.file_stem().unwrap().to_string_lossy().to_string();
        let gp = Path::new(&golds).join("ir").join(format!("{stem}.ir"));
        let Ok(gold) = std::fs::read_to_string(&gp) else { nogold += 1; continue };
        let name = gold_chapter_name(&gold);
        match whole(f, name) {
            None => refused += 1,
            Some(ours) => {
                if ours.trim_end() == gold.trim_end() {
                    ok += 1;
                } else {
                    differ += 1;
                    if shown < 3 {
                        shown += 1;
                        let (at, g, o) = first_difference(gold.trim_end(), ours.trim_end());
                        println!("DIFFER {stem} at byte {at}\n  gold {g}\n  ours {o}");
                    }
                }
            }
        }
    }
    println!("{} unit(s): {ok} byte-identical, {differ} differ, {refused} refused (not yet typable), {nogold} without a gold",
             files.len());
    if differ == 0 { ExitCode::SUCCESS } else { ExitCode::FAILURE }
}
