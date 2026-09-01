//! Run a Codex program.
//!
//!     codexrun <unit.codex>              print what it prints
//!     codexrun --check <unit.codex> <expected>
//!
//! It walks the desugared AST. No types, no IR, no zig, no guest -- which is
//! the point: this arm shares NOTHING with the others below the AST, so when
//! it disagrees the disagreement is attributable.
//!
//! The input must be a RESOLVED unit, the same as everything else here.

use codexc::desugar::Desugar;
use codexc::interp::Interp;
use codexc::parser;
use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("--check") if args.len() == 3 => check(Path::new(&args[1]), Path::new(&args[2])),
        Some("sweep") if args.len() == 3 => sweep(Path::new(&args[1]), Path::new(&args[2])),
        Some(p) if args.len() == 1 => match run(Path::new(p)) {
            Ok(out) => {
                print!("{out}");
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("{}: {e}", p);
                ExitCode::FAILURE
            }
        },
        _ => {
            eprintln!("usage: codexrun <unit.codex>");
            eprintln!("       codexrun --check <unit.codex> <expected>");
            eprintln!("       codexrun sweep <units-dir> <codex-test-dir>");
            ExitCode::from(2)
        }
    }
}

fn run(path: &Path) -> Result<String, String> {
    let src = std::fs::read(path).map_err(|e| e.to_string())?;
    let parsed = parser::parse(&src);
    let mut dg = Desugar::new(&src);
    let ch = dg.chapter(&parsed.tree);
    let mut it = Interp::new(&ch);
    match it.run() {
        Ok(()) => Ok(std::mem::take(&mut it.out)),
        // The partial output comes back with the error: seeing which line it
        // reached is most of the diagnosis.
        Err(e) => Err(format!("{}\n--- output before the error ---\n{}", e.0, it.out)),
    }
}

/// Run every unit that has a `.expected` beside it in the checkout, and diff.
///
/// This is the conformance question, and through the zig pipeline it costs
/// hours. Here it is one process and no compilation: the answer we care about
/// is whether the program still PRINTS the right thing, and that does not need
/// a compiler at all.
fn sweep(units: &Path, tests: &Path) -> ExitCode {
    let mut expected: Vec<std::path::PathBuf> = Vec::new();
    collect_expected(tests, &mut expected);
    expected.sort();
    let (mut ran, mut matched, mut no_unit) = (0usize, 0usize, 0usize);
    let mut by_cause: std::collections::HashMap<String, (usize, String)> = Default::default();
    let t0 = std::time::Instant::now();
    for exp in &expected {
        let Some(stem) = exp.file_stem().map(|s| s.to_string_lossy().into_owned()) else {
            continue;
        };
        let unit = units.join(format!("{stem}.codex"));
        if !unit.is_file() {
            no_unit += 1;
            continue;
        }
        ran += 1;
        let want = std::fs::read_to_string(exp).unwrap_or_default();
        match run(&unit) {
            Ok(got) if got == want => matched += 1,
            Ok(got) => {
                let first = want
                    .lines()
                    .zip(got.lines())
                    .position(|(a, b)| a != b)
                    .map(|i| format!("line {} differs", i + 1))
                    .unwrap_or_else(|| "output length differs".to_string());
                by_cause.entry(first).or_insert_with(|| (0, stem.clone())).0 += 1;
            }
            Err(e) => {
                // The first line of the error is the cause; group by it so a
                // missing builtin shows up once with a count.
                let cause = e.lines().next().unwrap_or("?").to_string();
                by_cause.entry(cause).or_insert_with(|| (0, stem.clone())).0 += 1;
            }
        }
    }
    println!("{matched} of {ran} programs print exactly what they should ({:.1}%), in {:.1}s",
             100.0 * matched as f64 / ran.max(1) as f64, t0.elapsed().as_secs_f64());
    if no_unit > 0 {
        println!("{no_unit} expected file(s) had no resolved unit");
    }
    let mut ranked: Vec<_> = by_cause.into_iter().collect();
    ranked.sort_by(|a, b| b.1 .0.cmp(&a.1 .0).then(a.0.cmp(&b.0)));
    for (cause, (n, at)) in ranked.iter().take(15) {
        println!("  {n} x {cause}   e.g. {at}");
    }
    if matched == ran {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn collect_expected(root: &Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(rd) = std::fs::read_dir(root) else { return };
    for e in rd.flatten() {
        let p = e.path();
        if p.is_dir() {
            if p.file_name().is_some_and(|n| n == "apps" || n == ".git") {
                continue;
            }
            collect_expected(&p, out);
        } else if p.extension().is_some_and(|x| x == "expected") {
            out.push(p);
        }
    }
}

fn check(path: &Path, expected: &Path) -> ExitCode {
    let want = match std::fs::read_to_string(expected) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("{}: {e}", expected.display());
            return ExitCode::from(2);
        }
    };
    let got = match run(path) {
        Ok(o) => o,
        Err(e) => {
            println!("FAILED to run {}", path.display());
            println!("{e}");
            return ExitCode::FAILURE;
        }
    };
    let (w, g): (Vec<&str>, Vec<&str>) = (want.lines().collect(), got.lines().collect());
    let mut bad = 0;
    for i in 0..w.len().max(g.len()) {
        let (a, b) = (w.get(i).copied().unwrap_or("<none>"), g.get(i).copied().unwrap_or("<none>"));
        if a != b {
            println!("line {}: want {a:?}", i + 1);
            println!("         got {b:?}");
            bad += 1;
        }
    }
    if bad == 0 {
        println!("MATCHES {} -- all {} lines", expected.display(), w.len());
        ExitCode::SUCCESS
    } else {
        println!("{bad} of {} lines differ", w.len().max(g.len()));
        ExitCode::FAILURE
    }
}
