//! Resolve a Codex file's cites into a self-contained unit, without asking
//! another toolchain where anything is.
//!
//!     bundle one <root.codex> [out.codex]   one unit, or stdout
//!     bundle diff <units-dir> <roots-dir>   against units another bundler wrote
//!
//! `$CODEX_ROOT` names the checkout whose chapters get cited; a `quires.tsv`
//! beside the root -- or `$CODEX_QUIRES` -- names any quire that checkout has
//! never heard of, one `Name<space>dir` per line.
//!
//! **`diff` IS THE REASON THIS EXISTS.** A second bundler nobody compares is
//! worse than one bundler: it is a second thing to keep in step and no signal
//! that it has drifted. `diff` takes a directory of units some other bundler
//! produced -- today the ladder's `resolve_corpus.py` -- and the roots they
//! were made from, and reports every byte of disagreement. A difference is a
//! FINDING until someone shows it is a bug in this arm; it is not a licence to
//! reach for the other bundler.
//!
//! WHAT IT SAYS TODAY, and it wants a same-instant comparison to say it: with
//! units resolved from the checkout as it stands, 606 are byte-identical and
//! FIVE differ. All five are the CRLF chapters, and that is the whole of the
//! disagreement between the two resolvers. Handed a units directory written
//! against an older checkout, most of the diff is upstream's prose edits rather
//! than anything either bundler did -- generate the units now.

use codexc::bundle::{self, Quires};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("one") if args.len() == 2 || args.len() == 3 => one(&args[1], args.get(2)),
        Some("diff") if args.len() == 3 => diff(Path::new(&args[1]), Path::new(&args[2])),
        _ => {
            eprintln!("usage: bundle one <root.codex> [out.codex]");
            eprintln!("       bundle diff <units-dir> <roots-dir>");
            ExitCode::from(2)
        }
    }
}

/// The checkout, and the local quire file if the project has one.
fn quires(near: &Path) -> Result<Quires, String> {
    let root = std::env::var("CODEX_ROOT")
        .map_err(|_| "CODEX_ROOT is not set; it names the checkout whose chapters get cited".to_string())?;
    let local = match std::env::var("CODEX_QUIRES") {
        Ok(p) => Some(PathBuf::from(p)),
        Err(_) => {
            // Walk up from the file being bundled: a project's quires belong to
            // the project, and finding them should not need an argument.
            let mut d = near.canonicalize().ok();
            let mut found = None;
            while let Some(dir) = d {
                let cand = dir.join("quires.tsv");
                if cand.is_file() {
                    found = Some(cand);
                    break;
                }
                d = dir.parent().map(Path::to_path_buf);
            }
            found
        }
    };
    Quires::read(Path::new(&root), local.as_deref())
}

fn one(root: &str, out: Option<&String>) -> ExitCode {
    let root = Path::new(root);
    let qs = match quires(root.parent().unwrap_or(Path::new("."))) {
        Ok(q) => q,
        Err(why) => {
            eprintln!("REFUSED: {why}");
            return ExitCode::from(2);
        }
    };
    let b = match bundle::resolve(root, &qs) {
        Ok(b) => b,
        Err(why) => {
            eprintln!("REFUSED: {why}");
            return ExitCode::from(2);
        }
    };
    for c in &b.complaints {
        eprintln!("{c}");
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
    let broken = b.complaints.iter().any(|c| {
        matches!(c, bundle::Complaint::UnregisteredQuire { .. } | bundle::Complaint::NoSuchChapter { .. })
    });
    if broken {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}

fn diff(units: &Path, roots: &Path) -> ExitCode {
    let qs = match quires(roots) {
        Ok(q) => q,
        Err(why) => {
            eprintln!("REFUSED: {why}");
            return ExitCode::from(2);
        }
    };
    let mut names: Vec<PathBuf> = match std::fs::read_dir(units) {
        Ok(rd) => rd.filter_map(|e| e.ok()).map(|e| e.path()).collect(),
        Err(e) => {
            eprintln!("REFUSED: cannot read {}: {e}", units.display());
            return ExitCode::from(2);
        }
    };
    names.retain(|p| p.extension().is_some_and(|e| e == "codex"));
    names.sort();

    // ROOTS ARE FOUND RECURSIVELY AND BY STEM, because that is the population
    // resolve_corpus.py resolves: every .codex under codex/test except apps/,
    // keyed by bare stem. Looking only in the top directory found roots for 611
    // of 1,231 units and called the other 620 "no root here" -- half the corpus
    // silently outside the gate, which is the failure this gate exists to catch
    // in other people's tools.
    let mut index: std::collections::BTreeMap<String, PathBuf> = std::collections::BTreeMap::new();
    let mut ambiguous: Vec<String> = Vec::new();
    walk_roots(roots, &mut index, &mut ambiguous);
    for a in &ambiguous {
        println!("ambiguous root stem: {a}");
    }

    let (mut same, mut differ, mut absent, mut eol) = (0usize, 0usize, 0usize, 0usize);
    let mut first: Vec<String> = Vec::new();
    for unit in &names {
        let stem = unit.file_stem().unwrap_or_default().to_string_lossy().into_owned();
        let Some(root) = index.get(&stem).cloned() else {
            absent += 1;
            continue;
        };
        let theirs = std::fs::read_to_string(unit).unwrap_or_default();
        let ours = match bundle::resolve(&root, &qs) {
            Ok(b) => b.text,
            Err(why) => {
                differ += 1;
                if first.len() < 10 {
                    first.push(format!("{stem}: REFUSED {why}"));
                }
                continue;
            }
        };
        if ours == theirs {
            same += 1;
        } else if universal(&ours) == universal(&theirs) {
            // Upstream's malformed line endings, filed as issue 124. Kept
            // visible and counted, but not a bundler disagreement: the two
            // resolvers read the same bytes and one of them is a text-mode
            // reader translating them.
            eol += 1;
        } else {
            differ += 1;
            if first.len() < 10 {
                first.push(format!("{stem}: {}", why_differ(&ours, &theirs)));
            }
        }
    }
    for line in &first {
        println!("{line}");
    }
    println!();
    println!("{same} identical, {eol} differ only in line endings (issue 124), \
{differ} differ, {absent} units with no root here");
    if differ == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}

/// What a text-mode reader would have seen: CRLF, and a LONE CR, are one break.
///
/// **THE LONE CR IS THE WHOLE REASON THIS EXISTS.** Twenty chapters upstream
/// carry `\r\r\n` on their `Chapter:` line -- a doubled carriage return, one per
/// file. Python reads with universal newlines, where a lone `\r` is also a line
/// break, so it sees a blank line there; reading bytes keeps two carriage
/// returns on one line. Stripping CR is NOT enough to compare the two, because
/// one side has a line the other does not. Translating the way the text-mode
/// reader does is.
fn universal(s: &str) -> String {
    s.replace("\r\n", "\n").replace('\r', "\n")
}

/// Every `.codex` under `roots` except `apps/`, keyed by bare stem.
fn walk_roots(
    dir: &Path,
    index: &mut std::collections::BTreeMap<String, PathBuf>,
    ambiguous: &mut Vec<String>,
) {
    let Ok(rd) = std::fs::read_dir(dir) else { return };
    for e in rd.filter_map(|e| e.ok()) {
        let p = e.path();
        if p.is_dir() {
            if p.file_name().is_some_and(|n| n == "apps") {
                continue;
            }
            walk_roots(&p, index, ambiguous);
        } else if p.extension().is_some_and(|x| x == "codex") {
            let stem = p.file_stem().unwrap_or_default().to_string_lossy().into_owned();
            if let Some(had) = index.insert(stem.clone(), p) {
                ambiguous.push(format!("{stem} ({} and another)", had.display()));
            }
        }
    }
}

/// The first line that disagrees, and how long each side is -- enough to say
/// what KIND of difference it is without printing two whole units.
///
/// **CARRIAGE RETURNS GET NAMED RATHER THAN SHOWN.** The known difference
/// between the two resolvers is that Python's text-mode read drops CR and this
/// one keeps it, and printing those two lines side by side prints two strings
/// that look identical -- the least useful true thing a diff can say.
fn why_differ(ours: &str, theirs: &str) -> String {
    if ours.replace('\r', "") == theirs.replace('\r', "") {
        let n = ours.bytes().filter(|b| *b == b'\r').count();
        return format!("carriage returns only ({n} of them); see issue 124");
    }
    let mut a = ours.lines();
    let mut b = theirs.lines();
    let mut n = 0usize;
    loop {
        n += 1;
        match (a.next(), b.next()) {
            (None, None) => {
                return format!("same lines, different bytes ({} vs {})", ours.len(), theirs.len())
            }
            (x, y) if x == y => continue,
            (Some(x), Some(y)) => {
                return format!("line {n}: ours `{}` theirs `{}`", clip(x), clip(y))
            }
            (Some(x), None) => return format!("line {n}: ours has `{}`, theirs ended", clip(x)),
            (None, Some(y)) => return format!("line {n}: theirs has `{}`, ours ended", clip(y)),
        }
    }
}

fn clip(s: &str) -> String {
    if s.chars().count() > 60 {
        format!("{}...", s.chars().take(60).collect::<String>())
    } else {
        s.to_string()
    }
}
