//! Assemble a self-contained unit from a Codex file and everything it cites.
//!
//! **THIS ARM RESOLVES ITS OWN CITES, AND THAT IS THE POINT.** Until now every
//! arm -- bare metal, zig, wasm and this one -- was handed a unit assembled by
//! one Python script. Four arms agreeing says nothing about that script: a
//! bundling bug is applied identically to all four before any of them run, so
//! the one component no comparison can falsify is the one they share. Two
//! independent resolvers that agree on a corpus is evidence; one resolver used
//! four times is none.
//!
//! WHAT THIS CANNOT INVENT, and it is exactly one thing: the QUIRE REGISTRY.
//! `cites Foreword chapter ListUtils` names a quire, and a quire maps to a
//! directory by a table with no derivable convention -- `Foreword` is
//! `codex/foreword/core` and not `codex/foreword`, `Wflow` is `codex/workflow`,
//! `Games` is `apps/games/classic`. Resolving by chapter NAME alone instead was
//! measured and refused: the checkout holds 3,728 chapters under 3,560 distinct
//! names, and the 85 collisions are the dangerous shape -- a test driver
//! shadowing the library chapter it tests, `codex/test/hamt-test.codex` against
//! `codex/foreword/core/Hamt.codex`. So the registry is DATA, read like the
//! chapters are, and this module parses it rather than asking another tool to.
//!
//! WHAT IT REFUSES OR REPORTS, which is where a second opinion earns its keep.
//! The Python resolver answers a case-insensitive lookup silently, because the
//! registry is a PowerShell hashtable and those are case-insensitive. That is
//! faithful, and it is also how `UI` spelled `Ui` fourteen times went unnoticed
//! until it had silently dropped whole programs from every sweep. Here the
//! lookup still succeeds -- refusing would help nobody -- and it SAYS SO. Same
//! for a registered directory that does not exist, and for a cite that names a
//! chapter no file provides.
//!
//! THE ORDER IS LOAD-BEARING AND IT IS UPSTREAM'S. Dependencies before the
//! thing that cites them, transitively, each one once, depth first. Two
//! chapters the desugarer needs and no author would think to cite -- ListUtils,
//! because `for x in xs` becomes `map-list`, and Tuple, because a tuple literal
//! becomes `MkTup<N>` -- lead every unit unless the source already embeds them.

use crate::cst::NodeKind;
use crate::parser;
use crate::token::Token;
use std::collections::BTreeSet;
use std::fmt;
use std::path::{Path, PathBuf};

/// The two chapters every unit gets whether or not anything cites them.
const IMPLICIT: [(&str, &str); 2] = [("Foreword", "ListUtils"), ("Foreword", "Tuple")];

/// Something worth saying out loud about a bundle that was still produced.
///
/// A complaint is not a failure. Every one of these describes a unit that got
/// built; refusing on them would only mean the caller reaches for the other
/// bundler. What they are for is the triage rule: a difference between this arm
/// and Codex is a finding until someone shows it is a bug in this arm.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Complaint {
    /// The cite's quire is not in the registry at all.
    UnregisteredQuire { who: String, quire: String, chapter: String },
    /// The quire is registered and the chapter is not a file in its directory.
    NoSuchChapter { who: String, quire: String, chapter: String, looked: PathBuf },
    /// The lookup only succeeded by ignoring case. Upstream spells it both ways.
    QuireCase { who: String, cited: String, registered: String },
    /// The registry names a directory that is not there.
    DeadQuireDir { quire: String, dir: PathBuf },
    /// Two files under the same quire claim the same chapter name.
    AmbiguousChapter { quire: String, chapter: String, first: PathBuf, second: PathBuf },
    /// The chapter's file is CRLF in a checkout that is otherwise LF.
    ///
    /// **The Python resolver makes this invisible.** It reads in text mode, so
    /// Python's universal-newline translation turns every CRLF into LF before
    /// the bundler ever sees one, and the unit it writes is uniformly LF. This
    /// one reads bytes and keeps what is there, so the two bundlers disagree by
    /// exactly one carriage return per line on 20 of the checkout's 3,718
    /// chapters -- all of them in `foreword`, which is to say in the library
    /// every program reaches transitively.
    ///
    /// Reported and not corrected. The lexer treats a carriage return as
    /// trivia, so the compiled program is the same either way; what is not the
    /// same is a bundler that quietly rewrites its input, and which of those
    /// two behaviours is wanted is not this module's call to make silently.
    CarriageReturns { chapter: String, path: PathBuf },
}

impl fmt::Display for Complaint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Complaint::UnregisteredQuire { who, quire, chapter } => {
                write!(f, "UNRESOLVED: {who} cites {quire} chapter {chapter} -- no such quire in the registry")
            }
            Complaint::NoSuchChapter { who, quire, chapter, looked } => {
                write!(f, "UNRESOLVED: {who} cites {quire} chapter {chapter} -- no {}", looked.display())
            }
            Complaint::QuireCase { who, cited, registered } => {
                write!(f, "CASE: {who} cites `{cited}`, the registry says `{registered}` -- resolved anyway, as PowerShell would")
            }
            Complaint::DeadQuireDir { quire, dir } => {
                write!(f, "DEAD QUIRE: the registry maps {quire} to {}, which is not a directory", dir.display())
            }
            Complaint::AmbiguousChapter { quire, chapter, first, second } => {
                write!(f, "AMBIGUOUS: {quire} chapter {chapter} is both {} and {}", first.display(), second.display())
            }
            Complaint::CarriageReturns { chapter, path } => {
                write!(f, "CRLF: chapter {chapter} is {} -- kept as written; the Python resolver drops these silently", path.display())
            }
        }
    }
}

/// The quire registry: a name, and the directory its chapters live in.
pub struct Quires {
    entries: Vec<(String, PathBuf)>,
}

impl Quires {
    /// Read upstream's registry, plus any local one the project supplies.
    ///
    /// The local file is how a project that is not the depot names its own
    /// quires -- safari's `Safari`, `Judge` and `Gold` are its own directories
    /// and upstream has never heard of them. One `name<TAB>relative/dir` per
    /// line, `#` to end of line is a comment. It is a FILE rather than a flag
    /// because the answer belongs to the project, not to the invocation.
    pub fn read(codex: &Path, local: Option<&Path>) -> Result<Self, String> {
        let mut entries = Vec::new();
        let map = codex.join("build").join("quire-map.ps1");
        let text = std::fs::read_to_string(&map)
            .map_err(|e| format!("cannot read the quire registry at {}: {e}", map.display()))?;
        for (quire, dir) in parse_quire_map(&text) {
            entries.push((quire, codex.join(dir)));
        }
        if entries.is_empty() {
            return Err(format!("{} has no $QuireDirs table", map.display()));
        }
        if let Some(path) = local {
            let text = std::fs::read_to_string(path)
                .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
            let base = path.parent().unwrap_or(Path::new("."));
            for (n, line) in text.lines().enumerate() {
                let line = line.split('#').next().unwrap_or("").trim();
                if line.is_empty() {
                    continue;
                }
                let mut it = line.split_whitespace();
                match (it.next(), it.next(), it.next()) {
                    (Some(q), Some(d), None) => entries.push((q.to_string(), base.join(d))),
                    _ => return Err(format!("{}:{}: want `Quire<space>dir`", path.display(), n + 1)),
                }
            }
        }
        Ok(Quires { entries })
    }

    /// -> (directory, the registered spelling) for a cited quire.
    ///
    /// Exact match first, then case-insensitively, which is what the registry's
    /// own PowerShell hashtable does. The caller is told which it was.
    fn dir(&self, quire: &str) -> Option<(&Path, &str)> {
        if let Some((n, d)) = self.entries.iter().find(|(n, _)| n == quire) {
            return Some((d.as_path(), n.as_str()));
        }
        self.entries
            .iter()
            .find(|(n, _)| n.eq_ignore_ascii_case(quire))
            .map(|(n, d)| (d.as_path(), n.as_str()))
    }

    /// Registered directories that are not there. Checked once, up front,
    /// because a registry nobody validates is a registry that rots.
    pub fn dead(&self) -> Vec<Complaint> {
        self.entries
            .iter()
            .filter(|(_, d)| !d.is_dir())
            .map(|(q, d)| Complaint::DeadQuireDir { quire: q.clone(), dir: d.clone() })
            .collect()
    }
}

/// Pull `'Name' = 'dir'` pairs out of the `$QuireDirs = @{ ... }` table.
///
/// A hand parser rather than a regex: it has to stop at the table's closing
/// brace and skip `#` comments, and the file carries several of both.
fn parse_quire_map(text: &str) -> Vec<(String, String)> {
    let Some(start) = text.find("$QuireDirs = @{") else {
        return Vec::new();
    };
    let body = &text[start + "$QuireDirs = @{".len()..];
    let end = body.find('}').unwrap_or(body.len());
    let mut out = Vec::new();
    for line in body[..end].lines() {
        let line = line.split('#').next().unwrap_or("");
        let mut rest = line;
        while let Some(open) = rest.find('\'') {
            let after = &rest[open + 1..];
            let Some(close) = after.find('\'') else { break };
            let key = &after[..close];
            let tail = &after[close + 1..];
            let Some(eq) = tail.find('=') else { break };
            let after_eq = &tail[eq + 1..];
            let Some(vopen) = after_eq.find('\'') else { break };
            let vrest = &after_eq[vopen + 1..];
            let Some(vclose) = vrest.find('\'') else { break };
            out.push((key.to_string(), vrest[..vclose].replace('\\', "/")));
            rest = &vrest[vclose + 1..];
        }
    }
    out
}

/// The `(quire, chapter)` pairs a source cites, in source order.
///
/// **Read through the real lexer, not a regex, and that is a deliberate
/// difference from the Python.** A regex over raw text matches the word `cites`
/// wherever it appears -- including inside prose, which every chapter in this
/// language has by the paragraph. Going through the parser means the bundler
/// and the compiler agree about what a cite IS, by construction rather than by
/// two patterns being kept in step.
pub fn cites_of(src: &[u8]) -> Vec<(String, String)> {
    let parsed = parser::parse(src);
    let mut out = Vec::new();
    for node in parsed.tree.descendants(NodeKind::Cites) {
        let toks: Vec<&Token> = node.tokens().filter(|t| !t.kind.is_trivia()).collect();
        let word = |t: &Token| String::from_utf8_lossy(t.text(src)).into_owned();
        // `cites <Quire> chapter <Name>` and optionally `(a, b)`.
        let Some(kw) = toks.iter().position(|t| word(t) == "chapter") else { continue };
        let (Some(quire), true) = (toks.get(kw - 1), kw >= 1) else { continue };
        // THE NAME IS A SPAN, NOT A TOKEN. `cites Build chapter Build Settings`
        // is one chapter called `Build Settings`, and there are chapters whose
        // names carry a hyphen too -- both lex as several tokens and neither
        // survives being rejoined by a rule. Taking the source between the
        // first name token and the last keeps whatever was written.
        let rest: Vec<&&Token> = toks[kw + 1..].iter().take_while(|t| word(t) != "(").collect();
        let (Some(first), Some(last)) = (rest.first(), rest.last()) else { continue };
        let from = first.offset as usize;
        let to = (last.offset + last.len) as usize;
        let name = String::from_utf8_lossy(&src[from..to]).trim().to_string();
        if name.is_empty() {
            continue;
        }
        out.push((word(quire), name));
    }
    out
}

/// The chapters a source already carries, as `Chapter: Quire--Name`.
///
/// A bundle satisfies a cite by CONTAINING the chapter, so a source that
/// already embeds one must not be handed a second copy.
fn embedded(src: &[u8]) -> BTreeSet<(String, String)> {
    let text = String::from_utf8_lossy(src);
    let mut out = BTreeSet::new();
    for line in text.lines() {
        let Some(rest) = line.trim_start().strip_prefix("Chapter:") else { continue };
        if let Some((q, n)) = rest.trim().split_once("--") {
            out.insert((q.trim().to_string(), n.trim().to_string()));
        }
    }
    out
}

pub struct Bundle {
    pub text: String,
    pub complaints: Vec<Complaint>,
}

/// Assemble `root` and everything it cites, dependencies first, each once.
pub fn resolve(root: &Path, quires: &Quires) -> Result<Bundle, String> {
    let src = std::fs::read(root).map_err(|e| format!("cannot read {}: {e}", root.display()))?;
    let mut seen: BTreeSet<PathBuf> = BTreeSet::new();
    seen.insert(root.to_path_buf());
    let mut complaints = quires.dead();
    let mut parts: Vec<String> = Vec::new();

    let here = embedded(&src);
    let mut cites: Vec<(String, String)> = IMPLICIT
        .iter()
        .map(|(q, c)| (q.to_string(), c.to_string()))
        .filter(|qc| !here.contains(qc))
        .collect();
    cites.extend(cites_of(&src));

    let who = name_of(root);
    walk(&who, &cites, quires, &mut seen, &mut complaints, &mut parts)?;
    parts.push(tidy(&String::from_utf8_lossy(&src)));
    Ok(Bundle { text: parts.join("\n"), complaints })
}

fn name_of(p: &Path) -> String {
    p.file_name().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default()
}

/// One chapter's own text is trailed by exactly one newline, as upstream's
/// bundler does; the parts are then joined by one more.
///
/// **THE TRIM TAKES CR AS WELL AS LF, AND THAT IS NOT COSMETIC.** A chapter
/// committed with CRLF ends `\r\n\r\n`; trimming only `\n` stops at the `\r`
/// and keeps a blank line that a text-mode reader -- which never sees a `\r` at
/// all -- has already removed. So the two bundlers differed by a whole line on
/// every CRLF chapter, and the cause looked like an ordering bug rather than
/// what it was. Trimming trailing blank lines is a question about blank lines,
/// and the answer should not depend on which bytes spell one.
fn tidy(text: &str) -> String {
    format!("{}\n", text.trim_end_matches(['\n', '\r']))
}

fn walk(
    who: &str,
    cites: &[(String, String)],
    quires: &Quires,
    seen: &mut BTreeSet<PathBuf>,
    complaints: &mut Vec<Complaint>,
    parts: &mut Vec<String>,
) -> Result<(), String> {
    for (quire, chapter) in cites {
        let Some((dir, registered)) = quires.dir(quire) else {
            complaints.push(Complaint::UnregisteredQuire {
                who: who.to_string(),
                quire: quire.clone(),
                chapter: chapter.clone(),
            });
            continue;
        };
        if registered != quire {
            complaints.push(Complaint::QuireCase {
                who: who.to_string(),
                cited: quire.clone(),
                registered: registered.to_string(),
            });
        }
        let dep = dir.join(format!("{chapter}.codex"));
        if !dep.is_file() {
            complaints.push(Complaint::NoSuchChapter {
                who: who.to_string(),
                quire: quire.clone(),
                chapter: chapter.clone(),
                looked: dep,
            });
            continue;
        }
        if !seen.insert(dep.clone()) {
            continue;
        }
        let src = std::fs::read(&dep).map_err(|e| format!("cannot read {}: {e}", dep.display()))?;
        if src.contains(&b'\r') {
            complaints.push(Complaint::CarriageReturns {
                chapter: chapter.clone(),
                path: dep.clone(),
            });
        }
        let sub = cites_of(&src);
        walk(&name_of(&dep), &sub, quires, seen, complaints, parts)?;
        parts.push(tidy(&String::from_utf8_lossy(&src)));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quire_map_reads_multiple_pairs_per_line() {
        let t = "$QuireDirs = @{\n    'Foreword' = 'codex\\foreword\\core'; 'OS' = 'codex\\os\\core'\n}";
        assert_eq!(
            parse_quire_map(t),
            vec![
                ("Foreword".into(), "codex/foreword/core".into()),
                ("OS".into(), "codex/os/core".into()),
            ]
        );
    }

    #[test]
    fn quire_map_skips_commented_lines() {
        let t = "$QuireDirs = @{\n    # 'Ghost' = 'nowhere'\n    'Real' = 'here'\n}";
        assert_eq!(parse_quire_map(t), vec![("Real".into(), "here".into())]);
    }

    /// The word `cites` is ordinary English and these chapters are mostly
    /// prose, so a text scan finds citations that are not there.
    #[test]
    fn prose_that_says_cites_is_not_a_citation() {
        let src = b"Chapter: X\n  cites Foreword chapter Maybe\n\n Nothing else cites Foreword chapter Ghost here.\n\n We say:\n";
        assert_eq!(cites_of(src), vec![("Foreword".to_string(), "Maybe".to_string())]);
    }

    /// `Build Settings` is one chapter with a space in its name, and a cite may
    /// carry a list of selected names that is not part of it.
    #[test]
    fn a_chapter_name_can_be_several_words_and_the_selection_is_not_part_of_it() {
        let src = b"Chapter: X\n  cites Build chapter Build Settings (max-errors, max-emit-work)\n\n We say:\n";
        assert_eq!(cites_of(src), vec![("Build".to_string(), "Build Settings".to_string())]);
    }

    #[test]
    fn embedded_chapters_are_recognised_by_their_double_dash() {
        let src = b"Chapter: Foreword--ListUtils\nChapter: Main\n";
        let e = embedded(src);
        assert!(e.contains(&("Foreword".to_string(), "ListUtils".to_string())));
        assert_eq!(e.len(), 1);
    }
}
