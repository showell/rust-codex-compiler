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
//! THE RULES, one each, with no second way in:
//!
//! - **The program names its checkout.** A file inside a Cobblestone checkout
//!   resolves against that checkout; a project outside one names it with a
//!   `checkout <path>` line in its `quires.tsv`. The environment is never read.
//! - **A cited chapter is written under its quire**, `Chapter: Foreword--Maybe`,
//!   as upstream's compile step writes it. The program's own chapter keeps its
//!   header.
//! - **A cite is present only under its own quire.** The same chapter name
//!   carried under another prefix, or plain, is a CLASH and the unit is
//!   refused. Upstream's two resolvers answer that case differently -- one
//!   skips the cite, the other adds a second copy -- so it is refused here
//!   rather than decided.
//! - **Resolving a resolved unit changes nothing, and needs no checkout.**
//!
//! THE ORDER IS LOAD-BEARING AND IT IS UPSTREAM'S. Dependencies before the
//! thing that cites them, transitively, each one once, depth first. Two
//! chapters the desugarer needs and no author would think to cite -- ListUtils,
//! because `for x in xs` becomes `map-list`, and Tuple, because a tuple literal
//! becomes `MkTup<N>` -- lead every unit.

use crate::cst::NodeKind;
use crate::parser;
use crate::token::Token;
use std::collections::BTreeSet;
use std::fmt;
use std::path::{Path, PathBuf};

/// The two chapters every unit gets whether or not anything cites them.
const IMPLICIT: [(&str, &str); 2] = [("Foreword", "ListUtils"), ("Foreword", "Tuple")];

/// What makes a directory a Cobblestone checkout: the compiler's driver.
const MARKER: &str = "codex/compiler/opening.codex";

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
    /// **REPORTED AND FATAL, because the compiled program is NOT the same
    /// either way.** `codexir` halts with CDX1000 when an unmapped byte lands
    /// inside a TYPE, and a `Chapter:` line ending in CRLF puts the return
    /// inside the chapter name, where it defeats the cite that names the
    /// chapter without one. Both failures read as something else entirely.
    ///
    /// The bytes are still kept as they were read. What changed is that the
    /// bundler will not WRITE a unit it knows cannot compile.
    CarriageReturns { chapter: String, path: PathBuf },
    /// The project's own quire file re-uses a name the checkout also registers.
    ///
    /// Upstream took safari's `port/` in as `apps/safari/port` at Update 55 and
    /// registered it under the same name the project has always used. The
    /// project's file wins -- it is the more specific statement, and a chapter
    /// cited from inside safari-codex means safari-codex's copy -- but a name
    /// resolving somewhere other than where the checkout says is not something
    /// to decide in silence.
    ShadowedQuire { quire: String, local: PathBuf, upstream: PathBuf },
}

impl Complaint {
    /// A unit with this complaint is missing a chapter it cites.
    pub fn is_broken(&self) -> bool {
        matches!(self, Complaint::UnregisteredQuire { .. } | Complaint::NoSuchChapter { .. })
    }
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
            Complaint::ShadowedQuire { quire, local, upstream } => {
                write!(f, "SHADOWED: quire {quire} is this project's {}, not the checkout's {}", local.display(), upstream.display())
            }
        }
    }
}

/// The quire registry: a name, and the directory its chapters live in.
pub struct Quires {
    entries: Vec<(String, PathBuf)>,
    shadowed: Vec<Complaint>,
}

impl Quires {
    /// Read upstream's registry, plus any local one the project supplies.
    ///
    /// The local file is how a project that is not the depot names its own
    /// quires -- safari's `Safari`, `Judge` and `Gold` are its own directories.
    /// One `name<space>relative/dir` per line, `#` to end of line is a comment,
    /// and a `checkout <path>` line names the checkout (see [`project_of`]).
    /// It is a FILE rather than a flag because the answer belongs to the
    /// project, not to the invocation.
    ///
    /// **THE LOCAL FILE WINS, and upstream having never heard of these names is
    /// not something to rely on.** It stopped being true at Update 55, which
    /// took safari's `port/` into the checkout as `apps/safari/port` under the
    /// name `Safari`. A shadowed name is removed here rather than merely
    /// outranked, so that spelling it in a different case cannot reach the loser
    /// either.
    pub fn read(codex: &Path, local: Option<&Path>) -> Result<Self, String> {
        let mut entries = Vec::new();
        let (map, text) = quire_registry(codex)?;
        for (quire, dir) in parse_quire_map(&text) {
            entries.push((quire, codex.join(dir)));
        }
        if entries.is_empty() {
            return Err(format!("{} has no $QuireDirs table", map.display()));
        }
        let mut shadowed = Vec::new();
        if let Some(path) = local {
            let text = std::fs::read_to_string(path)
                .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
            let base = path.parent().unwrap_or(Path::new("."));
            let mut mine: Vec<(String, PathBuf)> = Vec::new();
            for (n, line) in text.lines().enumerate() {
                let words: Vec<&str> = line.split('#').next().unwrap_or("").split_whitespace().collect();
                match words.as_slice() {
                    [] | ["checkout", ..] => continue,
                    [q, d] => mine.push((q.to_string(), base.join(d))),
                    _ => return Err(format!("{}:{}: want `Quire<space>dir`", path.display(), n + 1)),
                }
            }
            for (q, d) in &mine {
                for (uq, ud) in entries.iter().filter(|(n, _)| n.eq_ignore_ascii_case(q)) {
                    shadowed.push(Complaint::ShadowedQuire {
                        quire: uq.clone(),
                        local: d.clone(),
                        upstream: ud.clone(),
                    });
                }
            }
            entries.retain(|(n, _)| !mine.iter().any(|(q, _)| q.eq_ignore_ascii_case(n)));
            entries.extend(mine);
        }
        Ok(Quires { entries, shadowed })
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

    /// What is wrong with the registry itself: directories that are not there,
    /// and names the project took over from the checkout. Checked once, up
    /// front, because a registry nobody validates is a registry that rots.
    pub fn registry_complaints(&self) -> Vec<Complaint> {
        let mut out = self.shadowed.clone();
        out.extend(
            self.entries
                .iter()
                .filter(|(_, d)| !d.is_dir())
                .map(|(q, d)| Complaint::DeadQuireDir { quire: q.clone(), dir: d.clone() }),
        );
        out
    }
}

/// The file holding the `$QuireDirs` table, and its text.
///
/// **THE GENERATED REGISTRY, read where it is generated.** Since Update 62 the
/// quire map is written in Codex (`codex/build/quiremapScript.codex`) and
/// generated to `build/host/windows/quire-map.ps1`. `build/quire-map.ps1` is
/// kept upstream only as a shim for the many scripts that dot-source that
/// path; nothing here dot-sources anything, so this reads the generated file
/// and does not follow the shim. A checkout from before U62 has no such file
/// and is refused by name.
fn quire_registry(codex: &Path) -> Result<(PathBuf, String), String> {
    let map = codex.join("build").join("host").join("windows").join("quire-map.ps1");
    let text = std::fs::read_to_string(&map)
        .map_err(|e| format!("cannot read the quire registry at {}: {e}", map.display()))?;
    Ok((map, text))
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
    // A quire can also be added after the table, one indexed assignment per
    // line: U62 registers `$QuireDirs['Accp'] = 'apps\\accp'` that way.
    for line in text.lines() {
        let line = line.split('#').next().unwrap_or("").trim();
        let Some(rest) = line.strip_prefix("$QuireDirs['") else { continue };
        let Some(close) = rest.find('\'') else { continue };
        let key = &rest[..close];
        let tail = &rest[close + 1..];
        let Some(eq) = tail.find('=') else { continue };
        let after_eq = &tail[eq + 1..];
        let Some(vopen) = after_eq.find('\'') else { continue };
        let vrest = &after_eq[vopen + 1..];
        let Some(vclose) = vrest.find('\'') else { continue };
        out.push((key.to_string(), vrest[..vclose].replace('\\', "/")));
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

/// Where a program's cited chapters come from.
pub struct Project {
    /// The checkout the cites resolve against, if the program names one.
    pub checkout: Option<PathBuf>,
    /// The project's own quire file, the nearest `quires.tsv` above the program.
    pub quires: Option<PathBuf>,
}

/// The checkout and the quire file for the program at `path`.
///
/// **THE PROGRAM NAMES ITS CHECKOUT; NOTHING ELSE IS ASKED.** A file inside a
/// Cobblestone checkout resolves against that checkout, found by walking up to
/// the directory holding the compiler's driver. A project outside one says which
/// checkout it means with a `checkout <path>` line in its `quires.tsv`. The two
/// may not disagree. The environment is never read: a variable exported for
/// another tree once resolved a unit against it without a word.
pub fn project_of(path: &Path) -> Result<Project, String> {
    let file = path.canonicalize().map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    let (mut tree, mut quires) = (None, None);
    let mut d = file.parent().map(Path::to_path_buf);
    while let Some(dir) = d {
        if tree.is_none() && dir.join(MARKER).is_file() {
            tree = Some(dir.clone());
        }
        if quires.is_none() && dir.join("quires.tsv").is_file() {
            quires = Some(dir.join("quires.tsv"));
        }
        d = dir.parent().map(Path::to_path_buf);
    }
    let named = match &quires {
        Some(q) => checkout_line(q)?,
        None => None,
    };
    let checkout = match (tree, named) {
        (Some(t), Some(n)) if t != n => {
            return Err(format!(
                "{} lives in the checkout {}, and {} names {}",
                path.display(),
                t.display(),
                quires.as_deref().unwrap_or(Path::new("quires.tsv")).display(),
                n.display()
            ))
        }
        (Some(t), _) => Some(t),
        (None, n) => n,
    };
    Ok(Project { checkout, quires })
}

/// The `checkout <path>` line of a quire file, if it has one. The path is
/// relative to the file, or starts with `~/`.
fn checkout_line(file: &Path) -> Result<Option<PathBuf>, String> {
    let text = std::fs::read_to_string(file).map_err(|e| format!("cannot read {}: {e}", file.display()))?;
    let base = file.parent().unwrap_or(Path::new("."));
    let mut found = None;
    for (n, line) in text.lines().enumerate() {
        let words: Vec<&str> = line.split('#').next().unwrap_or("").split_whitespace().collect();
        let where_ = || format!("{}:{}", file.display(), n + 1);
        match words.as_slice() {
            ["checkout", p] => {
                if found.is_some() {
                    return Err(format!("{}: a second `checkout` line", where_()));
                }
                let raw = match p.strip_prefix("~/") {
                    Some(rest) => PathBuf::from(
                        std::env::var_os("HOME").ok_or_else(|| format!("{}: `~` with no HOME", where_()))?,
                    )
                    .join(rest),
                    None => base.join(p),
                };
                let dir = raw.canonicalize().map_err(|e| format!("{}: checkout {}: {e}", where_(), raw.display()))?;
                if !dir.join(MARKER).is_file() {
                    return Err(format!("{}: {} is not a Cobblestone checkout (no {MARKER})", where_(), dir.display()));
                }
                found = Some(dir);
            }
            ["checkout", ..] => return Err(format!("{}: want `checkout <path>`", where_())),
            _ => {}
        }
    }
    Ok(found)
}

/// Whether a cited chapter is already in the unit.
enum Presence {
    Present,
    Missing,
    /// Not under the cite's quire, and under several other headers, which are
    /// named.
    Ambiguous(Vec<String>),
}

/// The chapter headers a source carries, and the chapters added to it so far.
///
/// **A CITE FINDS ITS CHAPTER THE WAY THE COMPILER'S SCOPER DOES**
/// (`find-slug-for-cite-name`, ChapterScoper.codex): `Chapter: Quire--Name`
/// first; failing that, the one chapter of that name under any prefix or none;
/// and no answer when there are several. A prefix is not always the quire.
/// Upstream's plug bundler writes `Parsmi--Build Settings` for the chapter the
/// compiler cites as `Codex chapter Build Settings`, and a unit written by an
/// older bundler carries a plain `Chapter: ListUtils`.
///
/// Headers compare by `cite-key`, spaces removed and case ignored: a cite may
/// name the file, `ByteHelpers`, where the header says `Byte Helpers`.
struct Carried {
    /// (key, header as written)
    headers: Vec<(String, String)>,
}

impl Carried {
    fn read(src: &[u8]) -> Carried {
        let text = String::from_utf8_lossy(src);
        let headers = text
            .lines()
            .filter_map(|line| line.strip_prefix("Chapter:"))
            .map(|rest| {
                let header = rest.trim().trim_end_matches('\r').to_string();
                (cite_key(&header), header)
            })
            .collect();
        Carried { headers }
    }

    fn of(&self, quire: &str, name: &str) -> Presence {
        let exact = cite_key(&format!("{quire}--{name}"));
        if self.headers.iter().any(|(k, _)| *k == exact) {
            return Presence::Present;
        }
        let bare = cite_key(name);
        let suffix = format!("--{bare}");
        let mut keys: Vec<&str> = Vec::new();
        let mut named = Vec::new();
        for (k, header) in &self.headers {
            if (*k == bare || k.ends_with(&suffix)) && !keys.contains(&k.as_str()) {
                keys.push(k);
                named.push(header.clone());
            }
        }
        match named.len() {
            0 => Presence::Missing,
            1 => Presence::Present,
            _ => Presence::Ambiguous(named),
        }
    }

    fn add(&mut self, quire: &str, name: &str) {
        let header = format!("{quire}--{name}");
        self.headers.push((cite_key(&header), header));
    }
}

/// `cite-key`: spaces removed, ASCII letters lowered.
fn cite_key(s: &str) -> String {
    s.chars().filter(|c| *c != ' ').map(|c| c.to_ascii_lowercase()).collect()
}

fn ambiguous(who: &str, quire: &str, chapter: &str, headers: &[String]) -> String {
    let named: Vec<String> = headers.iter().map(|h| format!("`Chapter: {h}`")).collect();
    format!(
        "{who} cites {quire} chapter {chapter}; the unit carries no `Chapter: {quire}--{chapter}` and {} chapters \
         of that name ({}), so the cite does not say which",
        named.len(),
        named.join(", ")
    )
}

/// What `src` cites, and ListUtils and Tuple, that it does not carry yet.
fn missing(who: &str, src: &[u8], carried: &Carried) -> Result<Vec<(String, String)>, String> {
    let mut out: Vec<(String, String)> = Vec::new();
    let wanted = IMPLICIT.iter().map(|(q, c)| (q.to_string(), c.to_string())).chain(cites_of(src));
    for (quire, chapter) in wanted {
        match carried.of(&quire, &chapter) {
            Presence::Present => {}
            Presence::Ambiguous(headers) => return Err(ambiguous(who, &quire, &chapter, &headers)),
            Presence::Missing => {
                if !out.iter().any(|(q, c)| q.eq_ignore_ascii_case(&quire) && c.eq_ignore_ascii_case(&chapter)) {
                    out.push((quire, chapter));
                }
            }
        }
    }
    Ok(out)
}

pub struct Bundle {
    pub text: String,
    pub complaints: Vec<Complaint>,
    /// How many chapters resolving added. Zero means the source was a unit.
    pub added: usize,
}

/// Assemble `root` and everything it cites, dependencies first, each once.
pub fn resolve(root: &Path) -> Result<Bundle, String> {
    let src = std::fs::read(root).map_err(|e| format!("cannot read {}: {e}", root.display()))?;
    let who = name_of(root);
    let carried = Carried::read(&src);
    let wanted = missing(&who, &src, &carried)?;
    if wanted.is_empty() {
        return Ok(Bundle { text: String::from_utf8_lossy(&src).into_owned(), complaints: Vec::new(), added: 0 });
    }
    let project = project_of(root)?;
    let Some(checkout) = project.checkout else {
        let names: Vec<String> = wanted.iter().map(|(q, c)| format!("{q} chapter {c}")).collect();
        return Err(format!(
            "{} cites what it does not carry ({}) and names no checkout: it is not inside one, and no quires.tsv \
             above it has a `checkout` line",
            root.display(),
            names.join(", ")
        ));
    };
    let quires = Quires::read(&checkout, project.quires.as_deref())?;
    let mut w = Walk { quires: &quires, carried, seen: BTreeSet::new(), complaints: quires.registry_complaints(), parts: Vec::new() };
    w.walk(&who, &wanted)?;
    let added = w.parts.len();
    w.parts.push(tidy(&String::from_utf8_lossy(&src)));
    Ok(Bundle { text: w.parts.join("\n"), complaints: w.complaints, added })
}

/// Read a program as a unit: resolved if it is a root, as it is if it is
/// already whole.
///
/// **RESOLVING IS A COMPILER PHASE, NOT ANOTHER TOOL'S JOB**, so every tool
/// that reads a program reads it through here. A unit short a chapter it cites
/// is refused rather than handed on, and so is a unit carrying a carriage
/// return, which cannot compile.
pub fn load(path: &Path) -> Result<Vec<u8>, String> {
    let src = std::fs::read(path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    if missing(&name_of(path), &src, &Carried::read(&src))?.is_empty() {
        return Ok(src);
    }
    let b = resolve(path)?;
    let broken: Vec<String> = b.complaints.iter().filter(|c| c.is_broken()).map(|c| c.to_string()).collect();
    if !broken.is_empty() {
        return Err(broken.join("; "));
    }
    if b.text.contains('\r') {
        return Err(format!("{}: the unit carries a carriage return and cannot be compiled", path.display()));
    }
    Ok(b.text.into_bytes())
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
/// all -- has already removed. Trimming trailing blank lines is a question
/// about blank lines, and the answer should not depend on which bytes spell one.
fn tidy(text: &str) -> String {
    format!("{}\n", text.trim_end_matches(['\n', '\r']))
}

/// A cited chapter's text with its header written under its quire.
fn under_quire(text: &str, quire: &str) -> String {
    let mut out = String::with_capacity(text.len() + quire.len() + 2);
    let mut renamed = false;
    for line in text.split_inclusive('\n') {
        match line.strip_prefix("Chapter:") {
            Some(rest) if !renamed => {
                let (name, end) = match rest.find(['\r', '\n']) {
                    Some(i) => (&rest[..i], &rest[i..]),
                    None => (rest, ""),
                };
                out.push_str(&format!("Chapter: {quire}--{}{end}", name.trim()));
                renamed = true;
            }
            _ => out.push_str(line),
        }
    }
    out
}

/// The header a chapter file declares, or the cited name if it declares none.
fn header_of(text: &str, cited: &str) -> String {
    text.lines()
        .find_map(|l| l.strip_prefix("Chapter:"))
        .map(|r| r.trim().trim_end_matches('\r').to_string())
        .unwrap_or_else(|| cited.to_string())
}

struct Walk<'a> {
    quires: &'a Quires,
    carried: Carried,
    seen: BTreeSet<PathBuf>,
    complaints: Vec<Complaint>,
    parts: Vec<String>,
}

impl Walk<'_> {
    fn walk(&mut self, who: &str, cites: &[(String, String)]) -> Result<(), String> {
        for (quire, chapter) in cites {
            match self.carried.of(quire, chapter) {
                Presence::Present => continue,
                Presence::Ambiguous(headers) => return Err(ambiguous(who, quire, chapter, &headers)),
                Presence::Missing => {}
            }
            let Some((dir, registered)) = self.quires.dir(quire) else {
                self.complaints.push(Complaint::UnregisteredQuire {
                    who: who.to_string(),
                    quire: quire.clone(),
                    chapter: chapter.clone(),
                });
                continue;
            };
            if registered != quire {
                self.complaints.push(Complaint::QuireCase {
                    who: who.to_string(),
                    cited: quire.clone(),
                    registered: registered.to_string(),
                });
            }
            let dep = dir.join(format!("{chapter}.codex"));
            if !dep.is_file() {
                self.complaints.push(Complaint::NoSuchChapter {
                    who: who.to_string(),
                    quire: quire.clone(),
                    chapter: chapter.clone(),
                    looked: dep,
                });
                continue;
            }
            if !self.seen.insert(dep.clone()) {
                continue;
            }
            let src = std::fs::read(&dep).map_err(|e| format!("cannot read {}: {e}", dep.display()))?;
            if src.contains(&b'\r') {
                self.complaints.push(Complaint::CarriageReturns {
                    chapter: chapter.clone(),
                    path: dep.clone(),
                });
            }
            let text = String::from_utf8_lossy(&src).into_owned();
            // Carried before its own cites are walked, so a cycle back to it
            // finds it present.
            self.carried.add(quire, chapter);
            let header = header_of(&text, chapter);
            if !header.eq_ignore_ascii_case(chapter) {
                self.carried.add(quire, &header);
            }
            let sub = cites_of(&src);
            self.walk(&name_of(&dep), &sub)?;
            self.parts.push(tidy(&under_quire(&text, quire)));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fresh directory under the system temp dir, removed first if a failed
    /// run left one behind.
    fn scratch(tag: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("codexc-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    fn write(path: &Path, text: &str) {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }

    /// A checkout with the driver marker, a registry, and three small forewords.
    fn checkout(root: &Path) {
        write(&root.join(MARKER), "Chapter: Opening\n");
        write(
            &root.join("build/host/windows/quire-map.ps1"),
            "$QuireDirs = @{\n    'Foreword' = 'codex\\foreword\\core'; 'Parsmi' = 'codex\\parsmi'\n}\n",
        );
        for name in ["ListUtils", "Tuple", "Maybe"] {
            write(
                &root.join(format!("codex/foreword/core/{name}.codex")),
                &format!("Chapter: {name}\n\nSection: S\n  x-{} : Integer = 1\n", name.to_ascii_lowercase()),
            );
        }
    }

    fn headers(text: &str) -> Vec<&str> {
        text.lines().filter_map(|l| l.strip_prefix("Chapter: ")).collect()
    }

    /// U62 registers `Accp` after the table, by indexed assignment.
    #[test]
    fn quire_map_reads_an_indexed_assignment_after_the_table() {
        let t = "$QuireDirs = @{\n    'Foreword' = 'codex\\foreword\\core'\n}\n$QuireDirs['Accp'] = 'apps\\accp'\n";
        assert_eq!(
            parse_quire_map(t),
            vec![
                ("Foreword".into(), "codex/foreword/core".into()),
                ("Accp".into(), "apps/accp".into()),
            ]
        );
    }

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

    /// Update 55 took safari's `port/` into the checkout under the name the
    /// project already used, and appending the local entries meant every safari
    /// cite resolved to upstream's snapshot instead.
    #[test]
    fn the_projects_own_quire_file_beats_the_checkouts_and_says_so() {
        let dir = scratch("quires");
        write(
            &dir.join("build/host/windows/quire-map.ps1"),
            "$QuireDirs = @{\n    'Safari' = 'apps\\safari\\port'\n    'OS' = 'codex\\os'\n}",
        );
        let local = dir.join("quires.tsv");
        // Spelled in a different case on purpose: shadowing removes the loser
        // rather than outranking it, so no spelling can reach the checkout's.
        write(&local, "safari port\n");

        let q = Quires::read(&dir, Some(&local)).unwrap();
        assert_eq!(q.dir("Safari").unwrap().0, dir.join("port"));
        assert_eq!(q.dir("safari").unwrap().0, dir.join("port"));
        assert_eq!(q.dir("OS").unwrap().0, dir.join("codex/os"));
        assert!(q
            .registry_complaints()
            .iter()
            .any(|c| matches!(c, Complaint::ShadowedQuire { quire, .. } if quire == "Safari")));
        std::fs::remove_dir_all(&dir).unwrap();
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
    fn a_cite_finds_its_quire_first_then_the_one_chapter_of_its_name() {
        let c = Carried::read(
            b"Chapter: Foreword--ListUtils\nChapter: Main\nChapter: Parsmi--Build Settings\n\
              Chapter: Emit--Console\nChapter: Kernel--Console\n",
        );
        assert!(matches!(c.of("Foreword", "ListUtils"), Presence::Present));
        assert!(matches!(c.of("foreword", "listutils"), Presence::Present));
        assert!(matches!(c.of("Parsmi", "ListUtils"), Presence::Present));
        assert!(matches!(c.of("Foreword", "Main"), Presence::Present));
        assert!(matches!(c.of("Codex", "Build Settings"), Presence::Present));
        assert!(matches!(c.of("Codex", "BuildSettings"), Presence::Present));
        assert!(matches!(c.of("Emit", "Console"), Presence::Present));
        assert!(matches!(c.of("OS", "Console"), Presence::Ambiguous(h) if h == ["Emit--Console", "Kernel--Console"]));
        assert!(matches!(c.of("Foreword", "Maybe"), Presence::Missing));
    }

    #[test]
    fn the_checkout_is_the_tree_the_program_lives_in() {
        let dir = scratch("tree");
        checkout(&dir);
        let prog = dir.join("codex/test/probe.codex");
        write(&prog, "Chapter: Probe\n");
        assert_eq!(project_of(&prog).unwrap().checkout, Some(dir.canonicalize().unwrap()));
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_project_outside_a_checkout_names_it_in_its_quire_file() {
        let dir = scratch("named");
        checkout(&dir.join("co"));
        write(&dir.join("proj/quires.tsv"), "# ours\nSafari port\ncheckout ../co\n");
        let prog = dir.join("proj/spec/p.codex");
        write(&prog, "Chapter: P\n");
        let p = project_of(&prog).unwrap();
        assert_eq!(p.checkout, Some(dir.join("co").canonicalize().unwrap()));
        let q = Quires::read(p.checkout.as_deref().unwrap(), p.quires.as_deref()).unwrap();
        assert!(q.dir("Safari").is_some());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_quire_file_that_names_another_checkout_than_the_tree_is_refused() {
        let dir = scratch("disagree");
        checkout(&dir.join("a"));
        checkout(&dir.join("b"));
        write(&dir.join("a/codex/test/quires.tsv"), "checkout ../../../b\n");
        let prog = dir.join("a/codex/test/p.codex");
        write(&prog, "Chapter: P\n");
        let e = project_of(&prog).err().unwrap();
        assert!(e.contains("lives in the checkout"), "{e}");
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn cited_chapters_go_under_their_quire_and_the_program_keeps_its_header() {
        let dir = scratch("under");
        checkout(&dir);
        let prog = dir.join("codex/test/root.codex");
        write(&prog, "Chapter: Root\n  cites Foreword chapter Maybe\n\nSection: S\n  r : Integer = 2\n");
        let b = resolve(&prog).unwrap();
        assert_eq!(headers(&b.text), vec!["Foreword--ListUtils", "Foreword--Tuple", "Foreword--Maybe", "Root"]);
        assert_eq!(b.added, 3);
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn resolving_a_unit_changes_nothing_and_needs_no_checkout() {
        let dir = scratch("unit");
        checkout(&dir.join("co"));
        let prog = dir.join("co/codex/test/root.codex");
        write(&prog, "Chapter: Root\n  cites Foreword chapter Maybe\n\nSection: S\n  r : Integer = 2\n");
        let unit = dir.join("elsewhere/root.codex");
        write(&unit, &resolve(&prog).unwrap().text);
        let before = std::fs::read(&unit).unwrap();
        assert_eq!(load(&unit).unwrap(), before);
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_unit_with_plain_headers_is_whole() {
        let dir = scratch("plain");
        let unit = dir.join("u.codex");
        write(&unit, "Chapter: ListUtils\n\nChapter: Tuple\n\nChapter: Main\n  cites Foreword chapter ListUtils\n");
        assert_eq!(load(&unit).unwrap(), std::fs::read(&unit).unwrap());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_chapter_under_another_prefix_answers_the_cite() {
        let dir = scratch("prefix");
        checkout(&dir);
        let prog = dir.join("codex/test/root.codex");
        write(
            &prog,
            "Chapter: Parsmi--Maybe\n\nChapter: Root\n  cites Foreword chapter Maybe\n\nSection: S\n  r : Integer = 2\n",
        );
        let b = resolve(&prog).unwrap();
        assert_eq!(headers(&b.text), vec!["Foreword--ListUtils", "Foreword--Tuple", "Parsmi--Maybe", "Root"]);
        assert_eq!(b.added, 2);
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn two_chapters_of_the_cited_name_under_other_prefixes_are_refused() {
        let dir = scratch("ambiguous");
        let unit = dir.join("u.codex");
        write(&unit, "Chapter: Core--Maybe\n\nChapter: Emit--Maybe\n\nChapter: Root\n  cites Foreword chapter Maybe\n");
        let e = load(&unit).err().unwrap();
        assert!(e.contains("`Chapter: Core--Maybe`") && e.contains("`Chapter: Emit--Maybe`"), "{e}");
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_unit_short_a_chapter_with_no_checkout_is_refused() {
        let dir = scratch("nocheckout");
        let unit = dir.join("u.codex");
        write(
            &unit,
            "Chapter: Foreword--ListUtils\n\nChapter: Foreword--Tuple\n\nChapter: Main\n  cites Foreword chapter Maybe\n",
        );
        let e = load(&unit).err().unwrap();
        assert!(e.contains("names no checkout") && e.contains("Foreword chapter Maybe"), "{e}");
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
