//! Which memory and device builtins a program's opening can reach, each with
//! one chain of calls from the opening to it.
//!
//!     reaches <unit.codex>...
//!
//! rocemit picks a unit's threaded state from every definition its chapters
//! hold, because it emits them whole: a chapter cited for one drawing function
//! brings its PCI scan along, and the unit threads the machine. This asks the
//! narrower question of the same IR, following names from `opening`: which of
//! those builtins the program can call at all. A name is followed wherever it
//! appears, so a function handed on as a value counts as reached.
//!
//! One line a unit, then one line a builtin it reaches:
//!
//!     <unit>  emits <Machine|Mem|->  reaches <machine|memory|nothing>
//!         <builtin>  opening > f > g
//!
//! The same road as rocemit up to the IR. Exit 2 when a unit does not lower.

use codexc::ir_chapter::{IrDef, IrExpr};
use codexc::parser;
use codexc::roc_emit::{MACHINE_OPS, MEMORY_OPS};
use codexc::symbol::Sym;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let paths: Vec<String> = std::env::args().skip(1).collect();
    if paths.is_empty() {
        eprintln!("usage: reaches <unit.codex>...");
        return ExitCode::from(2);
    }
    let mut code = ExitCode::SUCCESS;
    for p in &paths {
        let path = Path::new(p);
        let unit = path.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
        match reaches(path) {
            Ok(text) => print!("{unit}  {text}"),
            Err(why) => {
                println!("{unit}  does not lower: {}", why.lines().next().unwrap_or(""));
                code = ExitCode::from(2);
            }
        }
    }
    code
}

fn names_in(d: &IrDef) -> Vec<Sym> {
    let mut out = Vec::new();
    d.body.walk(&mut |x| {
        if let IrExpr::Name(n, _, _) = x {
            out.push(*n);
        }
    });
    out
}

fn reaches(path: &Path) -> Result<String, String> {
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
    let low = codexc::ir::lower_whole(&ch, &bindings, &st, &tds)?;
    let syms = &low.syms;
    let machine: BTreeSet<Sym> = MACHINE_OPS.iter().filter_map(|b| syms.find(b)).collect();
    let memory: BTreeSet<Sym> = MEMORY_OPS.iter().filter_map(|b| syms.find(b)).collect();
    let by_name: BTreeMap<Sym, &IrDef> = low.defs.iter().map(|d| (d.name, d)).collect();

    // What rocemit sees: every definition, and the `.vmargs` beside the unit.
    let (mut any_machine, mut any_memory) = (path.with_extension("vmargs").exists(), false);
    for d in &low.defs {
        for n in names_in(d) {
            any_machine |= machine.contains(&n);
            any_memory |= memory.contains(&n);
        }
    }
    let emits = if any_machine {
        "Machine"
    } else if any_memory {
        "Mem"
    } else {
        "-"
    };

    let Some(open) = syms.find("opening").filter(|o| by_name.contains_key(o)) else {
        return Ok(format!("emits {emits}  is a library\n"));
    };
    // Breadth first from the opening, so each chain is a shortest one.
    let mut parent: BTreeMap<Sym, Sym> = BTreeMap::new();
    let mut hit: BTreeMap<Sym, Sym> = BTreeMap::new();
    let mut queue = VecDeque::from([open]);
    while let Some(n) = queue.pop_front() {
        for m in names_in(by_name[&n]) {
            if machine.contains(&m) || memory.contains(&m) {
                hit.entry(m).or_insert(n);
            } else if m != open && by_name.contains_key(&m) && !parent.contains_key(&m) {
                parent.insert(m, n);
                queue.push_back(m);
            }
        }
    }
    let reached = if hit.keys().any(|b| machine.contains(b)) {
        "machine"
    } else if hit.is_empty() {
        "nothing"
    } else {
        "memory"
    };
    let mut out = format!("emits {emits}  reaches {reached}\n");
    for (b, at) in &hit {
        let mut chain = vec![syms.text(*at).to_string()];
        let mut cur = *at;
        while let Some(p) = parent.get(&cur) {
            chain.push(syms.text(*p).to_string());
            cur = *p;
        }
        chain.reverse();
        out.push_str(&format!("    {}  {}\n", syms.text(*b), chain.join(" > ")));
    }
    Ok(out)
}
