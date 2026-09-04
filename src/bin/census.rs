//! What is DONE with a builtin's answer, across the whole checkout.
//!
//!     census <builtin> <dir>...     every call site, grouped by consumer
//!
//! `xref who` answers "which chapters read this name". That is the wrong
//! question for a builtin whose type is `forall a. a -> Integer`: every caller
//! reads it, and the reads are not alike. `address-of` is compared against zero
//! in one place to mean ABSENT, ordered against a floor in another to mean
//! HEAP-RESIDENT, and handed to `peek-qword` in a third to mean HERE IS A
//! STRUCT. Those are three different questions wearing one primitive, and the
//! type cannot tell them apart -- so neither can a checker, and neither can a
//! plug deciding what to emit.
//!
//! Grep cannot do this. The consumer of a call is its PARENT expression, which
//! is a tree fact and not a line fact, and a line-oriented search reports the
//! call without reporting what the answer is for. This walks the desugared AST
//! and classifies each call by the node that consumes it.
//!
//! Generated `*-subject.codex` bundles are skipped: they are copies of chapters
//! already in the tree, and counting both reports every site twice.
use codexc::ast::{ActStmt, BinaryOp, Chapter, Expr, LetBind, MatchArm};
use codexc::desugar::Desugar;
use codexc::parser;
use codexc::symbol::SymTab;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// How the value of the expression being visited is used by its parent.
#[derive(Clone)]
enum Consumer {
    /// Compared with `op` against something; the flag says the other side is
    /// the literal 0, which is what turns a comparison into a null test.
    Compared(BinaryOp, bool),
    /// An argument of a call to this name.
    ArgOf(String),
    /// Anything else -- bound, returned, printed, matched.
    Other,
}

struct Site {
    bucket: String,
    file: String,
    line: u32,
    arg: String,
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 2 {
        eprintln!("usage: census <builtin> <dir>...");
        return ExitCode::from(2);
    }
    let target = &args[0];

    let mut files = Vec::new();
    for d in &args[1..] {
        collect(Path::new(d), &mut files);
    }
    files.retain(|p| !p.to_string_lossy().ends_with("-subject.codex"));
    files.sort();
    if files.is_empty() {
        eprintln!("no .codex files under {}", args[1..].join(" "));
        return ExitCode::from(2);
    }

    let mut sites: Vec<Site> = Vec::new();
    for p in &files {
        let Ok(src) = std::fs::read(p) else { continue };
        let parsed = parser::parse(&src);
        let mut dg = Desugar::new(&src);
        let ch = dg.chapter(&parsed.tree);
        let file = short(p);
        for d in &ch.defs {
            walk(&ch, target, &d.body, &Consumer::Other, &file, &mut sites);
        }
    }

    let mut by_bucket: BTreeMap<&str, Vec<&Site>> = BTreeMap::new();
    for s in &sites {
        by_bucket.entry(s.bucket.as_str()).or_default().push(s);
    }

    println!("census of `{target}` over {} chapters", files.len());
    println!("{} call sites, {} distinct consumers\n", sites.len(), by_bucket.len());
    for (bucket, ss) in &by_bucket {
        println!("{:>4}  {bucket}", ss.len());
    }
    println!();
    for (bucket, ss) in &by_bucket {
        println!("== {bucket} ({})", ss.len());
        for s in ss {
            println!("   {}:{}   address-of {}", s.file, s.line, s.arg);
        }
        println!();
    }
    ExitCode::SUCCESS
}

/// The name at the head of an application spine: `f a b` is `Apply(Apply(f,a),b)`,
/// and the callee is the leftmost leaf.
fn head_name(syms: &SymTab, e: &Expr) -> Option<String> {
    match e {
        Expr::NameRef(n, _) => Some(syms.text(*n).to_string()),
        Expr::Apply(f, _, _) => head_name(syms, f),
        _ => None,
    }
}

fn is_zero(e: &Expr) -> bool {
    matches!(e, Expr::Lit(t, _, _) if t == "0")
}

fn describe(syms: &SymTab, e: &Expr) -> String {
    match e {
        Expr::NameRef(n, _) => syms.text(*n).to_string(),
        Expr::Lit(t, _, _) => t.clone(),
        Expr::FieldAccess(_, n, _) => format!("_.{}", syms.text(*n)),
        Expr::Apply(..) => head_name(syms, e).map_or("(call)".into(), |h| format!("({h} ...)")),
        _ => "(expr)".into(),
    }
}

fn bucket_of(c: &Consumer) -> String {
    match c {
        Consumer::Compared(BinaryOp::OpEq, true) => "ABSENCE       == 0".into(),
        Consumer::Compared(BinaryOp::OpNotEq, true) => "ABSENCE       /= 0".into(),
        Consumer::Compared(BinaryOp::OpEq | BinaryOp::OpNotEq, false) => {
            "IDENTITY      compared to another address".into()
        }
        Consumer::Compared(
            BinaryOp::OpLt | BinaryOp::OpGt | BinaryOp::OpLtEq | BinaryOp::OpGtEq,
            _,
        ) => "REGION        ordered against a floor".into(),
        Consumer::Compared(..) => "ARITHMETIC    combined with another value".into(),
        Consumer::ArgOf(n) if n.starts_with("peek-") => {
            format!("STRUCT READ   argument of {n}")
        }
        Consumer::ArgOf(n) => format!("PASSED        argument of {n}"),
        Consumer::Other => "UNCONSUMED    bound, returned or printed".into(),
    }
}

/// Visit `e`, knowing how its parent uses it. A call to the target is recorded
/// against that consumer; every child is then visited with the consumer THIS
/// node imposes on it.
fn walk(ch: &Chapter, target: &str, e: &Expr, c: &Consumer, file: &str, out: &mut Vec<Site>) {
    if let Expr::Apply(f, a, sp) = e {
        if matches!(&**f, Expr::NameRef(n, _) if ch.syms.text(*n) == target) {
            out.push(Site {
                bucket: bucket_of(c),
                file: file.to_string(),
                line: sp.line,
                arg: describe(&ch.syms, a),
            });
        }
    }
    let kids = |e: &Expr, c: &Consumer, out: &mut Vec<Site>| walk(ch, target, e, c, file, out);
    match e {
        Expr::Binary(l, op, r, _) => {
            kids(l, &Consumer::Compared(*op, is_zero(r)), out);
            kids(r, &Consumer::Compared(*op, is_zero(l)), out);
        }
        Expr::Apply(f, a, _) => {
            let callee = head_name(&ch.syms, f).unwrap_or_else(|| "(expr)".into());
            kids(f, &Consumer::Other, out);
            kids(a, &Consumer::ArgOf(callee), out);
        }
        Expr::Unary(x, _) | Expr::Lazy(x, _) | Expr::FieldAccess(x, _, _) => {
            kids(x, &Consumer::Other, out)
        }
        Expr::If(a, b, d, _) => {
            for x in [a, b, d] {
                kids(x, &Consumer::Other, out);
            }
        }
        Expr::Let(bs, body, _) => {
            for LetBind { value, .. } in bs {
                kids(value, &Consumer::Other, out);
            }
            kids(body, &Consumer::Other, out);
        }
        Expr::Lambda(_, body, _) => kids(body, &Consumer::Other, out),
        Expr::Match(s, arms, _) | Expr::Induction(s, arms, _) => {
            kids(s, &Consumer::Other, out);
            for MatchArm { body, .. } in arms {
                kids(body, &Consumer::Other, out);
            }
        }
        Expr::List(xs, _) => {
            for x in xs {
                kids(x, &Consumer::Other, out);
            }
        }
        Expr::Record(_, fs, _) => {
            for f in fs {
                kids(&f.value, &Consumer::Other, out);
            }
        }
        Expr::FieldAssign(o, _, v, _) => {
            kids(o, &Consumer::Other, out);
            kids(v, &Consumer::Other, out);
        }
        Expr::Act(ss, _) => act(ch, target, ss, file, out),
        // The three boxed forms. Rare, but a call inside a handler clause is a
        // call: skipping them silently would make the count look complete when
        // it was not.
        Expr::Handle(h) => {
            kids(&h.body, &Consumer::Other, out);
            for c in &h.clauses {
                kids(&c.body, &Consumer::Other, out);
            }
        }
        Expr::WithTimeout(w) => kids(&w.body, &Consumer::Other, out),
        Expr::Try(t) => {
            for ss in [&t.body, &t.fallback, &t.failure] {
                act(ch, target, ss, file, out);
            }
        }
        Expr::Lit(..) | Expr::NameRef(..) | Expr::Error(..) => {}
    }
}

fn act(ch: &Chapter, target: &str, ss: &[ActStmt], file: &str, out: &mut Vec<Site>) {
    for s in ss {
        match s {
            ActStmt::Bind(_, x, _) | ActStmt::Exec(x, _) => {
                walk(ch, target, x, &Consumer::Other, file, out)
            }
        }
    }
}

fn short(p: &Path) -> String {
    let parts: Vec<_> = p.components().collect();
    let keep = parts.len().saturating_sub(3);
    parts[keep..].iter().map(|c| c.as_os_str().to_string_lossy()).collect::<Vec<_>>().join("/")
}

fn collect(p: &Path, out: &mut Vec<PathBuf>) {
    if p.is_dir() {
        let Ok(rd) = std::fs::read_dir(p) else { return };
        for e in rd.flatten() {
            collect(&e.path(), out);
        }
    } else if p.extension().is_some_and(|e| e == "codex") {
        out.push(p.to_path_buf());
    }
}
