//! IR definition BODIES -- the `(defs ...)` the preamble stops short of.
//!
//! `preamble.rs` emits everything above `(defs` and is byte-identical on all
//! 1,012 golds, because that part is fixed by syntax alone. Below it, nearly
//! every node carries a TYPE:
//!
//! ```text
//! (def "opening" "NegIntParse" (params) int-default
//!   (apply (name "text-to-integer" (fn text int-default)) (text-lit "-5") int-default) 0 0)
//! ```
//!
//! so reaching a body means knowing types, not just shapes. This walks the
//! desugared AST and emits what it can TYPE WITH CERTAINTY, from three sources
//! and no inference: a definition's own declared type, the builtin table's
//! declared types, and the literals.
//!
//! ## It refuses rather than guesses, and that is the whole design
//!
//! Every function here returns `None` on anything it cannot type exactly. A
//! guessed type is not a partial answer -- it is a wrong answer that reads
//! exactly like a right one until someone diffs 900 bytes of nested s-
//! expressions. The gate is byte-identity against a gold, so a near miss is
//! worth nothing and a confident near miss is worth less than nothing.
//!
//! What it therefore cannot do yet, and must not pretend to: inferred types
//! (no annotation), local bindings whose type comes from their value, records,
//! lists, matches, effects. Those need the checker. `emit_defs` returns None
//! for the whole chapter if any definition in it is out of reach, because a
//! chapter emitted with half its defs is not comparable to anything.

use crate::ast::{Chapter, Expr, LiteralKind, TypeExpr};
use crate::builtins::BUILTIN_IR_TYPES;
use std::collections::BTreeMap;

/// A source type name as the IR spells it. Only the primitives: anything else
/// is a name this cannot resolve without the checker.
fn atom(n: &str) -> Option<&'static str> {
    Some(match n {
        "Integer" => "int-default",
        "Text" => "text",
        "Boolean" => "boolean",
        "Char" => "char",
        "Nothing" => "nothing",
        "Real" => "real",
        _ => return None,
    })
}

/// A declared type, in the IR's spelling. `A -> B` is `(fn A B)`; the arrow is
/// right-associative and stays curried, which is what the golds show:
/// `char-at` is `(fn text (fn int-default char))`.
pub fn render_type(t: &TypeExpr) -> Option<String> {
    match t {
        TypeExpr::Named(n, _) => atom(n).map(str::to_string),
        TypeExpr::Fun(a, b, _) => {
            Some(format!("(fn {} {})", render_type(a)?, render_type(b)?))
        }
        _ => None,
    }
}

/// Split `(fn A B)` into its argument and result. Balanced, not regex: `A` is
/// itself a `(fn ...)` whenever the function takes a function.
fn split_fn(ty: &str) -> Option<(&str, &str)> {
    let inner = ty.strip_prefix("(fn ")?.strip_suffix(')')?;
    let mut depth = 0usize;
    for (i, c) in inner.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth = depth.checked_sub(1)?,
            ' ' if depth == 0 => return Some((&inner[..i], &inner[i + 1..])),
            _ => {}
        }
    }
    None
}

/// Names in scope, with the type each one carries at a reference site.
pub struct Env {
    types: BTreeMap<String, String>,
}

impl Env {
    /// The builtins first, then this chapter's own declared types on top --
    /// a chapter that defines `max` shadows the builtin, and the golds show
    /// both spellings for that name.
    pub fn new(ch: &Chapter) -> Env {
        let mut types: BTreeMap<String, String> =
            BUILTIN_IR_TYPES.iter().map(|(n, t)| (n.to_string(), t.to_string())).collect();
        for d in &ch.defs {
            if let Some(dt) = d.declared_type.first().and_then(render_type) {
                types.insert(d.name.clone(), dt);
            }
        }
        Env { types }
    }

    fn get(&self, n: &str) -> Option<&str> {
        self.types.get(n).map(String::as_str)
    }
}

/// One expression, as `(ir-text, its-type)`. `None` means refused.
fn expr(e: &Expr, env: &Env) -> Option<(String, String)> {
    match e {
        // Literals carry no type of their own in the IR -- `(int-lit 1)`, not
        // `(int-lit 1 int-default)` -- but their type is needed by whatever
        // encloses them, so it is returned alongside.
        Expr::Lit(v, LiteralKind::IntLit, _) => {
            Some((format!("(int-lit {v})"), "int-default".into()))
        }
        Expr::Lit(v, LiteralKind::TextLit, _) => {
            Some((format!("(text-lit {v})"), "text".into()))
        }
        Expr::Lit(v, LiteralKind::BoolLit, _) => {
            Some((format!("(bool-lit {v})"), "boolean".into()))
        }
        Expr::NameRef(n, _) => {
            let t = env.get(n)?.to_string();
            Some((format!("(name {:?} {})", n, t), t))
        }
        Expr::Apply(f, a, _) => {
            let (ft, fty) = expr(f, env)?;
            let (at, _aty) = expr(a, env)?;
            // The result of applying one argument is the arrow's right half.
            // A non-arrow here is an over-application, which is a real error
            // and not something to paper over with the same type back.
            let (_arg, res) = split_fn(&fty)?;
            Some((format!("(apply {ft} {at} {res})"), res.to_string()))
        }
        _ => None,
    }
}

/// The definition lines for a chapter, or None if ANY definition in it is
/// out of reach -- a chapter with half its defs emitted compares to nothing.
/// The driver's own root set, `opening.codex:1373`:
///
/// ```text
/// ir-emit-roots = ["opening", "vb-capacity-auto", "vb-read-auto",
///                  "vb-write-auto", "fat16-servicer-read", "fat16-servicer-write"]
/// ```
///
/// NOT just `opening`. The block-device and FAT16 servicers are entered by the
/// runtime rather than called, so a call-graph walk cannot find them -- which
/// is exactly what `hal-device-declared` showed: its gold keeps `vb-off-magic`
/// from VirtioBlk, and rooting at `opening` alone dropped it.
pub const IR_EMIT_ROOTS: [&str; 6] = [
    "opening",
    "vb-capacity-auto",
    "vb-read-auto",
    "vb-write-auto",
    "fat16-servicer-read",
    "fat16-servicer-write",
];

pub fn emit_defs(ch: &Chapter) -> Option<String> {
    emit_defs_from(ch, &IR_EMIT_ROOTS)
}

/// Names reachable from the roots, following NameRefs through def bodies.
///
/// A gold's `(defs` is PRUNED: a resolved unit carries every cited chapter, and
/// `neg-int-parse` cites Foreword ListUtils, yet its gold holds one definition.
/// Emitting the unit's whole def list would be a different document from the
/// gold no matter how correct each line was -- and it is also why a chapter that
/// looks impossible to type usually is not: the untypable definitions are
/// library code nothing in the program reaches.
fn reachable(ch: &Chapter, roots: &[&str]) -> std::collections::BTreeSet<String> {
    let by_name: BTreeMap<&str, &crate::ast::Def> =
        ch.defs.iter().map(|d| (d.name.as_str(), d)).collect();
    let mut seen = std::collections::BTreeSet::new();
    let mut stack: Vec<String> =
        roots.iter().filter(|r| by_name.contains_key(**r)).map(|r| r.to_string()).collect();
    while let Some(n) = stack.pop() {
        if !seen.insert(n.clone()) {
            continue;
        }
        if let Some(d) = by_name.get(n.as_str()) {
            d.body.walk(&mut |x| {
                if let Expr::NameRef(m, _) = x {
                    if by_name.contains_key(m.as_str()) && !seen.contains(m) {
                        stack.push(m.clone());
                    }
                }
            });
        }
    }
    seen
}

pub fn emit_defs_from(ch: &Chapter, roots: &[&str]) -> Option<String> {
    let keep = reachable(ch, roots);
    if keep.is_empty() {
        return None;
    }
    let env = Env::new(ch);
    // The OPENER is the preamble's last line, so this contributes only the
    // definitions. `preamble::emit` ends at `  (defs` because that is where the
    // syntax-only part of a gold stops.
    let mut out = String::new();
    for d in ch.defs.iter().filter(|d| keep.contains(&d.name)) {
        let declared = d.declared_type.first().and_then(render_type)?;
        // Parameter types come from walking the declared arrow spine, which is
        // the only place they are written down.
        let mut rest: &str = &declared;
        let mut params = String::new();
        for p in &d.params {
            let (arg, res) = split_fn(rest)?;
            params.push_str(&format!(" (param {:?} {})", p.name, arg));
            rest = res;
        }
        let (body, _bty) = expr(&d.body, &env)?;
        out.push_str(&format!(
            "\n  (def {:?} {:?} (params{}) {} {} 0 0)",
            d.name, d.chapter_slug, params, declared, body
        ));
    }
    Some(out)
}
