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
//! ## The golds are POST-PIPELINE, and that is a ceiling on this file
//!
//! A gold is not the raw lowered IR. It is that IR after
//! `fold-constants, inline-leaf-calls, inline-single-caller` -- the
//! `CDX4030 PIPELINE` line every compile log carries. `type-checker-test`
//! showed it: its gold's `opening` is `add-one (add-one 40)` and the
//! `apply-twice` it actually calls is GONE, inlined away as a single-caller
//! function.
//!
//! So units match here only where no pass fired on them. That is a real
//! oracle for those units and a hard ceiling for the rest: matching a gold
//! whose shape a pass changed needs the passes, not a better emitter. Do not
//! read a DIFFER on such a unit as an emission bug without checking whether a
//! pass explains it first.
//!
//! What it therefore cannot do yet, and must not pretend to: inferred types
//! (no annotation), local bindings whose type comes from their value, records,
//! lists, matches, effects. Those need the checker. `emit_defs` returns None
//! for the whole chapter if any definition in it is out of reach, because a
//! chapter emitted with half its defs is not comparable to anything.

use crate::ast::{BinaryOp, Chapter, Expr, LiteralKind, TypeExpr};
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
        // `List a` is `(list a)` and `Vector a` is `(vector a)`. The golds
        // carry 228,533 of the first, which makes it the cheapest thing in the
        // language to be unable to spell.
        TypeExpr::App(head, args, _) => match (&**head, args.as_slice()) {
            (TypeExpr::Named(n, _), [only]) if n == "List" => {
                Some(format!("(list {})", render_type(only)?))
            }
            (TypeExpr::Named(n, _), [only]) if n == "Vector" => {
                Some(format!("(vector {})", render_type(only)?))
            }
            _ => None,
        },
        _ => None,
    }
}

/// The shape of a type we cannot render, for the refusal histogram. A NAMED
/// type reports its name, because "which named types are missing" and "which
/// type constructors are missing" are different questions with different fixes.
pub fn type_kind(t: &TypeExpr) -> String {
    match t {
        TypeExpr::Named(n, _) => format!("Named {n}"),
        TypeExpr::Fun(a, b, _) => {
            if render_type(a).is_none() { type_kind(a) } else { type_kind(b) }
        }
        TypeExpr::App(..) => "App (List a, Maybe a, ...)".into(),
        TypeExpr::Effect(..) => "Effect row".into(),
        TypeExpr::BoundedInt(..) => "BoundedInt".into(),
        TypeExpr::PropEq(..) => "PropEq".into(),
        TypeExpr::Constrained(..) => "Constrained".into(),
        TypeExpr::Linear(..) => "Linear".into(),
        TypeExpr::Forall(..) => "Forall".into(),
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
    /// Names bound inside one definition -- its parameters. Consulted FIRST.
    locals: BTreeMap<String, String>,
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
        Env { types, locals: Default::default() }
    }

    fn get(&self, n: &str) -> Option<&str> {
        self.locals.get(n).or_else(|| self.types.get(n)).map(String::as_str)
    }

    /// One more name in scope, for a `let` body.
    fn bind(&self, n: &str, ty: &str) -> Env {
        let mut l = self.locals.clone();
        l.insert(n.to_string(), ty.to_string());
        Env { types: self.types.clone(), locals: l }
    }

    /// A definition's own parameters, in scope for its body only. They shadow:
    /// a parameter named `max` is the parameter, not the builtin, which is the
    /// same collision the golds show for that name.
    fn with_locals(&self, locals: BTreeMap<String, String>) -> Env {
        Env { types: self.types.clone(), locals }
    }
}

/// One expression, as `(ir-text, its-type)`, or the REASON it was refused.
///
/// The reason is the whole point of the return type. A bare `None` told us the
/// corpus refused 1,008 of 1,012 units and nothing about which missing piece
/// would buy the most, so the next node form got picked by guessing. A reason
/// turns that into a histogram.
fn expr(e: &Expr, env: &Env) -> Result<(String, String), String> {
    match e {
        // Literals carry no type of their own in the IR -- `(int-lit 1)`, not
        // `(int-lit 1 int-default)` -- but their type is needed by whatever
        // encloses them, so it is returned alongside.
        Expr::Lit(v, LiteralKind::IntLit, _) => {
            Ok((format!("(int-lit {v})"), "int-default".into()))
        }
        Expr::Lit(v, LiteralKind::TextLit, _) => {
            Ok((format!("(text-lit {v})"), "text".into()))
        }
        Expr::Lit(v, LiteralKind::BoolLit, _) => {
            Ok((format!("(bool-lit {v})"), "boolean".into()))
        }
        Expr::Lit(_, k, _) => Err(format!("literal kind {k:?}")),
        Expr::NameRef(n, _) => match env.get(n) {
            Some(t) => {
                let t = t.to_string();
                Ok((format!("(name {:?} {})", n, t), t))
            }
            None => Err(format!("no type for name `{n}`")),
        },
        Expr::Apply(f, a, _) => {
            let (ft, fty) = expr(f, env)?;
            let (at, _aty) = expr(a, env)?;
            // The result of applying one argument is the arrow's right half.
            // A non-arrow here is an over-application, which is a real error
            // and not something to paper over with the same type back.
            let (_arg, res) = split_fn(&fty)
                .ok_or_else(|| format!("applying a non-arrow `{fty}`"))?;
            Ok((format!("(apply {ft} {at} {res})"), res.to_string()))
        }
        // `(binary <op> L R <type>)`. THE OPERATOR NAME DEPENDS ON THE OPERAND
        // TYPE -- `add-int`, `add-num` and `add-vec` are three names for one
        // source `+` -- so this needs the operands typed first and refuses
        // where it cannot tell. A comparison answers `boolean` whatever it
        // compared; arithmetic answers what it was given.
        Expr::Binary(l, op, r, _) => {
            let (lt, lty) = expr(l, env)?;
            let (rt, rty) = expr(r, env)?;
            if lty != rty {
                return Err(format!("binary operands disagree: `{lty}` vs `{rty}`"));
            }
            let arith = |stem: &str| -> Result<String, String> {
                match lty.as_str() {
                    "int-default" => Ok(format!("{stem}-int")),
                    "real" => Ok(format!("{stem}-num")),
                    other => Err(format!("{stem} on `{other}`")),
                }
            };
            let (name, ty) = match op {
                BinaryOp::OpAdd => (arith("add")?, lty.clone()),
                BinaryOp::OpSub => (arith("sub")?, lty.clone()),
                BinaryOp::OpMul => (arith("mul")?, lty.clone()),
                BinaryOp::OpDiv => (arith("div")?, lty.clone()),
                BinaryOp::OpEq => ("eq".into(), "boolean".to_string()),
                BinaryOp::OpNotEq => ("ne".into(), "boolean".to_string()),
                BinaryOp::OpLt => ("lt".into(), "boolean".to_string()),
                BinaryOp::OpGt => ("gt".into(), "boolean".to_string()),
                BinaryOp::OpLtEq => ("le".into(), "boolean".to_string()),
                BinaryOp::OpGtEq => ("ge".into(), "boolean".to_string()),
                BinaryOp::OpAnd | BinaryOp::OpBoolAnd => ("and".into(), "boolean".to_string()),
                BinaryOp::OpOr => ("or".into(), "boolean".to_string()),
                BinaryOp::OpAppend => match lty.as_str() {
                    "text" => ("append-text".to_string(), lty.clone()),
                    s if s.starts_with("(list ") => ("append-list".to_string(), lty.clone()),
                    other => return Err(format!("append on `{other}`")),
                },
                other => return Err(format!("binary op {other:?}")),
            };
            Ok((format!("(binary {name} {lt} {rt} {ty})"), ty))
        }
        // `(if C T E <type>)`. The type is the BRANCHES', and both must agree
        // -- if they do not, this is not a place to pick one and move on.
        Expr::If(c, th, el, _) => {
            let (ct, _) = expr(c, env)?;
            let (tt, tty) = expr(th, env)?;
            let (et, ety) = expr(el, env)?;
            if tty != ety {
                return Err(format!("if branches disagree: `{tty}` vs `{ety}`"));
            }
            Ok((format!("(if {ct} {tt} {et} {tty})"), tty))
        }
        // `(list-expr (elems ...) ELEM)` -- the trailing type is the ELEMENT's,
        // not the list's, checked against golds carrying text and nested-list
        // elements rather than assumed from the integer cases. The NODE's type
        // is `(list ELEM)`.
        //
        // An empty list has no element to read a type from and is refused: the
        // type is in the context, which is the checker's job and not ours.
        Expr::List(xs, _) => {
            if xs.is_empty() {
                return Err("empty list literal (its type is in the context)".into());
            }
            let mut parts = Vec::new();
            let mut elem: Option<String> = None;
            for x in xs {
                let (xt, xty) = expr(x, env)?;
                match &elem {
                    None => elem = Some(xty),
                    Some(e) if *e == xty => {}
                    Some(e) => return Err(format!("list elements disagree: `{e}` vs `{xty}`")),
                }
                parts.push(xt);
            }
            let e = elem.unwrap();
            Ok((format!("(list-expr (elems {}) {})", parts.join(" "), e), format!("(list {e})")))
        }
        // `(let "n" TYPE VALUE BODY)`, nested one deep per binding, and the
        // let's own type is the BODY's -- a let evaluates to its body. Each
        // binding is in scope for the ones after it and for the body.
        Expr::Let(binds, body, _) => {
            let mut env2 = env.bind("", "");
            let mut heads = Vec::new();
            for b in binds {
                let (vt, vty) = expr(&b.value, &env2)?;
                heads.push((b.name.clone(), vty.clone(), vt));
                env2 = env2.bind(&b.name, &vty);
            }
            let (bt, bty) = expr(body, &env2)?;
            let mut out = bt;
            for (n, ty, v) in heads.into_iter().rev() {
                out = format!("(let {:?} {} {} {})", n, ty, v, out);
            }
            Ok((out, bty))
        }
        other => Err(node_kind(other).to_string()),
    }
}

/// The variant's name, for the refusal histogram.
fn node_kind(e: &Expr) -> &'static str {
    match e {
        Expr::Lit(..) => "Lit",
        Expr::NameRef(..) => "NameRef",
        Expr::Apply(..) => "Apply",
        Expr::Binary(..) => "Binary",
        Expr::Unary(..) => "Unary",
        Expr::If(..) => "If",
        Expr::Let(..) => "Let",
        Expr::Lambda(..) => "Lambda",
        Expr::Match(..) => "Match",
        Expr::List(..) => "List",
        Expr::Record(..) => "Record",
        Expr::FieldAccess(..) => "FieldAccess",
        Expr::Act(..) => "Act",
        Expr::Handle(..) => "Handle",
        Expr::WithTimeout(..) => "WithTimeout",
        Expr::Try(..) => "Try",
        Expr::FieldAssign(..) => "FieldAssign",
        Expr::Lazy(..) => "Lazy",
        Expr::Error(..) => "Error",
        Expr::Induction(..) => "Induction",
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

pub fn emit_defs(ch: &Chapter) -> Result<String, String> {
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

pub fn emit_defs_from(ch: &Chapter, roots: &[&str]) -> Result<String, String> {
    let keep = reachable(ch, roots);
    if keep.is_empty() {
        return Err("no root reached: the chapter defines none of ir-emit-roots".into());
    }
    let env = Env::new(ch);
    // The OPENER is the preamble's last line, so this contributes only the
    // definitions. `preamble::emit` ends at `  (defs` because that is where the
    // syntax-only part of a gold stops.
    let mut out = String::new();
    for d in ch.defs.iter().filter(|d| keep.contains(&d.name)) {
        let declared = match d.declared_type.first() {
            None => return Err(format!("`{}` has no declared type (needs the checker)", d.name)),
            Some(te) => match render_type(te) {
                Some(s) => s,
                None => return Err(format!("type not renderable: {}", type_kind(te))),
            },
        };
        // Parameter types come from walking the declared arrow spine, which is
        // the only place they are written down.
        let mut rest: &str = &declared;
        let mut params = String::new();
        let mut locals: BTreeMap<String, String> = Default::default();
        for p in &d.params {
            let (arg, res) = split_fn(rest)
                .ok_or_else(|| format!("`{}` has more params than its type has arrows", d.name))?;
            params.push_str(&format!(" (param {:?} {})", p.name, arg));
            locals.insert(p.name.clone(), arg.to_string());
            rest = res;
        }
        let denv = env.with_locals(locals);
        let (body, _bty) = expr(&d.body, &denv).map_err(|r| format!("{}: {r}", d.name))?;
        out.push_str(&format!(
            "\n  (def {:?} {:?} (params{}) {} {} 0 0)",
            d.name, d.chapter_slug, params, declared, body
        ));
    }
    Ok(out)
}
