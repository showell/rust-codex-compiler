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

use crate::symbol::{Sym, SymTab};
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
pub fn render_type(syms: &SymTab, t: &TypeExpr) -> Option<String> {
    match t {
        TypeExpr::Named(n, _) => atom(syms.text(*n)).map(str::to_string),
        TypeExpr::Fun(a, b, _) => {
            Some(format!("(fn {} {})", render_type(syms, a)?, render_type(syms, b)?))
        }
        // `List a` is `(list a)` and `Vector a` is `(vector a)`. The golds
        // carry 228,533 of the first, which makes it the cheapest thing in the
        // language to be unable to spell.
        // **`(scopes ...)` IS PARALLEL TO `(effs ...)`**, one string per
        // effect and empty when that effect is unscoped -- three effects print
        // `(scopes "" "" "")`. Read off real IR rather than reasoned about: a
        // single empty list is what a reader expects and it is wrong for every
        // definition with more than one effect.
        TypeExpr::Effect(effs, scopes, _, result, _) => {
            let names: Vec<String> =
                effs.iter().map(|n| format!(" {:?}", syms.text(*n))).collect();
            // A scope is written down only when there is one, so the list is
            // padded to the effects rather than assumed to match.
            let sc: Vec<String> = (0..effs.len())
                .map(|i| format!(" {:?}", scopes.get(i).map_or("", |s| s.as_str())))
                .collect();
            Some(format!(
                "(effectful (effs{}) (scopes{}) {})",
                names.concat(),
                sc.concat(),
                render_type(syms, result)?
            ))
        }
        TypeExpr::App(head, args, _) => match (&**head, args.as_slice()) {
            (TypeExpr::Named(n, _), [only]) if syms.text(*n) == "List" => {
                Some(format!("(list {})", render_type(syms, only)?))
            }
            (TypeExpr::Named(n, _), [only]) if syms.text(*n) == "Vector" => {
                Some(format!("(vector {})", render_type(syms, only)?))
            }
            _ => None,
        },
        _ => None,
    }
}

/// The shape of a type we cannot render, for the refusal histogram. A NAMED
/// type reports its name, because "which named types are missing" and "which
/// type constructors are missing" are different questions with different fixes.
pub fn type_kind(syms: &SymTab, t: &TypeExpr) -> String {
    match t {
        TypeExpr::Named(n, _) => format!("Named {}", syms.text(*n)),
        TypeExpr::Fun(a, b, _) => {
            if render_type(syms, a).is_none() { type_kind(syms, a) } else { type_kind(syms, b) }
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
pub struct Env<'a> {
    /// Carried so the functions below can spell a name without every one of
    /// them taking a table -- `Env` was already threaded everywhere.
    syms: &'a SymTab,
    /// **Keyed by symbol, not by text.** These are lookup-only -- nothing
    /// iterates them -- so the key can be the four-byte name.
    types: BTreeMap<Sym, String>,
    locals: BTreeMap<Sym, String>,
}

impl<'a> Env<'a> {
    /// The builtins first, then this chapter's own declared types on top --
    /// a chapter that defines `max` shadows the builtin, and the golds show
    /// both spellings for that name.
    pub fn new(ch: &Chapter) -> Env<'_> {
        // A builtin this chapter never names cannot be what any symbol here
        // means, so it needs no entry.
        let mut types: BTreeMap<Sym, String> = BUILTIN_IR_TYPES
            .iter()
            .filter_map(|(n, t)| ch.syms.find(n).map(|s| (s, t.to_string())))
            .collect();
        for d in &ch.defs {
            if let Some(dt) = d.declared_type.first().and_then(|t| render_type(&ch.syms, t)) {
                types.insert(d.name, dt);
            }
        }
        Env { syms: &ch.syms, types, locals: Default::default() }
    }

    fn get(&self, n: Sym) -> Option<&str> {
        self.locals.get(&n).or_else(|| self.types.get(&n)).map(String::as_str)
    }

    /// One more name in scope, for a `let` body.
    fn bind(&self, n: Sym, ty: &str) -> Env<'a> {
        let mut l = self.locals.clone();
        l.insert(n, ty.to_string());
        Env { syms: self.syms, types: self.types.clone(), locals: l }
    }

    /// A definition's own parameters, in scope for its body only. They shadow:
    /// a parameter named `max` is the parameter, not the builtin, which is the
    /// same collision the golds show for that name.
    fn with_locals(&self, locals: BTreeMap<Sym, String>) -> Env<'a> {
        Env { syms: self.syms, types: self.types.clone(), locals }
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
        Expr::NameRef(n, _) => match env.get(*n) {
            Some(t) => {
                let t = t.to_string();
                Ok((format!("(name {:?} {})", env.syms.text(*n), t), t))
            }
            None => Err(format!("no type for name `{}`", env.syms.text(*n))),
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
            let mut env2 = env.bind(Sym::default(), "");
            let mut heads = Vec::new();
            for b in binds {
                let (vt, vty) = expr(&b.value, &env2)?;
                heads.push((b.name.clone(), vty.clone(), vt));
                env2 = env2.bind(b.name, &vty);
            }
            let (bt, bty) = expr(body, &env2)?;
            let mut out = bt;
            for (n, ty, v) in heads.into_iter().rev() {
                out = format!("(let {:?} {} {} {})", env.syms.text(n), ty, v, out);
            }
            Ok((out, bty))
        }
        // `(act (stmts S...) TYPE)`, one `(do-exec E)` or `(do-bind "n" TYPE E)`
        // per statement, and the block's type is the type of what it ENDS
        // with -- an act evaluates to its last statement, the same way a let
        // evaluates to its body.
        //
        // A BIND IS IN SCOPE FOR THE STATEMENTS AFTER IT, which is the whole
        // reason the environment is threaded rather than rebuilt: `x <- f ...`
        // followed by a statement mentioning `x` is the ordinary shape, and an
        // act that started each statement from the outer scope would refuse it
        // as an undefined name.
        //
        // A bind's written type is the type of what it binds. Upstream's row
        // arithmetic decides what the EFFECT of the block is; this is the
        // value side, which is all the wire carries here.
        Expr::Act(stmts, _) => {
            let mut env2 = env.bind(Sym::default(), "");
            let mut parts = Vec::new();
            let mut last = "nothing".to_string();
            for st in stmts {
                match st {
                    crate::ast::ActStmt::Exec(e, _) => {
                        let (t, ty) = expr(e, &env2)?;
                        parts.push(format!("(do-exec {t})"));
                        last = ty;
                    }
                    crate::ast::ActStmt::Bind(n, e, _) => {
                        let (t, ty) = expr(e, &env2)?;
                        parts.push(format!("(do-bind {:?} {} {})", env.syms.text(*n), ty, t));
                        env2 = env2.bind(*n, &ty);
                        last = ty;
                    }
                }
            }
            Ok((format!("(act (stmts {}) {})", parts.join(" "), last), last))
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
        ch.defs.iter().map(|d| (ch.syms.text(d.name), d)).collect();
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
                    if by_name.contains_key(ch.syms.text(*m)) && !seen.contains(ch.syms.text(*m)) {
                        stack.push(ch.syms.text(*m).to_string());
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
    for d in ch.defs.iter().filter(|d| keep.contains(ch.syms.text(d.name))) {
        let declared = match d.declared_type.first() {
            None => {
                return Err(format!(
                    "`{}` has no declared type (needs the checker)",
                    ch.syms.text(d.name)
                ))
            }
            Some(te) => match render_type(&ch.syms, te) {
                Some(s) => s,
                None => {
                    return Err(format!("type not renderable: {}", type_kind(&ch.syms, te)))
                }
            },
        };
        // Parameter types come from walking the declared arrow spine, which is
        // the only place they are written down.
        let mut rest: &str = &declared;
        let mut params = String::new();
        let mut locals: BTreeMap<Sym, String> = Default::default();
        for p in &d.params {
            let (arg, res) = split_fn(rest)
                .ok_or_else(|| {
                format!("`{}` has more params than its type has arrows", ch.syms.text(d.name))
            })?;
            params.push_str(&format!(" (param {:?} {})", ch.syms.text(p.name), arg));
            locals.insert(p.name, arg.to_string());
            rest = res;
        }
        let denv = env.with_locals(locals);
        let (body, _bty) =
            expr(&d.body, &denv).map_err(|r| format!("{}: {r}", ch.syms.text(d.name)))?;
        out.push_str(&format!(
            "\n  (def {:?} {:?} (params{}) {} {} 0 0)",
            ch.syms.text(d.name), d.chapter_slug, params, declared, body
        ));
    }
    Ok(out)
}

/// The `--- lower ---` section: a SHAPE dump, not IR text.
///
/// `LowerHarness.codex` prints each definition's header and then its expression
/// tree as depth-prefixed kinds. The walk is PRE-ORDER and descends only into
/// arms that carry an IRExpr -- a node holding a statement list prints its kind
/// and stops, because the point is to diff two arms against each other and a
/// node the walk does not enter is still a node both arms must agree on.
///
/// Cheaper to match than the IR text and it grades the same thing: whether the
/// tree we lowered has the shape upstream lowered.
/// NOT PRUNED. `ir-prune-unreachable-roots` runs at EMIT time -- the driver
/// writes `emit-ir-chapter (ir-prune-unreachable-roots lifted-ir
/// ir-emit-roots)` -- so the IR golds are pruned and this rung is not. `fib`
/// shows the difference directly: nothing calls `double`, the IR gold drops it,
/// and lower.truth keeps it.
pub fn lower_section(ch: &Chapter, _roots: &[&str]) -> String {
    let defs: Vec<&crate::ast::Def> = ch.defs.iter().collect();
    let mut s = String::from("--- lower ---\n");
    s.push_str(&format!("ir-name |{}|\n", ch.syms.text(ch.name)));
    s.push_str(&format!("ir-defs {}\n", defs.len()));
    s.push_str("ir-eff-ops 0\n.\n");
    for d in &defs {
        let ty = d
            .declared_type
            .first()
            .and_then(|t| crate::check::resolve_declared(&ch.syms, t))
            .map_or_else(|| "other".to_string(), |t| crate::check::type_kind(&ch.syms, &t));
        s.push_str(&format!(
            "irdef {} params {} slug {} punctual 0 uparams 0 ty {}\n",
            ch.syms.text(d.name),
            d.params.len(),
            d.chapter_slug,
            ty
        ));
        shape(&ch.syms, &d.body, 0, &mut s);
    }
    s.push_str(".\n---\n");
    s
}

fn kind(syms: &SymTab, e: &Expr) -> String {
    match e {
        Expr::Lit(_, LiteralKind::IntLit, _) => "int".into(),
        Expr::Lit(_, LiteralKind::NumLit, _) => "num".into(),
        Expr::Lit(_, LiteralKind::TextLit, _) => "text".into(),
        Expr::Lit(_, LiteralKind::BoolLit, _) => "bool".into(),
        Expr::Lit(_, LiteralKind::CharLit, _) => "char".into(),
        Expr::NameRef(n, _) => format!("name:{}", syms.text(*n)),
        Expr::Binary(..) => "binary".into(),
        Expr::Unary(..) => "negate".into(),
        Expr::If(..) => "if".into(),
        Expr::Let(bs, ..) => {
            format!("let:{}", bs.first().map_or("", |b| syms.text(b.name)))
        }
        Expr::Apply(..) => "apply".into(),
        Expr::Lambda(..) => "lambda".into(),
        Expr::List(..) => "list".into(),
        Expr::Match(..) => "match".into(),
        Expr::Act(..) => "act".into(),
        Expr::Record(n, ..) => format!("record:{}", syms.text(*n)),
        Expr::FieldAccess(_, f, _) => format!("field:{}", syms.text(*f)),
        Expr::FieldAssign(_, f, _, _) => format!("store:{}", syms.text(*f)),
        Expr::Error(..) => "error".into(),
        _ => "other".into(),
    }
}

fn shape(syms: &SymTab, e: &Expr, d: usize, out: &mut String) {
    out.push_str(&format!("e{d} {}\n", kind(syms, e)));
    match e {
        Expr::Binary(l, _, r, _) => {
            shape(syms, l, d + 1, out);
            shape(syms, r, d + 1, out);
        }
        Expr::Unary(x, _) => shape(syms, x, d + 1, out),
        Expr::If(c, t, e2, _) => {
            shape(syms, c, d + 1, out);
            shape(syms, t, d + 1, out);
            shape(syms, e2, d + 1, out);
        }
        Expr::Let(bs, body, _) => {
            if let Some(b) = bs.first() {
                shape(syms, &b.value, d + 1, out);
            }
            shape(syms, body, d + 1, out);
        }
        Expr::Apply(f, a, _) => {
            shape(syms, f, d + 1, out);
            shape(syms, a, d + 1, out);
        }
        Expr::Lambda(_, b, _) => shape(syms, b, d + 1, out),
        Expr::FieldAccess(r, _, _) => shape(syms, r, d + 1, out),
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    /// The IR text for one chapter, or the refusal.
    ///
    /// Through the real front end -- parse, desugar, emit -- because the point
    /// of these is the SPELLING that reaches the wire, and a unit test that
    /// built a `TypeExpr` by hand would be testing my idea of the AST rather
    /// than the one the parser makes.
    fn ir(src: &str) -> String {
        let bytes = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&bytes);
        let mut dg = crate::desugar::Desugar::new(&bytes);
        let ch = dg.chapter(&parsed.tree);
        match super::emit_defs(&ch) {
            Ok(s) => s,
            Err(e) => format!("REFUSED: {e}"),
        }
    }

    /// Just the one definition's line, which is what these are about.
    fn def_line(src: &str, name: &str) -> String {
        let all = ir(src);
        all.lines()
            .find(|l| l.contains(&format!("(def {name:?}")))
            .map(|l| l.trim().to_string())
            .unwrap_or(all)
    }

    const PURE: &str = "Chapter: T\n\nSection: S\n  f : Integer -> Integer\n  f (n) = n\n\n";

    /// **`[Console] Nothing` IS `(effectful (effs "Console") (scopes "") nothing)`.**
    ///
    /// `scopes` is PARALLEL TO `effs`, one string per effect and empty when the
    /// effect is unscoped -- read off real IR rather than guessed, where three
    /// effects print `(scopes "" "" "")`. Rendering it as a single empty list
    /// would be wrong for every multi-effect definition and right for the one
    /// a test would obviously reach for.
    #[test]
    fn an_effect_row_renders_with_a_scope_for_each_effect() {
        let src = format!(
            "{PURE}Section: E\n  opening : [Console] Nothing = act\n   f 1\n  end\n"
        );
        assert!(
            def_line(&src, "opening")
                .contains(r#"(effectful (effs "Console") (scopes "") nothing)"#),
            "got: {}",
            def_line(&src, "opening")
        );
    }

    #[test]
    fn two_effects_carry_two_scopes() {
        let src = format!(
            "{PURE}Section: E\n  opening : [Console, FileSystem] Nothing = act\n   f 1\n  end\n"
        );
        assert!(
            def_line(&src, "opening").contains(
                r#"(effectful (effs "Console" "FileSystem") (scopes "" "") nothing)"#
            ),
            "got: {}",
            def_line(&src, "opening")
        );
    }

    /// **AN `act` IS `(act (stmts ...) TYPE)` and each statement is wrapped.**
    /// `print-line-uni "a"` alone is one `do-exec`; the block's type is the
    /// type of what it ends with.
    #[test]
    fn an_act_block_wraps_its_statements() {
        let src = format!(
            "{PURE}Section: E\n  opening : [Console] Nothing = act\n   f 1\n   f 2\n  end\n"
        );
        let line = def_line(&src, "opening");
        assert!(line.contains("(act (stmts (do-exec "), "got: {line}");
        assert!(line.matches("(do-exec ").count() == 2, "one per statement: {line}");
        assert!(line.ends_with("int-default) 0 0)"), "the act ends with its last statement's type: {line}");
    }

    /// **WHAT IS STILL MISSING, PINNED SO IT IS A TEST AND NOT A COMMENT.**
    /// An effectful BUILTIN has no wire type here. Its spelling embeds a row
    /// VARIABLE ID -- `print-line-uni` is
    /// `(fn text nothing (row (labels (label "Console.Write" "")) "" 6))` --
    /// and that 6 is minted by the checker: `fresh-row-id` is a +1 counter
    /// fired from nine places, and defs the call never touches move the
    /// number. A static table cannot carry it, so this refuses rather than
    /// inventing one. Change this test when the checker can answer.
    #[test]
    fn an_effectful_builtin_is_the_gap_that_needs_the_checker() {
        let src = format!(
            "{PURE}Section: E\n  opening : [Console] Nothing = act\n   print-line-uni \"a\"\n  end\n"
        );
        assert_eq!(ir(&src), "REFUSED: opening: no type for name `print-line-uni`");
    }

    /// A pure definition still renders exactly as it did, which is the thing
    /// these changes must not disturb: it is already byte-identical to the
    /// oracle and that is the only verified ground the native road stands on.
    #[test]
    fn a_pure_definition_is_unchanged() {
        let src = "Chapter: Fib\n\nSection: M\n  fib : Integer -> Integer\n  fib (n) =\n   if n <= 1 then n\n   else fib (n - 1) + fib (n - 2)\n\nSection: E\n  opening : Integer\n  opening = fib 20\n";
        assert_eq!(
            def_line(src, "fib"),
            r#"(def "fib" "Fib" (params (param "n" int-default)) (fn int-default int-default) (if (binary le (name "n" int-default) (int-lit 1) boolean) (name "n" int-default) (binary add-int (apply (name "fib" (fn int-default int-default)) (binary sub-int (name "n" int-default) (int-lit 1) int-default) int-default) (apply (name "fib" (fn int-default int-default)) (binary sub-int (name "n" int-default) (int-lit 2) int-default) int-default) int-default) int-default) 0 0)"#
        );
    }
}
