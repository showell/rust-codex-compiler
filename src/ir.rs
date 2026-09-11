//! The IR document: check, lower, run the passes, emit.
//!
//! ```text
//!   check ──▶ lower ──▶ lift lambdas ──▶ pipeline ──▶ prune ──▶ text
//! ```
//!
//! **THE ORDER IS THE DRIVER'S**, `opening.codex:798` and the `CDX4030
//! PIPELINE` line every compile log carries. Two parts of it are easy to get
//! backwards and both change the document:
//!
//! * **lifting comes before the pipeline**, so an inlining pass sees `__lam_N`
//!   as an ordinary definition and can inline it like any other;
//! * **pruning comes LAST.** The driver writes `emit-ir-chapter
//!   (ir-prune-unreachable-roots lifted-ir ir-emit-roots)`, so a definition
//!   whose only caller inlined it away is dropped. That is why `sb-length` is
//!   in no gold: the pass took its body, and pruning took the definition.
//!
//! ## One deviation, and it is load-bearing
//!
//! Upstream lowers EVERY definition and prunes once at the end. This lowers
//! the reachable ones only, because lowering here refuses what it cannot type
//! exactly and a resolved unit carries whole cited chapters of library code
//! nothing in the program reaches -- `neg-int-parse` cites Foreword ListUtils
//! and its gold holds one definition. Refusing the chapter because a function
//! nobody calls uses a form we have not built yet would be an answer about the
//! wrong program.
//!
//! It is sound because the passes only REMOVE references: reachable-after is a
//! subset of reachable-before, so pruning the input and pruning the output
//! reach the same set. The one thing it would change is `__lam_N` NUMBERING,
//! which upstream assigns before pruning -- so `number_lambdas` walks the AST
//! rather than the lowered defs, and keeps the numbers upstream would give.

use crate::ast::{Chapter, Expr, LiteralKind};
use crate::ir_chapter::IrDef;
use crate::check::{Binding, TypeDefs, UnifyState};
use crate::symbol::SymTab;
use std::collections::BTreeMap;

pub use crate::ir_text::render_ty;

/// The definition lines for a chapter, or the reason one of them is out of
/// reach -- a chapter with half its definitions emitted compares to nothing.
///
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

/// Check, then lower -- the driver's own two steps, in its own order
/// (`opening.codex:798`). A program the checker refuses is not lowered:
/// the driver halts with the count and the first diagnostic.
pub fn emit_defs(ch: &Chapter) -> Result<String, String> {
    let (bindings, st, tds) = crate::check::check_chapter_full(ch);
    if let Some(halt) = codegen_halted(&st) {
        return Err(halt);
    }
    emit_defs_checked(ch, &bindings, &st, &tds, &IR_EMIT_ROOTS)
}

/// The driver's halt line when the checker raised, else None.
pub fn codegen_halted(st: &crate::check::UnifyState) -> Option<String> {
    let n = st.errors();
    if n == 0 {
        return None;
    }
    let first = st.diags.first().map(|d| format!("CDX{} {}", d.code, d.message)).unwrap_or_default();
    Some(format!("CODEGEN-HALTED: {n} error(s); no IR emitted; first {first}"))
}

/// Names reachable from the roots, following NameRefs through def bodies.
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

/// The lowered, resolved, lifted and pruned definitions, with the table
/// their names index. What every emitter reads: the IR text emitter and the
/// Roc emitter are two spellings of this one document.
pub struct Lowered {
    pub syms: SymTab,
    pub defs: Vec<IrDef>,
}

pub fn emit_defs_checked(
    ch: &Chapter,
    bindings: &[Binding],
    st: &UnifyState,
    tds: &TypeDefs,
    roots: &[&str],
) -> Result<String, String> {
    let low = lower_chapter(ch, bindings, st, tds, roots)?;
    Ok(crate::ir_text::emit_defs(&low.syms, &low.defs))
}

/// Lower, run the pipeline, resolve, lift, prune -- the driver's order.
pub fn lower_chapter(
    ch: &Chapter,
    bindings: &[Binding],
    st: &UnifyState,
    tds: &TypeDefs,
    roots: &[&str],
) -> Result<Lowered, String> {
    let keep = reachable(ch, roots);
    if keep.is_empty() {
        return Err("no root reached: the chapter defines none of ir-emit-roots".into());
    }
    lower_pipeline(ch, bindings, st, tds, roots, true)
}

/// Lower, resolve, lift -- and NO pipeline and NO prune. What an emitter
/// writing the chapters AS WRITTEN reads: the pipeline inlines a definition
/// the unit calls once, so a chapter's shape would depend on which spec is
/// attached to it, and a module imported by fifty specs has to be one text.
pub fn lower_whole(
    ch: &Chapter,
    bindings: &[Binding],
    st: &UnifyState,
    tds: &TypeDefs,
) -> Result<Lowered, String> {
    lower_pipeline(ch, bindings, st, tds, &[], false)
}

fn lower_pipeline(
    ch: &Chapter,
    bindings: &[Binding],
    st: &UnifyState,
    tds: &TypeDefs,
    roots: &[&str],
    driver_passes: bool,
) -> Result<Lowered, String> {
    // **A LIFTED NAME IS A NAME THE CHAPTER'S TABLE NEVER INTERNED.** `Sym` is
    // an index into the table that made it, so `__lam_0` needs a table that
    // holds it. Interning is append-only, so a clone extended with the lifted
    // names leaves every existing `Sym` meaning exactly what it did.
    //
    // `__linked-list-empty` is the same case one stage earlier: lowering
    // WRITES that call for an empty list in linked-list position, and no
    // source has to have named it.
    // **THE TABLE IS SHARED WITH LOWERING, NOT LENT TO IT.** `binder-fresh`
    // mints `max_1` for a binder that shadows, so lowering interns as it goes
    // and the cell is what lets it while every read stays a borrow.
    let syms = std::cell::RefCell::new(ch.syms.clone());
    let ll_empty = syms.borrow_mut().intern("__linked-list-empty");
    let mut defs = Vec::new();
    {
        let cx = crate::lowering::Lower::new(&syms, bindings, st, tds, ll_empty);
        for d in ch.defs.iter() {
            defs.push(crate::lowering::lower_def(d, &cx)?);
        }
    }
    let mut syms = syms.into_inner();
    // **THE PIPELINE RUNS BEFORE THE LIFT, AND THE ORDER IS THE POINT.**
    // `compile-frontend-ir` lowers and then calls `run-ir-pipeline`;
    // `lift-ir-for-emit` is a separate step the emitter takes afterwards
    // (subject 65601 and 66599). Lifting first is not a rearrangement --
    // `once-binder-free` REFUSES an `IrLambda`, so a definition whose body is
    // a comprehension is not an inline candidate at all upstream. With the
    // lift first its lambda is already a name and the definition inlines and
    // disappears: that is where the `mcopy-*-node` family and
    // `copy-sx-ctordef` went, five definitions the oracle keeps.
    let defs = if driver_passes { crate::ir_passes::pipeline(defs, &syms) } else { defs };
    // RESOLVE, between the pipeline and the lift (subject 65624). The table is
    // the chapter's type declarations OVER every name the checker typed, which
    // is `sort-bindings (type-map & all-bindings)` -- the declaration wins.
    let mut type_map: crate::resolve_types::TypeMap =
        bindings.iter().map(|b| (b.name, b.ty.clone())).collect();
    type_map.extend(tds.declared().iter().map(|(n, t)| (*n, t.clone())));
    let defs = crate::resolve_types::resolve_defs(defs, &syms, &type_map);
    let defs = crate::lambda_lifting::lift_lambdas(defs, &mut syms);
    let defs = if driver_passes {
        crate::ir_passes::prune_unreachable_roots(defs, roots, &syms)
    } else {
        defs
    };
    Ok(Lowered { syms, defs })
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
    let tds = crate::check::TypeDefs::new(ch);
    let defs: Vec<&crate::ast::Def> = ch.defs.iter().collect();
    let mut s = String::from("--- lower ---\n");
    s.push_str(&format!("ir-name |{}|\n", ch.syms.text(ch.name)));
    s.push_str(&format!("ir-defs {}\n", defs.len()));
    s.push_str("ir-eff-ops 0\n.\n");
    for d in &defs {
        let ty = d
            .declared_type
            .first()
            .and_then(|t| crate::check::resolve_declared(&ch.syms, &tds, t))
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

    /// **THE ROW ID IS THE CHECKER'S, AND IT MOVES.** `print-line-uni` in a
    /// chapter that applies nothing before it takes row 0; the same call in
    /// fib takes row 6, because fib's own body left the counter there. The two
    /// assertions differ in one digit and that digit is the entire reason a
    /// static table could not answer this.
    ///
    /// Both read off `codexir` at `u56-candidate-sunday`. `f` is absent from
    /// each because nothing calls it.
    #[test]
    fn an_effectful_builtin_carries_the_row_the_checker_minted() {
        let src = format!(
            "{PURE}Section: E\n  opening : [Console] Nothing = act\n   print-line-uni \"a\"\n  end\n"
        );
        assert_eq!(
            def_line(&src, "opening"),
            r#"(def "opening" "T" (params) (effectful (effs "Console") (scopes "") nothing) (act (stmts (do-exec (apply (name "print-line-uni" (fn text nothing (row (labels (label "Console.Write" "")) "" 0))) (text-lit "a") nothing))) nothing) 0 0)"#
        );
    }

    /// **THE ORACLE'S OWN BYTES, FOR THE WHOLE SLICE SUBJECT.**
    ///
    /// `codexir < fib.codex` at `u56-candidate-sunday`, the two definition
    /// lines verbatim. Everything the native road was missing is in the
    /// `opening` line and nowhere else:
    ///
    ///   * `print-line-uni` carries the row the CHECKER minted -- id 6, which
    ///     is what fib's own body leaves the counter at -- and no static table
    ///     can answer that.
    ///   * `show` is `(fn int-default text)`: a `forall` instantiated to a
    ///     fresh variable, then UNIFIED with the argument through the
    ///     application. Rendering the declared type gives `(fn (tvar 4) text)`.
    ///   * every `apply` carries its RESOLVED result, which is the same
    ///     substitution read a second time.
    ///
    /// `double` is absent because nothing calls it and `ir-prune-unreachable-roots`
    /// runs before emission.
    #[test]
    fn fib_is_byte_identical_to_the_oracle() {
        let src = "Chapter: Fib\n\nSection: Math\n  fib : Integer -> Integer\n  fib (n) =\n   if n <= 1 then n\n   else fib (n - 1) + fib (n - 2)\n\n  double : Integer -> Integer\n  double (n) = n + n\n\nSection: Main\n  opening : [Console] Nothing = act\n   print-line-uni (show (fib 20))\n  end\n";
        assert_eq!(
            ir(src),
            "\n  (def \"fib\" \"Fib\" (params (param \"n\" int-default)) (fn int-default int-default) (if (binary le (name \"n\" int-default) (int-lit 1) boolean) (name \"n\" int-default) (binary add-int (apply (name \"fib\" (fn int-default int-default)) (binary sub-int (name \"n\" int-default) (int-lit 1) int-default) int-default) (apply (name \"fib\" (fn int-default int-default)) (binary sub-int (name \"n\" int-default) (int-lit 2) int-default) int-default) int-default) int-default) 0 0)\
             \n  (def \"opening\" \"Fib\" (params) (effectful (effs \"Console\") (scopes \"\") nothing) (act (stmts (do-exec (apply (name \"print-line-uni\" (fn text nothing (row (labels (label \"Console.Write\" \"\")) \"\" 6))) (apply (name \"show\" (fn int-default text)) (apply (name \"fib\" (fn int-default int-default)) (int-lit 20) int-default) text) nothing))) nothing) 0 0)"
        );
    }

    /// **`^` IS ALWAYS `pow-int`**, whatever the operands: `lower-binary` has
    /// no Real arm for it, and the oracle spells `pow-int` for `pow-on-real`
    /// too. Lowering refused the operator outright until now.
    #[test]
    fn exponentiation_is_always_pow_int() {
        let ints = "Chapter: P\n\nSection: S\n  f : Integer -> Integer\n  f (n) = n ^ 2\n\nSection: M\n  opening : [Console] Nothing = act\n   print-line-uni (show (f 3))\n  end\n";
        assert!(def_line(ints, "f").contains("(binary pow-int"), "{}", def_line(ints, "f"));
        let reals = "Chapter: P\n\nSection: S\n  f : Real -> Real\n  f (n) = n ^ 2.0\n\nSection: M\n  opening : [Console] Nothing = act\n   print-line-uni (show (f 3.0))\n  end\n";
        assert!(def_line(reals, "f").contains("(binary pow-int"), "{}", def_line(reals, "f"));
    }

    /// `with <Effect> <body>` and its clauses, which lowering REFUSED until
    /// now -- six corpus chapters produced no IR at all for a program the
    /// oracle compiles.
    ///
    /// **THE LAST PARAMETER OF A CLAUSE IS THE RESUME NAME**, not a parameter:
    /// `tick (resume) = ...` spells `(params)` and a resume of `"resume"`.
    /// The ones before it are the operation's own, and they are spelled TWICE
    /// -- in `(params ...)` and again in the lambda
    /// `wrap-clause-body-in-lambda` makes of the body. That is upstream's
    /// shape, and a clause with no operation parameters is not wrapped.
    ///
    /// The `let .. in` matters: a handler block has no `end`, so without it
    /// the clause list swallows whatever follows.
    #[test]
    fn a_handler_lowers_to_handle_with_its_clauses() {
        let src = "Chapter: H\n\nSection: E\n\n  effect Counter where\n    tick : [Counter] Integer\n\nSection: B\n  run : Integer -> Integer\n  run (n) = let r = with Counter tick\n      tick (resume) = resume n\n    in r\n\nSection: Main\n  opening : [Console] Nothing = act\n   print-line-uni (show (run 1))\n  end\n";
        let line = def_line(src, "run");
        assert!(line.contains(r#"(handle "Counter""#), "{line}");
        assert!(line.contains(r#"(handle-clause "tick" (params) "resume""#), "{line}");
        // No operation parameters, so the body is NOT wrapped in a lambda.
        assert!(!line.contains("(lambda"), "{line}");
        // Nothing after the clause list was swallowed.
        assert!(!line.contains(r#""Section""#), "{line}");
    }

    /// An operation parameter appears in `(params ...)`, and the lambda the
    /// body is wrapped in is then LIFTED like any other -- upstream's own
    /// output for `handler-smoke` spells the clause body as an apply of
    /// `__lam_0`, so the wrap is real even though it is not visible here.
    #[test]
    fn an_operation_parameter_is_spelled_and_its_wrap_is_lifted() {
        let src = "Chapter: H\n\nSection: E\n\n  effect Transform where\n    apply-op : Integer -> [Transform] Integer\n\nSection: B\n  run : Integer -> Integer\n  run (n) = let r = with Transform (apply-op 6)\n      apply-op (x) (resume) = resume (x * n)\n    in r\n\nSection: Main\n  opening : [Console] Nothing = act\n   print-line-uni (show (run 1))\n  end\n";
        let line = def_line(src, "run");
        assert!(line.contains(r#"(handle-clause "apply-op" (params "x") "resume""#), "{line}");
        assert!(line.contains("__lam_0"), "the wrapping lambda was not lifted: {line}");
        // **AND `x` LEARNED IT WAS AN INTEGER FROM `x * n`.** Arithmetic
        // unifies its operands before it answers; without that the clause
        // parameter stayed a fresh variable and `resume` reached the wire as
        // `(fn (tvar N) ..)` where the oracle says `(fn int-default ..)`.
        assert!(!line.contains("(fn (tvar"), "an operand never resolved: {line}");
    }

    /// **A NESTED RECORD LITERAL'S FIELDS ARE NOT THE RECEIVER'S.** `revised`
    /// collected them with a DEEP walk, so `o revised { ob = Inner { ia = 5 } }`
    /// asked `Outer` for a field `ia` and the chapter was refused. Four corpus
    /// units died of this.
    #[test]
    fn revised_reads_its_own_fields_and_not_a_nested_literals() {
        let src = "Chapter: T\n\nSection: S\n  Inner = record {\n    ia : Integer\n  }\n\n  Outer = record {\n    oa : Integer,\n    ob : Inner\n  }\n\n  bump : Outer -> Outer\n  bump (o) = o revised { ob = Inner { ia = 5 } }\n\n  opening : Integer = (bump (Outer { oa = 1, ob = Inner { ia = 2 } })).oa\n";
        let out = ir(src);
        assert!(!out.contains("REFUSED"), "{out}");
        // The write is a `__record-set` spine, not a field store: upstream's
        // shape, and the value is hoisted above the write.
        assert!(out.contains("__record-set"), "{out}");
        assert!(out.contains("__rv0"), "{out}");
    }

    /// **THE TWO NUMBERS AT THE END OF A DEF LINE ARE NOT ALWAYS ZERO.** They
    /// are `is-punctual` and `wcet-budget` (`ir-emit-def`, subject 58000), and
    /// they were hardcoded here until the oracle was read: `punctual` defs
    /// spell `1`, and the budget is whatever the author declared. Twenty-one
    /// def lines in `punctual-quire` alone were wrong by these two bytes.
    #[test]
    fn a_punctual_def_publishes_its_flag_and_its_budget() {
        // `f` takes a LIST so that it survives to the wire: a constant call to
        // a straight-line function is folded and the definition pruned, and a
        // punctual function may not recurse (CDX6005 halts the driver).
        let chapter = |modifier: &str| {
            format!("Chapter: T\n\nSection: S\n  {modifier}f : List Integer -> Integer\n  f (xs) = list-length xs + 1\n\nSection: Main\n  opening : [Console] Nothing = act\n   print-line-uni (show (f [1, 2, 3]))\n  end\n")
        };
        assert!(def_line(&chapter(""), "f").ends_with("int-default) 0 0)"), "{}", def_line(&chapter(""), "f"));
        assert!(def_line(&chapter("punctual "), "f").ends_with("int-default) 1 0)"), "{}", def_line(&chapter("punctual "), "f"));
        // The budget is OPTIONAL and separate: a declared one reaches the wire.
        assert!(def_line(&chapter("punctual 64 "), "f").ends_with("int-default) 1 64)"), "{}", def_line(&chapter("punctual 64 "), "f"));
    }

    /// **A DOTTED EFFECT IS ONE NAME, AND A SCOPE BELONGS TO THE EFFECT IT
    /// FOLLOWS.** `[Device.Block]` is one effect; taking the identifiers and
    /// dropping the dots makes it two, pads `(scopes)` to match, and produces
    /// a signature no reader can resolve.
    ///
    /// Both lines are `codexir`'s at `u56-candidate-sunday`. The second is
    /// `[Console "stdout", FileSystem.Read "/config/"]`, which is the shape
    /// that needs the scope kept POSITIONAL: a scope in the middle of a row
    /// cannot be recovered by padding the end.
    #[test]
    fn an_effect_row_keeps_dotted_names_and_their_scopes() {
        let dotted = "Chapter: BlockIdentify\n\nSection: Body\n  opening : [Device.Block] Integer = block-sector-count\n";
        assert_eq!(
            def_line(dotted, "opening"),
            r#"(def "opening" "BlockIdentify" (params) (effectful (effs "Device.Block") (scopes "") int-default) (name "block-sector-count" int-default) 0 0)"#
        );

        let scoped = "Chapter: Sc\n\nSection: S\n  opening : [Console \"stdout\", FileSystem.Read \"/config/\"] Nothing = act\n   print-line-uni \"a\"\n  end\n";
        assert!(
            def_line(scoped, "opening").contains(
                r#"(effectful (effs "Console" "FileSystem.Read") (scopes "stdout" "/config/") nothing)"#
            ),
            "got: {}",
            def_line(scoped, "opening")
        );
    }

    /// **AN EMPTY LIST'S ELEMENT TYPE COMES FROM THE CONTEXT**, which is a
    /// variable the checker minted and unification decided. `codexir`'s bytes
    /// at `u56-candidate-sunday`, with `f` called twice so the single-caller
    /// pass leaves it standing.
    #[test]
    fn an_empty_list_carries_the_element_type_the_checker_decided() {
        let src = "Chapter: T\n\nSection: S\n  f : Integer -> List Integer\n  f (x) = []\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (list-length (f 1)))\n   print-line-uni (show (list-length (f 2)))\n  end\n";
        assert_eq!(
            def_line(src, "f"),
            r#"(def "f" "T" (params (param "x" int-default)) (fn int-default (list int-default)) (list-expr (elems) int-default) 0 0)"#
        );
    }

    /// **AN ORPHAN EMPTY LIST DEFAULTS ITS ELEMENT.** A monomorphic
    /// definition's unconstrained `[]` -- used only where the element is never
    /// observed -- has an element type no context and no generic binds. Left a
    /// bare variable it reaches the zig plug as "no element type for this empty
    /// list"; a provably-empty list's unobserved element defaults to
    /// int-default so every plug can size it. (roc-alias-empty.)
    #[test]
    fn an_orphan_empty_list_defaults_its_element() {
        let src = "Chapter: T\n\nSection: S\n  ae : Integer -> Integer\n  ae (n) = let x = [] in let y = x in if list-length y == 0 then 42 else 0\n\nSection: E\n  opening : Integer\n  opening = ae 0\n";
        // The checker resolves the orphan at the layer that owns types, so the
        // WHOLE definition is consistent -- literal, bindings, and references
        // all int-default, no variable left for a plug to choke on.
        let l = def_line(src, "ae");
        assert!(l.contains("(list-expr (elems) int-default)"), "orphan literal not defaulted: {l}");
        assert!(!l.contains("(tvar"), "orphan variable survived in the definition: {l}");
    }

    /// The zonk-and-default phase reaches an empty list in DIRECT position, not
    /// only through an alias. `list-length []` -- element observed only by its
    /// length -- defaults; called twice so the single-caller pass leaves the
    /// definition standing to inspect.
    #[test]
    fn an_orphan_empty_list_in_direct_position_defaults() {
        let src = "Chapter: T\n\nSection: S\n  count-empty : Integer -> Integer\n  count-empty (n) = list-length []\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (count-empty 1))\n   print-line-uni (show (count-empty 2))\n  end\n";
        let l = def_line(src, "count-empty");
        assert!(l.contains("(list-expr (elems) int-default)"), "direct empty not defaulted: {l}");
        assert!(!l.contains("(tvar"), "orphan survived: {l}");
    }

    /// An UNUSED binding of an empty list: the element is an orphan the phase
    /// defaults, independent of the plug's handling of the unused binding.
    #[test]
    fn an_unused_empty_list_binding_defaults_its_element() {
        let src = "Chapter: T\n\nSection: S\n  ret : Integer -> Integer\n  ret (n) = let e = [] in 42\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (ret 1))\n   print-line-uni (show (ret 2))\n  end\n";
        let l = def_line(src, "ret");
        assert!(!l.contains("(tvar"), "orphan survived in unused binding: {l}");
    }

    /// **A DEFINITION'S OWN GENERIC IS NOT AN ORPHAN.** An empty list typed as
    /// the definition's own type variable must keep that variable -- defaulting
    /// it would make a generic function monomorphic. The guard defaults only a
    /// variable the definition's type does not bind.
    #[test]
    fn a_generic_empty_lists_variable_is_not_defaulted() {
        let src = "Chapter: T\n\nSection: S\n  g : List a -> Integer\n  g (xs) = list-length (xs & [])\n\nSection: E\n  opening : Integer\n  opening = g [1, 2, 3]\n";
        let l = def_line(src, "g");
        assert!(l.contains("(list (tvar"), "generic element wrongly defaulted: {l}");
    }

    /// **A POLYMORPHIC DEFINITION SPELLS THE TYPE ITS OWN BODY WAS CHECKED
    /// WITH.** `ident : List a -> List a` reaches the wire as
    /// `(fn (list (tvar 2)) (list (tvar 2)))` -- the variable
    /// `instantiate-collect` minted for it -- and its parameter carries the
    /// same. The generalised `forall` is what REFERENCES instantiate from; it
    /// has no arrow to peel, and lowering that instead refused every
    /// polymorphic definition in the corpus.
    ///
    /// `codexir`'s bytes at `u56-candidate-sunday`, with `ident` called twice
    /// so the single-caller pass leaves it standing. Note the call sites carry
    /// `int-default`, resolved, while the definition keeps its variable.
    #[test]
    fn a_polymorphic_definition_keeps_its_own_type_variable() {
        let src = "Chapter: T\n\nSection: S\n  ident : List a -> List a\n  ident (xs) = xs\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (list-length (ident [1])))\n   print-line-uni (show (list-length (ident [2])))\n  end\n";
        assert_eq!(
            def_line(src, "ident"),
            r#"(def "ident" "T" (params (param "xs" (list (tvar 2)))) (fn (list (tvar 2)) (list (tvar 2))) (name "xs" (list (tvar 2))) 0 0)"#
        );
        assert!(
            def_line(src, "opening")
                .contains(r#"(name "ident" (fn (list int-default) (list int-default)))"#),
            "the call site resolves: {}",
            def_line(src, "opening")
        );
    }

    /// **AN ORPHAN SUM CONSTRUCTOR DEFAULTS ITS TYPE PARAMETER**, the same
    /// zonk-and-default the empty list gets, generalised to a nullary variant.
    /// `is-some None` never observes the `Maybe a`'s element, so its `a` is an
    /// orphan no context binds; the checker defaults it to int-default at the
    /// call site, keeping the IR hole-free. Upstream leaves the variable free
    /// and its zig plug refuses it ("type variable ... is not declared") -- this
    /// is a place our IR is the reference. The generic `is-some` DEFINITION
    /// still keeps its own variable; only the unconstrained USE is defaulted.
    #[test]
    fn an_orphan_sum_constructors_parameter_defaults() {
        let src = "Chapter: T\n\nSection: M\n  Maybe a =\n   | None\n   | Some (a)\n\n  is-some : Maybe a -> Boolean\n  is-some (m) = when m\n   is None -> False\n   is Some (x) -> True\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (is-some None))\n  end\n";
        let def = def_line(src, "is-some");
        assert!(def.contains("(tvar"), "the generic definition lost its variable: {def}");
        let op = def_line(src, "opening");
        assert!(
            op.contains(r#"(name "None" (ctd "Maybe" (args int-default)))"#),
            "orphan constructor not defaulted at the call site: {op}"
        );
        assert!(!op.contains("(tvar"), "orphan variable survived at the call site: {op}");
    }

    /// The orphan defaulting reaches a NESTED sum: `depth (Some None)` leaves the
    /// inner `None`'s parameter unconstrained, and the phase defaults it too, so
    /// no variable reaches the plug from the caller.
    #[test]
    fn a_nested_orphan_sum_constructor_defaults() {
        let src = "Chapter: T\n\nSection: M\n  Maybe a =\n   | None\n   | Some (a)\n\n  depth : Maybe (Maybe a) -> Integer\n  depth (m) = when m\n   is None -> 0\n   is Some (inner) -> when inner\n    is None -> 1\n    is Some (x) -> 2\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (depth (Some None)))\n  end\n";
        let op = def_line(src, "opening");
        assert!(!op.contains("(tvar"), "nested orphan variable survived at the call site: {op}");
    }

    /// A helper whose type variable lives ONLY in its return type --
    /// `make-empty : Integer -> List a` -- is generic where defined, and the
    /// single-caller inliner copies its body into the caller. Parameter/argument
    /// matching never reaches `a`; the call site's own type does (the checker
    /// resolved it, orphans defaulted), so the inlined `[]` takes `int-default`
    /// and no hole reaches the plug. Upstream carries the variable through.
    #[test]
    fn an_inlined_helpers_return_type_takes_the_call_sites_type() {
        let src = "Chapter: T\n\nSection: B\n  make-empty : Integer -> List a\n  make-empty (n) = []\n\nSection: M\n  opening : [Console] Nothing = act\n   print-line-uni (show (list-length (make-empty 0)))\n  end\n";
        let op = def_line(src, "opening");
        assert!(
            op.contains("(list-expr (elems) int-default)"),
            "inlined return type not taken from the call site: {op}"
        );
        assert!(!op.contains("(tvar"), "helper's return variable survived inlining: {op}");
    }

    /// A real literal types as `real` in the checker, as `infer-literal`
    /// says. Answering `error` for it typed every `let` whose value STARTS
    /// with one -- `if c then 0.0 else x`, `0.0 - x` -- as `error`, and every
    /// later read of that name carried it to the wire: 104 names over 24 of
    /// safari's 54 specs, and `sgn * hw` on an `error` operand chose `mul-int`
    /// over `mul-num`. Upstream's wire says `real` at all of them.
    #[test]
    fn a_let_headed_by_a_real_literal_reads_back_real() {
        let src = "Chapter: T\n\nSection: S\n  clamp : Real -> Real\n  clamp (x) =\n   let v1 = x * 2.0\n   in let v2 = if v1 < 0.0 then 0.0 else v1\n   in let sgn = 0.0 - v2\n   in v2 * sgn\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (real-to-int (clamp 1.0)))\n  end\n";
        let def = def_line(src, "clamp");
        assert!(def.contains(r#"(name "v2" real)"#), "v2 read back untyped: {def}");
        assert!(def.contains(r#"(name "sgn" real)"#), "sgn read back untyped: {def}");
        assert!(def.contains("mul-num"), "a real product chose the int operator: {def}");
        assert!(!def.contains("error"), "an error type reached the wire: {def}");
    }

    /// **`-n` IS A NEGATE NODE; `0 - n` IS A BINARY.** The two spell
    /// differently on the wire even though a reader would call them the same
    /// expression, and the negate carries its OPERAND's type. `codexir`'s
    /// bytes, with `neg2` called twice so it survives the single-caller pass.
    #[test]
    fn a_unary_minus_is_a_negate_node() {
        let src = "Chapter: T\n\nSection: S\n  neg2 : Integer -> Integer\n  neg2 (n) = -n\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (neg2 1))\n   print-line-uni (show (neg2 2))\n  end\n";
        assert_eq!(
            def_line(src, "neg2"),
            r#"(def "neg2" "T" (params (param "n" int-default)) (fn int-default int-default) (negate (name "n" int-default) int-default) 0 0)"#
        );
    }

    /// **A RECORD LITERAL EMITS ITS FIELDS IN THE ORDER THE EXPRESSION WRITES
    /// THEM, AND A FIELD ACCESS CARRIES THE DECLARATION'S SLOT.** Both halves
    /// measured: `P { py = ..., px = ... }` emits `py` first even though the
    /// declaration puts `px` first, and `p.py` is `"py/1"` because `py` is
    /// declared second.
    #[test]
    fn a_record_writes_its_fields_in_expression_order_and_reads_them_by_slot() {
        let decl = "Chapter: T\n\nSection: S\n  P = record { px : Integer, py : Text }\n\n";
        let calls = "\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (getx (mk 1)))\n   print-line-uni (show (getx (mk 2)))\n  end\n";
        let src = format!(
            "{decl}  mk : Integer -> P\n  mk (a) = P {{ px = a, py = \"z\" }}\n\n  \
             getx : P -> Integer\n  getx (p) = p.px\n{calls}"
        );
        assert_eq!(
            def_line(&src, "mk"),
            r#"(def "mk" "T" (params (param "a" int-default)) (fn int-default (record-ty "P" (args))) (record "P" (fields (field-val "px" (name "a" int-default)) (field-val "py" (text-lit "z"))) (record-ty "P" (args))) 0 0)"#
        );
        assert_eq!(
            def_line(&src, "getx"),
            r#"(def "getx" "T" (params (param "p" (record-ty "P" (args)))) (fn (record-ty "P" (args)) int-default) (field-access (name "p" (record-ty "P" (args))) "px/0" int-default) 0 0)"#
        );

        // Written out of declaration order, and emitted the way it is written.
        let swapped = format!(
            "{decl}  mk : Integer -> P\n  mk (a) = P {{ py = \"z\", px = a }}\n\n  \
             getx : P -> Integer\n  getx (p) = p.px\n{calls}"
        );
        assert!(
            def_line(&swapped, "mk").contains(
                r#"(fields (field-val "py" (text-lit "z")) (field-val "px" (name "a" int-default)))"#
            ),
            "got: {}",
            def_line(&swapped, "mk")
        );
    }

    /// **A BOUNDED INTEGER MEETING AN ORDINARY ONE ANSWERS THE LEFT.**
    /// `b + 1` over `Integer between 0 and 255` is `(int 0 255 ov-error)`;
    /// `1 + b` is `int-default`. Not the wider, not the narrower -- the left.
    #[test]
    fn arithmetic_on_a_bounded_integer_answers_the_left_operand() {
        let calls = "\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (w 3))\n   print-line-uni (show (w 4))\n  end\n";
        let right = format!(
            "Chapter: T\n\nSection: S\n  w : Integer between 0 and 255 -> Integer\n  w (b) = b + 1\n{calls}"
        );
        assert_eq!(
            def_line(&right, "w"),
            r#"(def "w" "T" (params (param "b" (int 0 255 ov-error))) (fn (int 0 255 ov-error) int-default) (binary add-int (name "b" (int 0 255 ov-error)) (int-lit 1) (int 0 255 ov-error)) 0 0)"#
        );

        let left = format!(
            "Chapter: T\n\nSection: S\n  w : Integer between 0 and 255 -> Integer\n  w (b) = 1 + b\n{calls}"
        );
        assert!(
            def_line(&left, "w").contains(
                r#"(binary add-int (int-lit 1) (name "b" (int 0 255 ov-error)) int-default)"#
            ),
            "got: {}",
            def_line(&left, "w")
        );
    }

    /// **A CONSTRUCTOR PATTERN CARRIES THE SCRUTINEE'S TYPE, A WILDCARD IS A
    /// BARE ATOM, AND EVERY BRANCH HAS A GUARD.** An unguarded arm carries
    /// `(bool-lit true)`, which the desugarer put there -- and note the
    /// lowercase: the source spells the constructor `True`, the wire spells the
    /// value.
    #[test]
    fn a_match_spells_its_patterns_against_the_scrutinee() {
        let decl = "Chapter: T\n\nSection: S\n  M =\n    | Some (Integer)\n    | Nowt\n\n";
        let calls = "\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (unwrap (Some 1)))\n   print-line-uni (show (unwrap Nowt))\n  end\n";
        let src = format!(
            "{decl}  unwrap : M -> Integer\n  unwrap (m) = when m\n    is Some (x) -> x\n    is Nowt -> 0\n{calls}"
        );
        assert_eq!(
            def_line(&src, "unwrap"),
            r#"(def "unwrap" "T" (params (param "m" (sum "M" (args)))) (fn (sum "M" (args)) int-default) (match (name "m" (sum "M" (args))) (branches (branch (ctor-pat "Some" (subs (var-pat "x" int-default)) (sum "M" (args))) (name "x" int-default) (bool-lit true)) (branch (ctor-pat "Nowt" (subs) (sum "M" (args))) (int-lit 0) (bool-lit true))) int-default) 0 0)"#
        );

        let wild = format!(
            "{decl}  unwrap : M -> Integer\n  unwrap (m) = when m\n    is Some (x) -> x\n    is otherwise -> 7\n{calls}"
        );
        assert!(
            def_line(&wild, "unwrap").contains("(branch wild-pat (int-lit 7) (bool-lit true))"),
            "got: {}",
            def_line(&wild, "unwrap")
        );
    }

    /// `True` in source is `true` on the wire -- the source names the
    /// constructor, the wire carries the value.
    #[test]
    fn a_boolean_literal_is_lowercase_on_the_wire() {
        let src = "Chapter: T\n\nSection: S\n  yes : Integer -> Boolean\n  yes (n) = True\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (show (yes 1))\n   print-line-uni (show (yes 2))\n  end\n";
        assert_eq!(
            def_line(src, "yes"),
            r#"(def "yes" "T" (params (param "n" int-default)) (fn int-default boolean) (bool-lit true) 0 0)"#
        );
    }

    /// **ONE TOKEN, THREE ATOMS.** `&` is `and` over Booleans, `append-text`
    /// over Text and `append-list` over a List, and the OPERAND type picks.
    /// Inferring Boolean for it unconditionally made `a & b & "!"` see a
    /// Boolean meeting a Text at the second `&` -- a disagreement that is not
    /// in the program.
    #[test]
    fn the_ampersand_is_three_operators() {
        let src = "Chapter: T\n\nSection: S\n  j : Text, Text -> Text\n  j (a) (b) = a & b & \"!\"\n\n  k : Boolean, Boolean -> Boolean\n  k (a) (b) = a & b\n\n  l : List Integer, List Integer -> List Integer\n  l (a) (b) = a & b\n\nSection: E\n  opening : [Console] Nothing = act\n   print-line-uni (j \"x\" \"y\")\n   print-line-uni (show (k True False))\n   print-line-uni (show (list-length (l [1] [2])))\n   print-line-uni (j \"p\" \"q\")\n  end\n";
        assert!(def_line(src, "j").contains("(binary append-text (binary append-text"), "{}", def_line(src, "j"));
        assert!(def_line(src, "k").contains("(binary and "), "{}", def_line(src, "k"));
        assert!(def_line(src, "l").contains("(binary append-list "), "{}", def_line(src, "l"));
    }

    /// **`[]` IS NOT ALWAYS A LIST.** An empty list has no element to speak
    /// for it, so its type is the bare variable the checker minted and the
    /// CONTEXT decides what that stands for. In linked-list position upstream
    /// emits a call to the `__linked-list-empty` builtin rather than a list
    /// literal, and the two spellings are not interchangeable below the IR.
    #[test]
    fn an_empty_list_in_linked_list_position_calls_the_builtin() {
        let src = "Chapter: T\n\nSection: S\n  e : Integer -> LinkedList Text\n  e (n) = []\n\n  p : Integer -> List Text\n  p (n) = []\n\nSection: E\n  opening : Integer\n  opening = list-length (p 1) + list-length (__linked-list-to-list (e 1))\n";
        assert!(
            def_line(src, "e").contains(
                r#"(apply (name "__linked-list-empty" (fn int-default (llist text))) (int-lit 0) (llist text))"#
            ),
            "{}",
            def_line(src, "e")
        );
        assert!(def_line(src, "p").contains("(list-expr (elems) text)"), "{}", def_line(src, "p"));
    }

    /// **THE CALLEE'S PARAMETER IS THE ARGUMENT'S EXPECTATION.** A lambda has
    /// nowhere else to get its parameter types from: nothing above a `for ...
    /// in` comprehension's synthetic span recorded one. Lowering the argument
    /// with no expectation left `error` in every slot -- seventy lifted
    /// lambdas of the compiler's own IR.
    ///
    /// At a POLYMORPHIC callee the parameter keeps the callee's own variable
    /// and the return is instantiated by what the body turned out to be --
    /// `lambda-recorded-ty` doing its half. This case is the concrete one,
    /// which needs no chapter but the test's own.
    #[test]
    fn a_lambda_peels_its_parameters_from_the_callee() {
        let src = "Chapter: T\n\nSection: S\n  twice : (Text -> Integer), Text -> Integer\n  twice (f) (s) = f s + f s\n\nSection: E\n  opening : Integer\n  opening = twice (\\t -> text-length t) \"ab\"\n";
        assert_eq!(
            def_line(src, "__lam_0"),
            r#"(def "__lam_0" "" (params (param "t" text)) (fn text int-default) (apply (name "text-length" (fn text int-default)) (name "t" text) int-default) 0 0)"#
        );
    }

    /// **A BINDER THAT SHADOWS IS RE-SPELLED**, and the references to it move
    /// with it. `binder-emitted` counts upward from `_1` until the name is
    /// free of BOTH the enclosing scope and the base -- and the base includes
    /// the builtins, which is why a `let max` is renamed in a chapter that
    /// never defines `max`.
    ///
    /// Twenty-two definitions of the compiler turned on this one rule.
    #[test]
    fn a_shadowing_binder_is_renamed_and_so_are_its_readers() {
        let src = "Chapter: T\n\nSection: S\n  f : Integer -> Integer\n  f (n) = let max = n + 1 in max\n\n  g : Integer -> Integer\n  g (n) = let a = n in let a = a + 1 in a\n\nSection: E\n  opening : Integer\n  opening = f 1 + g 2\n";
        // `max` is a builtin, so the very first binding of it already shadows.
        assert!(def_line(src, "f").contains(r#"(let "max_1" int-default"#), "{}", def_line(src, "f"));
        assert!(def_line(src, "f").contains(r#"(name "max_1" int-default)"#), "{}", def_line(src, "f"));
        // `a` is free, so the first one keeps its name and only the inner one
        // moves -- and the inner value still reads the OUTER `a`.
        assert!(
            def_line(src, "g").contains(
                r#"(let "a" int-default (name "n" int-default) (let "a_1" int-default (binary add-int (name "a" int-default) (int-lit 1) int-default) (name "a_1" int-default)))"#
            ),
            "{}",
            def_line(src, "g")
        );
    }

    /// **A DEFINITION WHOSE BODY IS A COMPREHENSION IS NOT AN INLINE
    /// CANDIDATE**, and it stays in the chapter even with one caller.
    ///
    /// That is entirely a question of ORDER. `once-binder-free` refuses an
    /// `IrLambda` by its default arm, so upstream -- which runs the pipeline
    /// on the lowered tree and lifts afterwards -- never sees this body as
    /// eligible. Lifting first turns the lambda into a name, the body becomes
    /// admissible, the definition is spliced into its one caller and vanishes.
    /// Five definitions of the compiler disappeared that way.
    #[test]
    fn the_pipeline_runs_before_the_lift() {
        // A comprehension desugars to a call of `map-list`, which a corpus
        // unit carries from ListUtils; a chapter without it is refused.
        let src = "Chapter: T\n\nSection: S\n  map-list : List a, (a -> b) -> List b\n  map-list (xs) (f) = map-list-loop xs f 0 (list-length xs) []\n\n  map-list-loop : List a, (a -> b), Integer, Integer, List b -> List b\n  map-list-loop (xs) (f) (i) (n) (acc) =\n   if i >= n then acc\n   else map-list-loop xs f (i + 1) n (list-push acc (f (list-at xs i)))\n\n  node : List Integer, Integer -> List Integer\n  node (xs) (k) = for x in xs -> x + k\n\n  ins : List Integer, Integer -> Integer\n  ins (xs) (k) = list-length (node xs k)\n\nSection: E\n  opening : Integer\n  opening = ins [1] 2\n";
        let all = ir(src);
        assert!(all.contains(r#"(def "node" "T""#), "node was inlined away:\n{all}");
        assert!(all.contains(r#"(name "node" ("#), "the call to node went too:\n{all}");
    }

    /// **`==` ON A TYPE WITH A GENERATED HELPER IS A CALL TO THE HELPER**,
    /// `lower-eq-dispatch`, and `/=` is `if call then False else True`. A
    /// type with arguments is called by its INSTANTIATED name and a list,
    /// which has no helper, stays a `binary eq`. The generated helper's own
    /// body is on the wire too, and its sub-patterns carry the FIELD types:
    /// every pattern in it shares one synthetic span, so those cannot come
    /// from the checker's table. Read off `codexir` at `8570fba1`.
    #[test]
    fn equality_on_a_sum_calls_the_generated_helper() {
        let src = "Chapter: T\n\nSection: S\n  Color =\n   | Red\n   | Green\n\n  Box a =\n   | Full (a)\n   | Empty\n\n  Pair =\n   | MkPair (Integer) (Box Text)\n\n  same : Color, Color -> Boolean\n  same (a) (b) = a == b\n\n  differ : Color, Color -> Boolean\n  differ (a) (b) = a /= b\n\n  same-box : Box Integer, Box Integer -> Boolean\n  same-box (a) (b) = a == b\n\n  same-list : List Integer, List Integer -> Boolean\n  same-list (a) (b) = a == b\n\n  same-pair : Pair, Pair -> Boolean\n  same-pair (a) (b) = a == b\n\n  count : Boolean -> Integer\n  count (b) = if b then 1 else 0\n\nSection: E\n  opening : Integer\n  opening = count (same Red Green) + count (differ Red Red) + count (same-box Empty Empty) + count (same-list [] []) + count (same-pair (MkPair 1 Empty) (MkPair 2 Empty))\n";
        let all = ir(src);
        let color = r#"(fn (sum "Color" (args)) (fn (sum "Color" (args)) boolean))"#;
        // `same` and `differ` have one caller each and are inlined into
        // `opening`, so the call is read there, with `Red` for `a`.
        assert!(
            all.contains(&format!(r#"(apply (apply (name "__eq_Color" {color}) (name "Red" (sum "Color" (args))) (fn (sum "Color" (args)) boolean)) (name "Green" (sum "Color" (args))) boolean)"#)),
            "{all}"
        );
        assert!(
            all.contains(&format!(r#"(if (apply (apply (name "__eq_Color" {color}) (name "Red" (sum "Color" (args))) (fn (sum "Color" (args)) boolean)) (name "Red" (sum "Color" (args))) boolean) (bool-lit false) (bool-lit true) boolean)"#)),
            "/= is an if: {all}"
        );
        assert!(
            all.contains(r#"(name "__eq_Box@Integer" (fn (ctd "Box" (args int-default)) (fn (ctd "Box" (args int-default)) boolean)))"#),
            "{all}"
        );
        assert!(all.contains(r#"(binary eq (name "a" (list int-default)) (name "b" (list int-default)) boolean)"#), "{all}");
        // The helper's body: field 0 is an Integer, field 1 calls Box's
        // instantiated helper, and both `MkPair` patterns carry `Pair`.
        let pair = def_line(src, "__eq_Pair");
        assert!(pair.contains(r#"(ctor-pat "MkPair" (subs (var-pat "__exf0" int-default) (var-pat "__exf1" (ctd "Box" (args text)))) (sum "Pair" (args)))"#), "{pair}");
        assert!(pair.contains(r#"(binary and (binary eq (name "__exf0" int-default) (name "__eyf0" int-default) boolean) (apply (apply (name "__eq_Box@Text""#), "{pair}");
    }

    /// **A BARE CONSTRUCTED TYPE IS A NAME, NOT AN ANSWER**, and the RESOLVE
    /// phase is what turns it into one. `__self-type-defs` is declared
    /// `List TypeBinding` in the builtin table and reaches lowering as
    /// `(list (ctd "TypeBinding" (args)))`; what it MEANS is whatever this
    /// unit declares `TypeBinding` to be.
    ///
    /// The three answers were read off `codexir` with this program, a record
    /// declaration, and a variant declaration. Only two are here: the
    /// undeclared case needs `TypeBinding` interned to reach the builtin
    /// table at all, so `resolve_types`' own tests carry that one.
    #[test]
    fn a_bare_constructed_type_resolves_to_what_the_unit_declares() {
        let head = "Chapter: T\n\nSection: S\n";
        let tail = "  count : Integer -> Integer\n  count (n) = let defs = __self-type-defs in list-length defs\n\nSection: E\n  opening : Integer\n  opening = count 1\n";
        let record = format!("{head}  TypeBinding = record {{\n   tb-name : Text\n  }}\n\n{tail}");
        let variant = format!("{head}  TypeBinding = | TbA | TbB\n\n{tail}");
        assert!(
            def_line(&record, "count").contains(r#"(list (record-ty "TypeBinding" (args)))"#),
            "{}",
            def_line(&record, "count")
        );
        assert!(
            def_line(&variant, "count").contains(r#"(list (sum "TypeBinding" (args)))"#),
            "{}",
            def_line(&variant, "count")
        );
    }

    /// **A CONSTRUCTED RECEIVER INSTANTIATES THE FIELD**, and the node under
    /// the access is retyped to the record.
    ///
    /// `SortPartition a` arrives as a `ConstructedTy` carrying the caller's
    /// own argument. Reading the DECLARED field type past it answers `List a`
    /// with `a` still the declaration's own name, which then unifies with the
    /// enclosing definition's variable and pins it -- `qsort-by`'s four
    /// parameters spelled `(tycon "a")` where the oracle spells `(tvar 28)`.
    #[test]
    fn a_field_read_off_a_generic_record_is_instantiated() {
        let src = "Chapter: T\n\nSection: S\n  Box (a) = record {{ bx : List a, n : Integer }}\n\n  wrap : List a, Integer -> Box a\n  wrap (xs) (i) = Box {{ bx = xs, n = i }}\n\n  pick : List a, Integer -> List a\n  pick (xs) (n) = (wrap xs n).bx\n\nSection: E\n  opening : Integer\n  opening = list-length (pick [\"x\"] 1)\n".replace("{{", "{").replace("}}", "}");
        let line = def_line(&src, "pick");
        assert!(!line.contains("tycon"), "{line}");
        // The receiver is retyped to the record, carrying the caller's own
        // argument -- `(ctd "Box" ...)` is what it says without that step.
        assert!(line.contains(r#"(record-ty "Box" (args (tvar"#), "{line}");
    }

    /// **THE TWO ARMS OF AN `if` MEET.** Without that, a polymorphic
    /// constructor in one of them never learns what it stands for.
    ///
    /// Read off `codexir` on a ten-line unit: `if n > 0 then Just "x" else
    /// None` types the `None` as `Maybe Text`, and ours said
    /// `Maybe (tvar 307)`.
    #[test]
    fn the_arms_of_an_if_meet() {
        // `Maybe` is declared here rather than cited, so the test needs no
        // checkout.
        let src = "Chapter: T\n\nSection: S\n  Maybe (a) = | None | Just (a)\n\n  pick : Integer -> Maybe Text\n  pick (n) = if n > 0 then Just \"x\" else None\n\n  use2 : Integer -> Integer\n  use2 (n) = when pick n is Just (t) -> text-length t is None -> 0\n\nSection: E\n  opening : Integer\n  opening = use2 1 + use2 2\n";
        let all = ir(src);
        assert!(all.contains(r#"(name "None" (ctd "Maybe" (args text)))"#), "{all}");
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

