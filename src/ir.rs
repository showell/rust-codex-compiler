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
/// (`opening.codex:798`).
pub fn emit_defs(ch: &Chapter) -> Result<String, String> {
    let (bindings, st, tds) = crate::check::check_chapter_full(ch);
    emit_defs_checked(ch, &bindings, &st, &tds, &IR_EMIT_ROOTS)
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

pub fn emit_defs_checked(
    ch: &Chapter,
    bindings: &[Binding],
    st: &UnifyState,
    tds: &TypeDefs,
    roots: &[&str],
) -> Result<String, String> {
    let keep = reachable(ch, roots);
    if keep.is_empty() {
        return Err("no root reached: the chapter defines none of ir-emit-roots".into());
    }
    // **A LIFTED NAME IS A NAME THE CHAPTER'S TABLE NEVER INTERNED.** `Sym` is
    // an index into the table that made it, so `__lam_0` needs a table that
    // holds it. Interning is append-only, so a clone extended with the lifted
    // names leaves every existing `Sym` meaning exactly what it did.
    //
    // `__linked-list-empty` is the same case one stage earlier: lowering
    // WRITES that call for an empty list in linked-list position, and no
    // source has to have named it.
    let mut syms = ch.syms.clone();
    let ll_empty = syms.intern("__linked-list-empty");
    let mut defs = Vec::new();
    {
        let cx = crate::lowering::Lower::new(&syms, bindings, st, tds, ll_empty);
        for d in ch.defs.iter() {
            defs.push(crate::lowering::lower_def(d, &cx)?);
        }
    }
    let defs = crate::lambda_lifting::lift_lambdas(defs, &mut syms);
    let defs = crate::ir_passes::pipeline(defs, &syms);
    let defs = crate::ir_passes::prune_unreachable_roots(defs, roots, &syms);
    Ok(crate::ir_text::emit_defs(&syms, &defs))
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

