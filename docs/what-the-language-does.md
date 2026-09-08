# What the language does that a reasonable implementation gets wrong

Moved out of the ladder's memory on 2026-09-08. Every rule here was paid for by
a diff against `codexir` or `codexcheck`; none is a guess. Memory holds Steve's
rulings and the working rhythm -- facts about the CODE belong beside the code,
where they can be checked against it.

`docs/charcode.md` carries the frequency-ordered alphabet -- read it before
touching literals -- and is not repeated here.

## What each layer guarantees

Repo pin `9ef2a13`, clean, pushed. Crate `codexc`. Build with
`export CARGO_TARGET_DIR=<a sandbox path>` -- ruling 4, nothing lands in-repo.

- **Lexer, DONE.** Byte-identical to `lex.truth` on the first run -- 5,335
  tokens, every span. Lossless: trivia (`Spaces`, `SkippedProse`) is emitted so
  `concat(tokens) == source`. 2,695 files / 16.3 MB in 0.147s (~111 MB/s;
  `codexir` is ~150 KB/s).
- **Parser: document layer, expressions, type expressions, patterns, type
  definitions and the four BLOCK forms, DONE.** `parse.truth` byte-identical. Over master-plus-outbound:
  2,695 files, 39,871 definitions, **46,770 patterns in 17,618 match arms (706
  alternating, 9 guarded), 0 tokens in pattern position not understood**, 2,414
  type definitions with 7,586 record fields and 472 variants of 2,514
  constructors, 3,723 act blocks of 14,522 statements, 26 handlers of 29
  clauses. 65 tests.
- **THE IR CHAPTER PREAMBLE ALL BUT MATCHES.** 1,011 of 1,012 codex programs
  byte-identical, re-measured 2026-09-04 against bank `53b3b2137644` — the
  file previously said 1,012 of 1,012, so ONE drifted and nobody noticed.
  27 of 27 safari units and the compiler itself (2.98 MB, 310 lines, 0.9s). `irdump grade <units-dir>` against
  `$CODEX_GOLDS/ir/*.ir`.
- **DESUGAR: `desugar.truth` byte-identical, and 1,584,224 AST expression
  nodes over 39,760 definitions with 9 error nodes** (6 in `test/errors/`,
  ZERO in compiler/foreword/plugs/os). `src/ast.rs` is `AstNodes.codex`
  variant for variant. Desugar runs at ~15 MB/s.
- **SPEED, measured on its own: 16.3 MB parsed in 0.37s, ~42 MB/s** -- against
  codexir's ~150 KB/s, so ~280x. `parsedump cover` reports the parse time
  separately from the sweep's own cost, because reporting them together hides a
  regression inside the gate.
- **CST is lossless BY CONSTRUCTION**: the builder only eats the next token and
  `finish()` refuses a short tree; `checkpoint`/`wrap_from` give the Pratt
  parser its left-folding. `Node::shape()` renders kinds alone for precedence
  tests -- do NOT slice its rendered text, take the child node.

- **THE INTERPRETER, `codexrun`.** Compiles the desugared AST to a RUN FORM
  (`src/code.rs`) and walks that -- no types, no IR, no zig, no guest -- so it
  shares NOTHING with the other arms below the text and a disagreement is
  attributable. It is also **the first oracle here that
  sees MEANING rather than shape**; five byte-comparison oracles are one
  oracle, and `and` failing to short-circuit was invisible to all of them.
  Tail calls are trampolined (`Step::Done | Step::Call`), so iteration written
  as recursion does not grow the Rust stack.
- **SPEED WORK IS RECORDED IN GIT, NOT HERE.** Two results outlived their
  measurements and are design rather than history: **a name is a `Sym`** (an
  index into a `SymTab` -- four bytes, `Copy`, compares as an integer;
  `src/symbol.rs`), and **the interner hashes with FNV, not SipHash**, because
  the keys are identifiers and there is no adversary. Re-measure before quoting
  any figure; `codexrun bench` and `safari/bench.sh` are the instruments.
- **`./safari.sh` -- the fourth arm, from the OUTSIDE.** safari-codex compiles
  `build/<mod>-unit.codex` to `build/<mod>` with codexzig, so both halves are
  already on disk after its `./harness/run.sh`: one source, two implementations,
  no gold in between. **25 of 27 units byte-identical**, render and ride
  included. `literal_main` differs AS IT MUST -- FINDINGS 1B's repro, where
  Cobblestone accumulates a 19-digit Real literal into a wrapping i64 and we
  read it as an f64; the script FAILS if the two ever agree, because a second
  front end not reproducing the bug is the evidence.

### The parser reads the whole checkout

    0 bodies not yet structured        0 annotation types not fully read
    2 parse errors, both in `parser-resync.codex` (a negative test)
    99.5% of files read whole

Nothing is a token bag. `desugar.truth` is byte-identical and `desugardump
cover` is the baseline-free half.

**THE NEXT UNIT IS SCOPE + CHECK + LOWER** -- the expression bodies, whose
SHAPE nothing checks today but 65 unit tests and the interpreter. The preamble
oracle is the declaration layer only: 7.7% of the corpus IR by bytes, 0.5% of
safari's.

**Owed inside desugar:** the synthesis passes are not written --
`synth-family-member-defs`, `synth-conversion-defs`, `synth-derived-defs`,
`synth-instance-defs`, `rewrite-constrained-defs`, `insert-dicts-at-call-sites`.
The def count is the plain translation and says so.

**Owed on the way: the effect row.** `[Console, Device.Block "scope", r]` is
taken whole by both `types::parse_effect_type` and `block::effect_row`.
Upstream's `parse-effect-names` separates names, scope literals and the
row-variable tail, and raises `cdx-row-tail-decorated` and `cdx-row-two-tails`.

### Rules a reasonable guess gets BACKWARDS (each one cost a fix)

- **PATTERNS.** A constructor's fields are PARENTHESIZED, one group each --
  `Cons (h) (t)`, never `Cons h t`; patterns are not applications. `(x)` is not
  a tuple, only a comma builds one. `Vector [a, b]` is its own form, by the
  constructor's TEXT. **`when` after a pattern is a GUARD**, and `|` separates
  alternative patterns for one body. Upstream never fails: anything
  unrecognised becomes a WildPat, so we split that out as `ErrPat` to keep it
  countable.
- **A match arm continues when it starts on the SAME LINE AS THE ARM BEFORE IT
  or at the arms' column.** Upstream's own prose records what pinning that to
  the line the match started on cost: arms silently dropped, `is otherwise`
  included.
- **`let` binds a LIST and the comma is optional**; `let (a, b) = p` binds a
  pattern and ENDS the list. `induction on n` takes an ATOM, not an expression.
- **TYPE DEFS.** A variant does not need its leading pipe -- `Colour = Red |
  Green` is a variant and `Alias = Integer` is not, and only a pipe before the
  end of the line separates them. A record field name may be a KEYWORD.
  `unit family` is a list of `Member = <factor>` lines, told from `unit T` by an
  ordinary identifier. A type parameter may be parenthesised, and missing that
  is SILENT -- 26 read as value definitions with capitalised names.
- **DESUGAR rewrites six forms that have NO AST node**: `(a,b)` -> `MkTup2 a b`;
  `for x in xs -> b` -> `map-list (\x -> b) xs`; `(e)` -> `e`; **`not x` ->
  `x == False`** (there is no negation node; `AUnaryExpr` is arithmetic
  negation alone); **`a |> f` -> `f a` with the operands SWAPPED**; `s in rest`
  -> `let __seq = s in rest`. Application is CURRIED, one argument per node.
  `is A | B -> body` FANS OUT into one arm per pattern, each with its own copy
  of the body, related by `alt-group`; an unguarded arm gets a `True` literal.
- **`===` is the propositional equality, NOT `==`**, and `=>` is a class
  constraint. Both live in `parse-type-continue`, and both only turn up inside
  a `claim`, so nothing finds them until `claim` parses.
- **A field assignment can be the LEFT of a SEQUENCE.** `port.a = .. in port.b
  = .. in port` is `SeqExpr`; inside a `let` the join is `in` and it is taken
  ONLY after a field assignment; in a def body there is no join at all, the
  next statement just sits further right.
- **ONE stray line after a body is upstream's RESYNC** (`if column > 3 then
  skip-to-next-line`), not a gap -- a source may write three `end`s for two
  `act` blocks. A RUN of real code still is a gap. Counted separately.
- **`claim`, `punctual` and `bounded` are MODIFIERS** on the definition that
  follows, not names. `qed` closes a proof.
- **BLOCKS: `with` and `with-timeout` have NO `end`.** A handler runs to the
  last of its clauses; a `with-timeout` to the end of its body. A clause STARTS
  ON ITS OWN LINE (the body is an ordinary expression and newlines are
  significant), needs at least one parameter to BE a clause, and its LAST
  parameter is the resume continuation. `trying`'s words -- `times`, `falling`,
  `back`, `to`, `on`, `failure` -- are ordinary identifiers matched by TEXT.
- **A prose block crosses BLANK LINES.** Stopping at one made the next
  paragraph look like an unread body.

- Structure is COLUMNS -- 1 header, 2 prose, **3 exactly** an item, deeper a
  continuation. `>= 3` reads the `of` in a `Page 1 of 3` footer as a definition.
- `grounds`/`cites`/`quotes` are top-level DECLARATIONS, not definitions.
- The body starts AFTER a newline; a Newline in atom position eats the body.
- Newlines are significant OUTSIDE brackets only -- that is CDX1070's cause.
- A minus TOUCHING its operand is an argument and wraps ONE atom.
- `not` takes a whole comparison; minus does not.
- A field name may be a KEYWORD but NOT a TypeIdentifier.
- `for x in xs -> body` is a comprehension; `for`/`all` are plain identifiers.
- A prose block's continuation lines are indented past column 3 and are not code.
- Title joining inserts a space only when the last byte written AND the first
  byte arriving are both alphanumeric (`Header Scanning(streaming)`).
- Types: a comma and an arrow build the SAME right-nested node; a chained arrow
  is REFUSED; a comma before `ident :` does not continue the type; a paren is a
  tuple only by lookahead (comma at depth 0, no arrow); and inside a tuple the
  comma SEPARATES, so the element parser must refuse it.

### What validates what -- read before trusting a green run

- **No rung truth checks expression SHAPE.** `parse.truth` AND `desugar.truth`
  are declaration-level dumps. `check.truth`/`lower.truth` are CUMULATIVE
  (parse+desugar+scope+check[+lower]) but the subject is `Fib`, 85 tokens. They
  do carry real counters: `resolve-errors`, `top-level-names`, `type-bindings`,
  **`substitutions`, `next-id`, `expr-types`**.
- **The scale gate is blind to shape.** `parsedump cover` proves the grammar is
  TOTAL, not RIGHT: giving `+` and `*` equal precedence leaves it fully green
  while the shape tests fail. Shape rests on unit tests until the IR golds.
- **Coverage alone was measured too weak**: a parser broken to stop consuming
  bodies passed it, the orphans reappearing as loose lines counted once each.
  The gate is coverage AND homelessness (367 loose tokens healthy, 357,339
  broken).
- "still flat" means CHILDLESS. Counting the wrapper reported 4,858 flat types
  at the moment they all gained structure.

## CCE tier-1 is a BLOCK MAP, not Unicode order

`is-tier1-letter-cp` is `cp - 128 < 896` -- a range on the CCE value, which is
tier-1 blocks 0..5, exactly `cce-is-letter-ext`. **Transcribing that range and
handing it a UNICODE codepoint is wrong and looks right**: `é` (233) passes by
luck, `д` (1076) fails. `cce-tier1-block-bases` in `foreword/core/CCE.codex`
maps CCE 128.. onto Unicode 128 (256 wide), then **Cyrillic at 1024**, Greek at
880, Arabic 1536, Hebrew 1424, Devanagari 2304 -- 128 wide each. Classify the
Unicode codepoint against those six ranges.

`test/ident-letters.codex` has `дом` in it and is banked CLEAN; that is the
oracle. Also: a CCE tier-1 character is ALWAYS two bytes, the same character in
UTF-8 may be three (Devanagari), so the lead-byte test is "starts a multi-byte
sequence" and the codepoint decides.

## A block with no `end` is ACCEPTED, silently

Upstream's `parse-act-stmts` answers `is-done` with a finished block and no
diagnostic. Three checkout files end mid-`act` and `ecdsa-p384` is **banked
clean**. So a truncated source compiles. Counted, not gated, on our side.
**Candidate finding, not yet verified enough to send.**

## The preamble oracle, and the rules only it could teach

`irdump grade <units-dir>` compares the IR chapter header -- everything above
`(defs` -- against `$CODEX_GOLDS/ir/*.ir`. It is the ONLY whole-corpus oracle
before the type checker, because every node below `(defs` carries an inferred
type. **It is a slice: 7.7% of the corpus IR by bytes, 0.5% of safari's, three
quarters of it type definitions. Every expression body is still unchecked by
anything but unit tests.**

Feed it RESOLVED units (`resolve_corpus.py`; safari's `build/*-unit.codex`
already are). Golds: `~/golds/53b3b2137644` (codex),
`~/golds/safari-0784a36b2874-cx-939d57187a37` (safari, cut by
`bank_safari_golds.py`), and the compiler's own pair sits in
codex-zig-transpiler as `generated/codexzig-subject.codex` +
`generated/codexzig.ir` (CCE -- decode with that repo's `cce.py`).

Ten rules it taught that reading Cobblestone had not:

- **`ctor-names` is SORTED BY CHAR-CODE, not alphabetically.** It is a
  `SkipListText`; `text-compare` is a builtin over `Text`; `Text` is CCE; so
  byte order IS char-code order. `E`=39 `N`=44 `M`=52 `J`=61.
- **A record field name may be a keyword IN THE EMITTER too** -- `SourceSpan`
  has a field called `end`.
- **A bound may be negative** (`EffectRow.tail-id` is -1).
- **A unit type's own name is a constructor**, and a **unit FAMILY is an
  ordinary `unit-def` over Integer**.
- **A type application is CURRIED**: one argument per `a-app`.
- **`join-title-parts` tests CHARACTERS, not bytes** -- a CCE tier-1 letter
  counts, so Cyrillic keeps its spaces.
- **A class dictionary's tparams are an INSTANCE COUNT** (`> 1` -> `["a"]`),
  never free-variable analysis.
- **`Real approximate trapping` is ONE atom**, `(a-named
  "real-approx-trapping")`.
- **`1 Minute = 60 Second` is a unit conversion**, and no token KIND says it
  starts an item.
- **`(chapter "...")` is a DRIVER PARAMETER** -- `compile-frontend source
  "Program" flags`. codexir passes the unit's own chapter; the transpiler's
  guest driver passes the literal `"Program"`. `grade` reads that one field
  from the gold and counts how often it had to.

## `\r` is SKIPPED by the lexer, and that arm is LIVE

`scan-token`'s first branch is `if c == cc-cr then scan-token (advance-char
s)`, and **`cc-cr : Integer = -1` is what `char-code-at` answers for a byte the
alphabet does not map** -- not "a value no byte can equal". Reading it the
second way gave `\r` an ErrorToken and cost the majority of every "not
understood" count: bodies 519 -> 248, unread annotation types 286 -> 20,
unread type-def bodies 41 -> 9, all from fifteen CRLF files.

**The gold IR settles it with no run:** `foreword/ai/DiffusionScheduler.codex`
has `record {\r\n` and is banked clean with `NoiseSchedule` carrying every
field. An ErrorToken between the brace and the first field would have left that
record empty. The byte is TRIVIA here, never dropped -- `concat(tokens) ==
source` needs no oracle and must hold.
