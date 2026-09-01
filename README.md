# rust-codex-compiler

A native Rust front end for Codex: `.codex` in, standard Codex IR out. Layered
the way Cobblestone is layered -- lexer, parser, desugarer, scope, check, lower
-- and stopping at the IR. **The primary goal is compile speed.** Linting and
bug-hunting come later, on the same front end.

## Four rules this repo is built under

1. **Canonical equality is the gate; byte-identity is a ratchet.** The IR text
   publishes the checker's unification-variable numbers, which are a function
   of allocation ORDER. Demanding byte-identical IR would demand reproducing
   Cobblestone's walk and would foreclose ever improving it. Compare with ids
   renumbered in first-appearance order; count byte-identical programs
   separately and ratchet that up, never down.
2. **Lossless CST from day one.** Trivia -- spaces, skipped prose, exact spans
   -- is kept, and the AST is lowered from it. This is the one place we
   deliberately do not copy Cobblestone, which throws trivia away. Retrofitting
   a CST later is a rewrite, and the linting goal wants one.
3. **Golds come from `master-plus-outbound`**, not plain master: two of our ten
   open PRs move front-end output, and golds cut against unpatched master would
   encode bugs we reported.
4. **Clean by construction.** No code generation in the repo, no `target/`, no
   vendored golds, no benchmark output. Point `CARGO_TARGET_DIR` at a sandbox.

## Building

    export CARGO_TARGET_DIR=~/runs/<sandbox>/rust-target
    cargo build --release

## Validating

Two gates, and they are independent.

**Losslessness needs no oracle.** Every byte of the source is covered by
exactly one token or one piece of trivia, so `concat(tokens) == source` is a
check the file itself answers. It runs over every `.codex` file in the
Cobblestone checkout -- thousands of them -- with no gold set and no compute.

    cargo run --release --bin lexdump -- --check-lossless <dir>

**Token agreement needs the ladder's `lex.truth`**, a bare-metal dump of
Cobblestone's own lexer over its own `Syntax/Lexer.codex`: kind, offset+length,
line, column, text. Our stream projected free of trivia must equal it.

    cargo run --release --bin lexdump -- --truth <file.codex> | diff - lex.truth

The truth is ONE subject and exercises 41 of the 92 token kinds. It starts a
lexer; it cannot finish one. The corpus finishes it.

**The parser has the same pair, and the shallow one is shallower.**
`parse.truth` records the DECLARATION layer only -- each definition's name,
parameter count, annotation count, position and chapter, plus the chapter's
sections, type definitions and counts. It says nothing whatever about
expression structure.

    cargo run --release --bin parsedump -- truth <file.codex> | diff - parse.truth
    cargo run --release --bin parsedump -- cover <dir>

`cover` is coverage AND homelessness, and the second half was added because the
first was measured to be too weak: a parser deliberately broken to stop
consuming definition bodies still passed a pure coverage check, because the
orphaned tokens simply reappeared as loose lines and were still counted exactly
once. Requiring that almost no token sit outside a named construct catches it --
367 loose tokens across the compiler's 64 chapters when healthy, 357,339 when
broken.

**What the scale gate cannot see.** It proves the grammar is TOTAL -- every
definition in the compiler's own 64 chapters parses, with no unread body and no
error -- and it says nothing about whether the shape is RIGHT. Giving `+` and
`*` the same precedence leaves it entirely green. Shape is guarded by unit
tests today and by the IR golds later; neither `parse.truth` nor
`desugar.truth` inspects an expression at all.

## `char-code` is not ASCII

Codex's `char-code` is a private frequency-ordered alphabet: 1 newline, 2
space, 3..12 the digits, 13..38 lowercase as `etaoinshrdlcumwfgypbvkjxqz`,
39..64 uppercase at lowercase+26, 65..96 punctuation. So `char-code 'A'` is
41, not 65, and it is **constant-folded into the IR** -- a front end that folds
it to 65 differs from the golds on every program containing a character
literal. `src/charcode.rs` carries the table; the ladder's `charcode_probe.py`
derives it from the compiler and checks it structurally. Do not hand-edit it.

Two pieces of Cobblestone read as bugs until you know this and are correct:
`Lexer.codex` classifies uppercase with `c >= char-code 'E' & c <= char-code
'Z'` (a range test -- 'E' is the lowest-coded uppercase letter, 'Z' the
highest), and `ChapterScoper.codex` lowercases with `c - 26`.
