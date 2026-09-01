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

`cover` also splits the parse-error count. `codex/test/errors/` holds programs
the compiler is SUPPOSED to decline, so a diagnostic we raise there is output
rather than a defect, and counting the two together gives a total that goes UP
as the front end improves. They are reported on their own line. The gold bank's
`refused.tsv` is the authority; the directory test is a heuristic.

**What the scale gate cannot see.** It proves the grammar is TOTAL -- every
definition in the compiler's own 64 chapters parses, with no unread body and no
error -- and it says nothing about whether the shape is RIGHT. Giving `+` and
`*` the same precedence leaves it entirely green. Shape is guarded by unit
tests today and by the IR golds later; neither `parse.truth` nor
`desugar.truth` inspects an expression at all.

`cover` also reports what the parse ALONE cost, separately from the sweep's
own -- a second tokenize, a dozen tree walks. Compile speed is this project's
first goal, and reporting them together would hide a regression inside the
gate's cost. Measured over the checkout: 16.3 MB in 0.37 s, ~42 MB/s, against
codexir's ~150 KB/s.

**What the gate promises is narrow on purpose.** Coverage, homelessness and
unread patterns are at zero today and must stay there. The inventory numbers
beside them -- unread type-definition bodies, blocks that ran to the end of the
file, bodies not yet structured -- are the size of the work still to do, and a
gate that is red for a month is a gate nobody reads. `unread type definition
bodies == 0` was in the test for one commit while the number was nine, and the
run was red the whole time without anybody noticing.

The one pattern number that IS a gate is `token(s) in pattern position not
understood`, which must be zero: upstream's pattern parser never fails, folding
anything it does not recognise into the same wildcard the author could have
written, and keeping the two apart is what makes the second countable. It is
reported next to the total pattern count, because a zero from a parser that
never ran looks exactly like a zero from one that works.

## The IR chapter preamble: 1,012 programs, and the compiler itself

Everything above `(defs` in an IR file is fixed by syntax alone -- chapter,
title, prose, pblocks, anns, sections, ctors, eff-ops, grounds, type-defs --
and it is present in every gold. Everything BELOW it carries an inferred type
on every node, so reaching that needs scope, check and lower.

    irdump preamble <unit.codex> [chapter-name]
    irdump grade <units-dir>              against $CODEX_GOLDS/ir/*.ir

    codex corpus     1012 of 1012 byte-identical
    safari app         27 of 27
    the compiler        1 of 1   -- 2.98 MB, 310 lines, in 0.9s

The input must be a RESOLVED unit; the ladder's `resolve_corpus.py` writes
them, and safari's `build/*-unit.codex` already are. A gold names sections from
`Foreword ListUtils` and constructors from `Foreword Tuple` that appear nowhere
in the program's own file.

It is a SLICE and it is worth saying which: the preamble is 7.7% of the corpus
IR by bytes and 0.5% of safari's, and type definitions are three quarters of
it. Every expression body is still unchecked by anything but unit tests.

`(chapter "...")` is a DRIVER PARAMETER -- `compile-frontend source "Program"
flags` -- so `grade` reads that one field from the gold and COUNTS how often it
had to. On the corpus it never has to, which is what says our derived rule
matches `native/codexir`.

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
