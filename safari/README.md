# Safari, driven from the Rust side

Everything here depends on a **safari-codex checkout** and nothing here is
vendored. `SAFARI_ROOT` points at it (default `~/showell_repos/safari-codex`).

    ./run.sh      the fourth arm: safari's own checks, through our interpreter
    ./bench.sh    time the interpreter on a fixed set of safari units

## The fourth arm, and why it needs no gold

safari-codex bundles each check into `build/<mod>-unit.codex` and compiles that
same unit to `build/<mod>` with codexzig. After its `./harness/run.sh` both are
already sitting there. So this needs no gold and no fixture:

> **ONE SOURCE, TWO INDEPENDENT IMPLEMENTATIONS, run now and diffed.**

Cobblestone's front end and emitter on one side; our lexer, parser, desugarer
and interpreter on the other, sharing nothing below the text. That is what
makes a disagreement attributable -- and it is the only oracle in this repo
that sees MEANING rather than shape. Five byte-comparison oracles are one
oracle, and `and` failed to short-circuit under all of them.

## `literal_main` MUST differ

`run.sh` **fails if the two arms ever agree** on it. It is FINDINGS 1B's repro:
Cobblestone accumulates a 19-digit Real literal into a wrapping i64 and we read
it as an f64. A second front end that does not reproduce the bug is the
evidence, so agreement there would mean we had acquired the bug.

## It is slow, and the number is not close

Measured on this box against the Debug binaries safari's `run.sh` builds:

    render   2.5s there, minutes here
    ride     1.3s there

The light checks are instant; the ones that simulate finish, but not quickly.
So each side is bounded (`ZIG_SECS`, `RUST_SECS`) and the five units in
`run.sh`'s `HEAVY` list are held back unless `SAFARI_ALL=1`. That list carries
each one's step count, which is the honest measure of why. A tree-walking interpreter over persistent lists is
what that costs today.

## Benchmarking

`bench.sh` is **not a gate** -- nothing in it fails. The number to watch is
steps per second, not seconds, because seconds are about this machine on this
day. Run it before and after any attempt to make the interpreter faster.

`ARITH_UNIT` optionally adds the transpiler's arith sample. Both scripts
document their own knobs and quirks; this file is the why.
