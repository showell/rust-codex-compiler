# Known gaps

What is not covered, and what has gone stale. Written so a green run is not
mistaken for a finished one.

## THE GOLD BANK IS STALE AT UPDATE 54

`$CODEX_GOLDS` (`~/golds/53b3b2137644/`) was cut at `master-plus-outbound` with
seed `B066CEB5`. **Update 54 moved every stage it grades** -- Lexer +122,
Parser +97, Desugarer +42, TypeChecker +324, Unifier +94, Lowering +260 -- so a
diff against it today measures the UPDATE and not our progress.

Nothing here is wrong; the comparand is. `irdump grade` and the `truth` gates
are not meaningful again until the bank is re-cut against U54, which needs the
ladder and a box. Until then, treat a red row as unattributable rather than as
a defect on this side.

**The gates that need no GOLD BANK are unaffected**, which is most of the
reason they exist: `lexdump lossless` and `parsedump cover` need no oracle at
all, and `codexrun sweep` and `safari/run.sh` have oracles of their own -- a
`.expected` beside each unit, and the codexzig binary built from the same
source. None of the four reads the bank.

## No byte oracle sees an expression

Every gold-backed gate in this repo inspects the DECLARATION layer or the IR
PREAMBLE. `parse.truth` says nothing about expression structure.
`desugar.truth` would pass a desugarer that answered `Error` for everything.
`irdump grade` stops above `(defs`.

Expression shape is guarded today by `cargo test` and by the interpreter, and
neither is a byte oracle. Reaching a real one needs check and lower.

**Where the front end stands:** lexer, parser, desugarer and scope are done --
scope resolves every name in every program the compiler accepts. Check and
lower are not written, which is why this stops at the IR preamble.

## Two parse errors, and they are correct

Over the whole checkout the parser leaves no unread body, no unread annotation
type, and two parse errors -- both in `parser-resync.codex`, whose definitions
are named `broken1` and `broken2`.

One type definition is not fully read: six lines of `--- Sorted builtin table`
rule, which the language has no syntax for.

## Error nodes in desugar

Nine, six of them in `test/errors/`, and none at all in the compiler, foreword,
plugs or os. Each error node carries the NAME of the CST kind it could not
translate, so the list is actionable rather than a count.

## The CCE round trip: codexrun and rocemit agree, and bare metal does not

Measured at Update 60. These codex/test programs print differently from their
`.expected`, and `codexrun` prints the same wrong lines the Roc arm does. The
defect is therefore on the side the two arms share (the front end, or a builtin
rule both mirror), not in either one:

    ops/unicode-bytes-roundtrip    65 -> units [75], back 41   (expected [41], back 65)
                                   192 -> units [0]            (expected [193 128])
    ops/char-encode-bands          128 len=1 decoded=0         (expected a round trip)
    forewords/encode-json-escapes  u00C0 len=3 units 15 0 32   (expected len=4, 15 193 128 32)
    validation-rules               greek=ERR                   (expected greek=ok)
    lib/utf8-cce-test              utf8-3byte-one-char=fail    (expected ok)

The round trip is Codex, in `codex/foreword/core/CCE.codex` (`cce-encode` and
its helpers), run by both arms through the same builtins. Two things to test
first:
- The expected outputs carry Text units 128..255, while `charcode.rs` holds
  that the alphabet ends at 127 and maps nothing above it.
- ASCII is wrong too: 65 comes back as unit 75.

Cause not located. `arm64-http-test` also differs under both arms (`method=7'(`)
and may share the cause; that is not measured.

## `literal_main` must differ

Not a gap -- a required disagreement, and `safari/run.sh` fails if it ever
goes away. See `safari/README.md`.
