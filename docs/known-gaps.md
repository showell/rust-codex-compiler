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

## The CCE round trip: closed in both arms

**Both arms hold a Text as CCE units**: codexrun as `interp::Str`
(`charcode.rs`), rocemit as a Roc `List(U8)` with the `Text.roc` it writes
(`roc_text.rs`), one helper per zig `cx_*` text part. Framing, the unit
builtins, `show` of a Char as its code, and x86's print loop byte for byte are
the same on both sides. The design is the essay `notes/codex-text-in-roc.md`.

The Roc ladder passes `ops/unicode-bytes-roundtrip`, `ops/char-encode-bands`,
`forewords/encode-json-escapes`, `validation-rules`, `lib/utf8-cce-test`,
`fat16-source-cr`, `factlog-layout` and `text-helper-native`: 787 of 1,032 at
u61-candidate, from 779, with none lost.

**`text-helper-native`'s verdict corrected both arms.** `text-to-integer`
reads a minus only as the first unit, then CCE digits up to the first unit that
is not one (`+7` and ` 42` are 0, `12abc` is 12), as `cx_text_to_integer`
does; `text-replace` with an empty pattern answers the text unchanged.

**No verdict pins how a framed unit prints.** Both arms emulate x86's printer,
including the two places it prints a character other than the one framed
(tier 1's first slice starts at U+00C0; a negative tier-2 delta gives an
overlong code point). A Roc `Str` cannot hold an overlong sequence, so
`Text.printed` hands the platform U+FFFD there.

## codexrun prints no value opening

`opening : Integer = text-to-integer "-5"` (`neg-int-parse`) prints nothing
under codexrun; its verdict and the Roc arm print `-5`. How many units have a
value opening is not counted.

## `literal_main` must differ

Not a gap -- a required disagreement, and `safari/run.sh` fails if it ever
goes away. See `safari/README.md`.
