#!/bin/bash
# ONE PROGRAM THROUGH EVERY LAYER, against the rung truth that grades them all.
#
# `check.truth` is CUMULATIVE -- it carries lex, parse, desugar and scope before
# its own section -- so a single diff says which layer breaks first. That is
# worth more than four separate green ticks: the layers validate each other's
# design, and a scope decision that lower cannot use shows up here rather than
# three weeks later.
#
#   ./slice.sh <file.codex> [<gold.truth>]
set -e
T="$(cd "$(dirname "$0")" && pwd)"
SRC="${1:?usage: slice.sh <file.codex> [gold.truth]}"
GOLD="${2:-${CODEX_GOLDS:?set CODEX_GOLDS}/rungs/check.truth}"
B="$T/target/release"

# desugardump's trailing `---` closes it as a STANDALONE dump; inside the
# cumulative truth the scope section ends at its `.` and check follows directly.
{ "$B/desugardump" scope "$SRC" | sed '$ { /^---$/d; }'
  "$B/checkdump" check "$SRC"; } > /tmp/slice-ours.txt

if diff -q /tmp/slice-ours.txt "$GOLD" > /dev/null; then
    echo "SLICE GREEN: $(basename "$SRC") is byte-identical through check"
    exit 0
fi
echo "slice diff ($(basename "$SRC") against $(basename "$GOLD")):"
diff /tmp/slice-ours.txt "$GOLD" | head -30
exit 1
