#!/bin/bash
# Time the interpreter on a fixed set, so a change to it is measurable.
#
# NOT a gate: nothing here fails, and the number to watch is steps per second
# rather than seconds, because seconds are about this machine on this day.
#
#   ./bench.sh
#
# The subjects are safari's committed units plus the transpiler's arith sample
# -- real programs with real work in them, tested from the OUTSIDE. Point
# SAFARI_ROOT and TRANSPILER_ROOT elsewhere if your checkouts are elsewhere;
# nothing is vendored here.
set -u
SAFARI="${SAFARI_ROOT:-$HOME/showell_repos/safari-codex}"
BIN="${CODEXRUN:-${CARGO_TARGET_DIR:-target}/release/codexrun}"
[ -x "$BIN" ] || { echo "no codexrun at $BIN; cargo build --release, or set CODEXRUN"; exit 2; }

SUBJECTS=()
for u in camera world truck_body cat_draw critter tree drive scene; do
    f="$SAFARI/build/$u-unit.codex"
    [ -f "$f" ] && SUBJECTS+=("$f")
done
[ -n "${ARITH_UNIT:-}" ] && [ -f "$ARITH_UNIT" ] && SUBJECTS+=("$ARITH_UNIT")

[ ${#SUBJECTS[@]} -gt 0 ] || { echo "no subjects found under $SAFARI/build"; exit 2; }
exec "$BIN" bench "${SUBJECTS[@]}"
