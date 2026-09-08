#!/bin/bash
# EVERY CORPUS UNIT'S MINT COUNTERS, ours against codexcheck.
#
#   ./corpus_counter_gate.sh            ~7 minutes, 1,246 units
#
# `corpus_check_gate.sh` compares DIAGNOSTICS and this compares ALLOCATION:
# substitutions, next-id, next-row-id, expr-types, in that order. They are
# different questions and a green run of one says nothing about the other --
# the counters gate what is MINTED, the diagnostics gate what is CONCLUDED.
#
# **A DIVERGENCE HERE IS USUALLY A DEFINITION WE DO NOT SYNTHESISE**, not an
# ordering bug in the walk. Four have been found with that shape so far --
# unit-family members, `deriving` on records and units, class dictionaries,
# instance methods. The signature is `next-id` and `next-row-id` apart while
# `expr-types` agrees, because a synthesised span is synthetic and
# `record-expr-type` skips those.
#
# To localise one: `tools/mintprofile.sh <unit>` for a small chapter, and
# `tools/whodunit.sh <unit>` for one too big to profile linearly.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
UNITS="${UNITS:-$HOME/units-u56}"
same=0; diff=0; halt=0
for u in "$UNITS"/*.codex; do
    out="$("$ROOT/tools/counters.sh" "$u")"
    case "$out" in
        SAME*) same=$((same + 1)) ;;
        *"oracle[HALT]"*) halt=$((halt + 1)) ;;
        *) diff=$((diff + 1)); echo "$out" ;;
    esac
done
echo
echo "$same agree, $diff diverge, $halt the oracle refuses"
[ $diff -eq 0 ] || { echo RED; exit 1; }
echo GREEN
