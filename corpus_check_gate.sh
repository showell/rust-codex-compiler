#!/bin/bash
# EVERY CORPUS UNIT'S DIAGNOSTICS, ours against codexcheck: the count and the
# first code, one line per DISAGREEMENT.
#
#   ./corpus_check_gate.sh              ~6 minutes, 1,433 units at U64
#
# SLOW ON PURPOSE AND NOT A CHECKPOINT. `linear_gate.sh` is the fast gate for
# one subsystem; this is the wide net you run after adding a diagnostic, and
# the one question it answers that nothing else does is **did we invent an
# error the oracle does not raise**:
#
#   grep -E 'ours\[[1-9]' out | grep 'oracle\[0'      <- must be empty
#
# A row reading `ours[0] oracle[N]` is a diagnostic we have not built yet, and
# there are many; those are inventory, not failure. A row where both sides
# count the same but name a different first code usually means the oracle
# stopped at an earlier cause than we did -- read the program before believing
# either side.
#
# KNOWN SLOW UNITS ARE LEFT OUT, AND SAID SO. `gate-slow.txt` lists the units
# our checker takes far longer on than the oracle does (a performance bug of
# ours, not a verdict); each is reported as SLOW, never silently skipped, and
# `ALL=1` runs them. Every other unit runs under `CHECK_TIMEOUT` seconds
# (default 30): one that exceeds it is a TIMEOUT disagreement, so a unit
# that newly turns slow is seen rather than stalling the gate.
UNITS="${UNITS:-$HOME/units-current}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SLOW=$(grep -v '^#' "$HERE/gate-slow.txt" 2>/dev/null | awk '{print $2}')
LIMIT="${CHECK_TIMEOUT:-30}"
BIN="${CHECKDUMP:-$HOME/build/rust-target/release/checkdump}"
ORACLE="${CODEXCHECK:-$HOME/codexir/codexcheck}"
[ -d "$UNITS" ] || { echo "no units at $UNITS"; exit 2; }

. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/gate_provenance.sh"
gate_provenance "$UNITS"
pair() { local c k; c=$(printf '%s' "$1" | sed -n 's/^check-errors \([0-9]*\).*/\1/p' | head -1)
  [ -z "$c" ] && c=$(printf '%s' "$1" | sed -n 's/^CODEGEN-HALTED: \([0-9]*\) error.*/\1/p' | head -1)
  k=$(printf '%s' "$1" | grep -o 'CDX[0-9]*' | head -1); printf '%s %s' "${c:-?}" "${k:--}"; }
a=0; d=0; slow=0
for u in "$UNITS"/*.codex; do
  n=$(basename "$u" .codex)
  if [ -z "${ALL:-}" ] && printf '%s\n' $SLOW | grep -qx "$n"; then
    slow=$((slow+1)); printf '%-40s SLOW (gate-slow.txt; ALL=1 runs it)\n' "$n"; continue
  fi
  out=$(timeout "$LIMIT" $BIN check "$u" 2>/dev/null); rc=$?
  if [ $rc -eq 124 ]; then d=$((d+1)); printf '%-40s ours[TIMEOUT %ss]\n' "$n" "$LIMIT"; continue; fi
  o=$(pair "$out")
  t=$(pair "$($ORACLE < "$u" 2>&1)")
  if [ "$o" = "$t" ]; then a=$((a+1)); else d=$((d+1)); printf '%-40s ours[%s] oracle[%s]\n' "$n" "$o" "$t"; fi
done
echo; echo "agree $a, differ $d, slow $slow"
