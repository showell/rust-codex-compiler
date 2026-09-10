#!/usr/bin/env bash
# THE CONFLICT CENSUS: every concrete, variable-free, different-head pair the
# unifier meets, on programs THE ORACLE COMPILES CLEAN. A pair that appears
# here is one `report_conflict` must NOT report, because reporting it invents
# an error. A pair that never appears is safe to report.
#
#   tools/conflict_census.sh            about six minutes over ~/units-current
#   UNITS=dir tools/conflict_census.sh
#
# Output: `count  A vs B` for pairs on clean units, then `unit  A vs B` rows.
set -u
UNITS="${UNITS:-$HOME/units-current}"
BIN="${CHECKDUMP:-$HOME/build/rust-target/release/checkdump}"
ORACLE="${CODEXCHECK:-$HOME/codexir/codexcheck}"
ulimit -s unlimited 2>/dev/null
rows=$(mktemp)
for u in "$UNITS"/*.codex; do
  n=$(basename "$u" .codex)
  pairs=$(CDX_MEASURE_CONFLICTS=1 "$BIN" check "$u" 2>&1 >/dev/null | grep '^CONFLICT-PAIR ' | sed 's/^CONFLICT-PAIR //' | sort -u)
  [ -z "$pairs" ] && continue
  if "$ORACLE" < "$u" 2>&1 | grep -q 'CODEGEN-HALTED'; then continue; fi
  printf '%s\n' "$pairs" | sed "s/^/$n\t/" >> "$rows"
done
echo "== pairs on clean units (count, pair)"
cut -f2 "$rows" | sort | uniq -c | sort -rn
echo "== rows"
cat "$rows"
rm -f "$rows"
