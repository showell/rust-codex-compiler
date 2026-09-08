#!/bin/bash
# THE LINEARITY GATE: our checker's diagnostics against `codexcheck`, on the 26
# corpus units that exercise the linear / mutable discipline.
#
#   ./linear_gate.sh
#
# TWO-SIDED ON PURPOSE. Eighteen of these MUST be refused and eight MUST pass
# clean, and the eight are the half that is easy to lose: a checker that reports
# an error on every program passes the first half of this gate perfectly.
#
# The oracle prints one of two shapes and both carry the count:
#
#   check-errors 0                                     ... clean
#   CODEGEN-HALTED: 3 error(s); ... first CDX2061 ...   ... refused
#
# so the comparison is the COUNT, plus the first code where there is one. A
# count that matches with the wrong code is not agreement, and this reports it
# as CODE so it cannot hide inside a green number.
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
UNITS="${UNITS:-$HOME/units-u56}"
BIN="${CHECKDUMP:-$ROOT/target/release/checkdump}"
ORACLE="${CODEXCHECK:-$HOME/showell_repos/codex-zig-transpiler/generated/local/codexcheck}"

[ -x "$BIN" ]    || { echo "no checkdump at $BIN; cargo build --release"; exit 2; }
[ -x "$ORACLE" ] || { echo "no codexcheck at $ORACLE"; exit 2; }
[ -d "$UNITS" ]  || { echo "no units at $UNITS"; exit 2; }

# `mutable-launder-sum-return` refuses for CDX2002 Unknown name: Some -- a
# different subsystem, and counting it here would make this gate lie about
# linearity. Excluded by name, with the reason.
declare -A NOT_OURS=( [mutable-launder-sum-return]="CDX2002 Unknown name: Some -- not the linear discipline" )

agree=0; differ=0; skipped=0
for u in "$UNITS"/linear-*.codex "$UNITS"/mutable-*.codex "$UNITS"/serial-*.codex; do
    [ -e "$u" ] || continue
    n="$(basename "$u" .codex)"
    if [ -n "${NOT_OURS[$n]:-}" ]; then
        printf '%-30s skipped -- %s\n' "$n" "${NOT_OURS[$n]}"
        skipped=$((skipped + 1)); continue
    fi

    # count and first code from either shape, from either side
    read_pair() {
        local out="$1"
        local c k
        c="$(printf '%s' "$out" | sed -n 's/^check-errors \([0-9]*\).*/\1/p' | head -1)"
        if [ -z "$c" ]; then
            c="$(printf '%s' "$out" | sed -n 's/^CODEGEN-HALTED: \([0-9]*\) error.*/\1/p' | head -1)"
        fi
        k="$(printf '%s' "$out" | grep -o 'CDX[0-9]*' | head -1)"
        printf '%s %s' "${c:-?}" "${k:--}"
    }

    ours="$(read_pair "$("$BIN" check "$u" 2>/dev/null)")"
    theirs="$(read_pair "$("$ORACLE" < "$u" 2>&1)")"

    if [ "$ours" = "$theirs" ]; then
        printf '%-30s ok    %s\n' "$n" "$theirs"
        agree=$((agree + 1))
    else
        printf '%-30s DIFFERS  ours[%s] oracle[%s]\n' "$n" "$ours" "$theirs"
        differ=$((differ + 1))
    fi
done

echo
echo "$agree agree, $differ differ, $skipped skipped"
[ $differ -eq 0 ] || { echo RED; exit 1; }
[ $agree -gt 0 ]  || { echo "nothing was compared"; echo RED; exit 1; }
echo GREEN
