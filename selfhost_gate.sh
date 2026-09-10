#!/bin/bash
# The compiler compiling ITSELF, ours against codexcheck and codexir.
#
#   ./selfhost_gate.sh              about a minute
#
# THE CHEAPEST GATE THAT SEES THE WHOLE COMPILER. One unit -- the transpiler's
# codexcheck-subject.codex, which is every chapter in one file -- against the
# corpus sweeps' twenty-odd minutes over 1,246 of them. It is the gate to run
# first after a repin, because it moves for the same reasons they do.
#
# IT COMPARES, AND IT EXITS NON-ZERO WHEN THE ANSWER MOVES. This lived as an
# inline snippet in a checkpoint script that printed both sides and never
# looked at them, so the run where the counters first diverged still reported
# PASS -- grep had found its lines, and that was the whole test.
#
# THREE OUTCOMES PER DEFINITION, NOT TWO. A definition the oracle emits and we
# do not is MISSING; one we both emit, differently, DIFFERS. Folding them
# together reports the arrival of new upstream code as though it were a
# regression in ours, and those two want opposite responses -- port it, or fix
# it.
#
# BOTH ORACLES ARE PINNED TO A CHECKOUT and this gate cannot tell which. Read
# generated/PROVENANCE.oracles beside them; a repin moves every number here at
# once, and a number compared across two pins is not a comparison.
set -u
T="${T:-$HOME/showell_repos/codex-zig-transpiler}"
SUBJECT="${SUBJECT:-$T/generated/codexcheck-subject.codex}"
CODEXCHECK="${CODEXCHECK:-$T/generated/local/codexcheck}"
CODEXIR="${CODEXIR:-$T/generated/local/codexir}"
BIN="${BIN:-$HOME/build/rust-target/release}"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

for f in "$SUBJECT" "$CODEXCHECK" "$CODEXIR" "$BIN/checkdump" "$BIN/irdump"; do
    [ -e "$f" ] || { echo "missing $f"; exit 2; }
done

if [ -f "$T/generated/PROVENANCE.oracles" ]; then
    echo "oracles   $(grep -A1 '^checkout' "$T/generated/PROVENANCE.oracles" | tail -1 | sed 's/^ *//')"
fi
echo "subject   $(basename "$SUBJECT")  $(stat -c%s "$SUBJECT") bytes"
echo

# --- the counters ---------------------------------------------------------
FIELDS='^(check-errors|substitutions|next-row-id|expr-types|next-id) '
"$BIN/checkdump" check "$SUBJECT" 2>/dev/null | grep -E "$FIELDS" | sort > "$OUT/ours.cnt"
"$CODEXCHECK" < "$SUBJECT" 2>&1   | grep -E "$FIELDS" | sort > "$OUT/gold.cnt"

bad=0
if diff -q "$OUT/ours.cnt" "$OUT/gold.cnt" >/dev/null; then
    echo "counters  EXACT on all five"
else
    echo "counters  DIVERGE"
    join "$OUT/ours.cnt" "$OUT/gold.cnt" -o 0,1.2,2.2 2>/dev/null |
        awk '{ d = $3 - $2; printf "  %-16s ours %-10s oracle %-10s %+d\n", $1, $2, $3, d }'
    bad=1
fi
echo

# --- the wire, per definition ---------------------------------------------
"$BIN/irdump" whole "$SUBJECT" > "$OUT/ours.ir" 2>/dev/null
"$CODEXIR" < "$SUBJECT" 2> "$OUT/gold.ir" >/dev/null

python3 - "$OUT/ours.ir" "$OUT/gold.ir" <<'PY'
import re, sys

def defs(path):
    out = {}
    for line in open(path):
        m = re.match(r'\s*\(def .([^"]+).', line)
        if m:
            out[m.group(1)] = line
    return out

ours, gold = defs(sys.argv[1]), defs(sys.argv[2])
same    = [k for k in gold if k in ours and ours[k] == gold[k]]
differs = sorted(k for k in gold if k in ours and ours[k] != gold[k])
missing = sorted(k for k in gold if k not in ours)

print(f'wire      identical {len(same)} of {len(gold)}   '
      f'differs {len(differs)}   MISSING {len(missing)}')
if missing:
    print('\n  MISSING -- the oracle emits these and we emit nothing:')
    for k in missing:
        print(f'    {k}')
if differs:
    print('\n  DIFFERS -- both emit, and the bytes disagree:')
    for k in differs:
        print(f'    {k}')
sys.exit(1 if (differs or missing) else 0)
PY
ir=$?

echo
if [ $bad -eq 0 ] && [ $ir -eq 0 ]; then
    echo "GREEN"
    exit 0
fi
# RED is this gate's normal state while the port is incomplete. The numbers
# above are the ratchet: identical goes up, MISSING goes down.
echo "RED"
exit 1
