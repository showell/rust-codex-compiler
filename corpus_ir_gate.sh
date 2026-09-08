#!/bin/bash
# EVERY CORPUS UNIT'S IR, ours against codexir, byte for byte.
#
#   ./corpus_ir_gate.sh              ~30-45 minutes, 1,246 units
#
# THE THIRD CORPUS GATE, and the only one that reads the WIRE.
# `corpus_check_gate.sh` compares diagnostics, `corpus_counter_gate.sh`
# compares what is minted, and both can be green on a program whose emitted
# bytes are wrong -- a name spelled from the wrong token, a slot from the wrong
# declaration. Counter agreement is a necessary condition that has been
# satisfied for entirely the wrong reason at least once: synthesised
# definitions named `"    "` kept every counter exact because they were
# unreachable and pruned before emission.
#
# THE RATCHET IS `identical`. It goes up, never down. `differs` is a work
# queue; `we-refuse` while the oracle emits is the worst row on the sheet,
# because we produce nothing at all for a program that compiles.
#
# **codexir WRITES THE IR TO STDERR** and its diagnostics to stdout, and a
# `CODEGEN-HALTED` line on stderr means it refused. Getting that backwards
# compares a refusal message against a program and calls it a difference.
set -u
UNITS="${UNITS:-$HOME/units-u56}"
IRDUMP="${IRDUMP:-$HOME/build/rust-target/release/irdump}"
CODEXIR="${CODEXIR:-$HOME/showell_repos/codex-zig-transpiler/generated/local/codexir}"
OUT="${OUT:-$(mktemp -d)}"

[ -x "$IRDUMP" ]  || { echo "no irdump at $IRDUMP"; exit 2; }
[ -x "$CODEXIR" ] || { echo "no codexir at $CODEXIR"; exit 2; }

same=0; diff=0; ours_refused=0; theirs_refused=0; both_refused=0
for u in "$UNITS"/*.codex; do
    n="$(basename "$u" .codex)"
    "$IRDUMP" whole "$u" Program > "$OUT/ours.ir" 2>"$OUT/ours.err"
    oe=$?
    "$CODEXIR" < "$u" 2>"$OUT/theirs.ir" >/dev/null
    if head -1 "$OUT/theirs.ir" | grep -q '^CODEGEN-HALTED'; then te=1; else te=0; fi

    if [ $oe -ne 0 ] && [ $te -ne 0 ]; then
        both_refused=$((both_refused + 1))
    elif [ $oe -ne 0 ]; then
        ours_refused=$((ours_refused + 1))
        printf 'WE-REFUSE   %-40s %s\n' "$n" "$(head -c 100 "$OUT/ours.err")"
    elif [ $te -ne 0 ]; then
        theirs_refused=$((theirs_refused + 1))
    elif cmp -s "$OUT/ours.ir" "$OUT/theirs.ir"; then
        same=$((same + 1))
    else
        diff=$((diff + 1))
        printf 'DIFFERS     %-40s %s lines\n' "$n" \
            "$(diff "$OUT/ours.ir" "$OUT/theirs.ir" | grep -c '^[<>]')"
    fi
done
echo
echo "identical $same, differs $diff, we-refuse $ours_refused, oracle-refuses $theirs_refused, both-refuse $both_refused"
