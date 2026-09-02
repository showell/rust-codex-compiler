#!/bin/bash
# THE FOURTH ARM, FROM THE OUTSIDE: run safari-codex's own checks through this
# interpreter and demand the zig arm's exact output.
#
#   ./safari.sh
#
# safari-codex bundles each check into `build/<mod>-unit.codex` and compiles that
# same unit to `build/<mod>` with codexzig; `./harness/run.sh` over there leaves
# both behind. So this needs no gold and no fixture: ONE SOURCE, TWO INDEPENDENT
# IMPLEMENTATIONS, run now and diffed. Cobblestone's front end and emitter on one
# side, our lexer, parser, desugarer and interpreter on the other, sharing nothing
# below the text.
#
# NOTHING IS VENDORED HERE. It reads another checkout and writes nothing into it;
# point SAFARI_ROOT elsewhere if yours is elsewhere. Units without a binary beside
# them are REPORTED rather than skipped -- a sweep that quietly covers eleven of
# twenty-three is worse than one that covers eleven and says so.
#
# THE DEFAULT RUN IS THE CHEAP ONE. Two units are held back; see HEAVY below.
# SAFARI_ALL=1 runs everything.
set -u

SAFARI="${SAFARI_ROOT:-$HOME/showell_repos/safari-codex}"
BIN="${CODEXRUN:-${CARGO_TARGET_DIR:-target}/release/codexrun}"
ZIG_SECS="${ZIG_SECS:-300}"
RUST_SECS="${RUST_SECS:-900}"

[ -x "$BIN" ] || { echo "no codexrun at $BIN; cargo build --release, or set CODEXRUN"; exit 2; }
[ -d "$SAFARI/build" ] || { echo "no $SAFARI/build; run ./harness/run.sh there first"; exit 2; }

# EXPECTED DIVERGENCES, and each one has to earn its line.
#
# literal_main is FINDINGS.md item 1B's repro: Cobblestone accumulates a Real
# literal's digits into a WRAPPING i64, so nineteen digits arrive as a different
# and usually negative number, silently. We read it as an f64 and get it right.
# The divergence is the evidence -- a second front end that does not reproduce
# the bug -- so it is REQUIRED rather than tolerated: if these two ever agree,
# either the finding was fixed upstream (delete this line and celebrate) or we
# grew the same defect (do not celebrate).
declare -A MUST_DIFFER=(
  [literal_main]="FINDINGS 1B: a 19-digit Real literal wraps an i64 in Cobblestone and does not here"
)

# HELD BACK BY DEFAULT, and each one has to earn that too.
#
# None of these is slow because anything is wrong. They ask for hundreds of
# millions of AST steps and the interpreter runs them at the same rate it runs
# the three-thousand-step ones -- `spike_profile_main` is a deliberate stress
# spike that iterates 4,000 times. A tree walker is not going to close the gap
# to compiled zig, so this is the workload's size and not a defect to chase.
#
# What they buy over the light units is SCALE, not coverage: same language,
# same front end, same interpreter, more iterations. That is worth running
# deliberately -- after a change to the evaluator -- and not worth paying for
# on every ordinary run. Five of them are 96% of the sweep's cost.
#
# THE LIST CAME FROM `codexrun bench`, not from a guess: the cut is 100M steps,
# which leaves `safari` at 82M as the heaviest thing still in the default run.
# Re-measure after a change to the corpus rather than trusting these numbers.
#
# HELD BACK, NOT DROPPED: every run prints them and says how to put them back.
declare -A HEAVY=(
  [spike_profile_main]="1,513,290,308 steps"
  [ride]="1,348,139,178 steps"
  [render]="605,930,430 steps"
  [drive_main]="115,152,004 steps"
  [rider]="111,647,964 steps"
)

same=0; differ=0; bad=0; nobin=0; held=0
for unit in "$SAFARI"/build/*-unit.codex; do
    [ -e "$unit" ] || break
    mod="$(basename "$unit" -unit.codex)"
    exe="$SAFARI/build/$mod"
    if [ -z "${SAFARI_ALL:-}" ] && [ -n "${HEAVY[$mod]:-}" ]; then
        echo "$(printf '%-18s' "$mod") held back (${HEAVY[$mod]}) -- SAFARI_ALL=1 runs it"
        held=$((held + 1))
        continue
    fi
    if [ ! -x "$exe" ]; then
        echo "$(printf '%-18s' "$mod") no binary -- not covered"
        nobin=$((nobin + 1))
        continue
    fi

    zout="$(cd "$SAFARI/build" && timeout "$ZIG_SECS" "./$mod" 2>&1)"; zrc=$?
    rout="$(timeout "$RUST_SECS" "$BIN" "$unit" 2>&1)"; rrc=$?
    label="$(printf '%-18s' "$mod")"

    if [ $zrc -ne 0 ]; then
        echo "$label ZIG FAILED (exit $zrc) -- nothing to compare against"
        bad=$((bad + 1))
    elif [ $rrc -ne 0 ]; then
        echo "$label RUST FAILED (exit $rrc): $(printf '%s' "$rout" | head -1 | cut -c1-100)"
        bad=$((bad + 1))
    elif [ "$zout" = "$rout" ]; then
        if [ -n "${MUST_DIFFER[$mod]:-}" ]; then
            echo "$label AGREES BUT SHOULD NOT -- ${MUST_DIFFER[$mod]}"
            bad=$((bad + 1))
        else
            echo "$label same, $(printf '%s\n' "$zout" | wc -l) lines"
            same=$((same + 1))
        fi
    elif [ -n "${MUST_DIFFER[$mod]:-}" ]; then
        echo "$label differs as it must -- ${MUST_DIFFER[$mod]}"
        differ=$((differ + 1))
    else
        echo "$label DIFFERS"
        diff <(printf '%s\n' "$zout") <(printf '%s\n' "$rout") | head -6 | sed 's/^/    /'
        bad=$((bad + 1))
    fi
done

echo
echo "$same agree, $differ differ on purpose, $bad wrong, $nobin without a binary, $held held back"
[ $bad -eq 0 ] || { echo RED; exit 1; }
[ $same -gt 0 ] || { echo "nothing was compared"; echo RED; exit 1; }
echo GREEN
