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

same=0; differ=0; bad=0; nobin=0
for unit in "$SAFARI"/build/*-unit.codex; do
    [ -e "$unit" ] || break
    mod="$(basename "$unit" -unit.codex)"
    exe="$SAFARI/build/$mod"
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
echo "$same agree, $differ differ on purpose, $bad wrong, $nobin without a binary"
[ $bad -eq 0 ] || { echo RED; exit 1; }
[ $same -gt 0 ] || { echo "nothing was compared"; echo RED; exit 1; }
echo GREEN
