# What a number is ABOUT. Sourced by every gate that prints one.
#
# A gate that prints "identical 865" and nothing else hands you a number nobody
# can place a week later. Three things decide it and every one of them moves:
#
#   subject   which corpus, cut from which checkout
#   oracles   codexir and codexcheck, built from which checkout
#   port      this repository, at which commit, clean or not
#
# THIS WAS NOT HYPOTHETICAL. Through 2026-09-08 the gates defaulted to
# ~/units-u56, and on 09-09 that directory was found to hold U55 sources -- 18
# of the 19 comparable files that changed between those Updates matched U55 and
# none matched U56. It had been graded against a U57 oracle for a night. The
# directory NAME was the only claim anything made about its pin, and it was
# wrong. Nothing printed by any gate would have caught it.
#
# A corpus with no PROVENANCE beside it says so here, loudly, rather than
# passing for pinned.

gate_provenance() {                       # gate_provenance <units-dir>
    # RESOLVED, not as given: ~/units-current is a symlink that moves with each
    # cut, and printing the pointer instead of what it points at is the same
    # class of thing this file exists to stop.
    local units="$(cd "$1" 2>/dev/null && pwd -P)"
    [ -n "$units" ] || units="$1"
    local rc="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    local t="${T:-$HOME/showell_repos/codex-zig-transpiler}"

    if [ -f "$units/PROVENANCE" ]; then
        printf 'subject   %s\n' "$units"
        printf '          %s\n' "$(awk '/^revision/{$1=""; sub(/^ +/,""); print}' "$units/PROVENANCE")"
    else
        printf 'subject   %s\n' "$units"
        printf '          REVISION UNKNOWN -- no PROVENANCE beside it, and the name is not a pin\n'
    fi
    printf '          %s units\n' "$(ls "$units"/*.codex 2>/dev/null | wc -l)"

    # The oracle BUNDLE: codexir and codexcheck beside the PROVENANCE.oracles
    # that names their checkout. ~/codexir by default; CODEX_ORACLES overrides.
    local ob="${CODEX_ORACLES:-$HOME/codexir}"
    if [ -f "$ob/PROVENANCE.oracles" ]; then
        printf 'oracles   %s  (%s)\n' "$(grep -A1 '^checkout' "$ob/PROVENANCE.oracles" | tail -1 | sed 's/^ *//')" "$ob"
    else
        printf 'oracles   REVISION UNKNOWN -- no PROVENANCE.oracles in %s\n' "$ob"
    fi

    local head dirty
    head="$(git -C "$rc" log -1 --format='%h  %s' 2>/dev/null)"
    dirty=""
    [ -n "$(git -C "$rc" status --porcelain 2>/dev/null)" ] && dirty="  DIRTY"
    printf 'port      %s%s\n' "$head" "$dirty"
    echo
}
