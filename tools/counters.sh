#!/bin/bash
u="$1"; n=$(basename "$u" .codex)
grab() { sed -n 's/^\(substitutions\|next-id\|next-row-id\|expr-types\) \([0-9-]*\)$/\2/p' | tr '\n' ' '; }
o=$(~/build/rust-target/release/checkdump check "$u" 2>/dev/null | grab)
t=$(~/showell_repos/codex-zig-transpiler/generated/local/codexcheck < "$u" 2>&1 | grab)
[ -z "$t" ] && t="HALT"
[ -z "$o" ] && o="HALT"
if [ "$o" = "$t" ]; then printf 'SAME %s\n' "$n"; else printf 'DIFF %-42s ours[%s] oracle[%s]\n' "$n" "$o" "$t"; fi
