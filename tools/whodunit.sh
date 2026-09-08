#!/bin/bash
# whodunit.sh <unit.codex>
# Bisect over DEFINITION PREFIXES of a chapter to find the first definition at
# which our counters part from the oracle's. Both sides see the same truncated
# program, so no additivity assumption is needed -- only that "diverged" is
# monotone in the prefix, which it is because the counters only grow.
set -u
U="$1"
OURS="${CHECKDUMP:-$HOME/build/rust-target/release/checkdump}"
ORAC="${CODEXCHECK:-$HOME/showell_repos/codex-zig-transpiler/generated/local/codexcheck}"
mapfile -t START < <(grep -nE '^  ([a-z_][A-Za-z0-9_?!-]* :|[A-Z][A-Za-z0-9]* =|class |instance |effect )' "$U" | cut -d: -f1)
N=${#START[@]}
grab(){ sed -n 's/^\(substitutions\|next-id\|next-row-id\|expr-types\) \([0-9-]*\)$/\2/p' | tr '\n' ' '; }
prefix(){ if [ "$1" -ge "$N" ]; then cat "$U"; else head -n $(( ${START[$1]} - 1 )) "$U"; fi; }
probe(){ # 0 = agree, 1 = differ, 2 = undecidable (a side refused)
  local p o t; p=$(prefix "$1")
  o=$(printf '%s\n' "$p" | $OURS check /dev/stdin 2>/dev/null | grab)
  t=$(printf '%s\n' "$p" | $ORAC 2>&1 | grab)
  [ -z "$o" ] || [ -z "$t" ] && return 2
  LASTO="$o"; LASTT="$t"
  [ "$o" = "$t" ] && return 0 || return 1; }
# nudge past an undecidable prefix (a forward reference the truncation cut)
decide(){ local k=$1 d
  for d in 0 1 -1 2 -2 3 -3 4 -4 5 -5 6 -6; do
    local j=$((k+d)); [ $j -lt 0 ] && continue; [ $j -gt $N ] && continue
    probe $j; local r=$?; [ $r -ne 2 ] && { DK=$j; return $r; }
  done; DK=$k; return 2; }
echo "$N definitions in $(basename "$U")"
lo=0; hi=$N
decide $hi; [ $? -ne 1 ] && { echo "no divergence at the whole file"; exit 0; }
probes=1
while [ $((hi-lo)) -gt 1 ]; do
  mid=$(( (lo+hi)/2 )); decide $mid; r=$?; probes=$((probes+1))
  case $r in 0) lo=$DK;; 1) hi=$DK;; *) lo=$((mid+1));; esac
  [ $lo -ge $hi ] && break
done
echo "probes: $probes"
echo "first divergence when definition #$hi is included"
s=${START[$((hi-1))]}; if [ $hi -lt $N ]; then e=$(( ${START[$hi]} - 1 )); else e=$(wc -l < "$U"); fi
echo "--- $U:$s-$e ---"; sed -n "${s},${e}p" "$U"
echo "--- ours[$LASTO] oracle[$LASTT] ---"
