#!/bin/bash
# mintprofile.sh <unit.codex>
# The oracle has no mint log, but it has a counter and the program is a knob.
# Run EVERY definition prefix on both sides; the first difference of the
# resulting sequences is the per-definition cost. Diff the two profiles and you
# have every diverging definition in the file, not just the first.
set -u
U="$1"
OURS="${CHECKDUMP:-$HOME/build/rust-target/release/checkdump}"
ORAC="${CODEXCHECK:-$HOME/showell_repos/codex-zig-transpiler/generated/local/codexcheck}"
mapfile -t START < <(grep -nE '^  ([a-z_][A-Za-z0-9_?!-]* :|[A-Z][A-Za-z0-9]* =|class |instance |effect )' "$U" | cut -d: -f1)
N=${#START[@]}
grab(){ sed -n 's/^\(next-id\|next-row-id\|expr-types\) \([0-9-]*\)$/\2/p' | tr '\n' ' '; }
pi=0 pr=0 pe=0 qi=0 qr=0 qe=0
printf '%-4s %-30s %-14s %-14s\n' '#' 'DEFINITION' 'OURS d(i,r,e)' 'ORACLE d(i,r,e)'
for k in $(seq 1 $N); do
  if [ $k -lt $N ]; then p=$(head -n $(( ${START[$k]} - 1 )) "$U"); else p=$(cat "$U"); fi
  o=$(printf '%s\n' "$p" | $OURS check /dev/stdin 2>/dev/null | grab)
  t=$(printf '%s\n' "$p" | $ORAC 2>&1 | grab)
  name=$(sed -n "${START[$((k-1))]}p" "$U" | sed 's/^ *//;s/ .*//')
  if [ -z "$o" ] || [ -z "$t" ]; then printf '%-4s %-30s %s\n' "$k" "$name" "(a side refused this prefix)"; continue; fi
  read -r i r e <<< "$o"; read -r j s f <<< "$t"
  a="$((i-pi)),$((r-pr)),$((e-pe))"; b="$((j-qi)),$((s-qr)),$((f-qe))"
  pi=$i pr=$r pe=$e qi=$j qr=$s qe=$f
  m=""; [ "$a" = "$b" ] || m="   <== DIVERGES"
  printf '%-4s %-30s %-14s %-14s%s\n' "$k" "$name" "$a" "$b" "$m"
done
