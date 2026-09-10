#!/usr/bin/env bash
# Discovery loop for one Codex program.
#   loop.sh prog.codex
# VALUE oracle: our interpreter (codexrun).   TYPE oracle: our IR -> zig build -> run.
# Attribution: upstream codexzig (frontend+plug) on the same program.
set -uo pipefail
IRDUMP=$HOME/showell_repos/rust-codex-compiler/target/debug/irdump
CODEXRUN=$HOME/showell_repos/rust-codex-compiler/target/debug/codexrun
ZIGEMIT=$HOME/runs/zigemit-catc2/zigemit
CODEXZIG=$HOME/codexzig/codexzig
ZIG=$HOME/zig-0.16.0/zig
prog="$1"; n=$(basename "$prog" .codex)
w=$(mktemp -d)
echo "### $n"
# --- VALUE oracle (our interpreter) ---
val=$("$CODEXRUN" "$prog" 2>"$w/run.err"); rc=$?
echo "-- codexrun (rc=$rc): $(echo "$val" | head -3 | tr '\n' '|')"
[ $rc -ne 0 ] && echo "   run.err: $(head -2 "$w/run.err")"
# --- our IR ---
"$IRDUMP" whole "$prog" > "$w/ir.txt" 2>"$w/ir.err"; irc=$?
if [ $irc -ne 0 ]; then echo "-- irdump REFUSED (rc=$irc): $(head -2 "$w/ir.err")"; fi
grep -oE '\(tvar [0-9]+\)' "$w/ir.txt" | sort | uniq -c | sed 's/^/   residual /'
# --- TYPE oracle (our IR -> zig) ---
"$ZIGEMIT" < "$w/ir.txt" 2>"$w/prog.zig" >/dev/null
if [ ! -s "$w/prog.zig" ] || head -c14 "$w/prog.zig" | grep -q CODEGEN-HALTED; then
  echo "-- zigemit produced no zig: $(head -2 "$w/emit.err")"
else
  if (cd "$w" && "$ZIG" build-exe prog.zig -femit-bin=prog.exe) 2>"$w/zig.err"; then
    zval=$("$w/prog.exe" 2>&1 >/dev/null); echo "-- OUR zig OK: $(echo "$zval" | head -3 | tr '\n' '|')"
  else
    echo "-- OUR zig BUILD-FAILED: $(grep -m1 error: "$w/zig.err" | cut -c1-80)"
  fi
fi
# --- attribution: upstream codexzig ---
"$CODEXZIG" < "$prog" 2>"$w/up.zig" >/dev/null
if [ ! -s "$w/up.zig" ] || head -c14 "$w/up.zig" | grep -q CODEGEN-HALTED; then
  echo "-- upstream codexzig REFUSED: $(head -1 "$w/up.zig")"
else
  if (cd "$w" && "$ZIG" build-exe up.zig -femit-bin=up.exe) 2>"$w/up.err"; then
    uval=$("$w/up.exe" 2>&1 >/dev/null); echo "-- upstream zig OK: $(echo "$uval" | head -3 | tr '\n' '|')"
  else
    echo "-- upstream zig BUILD-FAILED: $(grep -m1 error: "$w/up.err" | cut -c1-80)"
  fi
fi
echo "   (work: $w)"
