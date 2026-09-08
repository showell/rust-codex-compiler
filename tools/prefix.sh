#!/bin/bash
# prefix.sh <unit.codex> <k>   -- emit the chapter truncated after definition k
u="$1"; k="$2"
# definition start = a signature line: two-space indent, name, " : "
mapfile -t starts < <(grep -n '^  [a-z_][A-Za-z0-9_?!-]* :' "$u" | cut -d: -f1)
n=${#starts[@]}
if [ "$k" -ge "$n" ]; then cat "$u"; exit 0; fi
end=$(( ${starts[$k]} - 1 ))
head -n "$end" "$u"
