#!/bin/bash
# WHERE the extra mints happened: diff the GAPS between successive ids, not the
# ids. Equal gaps everywhere == one constant offset established before the first
# emitted id. A gap that differs at occurrence k == the extra mints happened
# between node k-1 and node k, and the IR line for k names the node.
gaps(){ grep -o '(tvar [0-9-]*)\|(row (labels[^)]*)[^)]*) *"[^"]*" [0-9-]*' "$1" \
  | sed 's/.* \([0-9-]*\)$/\1/; s/(tvar \([0-9-]*\))/\1/' \
  | awk 'NR>1{print NR-1, $1-p} {p=$1}'; }
diff <(gaps "$1") <(gaps "$2")
