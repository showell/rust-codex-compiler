#!/bin/bash
# The ORDERED SEQUENCE of every id the IR spells, with the 60 chars of context
# it sits in. Diffing two of these says which NODE first carries a wrong number.
grep -o '(tvar [0-9-]*)\|(row (labels[^)]*)[^)]*) *"[^"]*" [0-9-]*' "$1" \
 | sed 's/.* \([0-9-]*\)$/row \1/; s/(tvar \([0-9-]*\))/tvar \1/' | cat -n
