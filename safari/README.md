# Safari, driven from the Rust side

safari-codex's committed units are a fixed benchmark for the interpreter.
The fourth arm that used to live here (`safari/run.sh`) graded safari's
retired judge checks; safari's specs and `cobblestone-curated-tests`' arms
grade it now.

## Benchmarking

`bench.sh` is **not a gate** -- nothing in it fails. The number to watch is
steps per second, not seconds, because seconds are about this machine on this
day. Run it before and after any attempt to make the interpreter faster.

`ARITH_UNIT` optionally adds the transpiler's arith sample. Both scripts
document their own knobs and quirks; this file is the why.
