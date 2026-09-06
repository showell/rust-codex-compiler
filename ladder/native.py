#!/usr/bin/env python3
"""THE NATIVE ARM, GRADED THE WAY THE INTERPRETED ONE IS.

    CODEX_ROOT=<checkout> ./ladder/native.py <program.codex> [program ...]

`hosts.py` asks whether our INTERPRETER runs the Codex compiler the way a
native binary does. This asks the other question: whether `irdump` -- Rust
compiling Codex to IR directly, no Codex compiler in the loop -- reaches the
same document.

**THE CONTROL IS THE SAME `codexir`, ON THE SAME UNIT.** Both arms are handed
the bytes `cite_resolve.py` produces and both name the entry chapter
`"Program"`, so a difference is ours and there is no third explanation. Grading
against `$CODEX_GOLDS/ir` instead would carry a different pin, a different tree
and a different resolver, none of which is the thing under test.

A REFUSAL IS NOT A FAILURE AND NOT A PASS. `irdump` returns the reason it could
not type a chapter rather than guessing, so the three verdicts are counted
apart and the reasons are histogrammed -- which is the whole point of running
this before choosing what to build next.
"""
import collections
import os
import pathlib
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, "/home/steve/showell_repos/codex-zig-ladder")
from cite_resolve import resolve
from hosts import CODEXIR, TARGET, refuse_a_stale_binary

IRDUMP = TARGET / "irdump"
RUN_TIMEOUT = 120
ORACLE_TIMEOUT = 120


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    if "CODEX_ROOT" not in os.environ:
        raise SystemExit("set CODEX_ROOT to the checkout the ORACLE was built from")
    for b in (IRDUMP, CODEXIR):
        if not b.is_file():
            raise SystemExit(f"no {b.name} at {b}")
    refuse_a_stale_binary(IRDUMP)

    tally = collections.Counter()
    why = collections.Counter()
    for arg in sys.argv[1:]:
        path = pathlib.Path(arg)
        unit_text, missing = resolve(path.resolve())
        if missing:
            tally["UNRESOLVED"] += 1
            print(f"{path.stem:34} UNRESOLVED", flush=True)
            continue
        with tempfile.NamedTemporaryFile("w", suffix=".codex", delete=False) as f:
            f.write(unit_text)
            unit = f.name
        t0 = time.time()
        r = subprocess.run([str(IRDUMP), "whole", unit, "Program"],
                           capture_output=True, text=True, timeout=RUN_TIMEOUT)
        secs = time.time() - t0
        with open(unit, "rb") as fh:
            o = subprocess.run([str(CODEXIR)], stdin=fh, capture_output=True,
                               timeout=ORACLE_TIMEOUT)
        os.unlink(unit)
        oracle = o.stderr.decode("utf-8", "replace")
        if r.returncode != 0:
            # The reason, with the definition name stripped off the front so
            # the histogram groups by the missing PIECE and not by the caller.
            reason = (r.stderr.strip().splitlines() or ["no reason given"])[-1]
            reason = reason.split(": ", 1)[-1][:60]
            verdict, detail = "REFUSED", reason
            why[reason] += 1
        elif r.stdout == oracle:
            verdict, detail = "agree", f"{len(r.stdout)} bytes"
        elif not oracle.startswith("(chapter"):
            # **THE ORACLE REFUSED THE PROGRAM AND WE DID NOT.** Counted apart
            # because it is not a lowering diff: these are the corpus's
            # NEGATIVE tests, and we emit IR for them because there is no
            # diagnostics layer here yet to reject one. Folding them into
            # DIFFERS made the smallest sixty programs read as 41 disagreements
            # when four were about lowering at all.
            verdict, detail = "no-diagnosis", oracle.strip().split(";")[0][:60]
        else:
            verdict = "DIFFERS"
            detail = f"{len(r.stdout)} vs codexir {len(oracle)}"
        tally[verdict] += 1
        print(f"{path.stem:34} {verdict:11} {secs:6.2f}s  {detail}", flush=True)

    print("\n" + "  ".join(f"{v}: {n}" for v, n in sorted(tally.items())), flush=True)
    if why:
        print("\nwhy it refused:", flush=True)
        for reason, n in why.most_common(20):
            print(f"  {n:5}  {reason}", flush=True)
    return 1 if tally["DIFFERS"] else 0


if __name__ == "__main__":
    sys.exit(main())
