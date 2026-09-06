#!/usr/bin/env python3
"""**CUT THE CORPUS DOWN TO A SET WE CAN DEMAND PERFECTION FROM.**

    CODEX_ROOT=<checkout> ./ladder/curate.py <outdir> [keep]

STAGE 1 resolves every `codex/test` program and keeps the ones whose cites all
resolve. STAGE 1b runs each resolved unit under `codexrun` -- the interpreter
executing the PROGRAM, not interpreting the compiler -- and records how long it
took and whether it printed anything. The `keep` fastest that produced output
are the candidate set.

WHY THE UNIT AND NOT THE DRIVER. A corpus test is typically five lines and a
`cites`; its content is the ~30 KB unit cite resolution builds. Freezing the
driver would leave the set depending on a checkout, `quire-map.ps1` and every
foreword chapter -- so an Update still moves it, which is the thing being
escaped. Freezing the UNIT makes each program one self-contained file with no
`CODEX_ROOT`, no resolver and no quire registry.

WHAT THAT COSTS, stated because it is a real loss: the citing mechanism itself
stops being exercised. The drivers stay in the corpus and can be resurrected
against a checkout when that is what is under test.

THE TIMEOUT IS A SELECTION CRITERION, NOT A GUARD. We want the fastest `keep`
programs, so anything past the cap is by definition not among them; the cap only
has to be high enough that at least `keep` programs finish under it, which the
run reports.
"""
import os
import pathlib
import resource
import subprocess
import sys
import time

sys.path.insert(0, "/home/steve/showell_repos/codex-zig-ladder")
from cite_resolve import resolve, quire_dirs

TARGET = pathlib.Path(
    os.environ.get("CARGO_TARGET_DIR", os.path.expanduser("~/build/rust-target"))
) / "release"
BIN = TARGET / "codexrun"
RUN_TIMEOUT = 3.0
MEM_LIMIT = 4 << 30


def _cap():
    resource.setrlimit(resource.RLIMIT_AS, (MEM_LIMIT, MEM_LIMIT))


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    out = pathlib.Path(sys.argv[1])
    keep = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    root = pathlib.Path(os.environ["CODEX_ROOT"])
    units = out / "units"
    units.mkdir(parents=True, exist_ok=True)

    progs = sorted((root / "codex" / "test").rglob("*.codex"))
    print(f"stage 1: resolving {len(progs)} programs", flush=True)
    dirs = quire_dirs()
    resolved, unresolved = [], 0
    for p in progs:
        try:
            text, missing = resolve(p, dirs)
        except Exception:
            unresolved += 1
            continue
        if missing:
            unresolved += 1
            continue
        u = units / f"{p.stem}.codex"
        u.write_text(text)
        resolved.append((p.stem, u, p))
    print(f"stage 1: {len(resolved)} resolve clean, {unresolved} do not", flush=True)

    print(f"stage 1b: running each under codexrun (cap {RUN_TIMEOUT}s)", flush=True)
    rows = []
    for i, (name, u, src) in enumerate(resolved):
        t0 = time.time()
        try:
            r = subprocess.run([str(BIN), str(u)], capture_output=True,
                               preexec_fn=_cap, timeout=RUN_TIMEOUT)
            secs = time.time() - t0
            outcome = "ok" if r.returncode == 0 else "nonzero"
            nout = len(r.stdout)
        except subprocess.TimeoutExpired:
            secs, outcome, nout = RUN_TIMEOUT, "timeout", 0
        rows.append((name, u.stat().st_size, secs, outcome, nout, str(src)))
        if (i + 1) % 100 == 0:
            done = sum(1 for r_ in rows if r_[4] > 0)
            print(f"  {i+1}/{len(resolved)}  {done} with output", flush=True)

    tsv = out / "screen.tsv"
    with tsv.open("w") as f:
        f.write("name\tunit_bytes\tsecs\toutcome\tout_bytes\tsource\n")
        for row in sorted(rows, key=lambda r_: r_[2]):
            f.write("\t".join(str(x) for x in row) + "\n")

    # **A PROGRAM WITH NO `.expected` CANNOT BE HELD TO UPSTREAM'S ANSWER**,
    # and that is the whole point of the set -- so it is not a candidate,
    # however fast it is. 1,457 of the corpus's 1,727 have one.
    def has_expected(src):
        return pathlib.Path(src).with_suffix(".expected").is_file()

    produced = [r_ for r_ in rows if r_[4] > 0 and has_expected(r_[5])]
    produced.sort(key=lambda r_: r_[2])
    withexp = sum(1 for r_ in rows if has_expected(r_[5]))
    print(f"\n{sum(1 for r_ in rows if r_[4] > 0)} produced output; "
          f"{withexp} have an .expected; {len(produced)} have both; "
          f"{sum(1 for r_ in rows if r_[3] == 'timeout')} timed out", flush=True)
    if len(produced) < keep:
        print(f"WARNING: only {len(produced)} finished under {RUN_TIMEOUT}s, "
              f"fewer than the {keep} asked for -- raise the cap", flush=True)
    chosen = produced[:keep]
    (out / "candidates.txt").write_text(
        "\n".join(c[0] for c in chosen) + "\n")
    if chosen:
        print(f"candidates: {len(chosen)}, "
              f"{chosen[0][2]:.3f}s to {chosen[-1][2]:.3f}s, "
              f"units {min(c[1] for c in chosen)}..{max(c[1] for c in chosen)} bytes",
              flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
