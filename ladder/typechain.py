#!/usr/bin/env python3
"""**A CHAIN OF TYPE DECLARATIONS COSTS EXPONENTIALLY, ON BOTH ARMS.**

    ./ladder/typechain.py [max-levels] [ctors-per-level]

Generates `L0 .. Lk`, each a variant whose constructors name the level below it
and itself, and times both arms on each depth. Nothing else is in the file.

WHAT IT SHOWS. At six constructors a level, every ADDED LEVEL multiplies the
work by roughly the constructor count -- 164 bytes of extra source for a ~5x
compile. A 1,112-byte file takes `codexir` 1.37s; the Rust interpreter, ~30x
slower per step, is off the end of the table long before that.

    depth   source   codexir      ours
        3    620 B    0.148s     0.39s     13.9M steps
        4    784 B    0.182s     1.57s     55.6M steps
        5    948 B    0.394s     8.52s    302.8M steps
        6   1112 B    1.446s        --
        7   1276 B    7.933s        --
        8   1440 B   44.034s        --

**A 1,440-BYTE SOURCE FILE TAKES THE NATIVE COMPILER 44 SECONDS**, and the
next level would take four minutes. Eight type declarations, six constructors
each, no definitions at all.

WHY IT IS NOT AN INTERPRETER PROBLEM. `codexir` is the compiler compiled to
native code and it grows on the same curve -- 5 to 6x a level once its ~0.14s
of fixed cost is subtracted. Our arm hits the wall three levels earlier because
each step costs more, which is why this looked like ours at first.

WHERE THE TIME GOES, from the sampling profiler (`CODEXRUN_PROGRESS=1`):

    28.5%  fold-children-list         13.5%  codex-type-fold-children
    16.7%  fold-children-sum-ctors    17.6%  ty-has-typevars (+ its fold)

-- all of it walking CodexType trees. `build-sum-ctors` resolves a
constructor's field types against the partial type-definition map, which
already holds the FULL `SumTy` of every earlier declaration, so each level's
SumTy embeds the previous level's once per constructor. And `subst-type-var`
guards itself with `ty-has-typevars`, a full walk of the type, at every node it
recurses through.

THIS IS THE SHAPE THE DEPOT ACTUALLY WRITES. `Shell ShellTypes` is such a
chain, and it is why `shell-build-keep` -- NINETEEN LINES, a 24 KB resolved
unit -- takes `codexir` 1.17s where a larger 36 KB unit takes 0.27s.
"""
import os
import pathlib
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from hosts import BIN, CODEXIR, HARNESS, refuse_a_stale_binary

HERE = pathlib.Path(os.environ.get(
    "TMPDIR", "/tmp")) / "typechain"


def chain(levels, n):
    """`L0` self-recursive; every later level names the one below it."""
    out = ["  L0 =\n" + "\n".join(
        f"    | L0C{k} (Integer) (List L0)" for k in range(n))]
    for lv in range(1, levels):
        out.append(f"  L{lv} =\n" + "\n".join(
            f"    | L{lv}C{k} (L{lv-1}) (List L{lv})" for k in range(n)))
    return ("Chapter: T\n\nSection: S\n" + "\n\n".join(out)
            + "\n\nSection: E\n  opening : [Console] Nothing = act\n"
              "   print-line-uni \"x\"\n  end\n")


def secs(cmd, **kw):
    t0 = time.time()
    subprocess.run(cmd, capture_output=True, **kw)
    return time.time() - t0


def main():
    depth = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    subject = pathlib.Path(sys.argv[3]).read_text() if len(sys.argv) > 3 else None
    refuse_a_stale_binary(BIN)
    HERE.mkdir(parents=True, exist_ok=True)
    print(f"{'depth':>6} {'source':>8} {'codexir':>9} {'ours':>9}")
    for lv in range(1, depth + 1):
        unit = HERE / f"ch{lv}n{n}.unit"
        unit.write_text(chain(lv, n))
        g = secs([str(CODEXIR)], stdin=open(unit, "rb"))
        ours = "--"
        if subject is not None:
            prog = HERE / f"ch{lv}n{n}.codex"
            prog.write_text(subject + HARNESS.format(src=str(unit)))
            # Past five levels our arm is minutes; the native column alone
            # carries the curve.
            ours = f"{secs([str(BIN), str(prog)]):.3f}s" if lv <= 5 else "--"
        print(f"{lv:>6} {unit.stat().st_size:>7}B {g:>8.3f}s {ours:>9}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
