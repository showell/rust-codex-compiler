#!/usr/bin/env python3
"""THE INTERPRETED FRONT END, COMPILING THE FRONT END, ONE CHAPTER AT A TIME.

    ./ladder/ramp.py <subject.codex> [chapter.codex ...]

`subject.codex` is the bundled compiler -- the transpiler subject with its
trailing harness dropped. Every other argument is a program to compile with it.
With none, the compiler's own 65 chapters are the ramp, smallest bundle first.

WHY A RAMP AND NOT THE WHOLE THING. `fib` is two definitions and the compiler
is 6,431, and nothing measured so far says which way the cost curve bends: on
safari's units, 386,602 steps peaks at 50.8 MB while 720,886,624 steps peaks at
42.3, so memory tracks LIVE DATA and not run length. A ramp says which of those
the self-compile is, before an afternoon is spent finding out.

ONE SUBJECT PER PROCESS, CAPPED, AND WRITTEN DOWN AS IT GOES. A run that dies
on its ninth subject must keep the eight it earned: an unbounded run took the
kernel's OOM killer to a sweep here once and lost every verdict, because a
killed process flushes nothing. So each subject is a child with an address-space
cap and a timeout, each verdict is appended to the TSV and flushed before the
next child starts, and a re-run SKIPS what the TSV already holds. Interrupt it,
raise the cap, run it again -- it picks up where it stopped.

THE CAP IS PER CHILD AND DELIBERATELY LOW. The point of the exercise is to find
where the interpreter stops fitting, and a cap that is generous enough never to
fire tells you nothing until it takes the box down with it.
"""

import os
import pathlib
import re
import resource
import subprocess
import sys
import tempfile
import time

TARGET = pathlib.Path(
    os.environ.get("CARGO_TARGET_DIR", os.path.expanduser("~/build/rust-target"))
) / "release"
BIN = TARGET / "codexrun"
BUNDLE = TARGET / "bundle"

COMPILER = pathlib.Path(
    "/home/steve/showell_repos/cobblestone-safari/codex/compiler"
)
LEDGER = pathlib.Path("ramp.tsv")

# Four gigabytes and ten minutes per subject, on an eight-gigabyte box.
MEM_LIMIT = 4 << 30
RUN_TIMEOUT = 600

HARNESS = '''

Chapter: Parsmi--Ramp

Section: Subject

  src : Text
  src = "{src}"

Section: Entry

  opening : [Console] Nothing = act
    let mb = init-phase-allocator
    in let db = __heap-save
    in let ds = __deck-set db
    in let da = __heap-advance 536870912
    in let fe = compile-frontend-ir src "Program" compile-flags-default
    in if bag-has-errors (fe.bag) then print-uni "CODEGEN-HALTED"
    else let lifted-ir = lift-ir-for-emit (fe.ir) compile-flags-default
    in print-uni (emit-ir-chapter (ir-prune-unreachable-roots lifted-ir ir-emit-roots) (fe.text-meta) (fe.type-defs))
  end
'''

COLUMNS = ["chapter", "bundle_bytes", "verdict", "steps", "secs", "peak_mb", "ir_bytes", "detail"]


def cap_memory():
    resource.setrlimit(resource.RLIMIT_AS, (MEM_LIMIT, MEM_LIMIT))


def quote(text):
    """A Codex Text literal holding this source. Non-ASCII is refused rather
    than mangled into a diff nobody can read."""
    if any(ord(c) > 127 for c in text):
        raise ValueError("non-ASCII source")
    esc = {"\\": "\\\\", '"': '\\"', "\n": "\\n", "\t": "\\t"}
    return "".join(esc.get(c, c) for c in text)


def bundled(path):
    """The unit this chapter is, cites folded in. A chapter of the compiler
    cites a dozen others, so the bundle is the honest measure of the subject
    and the file on disk is not."""
    with tempfile.NamedTemporaryFile(suffix=".codex", delete=False) as f:
        out = f.name
    r = subprocess.run([str(BUNDLE), "one", str(path.resolve()), out],
                       capture_output=True, text=True, cwd=path.resolve().parent)
    if r.returncode != 0:
        os.unlink(out)
        raise ValueError((r.stderr.strip().splitlines() or ["bundle refused"])[-1][:80])
    text = pathlib.Path(out).read_text()
    os.unlink(out)
    return text


def already_done():
    if not LEDGER.is_file():
        return {}
    rows = {}
    for line in LEDGER.read_text().splitlines()[1:]:
        parts = line.split("\t")
        if parts:
            rows[parts[0]] = parts
    return rows


def append(row):
    """One row, on disk, before the next child starts. The header is written
    only when the file is new, so a resumed run appends rather than restarts."""
    new = not LEDGER.is_file()
    with LEDGER.open("a") as f:
        if new:
            f.write("\t".join(COLUMNS) + "\n")
        f.write("\t".join(str(c) for c in row) + "\n")
        f.flush()
        os.fsync(f.fileno())


def one(subject, path):
    """Compile one chapter with the interpreted front end. Answers a row."""
    name = path.stem
    try:
        src = bundled(path)
        body = quote(src)
    except ValueError as e:
        return [name, 0, "SKIPPED", "", "", "", "", str(e)]

    with tempfile.NamedTemporaryFile("w", suffix=".codex", delete=False) as f:
        f.write(subject + HARNESS.format(src=body))
        unit = f.name
    t0 = time.time()
    try:
        r = subprocess.run([str(BIN), "ramp", unit], capture_output=True, text=True,
                           preexec_fn=cap_memory, timeout=RUN_TIMEOUT)
    except subprocess.TimeoutExpired:
        os.unlink(unit)
        return [name, len(src), "TIMEOUT", "", f"{RUN_TIMEOUT}", "", "", f"over {RUN_TIMEOUT}s"]
    finally:
        if os.path.exists(unit):
            os.unlink(unit)
    secs = time.time() - t0

    stats = re.search(r"steps=(\d+) secs=([\d.]+) peak-mb=([\d.]+)", r.stderr)
    if r.returncode != 0 or not stats:
        # The cap fires as an allocation failure the runtime aborts on, so the
        # message names memory rather than the subject. Either way it is one
        # row and the ramp goes on.
        last = (r.stderr.strip().splitlines() or ["no output"])[-1][:80]
        verdict = "OUT-OF-MEMORY" if "memory allocation" in r.stderr else "FAILED"
        return [name, len(src), verdict, "", f"{secs:.1f}", "", "", last]
    steps, isecs, peak = stats.groups()
    halted = r.stdout.startswith("CODEGEN-HALTED")
    return [name, len(src), "HALTED" if halted else "ok", steps, isecs, peak,
            len(r.stdout), "the compiler refused it" if halted else ""]


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    subject = pathlib.Path(sys.argv[1]).read_text()
    for b in (BIN, BUNDLE):
        if not b.is_file():
            raise SystemExit(f"no {b.name} at {b}")

    if len(sys.argv) > 2:
        paths = [pathlib.Path(a) for a in sys.argv[2:]]
    else:
        paths = sorted(COMPILER.rglob("*.codex"))

    # Smallest bundle first, so the curve is learned before it is expensive.
    # The bundle is cheap; the interpretation is not.
    sized = []
    for p in paths:
        try:
            sized.append((len(bundled(p)), p))
        except ValueError:
            sized.append((0, p))
    sized.sort()

    done = already_done()
    print(f"{'chapter':34} {'bundle':>9} {'verdict':>14} {'steps':>12} {'secs':>7} {'peak MB':>8}")
    for _, p in sized:
        if p.stem in done:
            r = done[p.stem]
            print(f"{p.stem:34} {r[1]:>9} {r[2]:>14} {r[3]:>12} {r[4]:>7} {r[5]:>8}  (from the ledger)")
            continue
        row = one(subject, p)
        append(row)
        print(f"{row[0]:34} {row[1]:>9} {row[2]:>14} {row[3]:>12} {row[4]:>7} {row[5]:>8}"
              + (f"  {row[7]}" if row[7] else ""), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
