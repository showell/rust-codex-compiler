#!/usr/bin/env python3
"""**STAGES 2-6: FROM CANDIDATES TO A SET WORTH DEMANDING PERFECTION FROM.**

    ./ladder/curate2.py <outdir> [final]

Reads `<outdir>/candidates.txt` and `<outdir>/units/`, and for each program:

  2  `codexir` compiles it and emits a chapter -- no CODEGEN-HALTED, no empty
     output.
  3  how many diagnostics it emits on the way. A program the compiler complains
     about is not one to measure other things against.
  4  what it costs: unit bytes, and the compile's own seconds.
  5  WHICH LANGUAGE FORMS IT USES, read off `checkdump lower` -- the node kinds
     the desugared tree actually contains.
  6  whether running it reproduces upstream's `.expected`, byte for byte --
     built by UPSTREAM'S OWN COMPILER: `codexzig` to zig, `zig build-exe`, run.
     Using our interpreter here would be seconds instead of minutes and would
     bias the set towards what we already handle; the whole value of the set is
     that it is a gate we do not grade ourselves. Stage 6 runs LAST, on what
     survives the cheap gates, because it is the only expensive one.

THEN IT CHOOSES, and the choice is not "the fastest N". The fastest programs are
fast because they do nothing; a set picked that way has three records in it and
finds out on the first experiment that touches records. This takes a greedy set
cover over the node kinds in stage 5 -- cheapest program that adds an unseen
form, until no form is left to add -- and only then fills the remainder with the
cheapest that pass every gate. Coverage first, speed as the tie-break.
"""
import collections
import os
import pathlib
import subprocess
import sys
import time

TARGET = pathlib.Path(
    os.environ.get("CARGO_TARGET_DIR", os.path.expanduser("~/build/rust-target"))
) / "release"
RUN = TARGET / "codexrun"
CHECKDUMP = TARGET / "checkdump"
LOCAL = pathlib.Path("/home/steve/showell_repos/codex-zig-transpiler/generated/local")
CODEXIR = LOCAL / "codexir"
CODEXZIG = LOCAL / "codexzig"


def native_output(unit, work):
    """Compile with upstream's compiler and RUN it. Returns (text, why).

    `codexzig` emits its zig on STDERR, the same convention `codexir` uses for
    IR -- stdout carries diagnostics.
    """
    zig = work / "p.zig"
    exe = work / "p"
    r = subprocess.run([str(CODEXZIG)], stdin=unit.open("rb"),
                       capture_output=True, timeout=180)
    zig.write_bytes(r.stderr)
    head = zig.read_text(errors="replace")[:400]
    if head.startswith("CODEGEN-HALTED") or not zig.stat().st_size:
        return None, "codexzig refused"
    b = subprocess.run(["zig", "build-exe", str(zig), f"-femit-bin={exe}"],
                       capture_output=True, text=True, cwd=str(work), timeout=300)
    if b.returncode != 0 or not exe.is_file():
        return None, "zig build-exe failed"
    try:
        p = subprocess.run([str(exe)], capture_output=True, timeout=30)
    except subprocess.TimeoutExpired:
        return None, "ran over 30s"
    # **A COMPILED CODEX PROGRAM PRINTS ON STDERR**, the same convention
    # `codexzig` and `codexir` use for their own output. Reading stdout gets an
    # empty string, which compares unequal to every `.expected` there is -- 298
    # of 298 "differed" against a file the program reproduces byte for byte.
    return p.stderr.decode("utf-8", "replace"), None


def kinds(unit):
    """The node kinds the desugared tree contains, from `checkdump lower`."""
    r = subprocess.run([str(CHECKDUMP), "lower", str(unit)],
                       capture_output=True, text=True, timeout=60)
    out = set()
    for line in r.stdout.splitlines():
        f = line.split()
        if f and f[0].startswith("e") and len(f) > 1:
            out.add(f[1].split(":")[0])
        elif line.startswith("irdef ") and " ty " in line:
            out.add("ty:" + line.rsplit(" ty ", 1)[1].strip())
    return out


def main():
    out = pathlib.Path(sys.argv[1])
    final = int(sys.argv[2]) if len(sys.argv) > 2 else 80
    shortlist = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    names = [l.strip() for l in (out / "candidates.txt").read_text().splitlines() if l.strip()]
    src_of = {}
    for line in (out / "screen.tsv").read_text().splitlines()[1:]:
        f = line.split("\t")
        src_of[f[0]] = (int(f[1]), float(f[2]), f[5])

    # **EVERY ROW LANDS ON DISK AS IT IS MEASURED.** An earlier version
    # accumulated in memory and wrote once at the end, so an interrupted run
    # threw away everything it had done -- eleven minutes of compiles, gone,
    # with only a scrolled-past count to show for it. A stage that costs
    # minutes has to be resumable, and appending is the whole of it.
    gates = out / "gates.tsv"
    done = {}
    if gates.is_file():
        for line in gates.read_text().splitlines()[1:]:
            f = line.split("\t")
            if len(f) >= 8:
                done[f[0]] = f
        print(f"resuming: {len(done)} rows already measured", flush=True)
    else:
        gates.write_text("name\tunit_bytes\trun_s\tir_s\tir_bytes\tdiags"
                         "\tsource\tkinds\n")

    rows = []
    print(f"stages 2-5 over {len(names)} candidates", flush=True)
    for i, name in enumerate(names):
        if name in done:
            f = done[name]
            rows.append({
                "name": f[0], "unit": int(f[1]), "run": float(f[2]),
                "ir_secs": float(f[3]), "ir_bytes": int(f[4]),
                "diags": int(f[5]), "expected": "pending", "src": f[6],
                "kinds": set(f[7].split(",")) if f[7] else set(),
            })
            continue
        unit = out / "units" / f"{name}.codex"
        ubytes, run_secs, src = src_of[name]
        t0 = time.time()
        try:
            r = subprocess.run([str(CODEXIR)], stdin=unit.open("rb"),
                               capture_output=True, timeout=120)
        except subprocess.TimeoutExpired:
            continue
        ir_secs = time.time() - t0
        ir = r.stderr.decode("utf-8", "replace")
        if not ir.startswith("(chapter"):
            continue                                   # stage 2
        diags = len([l for l in r.stdout.decode("utf-8", "replace").splitlines()
                     if l.strip()])                    # stage 3
        rows.append({
            "name": name, "unit": ubytes, "run": run_secs, "ir_secs": ir_secs,
            "ir_bytes": len(ir), "diags": diags, "expected": "pending",
            "src": src, "kinds": kinds(unit),
        })
        r_ = rows[-1]
        with gates.open("a") as fh:
            fh.write(f"{r_['name']}\t{r_['unit']}\t{r_['run']:.4f}\t"
                     f"{r_['ir_secs']:.4f}\t{r_['ir_bytes']}\t{r_['diags']}\t"
                     f"{r_['src']}\t{','.join(sorted(r_['kinds']))}\n")
        if (i + 1) % 50 == 0:
            print(f"  {i+1}/{len(names)}  {len(rows)} passing stage 2", flush=True)

    # --- the shortlist stage 6 will pay for -------------------------------
    #
    # **THE SPEED GATE BARELY DISCRIMINATES**, so it must not be what chooses.
    # Five hundred of the corpus's eligible programs finish inside ten
    # milliseconds -- process startup -- and picking "the fastest N" out of that
    # floor is picking by noise, which can drop the only program that uses a
    # form. Coverage picks the shortlist; speed breaks ties inside it.
    rows.sort(key=lambda r_: (r_["run"] + r_["ir_secs"]))
    seen, short = set(), []
    for r_ in rows:
        if r_["kinds"] - seen:
            seen |= r_["kinds"]
            short.append(r_)
    print(f"  {len(short)} programs cover {len(seen)} node kinds", flush=True)
    for r_ in rows:
        if len(short) >= shortlist:
            break
        if r_ not in short:
            short.append(r_)
    skipped = [r_ for r_ in rows if r_ not in short]
    for r_ in skipped:
        r_["expected"] = "not-tried"
    rows = short

    # --- stage 6, last and only on the shortlist --------------------------
    import shutil, tempfile
    print(f"\nstage 6: building and running {len(rows)} with codexzig", flush=True)
    work = pathlib.Path(tempfile.mkdtemp(prefix="curate6-"))
    native = out / "native.tsv"
    seen6 = {}
    if native.is_file():
        for line in native.read_text().splitlines()[1:]:
            f = line.split("\t")
            if len(f) >= 2:
                seen6[f[0]] = f[1]
        print(f"  resuming stage 6: {len(seen6)} already built", flush=True)
    else:
        native.write_text("name\tverdict\n")
    for i, r_ in enumerate(rows):
        if r_["name"] in seen6:
            r_["expected"] = seen6[r_["name"]]
            continue
        exp = pathlib.Path(r_["src"]).with_suffix(".expected")
        if not exp.is_file():
            r_["expected"] = "no-expected"
            continue
        try:
            got, why = native_output(out / "units" / f"{r_['name']}.codex", work)
        except subprocess.TimeoutExpired:
            got, why = None, "timed out compiling"
        r_["expected"] = why if got is None else (
            "match" if got == exp.read_text() else "differs")
        with native.open("a") as fh:
            fh.write(f"{r_['name']}\t{r_['expected']}\n")
        if (i + 1) % 25 == 0:
            ok = sum(1 for x in rows[:i+1] if x["expected"] == "match")
            print(f"  {i+1}/{len(rows)}  {ok} match", flush=True)
    shutil.rmtree(work, ignore_errors=True)

    print(f"\nstage 2 (compiles):        {len(rows)}", flush=True)
    for label in sorted({r_["expected"] for r_ in rows}):
        n = sum(1 for r_ in rows if r_["expected"] == label)
        print(f"stage 6 {label:<18} {n}", flush=True)
    clean = [r_ for r_ in rows if r_["expected"] == "match"]
    print(f"\neligible (compiles AND reproduces .expected): {len(clean)}", flush=True)

    # --- the choice: coverage first, speed as tie-break --------------------
    clean.sort(key=lambda r_: (r_["run"] + r_["ir_secs"]))
    seen, chosen = set(), []
    for r_ in clean:
        if r_["kinds"] - seen:
            seen |= r_["kinds"]
            chosen.append(r_)
    covered = len(seen)
    for r_ in clean:
        if len(chosen) >= final:
            break
        if r_ not in chosen:
            chosen.append(r_)
    chosen.sort(key=lambda r_: r_["name"])
    (out / "final.txt").write_text("\n".join(r_["name"] for r_ in chosen) + "\n")
    every = set()
    for r_ in clean:
        every |= r_["kinds"]
    print(f"chose {len(chosen)}; {covered} of {len(every)} node kinds covered by "
          f"the first {sum(1 for r_ in chosen if r_['kinds'] - set())} picks", flush=True)
    print(f"total runtime of the set: "
          f"{sum(r_['run'] + r_['ir_secs'] for r_ in chosen):.1f}s", flush=True)
    miss = every - seen
    if miss:
        print(f"forms no eligible program uses: {' '.join(sorted(miss))}", flush=True)
    with (out / "final.tsv").open("w") as f:
        f.write("name\tunit_bytes\trun_s\tir_s\tir_bytes\tdiags\tkinds\n")
        for r_ in chosen:
            f.write(f"{r_['name']}\t{r_['unit']}\t{r_['run']:.3f}\t"
                    f"{r_['ir_secs']:.3f}\t{r_['ir_bytes']}\t{r_['diags']}\t"
                    f"{len(r_['kinds'])}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
