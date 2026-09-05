#!/usr/bin/env python3
"""RUN COBBLESTONE'S OWN FRONT END ON THE INTERPRETER, and grade its IR.

    ./ladder/rungs.py <subject.codex> [program ...]

`subject.codex` is the bundled compiler -- the transpiler subject with its
trailing harness dropped. Each program is BUNDLED FIRST, because the bank is a
bank of units: `neg-int-parse` alone is one definition and its gold carries
ListUtils and Tuple folded in, five type definitions and seven section titles.
The bundled text is then inlined as a Text literal in a harness chapter that
calls `compile-frontend-cdx`, run under `codexrun` and diffed against
`$CODEX_GOLDS/ir`.

THE HARNESS IS `emit-ir-uni`, THE DRIVER'S OWN IR MODE, with ONE deviation.
Emulating a driver's phases by hand is how every deviation gets in, so this
transcribes it: `compile-frontend-ir`, then `lift-ir-for-emit`, then a prune to
`ir-emit-roots` -- six names, `opening` and five servicer entry points. Without
that prune a one-definition program answers 22 KB of the ListUtils it cited.

The deviation is the CHAPTER NAME. `emit-ir-uni` passes the literal `"Program"`
and the bank says `NegIntParse`, because the bank was cut by `codexir` -- a
different front door on the same phases (`corpus_run.py:transpile`) -- which
names the entry chapter. So this passes the unit's LAST chapter name: a bundle
puts the cited chapters in front of the one that cited them. Measured against
`neg-int-parse`, that one line was the whole difference; the other 941 bytes
already agreed.

WHAT IS UNDER TEST IS THE INTERPRETER, NOT THE IR. The IR that comes out is
Cobblestone's own, by construction: the same algorithm, the same allocation
order, the same `(tvar N)` numbering. Agreement with the bank is not four
compilers agreeing, it is one compiler agreeing with itself on a fourth host.
That is still the most demanding interpreter test available here, and the
oracle is free and exact.

A DISAGREEMENT IS NOT AUTOMATICALLY A DEFECT. The bank was cut from bare metal
at `53b3b213`, on master-plus-outbound; a subject built from a later tree is a
later compiler, and the front end has moved since. Read a diff by asking which
tree it came from before asking what is wrong with the interpreter.
"""
import os
import pathlib
import resource
import subprocess
import sys
import tempfile
import time

GOLDS = pathlib.Path(os.environ.get("CODEX_GOLDS", "")) 
TARGET = pathlib.Path(
    os.environ.get("CARGO_TARGET_DIR", os.path.expanduser("~/build/rust-target"))
) / "release"
BIN = TARGET / "codexrun"
BUNDLE = TARGET / "bundle"

# The harness is one chapter, and its name has to be one no subject uses.
HARNESS = '''

Chapter: Parsmi--Rungs

Section: Subject

  src : Text
  src = "{src}"

Section: Entry

  opening : [Console] Nothing = act
    let mb = init-phase-allocator
    in let db = __heap-save
    in let ds = __deck-set db
    in let da = __heap-advance 536870912
    in let fe = compile-frontend-ir src "{name}" compile-flags-default
    in act
      print-codegen-error-header (bag-errors (fe.bag))
      if bag-has-errors (fe.bag) then print-line-uni "CODEGEN-HALTED: errors in bag; no IR emitted"
      else let lifted-ir = lift-ir-for-emit (fe.ir) compile-flags-default
       in print-uni (emit-ir-chapter (ir-prune-unreachable-roots lifted-ir ir-emit-roots) (fe.text-meta) (fe.type-defs))
    end
  end
'''


# ONE GIGABYTE PER PROGRAM, and a program that wants more is a refusal rather
# than a dead sweep. This box has 8 GB and the whole compiler is in the
# interpreter's heap before the subject program is even read; a run that grew
# without bound took the kernel's OOM killer to the sweep and lost every
# verdict already earned, because a killed process flushes nothing.
MEM_LIMIT = 1 << 30

# And two minutes. `shell-build-keep` is the slowest that finishes, at 31
# seconds; a program still running at four times that is not going to answer.
RUN_TIMEOUT = 120


def _cap_memory():
    resource.setrlimit(resource.RLIMIT_AS, (MEM_LIMIT, MEM_LIMIT))


class Refused(Exception):
    """This program never reached the interpreter, and why.

    A refusal here is about the HARNESS -- a cite it cannot resolve, a byte it
    cannot quote -- and says nothing about the interpreter. Kept apart from a
    diff for that reason, and counted separately.
    """


def quote(text):
    """A Codex Text literal holding this source.

    NON-ASCII IS REFUSED RATHER THAN GUESSED AT. Codex source is CCE on the way
    in and a byte above 127 means the file carries something this escape cannot
    honestly represent; silently mangling it would produce a diff nobody could
    read.
    """
    if any(ord(c) > 127 for c in text):
        raise Refused("non-ASCII source: this harness cannot quote it")
    esc = {"\\": "\\\\", '"': '\\"', "\n": "\\n", "\t": "\\t"}
    return "".join(esc.get(c, c) for c in text)


def bundled(path):
    """The unit this program is, cites folded in.

    `bundle` writes its complaints to stdout and its unit to a file, so the
    complaints are not mixed into the source. A DEAD QUIRE line is about the
    registry pointing at a checkout that is not here and says nothing about
    this program, so it is not fatal.
    """
    with tempfile.NamedTemporaryFile(suffix=".codex", delete=False) as f:
        out = f.name
    r = subprocess.run(
        [str(BUNDLE), "one", str(path.resolve()), out],
        capture_output=True, text=True, cwd=path.resolve().parent,
    )
    if r.returncode != 0:
        os.unlink(out)
        raise Refused(r.stderr.strip().splitlines()[-1][:90] if r.stderr.strip() else "bundle refused")
    text = pathlib.Path(out).read_text()
    os.unlink(out)
    return text


def main():
    if len(sys.argv) < 3:
        raise SystemExit(__doc__)
    subject = pathlib.Path(sys.argv[1]).read_text()
    for b in (BIN, BUNDLE):
        if not b.is_file():
            raise SystemExit(f"no {b.name} at {b}")
    if not (GOLDS / "ir").is_dir():
        raise SystemExit("set CODEX_GOLDS to a gold set with an ir/ directory")

    agree = differ = refused = 0
    for arg in sys.argv[2:]:
        path = pathlib.Path(arg)
        name = path.stem
        gold = GOLDS / "ir" / f"{name}.ir"
        if not gold.is_file():
            print(f"{name:34} NO GOLD", flush=True)
            continue
        try:
            src = bundled(path)
            harness_src = quote(src)
        except Refused as e:
            refused += 1
            print(f"{name:34} REFUSED  {'':7} {e}", flush=True)
            continue
        # A bundle puts the cited chapters first, so the entry is the last one.
        chapters = [l.split(":", 1)[1].strip() for l in src.splitlines() if l.startswith("Chapter:")]
        harness = HARNESS.format(src=harness_src, name=chapters[-1] if chapters else name)
        with tempfile.NamedTemporaryFile("w", suffix=".codex", delete=False) as f:
            f.write(subject + harness)
            unit = f.name
        t0 = time.time()
        try:
            r = subprocess.run(
                [str(BIN), unit],
                capture_output=True,
                text=True,
                preexec_fn=_cap_memory,
                timeout=RUN_TIMEOUT,
            )
        except subprocess.TimeoutExpired:
            os.unlink(unit)
            refused += 1
            print(f"{name:34} REFUSED  {RUN_TIMEOUT:6.2f}s  timed out", flush=True)
            continue
        secs = time.time() - t0
        os.unlink(unit)
        if r.returncode != 0:
            refused += 1
            print(f"{name:34} REFUSED  {secs:6.2f}s  {r.stderr.strip().splitlines()[-1][:90]}", flush=True)
        # `print-codegen-error-header` prints one empty line when there are no
        # errors, and the bank starts at `(chapter`. Leading blank lines are
        # the header's, never the chapter's.
        elif r.stdout.lstrip("\n") == gold.read_text():
            agree += 1
            print(f"{name:34} agrees   {secs:6.2f}s  {len(r.stdout)} bytes", flush=True)
        else:
            differ += 1
            print(f"{name:34} DIFFERS  {secs:6.2f}s  {len(r.stdout)} bytes vs {gold.stat().st_size}", flush=True)
    print(f"\n{agree} agree, {differ} differ, {refused} refused")
    return 1 if differ or refused else 0


if __name__ == "__main__":
    sys.exit(main())
