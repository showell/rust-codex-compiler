#!/usr/bin/env python3
"""ONE COMPILER, ONE SOURCE, TWO HOSTS -- and nothing else allowed to vary.

    CODEX_ROOT=<checkout> ./ladder/hosts.py <subject.codex> [program ...]

THE CONTROL IS `codexir`, NOT THE BANK. `codexir` is built from
`generated/codexir-subject.codex`; `subject.codex` is that same file with its
trailing harness cut off. So the two arms are the same compiler, from the same
bytes, at the same pin, and the ONLY variable is the host: a Rust tree-walker
against a native binary. A disagreement is an interpreter defect and there is
no third explanation to reach for.

WHY NOT GRADE AGAINST `$CODEX_GOLDS/ir`. The bank is a different pin, a
different tree AND a different resolver, so a diff against it carries three
confounds at once and none of them is the thing under test. That is not
hypothetical: the bank was cut through `cite_resolve.py`, which reads in text
mode, so Python's universal newlines stripped every carriage return before bare
metal saw one -- and the bank was then cited as PROVING that the lexer treats a
carriage return as trivia, a byte no gold in the set contains. Twenty-seven
programs read as interpreter failures that were a line ending. The bank is a
coverage net: it says which programs are worth running. It does not get a vote.

THE CHAPTER NAME IS `"Program"`, WHICH REMOVES THE LAST FUDGE. `codexir`'s
harness passes that literal, so passing it here too makes the comparison raw
bytes -- no normalising pass, nothing to get subtly wrong. The bank names the
entry chapter instead, which is why grading against it ever needed one.

The unit comes from `cite_resolve.py` because `bundle` now REFUSES to write a
unit carrying a carriage return, and fifteen `codex/foreword/*` chapters are
CRLF. Reading in text mode is the normalising step that refusal asks the caller
for, and it is what the corpus has always been resolved with.
"""
import os
import pathlib
import resource
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, "/home/steve/showell_repos/codex-zig-ladder")
from cite_resolve import resolve

TARGET = pathlib.Path(
    os.environ.get("CARGO_TARGET_DIR", os.path.expanduser("~/build/rust-target"))
) / "release"
BIN = TARGET / "codexrun"
CODEXIR = pathlib.Path(
    "/home/steve/showell_repos/codex-zig-transpiler/generated/local/codexir")

MEM_LIMIT = 1 << 30
RUN_TIMEOUT = 180
ORACLE_TIMEOUT = 120

HARNESS = r'''

Chapter: Parsmi--Hosts

Section: Halt

 **`cir-halted` FROM `CodexIrHarness`, WORD FOR WORD.** A refusal has to read
 the same on both arms or the comparison needs a special case, and a special
 case is where a real disagreement hides. Printing every error instead of the
 count and the first one made four mutual refusals -- identical diagnostics,
 identical order -- read as four disagreements.

  hosts-halted : List Diagnostic -> Text
  hosts-halted (es) =
   let n = list-length es
   in let e0 = list-at es 0
   in "CODEGEN-HALTED: " & show n & " error(s); no IR emitted; first CDX" & show (e0.code) & " " & (e0.message) & "\n"

Section: Entry

  opening : [Console, FileSystem] Nothing = act
    src <- read-file-uni "{src}"
    let mb = init-phase-allocator
    in let db = __heap-save
    in let ds = __deck-set db
    in let da = __heap-advance 536870912
    in let fe = compile-frontend-ir src "Program" compile-flags-default
    in if bag-has-errors (fe.bag) then print-uni (hosts-halted (bag-errors (fe.bag)))
    else let lifted-ir = lift-ir-for-emit (fe.ir) compile-flags-default
    in print-uni (emit-ir-chapter (ir-prune-unreachable-roots lifted-ir ir-emit-roots) (fe.text-meta) (fe.type-defs))
  end
'''


def _cap_memory():
    resource.setrlimit(resource.RLIMIT_AS, (MEM_LIMIT, MEM_LIMIT))


def main():
    if len(sys.argv) < 3:
        raise SystemExit(__doc__)
    if "CODEX_ROOT" not in os.environ:
        raise SystemExit("set CODEX_ROOT to the checkout the SUBJECT was built from")
    subject = pathlib.Path(sys.argv[1]).read_text()
    for b in (BIN, CODEXIR):
        if not b.is_file():
            raise SystemExit(f"no {b.name} at {b}")

    tally = {}
    for arg in sys.argv[2:]:
        path = pathlib.Path(arg)
        name = path.stem
        unit_text, missing = resolve(path.resolve())
        if missing:
            verdict = "UNRESOLVED"
            detail = "; ".join(f"{q}/{n}" for _, q, n in missing[:2])
        else:
            with tempfile.NamedTemporaryFile("w", suffix=".codex", delete=False) as f:
                f.write(unit_text)
                src_path = f.name
            with tempfile.NamedTemporaryFile("w", suffix=".codex", delete=False) as f:
                f.write(subject + HARNESS.format(src=src_path))
                unit = f.name
            t0 = time.time()
            try:
                r = subprocess.run([str(BIN), unit], capture_output=True, text=True,
                                   preexec_fn=_cap_memory, timeout=RUN_TIMEOUT)
                ours, why = r.stdout.lstrip("\n"), None
                if r.returncode != 0:
                    why = r.stderr.strip().splitlines()[-1][:70] if r.stderr.strip() else "nonzero"
            except subprocess.TimeoutExpired:
                ours, why = "", f"timed out at {RUN_TIMEOUT}s"
            secs = time.time() - t0
            os.unlink(unit)
            with open(src_path, "rb") as fh:
                o = subprocess.run([str(CODEXIR)], stdin=fh, capture_output=True,
                                   timeout=ORACLE_TIMEOUT)
            oracle = o.stderr.decode("utf-8", "replace")
            os.unlink(src_path)
            # Raw bytes, both ways. Both harnesses pass the chapter literal
            # "Program" and both refuse in `cir-halted`'s words, so there is
            # nothing left for a normalising pass to be wrong about.
            if why:
                verdict, detail = "REFUSED", why
            elif ours == oracle:
                kind = "halt" if ours.startswith("CODEGEN-HALTED") else "bytes"
                verdict, detail = "agree", f"{len(ours)} {kind}"
            else:
                verdict = "DIFFERS"
                detail = f"{len(ours)} vs codexir {len(oracle)}"
                halts = (ours.startswith("CODEGEN-HALTED"), oracle.startswith("CODEGEN-HALTED"))
                if halts[0] != halts[1]:
                    detail += "  (one halted, one did not)"
        tally[verdict] = tally.get(verdict, 0) + 1
        print(f"{name:34} {verdict:11} {secs if not missing else 0:6.2f}s  {detail}",
              flush=True)
    print("\n" + "  ".join(f"{v}: {n}" for v, n in sorted(tally.items())), flush=True)
    return 1 if tally.get("DIFFERS") or tally.get("REFUSED") else 0


if __name__ == "__main__":
    sys.exit(main())
