#!/usr/bin/env python3
"""Does this compiler's resolver build the unit upstream's compile step builds?

    tools/resolver_agree.py <checkout>

For every program under <checkout>/codex/test except apps/, it compares the
chapter headers of two units:

  ours      `bundle one <program>`, this compiler's resolver
  upstream  build/compile.ps1's Resolve-CiteOrder and Format-CiteChapters,
            run over every program by tools/r2_headers.ps1 in one pwsh process

It compares headers, not bytes: upstream separates chapters with two blank
lines and this compiler with one, and neither says anything about what the unit
is. The binary is $BUNDLE, default ~/build/rust-target/release/bundle.

One line per disagreement, then a count by kind. Exits 1 on any disagreement; a
program both resolvers refuse is listed and is not one.
"""
import concurrent.futures
import os
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
BUNDLE = os.environ.get("BUNDLE", os.path.expanduser("~/build/rust-target/release/bundle"))
PWSH = os.path.expanduser("~/.local/pwsh/pwsh")


def headers(text):
    return [l[len("Chapter:"):].strip() for l in text.splitlines() if l.startswith("Chapter:")]


def ours(path):
    r = subprocess.run([BUNDLE, "one", str(path)], capture_output=True, text=True)
    if r.returncode == 2:
        why = (r.stderr.strip().splitlines() or ["?"])[-1].removeprefix("REFUSED: ")
        return "REFUSED", why, []
    kind = "UNRESOLVED" if r.returncode == 1 else "OK"
    note = next((l for l in r.stderr.splitlines() if l.startswith("UNRESOLVED")), "")
    return kind, note, headers(r.stdout)


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: tools/resolver_agree.py <checkout>")
    checkout = pathlib.Path(sys.argv[1]).expanduser().resolve()
    tests = checkout / "codex" / "test"
    programs = sorted(p for p in tests.rglob("*.codex") if "apps" not in p.relative_to(tests).parts)
    if not programs:
        raise SystemExit(f"no programs under {tests}")
    print(f"checkout  {checkout}\nprograms  {len(programs)}\nbundle    {BUNDLE}\n", flush=True)

    r = subprocess.run([PWSH, "-NoProfile", "-File", str(HERE / "r2_headers.ps1"), "-Checkout", str(checkout)],
                       input="\n".join(map(str, programs)) + "\n", capture_output=True, text=True)
    theirs = {}
    for line in r.stdout.splitlines():
        path, kind, rest = (line.split("\t", 2) + ["", ""])[:3]
        theirs[path] = (kind, rest.split("|") if kind == "OK" and rest else [], rest)
    if len(theirs) != len(programs):
        raise SystemExit(f"upstream's resolver answered for {len(theirs)} of {len(programs)} programs\n{r.stderr[-800:]}")

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        mine = dict(zip(programs, pool.map(ours, programs)))

    counts = {}
    for p in programs:
        rel = p.relative_to(tests)
        okind, onote, oh = mine[p]
        tkind, th, twhy = theirs[str(p)]
        if okind in ("REFUSED", "UNRESOLVED") and tkind == "THROW":
            kind, say = "both refuse", f"ours: {onote[:70]} | upstream: {twhy[:70]}"
        elif okind == "REFUSED":
            kind, say = "ours refuses", onote[:150]
        elif tkind == "THROW":
            kind, say = "upstream throws", twhy[:150]
        elif oh == th:
            kind, say = ("agree, both unresolved" if okind == "UNRESOLVED" else "agree"), ""
        elif sorted(oh) == sorted(th):
            kind, say = "same chapters, other order", f"ours {oh[:4]} upstream {th[:4]}"
        else:
            only_o = [h for h in oh if h not in th]
            only_t = [h for h in th if h not in oh]
            kind, say = "different chapters", f"only ours {only_o[:4]} only upstream {only_t[:4]}"
        counts[kind] = counts.get(kind, 0) + 1
        if not kind.startswith("agree"):
            print(f"{kind:<28} {rel}  {say}")
    print()
    for kind, n in sorted(counts.items(), key=lambda kv: -kv[1]):
        print(f"{n:6d}  {kind}")
    return 0 if all(k.startswith("agree") or k == "both refuse" for k in counts) else 1


if __name__ == "__main__":
    sys.exit(main())
