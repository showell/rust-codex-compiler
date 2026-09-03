#!/usr/bin/env python3
"""Move a set of definitions out of one chapter into a new chapter file.

    extract_chapter.py <src.codex> <header.txt> <plan.txt> <out.codex>

`plan.txt` is `Section: <name>` lines and definition names, in the order the new
chapter should read. `header.txt` is the new chapter's `Chapter:` line, its
cites and its opening prose, verbatim.

WHAT MAKES THIS DIFFERENT FROM SPLITTING ON BLANK LINES: the byte ranges come
from `cohesion --blocks`, which reads the parser's own tree. A block is the
definition plus the prose above it, stopping at a `Section:` header -- so prose
cannot be misattributed to a neighbour, and a header cannot be dragged along
behind a definition that happens to follow it.

Nothing is written unless every planned name exists exactly once in the source.
The definitions left behind keep their own sections and prose untouched.
"""
import subprocess, sys, pathlib, collections

BIN = '/home/steve/showell_repos/rust-codex-compiler/target/release/cohesion'

def main(src_path, header_path, plan_path, out_path):
    src = pathlib.Path(src_path).read_bytes()

    blocks = {}
    order = []
    for line in subprocess.run([BIN, '--blocks', src_path], capture_output=True,
                               text=True, check=True).stdout.splitlines():
        if not line.startswith('block '):
            continue
        _, a, b, rest = line.split(None, 3)
        name = rest.split('  [')[0].strip()
        if name in blocks:
            sys.exit(f"refusing: {name} is defined twice in {src_path}")
        blocks[name] = (int(a), int(b))
        order.append(name)

    plan, seen = [], set()
    for raw in pathlib.Path(plan_path).read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith('#'):
            continue
        if line.startswith('Section:'):
            plan.append(('section', line))
            continue
        if line not in blocks:
            sys.exit(f"refusing: `{line}` is not a definition in {src_path}")
        if line in seen:
            sys.exit(f"refusing: `{line}` is planned twice")
        seen.add(line)
        plan.append(('def', line))

    # Build the new chapter.
    out = [pathlib.Path(header_path).read_text().rstrip('\n'), '']
    for kind, val in plan:
        if kind == 'section':
            out += ['', val]
        else:
            out.append(src[slice(*blocks[val])].decode().strip('\n'))
            out.append('')
    pathlib.Path(out_path).write_text('\n'.join(out).rstrip('\n') + '\n')

    # Cut the moved ranges out of the source, back to front so offsets hold.
    keep = bytearray(src)
    for name in sorted(seen, key=lambda n: -blocks[n][0]):
        a, b = blocks[name]
        del keep[a:b]
    text = keep.decode()
    while '\n\n\n\n' in text:
        text = text.replace('\n\n\n\n', '\n\n\n')
    pathlib.Path(src_path).write_text(text)

    left = [n for n in order if n not in seen]
    print(f"moved {len(seen)} definitions to {out_path}; {len(left)} remain in {src_path}")

if __name__ == '__main__':
    if len(sys.argv) != 5:
        sys.exit(__doc__)
    main(*sys.argv[1:])
