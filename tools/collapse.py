#!/usr/bin/env python3
"""Collapse every single-caller definition into its caller, repeatedly.

`--roots a,b,c` treats those names as exported too, which answers the question
"if I split these out, what would still be shared?" -- the leftovers are what
must sink into a chapter everything cites.

A node with exactly one predecessor is dominated by that predecessor, so
absorbing it changes no reachability. Iterate to a fixed point and what
survives is the SHARED SPINE: definitions two or more callers need, which are
exactly the ones that straddle any proposed cut. Steve's algorithm, 2026-09-03.

Interface names (read by another chapter) are roots and are never absorbed.
"""
import collections, subprocess, sys

argv = sys.argv[1:]
extra_roots = set()
if '--roots' in argv:
    i = argv.index('--roots')
    extra_roots = set(argv[i + 1].split(','))
    del argv[i:i + 2]
chapter, path = argv[0], argv[1]
dirs = argv[2:]
BIN = '/home/steve/showell_repos/rust-codex-compiler/target/release'

graph = subprocess.run([BIN + '/cohesion', '--graph', path],
                       capture_output=True, text=True).stdout
seams = subprocess.run([BIN + '/seams', chapter] + dirs,
                       capture_output=True, text=True).stdout

succ = collections.defaultdict(set)
nodes, section = set(), {}
for line in graph.splitlines():
    p = line.split()
    if not p: continue
    if p[0] == 'call':
        succ[p[1]].add(p[3]); nodes.add(p[1]); nodes.add(p[3])
    elif p[0] in ('def', 'isolated'):
        nodes.add(p[1])
        section[p[1]] = line.split('[', 1)[1].rstrip(']') if '[' in line else ''

iface = set()
grab = False
for line in seams.splitlines():
    if line.startswith('  INTERFACE'): grab = True; continue
    if grab:
        if not line.startswith('      '): break
        iface.update(line.split())
iface |= extra_roots

absorbed = {n: {n} for n in nodes}
changed = True
while changed:
    changed = False
    preds = collections.defaultdict(set)
    for a, bs in succ.items():
        for b in bs:
            if a != b: preds[b].add(a)
    for x in sorted(nodes):
        if x in iface or len(preds.get(x, ())) != 1: continue
        p = next(iter(preds[x]))
        if p not in nodes: continue
        succ[p] = (succ[p] | succ.get(x, set())) - {x, p}
        absorbed[p] |= absorbed.pop(x)
        succ.pop(x, None); nodes.discard(x)
        changed = True
        break

preds = collections.defaultdict(set)
for a, bs in succ.items():
    for b in bs:
        if a != b: preds[b].add(a)

print(f"{chapter}: collapsed to {len(nodes)} nodes from {len(absorbed) and sum(len(v) for v in absorbed.values())}\n")
print("SURVIVING BLOCKS -- each absorbed everything only it calls:")
for n in sorted(nodes, key=lambda n: -len(absorbed[n])):
    if len(absorbed[n]) == 1: continue
    secs = sorted({section.get(m, '') for m in absorbed[n]} - {''})
    print(f"\n  {n}  ({len(absorbed[n])} defs)  callers={len(preds.get(n, ()))}")
    print(f"      sections: {' + '.join(secs)}")
    print(f"      {' '.join(sorted(absorbed[n]))}")

print("\nSHARED SPINE -- survived because two or more blocks call them:")
for n in sorted(nodes):
    if len(absorbed[n]) == 1 and len(preds.get(n, ())) >= 2:
        print(f"  {n:22s} called by {len(preds[n])}: {' '.join(sorted(preds[n]))}")
