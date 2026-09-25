#!/usr/bin/env python3
"""Cut the corpus the gates read: every program under the checkout's
`codex/test/` except `apps/`, resolved into a self-contained unit by this
repository's own `bundle one`.

    CODEX_ROOT=<checkout> tools/cut_units.py       writes ~/units-<rev12>

Then point `~/units-current` at it (`ln -sfn`), which is what
`corpus_check_gate.sh`, `linear_gate.sh` and `tools/conflict_census.sh` read.
`codexrun sweep <units> <checkout>/codex/test` reads it too.

**THIS REPLACES THE LADDER'S `resolve_corpus.py`**, which cut the corpus with
the ladder's own cite resolver. The ladder is retired, and its resolver read
the quire table out of `build/quire-map.ps1`, which Update 62 turned into a
shim; this one is the resolver the port already uses, checked against
upstream's by `tools/resolver_agree.py`.

Stems must be unique across the tree, because every gate keys a unit by bare
name. A PROVENANCE beside the units names the checkout and revision, because a
directory name is not a pin (`gate_provenance.sh` prints it). A program the
bundler refuses is listed, not skipped silently: at U62 that is the two
`errors/` programs that exist to fail resolution, and two that cite the
compiler's own `Codex` quire, which upstream registers as a MANIFEST
(`$QuireManifests`) and this bundler does not read.
"""
import collections
import os
import pathlib
import subprocess
import sys
import time

CODEX = pathlib.Path(os.environ.get('CODEX_ROOT', '')).expanduser()
if not (CODEX / 'codex' / 'test').is_dir():
    sys.exit('set CODEX_ROOT to a Cobblestone checkout')
TARGET = pathlib.Path(os.environ.get('CARGO_TARGET_DIR', pathlib.Path.home() / 'build/rust-target'))
BUNDLE = TARGET / 'release' / 'bundle'
if not os.access(BUNDLE, os.X_OK):
    sys.exit(f'no bundle at {BUNDLE}; cargo build --release')

tests = CODEX / 'codex' / 'test'
rev = subprocess.run(['git', '-C', str(CODEX), 'log', '-1', '--format=%H %s'],
                     capture_output=True, text=True).stdout.strip()
out = pathlib.Path.home() / f'units-{rev[:12]}'
out.mkdir(exist_ok=True)

names = [n for n in sorted(tests.rglob('*.codex'))
         if 'apps' not in n.relative_to(tests).parts[:-1]]
dupes = [s for s, c in collections.Counter(n.stem for n in names).items() if c > 1]
if dupes:
    sys.exit(f'stems must be unique, every gate keys a unit by bare name: {dupes[:10]}')

t0, refused = time.time(), []
for n in names:
    r = subprocess.run([str(BUNDLE), 'one', str(n), str(out / f'{n.stem}.codex')],
                       capture_output=True, text=True)
    if r.returncode != 0:
        refused.append((n.relative_to(tests), (r.stderr.strip().splitlines() or ['?'])[-1][:120]))

(out / 'PROVENANCE').write_text(
    f'checkout   {CODEX}\n'
    f'revision   {rev}\n'
    f'resolver   rust-codex-compiler bundle one ({BUNDLE})\n'
    f'population codex/test/**/*.codex except apps/: {len(names)} programs, '
    f'{len(names) - len(refused)} units, {len(refused)} refused by the bundler\n'
    f'cut        {time.strftime("%Y-%m-%d %H:%M:%S")} in {time.time() - t0:.0f}s\n')
print(f'{out}: {len(names)} programs, {len(names) - len(refused)} units, {len(refused)} refused')
for p, why in refused:
    print(f'  REFUSED {p} -- {why}')
