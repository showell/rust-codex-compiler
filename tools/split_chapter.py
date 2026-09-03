#!/usr/bin/env python3
"""Move whole definitions -- with the prose that explains them -- between chapters.

Edit PLAN: a map of new chapter name -> the definitions it takes, in the order
they should appear. It refuses to write anything unless every definition in the
source is assigned to exactly one chapter and every assigned name exists, so a
typo cannot silently drop code.

Sections are NOT inherited. Give each new chapter its own -- Render's section
names described where its code sat, and carrying them over gave a 13-definition
chapter eight sections. Written for the Render split, 2026-09-03; the intended
next subject is ZigEmitter.
"""
import re, pathlib, collections

S = pathlib.Path('/home/steve/showell_repos/safari-codex/port')
src = (S/'Render.codex').read_text()

head, body = src.split('\n We say:\n', 1)

# chunk on blank lines; a chunk is prose (1 space), code (2 spaces) or a Section
chunks = body.split('\n\n')
DEF = re.compile(r'^  ([A-Za-z][A-Za-z0-9-]*)\s*(?::|=)')
units, pending = [], []
for c in chunks:
    if not c.strip():
        continue
    if c.lstrip('\n').startswith('Section:'):
        pending = []                      # section headers are re-made per chapter
        continue
    m = DEF.match(c.lstrip('\n'))
    if m:
        units.append((m.group(1), '\n\n'.join(pending + [c.strip('\n')])))
        pending = []
    else:
        pending.append(c.strip('\n'))

PLAN = {
 'SceneLimits': ['detail-dist','crown-shade-dist','min-scenery-px'],
 'TowerPlan':   ['max-vis-towers','tower-beyond','tower-right','seg-tower-left','tower-yaw',
                 'TowerItem','tower-if-ahead','seg-towers','seg-mid-tower','walk-towers',
                 'behind-tower','all-towers','tower-items'],
 'TreePlan':    ['max-vis-trees','TreeItem','place-tree','seg-trees','walk-trees','tree-items'],
 'CatPlan':     ['max-vis-cats','chain-gap','CatItem','cat-item','seg-cat','walk-cats','cat-items'],
 'CritterPlan': ['farm-seg-reach','safari-seg-reach','max-vis-critters','place-critter',
                 'place-critter-via','place-duck','place-all','place-all-via','place-ducks',
                 'seg-farm','seg-safari','seg-ducks','seg-billboards','walk-billboards',
                 'behind-billboards','behind-ducks','all-placed','cow-items'],
 'RailPlan':    ['leg-steps','leg-points','push-leg','rail-run-up','rail-run-out',
                 'joint-rail-path','joint-rails','walk-rails','behind-rails','all-rails','rail-items'],
 'TruckPlan':   ['TruckAt','no-truck','truck-step','truck-here','truck-at','truck-items'],
 'DepthSort':   ['Kind','Item','rest-from','merge-items','sort-tie','deeper-than','sort-items'],
 'Render':      ['seg-cull-count','walk-seg-cull','Collected','prev-index','collect'],
}
home = {n: ch for ch, ns in PLAN.items() for n in ns}
have = {n for n, _ in units}
missing = [n for n in home if n not in have]
extra   = sorted(have - set(home))
print('defs parsed:', len(units))
if missing: print('  ASSIGNED BUT NOT FOUND:', missing)
if extra:   print('  FOUND BUT UNASSIGNED  :', extra)
if missing or extra: raise SystemExit('refusing to write a partial split')

by = collections.defaultdict(list)
for n, text in units:
    by[home[n]].append((n, text))
for ch, ns in PLAN.items():
    order = {n: i for i, n in enumerate(ns)}
    by[ch].sort(key=lambda nt: order[nt[0]])
import json
pathlib.Path('/tmp/render_units.json').write_text(json.dumps({k: v for k, v in by.items()}))
print('grouped:', {k: len(v) for k, v in by.items()})
