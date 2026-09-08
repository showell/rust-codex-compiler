# Making an allocation-order divergence a lookup instead of an excavation

Everything below was built and run today. The working scripts are in
`/tmp/claude-1000/mint/` (`counters.sh`, `whodunit.sh`, `mintprofile.sh`,
`probes/gen.sh`, `probes/table.sh`, `idseq.sh`, `gapdiff.sh`). Nothing in the
repo was modified.

## 0. The constraint that shapes every answer

The oracle's whole interface is **four numbers and a program**:

```
$ codexcheck < unit.codex | tail -4
substitutions 1028   next-id 1028   next-row-id 2410   expr-types 1360
```

There is no log to get out of it and none can be added. So every instrument is
a *function of the program we feed it*. There are exactly three levers:

1. **Shrink the program** until the delta appears — attributes a delta to a place.
2. **Synthesise the program** one construct at a time — attributes a delta to a kind.
3. **Read the IR** it already emits — the only per-node evidence it gives away free.

The worked example in the brief spent an hour on lever 2 done by hand, badly
(grep-and-correlate), because lever 1 did not exist. Lever 1 is the missing
piece and it is forty lines of shell.

## 1. `mintprofile` — reconstruct the oracle's mint log at definition granularity. **Build this.**

**The oracle's log cannot be extracted, but it can be *differentiated*.** A
Codex chapter is a sequence of definitions and the counters only grow. Truncate
the chapter after definition *k*, run both sides, and the difference between
successive prefixes is the per-definition cost. Do that for every *k* and you
have, for both compilers, exactly the log you wanted:

```
$ ./mintprofile.sh ~/units-u56/dce-reach.codex        # 3.2 s, 26 definitions
#    DEFINITION                     OURS d(i,r,e)  ORACLE d(i,r,e)
...
24   class                          0,0,0          1,0,0            <== DIVERGES
25   instance                       0,0,0          16,13,9          <== DIVERGES
26   opening                        12,30,10       12,31,10         <== DIVERGES
```

That is steps 2 through 8 of the worked example, in one command, in three
seconds, and it names **every** diverging definition rather than the first.
`dce-reach` is a live divergence right now; nobody had localised it. The
answer: we synthesise nothing for `class` (upstream mints 1 id per member) and
nothing at all for `instance` (upstream checks the method body — 16 ids, 13
rows, 9 expr-types for one one-line method). It is `synth-family-members` all
over again — `synth-instance-defs` is named in `desugar.rs:615` and never
written.

**Why truncation is legitimate.** It does *not* require the per-definition cost
to be stable under truncation (it is not — cutting a forward reference turns a
known name into an unknown one, which mints differently). It requires only that
**both compilers see the same truncated program**. Localisation is therefore
exact; the *numbers* in a profile row are the cost in the truncated program,
not in the whole file, and should be read as a signal for where to write the
reproducer, not as a cost table. Say so in the header or someone will quote a
row as evidence.

**Cost to build:** it exists, 30 lines of bash. Productionising it — put it in
the repo next to `slice.sh`, teach it `Section:` and page boundaries, make the
"a side refused this prefix" rows fold explicitly instead of implicitly — is
about two hours.

**What it does not catch:** a divergence *within* one definition (see §4), and
a divergence that is a pure reordering with no count change (both sides mint
the same number, different order — the counters are blind, only the IR shows
it).

## 2. `whodunit` — the same thing, bisected, for files where the profile is too slow. **Build this too; it is the same 40 lines.**

`mintprofile` is O(N) oracle runs. For the big units that is too slow, and
bisection turns it into O(log N) because "has diverged" is monotone in the
prefix:

```
$ ./whodunit.sh ~/units-u56/builtin-alloc.codex        # 14.8 s
156 definitions   probes: 8
first divergence when definition #108 is included
  v4 : Integer -> Vector 4 Integer
  v4 (n) = vec-cons 4 (vec-cons 3 (vec-cons 2 (vec-singleton n)))
--- ours[747 747 1654 1138] oracle[750 750 1666 1138] ---
```

Sized vectors: three ids and twelve rows short, expr-types exact. `vec-sized`
in the corpus has the matching `(-13,-13,-32,0)` signature.

And on the hardest thing in the corpus — `desk-span`, **2.7 MB, 8,298
definitions, 14 s per oracle run** — 14 probes, about five minutes:

```
first divergence when definition #3226 is included
  fs-read-file : Text, Text -> [FileSystem.Read] Text
  fs-read-file (dir) (filename) = read-text (path-join dir filename)
--- ours[32372 32372 91199 39351] oracle[32372 32372 91201 39351] ---
```

That is the live "off by 32 rows with `next-id` exact" case, and it is now a
two-line reproducer: a nested application under a declared effect row mints two
rows we do not. Four `desk-*` units carry it sixteen times over; the five
`fs-*` units carry it 3–10 times each, which is why their deficits are
`-6, -8, -10, -12, -20` and not a shared constant.

**Do not build generic delta-debugging (ddmin).** It is the wrong shape here.
ddmin removes arbitrary chunks, which breaks Codex programs into
undefined-name errors most of the time, and it is O(n²) against an oracle that
costs 14 s on the units where you would want it. The prefix bisect exploits the
one structural fact ddmin cannot know — the checker walks definitions in file
order — and gets the same answer in 14 probes.

## 3. The construct cost table — mechanically derived, then asserted. **Build this; it is the only proposal that finds divergences before a unit fails.**

One file per construct, each the base program plus exactly that thing, and the
marginal cost on both sides. 20 probes, 2.8 s to run the whole table:

```
CONSTRUCT        ORACLE d(id,row,expr)  OURS d(id,row,expr)    VERDICT
apply1           1,3,1                  1,3,1                  ok
class1           4,1,0                  3,1,0                  MISMATCH
instance1        17,13,5                3,1,0                  MISMATCH
lambda1          2,3,2                  2,3,2                  ok
nosig            3,1,0                  3,1,0                  ok
record1          0,0,0                  0,0,0                  ok
record3          0,0,0                  0,0,0                  ok
record1_param    1,0,0                  1,0,0                  ok
rowpoly          5,5,1                  5,5,1                  ok
unitfam2         2,6,0                  2,6,0                  ok
unitfam3         3,9,0                  3,9,0                  ok
unittype         3,1,0                  3,1,0                  ok
variant2         0,0,0                  0,0,0                  ok
```

Two things to notice.

**`unitfam2 = 2,6,0` and `unitfam3 = 3,9,0` is step 7 of the worked example, as
a table row.** One id and three rows per family member, read off rather than
derived. Had the table existed, steps 3–6 — the hour — would have been "run
the table, read the MISMATCH."

**The table found `class` and `instance` cold**, before I had looked at
`dce-reach`, which is the property `mintprofile` does not have: it reports on
constructs no failing unit has yet forced you to look at.

**What keeps it honest** — and this is the whole design problem, because I hit
both failure modes while building it in twenty minutes:

- *A probe with wrong syntax reports `0,0,0` on both sides and passes.* My
  first `unit family` probe used a syntax the parser silently swallowed; the
  row said `ok` and it was measuring nothing. **A probe must be rejected unless
  at least one counter moves off the base on the oracle side.** A construct
  that genuinely costs nothing (`record3`, `variant2`, `deriving_eq`) must be
  listed as a deliberate zero, by name, so a broken probe cannot hide in the
  same shape.
- *A probe the oracle refuses must be a hole, not a missing row.* My `effect`
  probe was refused for three iterations (`CDX3001 ... conflicts with existing
  name`) and the table happily printed `REFUSED` next to our number. It must be
  loud, because a refused probe is a construct with no coverage.

**Shape it as a test, not a script.** Check in `probes/*.codex` plus a
`costs.tsv` holding the *oracle's* column, and a `cargo test` that asserts our
column equals it — no oracle in the loop, so it runs in CI at the speed of 20
`checkdump` calls. A `--refresh` mode re-derives `costs.tsv` from the oracle;
the diff it produces when the pin moves is a feature, and it is the only place
that will tell you a pin bump changed allocation order.

**Cost:** the generator and table are written (50 lines). Turning them into a
checked-in gate with the two honesty rules: half a day, most of it writing
correct probes for the constructs that are not yet covered — `handle`/`with`
clauses (10 diverging units), induction and proof forms (7), sized vectors,
`lazy`, `try`, `mutable`, `linear`.

**What it will not catch:** anything whose cost is not compositional — a
construct that costs differently depending on what surrounds it. The
`fs-read-file` case is exactly that shape (nested application *under a declared
effect row*), and a table of single constructs would have missed it. That is
why §1/§2 and §3 are complements, not alternatives.

## 4. The IR id-sequence differ — free, and the only thing that sees inside a definition

We already produce both IRs. The ids are spelled at nodes, in order, so the
ordered sequence of `(tvar N)` and `(row … N)` occurrences is a partial mint
log with no extra oracle run at all. Diff the **gaps** rather than the values:

```
$ ./gapdiff.sh f.ours.ir f.theirs.ir       # factorial
15,16c15,16
< 15 11        <- our gap between emitted id 15 and 16
> 15 10        <- the oracle's
```

Equal gaps everywhere means one constant offset established before the first
emitted id — the divergence is upstream of anything the wire shows, and §1 is
the tool. A gap that differs at occurrence *k* means the extra mints happened
between node *k−1* and node *k*, and the IR line names the node. Nothing else
proposed here can localise below a definition.

**Cost:** 10 lines, written. **Limit:** only works where both sides emit IR,
which excludes the 214 corpus units the oracle refuses and any chapter with no
`Program` root.

## 5. Named mint sites inside `check.rs` — cheap, complementary, not a localiser

There are **26 mint call sites in the whole compiler** (19 `.fresh()`, 7
`.fresh_row()`, all in `check.rs`). Giving `fresh` a `Site` enum argument and
keeping a `[u32; 26]` histogram is an afternoon, and it buys two things:

- **A regression instrument.** Diff the histogram before and after a change:
  "`app-result` went up by 507" says which rule moved, which is a question no
  counter can answer today.
- **The last mile after §1.** The bisect says *which definition*; the histogram
  snapshotted per definition says *which of our 26 rules fired there*. The
  oracle's behaviour at that definition is then one arithmetic fact — "it minted
  3 more ids and 12 more rows" — against 26 named candidates. That is a
  three-minute step instead of an hour.

**Be clear about what it is not.** The oracle has no histogram and cannot be
given one, so this is never a diff against the oracle. Proposals that read like
"instrument both sides and diff the traces" are not available in this problem,
and any design that assumes them is fiction.

## 6. A counter gate over the corpus — the cheapest thing here, and it does not exist

`corpus_check_gate.sh` compares only the error count and the first `CDX` code.
**Nothing in the repo compares the four graded counters across the corpus.** A
ten-line script (`counters.sh` + `xargs -P 6`) does it in seven minutes:

> **988 units agree, 44 diverge, 214 the oracle refuses** (the deliberate-error
> corpus).

Grouping the 44 by their delta signature is one `python3` block, and it turns a
list of failures into a list of *causes*:

| ours−oracle (subs,id,row,expr) | n | units |
|---|---|---|
| `0,0,-32,0` | 4 | `desk-hover`, `desk-parse`, `desk-root-guard`, `desk-span` |
| `-10,-10,-20,0` | 3 | `fork-reclaim`, `par-map`, `par-nested` |
| `+2,+2,0,+1` | 3 | `induction-assoc`, `induction-list`, `induction-parse` |
| `-2,-2,0,0` | 2 | `effect-handler-nested-same`, `nrf52840-drivers` |
| … | 32 | one each |

The clusters are the work items: type classes (6 units, `typeclass-*`,
`type-class-*`, `dce-reach`), effect handlers (10, `handler-*`, `effect-*`,
`fork-*`, `par-*`, `scope-handler-clause`), the shared filesystem chapter (9,
`desk-*`, `fs-*`, `foreword-file-system` — one root cause, `fs-read-file`),
induction and proof forms (7, and note **we over-mint** there, the other sign),
sized vectors (2). The full list is at
`/tmp/claude-1000/mint/diverging44.txt`.

**Cost:** it exists. Adding it to the repo as `counter_gate.sh` with a
checked-in expected-divergence list — so a *new* divergence is red and the
known 44 are inventory — is an hour, and it is the highest value per minute of
anything here.

## Ranking

1. **`counter_gate.sh`** — one hour, and the 44-unit inventory with delta
   grouping is already the work plan. Without it you do not know what is broken.
2. **`mintprofile` / `whodunit`** — two hours. This is the abstraction the
   brief is asking for. It collapses steps 2–8 of the worked example into one
   command, and it worked on the corpus's hardest unit.
3. **The construct cost table as a checked-in test** — half a day. The only
   proposal that finds a divergence before a unit fails, and the only one that
   survives a pin bump as a diff rather than a surprise. Needs the two honesty
   rules or it will quietly measure nothing.
4. **Named mint sites** — an afternoon. The last mile after (2), and a genuine
   regression instrument in its own right. Not a localiser.
5. **The IR gap differ** — ten lines, already written, free to run. Narrow, but
   it is the only thing that sees inside a definition.

Rejected: generic delta-debugging (§2), and anything premised on the oracle
having, or gaining, a trace (§5).

## The honest bottom line

**The minimal reproducer *is* the technique** — steps 7–9 of the worked example
took minutes and were never the problem. What was missing is a way to reach
step 7 in one move. The prefix bisect is that move, and it is available because
the checker walks definitions in file order and the counters only grow; those
two facts are what make an opaque four-number oracle behave like a log. The
cost table is the same insight applied ahead of time instead of after a
failure. Neither needs a line of Rust, and together they turn the hour into
about a minute.
