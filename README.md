# rust-codex-compiler

A native Rust front end for Codex: `.codex` in, standard Codex IR out. Layered
the way Cobblestone is -- lexer, parser, desugarer, scope, check, lower -- and
stopping at the IR. **The primary goal is compile speed.** Linting and
bug-hunting come later, on the same front end.

**It also transpiles Codex to Roc** (`rocemit`), down the same road as far as
the lowering and then writing Roc instead of IR text. That is what puts Codex
programs on Roc platforms; see "Emitting Roc" below.

There is also an interpreter (`codexrun`), which is not on that path. It
compiles the desugared AST to a run form -- names already resolved to frame
slots, literals already values -- and walks that. It exists to be an oracle
that sees MEANING rather than shape: see "Running a program" below, and
`docs/gates.md` for what it cannot see.

## Four rules this repo is built under

1. **Canonical equality is the gate; byte-identity is a ratchet.** The IR text
   publishes unification-variable numbers, which are a function of allocation
   ORDER, so demanding byte-identity would demand reproducing Cobblestone's
   walk -- and would foreclose ever improving on it. Compare with ids renumbered in first-appearance order; count
   byte-identical programs separately and ratchet that up, never down.
2. **Lossless CST from day one.** Trivia -- spaces, skipped prose, exact spans
   -- is kept and the AST is lowered from it. The one place we deliberately do
   not copy Cobblestone, which throws trivia away: retrofitting a CST later is
   a rewrite, and the linting goal wants one.

   **This is CARRYING EARNED KNOWLEDGE FORWARD, and it is the rule the others
   serve.** The lexer earned the exact bytes; the parser earned the structure.
   A layer that discards either forces a later one to re-derive it from less,
   and re-derivation from less is where the defects live. Every layering bug
   found in this repo so far has that shape -- a fact known upstream, dropped,
   and then reconstructed badly downstream: the `punctual` flag read three
   times and used none, `unit family` members parsed and thrown away, an
   `InstanceDef` whose methods the parser read and the desugarer discarded, a
   `for` comprehension recovering its loop variable by comparing a token's TEXT
   to `"for"` when the lexer had already declared a keyword for it.

   The asset is still underused. We can answer any question of the form "where
   in the source did this come from" and Cobblestone structurally cannot.
   Nothing in the release protocol exploits that yet, and something should.
3. **Golds come from `master-plus-outbound`**, not plain master -- two of our
   PRs move front-end output, and golds cut against unpatched master would
   encode bugs we reported. Reach them through `$CODEX_GOLDS`.
4. **Clean by construction.** No generated code in the repo, no `target/`, no
   vendored golds, no benchmark output. `CARGO_TARGET_DIR` goes to
   `~/build/rust-target` -- **a build cache, and deliberately NOT a sandbox.**
   A sandbox under `~/runs` is a measurement of ONE commit and is deleted when
   the work is done; a cargo cache spans commits by design, which is the whole
   point of it. Putting one in `~/runs` makes a directory that looks like a
   measurement, is not, and survives every cleanup.

## Using this compiler to verify an Update

**[Verifying an Update with a second front
end](http://143.244.172.148:9100/notes/verifying-an-update-with-a-second-front-end.md)**,
drafted **2026-09-08**, before this repo had met its first Update.

Why a second implementation is a release instrument at all (a regression suite
cannot tell you whether a change was *intended*; we can, because we were never
told what the Update was trying to do), the protocol -- bank a baseline, repin
and change nothing else, attribute every delta before closing any of it -- and
the four instruments with what each is blind to.

**Read the date.** The general argument is meant to last. The second half is a
watch-list for Update 56 specifically, and it is expected to go stale the day
that Update lands; the enduring principles will be lifted into their own
document then.

## Building

    export CARGO_TARGET_DIR=~/build/rust-target
    cargo build --release
    cargo test                    # needs no checkout and no bank

The gold-backed gates need two things pointed at other checkouts:

    export CODEX_ROOT=~/showell_repos/NewRepository      # the Codex checkout
    export CODEX_GOLDS=~/golds/<bank>                    # the bank; never guessed at

A bank holds `rungs/` (the per-stage truths) and `ir/` (the IR golds). The
corpus gates want RESOLVED units, which the ladder's `resolve_corpus.py`
writes; safari's `build/*-unit.codex` already are.

## The tools

| binary | stage | reads |
|---|---|---|
| `lexdump` | lexer | a file, or a directory to sweep |
| `parsedump` | parser | ditto |
| `desugardump` | desugarer | ditto |
| `irdump` | IR preamble | a RESOLVED unit |
| `codexrun` | interpreter (not on the path above) | a resolved unit |
| `rocemit` | Roc, from the lowering | a resolved unit, and a directory to write |

    ./safari/bench.sh   time the interpreter on a fixed set of safari units

Everything that depends on the safari-codex checkout lives under `safari/` and
has its own README there. Nothing is vendored; `SAFARI_ROOT` points elsewhere.

## Running a program

    codexrun <unit.codex>                        print what it prints
    codexrun --check <unit.codex> <expected>     diff against a `.expected`
    codexrun sweep <units-dir> <codex-test-dir>  every program that has one
    codexrun bench <unit.codex>...               steps, seconds, steps per second

The input is always a RESOLVED unit: one self-contained file carrying every
chapter it cites. The ladder's `resolve_corpus.py` writes them for the corpus;
safari's `build/*-unit.codex` already are.

**A sweep is ONE process and the programs run SERIALLY**, one at a time, in
sorted order. Each gets a thread that is spawned and joined before the next one
starts: the thread is there for its 512 MB STACK, not for concurrency.
Interpreting recursion with recursion makes a deep Codex program a deep Rust
one, the default 8 MB is not enough for the corpus, and a stack overflow aborts
the PROCESS -- so without the thread one program takes the whole sweep with it.
It bounds each program at 60M steps, since one runaway would otherwise own the
machine; a single run is unbounded. One line per program goes to stderr as it
finishes and the verdict to stdout, so an interrupted sweep still leaves
everything it learned.

What a program pays before its first step is the FRONT END -- read, lex, parse,
desugar, compile -- and a resolved unit carries its whole prelude, so that is
not free. `bench` times the RUN only; the gap between its total and the wall
clock is what the front end cost.

## Emitting Roc

    rocemit <unit.codex> <dir>             one module per chapter, holding what
                                           the opening reaches (upstream's
                                           prune), and the app, into <dir>
    rocemit --by-reach <unit.codex> <dir>
    rocemit --whole <unit.codex> <dir>     every definition of every chapter,
                                           unpruned (roc-apps tests/package.py)

Two lines on stdout: the app's file name, or `library` for a unit with no
opening, and a digest of everything written. A refusal exits 2.

**The same road as `irdump whole`** -- resolve, parse, desugar, check, lower --
and then `roc_emit` where the IR text would be. So a program that transpiles is
a program this front end already understood, and the emitter is judged by
whether the Roc it writes MEANS what the Codex meant, not by shape.

`--whole` is for sharing a chapter between programs, which needs its text to
be the same whichever program emitted it. A function rocemit cannot write
becomes `crash` with the reason, and crashes only if called; a constant it
cannot write is left out, because Roc evaluates top-level constants while it
compiles, so a `crash` there is a compile error even when nothing uses it.
Whatever uses one left out follows it, to a fixed point. Each stub and each
omission is printed on stderr.

`--by-reach` picks the threaded state from what the opening can actually reach
rather than from every definition in the unit's chapters. It is for a platform
whose host stops a read or write at an address it does not back -- roc-apps'
framebuffer -- where a program can reach a device through a memory address no
builtin names, and only the host can see it.

What the emitter has had to decide, and where those decisions are written down:
a Codex `Text` is a `List(U8)` of CCE units, with the `Text.roc` it writes
beside it (`docs/known-gaps.md`); a list built by pushing onto a recursive call
becomes an accumulator loop; a memory or port door that reads or writes is an
effect, as are the UEFI key reads; `bit-shr` is Roc's arithmetic shift and
`bit-shru` the zero-filling one; and a call to a forwarder that calls back is
written as the call it makes.

## After a new Update

The goal is that this compiler MEANS what Codex means. In order:

1. **Port the builtins.** An Update often adds or removes builtins, and a
   program calling one we do not know fails as an undefined name.
   `CODEX_ROOT=<checkout> ladder/builtins_probe.py --rust` and
   `--rust-check-types` print the two tables in `src/builtins.rs`; splice them
   over the committed ones (the two hand-kept constants between them stay) and
   read the diff. U62: `+pit-input-hz +pit-count +cpu-park -uefi-read-file`.
   `--rust-constants` prints the third table, `CONSTANT_BUILTINS`: the
   builtins x86 emits as constants, with their VALUES, which live in the x86
   emitter rather than in Builtins.codex. The interpreter and rocemit answer
   them from it. Any other new builtin needs a rule in `src/interp.rs` and a
   spelling in `src/roc_emit.rs`, by hand.
2. **Cut the corpus.** `CODEX_ROOT=<checkout> tools/cut_units.py`, then
   `ln -sfn ~/units-<rev> ~/units-current`.
3. **Meaning:** `codexrun sweep ~/units-current <checkout>/codex/test` --
   every upstream test with an `.expected`, run on our interpreter.
4. **Accept and refuse:** `./corpus_check_gate.sh` (nothing we refuse that
   the oracle compiles) and `./linear_gate.sh`, against `~/codexir/codexcheck`
   built at the same checkout.

The curated arms in `cobblestone-curated-tests` (`ir-zig`, `ir-rust`,
`run-interp`, `ir-interp`) grade types and IR on a smaller, chosen corpus.

## The gates

    lexdump lossless <path>...              concat(tokens) == source
    lexdump truth <file> | diff - $CODEX_GOLDS/rungs/lex.truth
    parsedump truth <file> | diff - parse.truth
    parsedump cover <dir>                   coverage AND homelessness
    desugardump truth <file>                against $CODEX_GOLDS/rungs/desugar.truth
    desugardump scope <file>                ditto, plus scope.truth
    desugardump cover <path>...             error nodes by CST kind, and unresolved names
    irdump preamble <unit.codex> [chapter]  print one
    irdump grade <units-dir>                against $CODEX_GOLDS/ir/*.ir
    irdump defs <units-dir>                 every gold definition present, by name and arity
    codexrun --check <unit.codex> <expected>
    codexrun sweep <units-dir> <codex-test-dir>
    cargo test                              65 unit tests; needs no checkout at all

**Every gate here has something it cannot see, and each one is worth knowing
before you trust a green run.** They are written down in `docs/gates.md`
rather than here, because the limits are longer than the commands.

The numbers these print are not copied into this file. A README that carries
counts is a README that is wrong a week later; run the tool.

## Work in progress (where U62 left off, 2026-09-25)

Processed in a claude.ai cloud session; the session log is `U62.log` in
codex-zig-ladder, whose README says how Updates are processed and how the
cloud container is set up.

- **`src/list_versions.rs`**: Codex's in-place list writes, made explicit
  for Roc; the default since U62. `docs/list-versions.md` says what it does,
  what it still refuses, and why.
- **The sweep at U62 is 843 of 1081.** Of the older differences only
  `variant-address` is left from that list: it expects a nullary constructor
  (`Empty`) to be allocated at each construction, where the interpreter
  builds it once. Changing that moves every heap measurement, so it waits.
  The rest of the gap is mostly device builtins the interpreter has no rule
  for (`port-out-32`, `block-read-sector`, ...) and programs that exceed the
  sweep's step limit.
- **roc-apps `tests/ported`** is emitted with `rocemit --whole` by
  `tests/package.py`; each unit's stubs and omissions are in
  `~/build/roc-apps/gen/whole/<unit>/notes.txt`.

## Read before you are surprised

- **`docs/known-gaps.md`** -- what is not covered, and what is stale.
- **`docs/gates.md`** -- what each gate proves, and what it does not.
- **`docs/charcode.md`** -- `char-code` is not ASCII, and two pieces of
  Cobblestone read as bugs until you know that.
