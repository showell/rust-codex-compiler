# rust-codex-compiler

A native Rust front end for Codex: `.codex` in, standard Codex IR out. Layered
the way Cobblestone is -- lexer, parser, desugarer, scope, check, lower -- and
stopping at the IR. **The primary goal is compile speed.** Linting and
bug-hunting come later, on the same front end.

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

    ./safari/run.sh     safari's own checks through our interpreter
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

## Read before you are surprised

- **`docs/known-gaps.md`** -- what is not covered, and what is stale.
- **`docs/gates.md`** -- what each gate proves, and what it does not.
- **`safari/README.md`** -- the fourth arm, and why one unit must disagree.
- **`docs/charcode.md`** -- `char-code` is not ASCII, and two pieces of
  Cobblestone read as bugs until you know that.
