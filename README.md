# rust-codex-compiler

A native Rust front end for Codex: `.codex` in, standard Codex IR out. Layered
the way Cobblestone is -- lexer, parser, desugarer, scope, check, lower -- and
stopping at the IR. **The primary goal is compile speed.** Linting and
bug-hunting come later, on the same front end.

There is also an interpreter (`codexrun`), which is not on that path. It walks
the desugared AST and exists to be an oracle that sees MEANING rather than
shape -- see `docs/gates.md`.

## Four rules this repo is built under

1. **Canonical equality is the gate; byte-identity is a ratchet.** The IR text
   publishes unification-variable numbers, which are a function of allocation
   ORDER, so demanding byte-identity would demand reproducing Cobblestone's
   walk. Compare with ids renumbered in first-appearance order; count
   byte-identical programs separately and ratchet that up, never down.
2. **Lossless CST from day one.** Trivia is kept and the AST is lowered from
   it. The one place we deliberately do not copy Cobblestone, which throws
   trivia away: retrofitting a CST later is a rewrite, and the linting goal
   wants one.
3. **Golds come from `master-plus-outbound`**, not plain master -- two of our
   PRs move front-end output, and golds cut against unpatched master would
   encode bugs we reported. Reach them through `$CODEX_GOLDS`.
4. **Clean by construction.** No generated code in the repo, no `target/`, no
   vendored golds, no benchmark output. Point `CARGO_TARGET_DIR` at a sandbox.

## Building

    export CARGO_TARGET_DIR=~/runs/<sandbox>/rust-target
    cargo build --release

## The tools, one per stage

| binary | stage | reads |
|---|---|---|
| `lexdump` | lexer | a file, or a directory to sweep |
| `parsedump` | parser | ditto |
| `desugardump` | desugarer | ditto |
| `irdump` | IR preamble | a RESOLVED unit |
| `codexrun` | interpreter | a resolved unit |

    ./safari/run.sh     safari's own checks through our interpreter
    ./safari/bench.sh   time the interpreter on a fixed set of safari units

Everything that depends on the safari-codex checkout lives under `safari/` and
has its own README there. Nothing is vendored; `SAFARI_ROOT` points elsewhere.

## The gates

    lexdump --check-lossless <dir>          concat(tokens) == source
    lexdump --truth <file> | diff - lex.truth
    parsedump truth <file> | diff - parse.truth
    parsedump cover <dir>                   coverage AND homelessness
    desugardump truth <file>                against $CODEX_GOLDS/rungs/
    desugardump cover <path>...             error nodes, by CST kind
    irdump grade <units-dir>                against $CODEX_GOLDS/ir/*.ir
    codexrun sweep <units-dir> <codex-test-dir>

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
