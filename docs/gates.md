# What each gate proves, and what it cannot

A gate that is green tells you something narrow. This file is the narrowness,
one section per gate, because that is the part a reader needs and the command
line is not.

## Losslessness -- `lexdump lossless <path>...`

Every byte of the source is covered by exactly one token or one piece of
trivia, so `concat(tokens) == source`. **Needs no oracle**: the file answers
it. Runs over every `.codex` in the checkout, thousands of them, no compute.

**Cannot see:** whether any token has the right KIND. A lexer that called
everything `Word` passes.

## Token agreement -- `lexdump truth <file>`

The ladder's `lex.truth` is a bare-metal dump of Cobblestone's own lexer over
`Syntax/Lexer.codex`: kind, offset+length, line, column, text. Our stream
projected free of trivia must equal it.

**Cannot see:** the other half of the language. One subject, 41 of the 92
token kinds. It starts a lexer; it cannot finish one. The corpus finishes it.

## Declaration agreement -- `parsedump truth <file>`

`parse.truth` records the DECLARATION layer only: each definition's name,
parameter count, annotation count, position and chapter, plus the chapter's
sections, type definitions and counts.

**Cannot see:** expression structure, at all. It says nothing whatever about
it.

## Coverage and homelessness -- `parsedump cover <dir>`

Coverage alone was measured to be too weak: a parser deliberately broken to
stop consuming definition bodies still passed it, because the orphaned tokens
reappeared as loose lines and were still counted exactly once. So the gate also
requires that almost no token sit outside a named construct -- 367 loose tokens
across the compiler's 64 chapters when healthy, 357,339 when broken.

**Cannot see:** whether the shape is RIGHT. It proves the grammar is TOTAL.
Giving `+` and `*` the same precedence leaves it entirely green. Shape is
guarded by unit tests today and by the IR golds later.

**One number here IS a gate** and must stay zero: `token(s) in pattern position
not understood`. Upstream's pattern parser never fails -- it folds anything it
does not recognise into the same wildcard the author could have written -- so
keeping ours able to say "I did not understand this" is what makes the
difference countable. It is reported beside the total pattern count, because a
zero from a parser that never ran looks exactly like a zero from one that works.

**Three of the rows `cover` prints are the gate; the rest are inventory.** The
gate rows are unread bodies, loose tokens above the threshold, and
unrecognised pattern tokens -- those fail the run. Everything beside them --
unread type-definition bodies, blocks that ran to the end of the file, bodies
not yet structured -- is the SIZE OF THE WORK LEFT, and a gate that is red for
a month is a gate nobody reads. `unread type definition bodies == 0` was in
the test for one commit while the number was nine, and the run was red the
whole time without anybody noticing.

`cover` also reports what the parse ALONE cost, separately from the sweep's
own. Compile speed is this project's first goal -- the front end reads the
checkout at roughly 42 MB/s against `native/codexir`'s ~150 KB/s, and that
ratio is the whole reason the goal is stated -- so reporting the two together
would hide a regression inside the gate's cost.

`cover` has a SECOND half, which the name does not suggest: it also runs the
scope pass over every file and reports unresolved names, splitting out those
in programs the compiler itself refuses -- the same refused/not partition the
parse errors get, and for the same reason.

**`codex/test/errors/` holds programs the compiler is SUPPOSED to decline**, so
a diagnostic raised there is output rather than a defect. The two counts are
reported on separate lines; added together they give a total that goes UP as
the front end improves. The gold bank's `refused.tsv` is the authority and the
directory test is a heuristic.

## Desugar -- `desugardump truth` and `cover`

`desugar.truth` **would pass a desugarer that answered `Error` for every
expression**, because it inspects the declaration layer alone.

So `cover` is the baseline-free half: it desugars every definition in every
file and counts the AST nodes that came out against the ones that are the error
node -- which carries the NAME of the CST kind it could not translate.

## IR preamble -- `irdump grade <units-dir>`

Everything above `(defs` in an IR file is fixed by syntax alone, and it is
present in EVERY gold, which is what makes it gradeable across the whole
corpus at once: chapter,
title, prose, pblocks, anns, sections, ctors, eff-ops, grounds, type-defs.
Everything BELOW it carries an inferred type on every node, so reaching that
needs scope, check and lower.

**Cannot see:** any expression body. The preamble is a slice -- 7.7% of the
corpus IR by bytes, 0.5% of safari's, and type definitions are three quarters
of it.

The input must be a RESOLVED unit; the ladder's `resolve_corpus.py` writes
them, and safari's `build/*-unit.codex` already are. A gold names sections from
`Foreword ListUtils` and constructors from `Foreword Tuple` that appear nowhere
in the program's own file.

`(chapter "...")` is a DRIVER PARAMETER -- `compile-frontend source "Program"
flags` -- so `grade` reads that one field from the gold and COUNTS how often it
had to. Never having to is what says our derived rule matches `native/codexir`.

## Definition agreement over the whole corpus -- `irdump defs <units-dir>`

For all 1,012 golds, every definition the gold names must be present in our
desugared chapter, by NAME and by ARITY -- reported as "no such definition" and
"parameter count" separately, because they fail for different reasons.

This is the widest gate here: whole-corpus, and it reaches the definition layer
rather than stopping at the preamble.

**Cannot see:** any expression body, still. A definition can have the right name
and the right parameter count and the wrong meaning.

## Scope -- `desugardump scope <file>`

`desugar.truth` plus a `--- scope ---` section, against
`$CODEX_GOLDS/rungs/scope.truth`.

**Cannot see:** the same thing every truth here cannot -- it is the declaration
layer with names resolved, not expressions.

## The interpreter -- `codexrun`, `safari/run.sh`

`codexrun` compiles the desugared AST to a run form -- names resolved to frame
slots, literals already values -- and walks that. No types, no IR, no zig, no
guest, which is the point: **it shares nothing with the other arms below the text**, so when it
disagrees the disagreement is attributable. It is also the first oracle here
that sees MEANING rather than shape -- five byte-comparison oracles are one
oracle, and `and` failed to short-circuit under all of them.

**Cannot see:** anything about the IR, or types. It is an interpreter.

The fourth arm built on it -- what it proves, why it needs no gold, and the one
unit that must DISAGREE -- is `safari/README.md`.

## Resolver agreement: ours against upstream's compile step

    tools/resolver_agree.py <checkout>

For every program under `<checkout>/codex/test` except `apps/`, the chapter
headers of `bundle one`'s unit against the unit `build/compile.ps1` builds:
`Resolve-CiteOrder` and `Format-CiteChapters`, run by `tools/r2_headers.ps1` in
one pwsh process from the checkout's own `quire-map.ps1`. Headers carry the
quire (`Foreword--Maybe`) and the order, so equal header lists mean the same
chapters, from the same quires, in the same order.

**What it cannot see.** Bytes: upstream separates chapters with two blank lines
and this compiler with one, so it compares headers and not text. And any
mistake both resolvers make, which is the shape of every differential. The two
share no code, but both take the registry as truth, so a quire mapped to the
wrong directory reads the same to both.

**Upstream is the reference, not the answer.** Upstream's build script and its
compiler answer "is this chapter already here" differently. `Resolve-CiteOrder`
fetches a Foreword chapter again when the unit carries it under another prefix;
the scoper's `find-slug-for-cite-name` takes the one chapter of that name. Ours
follows the compiler, so a program carrying such a chapter disagrees here by
design. Each disagreement is read, and named, before it is called a defect.

## The self-host -- `./selfhost_gate.sh`

The compiler compiling ITSELF: `codexcheck-subject.codex`, which is every
chapter in one unit, checked and lowered by us and by the oracles, compared on
five counters and then definition by definition on the wire.

**The cheapest gate that touches everything.** About a minute against the
corpus sweeps' twenty, because it is one unit rather than 1,246 -- and it moves
for the same reasons they do, so it is the one to run first after a repin.

**It compares, and it exits non-zero.** That is worth saying because it did not
always: this lived as an inline step in a checkpoint script that printed both
sides and never looked at them. The run where the counters first diverged still
reported PASS, since `grep` had found its lines and nothing else was asked.

**Three outcomes per definition, not two.** A definition the oracle emits and
we do not is MISSING; one we both emit and disagree on DIFFERS. They want
opposite responses -- port it, or fix it -- and folding them together reports
the arrival of new upstream code as if it were a regression in ours. The split
paid for itself on its first run: of 155, exactly one was MISSING, and it was
`__eq_TokenKind`, the synthesised equality `gen-eq-def` mints.

**WHAT IT CANNOT SEE, and this is the one to hold on to: the subject and the
oracle move TOGETHER.** The corpus gates hold `units-u56` fixed and repin only
the oracle, so a change in their numbers is the oracle's. Here the subject IS
the compiler, so repinning changes what is being compiled and what is grading
it in the same step. A number that moves cannot be attributed to either without
a second measurement at the old pin, and there is no cheap one -- the old
oracle is a build away.

So read a move here as "the window between these two pins did something", never
as "this Update did something". `generated/PROVENANCE.oracles` names the pin;
the gate prints it.
