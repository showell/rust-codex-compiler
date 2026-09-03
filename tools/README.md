# Prototypes, not yet Rust

`collapse.py` — collapse every single-caller definition into its caller, to a
fixed point. What survives is the SHARED SPINE: the definitions two or more
blocks need, which are exactly the ones that straddle any proposed cut.

    ./tools/collapse.py Render ~/showell_repos/safari-codex/port/Render.codex \
        ~/showell_repos/safari-codex/{port,judge,gold}

It reads `cohesion --graph` and `seams`, so it cannot drift from the front end's
own walk. **It answers what cohesion cannot.** cohesion put 89 of Render's 92
definitions in one component and called the chapter cohesive; the collapse showed
two programs -- `collect` (63) and `frame-ground` (20) -- joined by three shared
functions. GroundPlan came out of that and collapses to one node.

A node with exactly one predecessor is dominated by it, so absorbing changes no
reachability. This is the dominator-tree contraction that STOPS at join points
rather than assigning them a nearest dominator, which is the whole difference: the
join points are the answer.

Python and here rather than Rust and in `src/bin` because it has one subject so
far. Port it when it earns a second -- ZigEmitter is the intended one.

`split_chapter.py` — move whole definitions, with their prose, out of one
chapter into several. Edit its `PLAN` and it refuses to run unless every
definition is assigned exactly once, so nothing is dropped in a big cut. It did
the Render split: 92 definitions into nine chapters, `values` identical 18
differing 0 on the far side.

Neither of these parses Codex itself -- they read `cohesion --graph` and split on
blank lines. That is fine for a chapter whose definitions are separated by blank
lines and will not survive contact with ZigEmitter. Port both to the real parser
before pointing them at the compiler.
