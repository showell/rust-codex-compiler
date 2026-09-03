# The Zig Emitter four-way split

`ZigEmitter.codex` is ~4,500 lines and one chapter. These plans cut it into four
pages of that same chapter. Re-run them against each new Update rather than
rebasing the previous cut: upstream edits the emitter, and a rebase resolves
conflicts inside the very text being moved.

    cd <codex-tree>
    for f in ZigPrelude ZigEmitterExpressions ZigEmitterApply; do
      python3 <tools>/extract_chapter.py codex/plugs/zig/ZigEmitter.codex \
          <here>/$f.header.txt <here>/$f.plan.txt codex/plugs/zig/$f.codex
    done
    python3 <tools>/paginate_chapter.py \
        codex/plugs/zig/ZigEmitter.codex codex/plugs/zig/ZigEmitterExpressions.codex \
        codex/plugs/zig/ZigEmitterApply.codex codex/plugs/zig/ZigPrelude.codex

Order matters: each extraction cuts its definitions OUT of ZigEmitter.codex, so
the three run against a shrinking source. Pagination comes last and needs all
four files, because `Page N of M` cannot be written before M is known.

`extract_chapter.py` refuses unless every planned name exists exactly once, so a
definition upstream renamed or removed stops the run instead of silently
dropping. **That refusal is the value of keeping these files.** When it fires,
read what upstream did to that definition and edit the plan -- do not delete the
line to make the tool quiet.

## Three edits the scripts need alongside the split

The chapter's pages are LISTED, never discovered:

- `codex/plugs/zig/build.ps1` -- all four in `-Chapters`, then `ZigPlug`.
- `codex/plugs/wasm/page-lenses.ps1` -- all four in the zig row's `chapters`.
- `build/check-zig-prelude-surface.ps1` -- reads ZigPrelude.codex for the
  fragment lists and ZigEmitter.codex for `zig-prelude-decls`, which stays put.

## What the plans do NOT carry

Four definitions nothing reads -- `emit-zig-apply-args`, `zig-param-ll-elem`,
`zig-param-ll-scan`, `zig-subst-arg-type` -- are deleted separately, before the
split, and upstream has not taken that deletion. Re-verify they are still dead
before deleting again; the first two are a dead PAIR, which is why neither reads
as an unused leaf.

Re-cut at Update 55 on 2026-09-03: 421 definitions in, 421 out, and U55's new
`zig-bin-op-plain` added to page 2 beside `zig-bin-op-symbol`.
