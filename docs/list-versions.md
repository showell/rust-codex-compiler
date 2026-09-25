# List versions: Codex's in-place list writes in Roc

**Status, 2026-09-25 (U62): the default in rocemit.** `src/list_versions.rs`
runs on every emission, pruned and `--whole`. It replaced the refusal "`f`
writes its list parameter `p` and answers something else", which was the
ladder's largest at U62 (35 units).

## The problem

`list-set-at xs i v` changes `xs` in place in Codex (Builtins.codex: alloc
`none`). Every later read of `xs` sees the write, whether it happens in the
same definition, in a caller that passed `xs`, or through another name bound
to it. A Roc list is a value, so the emitted `List.set` answers a new list
and the old name still holds the old one. Three shapes show up in the corpus:

- **Scratch writes** (`lz77-count-distinct`, `sort-run`). The new list is
  passed along explicitly and nothing reads the old name afterwards. Value
  semantics are already right.
- **Writes the function itself relies on** (`ne2k-copy-into`). It discards
  the result of `list-set-at dst ...`, recurses on `dst`, and expects the
  write to be there.
- **Writes the caller relies on** (`fe-carry` reads `o` after
  `fe-carry-pass o 0 0`; `cb-dbl-mod` reads `x` after `cb-shl1 x ...`).

## What the pass does

The module comment in `src/list_versions.rs` is the full description. In short:

- **Every write is a new version.** Later reads of the list, under any name
  bound to it, read the version.
- **A function that writes a list parameter hands the last version back.**
  If it answers the list, it's a *list writer* and its answer is the version.
  Otherwise it's a *tuple writer* answering `(answer, list, ...)`, and the
  caller continues with the version it got back.
- **Which functions write is a least fixed point.** A call to a writer writes.
- **Which writers answer their list is a greatest fixed point.** Assume
  every candidate does, then drop the ones a leaf disproves. The least fixed
  point settled self-recursive list writers such as `brotli-histo` as tuples,
  and the answer-is-the-list aliasing was then lost. That was a correctness
  bug, not just the wrong shape.
- **Branches that leave a list at different versions return them**, as a
  tuple joined after the branch. In tail position the definition's own
  tuple is built in each arm, so a self-call stays a tail call.
- **A list passed by bare name is a reference.** It is the version after all
  the call's arguments have been evaluated (`references_last`).
- **`alias_root` says which list an expression IS.** That covers a name, a
  `list-set-at` on it, a call to a list writer, a `let` by its body, or an
  `if`/`when` whose every arm is the same list.
- **Refused, as a whole unit or as a `--whole` stub:**
  - a write to a list held in a record field (shared heap);
  - a lambda writing a list it captured;
  - a writer used as a value;
  - a write in one `act` statement that a later statement reads;
  - writes under `handle`, `with-timeout` or `try`.

The tuple is carried in the IR under reserved names, `__copyout` (type and
constructor) and `__copyout-at-K` (element K). `roc_emit` spells them as
`(a, b)` and `t.K`. Set `LV_TRACE=1` to print which definitions are writers,
and of which kind.

## Where it stands

    roc-apps ladder: 846 -> 872 PASS (863 PASS + 9 new SLOW, all compile-time
    evaluation, added to tests/slow.txt); no PASS lost.
    e1000-rx-reuse is DIVERGES (a __heap-save measurement).

Three things the first full run taught, all now in the pass:

- **A list stored by name is the list.** `brdix-build` stores four empty
  tables in a record and fills them in its last field. The fields must be
  the filled versions (`store`, like `references_last` for arguments). A
  write after the store is refused, since no renaming can reach the copy
  stored. This was both Brotli failures.
- **A write through a record field is refused only when its answer is
  dropped.** Refusing every field write lost 31 passing units (`fb-set` and
  others rebuild the record with the answer, which means the same in Roc).
  Only `let dummy = list-set-at (node.f) ...` with `dummy` unused, or the
  write run as a statement, relies on the record changing under it.
- **Only a LOCAL list is written in place.** A top-level constant is copied
  on write (codex/test's const-share pins `list-set-at w-direct 0 99`
  leaving `w-direct` as it was), so it is never a root.

And one for `--whole`: version names are numbered per definition against
its own and its chapter's names (`taken`), not the unit's symbol table.
Otherwise a chapter's text depended on which other chapters the unit cited.

## What is still refused

The eight remaining "record field" units at U62 (ranked-text-set x2,
network-effect, web-mux-* x5) are refused for dropping a field write's
answer (`rts-extend-path-loop`, `arp-cache-add` in their shapes) or for a
write in one `act` statement that a later one reads. Both mean shared heap
in Codex. Doing better needs a model of which records share a list, which
is a different piece of work.
