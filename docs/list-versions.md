# List versions: Codex's in-place list writes in Roc (WORK IN PROGRESS)

**Status, 2026-09-25 (U62):** `src/list_versions.rs` exists and works for
most of what it targets, but is **off by default**. It runs only under
`rocemit --list-versions`. Without the flag rocemit behaves exactly as it
did: a definition that writes a list parameter and answers something else
is refused, "`f` writes its list parameter `p` and answers something else".
That refusal was the ladder's largest, 35 units at U62.

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

## Where it stands (the 35 units refused at U62)

    rocemit --list-versions, via ROCEMIT=<a build that passes it>:
      24 PASS
       8 REFUSED  write to a list held in a record field (ranked-text-set x2,
                  network-effect, web-mux-* x5): correct refusals
       2 FAIL     lib@brotli-test (brotli-fit-exact, brotli-xform-smaller: the
                  output round-trips but is larger than it should be),
                  e1000-rx-reuse ("list heap grew": a heap measurement; probably
                  belongs on the DIVERGES list with the other __heap-save ones)
       1 CRASH    lib@brotli-dict-test, "list-at out of range"

The ladder script has no flag for it. To try it, point `ROCEMIT` at a small
wrapper that adds `--list-versions`, or temporarily make it the default.

## To finish it, in order

1. **Brotli.** Both Brotli failures are almost certainly one remaining
   aliasing shape the pass doesn't see. Use `LV_TRACE=1` on
   `codex/test/lib/brotli-test.codex` and read the emitted Roc for the
   length-limiting code (`brotli-fit`, `-clamp`, `-repair*`) and the transform
   search. Suspects:
   - a list that reaches a writer through something `alias_root` doesn't
     cover (a tuple writer's answer that IS a list, a list inside a list);
   - a top-level constant list passed to a writer. Codex would mutate the
     shared constant; the pass versions it only inside the one caller.
2. **e1000-rx-reuse.** Decide whether it is DIVERGES (a heap measurement) and
   say so in roc-apps `tests/ladder.sh`.
3. **Speed.** Some newly passing units are slow in Roc: ecdsa-sha384 ~49 s,
   tls-cv-schemes ~37 s, ecdsa-p384 ~35 s. The likely cause is copy-out
   keeping an old reference alive, so `List.set` copies instead of writing in
   place (O(n) per write). Check with a smaller case first; the fix is
   probably making sure the old version is dead at the write.
4. **Make it the default.** Remove the flag and the old `written_param`
   refusal in `roc_emit.rs`. Then run the full roc-apps ladder, diff the
   ledger against the committed one (no PASS may be lost; the new
   record-field refusal is the thing to watch), and regenerate
   `tests/ported` with `tests/package.py`.
