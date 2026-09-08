# `char-code` is not ASCII

Codex's `char-code` is a private frequency-ordered alphabet:

    1        newline
    2        space
    3..12    the digits
    13..38   lowercase, in the order etaoinshrdlcumwfgypbvkjxqz
    39..64   uppercase, at lowercase + 26
    65..96   punctuation

So `char-code 'A'` is 41, not 65 -- and it is **constant-folded into the IR**,
so a front end that folds it to 65 differs from the golds on every program
containing a character literal.

`src/charcode.rs` carries the table. The ladder's `charcode_probe.py` derives
it from `native/codexir` in about 0.05 s and checks it STRUCTURALLY; `--rust`
emits the table this repo commits by hand. **Do not hand-edit it.**

The diff a wrong table produces lands far from its cause: every program with a
character literal differs, and none of them mentions `char-code`.

## Two pieces of Cobblestone that read as bugs and are correct

- `Lexer.codex` classifies uppercase with
  `c >= char-code 'E' & c <= char-code 'Z'`. That is a RANGE TEST: 'E' is the
  lowest-coded uppercase letter and 'Z' the highest, because the ordering is by
  frequency and not alphabetical.
- `ChapterScoper.codex` lowercases with `c - 26`, which is exact because
  uppercase is defined as lowercase + 26.

A host `is_alphabetic` agrees with these on ASCII by coincidence, not by
construction.
