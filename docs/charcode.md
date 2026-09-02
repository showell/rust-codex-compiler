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
it from the compiler and checks it structurally. **Do not hand-edit it.**

## Two pieces of Cobblestone that read as bugs and are correct

- `Lexer.codex` classifies uppercase with
  `c >= char-code 'E' & c <= char-code 'Z'`. That is a RANGE TEST: 'E' is the
  lowest-coded uppercase letter and 'Z' the highest, because the ordering is by
  frequency and not alphabetical.
- `ChapterScoper.codex` lowercases with `c - 26`, which is exact because
  uppercase is defined as lowercase + 26.

A host `is_alphabetic` agrees with these on ASCII by coincidence, not by
construction.
