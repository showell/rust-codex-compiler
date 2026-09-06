#!/usr/bin/env python3
"""The compiler's BUILT-IN NAMES, read out of `Types/Builtins.codex`.

    ./builtins_probe.py            report the count and the first few
    ./builtins_probe.py --rust     emit the Rust table on stdout

`builtin-names` is `bs-name` of every entry in `builtins`, and the name
resolver needs the set: a call to `text-length` is not an undefined name, and
without the list every program in the corpus reports hundreds that are not
there.

WHY A PROBE AND NOT A TRANSCRIPTION. The list is 263 entries long and moves
with the compiler; typing it once would be a copy nobody could check. This
reads the source of truth, and re-running it after a pin change says whether
the committed copy still matches -- the same arrangement `charcode_probe.py`
has, and for the same reason.

The tables it emits are committed BY HAND. Nothing here runs at build time:
this is a probe you re-run after a pin change to see whether the committed copy
still matches, the same arrangement `charcode_probe.py` has.

It moved here from the ladder on 2026-09-06, when `src/builtins.rs` became
load-bearing for the native road. The ladder is retired and a generator its
consumer cannot run is a generator nobody re-runs.
"""

import argparse
import pathlib
import re
import sys

import os

CODEX = pathlib.Path(os.environ.get('CODEX_ROOT', ''))
if not CODEX.is_dir():
    raise SystemExit('set CODEX_ROOT to the checkout whose builtins you want')

SOURCE = CODEX / 'codex' / 'compiler' / 'Types' / 'Builtins.codex'
# `bs-name = "..."` inside a BuiltinSpec, and nothing else in the file is
# spelled that way.
ENTRY = re.compile(r'BuiltinSpec\s*\{\s*bs-name\s*=\s*"([^"]*)"')
# `bs-type = Just (...)` -- the declared type, from which the ARITY comes.
TYPED = re.compile(r'BuiltinSpec\s*\{\s*bs-name\s*=\s*"([^"]*)".*?bs-type\s*=\s*(Just|None)')


# `Name { value = "Device.Block" }` is the one record spelling in this file and
# it is always a wrapper around a text. Collapsing it before parsing is what
# lets a bracketed LIST of them stay one element: without this the tokeniser
# split `EffectfulTy [Name { value = "Device.Block" }] [] int-ty-default` into
# nine pieces, `_check_type` read element 3 as the word `value`, and every
# nullary effectful builtin -- `read-line`, `get-args`, `block-sector-count`,
# the whole `key-*` and `process-*` families -- was refused as unrenderable.
NAME_REC = re.compile(r'Name\s*\{\s*value\s*=\s*("[^"]*")\s*\}')

CLOSER = {'(': ')', '[': ']', '{': '}'}


def _sexp(text, i):
    """Parse one balanced bracketed form starting at i. Returns (form, next-i).

    All three brackets, because the file uses all three: `(...)` is a type
    application, `[...]` is a list (of effect names, of type arguments), and
    `{...}` is a record. A list keeps its own head marker so a caller can tell
    `[TextTy]` from `(TextTy)`, which are different things in this grammar.
    """
    out, tok = [], ''
    open_c = text[i]
    close_c = CLOSER[open_c]
    if open_c == '[':
        out.append('#list')
    i += 1
    while i < len(text):
        c = text[i]
        if c in CLOSER:
            if tok:
                out.append(tok)
                tok = ''
            sub, i = _sexp(text, i)
            out.append(sub)
            continue
        if c == close_c:
            if tok:
                out.append(tok)
            return out, i + 1
        # A comma separates list elements and carries no meaning of its own.
        if c.isspace() or c == ',':
            if tok:
                out.append(tok)
                tok = ''
            i += 1
            continue
        tok += c
        i += 1
    return out, i


# A wrapper that can HIDE AN ARROW has to be transparent or the arity comes out
# 0. Everything else is an ordinary type constructor and ends the spine.
#
# A head in NEITHER set is REFUSED rather than quietly counted as 0, because
# that silence is exactly what went wrong: `ForAllEff` was missing here, so
# `process-spawn :: ForAllEff 0 (FunTy ...)` was read as taking no arguments,
# and the interpreter built a one-argument function for a value. Nothing about
# an arity of 0 says whether it was read or defaulted.
TRANSPARENT = {'ForAllTy', 'ForAllEff', 'EffectfulTy'}
ENDS_THE_SPINE = {'TypeVar', 'ListTy', 'VectorTy', 'ConstructedTy', 'PropEqTy',
                  'VectorMaskTy', 'LinkedListTy', 'TypeApply', 'RecordTy',
                  # `deck-record T` is a record ON THE DECK -- a wrapper, but
                  # around a type and never around an arrow. `s-new :: ForAllTy 0
                  # (deck-record (ConstructedTy schan ...))` takes no arguments,
                  # and upstream's own emitter agrees: `emit-helper-call-0`.
                  'deck-record'}


def _arity(form, name):
    """How many arguments the FunTy spine takes.

    A builtin's arity is not written down anywhere; it is the shape of its
    type. A `FunTy` contributes one and recurses on its RESULT -- so a
    function-typed ARGUMENT (map-list's first) does not inflate the count.
    """
    if not isinstance(form, list) or not form:
        return 0
    head = form[0]
    if head == 'FunTy':
        return 1 + _arity(form[-1], name)
    if head in TRANSPARENT:
        return _arity(form[-1], name)
    if head in ENDS_THE_SPINE:
        return 0
    raise SystemExit(f'{SOURCE}: {name} has type head {head!r}, which this probe '
                     'does not know. Add it to TRANSPARENT if it can wrap an '
                     'arrow, or to ENDS_THE_SPINE if it cannot.')


def arities(text):
    """name -> arity, for every builtin that DECLARES a type.

    A name absent from the result declares `bs-type = None` and has no arity to
    read. **That is not the same as an arity of 0** and the two must not be
    collapsed: 23 entries declare a plain type -- `get-ticks :: Integer`,
    `uefi-read-key-ex :: Integer`, `__deck-enter :: Nothing`, `assume :: Proof`
    -- which is a NULLARY builtin, a value rather than a function. Only 8 of
    the 263 are genuinely undeclared: True, False, Nothing, open-file,
    close-file, read-all, now, random-integer.

    A bare type name is read here as well as a parenthesised one. Requiring a
    `(` sent all 23 of those down the undeclared path, where they picked up an
    arity of 0 by DEFAULT and looked identical to the ones that had earned it.

    Split per ENTRY rather than pairing a name with the next `bs-type` found: a
    name-then-type search reads straight past an undeclared entry into the
    following one's type -- which gave `__narrow` an arity of 0 and would have
    made every call to it wrong.
    """
    text = NAME_REC.sub(r'\1', text)
    out = {}
    for chunk in text.split('BuiltinSpec {')[1:]:
        m = re.match(r'\s*bs-name\s*=\s*"([^"]*)"', chunk)
        if not m:
            continue
        t = re.search(r'bs-type\s*=\s*Just\s*', chunk)
        if not t:
            continue
        if chunk[t.end():t.end() + 1] != '(':
            out[m.group(1)] = 0  # a bare type name: nullary, and DECLARED so.
            continue
        form, _ = _sexp(chunk, t.end())
        out[m.group(1)] = _arity(form, m.group(1))
    return out


# THE DECLARED TYPE AS A TYPE, not as its IR rendering.
#
# `ir_types` above answers what the IR PRINTS -- `(fn text int-default)` -- and
# that spelling cannot express a forall or a type variable. `show` is
# `ForAllTy 0 (FunTy (TypeVar 0) empty-row TextTy)`, so it is one of the 140
# builtins absent from that table, and the CHECKER is exactly what needs it:
# instantiating a forall mints a fresh type variable, and the count is graded.
#
# A compact s-expression rather than Rust constructor calls: it stays readable
# in a diff, and the parser that reads it back is forty lines and testable,
# where generated Rust is neither.
CHECK_ATOM = {
    'int-ty-default': 'int',
    'TextTy': 'text',
    'BooleanTy': 'bool',
    'CharTy': 'char',
    'NothingTy': 'nothing',
    'VoidTy': 'void',
    'ErrorTy': 'error',
    'ProofTy': 'proof',
    'real-f64': 'real',
    'real-f32': 'real-approx',
    # The two widths carry three modes each and the wire spells all six.
    'real-f64-trapping': 'real-trapping',
    'real-f64-saturating': 'real-saturating',
    'real-f32-trapping': 'real-approx-trapping',
    'real-f32-saturating': 'real-approx-saturating',
    'empty-row': 'empty',
}


def _elems(form):
    """The elements of a `[...]`, regrouped where a head lost its parentheses.

    `[TypeVar 0]` is ONE element and arrives as two tokens: the source writes
    the brackets and omits the parens, so a flat split reads `TypeVar` and `0`
    as two type arguments. Only the one-argument heads need this, and they are
    the only ones the file writes bare.
    """
    if not (isinstance(form, list) and form[:1] == ['#list']):
        return None
    out, it = [], iter(form[1:])
    for e in it:
        if e in ('TypeVar', 'ListTy', 'LinkedListTy'):
            out.append([e, next(it, '')])
        else:
            out.append(e)
    return out


def _bare(form):
    """`("Maybe")` is the name `Maybe`: a parenthesised `Name { ... }` record
    that the collapse above left as a one-element form."""
    if isinstance(form, list) and len(form) == 1 and isinstance(form[0], str):
        form = form[0]
    return form.strip('"') if isinstance(form, str) else None


def _check_type(form):
    """Render a parsed bs-type as the checker's s-expression, or None."""
    if isinstance(form, str):
        if form in CHECK_ATOM:
            return CHECK_ATOM[form]
        # `TypeVar 0` arrives split when it is bare; a lone name we do not know
        # is refused rather than invented.
        return None
    if not form:
        return None
    head = form[0]
    if head == 'FunTy' and len(form) >= 4:
        a, row, r = _check_type(form[1]), form[2], _check_type(form[3])
        if a is None or r is None:
            return None
        if row == 'empty-row':
            return f'(fn {a} empty {r})'
        if isinstance(row, list) and row and row[0] == 'concrete-row':
            lab = row[1].strip('"') if len(row) > 1 else ''
            # No inner quotes: this lands inside a Rust string literal, and a
            # label with a `"` in it would end the literal early. Labels are
            # dotted identifiers, so a bare word loses nothing.
            return f'(fn {a} (row {lab}) {r})'
        # A row VARIABLE, bound by an enclosing `ForAllEff`. It carries an id
        # and no labels, and instantiating the quantifier replaces the id --
        # so unlike an empty row it must NOT be minted a fresh one.
        if isinstance(row, list) and row and row[0] == 'row-var' and len(row) > 1:
            return f'(fn {a} (rowvar {row[1]}) {r})'
        return None
    if head == 'TypeVar' and len(form) >= 2:
        return f'(tvar {form[1]})'
    if head == 'ForAllTy' and len(form) >= 3:
        b = _check_type(form[2])
        return f'(forall {form[1]} {b})' if b else None
    if head == 'ForAllEff' and len(form) >= 3:
        b = _check_type(form[2])
        return f'(foralleff {form[1]} {b})' if b else None
    if head == 'ListTy' and len(form) >= 2:
        e = _check_type(form[1])
        return f'(list {e})' if e else None
    if head == 'EffectfulTy' and len(form) >= 4:
        # **THE EFFECT NAMES ARE DROPPED, AND THAT IS SAFE FOR EXACTLY ONE
        # REASON.** `infer-name` (TypeCheckerInference.codex:171) answers the
        # INNER type for an effectful name and hands the row to its caller, so
        # a builtin's effect names never reach the IR through a reference to
        # it; the `(effectful ...)` a wire carries comes from a DEFINITION's
        # own declared type, which is read from source and not from here. The
        # day something reads a builtin's row, this has to carry it.
        b = _check_type(form[3])
        return f'(eff {b})' if b else None
    # `deck-record T` is a record ON THE DECK -- a placement, not a type.
    if head == 'deck-record' and len(form) >= 2:
        return _check_type(form[1])
    if head == 'VectorTy' and len(form) >= 3:
        e = _check_type(form[2])
        return f'(vec {form[1]} {e})' if e else None
    if head == 'VectorMaskTy' and len(form) >= 2:
        return f'(vec-mask {form[1]})'
    if head == 'LinkedListTy' and len(form) >= 2:
        e = _check_type(form[1])
        return f'(llist {e})' if e else None
    if head == 'PropEqTy' and len(form) >= 3:
        a, b = _check_type(form[1]), _check_type(form[2])
        return f'(propeq {a} {b})' if a and b else None
    # `ConstructedTy "Maybe" [TextTy]` -- the name is a bare word here, so a
    # constructor whose name carries a space would need quoting. None does.
    if head == 'ConstructedTy' and len(form) >= 3:
        args = _elems(form[2])
        name = _bare(form[1])
        if args is None or not name:
            return None
        rendered = [_check_type(a) for a in args]
        if any(r is None for r in rendered):
            return None
        return f'(ctd {name}' + ''.join(f' {r}' for r in rendered) + ')'
    if head == 'TypeApply' and len(form) >= 3:
        f_, a_ = _check_type(form[1]), _check_type(form[2])
        return f'(tyapply {f_} {a_})' if f_ and a_ else None
    return None


def check_types(text):
    """name -> the declared type as the checker's s-expression."""
    text = NAME_REC.sub(r'\1', text)
    out = {}
    for chunk in text.split('BuiltinSpec {')[1:]:
        m = re.match(r'\s*bs-name\s*=\s*"([^"]*)"', chunk)
        if not m:
            continue
        ty = re.search(r'bs-type\s*=\s*Just\s*', chunk)
        if not ty:
            continue
        if chunk[ty.end():ty.end() + 1] != '(':
            bare = re.match(r'([A-Za-z_][\w-]*)', chunk[ty.end():])
            r = _check_type(bare.group(1)) if bare else None
        else:
            form, _ = _sexp(chunk, ty.end())
            r = _check_type(form)
        if r is not None:
            out[m.group(1)] = r
    return out


def as_rust_check_types(found, tys):
    body = '\n'.join('    ("{}", "{}"),'.format(n, tys[n]) for n in found if n in tys)
    return ('// Each builtin\'s DECLARED TYPE, as the checker needs it, read from\n'
            '// Types/Builtins.codex by ladder/builtins_probe.py --rust-check-types.\n'
            '//\n'
            '// THE ONLY BUILTIN TABLE THAT CARRIES A TYPE. A second one held the IR\n'
            '// SPELLING of the same declarations, for a lowering that built its own\n'
            '// environment; lowering now takes the checker\'s, so the spelling is\n'
            '// derived from these by `ir::render_ty` and there is nothing left to keep\n'
            '// in step. It also could not express a forall, so `show` was absent from\n'
            '// it -- and instantiating a forall mints, which next-id grades.\n'
            '//\n'
            '// Re-run the probe after a pin change; do not edit by hand.\n'
            'pub const BUILTIN_TYPES: [(&str, &str); '
            + str(sum(1 for n in found if n in tys)) + '] = [\n' + body + '\n];\n')


def names():
    text = SOURCE.read_text(errors='replace')
    found = ENTRY.findall(text)
    if not found:
        raise SystemExit(f'{SOURCE}: no BuiltinSpec entries matched; has the record changed?')
    dupes = [n for i, n in enumerate(found) if n in found[:i]]
    if dupes:
        raise SystemExit(f'{SOURCE}: duplicate builtin names {sorted(set(dupes))}')
    return found


def as_rust(found, ar):
    body = '\n'.join(
        '    ("{}", {}),'.format(n, f'Some({ar[n]})' if n in ar else 'None')
        for n in found)
    return ('// The compiler\'s built-in names and ARITIES, read from\n'
            '// Types/Builtins.codex by ladder builtins_probe.py. A call to one of\n'
            '// these is not an undefined name, and the arity is the shape of the\n'
            '// declared type -- a FunTy spine, with ForAllTy, ForAllEff and\n'
            '// EffectfulTy transparent -- so a function-typed argument does not\n'
            '// inflate it.\n'
            '//\n'
            '// `Some(0)` IS NOT `None`. `Some(0)` is a builtin whose declared type\n'
            '// is not an arrow -- `get-ticks : Integer` -- so a reference to it is a\n'
            '// VALUE and not a function of one argument. `None` is one of the eight\n'
            '// that declare no type at all. Re-run the probe after a pin change; do\n'
            '// not edit by hand.\n'
            f'pub const BUILTINS: [(&str, Option<usize>); {len(found)}] = [\n'
            + body + '\n];\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--rust', action='store_true', help='emit the Rust table on stdout')
    ap.add_argument('--rust-check-types', action='store_true',
                    help="emit the checker's declared-type table on stdout")
    a = ap.parse_args()
    found = names()
    ar = arities(SOURCE.read_text(errors='replace'))
    if a.rust:
        print(as_rust(found, ar), end='')
        return 0
    cts = check_types(SOURCE.read_text(errors='replace'))
    if getattr(a, 'rust_check_types'):
        print(as_rust_check_types(found, cts), end='')
        return 0
    print(f'{len(found)} builtin names from {SOURCE}')
    untyped = [n for n in found if n not in ar]
    nullary = [n for n in found if ar.get(n) == 0]
    print(f'  {len(ar)} declare a type; {len(untyped)} do not: ' + ', '.join(untyped))
    print(f'  {len(nullary)} are NULLARY -- a declared type that is not an arrow')
    print(f'  {len(cts)} have a type this probe can spell for the CHECKER; '
          f'{len(ar) - len(cts)} do not yet: '
          + ', '.join(n for n in found if n in ar and n not in cts))
    print('  ' + ', '.join(f'{n}/{ar[n]}' for n in found[:8] if n in ar) + ' ...')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
