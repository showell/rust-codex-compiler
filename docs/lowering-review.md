# Cold review — the check-to-IR half

Target: `lowering.rs`, `ir_passes.rs`, `preamble.rs`, `ir.rs`, `lambda_lifting.rs`,
`ir_chapter.rs`, `ir_text.rs`, `lowering_types.rs`, `resolve_types.rs`.
Spec grepped throughout: `~/showell_repos/codex-zig-transpiler/generated/codexcheck-subject.codex`
(71,967 lines).

Everything marked **MEASURED** was run. The harness for oracle comparisons is
`cmp.sh` in the scratchpad; it matters that it exists, because two things about
the two arms are easy to get wrong and I got both wrong first:

* `irdump whole` **resolves cites itself** (`irdump.rs:304`, `bundle::load`), so
  handing `codexir` the raw source compares two different programs. Everything
  below feeds both arms the same `bundle one` output.
* **`codexir` writes the IR to stderr and its diagnostics to stdout.** Piping its
  stdout gets you an empty file and a false "identical".

Sanity check on the harness: `fib.codex` and a `[] & xs` unit both come back
`IDENTICAL` byte for byte.

---

## 1. Layering findings — downstream re-derivation

### 1.1 `emit_defs_checked` computes reachability and then throws it away — MEASURED

`ir.rs:102`:

```rust
    let keep = reachable(ch, roots);
    if keep.is_empty() {
        return Err("no root reached: the chapter defines none of ir-emit-roots".into());
    }
```

`keep` is never read again. `ir.rs:122` lowers **every** definition:

```rust
        for d in ch.defs.iter() {
            defs.push(crate::lowering::lower_def(d, &cx)?);
        }
```

So `fn reachable` (`ir.rs:72-93`) — a 22-line call-graph walk — exists to answer
one `is_empty()`.

The module doc at `ir.rs:18-32` states the opposite as a deliberate design
decision:

> ## One deviation, and it is load-bearing
>
> Upstream lowers EVERY definition and prunes once at the end. This lowers the
> reachable ones only, because lowering here refuses what it cannot type exactly
> and a resolved unit carries whole cited chapters of library code nothing in
> the program reaches

**MEASURED** — 12 lines, `unreach2.codex`:

```
Chapter: T

Section: S
  used : Integer -> Integer
  used (n) = n + 1

  unused : Integer -> Integer
  unused (n) = lazy (n + 2)

Section: E
  opening : Integer
  opening = used 1
```

```
$ ~/build/rust-target/release/irdump whole unreach2.codex
REFUSED: unused: Lazy
```

`unused` is not reachable from `opening`. The chapter is refused anyway. The
documented deviation is not in the code.

**Which layer had the fact:** `reachable` itself, two lines earlier, in the same
function.

**Carrying it forward:** `for d in ch.defs.iter().filter(|d| keep.contains(ch.syms.text(d.name)))`.

**Does anything move?** Not on any unit that currently lowers, by the argument
already written at `ir.rs:33` (the passes only remove references, so
prune-then-lower and lower-then-prune reach the same set), and `number_lambdas`
— see 4.2 — does not exist to be disturbed. It moves the *refusal* set: the
following corpus refusals are all in a single named definition and would need
re-checking one by one against reachability, but the shape is right.

**Corpus context, MEASURED** — all 1,246 units in `~/units-u56/`, 44s:

```
$ for f in ~/units-u56/*.codex; do irdump whole "$f" >/dev/null 2>err || sed "s|^|$(basename $f) |" err; done
```

38 refusals of 1,246. By cause:

```
  10  Handle
   6  Error
   4  `OtaContext` has no field `bytes-received` here
   3  Lazy
   2  field access on `error`, which is not a record
   2  binary op OpPow
   2  Try
   1  vector pattern
   1  the chapter defines none of ir-emit-roots
   1  `rsa-take` has more params than its type has arrows
   1  field store into `(tvar 268)`, which is not a record
   1  field access on `(tvar 268)`, which is not a record
   1  field access on `(record-ty "Point" (args))`, which is not a record
   1  `Pt` has no field `z` here
   1  `Person` has no field `email` here
   1  WithTimeout
```

Nine of those 38 are the field-access family, and all nine are 1.2 below.

### 1.2 The field-access rebuild, verified independently — and it is worse than four ways

The prompt's thread is real. I read both sides rather than trusting the note.

`check.rs:2130-2141`:

```rust
            match st.deep_resolve(&obj) {
                Ty::Record(n, _) => match env.type_defs.field(n, *f).cloned() {
                    Some(t) => t,
                    None => st.fresh(),
                },
                Ty::Constructed(n, cargs) => match constructed_field(env, n, &cargs, *f) {
                    Some(t) => t,
                    None => st.fresh(),
                },
                _ => st.fresh(),
            }
```

`lowering.rs:504-528`:

```rust
        Expr::FieldAccess(r, f, s) => {
            let r = expr(r, &Ty::NoExpect, cx)?;
            let rty = r.ty();
            let name = record_name(&rty, cx, "field access on")?;
            let (Some(fty), Some(slot)) = (cx.tds.field(name, *f), cx.tds.field_index(name, *f))
            else {
                return Err(format!(...));
            };
            let fty = match &rty {
                Ty::Constructed(_, cargs) if !cargs.is_empty() => cx
                    .bindings
                    .get(&name)
                    .and_then(|c| crate::check::instantiate_field(c, slot, cargs))
                    .unwrap_or_else(|| fty.clone()),
                _ => fty.clone(),
            };
```

The two copies differ in six ways, four of them user-visible:

1. **`deep_resolve` on the receiver.** `check.rs` does it; `lowering.rs` takes
   `r.ty()` raw. Upstream does it too (`rec-ty = deep-resolve (ctx.ust) (ir-expr-type rec-ir)`,
   subject 54312).
2. **The constructor table.** `check.rs` reads `env.get(n)` (the scoped type
   environment); `lowering.rs` reads `cx.bindings` (the top-level list). Upstream
   reads `lookup-type-split (ctx.overlay) (ctx.base) (cname.value)` — the scoped
   one.
3. **`field_index` is required by lowering and not by the checker.** A record
   whose field type resolves but whose index does not is a refusal in lowering
   and a fresh variable in the checker. (Both branches of the same `let ... else`,
   so a missing field and a missing index give the same message.)
4. **The failure value.** `check.rs` mints `st.fresh()`; `lowering.rs` returns
   `Err` and takes the whole chapter with it. **Upstream does neither**: subject
   54334 is `is otherwise -> ty`, and subject 54339 is
   `is ErrorTy | NoExpectTy -> ty` — the *expectation*, twice over. Nine corpus
   refusals are exactly this.
5. **Ours has none of `refine-receiver-ty`** (subject 54446). Upstream: if the
   stripped receiver type has type variables and the receiver is an `IrName`,
   look the name's binding up and use that instead. That is precisely
   `unit-field-access.codex`'s and `unit-field-assign.codex`'s shape, and
   `qsort-by`'s.
6. **Ours has none of the `EffectfulTy | ForAllTy | ForAllEff` strip**
   (subject 54313-54317).

**MEASURED — a refusal caused by (6), with a self-contradicting error message.**
`noalias-linear-param.codex` declares `point-x : linear Point -> Integer`. Our
message is:

```
noalias-linear-param.codex REFUSED: point-x: field access on `(record-ty "Point" (args))`, which is not a record
```

The message says the type is a record and the code says it is not, because
`render_ty` makes `Ty::Linear` transparent (`ir_text.rs:107`,
`Ty::Linear(inner) => render_ty(syms, inner)`) while `record_name`
(`lowering.rs:853-858`) matches only `Record | Constructed`. The oracle lowers
it fine:

```
$ codexir < ~/units-u56/noalias-linear-param.codex
(def "point-x" "NoAliasLinearParam" (params (param "p" (record-ty "Point" (args)))) \
  (fn (record-ty "Point" (args)) int-default) \
  (field-access (name "p" (record-ty "Point" (args))) "x/0" int-default) 0 0 (unique "p"))
```

**What carrying it forward looks like.** `check.rs` already owns the precedent:
`pat_types` (`check.rs:193`, `record_pat_type` at 431) is an ungraded side table
invented for the same problem, and `lowering::pattern` is nine lines because of
it. The same move here is `record_field_type(sp, t)` on the FieldAccess and
FieldAssign arms, read by `lowering.rs` as `cx.st.field_type_at(*s)`.

**Does anything move?** No. `record_pat_type` is unconditional and does not
touch `expr_types`, `next_id` or `next_row_id`; a parallel `field_types` vector
behaves identically. `substitutions`, `next-row-id`, `expr-types`, `next-id`
and `check-errors` are all untouched as long as no `st.fresh()` call is added or
removed.

**What it does NOT carry.** The *slot* and the *receiver retype* are not the
checker's to give — see 3.1 and 3.2. Those stay in lowering.

### 1.3 `reachable` and `prune_unreachable_roots` are one walk written twice, one of them on strings

`ir.rs:72-93` keys on `&str` and accumulates `BTreeSet<String>` with a
`Vec<String>` worklist. `ir_passes.rs:638-659` is the same walk over `Sym`.
`Sym` is available at both sites (`ch.syms` is right there). The string version
is the one whose result is discarded (1.1), so the cheapest fix to 1.1 also
deletes the duplicate: filter `ch.defs` by the `Sym`-keyed walk.

### 1.4 `once_retype`'s parameter-type threading re-derives a substitution the checker had

`ir_passes.rs:507`:

```rust
    if c.ptys.iter().any(lt::has_typevars) {
        let atys: Vec<Ty> = args.iter().map(|a| a.ty()).collect();
        subst_once(&c.body, &c.params, &args, &c.ptys, &atys)
```

This is **faithful** — subst-once/once-retype at subject 56847 does exactly this,
including the `if list-length ptys == 0 then e` shortcut. Recorded here only
because it looks like re-derivation and is not; see the non-findings.

---

## 2. Layering findings — upstream withholding

### 2.1 `is-punctual` is known at the CST, published in the preamble, and dropped before the def line — MEASURED

`ir_text.rs:256`:

```rust
        "\n  (def {:?} {:?} (params{}) {} {} 0 0)",
```

The trailing `0 0` is hardcoded. `ir_chapter.rs:324` defends this:

> `is-punctual` and `wcet-budget` are upstream's and are emitted as the trailing
> `0 0` of every `(def ...)`; nothing here sets them, so they are not carried as
> fields that would only ever hold zero.

They do not only ever hold zero. **MEASURED**, `~/units-u56/punctual-fastmath.codex`,
whole-file diff against the oracle, everything on the same resolved bytes:

```
$ diff <(sed 's/(def /\n(def /g' oracle) <(sed 's/(def /\n(def /g' ours)
17c17
< (def "bit-clz" "BitOps" ... int-default) 1 0)
---
> (def "bit-clz" "BitOps" ... int-default) 0 0)
19c19
< (def "int-log2" "FastMath" ... int-default) 1 0)
---
> (def "int-log2" "FastMath" ... int-default) 0 0)
```

Two definitions, two bytes, and the two files are otherwise **byte-identical**.
Counts across three units:

```
punctual-quire     ours `1 0)`=0   oracle=21
punctual-iot       ours `1 0)`=0   oracle= 5
punctual-fastmath  ours `1 0)`=0   oracle= 2
```

16 units in `~/units-u56/` declare `punctual`.

**Which layer had the fact — every one of them.** The parser builds
`NodeKind::Punctual` (`parser.rs:379-385`). `preamble.rs:495` reads it and emits
`(ann "hard-realtime" name budget)` correctly. `desugar.rs:621-624` reads it a
second time:

```rust
        for d in tree.descendants(NodeKind::Def) {
            if d.children_of(NodeKind::Punctual).next().is_some() {
                ch.rt_names.push(self.str_of(self.def_name(d)));
            }
        }
```

and puts it in `ch.rt_names: Vec<String>` — a **list keyed by name**, which is
the "searching a list by name when the flag was known" shape. Nothing reads it:
the only other mention in the tree is `desugardump.rs:109`, which prints its
`.len()`.

**Carrying it forward:** `ast::Def` already has exactly this precedent —
`pub is_claim: bool` (`ast.rs:218`), set by the desugarer for the same kind of
reason. Add `is_punctual: bool` beside it, carry to `IrDef`, and `emit_def`
writes `1` or `0`. `rt_names` then has no reason to exist.

**Does anything move?** No counter. IR bytes move for exactly the definitions
that are punctual, and they move **toward** the oracle — from a known-wrong `0`
to the oracle's `1`. Three units in `~/units-u56/` go from differing to (on
`punctual-fastmath`, verified) identical.

### 2.2 `Ty::Record` drops the field list that upstream's `RecordTy` carries

Upstream's `RecordTy (rn) (ra) (rf)` carries its fields, and *four* places read
them straight off the type: `lookup-record-field rfields` at subject 52878,
53635, 54332, and `ir-find-field-in-record` at 57751 (the emitter). Our
`Ty::Record(Sym, Vec<Ty>)` carries name and arguments only.

That is why `lowering.rs` has to reach sideways into `cx.tds` for both the type
and the slot, why `check.rs` needs `constructed_field` + `instantiate_field`
(`check.rs:1299-1324`), and why `ir_text::emit_def` cannot recompute the slot at
emission the way upstream does (3.1). It is one missing field on one enum
variant, feeding three separate reconstructions.

I am **not** recommending the change — `Ty` is on the hot path and the field
list would be cloned on every `deep_resolve`. But it is the honest root of 1.2,
3.1 and 3.2, and it should be written down as such rather than rediscovered.

---

## 3. Ordinary smells and divergences from the subject

### 3.1 The field slot is frozen at lowering; upstream computes it at emission — MEASURED (latent)

`lowering.rs:544` bakes the slot into a `String`:

```rust
                format!("{}/{}", cx.text(*f), slot),
```

Upstream does not carry a slot at all. `IrFieldAccess` holds the bare field
name, and the emitter resolves the index **from the receiver node's final type**
(subject 57653):

```
is IrFieldAccess (r) (f) (ty) (sp) -> let fi = ir-resolve-field-index (ir-expr-type r) f in ...
```

and `ir-resolve-field-index` answers `-1` for anything that is not a `RecordTy`
(57750), at which point `ir-field-with-index` (57760) emits the **bare name with
no slot**.

So the two arms disagree wherever the receiver's *final* type is not a record.
**MEASURED**, `p2.codex` — a field store on a `Box a` receiver, which
`resolve_ty_deep` leaves as `Constructed` because its argument list is non-empty:

```
ours:   (field-store (name "__rev" (ctd "Box" (args text))) "n/1" (int-lit 3) (ctd "Box" (args text)))
```

Upstream's emitter on that node would write `"n"`, not `"n/1"`. It is latent
today only because upstream's `revised` never produces a field store at all
(3.3), so no gold puts these two side by side. It stops being latent the moment
lowering builds a field store on a receiver whose type stays constructed.

The comment at `ir_chapter.rs:217` ("the slot is resolved at lowering and carried
here as part of the name") states the deviation clearly but not that it *is* a
deviation. It is also the reason the passes cannot be trusted to retype a
receiver: `subst_once` (`ir_passes.rs:424`) and `expr` in `resolve_types.rs:153`
both rewrite the field-access *type* and copy `f.clone()` untouched.

### 3.2 The receiver retype is narrower than upstream's, in the arm that matters

`lowering.rs:533-541`:

```rust
            let r = match &rty {
                Ty::Constructed(n, cargs)
                    if matches!(cx.tds.declared().get(n),
                                Some(Ty::Record(_, ra)) if ra.len() == cargs.len()) =>
                {
                    r.with_ty(Ty::Record(*n, cargs.clone()))
                }
                _ => r,
            };
```

Upstream (subject 54342-54344) is:

```
in let node-rec-ty = instantiate-receiver-ty refined-rec-ty resolved-rec-ty
in let fixed-rec = when rec-ty
   is RecordTy (rn) (ra) (rf) -> rec-ir
   is otherwise -> set-ir-expr-type rec-ir node-rec-ty
```

Upstream retypes in **every** non-record case, including `ConstructedTy` with an
empty argument list, where `resolved-rec-ty` is the record the constructor
lookup found. Ours only retypes when the arity matches and the argument list is
non-empty. Today `resolve_types::resolve_ty_deep` (`resolve_types.rs:53-57`)
rewrites bare `Constructed` to the declared `Record` in a *later pass*, so the
net answer usually agrees — which means we get the right bytes for a reason that
is written down nowhere and that a change to `resolve_types` would silently
break. Also: upstream uses the **resolved record's** name `irn`; ours reuses the
constructed name `*n`.

### 3.3 `revised` desugars to a field-store chain, and it is wrong on nested record literals — MEASURED

Not my target file, but it is the largest single cause of corpus refusals and
its error message points the reader at `lowering.rs`. `desugar.rs:433`:

```rust
                for f in n.descendants(NodeKind::RecordField) {
```

`descendants` is a deep walk, so a nested record literal's own fields are
collected as if they were fields of the `revised` receiver. **MEASURED**, 12
lines:

```
  Inner = record { ia : Integer }
  Outer = record { oa : Integer, ob : Inner }
  bump : Outer -> Outer
  bump (o) = o revised { ob = Inner { ia = 5 } }
```

```
$ irdump whole rev.codex
REFUSED: bump: `Outer` has no field `ia` here
```

That is the four `OtaContext has no field bytes-received` refusals, verbatim
(`ota-update.codex:1229` is `progress = OtaProgress { bytes-received = 0, ... }`
inside a `revised`). The fix is the direct children of the brace body, not
`descendants`.

Separately, and independently of the bug: upstream does **not** build field
stores for `revised` at all. It builds a `__record-set` application spine
(**MEASURED**, same file through `codexir`), which is why the `subst-once`
prose at subject 56836 warns about `__record-set` writing into a shared
template. Our deviation is documented at `desugar.rs:13`; it is worth knowing
that it makes every `revised` in the corpus a guaranteed IR-byte difference.

### 3.4 `has_bounded_boundary` consumes a parameter for each quantifier; upstream does not

`ir_passes.rs:173-181`:

```rust
    let mut ret = d.ty.clone();
    for _ in 0..d.params.len() {
        ret = match ret {
            Ty::Fun(_, _, r) | Ty::ForAll(_, r) | Ty::ForAllEff(_, r) => *r,
            other => return bounded(&other),
        };
    }
```

Upstream's `return-bound-in` (subject 56453) decrements only on `FunTy`:

```
   else when ty
    is FunTy (p) (row) (r) -> return-bound-in r (n - 1)
    is ForAllTy (id) (b) -> return-bound-in b n
    is ForAllEff (id) (b) -> return-bound-in b n
```

A quantified definition with a bounded return would look unbounded to us and be
inlined, bypassing the entry/epilogue guards that are the whole reason for the
predicate.

**Unreachable today**, and I checked rather than assumed: `IrDef.ty` comes from
`cx.bindings.get(&name)` (`lowering.rs:191`), and a polymorphic definition's own
binding reaches lowering already instantiated —
`(fn (tvar 41) (fn int-default (int 0 255 ov-error)))`, no quantifier
(**MEASURED**, `bnd2.codex`). So no counter and no byte moves today. It is one
loop-body line away from mattering and it is wrong as written.

### 3.5 `emit_def` never writes `(unique ...)` — MEASURED

Subject 57992-58000:

```
  ir-emit-unique (ns) =
   if list-length ns == 0 then ""
   else " (unique" & ir-cat (for n in ns -> " " & ir-quote n) & ")"
```

Measured instance, `noalias-linear-param.codex`, quoted in full in 1.2: the
oracle's `point-x` line ends `0 0 (unique "p"))`. `IrDef` has no field for it
and `emit_def` cannot write it. Same class as 2.1, but the fact is a *linear
parameter list*, which the checker has (`Ty::Linear`) and the AST loses; this
one needs a real carry, not a flag.

### 3.6 `emit_pat`'s `vec-pat` does not match the subject

`ir_text.rs:238`:

```rust
        IrPat::Vec_(subs, ty, _) => format!(
            "(vec-pat (subs{}) {})",
```

Subject 57619:

```
    is IrVecPat (subs) (ty) (sp) -> "(vec-pat" & ir-emit-pat-list subs 0 & ")"
```

No `(subs ...)` wrapper and **no trailing type**. Unreachable today —
`lowering::pattern` refuses `Pat::Vec_` (`lowering.rs:885`), which is one of the
38 corpus refusals — so this is a floor that is wrong before anyone stands on
it, and it will be stood on by the lowering that clears that refusal.

### 3.7 `prune_unreachable_roots` misses the record-constructor name

`ir_passes.rs:649-651` collects only `IrExpr::Name`. Upstream's DCE collector
(subject 57824) also pushes the record name:

```
    is IrRecord (n) (fs) (ty) (sp) -> ir-dce-collect-fields fs 0 (list-push acc n)
```

Only reachable if a definition and a record type share a name. Low, but it is a
one-line divergence in a walk whose own comment (`ir_passes.rs:446`) says
undercounting is the direction that is not conservative — and that comment is
about `count_refs`, not this walk, which has the same hazard and no such note.

### 3.8 Two expectation arms in `lowering::expr` pass `NoExpect` where upstream passes a type

* `Expr::Binary` (`lowering.rs:326-327`) lowers both operands with `&Ty::NoExpect`.
  Subject 54282-54284 lowers both with `ty`, the node's own expectation.
* `Expr::Unary` (`lowering.rs:261`) lowers the operand with `&Ty::NoExpect`.
  Subject 54287 lowers it with `int-ty-default`.

**Unreproduced.** I tried four shapes (`[] & xs`, an empty list in a record
field, a `LinkedList` field, a bounded left operand) and every one came back
`IDENTICAL`, because the checker's recorded answer at a real source span covers
for the missing expectation everywhere I could reach. It stops covering at a
synthetic span, which is exactly the case the `Expr::NameRef` and `Expr::Lambda`
comments in this same file were written about. Stated as a divergence, not as a
defect, because I could not make it bite.

### 3.9 `Expr::Record` diverges three ways from `lower-record`

`lowering.rs:491-500` versus subject 55691-55703:

| | ours | upstream |
|---|---|---|
| the record's type | `cx.at(*s)`, **refuse** if absent | the constructor's binding, `strip-fun-args`; falls back to the expectation |
| each field's value | `expr(&f.value, &Ty::NoExpect, cx)` | `lower-expr (f.value) field-expected ctx`, where `field-expected` is `lookup-record-field rfields (f.name.value)` |
| the emitted type | as recorded | `refine-record-ty-from-fields` then `prefer-applied-record-ty` |

The refusal is the one with teeth: a record literal at a synthetic span takes
the chapter down, and the desugarer builds synthetic spans (`synth_derived_defs`).
No corpus unit hits it today. Same shape as 1.2 item 4.

### 3.10 `render_row` takes a `SymTab` it does not use

`ir_text.rs:126-127`:

```rust
fn render_row(syms: &SymTab, row: &crate::check::EffectRow) -> String {
    let _ = syms;
```

Dead parameter, silenced rather than removed. One caller.

### 3.11 `IrParam.span` and `IrDef.span` are write-only

Set at `lowering.rs:218` (to the *definition's* span, for every parameter),
`lowering.rs:228`, and `lambda_lifting.rs:251,262`. No reader anywhere in the
target files or the emitter. `IrExpr::span()` *is* read (`act_let` uses it), so
this is specifically the two struct fields. A field that is written with a
made-up value and never read is a fact the next reader will believe.

### 3.12 `ir_text` quotes names with `{:?}` while `ir_quote` exists five lines away

`ir_text.rs:274` writes `ir_quote` precisely because Rust's `{:?}` escapes more
than upstream's three characters, and says so. Then `emit_expr`'s `q`
(`ir_text.rs:142`), `emit_pat` (229, 233), `emit_params` (248), `emit_def` (256)
and the slot (216, 219) all use `{:?}`. Identifiers make the two agree in
practice; the reason is not written down and the file's own docstring argues the
other way. Either route it all through `ir_quote` or say in one line why names
are exempt.

### 3.13 `fold_expr`'s negate fold wraps on `i64::MIN`

`ir_passes.rs:60`: `E::IntLit(v, _) => E::IntLit(-v, *s)`. In release, `-i64::MIN`
is `i64::MIN`, so `-(-9223372036854775808)` folds to the atom `i64-min`. Upstream
(subject 56314, `IrIntLit (-v) sp`) is on a trapping `Integer`. A one-value
silent wrong-but-plausible answer.

### 3.14 `Candidate.ptys` is dead on the leaf path

`collect_leaf_defs` (`ir_passes.rs:277`) fills `ptys`; `leaf_site` and
`subst_leaf` never read it. Faithful to upstream — `InlineLeaf` is one record
shared by both passes there too — so this is noted, not filed.

---

## 4. Comment findings

### 4.1 `ir.rs:4` contradicts `ir.rs:127` and the code

The module diagram says:

```
//!   check ──▶ lower ──▶ lift lambdas ──▶ pipeline ──▶ prune ──▶ text
```

The code (`ir.rs:136-146`) is lower → **pipeline** → resolve → **lift** → prune →
text, and the comment at `ir.rs:127` shouts the correction:

> **THE PIPELINE RUNS BEFORE THE LIFT, AND THE ORDER IS THE POINT.**

The diagram also omits RESOLVE, which has its own module and its own test. Two
readings of the same order, 123 lines apart, in one file.

### 4.2 `number_lambdas` does not exist

`ir.rs:31` and `lambda_lifting.rs:16` both explain that "`number_lambdas` walks
the AST's whole definition list rather than the lowered one". `grep -rn
number_lambdas src/` returns those two comments and nothing else.
`lambda_lifting.rs:34` then says the opposite in capitals:

> **THERE IS NO SEPARATE NUMBERING PASS UPSTREAM, AND OURS COST 90 DEFINITIONS.**

and `LamNames::new` (`lambda_lifting.rs:51`) reserves from the **lowered** defs,
which its own docstring at line 49 says is correct. Two stale comments naming a
deleted function, one of them inside the docstring of the file that deleted it.

### 4.3 `ir.rs:18-32` — the "one deviation, and it is load-bearing" section

Documented in 1.1. This is the worst of the comment findings, because it is not
merely stale: it is the *justification* for a behaviour, and a reader who
believes it will not think to check why an unreachable `lazy` refuses the
chapter.

### 4.4 `check.rs:1650` — "Every expression's type is recorded"

Out of target, but it is the seam. `record_expr_type` is called at exactly five
sites (`check.rs:1738, 1762, 1958, 2003, 2107` — NameRef, Binary, List, Lambda,
Record). Not Apply, If, Let, Match, Act, FieldAccess, FieldAssign, or literals.

The **code is right** — upstream has eight `record-expr-type` calls across those
same five kinds (subject 52175, 52180, 52420, 52421, 52545, 53273, 53684), which
is why `expr-types 145772` is exact. The **comment** is wrong, and it is wrong in
the direction that makes 1.2 look unnecessary: a reader who believes it will
conclude that lowering *could* just look the field-access type up by span.

### 4.5 `ir_chapter.rs:324` — "would only ever hold zero"

Disproved in 2.1, with the oracle's own bytes.

### 4.6 Comments that restate the code

Small and worth one pass, not a project: `ir_passes.rs:222` ("Every name a
pattern binds, appended") wraps a one-line delegation to
`lambda_lifting::pat_names`; `lowering.rs:101` ("The text of a name. One borrow,
one line."); `lowering.rs:151` ("How deep the scopes are, to unwind back to.");
`ir_chapter.rs:2` ("variant for variant"). None of these carry a constraint.

The rest of the commentary in these files is unusually good and should be left
alone — the ones citing a subject line and a symptom (`lowering.rs:265-296` on
`lower-name-normal`, `lowering.rs:329-356` on `binary-result-type`,
`lowering_types.rs:52` on `usable-witness-ty`, `lambda_lifting.rs:301` on CCE
ordering, `preamble.rs:380` on the instance count) each saved me a grep.

---

## 5. Non-findings — considered and rejected

Each of these looked like a defect and is not. The subject line is given so
nobody re-investigates.

* **`fold_apply` matching on the name strings `"text-length"`, `"char-code"`,
  `"char-code-at"`** (`ir_passes.rs:130-141`). Faithful:
  `fold-apply` at subject 56331-56340 is `if n == "text-length" then ...`, and
  the `defined` guard (`skip-list-text-has dn n`) is upstream's too.
* **`count_refs` counting a candidate's own self-reference** (`ir_passes.rs:450`).
  Faithful: `count-refs-chapter` (subject 56937) walks every def's body,
  including the candidate's.
* **`IrExpr::ty()` answering `body.ty()` for a `Let`** (`ir_chapter.rs:254`).
  Faithful: `ir-expr-type` at subject 36792 is `is IrLet (n) (t) (v) (b) (s) -> ir-expr-type b`.
* **`with_ty` being an allow-list rather than a walk** (`ir_chapter.rs:149`).
  Faithful arm for arm: `set-ir-expr-type` at subject 36798-36808 lists exactly
  Name, Apply, Let, If, Match, Act, Record, FieldAccess.
* **Every act statement getting the *block's* expectation, including a `<-` bind**
  (`lowering.rs:716, 721`). Faithful and the comment at `lowering.rs:691` is
  right to flag it as odd: `lower-act-stmts-acc` at subject 55791-55801 passes
  `ty` to both arms.
* **`act_let` lowering the rest of the block after the let's bindings are pushed**
  (`lowering.rs:749-750`). Faithful: subject 55828 threads the accumulated `ctx`
  into `lower-act-stmts-acc stmts ty ctx (i + 1)`.
* **`has_error` recursing into a `List` and nothing else** (`lowering_types.rs:29`).
  Faithful; `ty-has-error` at Lowering.codex:297, and the comment already says so.
* **`ty_admits_widening` covering only Integer and Real** (`lowering_types.rs:48`).
  Faithful, and it is what makes `guarded-field`'s `if` `int-default`.
* **`subst_var` letting a `ForAllEff` fall through while `ForAll` shadows**
  (`lowering_types.rs:156-163`). Faithful — row ids are a separate numberspace —
  and there is a unit test pinning it.
* **`Ty::Linear` being transparent in `resolve_ty_deep`** (`resolve_types.rs:75`)
  and in `render_ty` (`ir_text.rs:107`). Both correct — `noalias-linear-param`'s
  gold spells the parameter `(record-ty "Point" (args))`, measured above. The bug
  is that `record_name` does not strip it (1.2, item 6), not that these strip it.
* **`unit-field-access.codex` / `unit-field-assign.codex` refusing.** These are
  NEGATIVE units. The oracle answers `CODEGEN-HALTED: CDX2095 'Spot' is a unit
  type, not a record`. Our refusal is the right verdict reached in the wrong
  layer (lowering rather than a check error), so the finding — if any — belongs
  to `check.rs`, not here.
* **`(tvar 41)` where the oracle says `(tvar 2)` on a hand-written 8-line
  chapter.** Not a divergence. `irdump whole` resolves cites and `codexir` on raw
  stdin does not, so the two arms saw different programs. Same source through
  `bundle one` first: `IDENTICAL`. This one cost me twenty minutes and is the
  reason `cmp.sh` exists.
* **The `Apply`/`Binary` result types not being cross-checked between operands**
  (`lowering.rs:335`). Faithful, and the comment explaining why the old
  agreement check was removed is one of the better ones in the tree.
* **`ir_passes` running one pass over the def list without re-firing the site
  rule on a spliced body.** Faithful: `inline-expr` fires on the way out
  (subject 56705 onward), same as `rewrite` at `ir_passes.rs:534`.
* **`prune_unreachable_roots` taking `roots: &[&str]` and calling `syms.find`**
  (`ir_passes.rs:643`). The root set genuinely is a list of literal names
  (`IR_EMIT_ROOTS`, `ir.rs:55`, quoted from `opening.codex:1373`), so a string is
  what it is. Not re-derivation.

---

## 6. What I would fix first

1. **`ast::Def.is_punctual` → `IrDef` → `emit_def`** (2.1). The smallest change
   with a measured, oracle-confirmed byte win: `punctual-fastmath` becomes
   byte-identical, three units improve, no counter moves. `rt_names` and its
   name-keyed list go away with it. Two hours.
2. **`desugar.rs:433`, `descendants` → direct children** (3.3). Four corpus
   refusals, a 12-line repro, one word.
3. **Restore the reachability filter at `ir.rs:122`, or delete `reachable` and
   fix the module doc** (1.1, 4.3). One of the two must happen: right now the
   code, the dead call and the docstring tell three different stories. If the
   filter goes back, re-run the 38 refusals and see how many were unreachable.
4. **Make `lowering`'s field access stop refusing** (1.2, items 4 and 6). Two
   changes, both quoted from the subject: strip `Effectful | ForAll | ForAllEff |
   Linear` before `record_name`, and fall back to the expectation instead of
   `Err`. That is up to nine of the 38 refusals and it removes the
   self-contradicting error message. Do this *before* 5.
5. **`check.rs` publishes the field-access type** (1.2). The `pat_types` move,
   applied to field access. Bigger than 4 and it does not subsume it — the slot
   and the receiver retype stay in lowering either way — but it is what stops the
   two copies drifting a fifth time.
6. **The comment sweep** (4.1, 4.2, 4.4, 4.5). Cheap, and 4.3 and 4.4 are both
   actively misleading about the two findings above them.
7. `has_bounded_boundary`'s quantifier peel (3.4), `vec-pat` (3.6), the DCE
   record name (3.7), `render_row`'s dead parameter (3.10), the two write-only
   span fields (3.11). All one-liners, none of them urgent, all of them wrong.

Left deliberately unranked: 3.1 (the baked slot), 3.5 (`(unique ...)`) and 2.2
(`Ty::Record` without fields) are one design question, not three bugs, and it is
Steve's call whether the answer is "carry the fields on the type" or "keep the
slot at lowering and write down why".

---

*Note: `scratch-lowering-review.md` is not covered by `.gitignore` — the file
list there is `target/`, `Cargo.lock`, `ladder/__pycache__/`. This file is
untracked but will show in `git status`.*
