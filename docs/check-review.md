# Cold review of `rust-codex-compiler/src/check.rs`

Read in full against `src/desugar.rs`, `src/ast.rs`, `src/lowering.rs`,
`src/lowering_types.rs`, `src/linearity.rs`, `src/resolve_types.rs`,
`src/builtins.rs`, and the upstream subject
`/home/steve/showell_repos/codex-zig-transpiler/generated/codexcheck-subject.codex`.

**Line numbers are against the WORKING TREE at 2026-09-08 14:42** (`check.rs`
3,094 lines, `git status` dirty, a `.swp` present — the file was being edited
while I read it). The uncommitted change is small and additive: `record_fields`
on `TypeDefs`, a `mutables: BTreeSet<Sym>` built in `check_chapter_full`, and a
widened `linearity::LinEnv`. It invalidates none of the findings below, but if
the file has moved again, anchor on the quoted code rather than the number.

Where a claim was cheap to *measure* I ran the already-built
`target/release/checkdump`; those are marked **MEASURED**. Nothing was built and
no file in the repo was modified.

Two standing caveats:

* **Faithfulness is the requirement.** Every item says whether it mirrors
  upstream (correct by construction), diverges from upstream, or is a place where
  our layering could carry a fact upstream cannot.
* **IR impact is called out.** Anything that would move a graded counter
  (`next-id`, `substitutions`, `next-row-id`, `expr-types`, `check-errors`) or
  change emitted IR says so.

I did not treat any comment as evidence. Where a finding rests on a claim a
comment makes, I read the code and say so.

---

## 1. Layering findings — what `check.rs` re-derives from incomplete information

### L1. `check_chapter_full` re-finds each definition's registration BY NAME, from a list whose index it already knows — `check.rs:1484`

```rust
let own = bindings.iter().find(|b| b.name == d.name).map(|b| b.ty.clone());
```

`register_defs` (`check.rs:1126-1139`) builds this list in exactly this order:
`register_ctors(...)` first, then one `Binding` per `ch.defs` in source order. The
binding for `ch.defs[i]` is at index `ctors.len() + i`, and `register_defs` knew
that index when it pushed. The checker throws it away and recovers it with a
linear scan on the name.

Three costs, increasing:

1. **O(defs × bindings)** — thousands against thousands on the 3.44 MB self-host,
   per definition.
2. **`find` returns the FIRST match, and constructors come first.** A definition
   sharing a name with a variant constructor or a record type checks its body
   against the *constructor arrow* instead of its own signature. Silent.
3. It is the seam that makes L2 possible.

**Which layer had it:** `register_defs`, in this file, ten lines up.
**Carrying it forward:** have `register_defs` return the ctor count, or a struct
with `ctors` and `defs` separate, and index directly. No counter moves and no IR
changes — the same `Ty` is produced, it is just found instead of searched for.

Upstream does not have this shape: `check-def-normal` does `env-lookup env rn`
against a map, and its registration list is not a positional array it searches.

---

### L2. The output binding list is two lists concatenated, and each consumer re-derives which half it wanted — `check.rs:1596-1598`

```rust
let mut bindings = bindings;      // registrations: ctors + one per def
bindings.extend(per_def);          // plus one INSTANTIATED entry per def
(bindings, st, tds)
```

Upstream's `check-all-defs` accumulates `acc` from `[]` and pushes **one entry per
definition** — registrations live in `env`, never in `all-bindings`. The harness
prints `list-length bs` from that list (subject 71956).

Ours returns both, so every definition appears twice with two different types, and
the consumers each recover what they want by accident:

* `section()` (`check.rs:1611`) prints `type-bindings {bindings.len()}` and one
  `tb` line each — **both** halves.
* `Lower::new` (`lowering.rs:88`) collects into a `BTreeMap`, so `per_def`
  overwrites the registration. That is the right answer obtained via an
  undocumented dependency on `extend` order plus `BTreeMap::from_iter` collapse.
  Swap the two lines and lowering silently starts publishing generalised `forall`
  types.
* `Lower::new`'s `base` set wants the union, and gets it.

**MEASURED.** `./target/release/checkdump check slice/Fib.codex`:

```
type-bindings 6          <- $CODEX_GOLDS/rungs/check.truth says 3
tb fib fn
tb double fn
tb opening eff
tb fib fn                <- each name twice
tb double fn
tb opening eff
```

`slice.sh Fib.codex` against `check.truth` is red on this section today, for a
layering reason rather than a typing one.

**Carrying it forward:** return the two lists separately; `section` prints
`per_def` (upstream's `all-bindings`), lowering asks for what it wants. **Changes
`checkdump check` output** — it makes it match the gold. No counter moves, no IR
changes.

---

### L3. A type declaration's parameter list is dropped, then re-derived from the FIRST CHARACTER of each name — `check.rs:847`, `1189`, `1375-1383`

`ast::TypeDef` carries the parameters explicitly:

```rust
TypeDef::Record(Name, Vec<Name>, Vec<RecordFieldDef>, bool, Span),
TypeDef::Variant(Name, Vec<Name>, Vec<VariantCtorDef>, Span),
```

`register_ctors` reads that `Vec<Name>` and immediately flattens it into anonymous
types — `check.rs:1189`, `params.iter().map(|p| Ty::TypeCon(*p))`; `TypeDefs::new`
does the same with `Ty::Constructed(*p, vec![])` at `check.rs:847`. The fact
"these names are this declaration's parameters" is now gone. `parameterize` →
`param_walk` reconstructs it from the initial letter:

```rust
let lower = |n: Name| syms.text(n).chars().next().is_some_and(char::is_lowercase);
```

This is `parameterize-type` (TypeChecker.codex:569) faithfully, and **upstream has
to do it this way** — the same function runs over *definition signatures*
(`ident : List a -> List a`), where nothing declares `a` and case is the only
signal. On the constructor path, though, we hold a strictly better fact and
discard it. Silent consequences: a parameter written with an uppercase initial is
not parameterised; a field type mentioning an unrelated lowercase name that is not
in `ps` *is*.

**Which layer had it:** the parser/desugarer, and it is still in `TypeDef`'s
second field when `register_ctors` reads it.
**Carrying it forward:** thread `ps` in as a membership set, keeping `entries`
discovery order, and fall back to the case test only on the signature path.
**Counter-safe:** `param_of` is called at the same sites in the same order, so
`next-id`/`next-row-id` are unchanged wherever the two rules agree — which is all
conforming input.

---

### L4. `resolve_declared` is `Option<Ty>` where upstream is TOTAL, and three callers paper over the `None` with a value that changes ARITY — `check.rs:889-995`, `855`, `1208`, `1135`

Upstream `resolve-type-expr` (subject 47556) has no failure mode: every arm answers
a `CodexType`, unresolvable cases answer `ErrorTy`. Ours returns `Option` and
propagates `?` through `T::Fun`, `T::App`, `T::Effect` and `T::Linear`.

The three `None` handlers are each wrong differently:

**(a) `TypeDefs::new`, `check.rs:855` — a dropped field SHIFTS EVERY LATER SLOT.**

```rust
.filter_map(|f| Some((f.name, resolve_declared(&ch.syms, &td, &f.type_expr)?)))
```

`TypeDefs::field_index` is the field's position in the declaration, and
`lowering.rs:543` writes it onto the wire as `(field-access OBJ "py/1" text)`.
Silently omitting one field renumbers every field after it. Highest-consequence
`?` in the file.

**(b) `register_ctors`, `check.rs:1208` — a dropped field CHANGES CONSTRUCTOR ARITY.**

```rust
let Some(a) = resolve_declared(&ch.syms, tds, f) else { continue };
```

`MkFoo (Unresolvable) (Integer)` becomes `Integer -> Foo`. `bind_pattern` then runs
the spine out on `is MkFoo (x) (y)` and mints for the surplus (`check.rs:2297`) —
a `next-id` divergence, and every sub-pattern below is bound to a variable instead
of its field type. Upstream's `build-ctor-type` gets `ErrorTy -> Integer -> Foo`
and keeps the arity.

**(c) `register_defs`, `check.rs:1133-1136` — "no declaration" and "declaration did
not resolve" are conflated.**

```rust
let ty = match d.declared_type.first().and_then(|t| resolve_declared(...)) {
    Some(t) => parameterize(&t, &ch.syms, st),
    None => st.fresh(),
};
```

`register-all-defs` mints iff `list-length (def.declared-type) == 0`. The
`and_then` makes an unresolvable *present* declaration mint too.

**Carrying it forward:** return `Ty`, answering `Ty::Error` where it now answers
`None`, and split (c) on `d.declared_type.is_empty()`. **No counter moves on any
input where `resolve_declared` currently succeeds** — i.e. none on the graded
corpus. It removes silent corruption on inputs we have not met.

`T::Constrained` has no arm and falls to `_ => return None`; harmless today
because `desugar.rs:956` unwraps `NodeKind::ConstrainedType` to its body and never
builds the AST variant (see S16, dead variant).

---

### L5. `is_synthetic` reconstructs "the desugarer invented this span" from `line == 0`, and cannot tell it from "the desugarer LOST this span" — `check.rs:217-219`, `desugar.rs:60`

```rust
pub fn is_synthetic(sp: crate::ast::Span) -> bool { sp.line == 0 }
```

Upstream marks it explicitly — `is-synthetic-span` is `span.file-id == 0`, a field
on the span. `ast::Span` has no such field, so the checker infers it.

Sound for deliberate synthesis: the desugarer writes `Span::default()` at the ~15
invention sites (`__seq`, `__rev`, `MkTupN`, `map-list`, `__eq_<T>`, the `True`
guard) and source lines are 1-based. **Not sound for accidental loss:**

```rust
fn head_span(n: &Node) -> Span { head_token(n).map(span_of).unwrap_or_default() }
```

A real source node whose first non-trivia token could not be found yields the
identical all-zeros span. The checker records nothing for it and lowering falls to
its name-keyed fallback (`lowering.rs:265`) with no signal. Two situations, one
encoding.

**Carrying it forward:** add `synthetic: bool` (or upstream's `file: u16`) to
`ast::Span`, set at the invention sites, and make `head_span`'s failure a distinct
loud state. `expr_type_key`'s hardcoded `1u64 << 48` file id becomes real at the
same time.

Honest ranking: I found no *current* miscompile from this. Hazard and lost
distinction, not a live bug.

---

### L6. `flatten_app` un-curries what the desugarer just curried, and the AST node's `Vec` lies about its arity — `check.rs:1083-1095`, `desugar.rs:900-904`, `975-979`, `906-917`

The parser hands `NodeKind::AppType` a base and *all* its arguments; the desugarer
folds them into one-argument nodes to mirror `apply-atype-args`. `resolve_declared`
immediately calls `flatten_app` to reassemble them, because `resolve_applied`'s
`List`/`LinkedList`/`Real`/`Vector` rules are arity rules.

Upstream re-flattens too (`resolve-applied-type`'s `is AAppType` arm recurses with
`inner-args & args`), so the round trip is faithful. What is *ours* is that
`TypeExpr::App`'s second field is a `Vec<TypeExpr>` that is length 1 by
convention — except `desugar.rs:906-917` (`ArithType`), which puts all children in
one node. Nothing enforces it, and `flatten_app` copes with both
(`args.extend(a.iter().rev())` then `args.reverse()` — correct, and fiddly for a
reason nothing states).

**Carrying it forward:** make the node genuinely unary
(`App(Rc<TypeExpr>, Rc<TypeExpr>, Span)`) so `flatten_app` is a plain spine walk
and `ArithType` has to say what it means. Medium value: the code is correct, the
representation permits an invalid state.

---

### L7. `E::Record` rediscovers the record's name from the peeled constructor result while holding the name — `check.rs:2083-2087`

```rust
let rec_name = match &result {
    Ty::Record(rn, _) | Ty::Constructed(rn, _) | Ty::Sum(rn, _) => *rn,
    _ => *n,
};
```

`n` is the name written in the source. In Codex a record's constructor is named
after the type, so `rn == *n` in every well-formed case; where it differs,
`field_index` answers `None` and the field goes unchecked either way. Low value —
listed because it is L1's shape again: a fact the node carries, re-derived from a
downstream artefact with a fallback to the fact itself.

---

### L8. `builtin_env` holds `TypeDefs` and never gives it to the parser that needs it — `check.rs:2474-2519`, `2535-2544`; see R2

`build`'s `"ctd"` arm refuses a constructed type whose name this chapter never
spells, and the comment explains why (interning needs a mutable table). But
`builtin_env` already takes `type_defs: &TypeDefs` and uses it for nothing except
constructing the `TyEnv`. The declared shape of `TypeBinding` — the thing
`resolve_types.rs` exists to fill in later — is in that map at this call site.

---

## 2. Reverse-direction findings — what `check.rs` knows that a later layer redoes

### R1. `Expr::FieldAccess`: the field's instantiated type is worked out twice, and the copies have drifted — `check.rs:2134-2148` vs `lowering.rs:504-533`

Checker:

```rust
match st.deep_resolve(&obj) {
    Ty::Record(n, _)          => match env.type_defs.field(n, *f).cloned() { Some(t) => t, None => st.fresh() },
    Ty::Constructed(n, cargs) => match constructed_field(env, n, &cargs, *f)  { Some(t) => t, None => st.fresh() },
    _ => st.fresh(),
}
```

Lowering, same node:

```rust
let (Some(fty), Some(slot)) = (cx.tds.field(name, *f), cx.tds.field_index(name, *f)) else { ... };
let fty = match &rty {
    Ty::Constructed(_, cargs) if !cargs.is_empty() =>
        cx.bindings.get(&name).and_then(|c| crate::check::instantiate_field(c, slot, cargs)).unwrap_or_else(|| fty.clone()),
    _ => fty.clone(),
};
```

Same derivation, already drifted four ways:

| | check.rs | lowering.rs |
|---|---|---|
| constructor source | `env.get(n)` (live env, shadowable) | `cx.bindings` (per L2, the `per_def` copy) |
| constructed guard | none | `if !cargs.is_empty()` |
| failure | `st.fresh()` — a mint | `unwrap_or_else(|| fty.clone())` — the uninstantiated declared type |
| record receiver, field absent | `st.fresh()` | `Err(...)`, a refusal |

**The right tool already exists in this file.** `pat_types` (`check.rs:180-192`)
is an ungraded second span-keyed table invented so lowering would not rebuild
destructured field types. I verified the payoff is real: `lowering::pattern`
(`lowering.rs:869-886`) is eight lines and reads `pat_type_at`, where upstream
carries `pattern-type-subst` / `apply-ctor-subst` / `pair-tvars` / `subst-tvars`.
Field access is the one place the idea was not applied.

**Carrying it forward:** record the field-access result in a third ungraded table
(or generalise `pat_types` to `aux_types`) and have lowering read it. `field_index`
stays in lowering — the *slot* is genuinely lowering's business. **Would not move
`expr-types`** (separate table, exactly as `pat_types` is), and would not change IR
if the checker's answer is adopted verbatim — but it *would* wherever the two
currently disagree, which is the point.

Confidence: high that the duplication is real; medium that they currently
disagree on some corpus unit — I did not enumerate one.

### R2. `resolve_types.rs` finishes a job `check.rs` starts — `check.rs:936` vs `resolve_types.rs:47-61`

`resolve_declared`'s `T::Named` arm already resolves a declared name through
`tds.by_name`. `resolve_types.rs` then walks every type on every IR node doing the
same lookup for `Ty::Constructed(n, [])`. Its own doc says nothing in the checker
has both the type-def map and the finished IR at once — true of IR nodes in
general, **not** true of the population the pass names: `(ctd "TypeBinding" ...)`
from a *builtin's* declared type, which enters through `check.rs`'s `build`, called
from `builtin_env`, which is holding `type_defs` (L8).

**Carrying it forward:** pass `tds` into `parse_ty`/`build` and resolve `ctd`
there. The pass still exists for types arriving from elsewhere, so this is a
narrowing, not a deletion. **Net wire output should be identical** (the late pass
currently fixes them up) — verify before shipping. Medium confidence, flagged.

### R3. `linearity.rs` re-walks the DECLARED arrow spine `check.rs` already resolved — `linearity.rs:577-637`

`is_linear_atype`, `strip_effect`, `return_after`, `core_name`, `tuple_has_linear`
and `check_def`'s own loop all walk `ast::TypeExpr`, peeling arrows and effect
wrappers, while `check.rs` has the same signature as a resolved
`Ty::Fun`/`Ty::Effectful`/`Ty::Linear` spine in `lin_bindings` (`check.rs:1449`),
handed to the same function.

**Not a defect.** Upstream's `is-linear-atype` is deliberately syntactic, and there
is a real reason ours must be too: `register_defs` → `parameterize` rewrites
parameter names into type variables, so the resolved `Ty` cannot answer "was
`linear` *written* here" for a generic parameter. Recorded so the next reader does
not spend the afternoon on it.

### R4. `builtin_names` parses every builtin type to throw the result away — `check.rs:2522-2530`

```rust
.filter_map(|(n, s)| { let sym = syms.find(n)?; parse_ty(syms, s).map(|_| sym) })
```

Called from `Lower::new` (`lowering.rs:85`), it re-runs the whole s-expression
parse of `BUILTIN_TYPES` to reproduce `builtin_env`'s "which names parsed"
predicate — a fact `builtin_env` established one call earlier and dropped. Have
`builtin_env` return the name set. Pure duplicated work; no output change.

### R5. The in-flight `mutables` set is the pattern done RIGHT — `check.rs:1452-1462` (uncommitted)

Worth naming as the positive example, since it is the same shape as L3 and was
handled correctly:

```rust
// Upstream binds a `"__mutable-" & name` marker into the type
// environment; a set of names is the same fact without the string surgery.
let mutables: BTreeSet<Sym> = ch.type_defs.iter().filter_map(|d| match d {
    TypeDef::Record(n, _, _, true, _) => Some(*n), _ => None }).collect();
```

The `mutable` keyword is read off the declaration where it lives and carried as a
typed set, rather than re-derived from a synthesised name string. That is exactly
what L3 asks for on the parameter list.

---

## 3. Ordinary code smells and divergences in `check.rs`

Items marked **DIVERGENCE** differ from the subject and are correctness issues.

### S1. **DIVERGENCE** — `E::Binary` unifies NOTHING; `infer-binary-op` unifies on every arm — `check.rs:1742-1780`

Upstream `infer-binary-op` dispatches to `infer-arithmetic`, `infer-comparison`,
`infer-logical`, `infer-append` or `infer-cons`, and **every one calls `unify`**.
Ours infers both sides, unions rows, records for `OpAnd`, and then *selects* a
result type with no unification.

Beyond the missing bindings:

* `OpCons` falls to `_ => lt` (`check.rs:1778`). `infer-cons` answers `ListTy lt`
  and unifies `rt` against it. **`n :: xs` currently types as the ELEMENT type.**
* `OpApproxEq`, `OpApproxEqExact` and `OpDefEq` also fall to `_ => lt`; upstream
  routes all three through `infer-comparison`, which answers `BooleanTy`.
  **`a ~ b` over two Reals currently types as `Real`.**
* `OpAppend` falls to `_ => lt`; `infer-append` answers `TextTy` when the left
  resolves to Text.
* `infer-arithmetic`'s `UnitTy` arms have no counterpart, and `arith_result_ty` is
  called on `st.resolve(...)`-ed operands where upstream unifies first and then
  reads `arith-result-ty lt rt` off the *unresolved* pair.
* Six `check-errors` sources absent: `cdx-real-equality-banned`,
  `cdx-text-ordering-banned`, `cdx-arithmetic-requires-numeric` and the
  `is-real-type` / `is-text-or-char-type` / `is-arithmetic-type` guards.

`arith_result_ty` itself (`check.rs:1240-1252`) is a faithful, well-tested port —
the problem is everything around it. **Counter impact:** adding the unifications
moves no mint counter (unification binds, it does not allocate, and
`substitutions.len()` tracks `next_id`). It **would** change `check-errors` and
would change emitted types wherever a variable currently escapes unbound.

### S2. **DIVERGENCE** — a non-empty list literal answers the LAST element's type and unifies none of them — `check.rs:1959-1965`

```rust
let mut elem = Ty::Error;
for x in xs { let (t, erow) = infer_row(x, env, st); elem = t; row = st.row_union(&row, &erow); }
Ty::List(Box::new(elem))
```

`infer-list` infers the first element, answers `ListTy first.inferred-type`, and
calls `unify-list-elems` to unify every later element *into* the first. Ours
overwrites `elem`, so `[n, m]` answers `List(typeof m)` and `[Just 1, None]`
answers `List (Maybe (tvar N))` with nothing telling `None` what it holds. Would
change emitted IR. Also missing: `cdx-list-literal-too-large`.

### S3. **DIVERGENCE** — an unknown name is silently `Error`, records an `expr-types` entry upstream never records, and raises no diagnostic — `check.rs:1687-1691`, `1736`

`infer-name`'s not-found branch bags `cdx-unknown-name` (or `cdx-nothing-as-value`
for `Nothing`) and returns **without** calling `record-expr-type`. Ours falls to
`None => Ty::Error` and then records at `check.rs:1736` regardless.

**MEASURED**, `f : Integer -> Integer / f (n) = nope`:

```
check-errors 0        <- upstream: 1
expr-types  1         <- upstream: 0
```

Two graded counters, on the most common error class in the language. Also absent
from this arm: `rename-lookup (env.chapter-renames)` (chapter cite renames are not
applied before the lookup) and the `cdx-axiom-assumed` warning for `assume`.

### S4. **DIVERGENCE** — a missing record field MINTS instead of raising `cdx-unknown-record-field`, and two distinct failures collapse into one `None` — `check.rs:2137-2148`

Upstream's `AFieldAccess` mints (`fresh-and-advance`) only when the receiver **does
not resolve to a record at all**. Record-but-no-such-field answers `ErrorTy` and
bags `cdx-unknown-record-field`; a `UnitTy` receiver bags `cdx-field-on-unit-type`.

Ours mints in all three, because `env.type_defs.field(...)` and
`constructed_field(...)` answer `None` for "not a record here" and "no such field"
alike. `constructed_field` (`check.rs:1322-1325`) is where they merge — `?` on
`field_index` and on `env.get(n)` identically.

**MEASURED**, `R = record { ra : Integer }` / `f (r) = r.nosuch`:

```
next-id 3   substitutions 3   check-errors 0
```

against `next-id 2 / check-errors 1` for the upstream shape. Both counters diverge.

Same collapse in `E::FieldAssign` (`check.rs:2158-2163`), which also omits
`cdx-field-assign-immutable`, `cdx-field-assign-unobservable`,
`cdx-field-on-unit-type` and `cdx-unknown-record-field`. *Note:* the working tree
is building the `mutable` fact right now (R5) but routing it to `linearity.rs`;
upstream raises `cdx-field-assign-immutable` in the checker's `AFieldAssignExpr`
arm. Worth deciding deliberately which layer owns it rather than letting it land
where the current task happens to be.

### S5. **DIVERGENCE** — `E::Lazy` is fused with `E::Unary`, and the arm matches neither — `check.rs:1933-1937`

```rust
E::Unary(x, _) | E::Lazy(x, _) => { let (t, xrow) = infer_row(x, env, st); row = xrow; t }
```

Two unrelated rules:

* **`ALazyExpr`** answers `FunTy int-ty-default thunk-row inner-type` with
  `thunk-row` from `open-row-if-closed` — **a lazy expression MINTS A ROW** — and
  hands `empty-row` up. Ours answers the inner type, mints nothing, and propagates
  the inner row. `next-row-id` diverges by one per `lazy`, and the node's wire type
  is the value's rather than a thunk arrow's.
* **`AUnaryExpr`** has real logic: an `is-int-min-literal` shortcut, an
  `is-real-type` passthrough, an `is-undecided-type` passthrough, else
  `unify op-ty int-ty-default` answering `int-ty-default`. Ours answers the
  operand's type unconditionally and unifies nothing.

`lowering.rs:259-264` builds `IrExpr::Negate(x, x.ty(), s)` from the operand's
type, so lowering is consistent with *our* checker, not upstream's — check them
together.

### S6. **DIVERGENCE** — `E::Try` does five things differently from the `E::Act` arm above it — `check.rs:2180-2196`

Upstream runs `infer-act` **separately** on `body`, `fb` and `fail` (skipping empty
ones), row-unions all three, and answers `body-r.inferred-type`.

```rust
E::Try(t) => {
    let mut last = Ty::Nothing;
    let mark = env.scope.len();
    for stmts in [&t.body, &t.fallback, &t.failure] {
        for stmt in stmts { match stmt {
            ActStmt::Exec(x, _)    => last = infer(x, env, st),
            ActStmt::Bind(n, x, _) => { last = infer(x, env, st); env.bind(*n, last.clone()); }
        }}
    }
    env.scope.truncate(mark);
    last
}
```

1. **The result is the LAST statement of `failure`**, not the body's type.
2. **Every row is discarded** — `infer` drops it.
3. **`Bind` binds the RAW type**, not `st.deep_resolve(&t)`. The `E::Act` arm does
   deep-resolve, and I verified the difference matters: the `act_bind_is_in_scope`
   test module at `check.rs:2880` pins `(next_id, next_row_id, expr_types) == (4, 6, 7)`
   and would read 5 on a raw bind. The `Try` arm re-makes that bug.
4. **All three lists share one scope**, so a `<-` in `fallback` is visible in
   `failure`; upstream scopes each to its own `infer-act`.
5. `t.count` is never read.

### S7. **DIVERGENCE** — `E::Handle` and `E::WithTimeout` discard the row and the handler's bindings — `check.rs:2170-2178`

```rust
E::Handle(h) => { let t = infer(&h.body, env, st);
                  for c in &h.clauses { let _ = infer(&c.body, env, st); } t }
E::WithTimeout(w) => infer(&w.body, env, st),
```

Upstream `AHandleExpr` resolves the body's row and either drops covered labels, or
**mints a fresh row** (`fresh-row-id`) and `unify-row`s an extension onto it, or
bags `cdx-handler-unused`. `infer-handle-clauses` calls `bind-lambda-params`
(**one fresh variable per clause parameter**) and `fresh-and-advance` for the
`resume` name (**one more**), binds both, and row-unions each clause's row.

So per clause we are `params + 1` short on `next-id`, and short by the handle's own
mint on `next-row-id`. `WithTimeout` drops the row where upstream returns the whole
`CheckResult`. `E::FieldAccess` (`check.rs:2121`) and `E::FieldAssign`
(`check.rs:2156-2157`) also call `infer` and drop the row. Five arms leak it, and
`open_row_if_closed` at a lambda consumes it, so each leak can cost a row id.

Unlike the `Induction` arm — which documents its approximation honestly — nothing
marks these as known gaps.

### S8. `subst_row_var` has drifted from its sibling `subst_type_var` — `check.rs:778-806`

`subst_type_var` (`739`) walks `Fun`, `List`, `LinkedList`, `Linear`, `Effectful`,
`Sum`, `Record`, `Constructed`, `Vector`, `Unit`, `ForAll`, `ForAllEff`.
`subst_row_var` walks `Fun`, `List`, `Effectful` and `ForAll` only.

* **`ForAllEff(j, b)` with `j != id` falls to `other => other.clone()`** — the body
  of a differently-bound row quantifier is never entered. `instantiate` calls
  `subst_row_var` once per `ForAllEff` in a chain, so a type with two row
  parameters has its inner one substituted into a body the walk never reaches.
  High confidence this is a bug.
* `LinkedList`, `Linear`, `Vector`, `Unit`, `Record`, `Sum`, `Constructed` are
  missing, so a row variable inside `LinkedList (Integer -> [e] Integer)` is never
  rewritten. Medium confidence — read `subst-row-var`
  (TypeCheckerInference.codex:251) for the intended arm list before changing it.

### S9. `row_union` neither sorts nor de-duplicates labels, where upstream's `make-row` does both — `check.rs:332-360`

`make-row` runs `sort-labels-canonical`, and `insert-label-sorted` skips an equal
label (`if c == 0`). Ours:

```rust
let mut merged = a.labels.clone();
merged.extend(b.labels.iter().cloned());     // check.rs:345 -- no sort, no dedup
```

Two sibling `act` statements that both perform `Console.Write` union two rows with
the same label and different ids, fail the identical-rows early-out, and produce
`labels = [Console.Write, Console.Write]`. `resolve_row` (`check.rs:302-306`)
*does* de-duplicate, so the file is internally inconsistent. Two more in the same
function:

* our empty test is `a.labels.is_empty() && a.id < 0`; `row-is-empty` also requires
  `text-length (row.tail-name) == 0`. A row with a tail *name* but no id — which
  `resolve_declared`'s `T::Fun`/`T::Effect` arm produces before `parameterize`
  runs — is treated as empty and discarded.
* our identical test adds `a.tail == b.tail`; `rows-identical` compares only
  `tail-id` and labels.

**Would change emitted IR** wherever a row reaches the wire with a duplicated or
mis-ordered label. I did not find a corpus unit that exhibits it — the early-outs
cover the common shapes. Real divergence, unproven impact.

### S10. `check-errors` sources absent wholesale

`check-errors` is graded, so each is a latent divergence on any subject that
triggers it:

| upstream site | diagnostic |
|---|---|
| `check-lit-range` / `check-num-lit-range` | integer and Real literal range/overflow |
| `check-match-exhaustiveness` | non-exhaustive `when` |
| `check-record-complete` | record literal missing a field |
| `check-mutation-in-ctor-fields` | mutation inside a constructor field |
| `bind-list-ctor-pattern` | `cdx-list-pattern-shape` (three shapes) |
| `bind-ctor-pattern-generic` | `cdx-unknown-pattern-ctor` (noted in place, `check.rs:2283`) |
| `check-effect-row-subset` | body performs effects the signature does not declare |
| `check-declared-rigidity` | a declared type variable was pinned |
| `lint-return-narrowing` / `lint-narrowing-check` | the whole narrowing lint |
| `check-bounded-bases-def` | bounded-integer base checking |
| `check-rt-*` | `punctual` no-alloc / no-lambda / no-self-recursion |
| `cdx-resource-exhausted` | the `max-recursion-depth` guard on `infer-expr-at` |

The last deserves separate mention: `infer_row` has **no depth budget**, where
upstream refuses at `max-recursion-depth` with a diagnostic. A deeply nested
expression blows the Rust stack instead — a crash where upstream reports.

### S11. `E::Lit` types a Real literal and a char literal as `Ty::Error` — `check.rs:1679`

```rust
E::Lit(..) => Ty::Error,
```

covers `NumLit` and `CharLit`; `infer-literal` (subject) answers `real-f64` and
`CharTy`. `Ty::Error` unifies with everything (`check.rs:626`), so this fails
silently: a variable that should be pinned to `Char` by `f 'a'` stays free, and
`let c = 'a' in ...` binds `c : Error`.

Lowering emits the literal from the AST kind directly (`lowering.rs:246-256`), so
the literal node itself is right on the wire — which is why it survived.
Mitigating: no counter moves. Aggravating: two-line fix, and the code reads as if
`NumLit`/`CharLit` were not language features.

### S12. `bind-def-params` binds the `linear` wrapper where upstream strips it — `check.rs:1528-1542`

Upstream: `let bound-ty = strip-linear-ty param-ty in env-bind-local env ... bound-ty`.
Ours binds `*a` raw. Since `Ty::Record`/`Ty::Constructed` are matched structurally
in the field arms, a `linear R` parameter falls to `_ => st.fresh()` on every
`r.field` — an extra mint per access and a lost field type. `strip_linear` already
exists at `check.rs:1065`.

Two more in the same block:

* `spine = None` (`check.rs:1535`) is permanent, so once the declared spine runs
  out **the body is never unified against the declared result** (`want` is `None`
  at `check.rs:1552`). `bind-def-params` leaves `remaining` unchanged and still
  unifies.
* `check-def-normal`'s `row-tied` step — for an *undeclared* definition, unify the
  last arrow's row against the body's row — has no counterpart. That is a
  `unify-row`, and its open-meets-open arm mints.

### S13. `bind_var` and `add_row_subst` silently do nothing on an out-of-range id — `check.rs:320-324`, `601-605`

```rust
fn bind_var(&mut self, id: u32, t: Ty) {
    if let Some(slot) = self.substitutions.get_mut(id as usize) { *slot = t; }
}
```

An id outside the slot array is a bug in this file, not an input condition.
Swallowing it loses a binding silently, which reads downstream exactly like a
variable that was never constrained. Same in `resolve` (`check.rs:513-528`) and
`resolve_row` (`293-318`), which return the unresolved value after 10,000
iterations without saying anything. Fail-loud is the floor.

### S14. Scope unwinding is done two incompatible ways, and the fragile one is used four times

* mark/truncate: `E::Let` (`1901`, `1916`), `E::Try` (`2183`, `2194`)
* pop-N-times: definitions (`1589`), `E::Act` (`1885`), `E::Match` (`2056`),
  `E::Lambda` (`1977`)

The `E::Let` arm's comment narrates the disaster the count style caused and the
test module at `check.rs:2958` pins it — I verified that test does assert the global
`table`'s type survives a later definition. The count style survives in four
places, and `bind_pattern`'s `-> usize` exists only to feed one. Converting all
four to mark/truncate deletes the return value and one class of bug.

### S15. `instantiate_inner`'s second parameter is dead — `check.rs:466-482`

```rust
pub fn instantiate(&mut self, t: &Ty) -> Ty { self.instantiate_inner(t, 1) }
fn instantiate_inner(&mut self, t: &Ty, _unused: usize) -> Ty { ... self.instantiate_inner(&b, 0) ... }
```

Named `_unused`, passed `1` then `0`, never read.

### S16. Smaller items

* `check.rs:1539` — `saved.push(p.name.clone())`: `p.name` is a `Copy` `Sym`, and
  `saved` is used only as `for _ in saved`. It is `d.params.len()`.
* `check.rs:1743-1745` — `_rt` is bound with a leading underscore and then used at
  `check.rs:1776`.
* `check.rs:703` — `Ty::Effectful(e1, _, r1)` vs `(e2, _, r2)`: unification
  ignores the scopes vector. Deliberate? Nothing says.
* `check.rs:439-446` / `456-463` — `pat_type_at` and `expr_type_at` are the same
  five lines over two fields.
* `check.rs:2386-2400` — `parse_row`'s `"rowvar"` arm uses
  `.and_then(|w| w.parse().ok()).unwrap_or(-1)`, so a malformed `BUILTIN_TYPES`
  entry becomes a *closed* row instead of an error. With `builtin_env`'s
  `else { continue }` (`check.rs:2540`), a typo in the builtin table silently drops
  or mis-types a builtin — the exact failure the `take_group` doc says already
  happened once.
* `check.rs:1429-1432` — `check_chapter` exists only to drop `tds`; four callers,
  all tests.
* `pat_span` (`check.rs:2833`) is production code sitting **between two
  `#[cfg(test)] mod` blocks**. Five test modules are interleaved with production
  items from `check.rs:2545` to the end of the file.
* `ast::TypeExpr::Constrained` is a dead variant — matched in four files,
  constructed in none (`desugar.rs:956` unwraps it). Belongs to `ast.rs`.
* **Module size.** 3,094 lines holding the type representation, the unifier, the
  declared-type resolver, registration, the inference walk, the environment, a
  hand-written s-expression parser for `BUILTIN_TYPES`, and the harness printer.
  Cleanest cut is the parser (`parse_ty` / `take_group` / `parse_row` /
  `parse_one` / `take_word` / `atom` / `build`, `check.rs:2346-2520`): 175 lines
  with nothing to do with type checking, separately testable, and the piece that
  disappears entirely if `builtins.rs` ever grows real constructor calls.

---

## 4. Comment findings

Secondary section. Only comments that are **wrong relative to the code beneath
them** or that repeat orientation belonging in the README once. Every one below
was checked against the code, not taken on its word.

### C1. `check.rs:2108-2110` claims the checker does not carry record fields — it does, three lines below

```rust
// **A FIELD ACCESS ON A TYPE THAT IS NOT A RECORD MINTS A FRESH
// VARIABLE**, which is most of them here: the field's type comes from
// the chapter's type definitions and this does not carry them yet.
```

`TyEnv` carries `type_defs` (`check.rs:2316-2327`) and the arm at
`check.rs:2137-2140` calls `env.type_defs.field(n, *f)`. The very next paragraph of
the same comment block sets out the future condition — *"When record fields are
carried, the successful lookup must mint NOTHING"* — and the code already
implements it. So the block states a present-tense falsehood, and a reader
diagnosing S4 (the minting on a *missing* field) would be told the minting is
expected because fields are not carried, when it is not. Highest-value comment fix
in the file: this one actively misdirects.

### C2. `check.rs:1628-1632` says the section is shaped to `codexcheck` — it is not

```rust
// `CheckHarness.codex` prints this and `$CODEX_GOLDS/rungs/check.truth`
// does not: the bank predates the row counter. `codexcheck` is the control
// now, so the section is shaped to IT.
```

Verified false for the `type-bindings` lines: `cc-bindings` (subject 71926) prints
one entry per definition, and `section` prints registrations *and* per-def entries
— **MEASURED** at 6 for `Fib` (L2). The comment is true of `next-row-id` alone.
As written it is the sentence that would stop a reader investigating L2.

### C3. `check.rs:1919-1932` describes a state of the file that no longer exists

```rust
// **EVERY REMAINING FORM IS WALKED, EVEN WHERE THE TYPE IS NOT KNOWN.**
// ... no name inside a lambda, a match arm, a record literal or a
// list literal was ever visited ...
// ... until then they recurse and mint nothing of their own ...
```

All four forms it names now have full arms below it with real minting —
`E::List` at `check.rs:1945`, `E::Lambda` at `1969`, `E::Match` at `2034`,
`E::Record` at `2066`. The comment sits as the doc for `E::Unary | E::Lazy`
(S5), so a reader takes "recurse and mint nothing of their own" as a *statement of
intent for this arm* when it is a fossil of an earlier pass. It is why S5 reads as
deliberate.

### C4. `check.rs:2215-2216` documents a parameter that does not exist

```rust
/// `expected` is the type the enclosing pattern decided for this position;
/// only where there is none does a variable mint one of its own.
```

`bind_pattern`'s signature (`check.rs:2237-2242`) is `(p, ty, env, st)`. There is no
`expected`. The parameter was renamed to `ty` and the comment was not.

Same block: `bind_pattern` carries **two independently written doc headers** stacked
(`check.rs:2202-2213` and `2219-2236`), both opening on "a constructor pattern
instantiates the constructor, not its variables", with the orphan `expected`
sentence wedged between them. One of the two should go.

### C5. `linearity.rs:96-98` (uncommitted) — a doc comment was orphaned by the in-flight edit

The working-tree diff inserts `path_max` **between `move_join`'s doc comment and
`move_join`**:

```rust
/// `lin-move-join`: the value was rebound to `h` and this name is now dead, so
/// everything the old name still does counts as `dead`.
/// `lin-path-max`: two paths of which one is taken, ...
fn path_max(...) { ... }

fn move_join(moved: LinResult, dead: LinResult) -> LinResult {
```

`lin-move-join`'s doc is now attached to `path_max`, and `move_join` has none.
Worth catching before it is committed. (`path_max` is also currently unused.)

### C6. The file header's oracle block is stale — `check.rs:1-39`

* `check.rs:4` — *"`ir.rs` reached 8 of 1,012 golds and then stalled"*. Per the
  project's own record the corpus is now at 1,208 of 1,246 lowering with all 28
  curated subjects byte-identical. A reader takes this as current status.
* `check.rs:11-25` quotes `check.truth` as the oracle, showing `type-bindings 3`
  and no `next-row-id`. The code now prints `next-row-id` and, per L2, six
  bindings — so the header's quoted gold no longer describes this file's output.
* `check.rs:36-39` — *"The three counts need inference and will not match until it
  does. Reporting the section with the counts wrong is the point"*. They match now.

This is orientation-plus-history, and the parts that are still load-bearing (why
`next-id` order is graded, why the representation mirrors `CodexType.codex`) would
survive a trim to about a third of the length.

### C7. Project orientation repeated per module

*"Cobblestone's `Desugarer.codex`"* (desugar.rs:1), *"`AstNodes.codex`, variant for
variant"* (ast.rs:1), *"a representation that cannot express what theirs expresses
cannot be compared against theirs"* (check.rs:43-45), *"a chapter of its own
upstream"* (resolve_types.rs:1). The README already says it once and better
(README.md:1-30, "Four rules this repo is built under"). Each module restating it
is the orientation-in-every-module pattern; the per-module version that earns its
keep is the *specific* upstream function a file mirrors, not the general claim.

### C8. `check.rs:1197-1204` — a comment about a previous comment

*"...the note that stood here said a record declared no function and needed its
own probe, and this is that probe's answer."* The answer is above it; the history
of the note is not information a future reader can use.

**Not filed:** the SHOUTY-caps measurement notes that record *what was measured on
`codexcheck` and what broke without the rule* — `open_row_if_closed`'s "+1 per
lambda over an effectful body", `resolve_applied`'s "99 definitions spelled
`(ctd "LinkedList" ...)`", `E::Act`'s "cost seven variables on the self-host". I
verified several against the code and the subject and they are accurate. Those are
constraints and orderings that matter, which is exactly the load-bearing case.

---

## 5. Non-findings — deliberately rejected, with the reason

1. **`"__record-set"` matched by name string in `bind_record_set_value`
   (`check.rs:1259-1297`).** Looks like the "special case keyed on a NAME string"
   symptom and is not: `__record-set` is a real source-level builtin
   (`builtins.rs:181,457`) written at ~40 sites in the subject; the desugarer never
   synthesises it (`Expr::FieldAssign` is a separate node, `desugar.rs:292`,
   `438`). Upstream's `lint-record-set` (subject 52828) matches the same string in
   the same nested-`AApplyExpr` shape. Faithful. *(One real gap: our port omits the
   trailing `lint-narrowing-check` — that is S10's narrowing-lint row.)*

2. **`"Nil"` / `"Cons"` matched by name in `bind_pattern` (`check.rs:2254-2264`).**
   `is-builtin-list-ctor` (subject 53483) is literally
   `if n == "Cons" then True else n == "Nil"`, dispatched from `bind-pattern`'s
   `is ListTy (elem)` arm — same order, same shape, and `LinkedList` correctly falls
   through in both. Faithful. The shape errors it should raise are filed under S10.

3. **`"List"` / `"LinkedList"` / `"Real"` / `"Vector"` in `resolve_applied`
   (`check.rs:1009-1031`) and the qualifier words in `resolve_real_quals`.**
   Verbatim `resolve-applied-type` / `resolve-real-quals` (subject 47609, 47593),
   including the wrong-arity fallbacks. Faithful.

4. **`Vector`'s length read out of a NAME with `lit_text_to_integer`.** It *is*
   re-parsing text for an integer the lexer knew, but upstream does the same
   (`let n-text = when (list-at args 0) is ANamedType (nt) (ns) -> nt.value
   is otherwise -> "0"`), and `ast::TypeExpr` has no integer node to carry it.
   Fixing it means a new `TypeExpr` variant for one construct. Noted, not filed.

5. **`resolve_declared`'s string comparisons against `"Integer"`, `"Text"`,
   `"Boolean"`, `"Char"`, `"Nothing"`, `"Real"`, `"Proof"` (`check.rs:897-906`).**
   `resolve-type-name` (subject 47605) is the same seven comparisons in the same
   order. Faithful.

6. **`type_kind`'s `_ => "other"` catch-all (`check.rs:128-146`).** `cc-type-kind`
   (subject 71907) has precisely these fourteen arms and the same
   `is otherwise -> "other"`. Graded output. Faithful, verbatim.

7. **`param_walk`'s lowercase-initial rule as such.** The rule is
   `parameterize-type` and is correct; only discarding `ps` before applying it is
   filed (L3). Do not "fix" the rule.

8. **`lowering.rs` reading types back out of `expr_types` by span.** The designed
   interface, and it has to be: `fib` appears twice in its own body with a
   different row id at each, so a name-keyed lookup cannot work.

9. **`UnifyState::default` starting at `next_id = 2`, the `-1` row default, the
   `pat_types` second table, and the `Induction`-walked-as-a-`Match`
   approximation.** All deliberate and all measured. The `Induction` arm
   (`check.rs:2014-2033`) is the model for how to record a known approximation —
   which is why S5/S6/S7, the same kind of gap with none of the honesty, are filed
   and this is not.

10. **`linearity.rs` walking `TypeExpr` rather than `Ty`.** Filed as R3 and
    explicitly rejected as a defect: `is-linear-atype` is deliberately syntactic
    upstream, and `parameterize` destroys the information the semantic type would
    need.

11. **`resolve_types.rs` existing at all.** Only the *builtin* slice of its work is
    filed (R2). The pass is genuinely needed for types reaching the IR from
    elsewhere.

---

## What I would fix first

1. **L2** — split the returned binding list. Verified red against the gold today.
2. **S1 / S2 / S3 / S4** — the four measured or clearly-evidenced inference
   divergences: binary unifies nothing, list literals take the last element,
   unknown names are silent, missing fields mint.
3. **C1 / C2** — the two comments that would stop someone finding S4 and L2. Cheap,
   and they are actively misdirecting right now.
4. **L4** — make `resolve_declared` total; removes two silent arity/slot
   corruptions.
5. **L1** — index the registration instead of searching it by name.
6. **R1** — record the field-access type in an ungraded table the way `pat_types`
   already does for patterns, and delete lowering's copy.
