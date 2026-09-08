# Cold review — `src/desugar.rs` (1258 lines)

Reviewer: fresh eyes, no prior context on this file. Spec consulted throughout:
`/home/steve/showell_repos/codex-zig-transpiler/generated/codexcheck-subject.codex`
(71,967 lines, referred to below as **the subject**). Everything marked
**MEASURED** was actually run; the command and output are inline.

Binaries used: `~/build/rust-target/release/desugardump` (no rebuild).
Corpus: `~/units-u56/` (1,246 units).

**Nothing in this file was modified.**

---

## 0. What I checked first, so the rest can be read against it

The subject's span model is the key to most of this file, and it is richer than
ours. `SourceSpan` upstream carries **four** facts:

```text
subject:35969   synthetic-span : SourceSpan
subject:35970    SourceSpan { start = ..., end = ..., file-id = 0, provenance = ProvSynthetic }
subject:35978   is-synthetic-span (span) = span.file-id == 0
subject:42697   desugared-span (s) = span-with-provenance s ProvDesugared
```

So upstream has **three** states: `ProvParsed` (a real token), `ProvDesugared`
(a real location, but this node is not in the source), and `ProvSynthetic`
(file-id 0, no location at all). `record-expr-type` (subject:46134) skips only
the third:

```text
  record-expr-type (st) (sp) (ty) =
   if is-synthetic-span sp then st
   else ... list-push (st.expr-types) ...
```

Our `ast::Span` is `{ line, col, offset, len }`. There is no provenance field.
That is the root of finding **L2.1**.

---

## 1. Layering findings — what desugar re-derives from incomplete information

### 1.1 The `for` loop variable is recovered by a string comparison, after both the lexer and the parser already knew it — MEASURED-adjacent, verified by code

`desugar.rs:310-316`:

```rust
NodeKind::ForExpr => {
    // `for x in xs -> b` is `map-list (\x -> b) xs`.
    let var = n
        .own_tokens()
        .find(|t| matches!(t.kind, Kind::Identifier | Kind::Underscore) && self.text(t) != "for")
        .map(|t| self.sym(t))
        .unwrap_or_default();
```

Three layers below this already hold the answer exactly:

* `src/token.rs:74` declares `Kind::ForKeyword`. **It is never produced.**
  `grep -n "ForKeyword" src/*.rs` returns only `token.rs:74` and `token.rs:205`
  (the display arm). The lexer's keyword table (`src/lexer.rs:229-259`) has
  `in`, `not`, `claim`, `punctual`, `bounded`, `linear` — no `for`.
* `src/expr.rs:313-316` (the parser) makes the decision **once**, positionally:

  ```rust
  Kind::Identifier => {
      // `for` is a keyword the lexer does not know about...
      if p.sig(0).is_some_and(|t| p.text_is(t, b"for")) {
          return parse_for(p, cp);
      }
  ```
* `src/expr.rs:658-665` (`parse_for`) then **bumps the loop variable
  positionally**, immediately after `for` and before `InKeyword`.

Desugar throws that structure away and recovers it by re-testing the *text* of
every own-token. The subject does not do this. Its CST node carries the token
as a **field**:

```text
subject:37663    | ForExpr (Token) (Expr) (Expr)
subject:39849   parse-for-expr (st) =
subject:39851    in let var-tok = current st1          -- positional, no string test
subject:39867   ExprOk (deck-record (ForExpr var-tok list-expr body))
subject:42765    in let lam = ALambdaExpr [make-name (token-text var-tok)] dbody synthetic-span
```

This is the sharpest instance of the owner's question in the whole file, and it
runs the wrong way: **upstream, which throws trivia away, keeps the variable as
a named field; we, with a lossless CST, keep it in an anonymous token bag and
recover it by string comparison.**

It is also fragile rather than merely redundant. `for for in xs -> b` parses
(`parse_for` accepts any `Identifier` as the variable) and desugars to a lambda
whose parameter is `Name::default()`, silently. Note that two neighbouring
functions in this same file already do it structurally —
`field_after_dot` (`desugar.rs:130`: `skip_while(|t| t.kind != Kind::Dot)`) and
`ForAllType` (`desugar.rs:962-964`: `skip_while(|t| t.kind != Kind::LeftParen)`)
— so the string test is the odd one out even locally.

**Fix:** either give the parser a `NodeKind` wrapper for the loop variable (the
subject's shape), or at minimum read it as
`own_tokens().take_while(|t| t.kind != Kind::InKeyword)` — `InKeyword` *is* a
real lexer kind (`token.rs:38`, produced at `lexer.rs:229`).

### 1.2 `binary_op`'s sibling: the whole effect-row state machine is re-derived in desugar, and its two diagnostics are lost

`desugar.rs:1005-1047` (`effect_row`) reads an effect row **from raw tokens**,
re-deriving: dotted-name joining, the tail-vs-effect distinction, and
scope-to-effect pairing. Its own docstring says why (`desugar.rs:1002-1004`):

```rust
/// Assembled from the TOKENS rather than read off child nodes: an effect
/// row is not a type, so the parser leaves it flat and a dotted name
/// arrives as three tokens.
```

The subject does all of this **in the parser**, and the parser is where it has
to be, because two diagnostics come out of it:

```text
subject:40250   parse-effect-names (st) (acc) (sacc) (tacc) =
subject:40256    else if is-ident (current-kind st) then parse-row-tail st acc sacc tacc
subject:40264   parse-row-tail ... cdx-row-tail-decorated (CDX1121)
subject:40275                  ... cdx-row-two-tails      (CDX1120)
subject:40287   parse-dotted-effect ... builds ONE combined Token spanning base..sub
```

Because our version lives in desugar, **CDX1120 and CDX1121 are never raised**.
`check-errors` is a graded counter (currently 0), so a program that upstream
refuses we accept. Two concrete divergences follow from the same place:

* a dotted lowercase tail (`[e.f]`): upstream diagnoses CDX1121 and then treats
  it as an **effect**; `desugar.rs:1034` sets `is_tail = true` on the first
  token's kind and never revisits it, so we make it a **tail** — a row variable
  where upstream has a concrete effect. That changes what `parameterize-type`
  mints, i.e. `next-row-id`.
* a second tail (`[e, f]`): upstream diagnoses CDX1120 and **drops** the second;
  we push both into `tail`.

I could not measure either case cleanly — my grep for `[a, b]`-shaped rows could
not distinguish an effect row from a list literal, so I am reporting these as
verified-by-code, unmeasured, and almost certainly unexercised by the corpus
(they are diagnostic paths).

The scope-pairing half **is** faithful and I want to say so: upstream pushes
`empty-scope-tok` (subject:40234) so scopes stay positional, and
`desugar.rs:1018-1019` pushes `std::mem::take(&mut scope)` (empty when absent)
for the same reason.

### 1.3 `NamedType` rebuilds a name's text from a token list, on the hottest path in the file

`desugar.rs:888-897`:

```rust
NodeKind::NamedType => TypeExpr::Named(
    self.sym_str(
        &n.tokens()
            .filter(|t| !t.kind.is_trivia())
            .map(|t| self.text(t))
            .collect::<Vec<_>>()
            .concat(),
    ),
    sp,
),
```

Our parser (`src/types.rs:120-137`) builds a `NamedType` from **exactly one
bumped token**, with one exception — a signed literal (`-2`) bumps two. The
subject's is one token, full stop (`subject:42993`:
`is NamedType (tok) -> ANamedType (make-name (token-text tok)) (token-span tok)`).

So in the overwhelmingly common case this allocates a `String` per token, a
`Vec<String>`, and a concatenated `String`, to reproduce bytes that
`self.sym(t)` (`desugar.rs:138`) interns directly from `&[u8]`. `preamble.rs`'s
module docstring counts **61,734 `a-named` nodes** in the golds, so this is not
a rare path. The file's own note at `desugar.rs:105-107` says `sym` exists
precisely because `text` is too expensive here; this arm ignores it.

### 1.4 `expr()` allocates twice per node before it dispatches

`desugar.rs:176-178`:

```rust
pub fn expr(&self, n: &Node) -> Expr {
    let kids = n.child_nodes();
    let sp = head_span(n);
```

`Node::child_nodes` (`cst.rs:229-237`) **collects into a `Vec`**, and
`Node::tokens` (`cst.rs:197-209`, which `head_span` drives) allocates a `Vec`
for its own DFS stack. Both are computed unconditionally, including for `Lit`
(which uses `span_of(t)` and never touches `kids`) and `NameRef`. `ast.rs`'s
size test counts **6,575,252 `Expr`s over the corpus**, so this is ~13M
allocations that a `match` on `n.kind` first would avoid. `children_of`
(`cst.rs:211`) is already lazy and allocation-free; several arms use it.

Same shape, smaller: `desugar.rs:209` and `desugar.rs:220` call
`b.child_nodes()` twice for the same binding; `desugar.rs:774` and
`desugar.rs:802` call `d.child_nodes()` twice for the same definition.

### 1.5 The parser already knows a pattern binding ends the `let`; desugar re-derives it with a `break`

`src/expr.rs:501-507`:

```rust
Some(Kind::LeftParen) => {
    p.bump();
    crate::pattern::paren_or_tuple(p, bcp);
    let_value(p);
    p.b.wrap_from(bcp, NodeKind::LetBinding);
    break; // a pattern binding is the last one
}
```

`desugar.rs:220-231` re-discovers this by scanning each `LetBinding` for a
pattern child and `break`ing. The behaviour is faithful — the subject makes the
same guarantee, and it makes it in the parser too
(`subject:39384 finish-let-pattern`, reached only from
`parse-let-pattern-binding`, which goes straight to `in`) — but our version is a
**silent drop**: any binding after the pattern one is discarded with no
diagnostic. The invariant lives in one file and is enforced in another, with
nothing tying them together. A distinct `NodeKind::LetPatternBinding` would make
the desugar arm a `match` instead of a scan-and-break.

---

## 2. Layering findings — what desugar knows and does not pass on

### 2.1 The `line == 0` sentinel: the two live threads, verified independently, plus a MEASURED instance of the bad case

`desugar.rs:60-62`:

```rust
fn head_span(n: &Node) -> Span {
    head_token(n).map(span_of).unwrap_or_default()
}
```

`check.rs:216-219`:

```rust
/// Upstream's `is-synthetic-span` is `span.file-id == 0`. There is one file
/// here, so the marker is the LINE: source lines are 1-based, and only a span
/// this desugarer invented has line 0.
pub fn is_synthetic(sp: crate::ast::Span) -> bool { sp.line == 0 }
```

**The thread is real, and the precise diagnosis is not the one in the brief.**
Upstream *also* collapses "synthesized" into one boolean (`file-id == 0`), so
that half is faithful. What we cannot represent at all is upstream's **third**
state, `ProvDesugared` — a span with a real location that is nonetheless not a
source node. Upstream stamps it on 8 forms (`AApplyExpr`, `AIfExpr`,
`ALetExpr`, `AMatchExpr`, `AInductionExpr`, and the `|>` rewrite). We have no
field for it, so the fact is unrepresentable, not merely unpublished.

The *other* half of the brief's claim — that the sentinel cannot distinguish
"synthesized" from "the desugarer LOST the span" — I confirmed **with a measured
instance**:

```
$ cd ~/units-u56 && for f in *.codex; do desugardump truth "$f" 2>/dev/null; done \
    | grep -c "^adef .*L0C0"
159
$ ... | grep "^adef .*L0C0" | grep -v "^adef __eq_"
adef  params 0 dtype 0 L0C0 slug BoundedExceeded
```

158 of the 159 are `__eq_<T>` — deliberately synthetic, correct. **One is not.**
Full dump of `bounded-exceeded.codex`:

```
def  walks params 1 anns 0 L166C3 slug BoundedExceeded    <- parse level
...
adef grow-loop params 3 dtype 1 L159C3 slug BoundedExceeded
adef  params 0 dtype 0 L0C0 slug BoundedExceeded          <- a GHOST definition
adef walks params 1 dtype 0 L166C3 slug BoundedExceeded   <- lost its dtype
```

Root cause, traced end to end: source line 165 is
`bounded linear walks : Integer -> Text`. `lexer.rs:256` lexes `linear` as
`Kind::LinearKeyword`. `parser.rs:371-377` only bumps
`Identifier | TypeIdentifier` as the bound class, so `linear` is left
unconsumed, `p.kind(1) == Some(Kind::Colon)` fails, no `TypeAnnotation` is
built, and the `Def` node closes empty.

The parser bug is not desugar's. **Desugar's part is that it publishes the
wreck as a plausible definition** — `desugar.rs:792-803` produces
`Def { name: Name::default(), params: [], declared_type: [], body: Error("no body"), span: Span::default() }`
and pushes it into `ch.defs`. Downstream, `is_synthetic` says "the desugarer
invented this", which is the wrong answer, and `register-all-defs` mints a fresh
variable for it (`next-id` +1). `walks` separately loses its declared type.

Blast radius today, MEASURED:

```
$ grep -rhoE "^[[:space:]]*bounded[[:space:]]+[a-z]+" *.codex | awk '{print $2}' | sort | uniq -c
      1 linear    <- the only keyword-valued bound class; 1 unit of 1,246
      1 none      <- Identifier, parses fine
      (the rest are prose: "bounded by", "bounded and", ...)
$ grep -cE "^[[:space:]]*bounded[[:space:]]+" codexcheck-subject.codex
3   (all three are prose: lines 5226, 14571, 59345)
```

**No graded counter moves.** The self-host has no `bounded` declaration.

**What each layer should have said.** Two separate facts want two separate
carriers, and only one of them is a span:

1. *"this node has no source location"* — keep `Span::default()`, but make it
   say so by construction. Add `Provenance` to `ast::Span` (the subject's own
   three values) and have `is_synthetic` read it instead of inferring from
   `line`. That makes `line == 0` no longer load-bearing and unblocks
   `ProvDesugared`.
2. *"the CST gave me nothing where a name was required"* — that is not a span
   fact at all. `desugar.rs:61`, `135`, `165`, `171`, `316`, `745`, `793`,
   `798`, `911`, `966` all end in `.unwrap_or_default()`. Each is a place where
   the desugarer, uniquely in the pipeline, can see that the CST is malformed.
   It should raise a diagnostic (the subject raises them freely at this layer —
   `desugar-type-expr-at` emits `_fuel`, `desugar-literal` emits `AErrorExpr`)
   rather than emitting a default and letting a later layer guess.

### 2.2 `check.rs:1083 flatten_app` — NOT a finding, and here is the line that makes it faithful

I looked at this closely because the brief flagged it, and I disagree with the
diagnosis. `check.rs:1083`'s `flatten_app` is over `ast::TypeExpr::App`, not
`Expr::Apply`. **The subject has the identical function, at the same layer, for
the same reason:**

```text
subject:51840   FlatAppResult = record { ctor : ATypeExpr, args : List ATypeExpr }
subject:51843   flatten-app (expr) (outer-args) =
subject:51845    is AAppType (ctor) (args) (s) -> flatten-app ctor (args & outer-args)
subject:51893   is AAppType (ctor) (args) (s) -> ... check-arity-in-expr
```

and the node it flattens has the same shape as ours:

```text
subject:42143    | AAppType (ATypeExpr) (List ATypeExpr) (SourceSpan)
```

The `Vec` really is arity-dishonest — `desugar.rs:900-904` (`AppType`) and
`desugar.rs:983` (`TupleType`) fold to nested `App`s each carrying a 1-element
`Vec`, while `desugar.rs:912-916` (`ArithType`) builds one `App` with a
2-element `Vec` — but **upstream's `List ATypeExpr` has exactly the same two
producers**:

```text
subject:40325   parse-type-args (deck-record (AppType base-type [arg])) st        -- 1 element
subject:39970   AppType (NamedType op-tok) [left, right]                          -- 2 elements
subject:43032   apply-atype-args (AAppType base [list-at elems i] synthetic-span) -- 1 element
```

Changing the node shape here would diverge from the file we grade against.
I verified the ordering too: upstream's `args & outer-args` (innermost-first
append) and our `args.extend(a.iter().rev()); ...; args.reverse()` produce the
same left-to-right list. **Non-finding, closed.**

There is one small ours-only detail worth keeping: our `AppType` arm folds
because *our parser leaves the args flat under one node* where upstream's parser
already nests them. `preamble.rs:179-181` says so and does the identical fold.
The resulting AST is the same shape. Fine.

### 2.3 `deriving Eq` is parsed, dropped at the AST boundary, and the docstring blames the wrong layer — MEASURED

`desugar.rs:645-647`:

```rust
/// `deriving Show` and `deriving Ord` synthesise two more. Those are NOT
/// here: our parser does not capture the `deriving` clause at all, so they
/// need a parser change first. Fifteen files in the depot carry one.
```

**That sentence is false.** I read the code:

* `src/cst.rs:110-111` declares `NodeKind::Deriving` (`/// deriving Show, Eq, Ord`).
* `src/typedef.rs:283-300` (`fn deriving`) parses it and wraps a node, and
  `typedef.rs:58` calls it. There is a passing test at `typedef.rs:366`.
* `grep -rn "Deriving" src/` outside `typedef.rs`/`cst.rs` returns **one hit,
  and it is prose in a `preamble.rs` comment.** Nothing reads the node.

The fact reaches the CST and dies at the AST boundary: `ast::TypeDef` has no
`deriving` field. `synth_derived_defs` (`desugar.rs:648-660`) therefore fires on
self-recursion alone:

```rust
let TypeDef::Variant(name, _, ctors, _) = td else { continue };
let names_itself = ctors.iter().any(|c| c.fields.iter().any(|f| type_names(f, *name)));
if names_itself { out.push(self.eq_def(*name, ctors)); }
```

The subject's condition is a **disjunction**, and its generator handles records
and unit types as well as variants:

```text
subject:43350   let acc2 = if deriving-has (td.deriving) "Eq" | td-self-recursive td
                           then __linked-list-push acc1 (gen-eq-def td) else acc1
subject:43353   td-self-recursive (td) = when td.body
subject:43355    is VariantBody (ctors) -> ctors-name-type ...
subject:43356    is otherwise -> False
subject:43509   gen-eq-body (body) (xn) (yn) = when body
subject:43511    is VariantBody (ctors) -> ...
subject:43512    is RecordBody (fields) -> gen-eq-record ...
subject:43513    is UnitBody (base) -> ABinaryExpr (ANameExpr xn) OpEq (ANameExpr yn)
```

MEASURED, on the corpus:

```
$ grep -rn "deriving Eq\|deriving Show, Ord" ~/units-u56/*.codex | grep -v prose-words
deriving-eq-recursive.codex:151:    deriving Eq
typeclass-smoke.codex:169:  Color = | Red | Green | Blue  deriving Show, Eq, Ord
typeclass-smoke.codex:174:    deriving Show, Ord
typeclass-smoke.codex:176:  Wrap = | Wrap (Integer)  deriving Eq
typeclass-smoke.codex:178:  Point = record { x : Integer, y : Integer }  deriving Eq

$ desugardump truth typeclass-smoke.codex | grep -E "^a-defs|^adef __eq"
a-defs 31
   (no __eq_ lines at all)

$ desugardump truth deriving-eq-recursive.codex | grep -E "^adef __eq"
adef __eq_Tree params 2 dtype 1 L0C0 slug
```

So `typeclass-smoke.codex` is short **at least three** definitions upstream
synthesizes (`__eq_Color`, `__eq_Wrap`, `__eq_Point`) — exactly the failure the
same docstring warns about at `desugar.rs:641-643`: *"a chapter missing it
reports a smaller `next-id` than upstream for the same source and can emit a
`(defs ...)` short of a definition."*

The docstring's real damage is that it points the next person at the parser. The
parser is done. What is missing is a `deriving: Vec<Name>` on `ast::TypeDef` and
a disjunct at `desugar.rs:655`.

### 2.4 `with timeout` re-implements the effect row naively, three functions above the fixed version

`desugar.rs:399-422`:

```rust
NodeKind::WithTimeout => {
    ...
    let effs: Vec<Name> = n
        .children_of(NodeKind::EffectRow)
        .flat_map(|r| r.tokens())
        .filter(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
        .map(|t| self.sym(t))
        .collect();
    Expr::WithTimeout(Box::new(WithTimeoutExpr {
        timeout, effects: effs,
        labels: Vec::new(),
        ...
```

This is verbatim the bug that `effect_row`'s own docstring (`desugar.rs:969-975`)
records as fixed:

> **A DOTTED EFFECT IS ONE NAME AND A SCOPE BELONGS TO THE EFFECT IT FOLLOWS.**
> ... Taking the identifiers alone made `Device.Block` two effects and dropped
> every scope in the depot

The fix was applied at `desugar.rs:976-979` (`NodeKind::EffectType`) and not
here. Consequences: `FileSystem.Read` becomes two effects; a lowercase row tail
becomes an effect; and `labels` — which is upstream's **scopes** list
(`subject:42745`: `AWithTimeoutExpr (token-text timeout-tok) (map-list
make-type-param-name effs) (map-list extract-scope-text scopes) body span`) — is
hard-coded empty, so every `with timeout` scope in the source is destroyed.
`ast.rs:154-156` documents `labels` as "Always empty today: nothing constructs
it and nothing reads it. Kept because the upstream node has it" — which
describes the symptom, not that desugar is the layer discarding the input.

MEASURED — this is currently unreachable:

```
$ grep -rc "with timeout" ~/units-u56/*.codex | awk -F: '$2>0' | wc -l
0
```

but dotted effects with scopes are common in the corpus, so the bug is one
`with timeout` away:

```
$ grep -rhoE '\[[A-Z][A-Za-z.]* "[^"]*"' ~/units-u56/*.codex | sort -u | head -6
[Console "auth"
[Console "stdout"
[Console.Write "stdout"
[FileSystem.Read "/config/"
[Network.Read "api.example.com"
```

### 2.5 The class constraint is thrown away, and `TypeExpr::Constrained` has no producer

`desugar.rs:956`:

```rust
NodeKind::ConstrainedType => first(kids.len().saturating_sub(1)),
```

`src/types.rs:327-331` parses `Showable a => a -> Text` into a
`ConstrainedType` node holding both halves. Desugar keeps the body and drops the
constraint. `grep -rn "TypeExpr::Constrained" src/` shows **no construction
site** — only three consumers matching a variant nothing produces
(`desugar.rs:1099`, `xref.rs:127`, `interp.rs:3426`). That is a dead arm in
three files pretending a fact is carried.

The subject builds the node and **three passes read it**:

```text
subject:43042   is NamedType (var-tok) -> AConstrainedType (make-name (token-text class-tok))
                                                            (make-name (token-text var-tok)) body synthetic-span
subject:43720   is AConstrainedType (class-name) (type-var) (body-type) (sp) ->   (dict type synthesis)
subject:43943   is AConstrainedType (cn) (cv) (b) (s) -> ... chapter-has-constraint
subject:44009   is AConstrainedType (class-name) (type-var) (body-type) (sp) ->   (rewrite-constrained-defs)
```

`chapter()`'s docstring (`desugar.rs:561-565`) already says
`rewrite-constrained-defs` and `insert-dicts-at-call-sites` are not implemented.
Fair. But there is a difference between *not running a pass* and *destroying the
pass's input*, and this is the second. When someone implements it they will
have to go back to the CST.

**No graded counter moves today**, and this is why: the constraint is
transparent in IR emission upstream too — `subject:57545`:
`is AConstrainedType (cn) (cv) (body) (s) -> ir-emit-atype-expr body` — which
`preamble.rs:233-235` already mirrors independently.

### 2.6 The `punctual` budget is read by `preamble.rs` off the CST because desugar publishes only the name

`desugar.rs:621-625`:

```rust
for d in tree.descendants(NodeKind::Def) {
    if d.children_of(NodeKind::Punctual).next().is_some() {
        ch.rt_names.push(self.str_of(self.def_name(d)));
    }
}
```

The parser bumps the budget into the `Punctual` node (`parser.rs:377-385`:
`if p.kind(0) == Some(Kind::IntegerLiteral) { p.bump(); }`), and the IR needs it
— `preamble.rs:488-508` emits
`(ann "hard-realtime" <name> <budget>)`. Because desugar publishes only
`rt_names`, `preamble.rs` re-derives **both** name and budget from the CST.
`ast::Chapter::rt_budgets` (`ast.rs:383`) is the field that was meant to carry
it: `grep -rn "rt_budgets" src/` finds **the declaration and nothing else** —
never written, never read.

Meanwhile `rt_names` itself is read by exactly one thing:
`desugardump.rs:109`, a count. So this loop — a full-tree `descendants()` walk —
produces a number for a dump row and nothing else.

Note also that it walks `tree.descendants(NodeKind::Def)` while `ch.defs` is
built from `tree.child_nodes()` (`desugar.rs:571`). Two different populations
from one tree; today they agree only because `Def` does not nest.

### 2.7 `CitesDecl` is published two-thirds empty, and `bundle.rs` re-derives the missing part by string-matching a token

`desugar.rs:606-612`:

```rust
NodeKind::Cites => ch.citations.push(CitesDecl {
    quire: self.name_of(child),
    chapter_name: Name::default(),
    selected_names: Vec::new(),
    citing_chapter: slug.clone(),
    span: head_span(child),
}),
```

Both empty fields are present in the CST. `bundle.rs:260-285` reconstructs them:

```rust
let Some(kw) = toks.iter().position(|t| word(t) == "chapter") else { continue };
let (Some(quire), true) = (toks.get(kw - 1), kw >= 1) else { continue };
...
let name = String::from_utf8_lossy(&src[from..to]).trim().to_string();
```

— finding the keyword by **comparing a token's text to `"chapter"`**, then
slicing raw source between two offsets. Its own test comments record how hard
this is (`bundle.rs:540`: *"The word `cites` is ordinary English and these
chapters are mostly prose"*; `bundle.rs:549`: *"`Build Settings` is one chapter
with a space in its name"*). All of that difficulty is real; none of it needed
to happen twice.

`selected_names` — the `(max-errors, max-emit-work)` list — is dropped by both,
and `bundle.rs:274` explicitly stops at `(`.

Two seam notes while I was there, neither in my target file:
`bundle.rs:268` evaluates `toks.get(kw - 1)` **before** the `kw >= 1` guard in
the same tuple pattern, so `kw == 0` underflows; and `bundle.rs:261` re-parses
the source from scratch.

### 2.8 Five `Chapter` fields can only ever report zero

`grep -rn` for each field outside `ast.rs`:

| field | written by | read by |
|---|---|---|
| `section_titles` | `desugar.rs:579` | `desugardump.rs:104-106` (count + names) |
| `ground_effects` | `desugar.rs:615` | `desugardump.rs:101` (count only) |
| `rt_names` | `desugar.rs:623` | `desugardump.rs:109` (count only) |
| `prose` | — | `desugardump.rs:81` |
| `prose_blocks` | — | `desugardump.rs:102` |
| `annotations` | — | `desugardump.rs:103` |
| `conversions` | — | `desugardump.rs:110` |
| `rt_budgets` | — | — |

`desugardump truth` is the ladder's graded `desugar.truth`, so the first three
are legitimately load-bearing — I am not calling them dead. The last five are:
four rows of a graded truth that are structurally incapable of being anything
but `0`, which is the "green because it never ran" shape. They should either be
filled or removed from the truth, so the row means something.

Separately, `ground_effects` encodes a pair as `format!("{slug}\n{name}")`
(`desugar.rs:615`) — a two-field record spelled as a newline-delimited string
that nothing ever splits.

---

## 3. Ordinary smells and divergences from the subject

### 3.1 `leading()` admits a layout token — the exact bug `field_after_dot` was fixed for

Three near-identical name-extractors with three different filters:

```rust
desugar.rs:56    head_token:      !t.kind.is_trivia() && !t.kind.is_layout()
desugar.rs:171   leading:         !t.kind.is_trivia()                        <-- weaker
desugar.rs:163   name_of:         matches!(t.kind, Identifier | TypeIdentifier)
desugar.rs:130   field_after_dot: skip to Dot, then !t.kind.is_trivia()
```

`is_trivia` is `Spaces | SkippedProse | Unmapped` (`token.rs:129-131`);
`is_layout` is `Newline | Indent | Dedent` (`token.rs:143-145`). So `leading`
can return a **Newline** — which is precisely what `field_after_dot`'s own
docstring (`desugar.rs:111-124`) records as a silent, long-lived bug:

> **THIS WAS `.last()` OF THE NON-DOT TOKENS AND IT WAS WRONG, silently.**
> A newline is NOT trivia in Codex ... `.last()` took a NEWLINE as the field's
> name. The record then grew a second field whose name was "\n"

`leading` is used for ten things (`desugar.rs:184, 271, 274, 285, 293, 441, 451,
809, 835, 849, 1054, 1060`) including every record field name, every constructor
name and every effect-op name — the same population as the bug that was fixed.
Nothing forbids a node from owning a leading newline; the parser attaches
newlines liberally (`skip_newlines` inside open nodes). I did **not** measure an
active occurrence — the 28 curated subjects are byte-identical, so the record
fields there are fine. It is a live fragility with a known precedent, and the
one-word fix is to make `leading` call `head_token`.

The same class covers `name_of` (`desugar.rs:161-166`), which searches
`n.tokens()` — **all descendants**, not `own_tokens()`. When the intended name
token is absent it silently takes the first identifier out of the *value*
expression. It is used for `EffectDef`/`ClassDef`/`InstanceDef` names,
`ActBind` names and `Cites` quires.

### 3.2 `NodeKind::Selector` desugars to a name that is the dot

`desugar.rs:184`:

```rust
NodeKind::Name | NodeKind::Selector => Expr::NameRef(self.leading(n), sp),
```

`expr.rs:358-364` builds a `Selector` from `[Dot, fieldname]`. `Kind::Dot` is
not trivia, so `leading` returns `sym(".")` and the field name is dropped
entirely. `field_after_dot` — three functions up, written for exactly this — is
not used.

MEASURED, unreachable today:

```
$ grep -rn "^[[:space:]]*\.[a-zA-Z_]" ~/units-u56/*.codex | wc -l
22          # all 22 are prose: ".NET at quality eleven", ".NET's own output"
$ grep -cn "^[[:space:]]*\.[a-zA-Z_]" codexcheck-subject.codex
0
```

So no counter is at risk. It is still a wrong answer sitting in the dispatch
table, and `Name` and `Selector` sharing an arm is what hides it.

### 3.3 Two integer decoders in one file, and the wrong one is used for `trying N times`

`desugar.rs:347-352`:

```rust
NodeKind::TryExpr => {
    let count = n
        .own_tokens()
        .find(|t| t.kind == Kind::IntegerLiteral)
        .and_then(|t| self.text(t).parse().ok())
        .unwrap_or(0);
```

Ninety lines below, `BoundedIntType` (`desugar.rs:924-935`) carries a long
comment about why `parse()` is the wrong tool here and uses
`crate::token::lit_text_to_integer` instead. `lit_text_to_integer`
(`token.rs:281-299`) handles `#`-hex and `_` separators and wraps; `parse::<i64>`
handles neither and `unwrap_or(0)` then produces a **wrong-but-plausible zero**.

The subject uses the same decoder in both places:

```text
subject:42743   is TryExpr (count-tok) ... -> ATryExpr (lit-text-to-integer (token-text count-tok)) ...
```

MEASURED — currently masked, every corpus `trying` count is a bare small decimal:

```
$ grep -rhon "trying[[:space:]]*[0-9#_][0-9a-fA-F#_]*" ~/units-u56/*.codex | sed 's/.*trying//' | sort | uniq -c
      2  3
      2  1
      1  2
```

`trying 1_000 times` or `trying #10 times` silently becomes `trying 0 times`.

### 3.4 `literal_kind`'s fallback is `IntLit`; the subject's is `TextLit`

`desugar.rs:1140-1148`:

```rust
fn literal_kind(k: Kind) -> LiteralKind {
    match k {
        Kind::NumberLiteral => LiteralKind::NumLit,
        Kind::TextLiteral => LiteralKind::TextLit,
        Kind::CharLiteral => LiteralKind::CharLit,
        Kind::TrueKeyword | Kind::FalseKeyword => LiteralKind::BoolLit,
        _ => LiteralKind::IntLit,
    }
}
```

```text
subject:42811   classify-literal (k) = when k
subject:42814    is IntegerLiteral -> IntLit
subject:42815    is NumberLiteral -> NumLit
...
subject:42819    is otherwise -> TextLit
```

Two differences. (a) `IntegerLiteral` is folded into the catch-all, so any token
kind added to the lexer later silently classifies as an integer literal. (b) The
fallback value itself diverges.

`literal_kind` has two callers. The `Lit` one (`desugar.rs:181`) is guarded by
the parser's `is_literal` check (`expr.rs:308`). The **`LitPat` one is not**
(`desugar.rs:1055-1057`), and neither is upstream's
(`subject:42974: is LitPat (tok) -> ALitPat ... (classify-literal (tok.kind))`),
so this is the arm where the divergence is reachable.

Relatedly, `desugar.rs:180-183` has no `is-literal` guard where upstream does:
`subject:42808: if is-literal (tok.kind) then ALitExpr ... else AErrorExpr (token-text tok) (token-span tok)`.
We would emit a `Lit` where upstream emits an error node.

### 3.5 `unary` returns the operand unnegated when the operator token is missing; `binary` returns an error for the same condition

```rust
desugar.rs:470   let Some(op) = op_tok else { return Expr::Error("bin".into(), sp) };
desugar.rs:486   let Some(op) = op else { return inner };
```

Same condition, fifteen lines apart, two different answers, and the `unary` one
is the silently-wrong-but-plausible kind: `-x` becomes `x`. Neither case exists
in the subject (its parser always has the token), so `Expr::Error` is the honest
answer for both.

### 3.6 `trim_matches('"')` is not `extract-scope-text`

`desugar.rs:1029-1032`:

```rust
Kind::TextLiteral => {
    let raw = String::from_utf8_lossy(t.text(self.src)).to_string();
    scope = raw.trim_matches('"').to_string();
}
```

```text
subject:42840   extract-scope-text (tok) =
subject:42842    in if len >= 2 then substring raw 1 (len - 2) else ""
```

`trim_matches` strips *every* leading and trailing `"`, not one of each. For a
scope literal ending in an escaped quote — `"say \"hi\""` — upstream yields
`say \"hi\"` and we yield `say \"hi\` , one character short. Also `""` (the
empty scope) becomes the empty string under both, by luck rather than by the
same rule. I found no corpus instance; it is a one-line divergence with a
concrete wrong output.

### 3.7 `InstanceDef` is pushed with two fields permanently blank

`desugar.rs:600-605` pushes `InstanceDef { class_name, type_name: Name::default(),
methods: Vec::new(), span }`. `chapter()`'s docstring says instance synthesis is
not implemented — but the *declaration's* type name and method list are in the
CST, and the struct's shape claims to carry them. Either fill them or make the
type say what it holds.

### 3.8 `chapter()` is the only `&mut self` method, for one `String` field

`Desugar` uses a `RefCell<SymTab>` (`desugar.rs:47`) so that everything can take
`&self` — then `chapter` takes `&mut self` anyway (`desugar.rs:566`) solely to
set `self.slug` (`desugar.rs:582`), which is read once, in `def` (`desugar.rs:797`).
Passing the slug as a parameter to `def` removes the field, the `&mut`, and the
`slug: String::new()` in `new` (`desugar.rs:66`).

---

## 4. Comment findings (secondary)

### 4.1 `head_token`'s docstring asserts an invariant the subject contradicts, and it is the comment that licenses the file's span policy

`desugar.rs:54-55`:

```rust
/// The first real token under a node -- every AST span upstream builds is
/// `token-span` of some token this node holds.
```

**I read the subject rather than trusting this.** It is false for at least nine
forms. Upstream's `AIfExpr` span is the *condition's* span, `ALetExpr`'s is the
*body's*, `AMatchExpr`/`AInductionExpr`'s is the *scrutinee's*, and Tuple,
Revised, Lazy and the `for` rewrite use `synthetic-span`, which is no token at
all:

```text
subject:42727   is IfExpr (c) (t) (e) -> AIfExpr dc ... (desugared-span (aexpr-span dc))
subject:42730   is LetExpr (bindings) (body) -> ALetExpr ... db (desugared-span (aexpr-span db))
subject:42733   is MatchExpr (scrut) (arms) -> AMatchExpr ds ... (desugared-span (aexpr-span ds))
subject:42738   is TupleExpr (elems) -> apply-aexpr-args (ANameExpr ... synthetic-span) ...
subject:42761   is LazyExpr (inner) -> ALazyExpr ... synthetic-span
```

This matters because `let sp = head_span(n)` at `desugar.rs:178` is then used as
the span for roughly fourteen expression forms, and this comment is the only
thing that says that is right. It is not right; it is *harmless*, for a reason
worth writing down instead (see the non-finding in §5.1).

### 4.2 A docstring belonging to `sym` is glued onto `field_after_dot`

`desugar.rs:105-129`:

```rust
    /// A token's text as an interned name. This is the one that runs 6.19
    /// million times over the corpus; `text` above still serves the places
    /// that want an owned string, which is literals and chapter metadata.
    /// The field named by a `.field` access or a `.field = v` assignment: the
    /// first non-trivia token AFTER the dot.
    ///
    /// **THIS WAS `.last()` OF THE NON-DOT TOKENS AND IT WAS WRONG, silently.**
    ...
    fn field_after_dot(&self, n: &Node) -> Name {
```

The first three lines describe `sym`, not `field_after_dot`. `sym`
(`desugar.rs:138`) has no docstring at all. A merge left the paragraph behind.

### 4.3 "the fourteen `&self` methods below" — MEASURED stale

`desugar.rs:42`. There are **22**:

```
$ grep -c "fn .*(&self" src/desugar.rs
22
```

### 4.4 "our parser does not capture the `deriving` clause at all" — stale and actively misleading

`desugar.rs:646`. Covered in §2.3: the parser captures it
(`typedef.rs:283-300`, `cst.rs:110`), and this sentence sends the reader to the
wrong layer.

### 4.5 Module-header drift between `desugar.rs` and `ast.rs`

`desugar.rs:3` says "Seven forms are REWRITTEN" and lists seven.
`ast.rs:193-199` says "**Six** of the parse tree's forms have no node here at
all" and lists six (it omits the `s in rest` -> `__seq` rewrite). One of the two
is wrong, and both are the kind of count that will drift again.

### 4.6 Comments I checked and found accurate — worth not re-litigating

* `desugar.rs:1080-1085` (`NO_ALT_GROUP`): *"Nothing reads the field today."*
  Verified: `grep -rn "alt_group" src/` outside `desugar.rs`/`ast.rs` returns
  nothing. The `u32::MAX`-vs-upstream's-`-1` rationale is load-bearing and correct.
* `desugar.rs:672-675` (`eq_def`'s "THE LIVE TABLE, NOT THE CHAPTER'S"):
  verified against `desugar.rs:631` (`std::mem::take`). Correct and non-obvious.
* `desugar.rs:459-463` and `desugar.rs:1150-1158` (the newline-read-as-`&`
  story): the fix is present at `desugar.rs:465` and `binary_op` really has no
  fallback. Load-bearing, keep.
* `desugar.rs:924-933` (`parse()` cannot read `i64::MIN`): correct, and there is
  a regression test at `desugar.rs:1227-1258`.

---

## 5. Non-findings — considered and rejected, with the upstream line

These are things that look wrong and are not. Each cost me time; the point of
listing them is that they should not cost the next reader any.

**5.1 `sp = head_span(n)` used as a blanket span for ~14 expression forms.**
It diverges from the subject (§4.1) but **cannot move a graded counter**, and
here is why I am confident. Our checker records an expression type at exactly
five sites (`check.rs:1738, 1762, 1958, 2003, 2107`): record type, `&`-binary,
*empty* list, lambda, record literal. `Apply`, `Let`, `If`, `Match` and
`Induction` — every form whose span we compute differently — record nothing.
And `record-expr-type` pushes unconditionally (`subject:46136`, a `list-push`,
no dedup), so the counter is the number of non-synthetic *calls*, not the number
of distinct keys. The span *value* therefore never reaches `expr-types`. The
four forms that do record all match upstream's rule exactly: `&` uses the
operator token both sides; a record literal uses its type token both sides; the
empty list uses the list's own span both sides; and the lambda uses `\` /
`token-span lam-tok`. Writer and reader both read the same `ast::Span`, so
`lookup-expr-type` stays self-consistent. Latent, not live.

**5.2 The `for` comprehension's `Span::default()` everywhere.**
`desugar.rs:319-329` gives the lambda, the `map-list` name and both applications
a default (i.e. synthetic) span, which looks like sloppiness. It is exact:

```text
subject:42765    in let lam = ALambdaExpr [make-name (token-text var-tok)] dbody synthetic-span
subject:42766    in let map-fn = ANameExpr (make-name "map-list") synthetic-span
subject:42767    in AApplyExpr (AApplyExpr map-fn lam synthetic-span) dlist synthetic-span
```

This is load-bearing for `expr-types`: a lambda **does** record
(`check.rs:2003`), so a real span here would over-count by one per comprehension.

**5.3 `Expr::Lazy(..., Span::default())` (`desugar.rs:423-426`).**
Every sibling arm uses `sp`; this one does not. Faithful:
`subject:42761: is LazyExpr (inner) -> ALazyExpr (desugar-expr-at inner ...) synthetic-span`.

**5.4 `MkTupN` / `Tup{N}` built by string formatting (`desugar.rs:307, 982, 1070`).**
Looks like name-by-concatenation. It is the subject's own construction:
`subject:42738` (`"MkTup" & integer-to-text (list-length elems)`),
`subject:43030` (`"Tup" & integer-to-text n`), `subject:42980` (the pattern).

**5.5 `Expr::Error(self.str_of(self.leading(n)), sp)` for `ErrExpr` (`desugar.rs:451`)** —
an error message taken from a token's text. Faithful:
`subject:42768: is ErrExpr (tok) -> AErrorExpr (token-text tok) (token-span tok)`.

**5.6 The effect-row scope is stored raw, not run through `literal_value`.**
`literal_value`'s docstring (`desugar.rs:76-79`) says it is *"THE ONE PLACE A
LITERAL IS DECODED"*, so the raw scope looked like a second decoder. It is not:
`extract-scope-text` (`subject:42840-42843`) is a plain `substring` and never
calls `decode-escapes`. Only the quote-stripping *method* diverges (§3.6).

**5.7 `alt_group` from the first pattern's offset (`desugar.rs:542`).**
Exactly upstream: `subject:39541: alt-group = pat-offset (list-at pats 0)`,
`subject:39386: alt-group = pat-offset pat`. And the pattern-let arm's
`guard: Expr::Lit("True", BoolLit, Span::default())` matches
`make-true-guard st`.

**5.8 Derived `__eq_` definitions carry `chapter_slug: String::new()`
(`desugar.rs:733`).** Faithful: `subject:43499: chapter-slug = ""`.

**5.9 `preamble.rs` duplicating `type_expr`'s `BoundedIntType`, `ArithType`,
`TupleType` and `AppType` logic.** It looks like the same rule written twice.
It is a **deliberate independent arm** — `preamble.rs:16-18`: *"This is the only
whole-corpus oracle that exists before the type checker"* — and the subtle half
(`lit_text_to_integer` plus minus-detection) is already shared via
`crate::token`. Not a finding; noting it so nobody "de-duplicates" the oracle.

**5.10 `Kind::ForKeyword` declared and never produced.** Dead, but the subject
has the identical corpse: `subject:38607: is-for-keyword (k) = when k is
ForKeyword -> True`, with no caller. A faithful port of a dead branch.

**5.11 `TypeExpr::App`'s `Vec` and `check.rs:flatten_app`.** §2.2. Faithful,
closed.

**5.12 `Expr::Apply` being binary and un-curried in `arity.rs:165` /
`code.rs:211`.** `AApplyExpr` is binary upstream too (`subject:42711`) and
upstream walks its own spines. Currying is the AST, not an artefact.

---

## 6. What I would fix first, ranked

1. **`deriving Eq` (§2.3).** MEASURED missing definitions in a corpus unit, and
   `next-id` is a graded counter. The parser work is done; this is a
   `deriving: Vec<Name>` field on `ast::TypeDef`, a disjunct at
   `desugar.rs:655`, and record/unit arms in `eq_def`. **Delete the false
   sentence at `desugar.rs:646` in the same commit** — it is what would stop
   the next person from finding this.

2. **The `bounded linear` ghost definition (§2.1).** MEASURED, one corpus unit,
   two defects: the parser's bound-class arm should accept a keyword-kinded
   class word (`parser.rs:373`), and desugar should refuse a nameless `Def`
   rather than publishing one. Do the parser half first; the ghost disappears
   with it.

3. **Add `Provenance` to `ast::Span` and make `check.rs::is_synthetic` read it
   (§2.1).** Removes the `line == 0` inference, unblocks `ProvDesugared`, and
   makes the ~10 `.unwrap_or_default()` sites in this file distinguishable from
   deliberate synthesis. Purely additive: today's behaviour is
   `Provenance::Parsed` for anything with a token and `Synthetic` for
   `Span::default()`. **Nothing on the wire moves** — see §5.1 for why.

4. **`for`'s loop variable (§1.1).** Highest ratio of clarity to risk in the
   file. Either the parser wraps it or desugar reads to `InKeyword`; either way
   a `for` disappears from a string comparison.

5. **Fold `WithTimeout` onto `effect_row` and carry the scopes into `labels`
   (§2.4).** Deletes a known-bad copy of logic that was already fixed once,
   three functions away. Unreachable today (0 `with timeout` in the corpus), so
   it is free.

6. **`leading` -> `head_token` (§3.1), and `Selector` -> `field_after_dot`
   (§3.2).** Two one-line changes closing a documented class of bug. Both
   unreachable in today's corpus, both wrong.

7. **`TryExpr`'s `parse()` -> `lit_text_to_integer` (§3.3), `literal_kind`'s
   fallback -> `TextLit` with `IntegerLiteral` listed explicitly (§3.4),
   `unary`'s missing-operator path -> `Expr::Error` (§3.5), `trim_matches` ->
   a one-quote strip (§3.6).** Four independent one-liners, each a divergence
   from a subject line quoted above, none reachable today.

8. **Hoist `child_nodes()`/`head_span()` behind the `match` in `expr()`
   (§1.4), and special-case the single-token `NamedType` (§1.3).** Pure
   allocation removal on the two hottest paths; no behaviour change. Worth a
   benchmark before and after rather than an assertion — I did not measure it.

9. **Housekeeping:** move the misplaced `sym` docstring (§4.2), fix "fourteen"
   (§4.3), delete or fill `rt_budgets`/`conversions`/`prose`/`prose_blocks`/
   `annotations` so their truth rows mean something (§2.8), turn
   `ground_effects` into a real pair (§2.8), and drop `chapter`'s `&mut self`
   (§3.8).

Not ranked, because they are gaps rather than defects and the file already says
so: the constraint drop (§2.5) and the `CitesDecl` blanks (§2.7). Both are worth
recording as *"desugar destroys the input"* rather than *"the pass is not
written"*, because that is the sentence that tells the next implementer where to
start.
