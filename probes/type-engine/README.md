# Type-engine discovery probes

Minimal Codex programs that pressure the checker's type engine, each with an
unarguable answer, run through two oracles:

- **value:** `codexrun` (our interpreter, type-erasing).
- **type:** `irdump whole <prog> | zigemit | zig build-exe` — our IR through the
  zig plug, which refuses a hole.

Each break is attributed against `~/codexzig` (upstream frontend + plug): a
break upstream shares is a Codex-wide frontier, not our regression.

## The probes and what each establishes

- **01-sum-baseline** — `Nat`/`when..is`, `Maybe`, recursive `MyList`, summed
  and printed. Constructor typing, pattern-binding types, branch unification,
  recursive data. All three arms agree. The floor: sums and pattern matching
  are sound.

- **02-orphan-sum-ahead** — `is-some None`. The orphan `Maybe a` is never
  observed at a type. Our zonk-and-default resolves its element to int-default,
  so our IR is hole-free and the zig plug accepts it (`False`). **Upstream
  leaves the variable free and its plug refuses it** ("type variable T11 is not
  declared"). Our IR is the reference here; locked as `ir.rs`
  `an_orphan_sum_constructors_parameter_defaults` (and the nested `Some None`).

- **03-undeclared-poly** — `my-id (x) = x`, used at Integer AND Text. The
  interpreter prints `7`/`hello` — the answer of the generic typing that a full
  HM would infer. We have no generalization, so zonk-and-default pins `my-id` to
  `int-default -> int-default`; the Text use is then un-compilable and **our
  checker does not complain**. Upstream rejects at check (CDX2001). Two honest
  answers exist (generalize, or reject); we do neither. The generalization
  frontier (curriculum phase 3).

- **04-inline-return-orphan** — `make-empty : Integer -> List a; make-empty (n)
  = []`, used as `list-length (make-empty 0)`. `make-empty`'s `a` is a genuine
  generic where DEFINED (its zonk protects it), an orphan where USED. Inlining
  (`ir_passes.rs` `once_retype`) recovers type variables only by matching
  parameters to arguments — `a` is in the return type, in no parameter, so it is
  carried into the caller as a free var, and inlining runs AFTER check's
  zonk-and-default so nothing defaults it. Both arms fail — a shared frontier.
  (Pinning from outside, `list-push (unwrap (make-empty 0)) 5`, does not reach
  the inlined body either.)

- **05-nonfatal-unify** — `n + "hello"`. Our checker emits IR; the interpreter
  catches it at runtime and the zig plug at build. **Upstream rejects at check**
  (CDX2001). The checker treats every unification failure as its own ignorance
  (`check.rs`: "a `false` out of a partial unifier is our ignorance and not the
  program's fault"), counting `unify_gaps`, never raising an error — because it
  grew against the self-host corpus, which is entirely well-typed. A conflict
  between two FULLY CONCRETE types (Integer vs Text) is not ignorance; it is a
  CDX2001 the program earned. Being the reference means rejecting ill-typed
  programs, so this distinction is the next design step.

## The three phases, seen through the probes

- **phase 1, zonk-and-default:** 02 shows it working and ahead of upstream; 04
  shows its blind spot — vars injected after check (by inlining) are never
  defaulted.
- **phase 2, bidirectional check:** 04's pinned variant wants the expected type
  to flow down into an inlined body.
- **phase 3, generalization:** 03 is the case; without it, an undeclared
  polymorphic definition is either mis-defaulted or (better) should be rejected.

Cross-cutting: 03, 05 (and 04's malformed cousins) all trace to the checker's
non-fatal unification. Making a concrete-vs-concrete conflict a reported error
is the single change that most moves us toward "the reference for well-typed
IR."
