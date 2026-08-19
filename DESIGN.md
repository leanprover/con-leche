# Setlec — a verified Lean checker

Setlec is a checker for Lean declarations, implemented in Lean, verified in
Lean. The goal is a checker that is performance-competitive with lean4lean or
even the official kernel, together with a machine-checked consistency proof:

> For everything the checker accepts there is a model in a suitable set
> theory. In particular, no declaration of type `Empty` is ever accepted.

This document records the design decisions. It was distilled from the initial
project prompt and is updated as decisions evolve.

**Project goal** (set 2026-08-19): the lean kernel arena *tutorial* tests
(except those involving custom axioms) are accepted by the checker, and the
checker is verified to be consistent.

## The model

* The target theory is **Tarski–Grothendieck set theory**. Inside Lean it is
  expressed as an interface (`Setlec.SetTheory`), a class over a universe
  type `V`; all verification is parametric in a model of that interface, which
  serves as the "extra assumption for cardinality reasons". Constructing an
  instance from `ZFSet`-style machinery (cf.
  https://github.com/digama0/lean4lean-model, `Consistency.lean`) can be done
  separately. The interface only grows on demand, so it stays evident what the
  consistency proof assumes.
* In the target theory, **propositional and definitional equality coincide**
  and are plain set equality. `Eq` maps directly to equality in the model;
  this collapse is a crucial design point.
* `Prop` maps to `{ {}, {•} }`: a proposition is either the empty set or a
  fixed singleton. Proof irrelevance is immediate.
* `Empty` maps directly to the empty set (as does `Empty.rec` suitably), which
  is what lets us phrase consistency as "no declaration of type `Empty` is
  accepted".
* The model of `Nat` is the omega set; `Nat` literals map to the binary
  representation of elements of omega. Justifying optimized `Nat` operations
  comes later.
* The model is **level-polymorphic**: level-polymorphic constants map to
  functions from omega (level assignments) into a sequence of universes.
* **No general construction of inductives** (no W-types). This is the main
  simplification over Mario Carneiro's thesis
  (https://github.com/digama0/lean-type-theory/releases): the parts of the
  thesis about the core type theory construction remain relevant, the
  inductive construction does not.

## Inductives via preprocessing

The checker uses https://github.com/nomeata/lean-inductive-models as a
preprocessor (invoked transparently by the `setlec` binary). For
each inductive it builds, *in Lean*, a model: type former, constructors,
recursors, projections as `def`s, and their iota rules as theorems. The
checker then only needs to check that this model matches the declared
inductive. For an inductive with a `_model` from the preprocessor,
`⟦T⟧ := ⟦T._model⟧`, so the model theorems apply without rewriting.

**Modeled inductives are opaque (decision 2026-08-19, per review).** A
modeled inductive `T` is *not* installed as an alias definition
`T := T._model` — it is stored as a real inductive-kind constant
(indInfo/ctorInfo/recInfo), i.e. a whnf head form. The `_model` family
(checked earlier in the stream as ordinary defs/thms) is consulted only
(1) at install time, to check that the inductive matches the model it
claims — member types under the public↔`_model` constant-name rewrite,
iota rules against the `R._model.iota_j` theorems, and (as features
land) `unitlike`/`eta`/`ruleK` theorems — and (2) in the consistency
proofs, where `⟦T⟧ := ⟦T._model⟧` supplies the values and each checked
theorem `a = b` yields `⟦a⟧ = ⟦b⟧` through `mem_eqv`.  Type checking of
code *using* `T` never unfolds it: whnf stops at `T` applications, iota
fires on `T.rec` through the stored rules, and projections use the
stored constructor telescope.  (Aliasing was tried first and makes whnf
see through `T` into the model's encoding — tagged sigmas etc. — so the
kernel-level projection/eta/K rules on `T` become untypeable.)

Consequently the environment invariant carries per-stored-constant
semantic facts abstractly — for every stored recursor rule a fold
equation over value spines (`RecRulesOk`: interpreted recursor applied
through its telescope, with the major a constructor-value spine, equals
the interpreted rule rhs applied to the non-index prefix and fields,
together with the `AppSlot` typing facts and rule-rhs `AnnotOk` the
reduct's annotation chain needs); analogous records for projections and
unit-like/eta/K as those land.  Basis blocks discharge these facts from
the hand-written set values (`Setlec/Model/BasisIota.lean`); modeled
blocks discharge them at install from the checked `_model` theorems.
`whnf`/`isDefEq`/`inferType` soundness consumes only the abstract facts
and never identifies constants by name.

Only the "basis" inductives get hand-written models: `Eq`, `Nat`, `PSigma'`,
`PUnit`, `Quot` (plus the direct `Empty` clause). `PSigma'` and `PUnit` get
custom models (level-zero-or-not case distinction may be needed). These live
in modules analogous to `derived/` in nanodatg.

Axioms: only the three standard axioms are supported; anything else is
"declined" (lean kernel arena exit convention). They map to custom
constructions.

## Term representation

* Our own inductives (`Setlec.Expr` etc.), not `Lean.Expr`: no cached
  metadata, clean verification.
* nanoda-style free variables: an `fvar` is a **de Bruijn level plus its
  type** (binder name is display-only); the type is part of the variable's
  identity. Hence the local context is implicit in every open term, which
  simplifies verification substantially. Input terms from declarations are
  closed and use only `bvar` (de Bruijn indices).
* No metavariables, no `mdata`.

## Checker structure and verification style

* **Strict layering**: implementation code (`Setlec/Kernel/*`, `Main.lean`)
  must not depend on any module from the theory/verification part
  (`Setlec/SetTheory/*`, `Setlec/Model/*`, `Setlec/Verify/*`). The
  verification imports the implementation, never the other way around.
* Verification is **extrinsic**: alongside each checker function there is a
  certifying variant producing the model-level fact
  (we don't put LCF-style certificates in the runtime environment):
  - `infer_ev e` returns a proof of `⟦e⟧ ∈ ⟦infer e⟧`
  - `whnf_ev e` returns a proof of `⟦e⟧ = ⟦whnf e⟧`
  - `defeq_ev e₁ e₂` succeeds iff `defEq e₁ e₂` and returns a proof of
    `⟦e₁⟧ = ⟦e₂⟧`
  - similarly for level operations.
  Whenever the checker produces or assumes `e : t`, a corresponding
  `⟦e⟧ ∈ ⟦t⟧` fact is produced or assumed. Typing assumptions about the local
  environment are hypotheses of the kernel theorems (only such typing facts
  may appear as hypotheses of `*_ev` results); recall the local environment is
  implicit in the term representation.
* The `*_ev` functions follow the structure of the unverified ones closely.
  Steps needing non-trivial constructions go into helper functions in their
  own modules, keeping files small and context-friendly.
* Per constant the (conceptual) global environment carries: its
  interpretation and typing theorem; for inductives the symbols/theorems
  listed above (iota, and where applicable unit-like/eta/K theorems); for
  definitions the delta-unfolding theorem.
* **Match real kernels**: follow nanoda and the official kernel for the order
  of clauses and checks, so reduction happens the same way — same lazy
  unfolding strategy, same pervasive caching. Caches (including the fvar
  caches and any expr-keyed construction) must be memoized with data
  structures whose soundness is feasible to verify, and the certifying
  operations are memoized alongside so proofs are not re-derived. Cache
  lifetime equals that of the corresponding unverified caches.
* **No union-find defeq cache**: known unsound with a non-transitive defeq
  implementation.
* Reference material: https://github.com/nomeata/nanodatg (a certifying, not
  verified, checker for the same target theory; see its `kernel/`) — much of
  its construction transfers. Local clones of reference repos live in
  `_tmp/`.

## Iteration protocol

1. Started from a trivial checker that rejects every declaration as
   "not implemented yet", proved consistent (vacuously, but with
   non-degenerate definitions: the interpretation function is undefined
   everywhere, so only the empty environment has a model).
2. Add **one feature at a time**, updating the verification each step. Use
   the lean kernel arena tutorial tests as a guide; when the next tutorial
   step is too big, write intermediate test cases. Maintain a regression test
   suite (`tests/`, run via `lake test`).
3. Termination of checker functions: use fuel, `partial_fixpoint`, or the
   lean4lean approach — whatever keeps verification simple.
4. Proof style: aim for high `grind` automation. Most proofs should be
   induction / `fun_induction` followed by `grind`; invest in good grind
   annotations.
5. If the checker becomes too slow to iterate quickly, prefer algorithmic
   fixes (caching) over pressing on with features.
6. Constructions not tied to Lean specifics (or to a particular syntax
   representation) go into their own modules (analogous to nanodatg's
   `derived/`). Small modules, narrow interfaces; isolate users of a
   set-theoretic construction from its implementation.
7. Depending on mathlib is acceptable if necessary (ordinals etc.), but
   self-contained is preferred.
8. Commit often.

## Environment notes

* Sandbox: `/tmp` and `/home` are tmpfs — large artifacts (repo checkouts,
  worktrees) go into `_tmp/` inside this repository (gitignored).
* If the checker may OOM, run it under a timeout and memory limit; a process
  eating all memory can kill the whole session.
* For Lean proof work, https://github.com/ejgallego/lean-beam/ may speed
  things up.

## Current state

Supported fragment: **`def`/`thm` declarations over sorts, dependent
function types, lambdas/apps with certified beta, lets (zeta-expanded in
the frontend), constants with delta unfolding, all four basis blocks
(`PUnit`, `Eq`, `Nat`, `PSigma'`) with verified set models,
`PSigma'.mk` projections, proof irrelevance, lambda/unit eta, and
verified iota reduction for all five basis recursor rules** (62/92 good
arena tutorial tests accepted; the good tests still rejected need
ctor-param reduction under `mk` (053), rule K / singleton-elim
reduction (073, 097), second projections (082–084, 096), and struct
eta (109); type-mismatch, duplicate-name, duplicate/undeclared level
parameters, stray free variables, and unknown constants rejected).

Iota soundness (2026-08-19): the whnf iota step is verified end to end.
Per recursor rule, `Setlec/Model/BasisIota.lean` provides the
interpretation of the (annotated) rule rhs, its annotation
truthfulness, the *fold equation* (recursor value applied through the
telescope equals the rhs value applied to the non-index prefix and
fields), and a claims-glue lemma packaging the `AppSlot` typing facts
the reduct's `AnnotOk` app-chain needs.  The claims-side `iota_sound`
(in `Setlec/Model/TypeChecker.lean`) identifies the recursor and
constructor through `decl_ok`/`pinnedInfo`, destructures the concrete
spine, and recovers the canonical argument memberships from the
*original* application chain's `AnnotOk` witnesses via `lam_dom`
("graphs determine their domains") away from the Prop collapse — no
use of the runtime `iotaCerts` is needed for soundness; under the
collapse both sides are the proof point and `AppSlot`s are discharged
with `pt ∈ pi 0 A (fun _ => unitSet)`.  A new `IndOk` conjunct
`BasisBlocks` records that whenever a pinned basis *recursor* is
stored, its block siblings are stored pinned too (blocks install as a
unit, recursor last), which resolves the constants a rule rhs
mentions.  `whnf` is fueled and
delta-unfolds definitions eagerly for now (the lazy strategy of real
kernels is deferred to performance work).

Consistency corollary (2026-08-19): the 15 pinned basis names are
*reserved* — `checkConstantVal` (and the per-member checks of the
dormant `checkIndDecl`) reject any input declaration using one, so the
only thing `Empty` can ever denote is the pinned empty inductive.  The
`IndOk` Empty clause is unconditional (`val emptyName` is uninhabited
in every model, starting from the all-empty base valuation), giving
`no_proof_of_Empty` with no hypothesis about how `Empty` is stored,
and the input-level `no_proof_of_Empty_input`: `checkDecls` never
accepts a list containing a `def`/`theorem` whose *stated* type is
`.const Empty []` (via `checkDecl_stores`: a checked `def`/`thm`
stores its annotated declared type, and `annotate` is the identity on
bare constants).

The environment invariant `EnvWF` (stored declarations closed,
level-param-bounded, constants resolving — all checked syntactically per
declaration) supports monotonicity of reduction/inference/interpretation
under fresh environment extension, and `EnvModel` carries, per constant,
its (level-polymorphic) value, membership in its type's interpretation,
the delta equation for definitions, and parameter-only dependence
(`val_params`).  Level instantiation corresponds semantically to
composing the level assignment (`Level.substFn`), with commutation laws
through `whnf`/`inferType`/`interpExpr`.

Binders follow nanoda: opening substitutes `fvar d n ty` where `d` is the
binder depth (de Bruijn level) and the annotation `ty` is part of the
variable's identity; the local context is implicit in terms.  The model
interprets `Π` with the thesis's Prop/Type split: `SetTheory.pi` takes the
*evaluated codomain sort* explicitly (not recoverable from the sets:
`⟦True⟧ = ⟦PUnit⟧`), and `interpExpr` obtains it by re-running the
checker's own `inferType` on the opened body.  Deviation from real kernels
(documented in `Kernel/TypeChecker.lean`): `isDefEq` on two ∀-types also
checks the codomain sorts are semantically equal levels — implied for
well-typed input, but proving that needs sort-coherence metatheory we
don't have yet; costs completeness/performance only.

The binder metatheory lives in `Verify/Shift.lean` (`WScoped`,
`shiftFrom`, commutation with `instantiate1`), `Verify/InferShift.lean`
(shift invariance of `whnf`/`ensureSort`/`inferType`) and
`Model/InterpLemmas.lean` (`interp_ext`, `interp_shift`,
`interp_weaken_top`, `FvarsOk.instantiate1`).  The soundness statements
take `WScoped` (syntactic scoping, annotations scoped at their own index)
and `FvarsOk` (each free variable's valuation is a member of its
annotated type's interpretation — "the typing assumptions of the local
environment are hypotheses of the kernel theorems") as hypotheses.

* `Setlec.Kernel.{Expr,Env}`: term representation, environment.
* `Setlec.Kernel.Level`: `simplify`/`leqCore` (nanoda's algorithm and case
  order; fuel for termination, exhaustion = internal error)/`isEquiv`.
* `Setlec.Kernel.TypeChecker`: `whnf`/`inferType`/`isDefEq` on the fragment;
  `CheckError` distinguishes `notImplemented` (decline) / `invalid` (reject)
  / `internal` (error).
* `Setlec.Kernel.Checker`: `checkDecl`/`checkDecls` (guards: fresh name,
  nodup level params, params declared, type is a sort, value type defeq).
* `Setlec.Verify.Level`: `Level.eval` semantics into `Nat`; soundness of
  `simplify`, `leqCore`, `isEquiv` (the `some true` direction).
* `Setlec.SetTheory.Basic`: TG interface — membership, empty set,
  `univ : Nat → V` with `univ n ∈ univ (n+1)`.
* `Setlec.Model.Interp`: `interpExpr` (sorts ↦ `univ (eval φ u)`), `EnvModel`
  (level-polymorphic constant valuations; membership in type; definitions
  interpreted by their bodies).
* `Setlec.Model.TypeChecker`: soundness of `whnf`/`inferType`/`isDefEq`.
* `Setlec.Model.Consistency`: `checkDecl_sound` (checking preserves having a
  model), `checkDecls_sound` (accepted ⇒ model exists).
* `Setlec.Frontend.Export`: lean4export 3.x ndjson parser (sparse tables).
* `Main.lean`: CLI with arena exit codes.
* Tests: `lake test` (unit `#guard`s), `tests/arena.sh` against
  `tests/arena-expected.txt` (per-test pinned exit codes; good tests must
  never be rejected, bad tests never accepted).

### Next step: sort annotations, then lambdas/app/beta (task 3)

**The problem.** `interpExpr` currently classifies each `Π`-type's
codomain (Prop vs Type, needed by `SetTheory.pi`) by re-running the
checker's `inferType` on the opened body.  This made the weakening lemmas
carry inference-shift lemmas, and it makes the *substitution lemma*
(needed for beta and for the dependent application rule `(Π x:A. B) a ↦
B[a]`) essentially unprovable without subject-reduction-grade metatheory:
substituting `a` for an fvar changes the syntactic inference runs inside
the classifier, and reconnecting them needs "defeq types have eval-equal
sorts" compositionally.

**The decision (2026-08-19): annotate binders with their codomain sort.**
`Expr.forallE` (and `lam`) gets an `Option Level` annotation slot:

* the frontend parses everything with `none`;
* a checker pass (or the inference itself) computes each binder's
  codomain sort once, by real inference, and stores it — annotations are
  *checked once at creation, then trusted*;
* `inferType` on an annotated `forallE` *reads* the annotation for the
  imax rule; `isDefEq` compares annotations with `Level.isEquiv`
  (replacing the current re-inference deviation — also cheaper);
* `interpExpr`'s classifier becomes `eval φ` of the stored annotation —
  **fully structural**, no embedded inference.  `sortLevelOf` and all its
  shift/mono/instLevels plumbing get deleted.

Then substitution (`fvar` ↦ arbitrary term) does not touch levels, so the
substitution lemma is mechanical, like `interp_shift`: define
`substFvarAt p a` (replace `fvar p`, shift higher fvars down) with a
`delV`-style valuation contraction, plus depth-invariance for scoped
terms (generalizing `interp_closed_invariant`).  Beta and the dependent
application rule then verify without new metatheory classes.

**Status: the refactor (order-of-work item 1) is DONE** — `annotate`,
trust-and-read `inferType`, annotation-comparing `isDefEq`, structural
`interpExpr`, the `AnnotOk` invariant with its full transport family,
`annotate_sound`, and the reworked consistency proof are all merged and
verified.  Next: order-of-work item 2 (lambdas, application, beta, the
now-mechanical substitution lemma).

Refined plan (annotation slot itself is done):

* `annotate env d e` (bottom-up): opens each binder with the annotated
  domain, recurses, computes the codomain sort by real inference on the
  fully-annotated body (`ensureSort ∘ inferType`, for a `lam` the sort of
  the body's inferred type), stores it, and re-closes with `abstract1`
  (replace `fvar d` by `bvar k`).  `checkDecl` annotates type and value
  right after the syntactic guards and stores annotated declarations.
* `inferType` on an annotated `forallE` **trusts** the annotation: it
  infers only the domain sort and returns `sort (imax u cod)` without
  descending into the body (`cod = none` is an internal error).  Bodies
  are checked exactly once, at annotate time.  This also makes
  `inferType` structurally recursive.
* `isDefEq` on two ∀s compares the annotations with `Level.isEquiv`
  (replaces the re-inference deviation).
* `interpExpr`'s ∀-clause reads the annotation; `sortLevelOf` and all its
  shift/instLevels/mono lemmas are deleted (`Verify/InferShift.lean`
  disappears; `Verify/InferLemmas.lean` shrinks).
* New semantic invariant `AnnotOk` (structural, like `FvarsOk`): each
  ∀-subterm's fibres, over its interpreted domain, land in
  `univ (eval φ cod)`.  Established by `annotate_sound`, consumed as a
  hypothesis by `inferType_sound` (whose ∀-case no longer has body
  inference to lean on), preserved by opening/substitution — the
  preservation under *term* substitution follows from the now-mechanical
  substitution lemma, which is the whole point of the design.

Plan for item 2 (worked out 2026-08-19, after the refactor):

* **Leaf-closure `FvarsOk`**: redefine `FvarsOk` as "every triple in
  `Expr.fvarLeaves e` (reachable `fvar` leaves plus, hereditarily, the
  leaves of their annotations) satisfies the membership condition".  Then
  every syntactic transformation needs only an `fvarLeaves`-subset lemma
  (instantiate1, abstract1, annotate ≙ leaf-equal via `LeafEquiv`,
  `whnf`/`inferType` outputs ⊆ input closure ∪ closed), and
  `inferType_sound` can conclude `FvarsOk` of its *output* uniformly —
  which the λ-rule needs (the abstracted body type reappears as a Π-body).
* `isDefEqCore_sound` in fact never consumes `FvarsOk` (definedness comes
  from `AnnotOk`); drop those hypotheses.
* `inferType` gets fuel (the λ-rule re-checks the stored annotation
  against `ensureSort ∘ inferType` of the inferred body type, which is
  not structurally smaller).
* λ-rule: infer opened body, re-close with `abstract1` (roundtrip via
  `fvarConsistent`/`looseBVarsBounded` output-preservation lemmas for
  `inferType`), result `Π` annotated with the λ's stored `cod`.
* app-rule: whnf the function type to a `Π`, check the argument against
  the domain, return `body.instantiate1 arg`.
* `whnf` beta case: `app (lam …) a ↦ body.instantiate1 a`.
* `SetTheory` additions: `lam : Nat → V → (V → V) → V`, `app : V → V → V`
  with `lam_congr`, `lam_mem : (∀ x ∈ A, F x ∈ B x) → lam v A F ∈ pi v A B`
  (no fibre-universe premise needed — for `v = 0` the premise itself
  makes every fibre inhabited), `app_mem : f ∈ pi v A B → a ∈ A →
  (∀ x ∈ A, B x ∈ univ v) → app f a ∈ B a` (fibre premise needed for
  `v = 0` realizability), and conditional beta
  `app_lam : a ∈ A → (∀ x ∈ A, F x ∈ B x) → (∀ x ∈ A, B x ∈ univ v) →
  app (lam v A F) a = F a`.
* `interpExpr`: `lam` ↦ `SetTheory.lam (eval cod) ⟦ty⟧ (fibres)`,
  `app` ↦ `SetTheory.app ⟦f⟧ ⟦a⟧`.
* **Substitution lemma** (now classifier-free): `substFvarAt p a` with a
  `delV` valuation contraction; `interp d (delV ρ' p) (t.substFvarAt p a)
  = interp (d+1) ρ' t` given `ρ' p = ⟦a⟧` and depth-invariance of `⟦a⟧`
  (scoped-term generalization of `interp_closed_invariant`).  Beta/whnf
  soundness and the dependent application rule reduce to it.

### Beta soundness without subject reduction (worked out 2026-08-19)

`whnf`-beta (`app (lam n ty body ⟨…,v⟩) a ↦ body.instantiate1 a`) is
sound in the model only via `SetTheory.app_lam`, whose key premise is
`⟦a⟧ ∈ ⟦ty⟧` — the argument lives in *the λ's own* domain.  A typing
derivation would hand this over (that's how thesis-style models get it);
an invariant on raw terms has to carry it through arbitrary reductions
and substitutions.  Analysis of the design space:

* For `Prop`-valued functions the interpretation collapses to a point
  (impredicativity forces this — proof-relevant impredicative Prop has no
  set model), so **no semantic invariant can recover the domain of a
  proof-λ**.  Any route that beta-reduces proof-redexes needs syntactic
  subject-reduction metatheory (checker-run commutation with
  substitution) — exactly what the annotation design exists to avoid.
* Consequently `whnf` cannot blindly beta-reduce possibly-Prop redexes.
  A pure syntactic guard (`Level.isNonZero` on the codomain sort) is
  *insufficient in practice*: level-polymorphic lambdas (`Sort u`
  codomains — e.g. Church encodings, arena 029/030) are never certainly
  non-Prop and would stay stuck, failing good tests.  **Resolution
  (2026-08-19): runtime certification.**  On a redex whose codomain sort
  is not certainly nonzero, `whnf` first checks
  `isDefEq (inferType a) ty` — the check passing hands the soundness
  proof exactly the missing fact (`⟦a⟧ ∈ ⟦ty⟧`, at *every* level
  assignment); failing leaves the redex stuck (sound: `whnf` may always
  under-reduce; unreachable for well-typed input).  This makes
  `whnf`/`inferType`/`isDefEq` mutually recursive on one shared,
  strictly decreasing fuel (separate per-function fuels would regress
  infinitely across the mutual calls), and the three soundness theorems
  one mutual fuel induction.  Deviation from real kernels (documented):
  they reduce unconditionally and compensate with proof irrelevance;
  the certification costs an inference+defeq per possibly-Prop redex.
  Revisit with performance work (e.g. cache certified redexes).
* For non-Prop redexes a **semantic-only app clause in `AnnotOk`**
  suffices: `∃ vE A B, ⟦f⟧ ∈ pi vE A B ∧ ⟦a⟧ ∈ A ∧ ∀ x ∈ A, B x ∈ univ
  vE` (plus definedness).  Established by `annotate` running the full
  application rule (infer `f`, whnf to `Π`, defeq-check the argument) —
  `annotate` remains the one place where typing is *checked*; the clause
  transports purely semantically (no checker runs inside the invariant).
* Connecting the clause's `pi`-membership to the λ that `f` reduces to
  uses new (realizable) `SetTheory` axioms about the **tagged proof
  point** `pt := {∅}` — a set that is never a function graph:
  `mem_pi_zero : f ∈ pi 0 A B → f = pt`, `lam_ne_pt : v ≠ 0 → lam v A F
  ≠ pt`, `lam_dom : lam v' A F ∈ pi v A' B → v ≠ 0 → v' ≠ 0 → A' ⊆ A`
  (graphs determine their domains), `mem_univ_zero : T ∈ univ 0 → x ∈ T
  → x = pt`.  The mismatched-level "junk" cases (`vE = 0` but the λ
  type-valued, or vice versa) are then *vacuous by contradiction* instead
  of needing typing: a genuine graph is never `pt`.  (Realization: `app f
  a := if f = pt then pt else ⋃ {y | ⟨a,y⟩ ∈ f}`; `lam 0 A F := pt`;
  truth values are subsets of `{pt}`.)
* `inferType`'s app rule keeps the runtime defeq check (`ta ≟ domain`)
  and its soundness needs **no clause at all**: IH gives `⟦f⟧ ∈ ⟦tf⟧` and
  `⟦a⟧ ∈ ⟦ta⟧`, `whnf_sound` turns `⟦tf⟧` into a canonical `pi`,
  `isDefEq_sound` identifies `⟦ta⟧` with the domain, `app_mem` closes.
  This is *why* kernels have that check.
* The λ-rule's `abstract1` roundtrip needs `inferType` outputs to be
  bvar-closed and fvar-consistent; both are leaf-closure conditions
  (`∀ l ∈ fvarLeaves`, …) so the output-⊆-input leaf lemma for
  `whnf`/`inferType` transports them for free.
* **Inductive-model layering** (user decision, 2026-08-19): the
  environment invariant (`EnvModel.ind_ok`) states, for every stored
  inductive-kind constant (`indInfo`/`ctorInfo`/`recInfo`), the semantic
  facts the checker functions need — application-fold equations, domain
  determinations for partial applications, iota equations — abstractly
  over the model's valuation.  `whnf`/`inferType`/`isDefEq` soundness
  consumes only these fields and is construction-agnostic; only the
  *installation* code (`checkDecl` on a basis block) contains
  construction-specific proofs, discharging `ind_ok` from the
  hand-written basis values (`pinnedVal`, `psigmaVal_fold`, …).
* Deleted rather than ported: `Verify/InferShift.lean` and the
  instLevels/mono/constsResolve/allLevelParams lemma family for
  `inferType` — they were only needed when the interpretation re-ran
  inference; nothing imports them anymore.

Order of work:
1. ~~Refactor: annotation pass, structural `interpExpr`, `AnnotOk`~~ DONE.
2. Lambdas, application, beta, congruence defeq (`abstract1` for
   `infer`-lam with the fvar-annotation-consistency roundtrip), the
   substitution lemma; arena 005–007, 020, 021, 026, 027.
3. `letE` (zeta) — 031–033; eta — 111, 112.
4. Axioms (only the three standard ones; models for them come with the
   `Eq`/`Quot` machinery), 011.
5. Inductives via lean-inductive-models preprocessor (034 ff.).

### Proof irrelevance (2026-08-19)

`isDefEq` implements proof irrelevance by *certification*, like beta and
proj: on any structural-comparison failure (mismatched stuck heads,
distinct fvars/consts, failed app congruence) it runs `proofIrrel a b`,
which checks that both sides' types' *sorts* are `Prop`
(`inferType (inferType x)` whnfs to `.sort u` with `u ≡ 0`).  Soundness
needs *no common-type check*: in the model everything inhabiting a
proposition is the tagged proof point `pt` (`sortCert_pt` twice), so the
interpretations are equal outright.  This is what lets the
lean-inductive-models `_model` encodings of `Prop` inductives (`And`,
`Exists`, …) typecheck: their recursors re-build the scrutinee from its
projections, which only proof irrelevance can equate with the original.

The frontend matches incoming inductive blocks against the pinned basis
blocks *up to binder names and positional level-parameter renaming*
(`ConstantInfo.canon`): Lean's exports use auto-bound universe names
(`Eq.{u_1}`, `Eq.rec.{u, u_1}`) and hygienic binder names, both
semantically irrelevant; the checker installs the pinned (annotated)
declarations.

### Generic eta/iota machinery (2026-08-19, per review)

`whnf`/`isDefEq` never test basis *names*: the kernel keys only on
environment shapes — `ctorInfo`/`indInfo`/`recInfo` numbers, the iota
rules, and the `<ind>.rec` naming convention that links a type to its
recursor (a rule's `ctor` field links back to the constructor).  Unit
eta fires for any stored inductive whose recursor has no indices and a
single zero-field rule; pair eta for any fully applied two-field
structure constructor.  The soundness side identifies the concrete
basis constant through the environment invariant's `decl_ok` conjunct
(every stored basis-shaped constant *is* its pinned declaration —
`pinnedInfo` — and its valuation *is* its pinned value — `pinnedVal`),
so only installation contains construction-specific proofs.
