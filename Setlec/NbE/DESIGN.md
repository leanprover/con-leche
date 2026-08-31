# NbE pilot (task #159) — design record and verdict memo

Charter: implement a core checker in the NbE / environment-machine
regime and probe whether its soundness proof against the set model is
genuinely simpler than the substitution checker's.  Walls are the
deliverable.  Branch `agent/nbe-pilot`, parked unmerged; additive files
only (`Setlec/NbE/*`, `tests/NbETests.lean`, umbrella + lakefile-roots
wiring).  Build warning-free, `lake test` green, arena battery
unchanged (90/92 tutorial, 72/72 e2e, sweeps as recorded).

## What landed

Implementation (no theory imports; reuses the campaign's `Name`/`Level`
and `Level.isEquiv` so levels are the real thing):

| module | content |
|---|---|
| `Term.lean` | Π/λ/app/sort/bvar/const terms.  **No fvar constructor, no lift, no subst.**  `instL` = level instantiation (the one syntax traversal, as in every real kernel). Environment of *definitions only* (keeps `EnvOk` satisfiable; axioms would puncture the slice's consistency story). |
| `Value.lean` | Defunctionalized closures (captured env + body).  Neutrals = head (untyped fvar *level*, or const + levels) + spine.  Glued: the const-headed neutral *is* the cheap face; the unfolded face is recomputed on demand (`unfoldNeu`).  Finding: the thunk-cached variant (`Thunk (Option Value)` field) makes `Value` reflexive and Lean cannot derive `SizeOf` — every verification recursion dies; recompute-on-force keeps the algorithmic shape and *simplifies* the proof obligations (event premises instead of a pedigree invariant on all reachable thunks). |
| `Eval.lean` | Fueled environment machine: β = closure application, never syntax rewriting.  `quote` (readback) never unfolds a definition — the gluing payoff. |
| `Conv.lean` | Untyped value conversion: `Level.isEquiv` at sorts; domains-then-bodies at binders under a *shared untyped* fresh variable; glued/glued tries the spine-equality shortcut (equal head, `isEquivList` levels, pairwise-convertible spines ⇒ true *without unfolding*; shortcut failure is not a verdict — δ both sides and retry).  No η, no proofIrrel (slice 1). |
| `Check.lean` | Front door only: infer-style, one typing pass per declaration; after it, no types are carried, no certificates produced.  The single place readback enters checking: `infer` of a λ quotes the body's inferred type value to re-close it as a Π over `freshEnv`. |

Verification (parametric in the campaign's own `SetTheory` interface):

| module | status |
|---|---|
| `Verify/Denote.lean` | `dTerm`/`dVal`/`dClosure`/`dVals` (closure denotation = environment extension + `dTerm`, i.e. *the machine's own shape*).  Level transport `dTerm_instL` + `dTerm_ext_φ` + `substFn_eq_lvlAssign`: **unconditional**, ~60 lines — the entire substitution metatheory of the tier.  Scoping (`ScopedV`, `dVal_ext_σ`). All proved. |
| `Verify/Eval.lean` | **Fundamental theorem `eval_applyV_sound` proved** (fuel induction over both machine functions), conditional on the β-membership ledger `EvalOk`/`ApplyOk`.  β case = IH + **one** `app_lamC`; binder cases = `rfl` after domain rewrite.  `ft_unconditional_refuted`: the ledger-free FT is false (machine-checked schema countermodel).  δ-coherence `unfoldNeu_sound` proved (glued faces agree, given `EnvOk` + ledger).  Vacuity probes: concrete satisfiable ledger instance with a nontrivial model conclusion. |
| `Verify/Conv.lean` | **`conv_sound` proved** (some-true verdict ⇒ equal denotations), conditional on the `ConvOk` ledger mirroring `conv`'s match tree.  Spine shortcut sound with zero unfolding and zero typing.  `closure_app_coherent` + `eval_applyV_scoped`: the binder-clause coherence premises are exactly FT + scoping, i.e. dischargeable. |
| `Verify/Walls.lean` | The frontier, as named `Prop`s (below), plus the assembly theorem `no_universal_inhabitant_of_adequacy`: wall 1 alone yields the slice's consistency-style corollary, so the walls are jointly sufficient — the frontier is exact. |

Sizes: implementation 529 lines, verification 1376 lines, tests 131.

## FT status, case by case

| case | status |
|---|---|
| bvar / sort / const / neutral-app | proved, essentially `rfl` / one list lemma |
| λ, Π formation (under binder) | proved, `rfl` after IH — the promise's heart: machine env-extension ≡ denotation env-extension |
| β (`applyV` λ clause) | **proved with exactly one `app_lamC`**, premised on the one ledger membership `⟦a⟧ ∈ˢ ⟦dom⟧`; ledger-free version refuted |
| δ (glued unfold) | proved (`unfoldNeu_sound`) given `EnvOk` + ledger; levels cross via the unconditional `dTerm_instL` |
| conv: sorts | proved via `Level.isEquiv_sound` (regime transfer: same `Level` syntax, all-assignment statement) |
| conv: binders | proved given the `BinderOk` coherence facts (shown = FT + scoping) |
| conv: spine shortcut | proved, no typing, no unfolding |
| conv: δ fallback | proved given `DeltaOk` (= `unfoldNeu_sound`'s equations) |
| ledger discharge from the front door | **WALL 1** (below) |
| readback | **WALL 2** |

## The walls (exact clauses in `Verify/Walls.lean`)

1. **Front-door adequacy** (`FrontDoorAdequacy`, `InferAdequacyStmt`):
   acceptance ⇒ semantic typing + all ledgers.  Naive induction on
   `infer` fails at exactly the λ clause: `infer` sees the body once
   under one fresh variable; the conclusion and every later β ledger
   need it for *all* `x ∈ˢ ⟦dom⟧`.  Fix = Kripke-style logical
   relation over semantic environments.  This is hard class 3, not
   eliminated but relocated (per-β-event memberships instead of
   per-syntax-node `AnnotOk`); crucially it needs **no stability under
   syntactic substitution**, because there is none.
2. **Readback coherence** (`QuoteCoherenceStmt`): `quote` inverts
   `dVal` against the fresh frame.  Forced into the checking path only
   by `infer`-of-λ.  Statable crisply because readback never unfolds;
   estimated cost ≈ `conv_sound`.
3. **Ledger transport along forcing** (`forceV`/`toPi`/`toSort`
   chains): iterate `unfoldNeu_sound`; mechanical but real, and wants
   fuel-monotonicity lemmas for the mirrors.

## Gluing-coherence verdict

The spine-equality shortcut needs **no coherence tier at all**: `app`
is a function, so pointwise-equal spines compose for free; heads need
only `Level.isEquiv_sound`.  The δ side needs exactly one equation per
unfold event (`⟦unfolded⟧ = ⟦spine⟧` = `unfoldNeu_sound`), premised on
`EnvOk` + the β ledger of the body.  With recomputed unfolding this is
an *event* premise; a thunk-cached implementation upgrades it to a
value invariant ("every thunk in every reachable value is pedigreed"),
fuel-indexed, threaded through every constructor site — that is the
mini coherence tier the charter asked about, and it is the price of
caching, not of gluing per se.

## The comparison memo (three hard classes)

1. **Substitution transport — eliminated, genuinely.**  The
   implementation contains no term substitution, so the campaign's
   dominant cost class has *no object to be about*.  Its entire
   residue: `dTerm_instL` (levels, unconditional, ~20 lines of proof)
   plus scoping (`ScopedV`/`dVal_ext_σ` + `eval_applyV_scoped`,
   ~150 lines — the ScopedSim discipline shrunk to one structural
   induction).  Compare ≈8.6k lines in the named transport modules of
   `Setlec/Verify` (Shift/Abstract/AbstractRange/InstList/InstSpine/
   BetaSpine/Extend*), all conditional on typing and multiplied across
   rewrite sites.  The β case of the FT is one lemma application.
   **Promise verified.**
2. **Cross-run sort agreement — absent from this slice, structurally.**
   Conversion's fresh variables are untyped (no sort exists to
   disagree about); sorts meet only as carried `Level` syntax at
   `sort`/`sort` leaves, decided by `isEquiv` whose soundness is
   all-assignment arithmetic; the model is only ever applied forward
   (`univ ∘ eval φ`), never inverted.  `infer` runs once, before
   values exist, so no second run manufactures types.  Honest caveat:
   this is a property of *slice 1's rule set*; a second slice adding
   rules that must *produce* a sort mid-conversion (e.g. η for Π-typed
   neutrals done type-directedly, or proofIrrel) reopens the question —
   but through the typing channel (class 3), not through model-level
   arbitration.
3. **Typing boundary — reappears, in new clothing, undiminished in
   kind but cheaper in composition.**  Model β is domain-conditional
   (post-#100 collapse: membership only, no fibre/universe premise —
   this collapse is what makes the whole pilot this small), so
   soundness facts exist only along typed evaluations.  The clothing:
   fueled Prop-mirrors of the machine (`EvalOk`/`ApplyOk`/`ArgsOk`/
   `ConvOk`) carrying one membership per β event and one equation per
   δ/binder event.  The discharge (wall 1) is a logical relation of
   the same species as the campaign's typing tier.  What is cheaper:
   the relation composes with the machine definitionally (no
   preservation-under-rewriting obligations), and the ledger is
   positional (per event) rather than structural (per node of every
   intermediate term).  Rough odds: the pilot's proved tier is ~1.4k
   lines where the analogous campaign surface is tens of thousands,
   but wall 1 is the unbuilt part and is the hard kind; the honest
   claim is "class 1 deleted, class 2 not summoned, class 3
   conserved" — a large constant-factor and *structural* win, not a
   free consistency proof.

## Performance shape notes

* β/δ never rewrite syntax; environments are shared cons-lists; glued
  spines make readback and the defeq shortcut O(spine) with zero
  unfolding.  `infer`-of-app checks the argument by `conv` on values.
* The pilot recomputes δ-unfoldings (`unfoldNeu`); production wants
  the memoizing thunk back.  Options recorded in `Value.lean`:
  `genSizeOfSpec false` + hand-rolled measure, or an opaque cache
  handle — either way the verification interface should stay
  "`unfoldsTo` as a relation defined by `eval`", with the cache proven
  to *implement* it, so the event-premise proofs survive unchanged.
* Fuel is decremented per structural step (crude); a production
  machine wants step-counting only at β/δ.  Mirrors must then be
  restated at the same grain (they mirror whatever the machine does).

## Second slice (ι, proofIrrel, letE, projections): costs and risks

* **letE**: trivial in this regime (evaluate the bound value, extend
  the environment; denotation likewise); no new ledger clause.
* **ι / recursors**: recursor application is a new `applyV` head case
  (stuck-until-major-is-constructor); the value domain gains
  constructor forms; the ledger gains the recursor-rule membership
  facts — the campaign's `RecRulesOk` (total λ-equality per stored
  rule) transplants as the `EnvOk` analogue for rec rules, consumed at
  ι events exactly like `app_lamC` at β events.  Risk: moderate,
  mostly volume.
* **proofIrrel**: the sharp one.  See `Verify/Walls.lean` §"where
  proof irrelevance would enter": the untyped comparison must acquire
  a typing channel (official kernel and nanoda *infer inside defeq*;
  here that means quote + infer mid-`conv`).  Model-side nearly free
  (`mem_univ_zero`), ledger-side one clause; realism-side it breaks
  the "no typing after the front door" purity — recorded as a finding,
  per the charter, not designed around.
* **projections**: value-level `.proj` on constructor forms plus a
  stuck-neutral form; same pattern as ι.

## Iteration protocol notes

* Trap-ledger discipline applied: every theorem premised on
  env/ledger wellformedness, never bare; `ft_unconditional_refuted` is
  the recorded refutation forcing the ledger; vacuity probes in
  `Verify/Eval.lean` (satisfiable ledger + nontrivial conclusion) and
  `Verify/Walls.lean` (`envOk_empty` + accepted decls in tests);
  regime transfers named where used (`Level.isEquiv_sound`,
  `eval_subst`/`eval_ext` — same syntax, all-assignment statements).
* The branch parks unmerged pending the pilot verdict.
