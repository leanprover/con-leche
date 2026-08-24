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

* The target theory is **ZF (minus Infinity) plus an ω-chain of Grothendieck
  universes** — the consistency strength of Lean itself: the
  `OmegaInaccessibles` hypothesis of Mario Carneiro, *The Type Theory
  of Lean*, master's thesis, Carnegie Mellon University, 2019 (ZFC +
  a strictly increasing ω-sequence of inaccessibles; model the chain
  by `V_{κ n}`). Inside Lean it is
  expressed as an interface (`Setlec.SetTheory`, see
  `Setlec/SetTheory/Core.lean`), a class over a universe
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
stored constructor telescope.  Projections annotate into applications
of installed `T.proj.i` functions (checked against `_model.proj_i` at
install); when no projection function is installed — Prop
structure-likes with data fields, whose projections only *exist* at
certain level instantiations, so level-polymorphic artifacts cannot
cover them — `annotateProjRec` permanently falls back to inlining the
recursor elimination at the use site's concrete levels (constant
motive = the field's type with earlier fields as projections, minor =
the constructor telescope as `λ`s returning the field), re-annotated
so the ordinary rules re-check it; the official kernel's Prop
restrictions are mirrored in the telescope walk.  (Aliasing was tried first and makes whnf
see through `T` into the model's encoding — tagged sigmas etc. — so the
kernel-level projection/eta/K rules on `T` become untypeable.)

Consequently the environment invariant carries per-stored-constant
semantic facts abstractly — for every stored fireable recursor rule a
**total λ-equality** (`RecRulesOk`, task #58): the canonical
frame/body decomposition `ruleLhsParts` computes, is well-formed and
resolves, and for every level assignment the closed left-hand λ-tower
(`closeLamsAt fvms bL`) is `AnnotOk` and interprets to the same value
as the stored rule right-hand side; analogous records for projections
and unit-like/eta/K as those land.  Basis blocks discharge these facts from
the hand-written set values (`Setlec/Model/BasisIota.lean`); modeled
blocks discharge them at install from the checked `_model` theorems.
`whnf`/`isDefEq`/`inferType` soundness consumes only the abstract facts
and never identifies constants by name.

Only the "basis" inductives get hand-written models: `Eq`, `Nat`, `PSigma'`,
`PUnit`, `Quot` (plus the direct `Empty` clause). `PSigma'` and `PUnit` get
custom models (level-zero-or-not case distinction may be needed). These live
in modules analogous to `derived/` in nanodatg.

Axioms: only the standard axioms are supported; anything else is
"declined" (lean kernel arena exit convention).  This is a deliberate
ceiling (owner ruling, 2026-08-21): acceptance routes for custom
axioms (opaque-with-witness, unfoldable-definition storage,
canonical-value models) were explored and rejected: none is wanted.
Refinement (user rulings, 2026-08-22/24, revised for task #95): the
*tolerated whitelist* (`toleratedAxiomNames`) is exactly `sorryAx` — a
tolerated `axiom` record is dropped by the frontend without parsing
its type at all; nothing is installed and the name is tainted
(`Frontend.State.taintedNames`).  The `Init` **compiler-trust family
is installed** instead (task #95, user design 2026-08-24):
`Lean.trustCompiler : True` is trivially realizable and installs like
a checked `opaque` realized by `True.intro` over the pinned `True`
family; `Lean.reduceNat`/`Lean.reduceBool` then check as ordinary
opaques, pin-gated against the toolchain's own defining expressions
plus an identity certificate; and `Lean.ofReduceNat`/
`Lean.ofReduceBool` install as pinned axioms whose types are trivially
inhabited once the reduce opaques are the identity (see "The
compiler-trust axiom family" below).  Any other `axiom` record is
forwarded and positively declined by the checker at its own record,
after well-formedness-checking — a garbage record such as arena
`bad/011_nonTypeAxiom` keeps *rejecting*; the two tutorial tests
scaffolded by custom axioms (`032_letTypeDep`, `033_letRed`) decline
at their custom `axiom` record, exit 2, so the vendored tutorial
snapshot stays at 90/92 accepted, the full non-axiom set.  *Uses* of
a tainted constant are never accepted, but no longer stop the stream
either (skip-and-continue, user directive 2026-08-24): a declaration
whose type/value (transitively) references a tainted name is *skipped*
at parse time — absent from the parsed declarations, so it can never
be checked or installed — its declared names are tainted in turn (so
transitive users skip too), and the rest of the stream is checked as
usual.  `Frontend.ParseResult.taintSkipped` records the skips (name +
whitelisted axiom root); the driver declines the input as a whole
(exit 2) whenever it is nonempty, even if every remaining declaration
checks, and prints a per-root summary (`Frontend.taintSummary`).  A
stream with no tainted uses behaves exactly as before.  With the
compiler-trust family installed, the full `Init` export has **zero**
skips and exits 0 (`sorryAx` is declared but unused in `Init`).
`Quot.sound` is part
of the pinned quotient basis block; `propext` and `Classical.choice`
are accepted as `axiomDecl`s by `stdAxiomOk`: a pure predicate that
requires the pinned `Eq` basis plus standardly-shaped stored `Iff`
(for `propext`) resp. `Nonempty` (for `choice`) families, and matches
the checked type against annotated pins (`Setlec/Kernel/StdAxioms.lean`).
Since the exporter's hygienic binder names are unstable across
preprocessor runs, pin matching compares types up to binder names
(`Expr.eraseNames`); the interpretation never reads what is erased
(`Expr.ErasedEq.of_eraseNames` + `interp_erasedEq` transport the model
facts from the pin to the stored type).  Models: `propext` is the
proof point `pt`, true by propositional extensionality of the set
model (`SetTheory.prop_ext`) via the stored `Iff.rec`'s member fact;
`Classical.choice` is a function tower ending in a global choice
operator (`SetTheory.schoice`), with nonemptiness extracted from the
stored `Nonempty.rec`'s member fact (`Setlec/Model/StdAxioms.lean`).

Consequence for the arena's non-tutorial good roots (finding,
2026-08-22, task #67): `good/proof-irrel.ndjson`,
`good/level-index-out-of-order.ndjson` and
`good/sparse-name-index.ndjson` all *decline* (exit 2) **because they
are scaffolded by custom axioms** (`axiom foo : Sort 2`, `axiom foo :
Prop`, and an `A`/`P`/`Q`/`foo` axiom frame respectively) — exactly
the pinned `custom_axiom_declined` e2e behavior, not a frontend
restriction.  The features their names advertise are in fact
supported: the export tables are hash-map-backed, so sparse and
out-of-order `in`/`il`/`ie` indices parse fine (the declines name the
axioms, which requires the sparse indices to have resolved), and
algorithmic proof irrelevance is implemented (`proofIrrel`,
exercised by the accepted `subject-reduction-redex` test).  These
three stay declined by design under the axiom ceiling.

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

## The open-recursion core and the refinement bridge (2026-08-20)

The checker core is **single-sourced**: every core function is one
non-recursive *body* in `Setlec/Kernel/Core.lean`, parameterized over a
record of the mutually recursive entry points (`CoreFns`) and
monad-polymorphic.  Fuel lives only in the knots that tie the record:
the **pure knot** (`Setlec/Kernel/TypeChecker.lean`, `pureFns`) at
`CheckM` is the verification's subject; the **memoized knot**
(`Setlec/Kernel/TypeCheckerC.lean`, `cachedFns`) wraps every level's
entry points with a `KCache` lookup (maps keyed by the **expression
alone** — see *Depth-free memo keys* below) in `StateT` over `CheckM`
and is what the checker executes
(`cachedOps` in `Setlec/Kernel/Checker.lean`; the declaration checker
itself is written once over a `CheckerOps` record).  The knots are
built lazily — each level closes over a thunk of the next; an eager
tower was a 12x slowdown.  Memoization took 053_reduceCtorParam from
2m04s to 0.6s and the whole tutorial arena to ~13s.

Verification style: `Setlec/Verify/Knot.lean` holds the definitional
equations bridging fueled spellings to bodies-at-the-knot
(`whnfCore_succ`, `*_def`, `*_zero`), plus fueled `P`-abbrevs and
`*_fold` rewrites for the record-parameterized helpers.  Inversions
(`Setlec/Verify/*`) and claims (`Setlec/Model/Core/*`) unfold one body
with the recipe `rw [X_succ]; simp only [XBody, …]; simp only [*_def,
*_fold]` and obtain all helper facts at the **same** fuel (helpers no
longer consume fuel — only the knot does).  Dependent `match e, h`
on knot-defined hypotheses times out; use `cases e` + the recipe.

The **refinement bridge** (2026-08-20) transports every claim to the
executable, in three parts built on one device — the bodies are
monad-polymorphic, so relational statements about two instantiations
are obtained by instantiating them *once* at a **relational pair
monad** (`PairM rel`, `Setlec/Verify/PairM.lean`): pairs of
computations carrying a relation closed under `bind`/`pure`/`throw`;
the instantiated body's subtype proof *is* the per-body lemma, and
small "projection batteries" (tactic cascades; hand-rolled commute
lemmas only for the structurally recursive list helpers and folds)
relate the pair's components to the plain instantiations.

* **Fuel monotonicity** (`Verify/Mono.lean`): `PairM` at
  success-refinement between two `CheckM` runs + one knot induction
  gives `whnfCore/whnf/infer/defeq/annotate/ensureSort` monotonicity.
* **Cache simulation** (`Verify/Bridge.lean`): `FueledM` packages
  monotone fuel-indexed families; `CacheOK` backs every cache entry by
  a pure run at one fuel valid at *every* depth at which the key is
  well-scoped (see *Depth-free memo keys*); `simRel` (families vs.
  `StateT KCache` computations) is `bind`-closed via monotonicity,
  `memoE`/`memoB` wrapper lemmas + a knot induction give: under
  `EnvWF env` (a hypothesis, not a runtime check — see *Depth-free
  memo keys*), every successful `cachedOps` entry-point run is
  reproduced by the pure knot at some fuel.
* **Declaration checker** (`Verify/BridgeDecl.lean` +
  `Model/BridgeWF.lean`): the checker is monad-polymorphic over
  `CheckerOps m`; `bridgeRel` (families vs. plain `CheckM`) + the
  ops-record pairing against the conditional comparand `wfOpsM` +
  batteries over every declaration-checker function yield
  `checkDecl_wfOpsM_bridge` (unconditional), and `Model/BridgeWF.lean`'s
  `checkDecl_bridge`: under `EnvWF env`, a successful
  `checkDecl cachedOps` step is reproduced by
  `checkDecl (fueledOps F)` for some fuel.

The consistency layer is stated fuel-generically (`fueledOps F`;
`pureOps = fueledOps checkFuel`), so `Setlec/Model/ConsistencyC.lean`
concludes by a per-declaration fold interleaving `EnvModel.wf` (which
discharges the bridge's `EnvWF` hypothesis), the bridge, and
`checkDecl_sound`: **every environment the executable accepts has a
model** (`checkDeclsC_sound`), and the executable never accepts a
proof of `Empty` (`no_proof_of_Empty_C`).  If the pair-monad batteries ever get
unwieldy, `mvcgen` (Lean's verification-condition generator for
monadic programs) plus precondition-carrying high-level combinators is
the designated fallback.  Both `_model` declarations and real Lean
terms are DAGs sharing subterms; every traversal must eventually be
memoized under a cached-hash representation, tracked as follow-up
work.

### Depth-free memo keys and depth invariance (2026-08-21)

Memo keys carry **no binder depth**: `KCache` maps `whnfCore`/`whnf`/
`infer`/`annot` under the expression and `defeq` under the pair, so
the same subterm reached under different binder contexts hits one
entry.  The mathematics behind this is **depth invariance**
(`Setlec/Verify/Deep.lean`): every core entry point returns the same
result at any two depths at which its inputs are well-scoped
(`whnfCore_depth_inv`, `whnf_depth_inv`, `inferTypeCore_depth_inv`,
`isDefEqCore_depth_inv`, `annotateCore_depth_inv`, all under `EnvWF`).
The proof is a shift bisimulation: the run at depth `d` is matched
against the run at depth `d+1` on `shiftFrom p` of the input (all
`fvar` indices `≥ p` bumped by one, `p ≤ d`); one claim per entry
point (`ShiftClaims`), one commutation lemma per record-parameterized
helper body at the same fuel, one fuel induction at the knot — then
`p := d` plus `shiftFrom_eq_self` collapses the bisimulation to a
depth bump, chained across any gap.  The syntactic commutation kit
(`shiftFrom` vs. `instantiate1`/`abstract1`/level instantiation/spine
operations/the scope guards) lives at the end of
`Setlec/Verify/Shift.lean`.

Depth invariance holds only for well-scoped inputs under well-formed
environments.  **Neither half is checked at runtime** (principle,
owner ruling 2026-08-21: *never add boolean checks for what is proven
to hold*):

* The environment half: the executable always runs the memoized knot,
  and `EnvWF` is a *hypothesis* of the bridge, threaded down from the
  model invariant `EnvModel.wf` — the checker only ever calls the core
  on environments it built itself, and `checkDecl_sound` proves those
  have models.  (An earlier `Env.wfB` boolean gate — one `O(|env|)`
  walk per top-level entry-point call — was deleted, task #42.)
* The scoping half (task #43): the memo operations
  (`memoE`/`memoB`) consult and fill the caches **unguarded** — the
  earlier per-op `wscopedB` key walks (O(key size) each) are deleted.
  Soundness comes from the proven **call discipline**: every core
  body, run at the cached record on well-scoped inputs, only ever
  invokes the record on well-scoped arguments at the ambient depth.
  The proof (`Setlec/Verify/Scoped.lean` + `Setlec/Verify/Disc.lean`)
  is one `DiscV` walk per body/helper exhibiting a disciplined cached
  run as verbatim a run at the *guarded* verification-only record
  `gFns` (each entry wrapped in a `wscopedB` test that throws) — to
  which the pair battery applies unconditionally (`gFns_rel`); the
  scoping of intermediate values flows from the conditional simulation
  (`ScopedSim`) plus the pure preservation lemmas
  (`whnfCore_WScoped` and friends), the scoping of syntactically
  constructed arguments from the `WScoped` toolkit — the same
  per-site facts the depth-invariance bisimulation established, with a
  one-sided conclusion.  The base case is the checker's own input
  validation: raw declarations are checked closed
  (`looseBVarsBounded 0`/`hasFvar`) before any operation call, at
  depth 0 closedness *is* well-scopedness.  Additionally (owner
  refinement, 2026-08-21) the `fvar` cases of `inferBody` and
  `annotateBody` fail hard unless `idx < depth` — an O(1) check at a
  leaf of a traversal that happens anyway, never a fresh walk — so a
  dangling free variable is rejected inside the passes raw input flows
  through, and inference/annotation success implies well-scopedness
  for the calls the checker makes.  The scope guards on
  checker-fabricated terms (stuck-major rescues, projection
  eliminations in `Setlec/Kernel/Core.lean`) stay: they validate
  freshly constructed terms once per fabrication.

Concretely: the per-entry-point simulation is the *conditional*
`ScopedSim` (one knot induction, `scopedSim` in
`Setlec/Verify/Bridge.lean`), and the entry-point bridges
(`cachedOps_*_bridge`) take `henv : EnvWF env` *and* the argument's
`wscopedB` at the call depth.  The declaration-checker comparand
`wfOpsM` (`Setlec/Verify/BridgeDecl.lean`) conditions per call on
`EnvWF env ∧ wscopedB`; since the condition is now per-argument, the
former wholesale function-level rewrites became run-level implications
(`Setlec/Verify/BridgeWfImp.lean`): per declaration-checker function,
a successful `wfOpsM` run over a well-formed environment is the pure
`fueledOps` run, with the per-site scoping facts read off the
checker's guards, the preservation lemmas, and scoping of the
iota-theorem check's opened telescopes (`openPisAtFvars_WScoped` and
friends; also the `natOpEquations`/`substConst0` scoping lemmas).
`Setlec/Model/BridgeWF.lean` composes these with the intermediate
`EnvWF` facts into `checkDecl_bridge`, and
`Setlec/Model/ConsistencyC.lean` is unchanged: the top-level
statements (`checkDeclsC_sound`, `no_proof_of_Empty_C`,
`no_proof_of_Empty_input_C`) keep exactly their strength —
acceptance by the executable, no side conditions.

`CacheOK` (now in `Setlec/Verify/Scoped.lean`) still backs an entry
`e ↦ r` by `∃ F, ∀ d, e.wscopedB d → run F d e = .ok r`: inserts
establish the universal form from the run at the ambient depth (whose
well-scopedness the discipline supplies) via the invariance theorems,
hits consume it at their own depth.  Numbers for the guard removal
(tutorial arena, fresh builds at the same base, best of 3): suite
26s → 24–25s; 043_rbTreeDef 1.52s → 1.42s; 069_rbTreeRef
1.53s → 1.42s; 080_RBTree.id_spec 1.55s → 1.43s; 120_rTreeRec
0.96s → 0.90s — a consistent ~6% per-test win (the guard walked every
key per memo op, but hashing already walked it; the leaf scope checks
cost nothing measurable).

### Inference re-checks: possibly-Prop-gated (2026-08-22, task #49)

The official kernel's inference is *infer-only* inside reduction
(argument checks ran once, at declaration time; lean4lean's `inferApp`
walks the Π-telescope with no per-argument checks).  Setlec's
`inferBody` app rule (and the interned spine loop `inferSpineI`) now
runs the argument re-check (infer + defeq against the domain) **only
when the Π's codomain-sort annotation is not provably nonzero**
(`codNonZero`, `Level.isNonZero` on the instantiated annotation — an
all-assignments guarantee).  At a provably nonzero Π the soundness
claims recover `⟦a⟧ ∈ ⟦domain⟧` from the app node's own `AnnotOk`
slot by *domain determination*: the function's value sits both in the
Π-type's interpretation (a `pi` at a nonzero sort, whose members are
graphs — `eq_graph_app_of_mem_piSet`) and in the slot's existential
pi, and graphs determine their domains (`graph_dom_of_mem_piSet`);
the mismatched-level case is vacuous (`graph_ne_pt`).  At a
possibly-Prop Π (`Sort u` codomains included: the claims quantify
over *every* level assignment, and at `u := 0` the interpretation
collapses to the proof point) **no semantic invariant can recover the
membership** — impredicativity, the same analysis as the beta
certificate — so the defeq re-check stays exactly there; this is the
minimal-cert residue, a finding, not an oversight.  The λ-annotation
re-check (against the body's inferred sort) is unchanged.  Measured
in isolation (init-prelude probe): 284.8 G → 272.2 G instructions
(−4.4 %), 24.6 s → 23.4 s; verdicts identical (arena 90/92, e2e
46/46, probe exit 0 / 3653).  The speculative-inference-cannot-reject
property is correspondingly strengthened on gated slots and unchanged
on the possibly-Prop residue.

### Finding: the possibly-Prop infer residue is not removable (2026-08-23, task #73)

Task #73 proposed dropping the residual checks at possibly-Prop-*codomain*
slots too, restating the internal claims disjunctively per level
assignment: either the strong membership fact, or φ collapses the
subject's type-sort to `Prop` (the subject interprets to the proof
point).  The collapse branch itself *is* nearly free — the
interpretation is already annotation-directed to `pt`: `lam 0 A F =
pt` (`lam_zero`), `app pt a = pt` (`app_pt`), members of `pi 0`/truth
values/`univ 0`-members are `pt` (`mem_pi_zero`, `mem_univ_zero`), and
`sfst pt = pt` — so app/proj/letE cases *propagate* a collapsed claim,
and the app case could even dispatch semantically per φ (nonzero
codomain-sort evaluation → domain determination exactly as the `#49`
gate branch; zero evaluation with the argument's value in the domain,
by classical case split → the strong fact via the `pi_zero`
all-fibres-inhabited characterization).  The residue would survive
only as the case "argument value off the Π's domain".

**Why it cannot go**: the check is not only a membership check — it is
the guard that keeps inference *outputs* (the instantiated codomains
`body[a]`) inside the invariant-carrying fragment.  The strong branch
of the infer claims delivers `AnnotOk t` and the interpretability of
`t`; at an off-domain argument the output type is junk (its binder
annotations need not be truthful, its interpretation is unrelated to
any fibre), and there is no collapse-branch statement about `t` that
is both provable at the emission site and usable by consumers.  Every
consumer that runs checker chains *on inferred types* needs those
type-side invariants as hypotheses of the mutual claims: the retained
possibly-Prop **beta certificate** (its soundness identifies
`⟦inferType a⟧` with the λ-domain via the defeq claims — impossible
without the argument's strong branch), the **iota certificates**'
telescope fit (`certs_fit`), the **λ-rule**'s body-type/annotation
re-check chain, and `proofIrrel`'s sort-certification chain
(`sortCert_pt`).

**Countermodel** (falsifies `WhnfCoreClaims` as stated, before any
restatement of the infer claims): in any modeled environment
containing `True`, `False` and `g : False → False := fun h => h`,
take the fabricated redex

    (λ x : False. ∀ z : x, True)  (g True.intro)

with codomain-sort annotations `0` throughout.  All claim hypotheses
hold: it is closed, and `AnnotOk` is satisfiable — the λ-clause is
vacuous over `⟦False⟧ = ∅`, and the app slots are the existential
`vf ∈ pi 0 A B ∧ va ∈ A` clauses, satisfied with `vf = pt` (both
`⟦g⟧` and `⟦λ…⟧` are Prop-λs, hence `pt`) at suitably chosen
truth-value sets: at `Prop`, `pi`-membership does not determine the
domain (impredicativity), so the slot cannot see that `True.intro` is
fed to a `False`-expecting function.  Without the residue,
`inferType (g True.intro)` succeeds with `False`, the beta
certificate's `defeq (inferType a) ty` compares `False` with `False`
and **passes**, and the redex reduces — but `⟦redex⟧ = app pt pt =
pt` while `⟦∀ z : (g True.intro), True⟧ = pi 0 pt (λ_. ⟦True⟧) =
truthVal True = unitSet ≠ pt`: the interp-equality conclusion is
**false**.  With the residue, the same run positively rejects inside
`inferType` (`defeq True False` fails), the certificate propagates
the throw, and the claim is vacuous — exactly the pre-#73 status.
The reduct re-enters *type*-land (a Π formed over a junk proof), which
is why the pt-collapse intuition ("the collapsing φ trivializes the
subject's claim") fails: Prop-collapse of the redex does not collapse
the *reduct*, whose interpretation is a truth value, not the point.

No claim-shape fix exists within the design: weakening the whnf/defeq
claims to tolerate the drift cascades into the final membership
transport of `checkDecl`, whose refutation of the drift branch would
need the unformalized "reachable from annotate-checked input"
invariant — i.e. subject-reduction metatheory (plus
sort-substitution-stability of inference for the λ-rule consumer),
exactly what the annotation design exists to avoid; and `AnnotOk`'s
app slot cannot be strengthened to pin a Prop-function's domain, since
at `Prop` values do not determine domains (the same impredicativity
analysis as the beta certificate).  The official kernel checks nothing
here because its internal terms are well-typed by subject reduction;
setlec's residue is the annotation-design's price for skipping that
metatheory, and is hereby established as *necessary*, not an
oversight.

**Measured bounty** (kernel-only A/B probe, committed and reverted on
the task branch; `perf stat` instructions, best of 2; verdicts
identical everywhere — arena 90/92, e2e 48/48, equal accepted-count on
both probes, both modes): `repro-extract-proof11-pre` default
184.7 G → 173.9 G (**−5.9 %**), `init-sizeof` default 193.4 G →
164.2 G (**−15.1 %**); the NC mode is unchanged (135.9 G / 147.1 G —
it already skips the site), so the numbers are also the current
measure of this residue's engineering-quality tax.  Worth revisiting
only together with genuine syntactic metatheory or a
certified-redex/argument cache.

### Possibly-Prop-gated iota certificates (2026-08-23, task #71)

`iotaRec`/`iotaRecI` certify their two telescopes (the recursor's, on
`args.take mI ++ [major]`, and the constructor's, on the major's
spine) with the **gated** `iotaCertsG`/`iotaCertsGI`: a slot whose
codomain-sort annotation is provably nonzero (`codNonZero`) runs *no*
per-fire infer+defeq — the soundness claims recover the argument's
domain membership from the redex's own annotated application chain by
domain determination, exactly as the task-#49 infer-app gate — while a
possibly-Prop slot keeps the check (the load-bearing residue, task
#73; never remove it).  `certs_fit` gains the gated sibling
`certsG_fit` (Model/Core/Certs.lean), which produces the same
`TeleFitI` from two extra semantic inputs available at both fire-path
call sites: the head value's membership in the telescope's
interpretation (`EnvModel.mem_type` for the stored recursor resp.
constructor) and the chain's `AppSlot`s (`annotOk_spine_inv` on the
redex resp. the — possibly rescued — major, whose `AnnotOk` comes from
`majorToCtor_claims`).  Per gated slot: the walked head value lies in
`pi (cod.eval φ) ⟦dom⟧ B` at a nonzero tag, hence is a graph over
`⟦dom⟧` (`pi_pos`, `eq_graph_app_of_mem_piSet`); the `AppSlot` puts
the argument's value in *some* pi domain containing that same
function value, and graphs determine their domains
(`graph_dom_of_mem_piSet`; a zero-tagged slot pi is vacuous — its
members are the proof point, `graph_ne_pt`).  The invariant steps by
`app_mem` through the annotated fibres.  Kept as runtime checks (their
facts feed the #58 fold-clause interface and are not present in any
annotation invariant): the plain-rule level linking, the
constructor-parameter `defEqList`, the canonical-index `defEqList`,
and the `stripPis` arity pins.

**Synthetic spines keep ungated certificates.**  A checker-fabricated
spine has no annotated application chain to recover memberships from,
so the structure-eta, unit-like and projection telescope certificates
stay on the ungated `iotaCerts`, and the stuck-major rescue's
fabrications are now certified *inside* `majorToCtor` (relocated from
the fire path, where the gating would have starved
`majorToCtor_claims`): each fabrication branch pins
`(cvj.type.stripPis k).isSome` plus the spine arity and runs
`iotaCerts` on the constructor telescope against the fabricated spine
(`etaFabArgs` names the eta spine, shared between the fabrication and
its certificate — and keeps the walked proof goals inside the
splitter's simp budget; the majorToCtor walk proofs in
PairM/Fueled/Disc peel the outer casing by hand for the same reason).
`majorToCtor_inv` carries the new facts and `majorToCtor_claims` lost
its `hstripLen`/`hmcerts` hypotheses.

**The official `to_cnstr_when_K` type check is now explicit.**  The K
rescue's fabrication check (defeq of the major's whnf'd type against
the fabrication's inferred type — for `Eq` the endpoint condition) was
deliberately omitted while the ungated major-slot certificate implied
it; with that slot gated at nonzero motives the reference check is
load-bearing (arena `bad/098_ruleKbad` fires at `Eq.rec.{3,3}`) and
`majorToCtor`'s K branch performs it before `proofIrrel` (which stays
as the value-identification certificate), mirroring `majorToCtorNC`.

**Measured** (init-prelude probe `_tmp/perfcmp/
init-prelude.preprocessed.ndjson`, `perf stat` instructions, best of
3, baseline re-measured at the merge base): default (certified)
187.4 G → 176.4 G (**−5.8 %**), user time 13.7 s → 12.5 s; NC mode
141.9–143.1 G on both sides (unchanged — it already skips all fire
certificates).  Verdicts identical: arena 90/92 (bad/098 rejecting),
e2e 48/48, probe exit 0 / 3653 accepted both modes, scale.sh all
shapes PASS.  The delta is smaller than #49's toggle estimate
(−23.5 G on the 284.8 G pre-#50 baseline) because the interning and
bulk-instantiation work since then already removed most of the
telescope-walk cost the toggle measured; the remaining certified-vs-NC
gap (~34 G) is now dominated by the beta/infer possibly-Prop residues
and the letE/projection certificates.

### The certified structural-Nat fast path (2026-08-21)

`reduceNat` — sitting exactly where the official kernel's literal
acceleration sits in the whnf loop — reduces `Nat.pred/add/sub/mul/
pow/beq/ble` on literal arguments (arguments are whnf'd first, as in
the official kernel).  Soundness comes from *install-time
certification*: when a definition under one of these names is checked,
`checkDecl` verifies its defining recurrence equations by definitional
equality over fresh variables (`natOpEquations`, binder-free
constructor forms; `certifyNatEqs`), and positively rejects a
nonstandard definition.  Presence in the store is therefore the
certificate — there is no runtime flag and no reduction-time
re-check (a re-check would livelock: the certification's own
`pred zero` equation re-enters the fast path).  The environment model
carries the matching semantic clause (`NatOpsOk`: a stored definition
under one of these names satisfies its recurrences), discharged in the
`defnDecl` consistency case from the certification's defeq soundness
and consumed by the whnf claims via per-op meta-level induction over
the literal (`Setlec/Model/NatOps.lean`).  The `natOpGuard` reduction
guard additionally requires the dependencies (`sub`→`pred`,
`mul`→`add`, `pow`→`mul`,`add`) and, for the `Bool`-valued ops and the
pin-certified `div`/`mod`, the `Bool` constructors, all stored
level-monomorphic.  Bodies cannot be
pinned instead: elaborator output is `brecOn`-compiled and is *not*
definitionally equal to the plain `Nat.rec` spelling at stuck majors —
only the recurrence equations are.  `div`/`mod` land via pinned
declarations plus checked characterization certificates (see the
dedicated section); `gcd` and the bit operations
remain deferred; string literals have their own section below.  The `succ`-packing case of `reduceNat` reduces its
argument first (as `pred` and the binary operations do, and as the
reference kernels do): literals reach `Nat.succ` wrapped in
`OfNat`/instance towers, and a missed packing defeats the binary fast
paths downstream, which then delta-grind the `brecOn` below-tower
unarily (55296 levels at the `isValidChar_UInt32` scale — the former
init-prelude probe wall).

### Nat literals in the model (2026-08-20)

`natLitSupported env` pins the stored `Nat`/`Nat.zero`/`Nat.succ`
declarations (kinds, empty level parameters, exact annotated types,
via per-slot checks `natIndOk`/`natZeroOk`/`natSuccOk`).  Every literal
code path guards on it: `inferBody`/`annotateBody` lit cases,
`reduceNat`, and the lit-to-constructor major conversion
(`litToCtorIfNat` takes the env).  The model interprets
`.lit (.natVal n)` as `natLitVal` — the `Nat.succ` value iterated on
the `Nat.zero` value — under the same guard; numeral membership in the
`Nat` value falls out of `EnvModel.mem_type` alone
(`Setlec/Model/NatLit.lean`), with no `Nat`-specific model fields.
`constsResolve` counts a literal as referencing the three `Nat`
constants (interp stability under environment extension needs their
presence), and the env-relating lemmas (`interp_env_ext`,
`AnnotOk.env_ext`, `TeleFit.env_levelext`) carry the guard across
explicitly (`natLitSupported_cons_recRules` for the recursor-rules
swap the install proofs perform).

### String literals (2026-08-22)

A string literal unfolds on demand to the reference kernels' exact
constructor spelling (`strLitToConstructor`, mirroring lean4lean
`Expr.strLitToConstructor` and nanoda `str_lit_to_constructor` at this
toolchain):

    String.ofList (List.cons.{0} Char (Char.ofNat (lit c₁)) (… (List.nil.{0} Char)))

`String.ofList` and `Char.ofNat` are ordinary *definitions* in the
stream (at v4.29 `String` is the ByteArray-backed structure with
constructor `String.ofByteArray`), so the expansion is not itself a
constructor form; wherever the references reduce after expanding, so
does setlec.  The pinned names `String`/`String.ofList`/`List`/
`List.nil`/`List.cons`/`Char`/`Char.ofNat` are an acceptable core pin
per the `Nat`-literal precedent (`natName` etc.); the core stays
otherwise basis-generic.  Use sites, each mirroring the references:

* `inferBody`/`annotateBody`: a literal types as `String` (the
  references' `Literal.typeName`); the literal itself is annotation-
  and shift-invariant.
* recursor majors (`litMajorToCtor`, in `iotaRec` next to
  `litToCtorIfNat`): a string-literal major becomes
  `whnf (strLitToConstructor s)` — the references re-reduce because the
  expansion's head is a definition (lean4lean `Inductive/Reduce.lean`,
  nanoda `str_lit_to_ctor_reducing`).
* projection scrutinees (`projLitToCtor`, in the `.proj` whnf clause
  between the scrutinee whnf and the projection-table match): a
  string-literal scrutinee becomes `whnf (strLitToConstructor s)` —
  the references' `reduce_proj_core` step (official
  `type_checker.cpp:383-384`, lean4lean `TypeChecker.lean` proj
  clause, nanoda `tc.rs` `reduce_proj`), completing all five official
  literal sites (task #52).  NOTE: for *annotated* input this site is
  unreachable — annotate rewrites every template-entry projection into
  the installed projection recursor (native `.proj` nodes exist only
  for the pinned `PSigma'` basis, whose scrutinee can never be a
  `String` literal on well-typed input), so a stream-level
  `.proj String 0 "s"` is in fact forced through the *rec-major*
  expansion above (e2e `str_proj.ndjson`, the
  `String.utf8ByteSize_empty` shape, is accepted through that route
  even without this site).  The site is kept for reference-exact
  reduction on the raw core and as the load-bearing step should native
  projection entries ever extend beyond the pair basis.
* `defeqBody` stuck phase: a literal against a *unary application of
  the bare `String.ofList` constant* expands and recurses — exactly the
  references' `tryStringLitExpansion` shape test, no more (lean4lean
  `tryStringLitExpansionCore`); literal-vs-literal was already decided
  by `BEq`.  (No interning back and no accelerated `String` operations:
  the references have none in the kernel.)

Guarding deviates from the references in one deliberate way: they only
check *existence* of `Char.ofNat`/`String.ofList`; `strLitSupported`
additionally pins the seven constants' level parameters and exact
annotated types (`stringTyOk` … `charOfNatTyOk`, plus
`natLitSupported` for the character numerals) — the shape facts the
model reads the literal's meaning off, in the spirit of the
`Nat`-literal guard.  A string literal in the input while the guard
fails is a *positively detected* unsupported feature: `annotate`/
`infer` decline (exit 2), unlike the `Nat` case (whose basis is always
pinned-installed, so absence is invalid input).  Inside `whnf`/`defeq`
an unsupported literal simply stays stuck (sound; unreachable for
annotated input).

Model: `.lit (.strVal s)` interprets as `strLitVal` — the value-level
reading of the constructor form, each pinned constant valued exactly as
the `.const` clause values it on that form (`List.nil`/`List.cons` at
their own stored parameter instantiated to `0`,
`Env.levelParamsAt`).  `interpExpr_strLitToConstructor` identifies the
form's interpretation with the literal's, so reduction may switch
representations; membership of the value in the `String` value and
truthful annotations (`AnnotOk`) of the form derive from
`EnvModel.mem_type` and the guard's shape facts alone
(`Setlec/Model/StrLit.lean`, mirroring `Setlec/Model/NatLit.lean`; the
syntactic closedness facts live in `Setlec/Verify/StrLitExpr.lean` —
the expansion is a closed term, which keeps the Deep/Disc walks easy).
`constsResolve` counts a string literal as referencing the ten support
constants, and the env-relating lemmas carry the guard across like the
`Nat` one (`strLitSupported_cons_recRules`, `strLitSupported_env_ext`
— the type pins read stored constants only through `toConstantVal`, so
kind-preserving lookup changes transport).

Reference-comparison findings (string-literal survey, 2026-08-22;
official = v4.33/v4.35, byte-identical in the relevant code):

* **D1 — unvalidated primitives.**  The official kernel builds and
  *uses* the expansion whatever `String.ofList`/`Char.ofNat` happen to
  be declared as (no environment check at all; infer of a literal is
  env-blind, `type_checker.cpp:301`), and nanoda checks existence
  only.  A stream may declare `String.ofList` at an arbitrary type and
  official still expands `"s"` to an application of it inside
  defeq/iota/proj.  lean4lean closes this at declaration time
  (`Primitive.lean:443-461` defeq-checks the types, hard error on
  mismatch); setlec's `strLitSupported` closes it at use time.
  Candidate adversarial-prelude unsoundness report against the
  official kernel (same family as the Nat-op acceleration concerns).
* **D2 — nanoda ignores levels on `String.ofList`** in its defeq
  string expansion (`tc.rs:302`, name-only match, "levels should be
  empty" comment) where official/lean4lean require the whole constant
  `== String.ofList []` — possible verdict divergence on a stream
  declaring `String.ofList.{u}`.
* **D3 — no common reference verdict for a literal in an impoverished
  environment.**  Typing (never forcing) a literal without
  `Char.ofNat`/`String.ofList`: official ACCEPTS (env-blind infer),
  lean4lean REJECTS (`env.get` throws in infer), nanoda
  panics/config-rejects.  Setlec's decline (2) is a fourth behavior,
  already ratified above; there is no single reference verdict to
  match.
* **D4 — the proj expansion site** was setlec's one missing reference
  site; now landed (`projLitToCtor`, above).  Contrary to the survey's
  initial verdict-relevance claim, setlec's annotate-time projection
  rewrite means the rec-major site already covered stream-level
  string-literal projections (the 86 literal-forcing Init theorems
  reduce through the projection recursor), so landing it changed no
  verdict on annotated input; it restores site-for-site reference
  parity of the reduction strategy.

### Certified structural-Nat fast path (2026-08-21)

`reduceNat` computes `pred/add/sub/mul/pow/beq/ble` on literal
arguments (`natOpResult`), guarded by `natOpGuard`: `natLitSupported`,
every dependency (`natOpDeps`, always including the op itself) stored
as a level-monomorphic `defnInfo`, and for `beq`/`ble` the `Bool`
constructors stored monomorphically.  *Presence in the store is the
certificate*: `checkDecl`'s defn arm certifies each op at install and
positively declines nonstandard definitions under these names, so the
reduction needs no runtime re-check (which would livelock anyway).

The certification runs in the **pre-insertion** environment on the
recurrence equations (`natOpEquations`) with the op's self-references
replaced by the stored annotated value (`Expr.substConst0`).  Two
reasons, both load-bearing:

* **Soundness.**  Certifying post-insertion (const-headed equations in
  the extended env) lets the op's own just-enabled fast path discharge
  its all-literal-argument equations vacuously (`pred zero`,
  `beq zero zero`): a definition standard except at `beq 0 0` would be
  accepted, after which `beq 0 0 ≡ true` (fast path) and
  `B 0 0 ≡ false` (delta on the literal body `B`) are both certifiable
  `rfl`s — a checkable proof of `False`.
* **Non-circularity of the model.**  The certification's soundness is
  discharged with the *previous* environment's model
  (`isDefEqCore_sound`); dep fast paths that fire during the run are
  covered by the previous `nat_ops` invariant.  Post-insertion
  certification would need the extended model that is being built.

The install additionally pins the op's and its deps' stored types to
`Nat → … → Nat`/`Bool` (`natOpTyPinned`/`natOpStoredOk`; codomain-sort
annotations `≈ 1`, `Bool` itself monomorphic at `Sort 1`): the model
reads the operations' function-space memberships off these shapes
(`mem_type` + `natOpTyPinned_interp`), which is what makes `AnnotOk`
of the certification equations derivable.

Model side: `EnvModel.nat_ops : NatOpsOk` states that every stored op
satisfies `natOpGuard` and its recurrence equations semantically (at
every level assignment, over members of the `Nat` value).  Established
in the defn install case (`natop_eqs_sound` + `interp_substConst0`
converting value-headed old-env equations to const-headed new-env
ones); preserved by `NatOpsOk.cons` (guard names are stored, hence
fresh-distinct) and `NatOpsOk.cons_recRules` (the recursor-rule-patch
constructions).  Consumed by `reduceNat_sound`
(`Setlec/Model/Core/Whnf.lean`): the whnf claims give the arguments'
literal values, `Setlec/Model/NatOps.lean`'s meta-level inductions
(`natOpVal_*`) compute the op on `natLitVal` values from the
recurrences.  WF-recursive ops (`div`, `mod`, `gcd`) and string
literals remain deferred.


### Certified `Nat.div`/`Nat.mod` via pinned declarations (2026-08-21, task #47)

The WF-recursive `Nat.div`/`Nat.mod` (fuel-compiled in core: a
`dite (0 < y)` dispatcher over a `brecOn`-on-fuel worker) get the
literal fast path through **pinned declarations plus checked
characterization certificates** — never by grinding the fuel recursion
on literals.

* **Pinned defining expressions.**  An *elab-time* generator
  (`Setlec/PinGen.lean`, see "Elab-time pin generation" below — run
  against the toolchain's own prelude at `lake build` time, nothing
  hand-transcribed and nothing vendored) reads `Nat.div`/`Nat.mod`
  from the compiling environment and delta-unfolds every local helper
  (`Nat.modCore`, `Nat.modCore.go`, `Nat.div.go`, matchers, `._f`
  functionals) into one closed expression per op over stream-present
  ground constants (non-prefix *definitions* are inlined too, e.g.
  `and`), spliced with hash-consed `let`-sharing into
  `Setlec/Kernel/NatOpPins.lean`.  At install (`checkDivModPin`,
  after the ordinary definition check) the stream's stored value is
  compared against the pin by **definitional equality** (one
  `isDefEq` at depth 0) — robust to helper factoring/naming drift
  (the 4.29-exported stream matches the 4.33-generated pin), while
  a semantic change **declines** (exit 2, "unsupported Nat.div/mod
  spelling"): elaborator drift surfaces visibly, never silently.  The
  stored body stays a transparent, ordinary definition — nothing
  opaque, no input theorem bypassed.

* **Checked characterization certificates.**  Per op, three pinned
  statements characterize it against already-certified ground — the
  guards are spelled with `Nat.ble` (never the `Nat.le`/`Nat.lt`
  `Prop` inductives) and the numeral `1` as `Nat.succ Nat.zero`, so
  the model side rides the existing `NatOpsOk` literal semantics:
  `ble y x = true → ble 1 y = true → c x y = c (x-y) y (+1 for div)`,
  `ble y x = false → c x y = base`, `ble 1 y = false → c x y = base`
  (`base` = `0` for `div`, `x` for `mod`).  The statements are pinned
  in *open* form (`divModCertStmts`: hypothesis types over
  `x := fvar 0`, `y := fvar 1`); the **proof terms** are generated by
  the same generator — elaborated against real core with controlled
  dependencies (no `simp`/`decide` steps: core's own `Nat.mod_eq`
  proof mentions `eq_true`/`and_self` and hence `Iff`/`propext`,
  which do not exist in the stream before `Nat.mod`; instead
  fuel-congruence and one-step `eq_def` unfoldings are reproved from
  scratch), then closed over the stream prefix by inlining every
  constant that is not declared before the op in the stream (the
  allowlists are extracted from the supported streams — intersected
  per op — by `scripts/extract_natop_prefix.py` into
  `scripts/natop_prefix.json`; a non-prefix *inductive* aborts
  generation loudly, i.e. fails the build).  At install each
  certificate is checked exactly
  like a theorem over an opened telescope — the generated proof,
  self-references substituted with the stored annotated value
  (pre-insertion, like the structural-Nat certification: post-insertion
  the op's own just-enabled fast path would participate in checking
  the very certificates that justify it), is applied to the statement
  frame's `fvar`s, annotated, inferred, and its type compared against
  the pinned equation — and **not installed**.  Missing ground
  constants (a stream stopping short) decline; a certificate failure
  *after* a pin match is an internal inconsistency (exit 3).  The
  separation of roles: the **certificate check** justifies the fast
  path semantically; the **pin defeq** is only the gate that makes
  certificate failure a genuine internal error instead of an expected
  path.

* **Capability = presence.**  As with the structural ops, the env
  stores no runtime flag: a stored `Nat.div`/`Nat.mod` *is* the
  capability, because the install path declines or errors otherwise.
  `reduceNat`'s certified binary branch covers `div`/`mod` under
  `natOpGuard` (deps `pred`/`sub`/`ble` + the op itself, and the
  `Bool` constructors); a *capless* literal application (op absent or
  guard failing — nearly unreachable, since a mismatching declaration
  already declined at install) is caught by the `natOpWfNames` safety
  net and declines rather than grinding the fuel recursion unary.
  Helper definitions (`modCore`, `go`, …) applied to literals reduce
  *honestly* by ordinary structural reduction, exactly like the
  reference kernels.

* **Model side.**  `EnvModel` gains `div_mod : DivModOk`: a stored
  pin-certified op satisfies its `ble`-guarded recurrences at the
  *value* level (`DivModEqs` — expression-free, so environment
  transports only move the guard/lookup side).  Established in the
  `defnDecl` case from the certificate runs
  (`Setlec/Model/DivModCert.lean`): the certificate frame's valuation
  puts the proof point at the hypothesis variables, so inhabitation of
  the interpreted guard types is exactly the semantic guard equality
  (`pt_mem_eqv_self`); annotate/infer soundness gives the applied
  proof's membership in its inferred type, defeq soundness identifies
  it with the pinned equation's value computed through the pinned `Eq`
  (`eqVal_app₃`, over the depth-generalized `EqSideOk` machinery), and
  `mem_eqv` closes — the vendored proof blobs stay completely opaque
  to the model.  Consumed by `reduceNat_sound` through the once-per-op
  uniqueness lemmas (`natOpVal_div`/`natOpVal_mod`): strong induction
  over the literal, with the guards computed by `natOpVal_ble` and the
  step by `natOpVal_sub`, pins the op's value on literals to the
  metatheory's own `Nat.div`/`Nat.mod`.

### Elab-time pin generation (2026-08-22, task #53)

The vendored pin blobs of task #47 are replaced by **generation at
`lake build` time**: `Setlec/PinGen.lean` provides `ToExpr` instances
for the checker's `Name`/`Level`/`Expr` types, the helper-unfolding and
prefix-closure machinery, and a command elaborator `#gen_natop_pins`
that `Setlec/Kernel/NatOpPins.lean` invokes.  The command reads each
pinned operation and its certificate proofs (theorems in
`Setlec/PinGen/Certs.lean`, elaborated against the real toolchain
prelude) from the build's own oleans, closes them over the stream
prefix, and splices `nat…DeclPin : Expr` / `nat…CertProofs : List Expr`
into the invoking module as kernel-checked, compiled definitions with
hash-consed `let`-sharing (a memoized builder; the plain `ToExpr`
instances would lose all sharing).  An out-of-prefix dependency is a
hard build error.  Contract points:

* **Statements are the interface.**  The certificate *statements* stay
  hand-pinned in `Setlec/Kernel/Checker.lean` (`divModCertStmts`); only
  def pins and proof blobs are generated.  A toolchain bump regenerates
  those silently; the checker cares only that the pinned statements
  still check.  One pin and one proof list per op (no multi-variant
  lists — revisit only if two prelude spellings must be supported at
  once).
* **Layering via the module system.**  `Setlec/Kernel/Expr.lean`,
  `Setlec/PinGen/*.lean` and `Setlec/Kernel/NatOpPins.lean` are
  `module`s; `NatOpPins` reaches the generator through
  `meta import Setlec.PinGen`, so `Lean.*` stays out of the runtime
  import closure (the setlec binary grew ~2 MB for the pins data, not
  ~100 MB for libLean; checker runtime code never touches `Lean.*`
  APIs).  Because a `module`'s ambient environment strips imported
  theorem *proofs* (and `meta import all Lean` does not restore
  cross-package proofs — probed: `dif_pos` has no value there), the
  generator computes in a dedicated full-view environment
  (`importModules` at `OLeanLevel.private` over `Init` and the
  certificate module) and splices into the ambient one.
* **Prefix allowlists** (`scripts/natop_prefix.json`, from
  `scripts/extract_natop_prefix.py`) are checked-in generator *input*
  (an allowlist of stream-declared names, not a blob), extracted from
  the supported streams and intersected per op.  The install-time
  `constsResolve` guards remain the actual gate; the allowlist only
  makes generation fail early and loudly.
* **StdAxioms pins** are small and stay vendored
  (`Setlec/Kernel/StdAxioms.lean`); basis blocks (`PSigma'` …) are
  preprocessor-owned and out of scope for the generator.

### The remaining GMP `Nat` operations (2026-08-22, task #54)

The official accelerator whitelist's seven remaining operations —
`Nat.gcd`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`,
`Nat.shiftRight`, `Nat.log2` — join the `div`/`mod` family (the
`natDivModNames` list, now nine operations; the name is historic).
Each follows exactly the pinned-declaration pattern: elab-time def pin
(defeq gate, mismatch declines), hand-pinned `ble`-guarded
characterization statements in `divModCertStmts`, generated proof
blobs checked pre-insertion, capability = presence, value-level
clauses in `DivModClauses` (per-op dispatch), once-per-op uniqueness
lemmas (`natOpVal_gcd` … in `Setlec/Model/NatOps.lean`, strong
induction over the literal), consumed by `reduceNat_sound`.

* **Statements** (all over the `x`/`y` frame; guards via certified
  `Nat.ble`; numerals as `succ`/`zero` chains):
  - `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`; `x = 0 → gcd x y = y`.
  - `shiftLeft`: `1 ≤ y → x <<< y = (2*x) <<< (y-1)`; `y = 0 → = x`.
  - `shiftRight`: `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`; `y = 0 → = x`.
  - `log2`: `2 ≤ x → log2 x = succ (log2 (x/2))`; `x < 2 → = 0`.
    `log2` is **unary**: the statements still quantify over both frame
    variables (`y` unused), so the certificate check, `checkDivModCerts`
    and the frame machinery stay uniform; only the *model* side
    branches (a unary `natOpTyPinned` shape shared with `pred`, a
    unary function-space membership, and `eqSide_app1` in place of
    `eqSide_app2` in the bridge).
  - `land`/`lor`/`xor` (`Nat.bitwise` at `and`/`or`/`bne`): the
    recurrence characterizes the operation **arithmetically** — the
    combined low bit is `(x%2)*(y%2)` for `and`,
    `x%2 + y%2 - (x%2)*(y%2)` for `or`, `(x%2 + y%2) % 2` for `bne` —
    `1 ≤ x → op x y = 2*(op (x/2) (y/2)) + bit`, with bases
    `x = 0 → land x y = 0` and `x = 0 → lor/xor x y = y`.  This keeps
    the statements over already-certified ground only (`add`/`sub`/
    `mul`/`div`/`mod`) — no `Bool` combinators, no `ite`, no
    per-bit-case guard explosion.

* **Certificate-proof constraints.**  The bit operations sit in the
  stream's `Init.Prelude` region — before `HAnd`/`AndOp`, `testBit`,
  `Trans`, `Subsingleton`, `Lean.RArray` even exist — so their proofs
  can use neither `omega` (RArray in the atom certificates), `calc`
  (`Trans`), the public bitwise lemma API (`HAnd` in the statements),
  nor the auto-generated `Nat.bitwise.eq_def` (its proof mentions
  `Subsingleton`).  Instead `Setlec/PinGen/Certs.lean` derives a
  one-step unfolding from `WellFounded.Nat.fix_eq` directly (via
  `delta`; WF definitions are irreducible) and finishes with
  elementary `Nat` rewriting.  The later ops (`gcd` at its stream
  position, `log2`) have `Iff`/`And`/`propext`/`Int` prefix-present
  and use ordinary core lemmas (`Nat.gcd_succ`, `Nat.log2_def`); the
  shifts are structural and their recurrences are `rfl`.

* **Uniqueness lemma shapes.**  `gcd`/`land`/`lor`/`xor`: strong
  induction on the first literal with the second generalized (step at
  `y % x` resp. `x/2`, `y/2`); shifts: strong induction on the second
  literal with the first generalized; `log2`: strong induction on the
  single literal.  The bit operations' metatheory-side recurrences are
  the *generator's own certificate theorems reused at the meta level*
  (`Setlec/Model/NatOps.lean` imports `Setlec.PinGen.Certs`); their
  guards are bridged with `Nat.ble_eq_true_of_le`.

* **Model plumbing.**  `DivModEqs` is now
  `∀ ψ x y ∈ Nat, DivModClauses val c ψ x y` with a per-op clause
  dispatch mirroring the pinned statements; `DivModEqs.val_congr` and
  `DivModOk.cons` are generic over the family (agreement at the
  `Nat`/`Bool` pins plus `natOpDeps c`, which by construction contains
  every operation a clause mentions).  The certificate bridge
  (`divmod_certs_sound`) is one nine-case proof over generalized
  clause extractors (`clause_extract1/2` now take the equation's
  left-hand side as an arbitrary `Nat`-typed spine).

* **Fixtures.**  `scripts/mk_natop_fixture.py` builds per-op e2e
  fixtures by *dependency-closure slicing* of the full-Init export
  (keeping the preprocessor's `_model` companion families and every
  pin/certificate ground constant, incl. those of pin-ops pulled into
  the closure), plus a literal `Eq.refl` use (accept) or a perturbed
  op body (decline); committed gzipped under `tests/e2e/`.

* **Findings.**  No operation resisted: all seven land with the
  ble-guarded defeq-checkable statement forms.  The full Init stream
  itself still does not check end-to-end for unrelated reasons
  (frontend memory on the 336 MB export; `Lean.trustCompiler` uses are
  declined by design — since the 2026-08-24 skip-and-continue as a
  whole-stream decline after skipping them; the `Unit.sizeOf` mismatch
  is fixed, see the basis `PUnit` rescue note) — the previous positive
  declines at `Nat.land`/`Nat.shiftRight`/… literal uses are gone.

### Theorem values delta-unfold (2026-08-22, task #66)

`unfoldDefinition` (and the interned `unfoldDefinitionI`/`constValAtM`)
unfolds *theorem* values exactly like definition values, at reducibility
hint `opaque` — the reference kernels' `is_delta` accepts any constant
with a value, and the official `constant_info::get_hints` gives theorems
`opaque` (so they unfold last, and a theorem-vs-theorem comparison at
equal opaque hints unfolds both sides with no spine shortcut).
Previously theorems never unfolded, which wrongly *rejected* the arena's
`good/undecidability/subject-reduction-redex`: its `x2 x4` application
needs `f 1 (proof_2 x0) ≡ f 0 (proof_1 x0)`, where `proof_2` is a
theorem whose value reduces to an `Acc.intro` application — without
unfolding it the `Acc.rec` iota step cannot fire and both sides stay
stuck with mismatched indices (`1` vs `0`).  (The test's outer
beta-redex is the transitivity trap: `f 1 x0 ≡ f 1 (proof_2 x0)` holds
only via the same-head spine shortcut + proof irrelevance on the `Acc`
argument — over-reducing that side breaks it — which the lazy-delta
`defeqSpine` shortcut already handled.)  Claims impact: `ConstWF` gains
a theorem-value clause (same four syntactic facts as definition
values), `EnvModel` gains `thm_ok` (a theorem constant is interpreted
by its proof value, which carries truthful annotations — established
by `extend_model` exactly as for definitions, since the valuation was
already the value's interpretation), and `unfoldDefinition_sound`
consumes either `defn_eq` or `thm_ok`.  E2e fixture:
`subject_reduction_redex.ndjson`.

With theorems unfoldable, the earlier deviation of keeping proof
irrelevance only in the stuck fallback (design-review triage) became
expensive: proof-typed comparisons delta-ground through proof bodies
before the fallback could fire (init-prelude probe 167.9 G → 227.3 G
instructions).  `defeqBody` therefore now runs `proofIrrel` right
after the `whnfCore` fast path and before lazy delta — exactly the
official kernel's `is_def_eq_proof_irrel` position — recovering to
205.2 G / 15.6 s; the residual ≈ +22 % over the pre-#66 numbers is
the price of actually performing the reference kernels' theorem
delta (majors and proof arguments now reduce where they used to stay
stuck).  The stuck-fallback copy stays (memoized) for sides rewritten
by a reduction step after the hoist ran.

### Memory blowups: DAG budget and OOM supervision (2026-08-22, task #65)

Findings from the arena `good/perf` OOM pair:

* `beta-ladder` (2000 nested `(λx. …) 0` redexes whose innermost body
  reads every binder) now **accepts** (~25 s, ~1.8 GB peak): the
  Θ(n²) substitution copies are inherent (each beta step re-interns
  the remaining ladder — the eliminated binder shifts every `bvar`
  below), and the single-tier arena *retains* all Θ(n²) reducts by
  design until #64's two-tier arena; at n = 2000 that fits.
* `app-lam` is a different beast: its `dag_app_binder` value is a
  `wrap2 f f` doubling tower — DAG size 24 001, **unshared tree size
  ≈ 10¹¹⁶⁰** — shared through *export-table indices*, not `let`s (the
  file contains no `letE` entry at all), so kernel letE support
  (task #79) does not reach it.  Every remaining tree-materializing
  pass (the raw syntactic checks, arena interning of `Expr` trees) is
  exponential on it; before the size budget the OOM happened already
  inside `parseExport` (the then-eager frontend zeta expansion).  This is exactly the `no-unmemoized-traversals`
  architectural gap (the raw-`Expr` pipeline walks trees), not a
  reduction-sharing bug.  Until the pipeline is DAG-preserving
  end-to-end, the frontend now tracks each expression-table entry's
  *saturated unshared tree size* (`State.sizes`, `O(1)` per entry) and
  **positively declines** any declaration whose tree size reaches
  `declTreeSizeBudget` (2^25) at its own record — beyond that scale
  the tree-materializing pipeline could not represent the declaration
  anyway, and every supported stream is far below it.
* Exit-code hardening: the Lean runtime's out-of-memory handler
  (`lean_internal_panic_out_of_memory`) prints `INTERNAL PANIC: out
  of memory` and calls `exit(1)` — in-process it is uncatchable, and
  exit 1 reads as *reject* under the arena convention.  `main` now
  supervises: it re-execs the checker as a child
  (`SETLEC_SUPERVISED` guard), and a child that exits 1 with a panic
  marker on stderr is reported as exit 3 (error).  Genuine rejects,
  declines and accepts pass through unchanged; abort-style deaths
  (stack overflow = 134, SIGKILL = 137) were never 1 and stay as-is.
  Known limitation: an external `timeout` killing the supervisor
  orphans the child; the arena harness kills process groups, and the
  in-repo scripts use `timeout` on the whole invocation.

## Kernel design review triage (2026-08-20)

A fresh-context implementation review compared the core against nanoda,
lean4lean (the faithful port of the official kernel) and the mini
checker (`_tmp/kernel-design-review.md`).  Disposition of its findings:

**Adopted immediately** (fidelity fixes):
* The structure-eta rescue is guarded against propositional structures
  (`piResultIsProp`), as in the official kernel.
* The K capability's Prop test normalizes the result sort
  (`Level.isEquiv` against zero) instead of comparing syntactically.

**Considered and reverted** (checks implied by machine-checked
invariants; no `.ndjson` reachability test is constructible, so the
checks are omitted — we verify the kernel and may rely on invariants
where other kernels re-check):
* `proofIrrel`'s common-type check (annotation-first discipline already
  forces both sides' types through the same checked chain).
* The K rescue's explicit fabricated-type check (then implied by the
  load-bearing iota certificates that ran on the fabrication;
  **reinstated by task #71** — with the fire-path certificates
  possibly-Prop-gated the implication broke and the official check is
  load-bearing again, see "Possibly-Prop-gated iota certificates").

**Adopted as part of the open-recursion core restructure**: the
`whnfCore`/`whnf` split with the official loop (`whnfCore → reduceNat →
unfold → repeat`) and its literal/quotient hook points; the syntactic
`a == b` fast path (pre- and post-whnf) in defeq; hoisting proof
irrelevance into the stuck-terms fallback.  The **infer-only** mode was
attempted and deferred (see "Inference re-checks" above); the early
proof-irrelevance hoist in defeq was reverted for fuel-depth reasons
(it stays in the stuck fallback).

**Deferred, tracked as tasks**: the lazy-delta extras — failure cache,
`tryUnfoldProjApp`, cheapProj (lazy delta itself landed, see below);
string literals; the performance substrate (cached hashes /
hash-consing, array spines, indexed environment, per-declaration cache
threading; the possibly-Prop-gated iota certificates landed with task
#71, see "Possibly-Prop-gated iota certificates" below); per-loop fuel
budgets; instrumenting the possibly-Prop beta wedge (3.5) as an
internal-error signal; removing the codomain-annotation comparison in
binder defeq (documented deviation, benign for well-typed input).
Task #49 measured (implementation-only toggles, init-prelude probe,
284.8 G baseline; proofs not landed, numbers inform the follow-ups):
possibly-Prop-gated *iota* certificates + comparand/index checks kept
−23.5 G (−8.3 %); lazy delta *materialization* in `defeqBodyI`
(probe both heads, unfold only the chosen side) −0.2 G — the
`(name, levels)` value cache already absorbs it, not worth the walk
rework; removing the possibly-Prop *beta* certificate −2.2 G — never
landable (unprovable, the impredicativity analysis above).  The
gated infer-app re-check (−4.4 % standalone) landed; see "Inference
re-checks" below.

## Kernel letE support: reference-style lazy zeta (2026-08-23, task #79)

The kernel handles `letE` natively, with **no local let environment**,
mirroring the current reference kernels site by site:

* **whnfCore zeta** — a `letE` head reduces by instantiating the body
  with the value on demand and continuing:
  official kernel `type_checker.cpp` `whnf_core`,
  `case expr_kind::Let: r = whnf_core(instantiate(let_body(e),
  let_value(e)), …)`; nanoda `tc.rs` `whnf_no_unfolding_aux`
  `Let { val, body, .. } => inst(body, &[val])` (spine args re-applied);
  lean4lean `TypeChecker.lean` `whnfCore'`
  `| .letE _ _ val body _ => save <|← whnfCore (body.instantiate1 val)`.
* **infer** — the type of a `letE` is the type of the instantiated
  body: nanoda `infer_let` (`inst(body, &[val])` then `infer`); the
  official `infer_let` at `infer_only` likewise derives the result with
  the let value transparent (valued let-fvars in its local context).
  As with the λ-annotation, the checks ran once, at annotate time, so
  `infer` performs none.
* **annotate** — the checking pass runs the official `infer_let`
  check sequence (`!infer_only` branch, `type_checker.cpp:200`):
  `ensure_sort(infer(type))`, `infer(val)`,
  `is_def_eq(val_type, type)`; then the *body is annotated with the
  value transparent, as its zeta reduct* — exactly nanoda's
  `infer_let` (`inst(body, &[val])` then recurse; the official kernel
  gets the same transparency from valued let-fvars in its local
  context, which setlec fvars cannot express).  Annotation therefore
  zeta-expands per-binder, on demand: the annotated output is
  let-free, and expansion runs on the interned arena where `inst1M`
  is sharing-preserving and `annotate` is memoized per node — the
  *checking* of a shared let tower is polynomial even though the
  eager frontend expansion it replaces was exponential.  **Finding
  (letE-preserving annotation rejected)**: annotating the body at an
  *opened opaque* variable of the annotation type — which would let
  the stored term keep its `letE` node — was implemented first and
  rejects real streams (`Nat.succ_le_succ` and 19 more e2e fixtures:
  elaborated `let` bodies rely on the value definitionally, and an
  fvar without a value loses `fvar ≡ value`).  Recovering it needs
  either a try-opaque-else-expand fallback (a `tryCatch` in a core
  body, restricted to `.invalid` errors to keep fuel monotonicity)
  or re-abstracting value occurrences from the expanded annotated
  body; both are future work if stored-`letE` compactness is ever
  needed.
* **Frontend** — parsed expressions keep their `letE` nodes (the five
  eager `zetaExpand` sites — declaration types, def/thm/opaque values,
  the recursor-rule rhs — are gone, and `Expr.zetaExpand` is deleted;
  the old plain-`Expr` expansion walked trees, exponential-time on
  shared let-values); the interned `inst1M` makes the kernel's zeta
  substitution sharing-preserving on the arena.  The unshared-tree-size budget
  (task #65) stays as the backstop for the *remaining*
  tree-materializing passes (raw-input closedness/consts checks, entry
  interning of `Expr` trees, post-annotate `allLevelParamsDefined`/
  `constsResolve` walks): a let-free DAG shared through export-table
  indices (arena `good/perf/app-lam`) still materialized as a tree in
  those passes and kept declining; task #78's parse-time interning
  (see its section) lifted this — `app-lam` now accepts and the budget
  is re-scoped to the remaining tree-materializing record kinds.

Model: `⟦letE n t v b⟧ρ = ⟦b[fvar_d]⟧(ρ, d ↦ ⟦v⟧ρ)` — valuation
extension, the same binder opening as `lam`/`forallE` (the fvar
annotation is never read), chosen over interp-by-substitution because
`interpExpr` recurses structurally (`sizeB`; instantiating the value
would break termination).  The substitution lemmas already built for
beta (`interp_beta`, `AnnotOk_beta`) identify it with the zeta
reduct's interpretation, so the whnfCore-zeta and infer claims are
exactly beta-shaped; the `AnnotOk` `letE` clause carries truthfulness
of the annotation and value, the value's interpretation, and
truthfulness of the opened body at it.  Since annotate emits let-free
terms, the whnf/infer `letE` cases and the model clauses are exercised
only on raw-shaped input; they are kept verified as the reference
kernels' strategy and as the substrate for a future letE-preserving
annotation.  The annotate soundness case itself is just the recursion
on the instantiated body (the type/value checks steer the verdict
only, for reference parity).

## Stuck-major rescue: rule K and structure eta in iota (2026-08-20)

`majorToCtor` (in the mutual core, mirrored in the cached twin)
implements `to_cnstr_when_K` and `to_cnstr_when_structure`: a
recursor's major premise that does not whnf to a constructor
application is *replaced* by a fabricated one.

* **K**: for a K-flagged inductive proposition (single-rule recursor,
  zero-field constructor), the constructor applied to the first
  parameters of the major's reduced type.  Checked (since task #71) by
  the relocated ungated constructor-telescope certificate on the
  fabricated spine, the official `to_cnstr_when_K` type comparison
  (defeq of the major's type against the fabrication's inferred type —
  the `Eq` endpoint condition; load-bearing with the fire path's
  major-slot certificate gated, arena `bad/098_ruleKbad`), and
  certified by `proofIrrel`
  — in the model both the stuck major and the fabrication are the
  proof point, so no `_model.ruleK` theorem is consulted; the
  `ruleK` capability is computed from shape at install exactly as the
  official kernel computes the `k` flag (inductive proposition, one
  constructor taking only the parameters) and pinned `true` on the
  basis `Eq`.
* **Structure eta**: for an eta-capable structure, the constructor of
  the major's projection functions, certified by the structure-eta
  certificate in its `With` form (`structEtaCertWith` takes the
  already-reduced type of the stuck side, so the certificate's facts
  are in terms of the rescue's own reduction — no fuel-determinism
  reasoning needed).  Projection-function recursors are excluded (the
  rescue's reduct would be the projection itself, looping reduction:
  a stuck projection stays stuck, as in the official kernel).

Fabricated majors carry a syntactic scope guard (`wscopedB` &&
`looseBVarsBounded` && leaf-subset, as in `annotateProjElim`), keeping
their well-scopedness verification local.  Soundness
(`majorToCtor_claims`, `Setlec/Model/Core/MajorToCtor.lean`) assembles
the fabrication's `AnnotOk`/interpretation from the constructor
telescope's iota certificates — since task #71 carried by
`majorToCtor` itself, ungated, on the fabricated spine (`certs_fit` +
`TeleFit.chainSlots` + `annotOk_spine`) — the reduced type's argument
spine, and (for eta) the projection certificates; the value
identification is proof irrelevance (K) or the stored eta law via
`structEtaWith_sound` (eta).

(Historical: until task #79 the frontend zeta-expanded every parsed
expression — the checker worked let-free — which duplicates shared
let-values exponentially; the kernel now has native `letE` support,
see "Kernel letE support" below, and the frontend passes lets
through unexpanded.)

### Basis `PUnit` 0-field rescue (2026-08-22, task #59)

The pinned `PUnit` block now carries `eta := true` (ctor `PUnit.unit`,
0 params, 0 fields), matching the official kernel's structure-rescue
eligibility — `to_cnstr_when_structure` covers 0-field structures, so
`Unit.sizeOf : sizeOf u = 1 := rfl` needs `PUnit.rec _ 1 u ≡ 1` at a
neutral `u`.  The generic structure-eta certificate excludes reserved
basis names (its soundness runs through `_model` value bridges the
pins do not have), so the rescue's eta branch gains a 0-field
fallback: the fabrication is the bare constructor, certified by
`proofIrrel`, whose unit-likeness branch (`isUnitLikeTy`, native basis
semantics `val PUnit = unitSet`, every member `pt`) covers exactly the
pinned `PUnit`.  Two gates keep the strategy aligned with the
official kernel: the constructor's level-parameter count must match
the head's level list (mirroring the K branch's runtime gate), and
the *instantiated* result sort must be provably nonzero
(`Level.isNeverZero`, the official `is_never_zero`: the official
rescue refuses a structure that could be a proposition at the given
levels — `Unit = PUnit.{1}` passes, a bare parameter `u` does not).
Soundness is a third `majorToCtor_claims` case mirroring the K case
(`proofIrrel_pt`); no new model obligations — `CapsOk`'s eta
clause stays guarded on non-reserved names.

Pin audit against official structure-rescue eligibility: `Empty` (no
constructor) and `Nat` (two constructors) are ineligible; `Eq` has an
index (ineligible; its `ruleK` pin covers the official K rescue);
`Quot` has no recursor rules.  `PSigma'` *is* eligible and already
pins `eta := true` with 2 fields — but the reserved-name gate in
`structEtaCertWith` makes the declared capability inert for the
stuck-major rescue (defeq-side pair eta is covered separately by
`pairEtaCert`), so a stuck `PSigma'.rec` major is still not rescued.
Open finding: fixing it needs a pair-eta-based rescue certificate for
the basis pair (or restating the eta law in public names).  Note also
the modeled eta branch still gates on the *static* `piResultIsProp`
rather than the official instantiated `is_never_zero`; for the
Type-valued structures the preprocessor emits the two agree.

## Indexed recursors (2026-08-21)

The iota machinery is index-generic; the one addition over the
official kernel is the **canonical-index certificate**.  The model's
`iota_j` theorem only speaks about the constructor's canonical index
tuple `ı⃗_j(p⃗, x⃗)`, so the semantic fold fact cannot hold at arbitrary
index arguments — before firing, `iotaRec` checks (mirroring the
existing parameter `defEqList`) that the recursor's index arguments
are definitionally equal to the residual of the constructor's
telescope under the major's arguments, whose stripped result head must
be a constant.  On well-typed input this always succeeds (with the
family opaque, the defeq that typed the application can only have
proceeded by congruence), so no completeness is lost.  `RecRulesOk`'s
hypothesis block carries the matching semantic fact — the trailing
interpretations of the constructor walk's (fvar-opened) residual
`rest₂` are the recursor's index-argument values — produced by
`iota_sound` from the certificate and consumed by `modeled_rule_fold`,
where the statement's index slots collapse onto the parameter+field
spine (`instSeq_mid_collapse`) and swap onto the walk's opening
variables via `interp_instSeq_congr` (instantiation interpretations
are determined by argument values).  The preprocessor's indexed
`iota_j` statement (indices instantiated at `ı⃗_j`, never quantified)
is checked *semantically* by `checkIotaThm` (see the defeq-based
install section below), which replaced the syntactic
`buildIotaStmt`/`checkIotaStmtShape` pin.

## Quotients as a pinned basis block (2026-08-21)

Lean's kernel quotient bundle is the sixth pinned basis block
(`BasisKind.quotK`): `Quot` is stored as an inductive type former,
`Quot.mk` as its constructor, and `Quot.lift`/`Quot.ind` as stored
recursors with one synthetic rule each (`⟨Quot.mk, 1, λ … a, f a⟩`,
resp. `mk a`), so the *generic* iota machinery reduces them — no new
kernel reduction code.  `Quot.sound` is part of the block as a stored
axiom: it is true in the set model, and a matching `axiom` record in
the input is skipped by the frontend (`propext` and
`Classical.choice` are instead accepted as ordinary `axiomDecl`s; see
the axioms note in the overview).  The frontend verifies each exporter `quot` record against
the pinned member of its kind and installs the block at the `type`
record.  Because the block's types mention the pinned equality former,
`checkDecl`'s `basisDecl` arm requires `Eq` to be installed first.

The set-theoretic interface gains `quotSet u A R` (for `u ≠ 0` the
classes of the equivalence closure of "`R a b` is inhabited";
for `u = 0` a proposition — realizable since `Quot`'s base then lives
in `Prop`), `quotClass`, and `quotLift` (the induced map on classes),
with laws for formation, class membership, surjectivity of classes,
soundness (related elements share a class), and conditional lift
membership/beta whose invariance premise is discharged from the
`h`-argument's semantic membership.  `Quot.ind` and `Quot.sound` are
proof points (their statements are propositions, true by class
surjectivity resp. soundness).

## Current state

Supported fragment: **`def`/`thm` declarations over sorts, dependent
function types, lambdas/apps with certified beta, lets (native `letE`
with reference-style lazy zeta, task #79), constants with delta
unfolding, all five basis blocks
(`PUnit`, `Eq`, `Nat`, `PSigma'`, `Empty`) with verified set models,
`PSigma'.mk` projections, proof irrelevance, lambda/unit eta,
verified iota reduction, `Nat` literals (succ-packing `reduceNat`,
literal defeq, lit-major conversion — all modeled), modeled inductives
— including indexed families/recursors — with projection functions
and the eta/unit-like/rule-K capabilities, and the stuck-major rescue
(rule K + structure eta in iota)** (71/92 good arena tutorial tests
accepted; the good tests still rejected need quotients, Prop
projections and assorted features (080, 087–093, 102–107, 118–123);
type-mismatch, duplicate-name, duplicate/undeclared level parameters,
stray free variables, and unknown constants rejected).  The whole verification stack (claims in
`Setlec/Model/Core/*`, annotation, extension, consistency) is stated
against the open-recursion pure knot at `pureOps`.

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
mentions.

### Lazy delta reduction with reducibility hints (2026-08-21)

`isDefEq` unfolds definitions lazily, the way real kernels do
(`lazyDeltaStep`), instead of eagerly whnf-ing both sides: the defeq
body `whnfCore`s both sides (no delta), tries the literal
acceleration, and only then decides on delta — one-sided heads unfold
that side; when both heads are stored definitions the *reducibility
hint* (`ReducibilityHint`: `opaque < regular h < abbrev`, regular
heights by `<`; parsed from the export's `hints` field, stored on
`defnInfo`) picks the greater side to unfold; at equal hints the
*same-head short-circuit* first tries level-and-spine congruence
(`defeqSpine`, pairwise `defEqList` on the arguments) and only on
failure unfolds both.  Each unfolding step recurses through
`r.defeq`, so the reference kernels' loop is the knot recursion and
every re-entry re-runs the syntactic fast path and `whnfCore`.  The
hints steer *order only* — every branch is an independently sound
reduction or comparison — so the model layer never reads them: the
semantic invariants quantify over the stored hint and the claims
proofs (`defeq_claims` consumes `WhnfCoreClaims`, `reduceNat_sound`,
`unfoldDefinition_sound`, and the new `defeqSpine_values` spine
congruence) are hint-independent.  `whnf` itself (as a normalizer)
still unfolds eagerly in its loop.  The same-head try is guarded to
equal *regular* hints (`ReducibilityHint.sameRegular`), mirroring the
reference kernels exactly (owner ruling, 2026-08-21): at equal
`abbrev`/`opaque` hints both sides unfold eagerly without a spine
attempt — proof authors rely on abbrevs unfolding eagerly, and a
spine defeq attempt on abbrev-headed applications risks reduction
bombs; do not generalize the guard.  Remaining deviations from the
reference kernels, all safe-side: no failure cache for the same-head
check yet, no `tryUnfoldProjApp`, no cheapProj (tracked as deferred
tasks).  Arena suite wall time dropped ~33% (47s → 31s).

### Defeq-side Nat folding: the fvar guard (2026-08-24, task #94)

A **forbidden strategy superset** (match-reference ruling: the
reduction strategy mirrors the reference kernels site by site — no
supersets, even verdict-preserving ones) that real input detonated,
found by the init-full frontier at 34.0 % (task #93 diagnosis).  `defeqBody`/
`defeqBodyI` ran `reduceNat` during definitional equality
*unconditionally*; the official kernel attempts defeq-side literal
folding only when **both** whnfCore'd sides are free-variable-free
(`type_checker.cpp`, `lazy_delta_reduction`:
`if ((!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce)`), as does
lean4lean (`TypeChecker.lean:782`).  On the *open* `Int32` arithmetic
pairs of `_private.….Int32.instUpwardEnumerable_eq`, the unguarded
attempt whnfs an open argument (`x + 2147483647`-shaped), which
delta-unfolds `Nat.add` and iota-grinds its `Nat.brecOn` tower down
the literal unarily toward `2^31` `succ` steps — fuel exhaustion,
exit 3.  With the guard the pair falls through to the `sameRegular`
spine-congruence path (the official kernel's `is_def_eq_args`) and
reduces cheaply.

Implementation: both defeq-side call sites (plus the `defeqBodyNC`
twin) wrap `reduceNat` in `if fold then … else pure none`, `fold` =
both sides fvar-free — `Expr.hasFvar` on the spec body (no more than
the `a' == b'` comparison already there), the `O(1)` eager fvar-range
read `hasFvarI` (task #86) on the interned twins.  The whnf-loop
`reduceNat` stays **unguarded** — the official whnf loop is unguarded
too; exact parity, no over-correction.  Verification: the guard only
*prunes*, so each proof keeps its shape via a per-file guarded wrapper
over the existing step lemma (`reduceNatIf_disc`, `reduceNatIf_shift`
+ `hasFvar_shiftFrom`, `reduceNatIfI_sim` behind a `SimAt.withStore`
peel + `hasFvarI_spec`), and `defeq_claims` extracts the underlying
`reduceNatP` run from a `some` result before `reduceNat_sound`
(a false guard yields `ok none`, closing that case vacuously).

Acceptance: the repro slice (`_tmp/init-exports/
repro-int32-upward-enum-pre.ndjson`, 154 k lines, kept out of tree)
flips exit 3 → 0 in both modes; committed as the minimal e2e fixture
`reducenat_guard.ndjson` (`tests/e2e/src/reducenat_guard.lean`: open
`x + 2147483647 + 1 ≡ Nat.succ (x + 2147483647)`, verified to
detonate pre-fix and accept post-fix).  Arena/e2e/scale verdicts
otherwise unchanged; init-prelude probe 20.94 G yolo / 27.22 G cert
(vs 22.02/28.03 at the merge base — the guard also stops fruitless
whnfs of open arguments during defeq).

**Milestone — init-full completes** (init-full-pre2, streaming,
32 GB ulimit): with the guard the *entire* 6 223 893-line /
58 609-record full-Init stream runs to the end in **both modes** —
**61 043 declarations accepted** (certified 4 m 09 s wall, `--yolo`
3 m 50 s), exactly the two known taint skips
(`Lean.reduceNat`/`Lean.reduceBool` via `Lean.trustCompiler`), final
verdict decline (2) by taint-skip design.  No new frontier: the 66 %
of the stream beyond the old 34 % detonation point checks clean on
first contact.  (Task #95 then installed the compiler-trust family:
zero skips remain and the run exits **0** with 61 048 accepted — see
"The compiler-trust axiom family installs".)

Modeled-install soundness architecture (2026-08-19, in progress): the
fold facts for a modeled recursor come from eliminating its checked
`R._model.iota_j` theorem.  The pipeline: the kernel's iota
certificates (now covering the major and the constructor spine, plus
syntactic arity pins on both types) become expression-spine fits
(`certs_fit` → `TeleFitI`), relocated to value-spine fits
(`TeleFitI.toTeleFit` via `arg_swap`/`instantiate1_instantiate1` —
each instantiation argument exchanged for its opening variable) and
carried as hypotheses of `RecRulesOk`'s fold clause (transported past
extensions by `TeleFit.env_shrink`; the basis instances ignore them).
The consumer-side plan: the fits give exactly the memberships the
stmt-telescope quantifies over (rule λ-domains are kernel-pinned to
the recursor/constructor type domains), `TeleFit.elim` + the Eq
collapse (`mem_eqv`) turn the theorem's inhabitant into the value
equation, and a λ-tower fold lemma (app_lam per binder, with
`app_pt`/`lam_zero`/`mem_univ_zero` making the Prop collapse
self-handling) identifies the right-hand side.  The generic machinery is
complete and committed: the erasure congruence (`interp_erasedEq`),
the λ-tower fold (`TeleFitLam.fold`, collapse-free via unconditional
`app_lam`), the value↔expression spine bridges
(`TeleFit.toTeleFitI`, `TeleFitI.toLam`), renaming transfer (`RenEq`,
`TeleFitI.ren_transfer`), argument swapping (`arg_swap_list`), and
the lift/instantiate commutations.  The kernel additionally pins the
stored iota theorem's statement piecewise (telescope domains = rule
λ-domains renamed; body = the expected Eq application), so soundness
never reasons about annotate/rename commutation.  The semantic
centerpiece is proven: modeled_rule_fold (Setlec/Model/IndInstall)
derives a modeled recursor rule's fold obligation end to end from its
checked _model.iota theorem.  The recursor
extension itself (extend_modeled_rec) is also proven: phase-0
rules-free provisional model, environment transport, and
modeled_rule_fold per rule.

**Member types match up to display-only binder names (2026-08-21,
owner ruling).**  `checkMemberVal` compares the renamed public member
type against its stored `_model` type with `Expr.eqUpToNames`: plain
structural `==` except that the binder names of
`lam`/`forallE`/`letE` and an `fvar`'s display name are ignored —
everything semantic (indices, constants, levels, `BinderMeta`
including the codomain-sort annotation and the binder info, `fvar`
type annotations) still compares.  Definitional equality was
explicitly ruled out as far too heavy.  The reason a syntactic
contract cannot hold at the binder-name level: lean4export's
expression table is keyed by `Lean.Expr`'s hash/equality, which
identify terms differing only in binder names, so the *first
occurrence's* spelling wins for every shared subterm — in the
init-prelude export, `ParserDescr.const (name : Name)` and
`ParserDescr.parser (declName : Name)` share one table entry, and
`trailingNode`'s `(prec lhsPrec : Nat)` telescope is spelled
`prec, prec` in the constructor record while the recursor record's
own type keeps `prec, lhsPrec` (this blocked the init-prelude probe
at `Lean.ParserDescr.rec`; even a correct preprocessor stream can
drift this way).  On failure the error message dumps both compared
expressions, which localizes the offending subterm immediately.
Soundness rides on names being display-only: the inversion yields
`eqUpToNames` instead of `=`, bridged to the existing erasure
machinery by `ErasedEq.of_eqUpToNames` (structural induction; the
comparison is strictly stronger than `ErasedEq`, which also drops
`fvar` types), consumed via `interp_erasedEq` (the interpretation
never reads names) and a new `ErasedEq.stripPis_inv` (telescope strip
transport with pointwise-erased domains and equal binder metadata,
for the eta/unit-like pins).  `extend_modeled_one` takes the member's
own `AnnotOk` as a hypothesis (from its annotation run,
`annotate_sound`) instead of transporting the model's across the
no-longer-syntactic equality, and `eta_rule_fold`/`unit_rule_fold`'s
statement-vs-public domain hypothesis weakened from renaming equality
to the already-erased-based `RenEq`.  No other congruences were
needed: the syntactic facts about the member type (`hasFvar`,
`looseBVarsBounded`, `constsResolve`, `allLevelParamsDefined`) were
always derived from the member's own annotation run, not from the
model's type.

Modeled install wired end to end (2026-08-20): checkDecl's indDecl arm
runs checkIndDecl and the frontend emits opaque blocks (the alias
shortcut is gone).  Soundness (Setlec/Model/Extend/, split out of
Consistency for iteration speed; since 2026-08-21 a directory of
per-lemma files re-exported by the imports-only umbrella
Setlec/Model/Extend.lean, with the shared clause transports —
`extend_fresh`, `extend_rec_swap`, the fresh-extension and
rule-list-swap congruences — in Extend/Transport.lean, and the
quotient-basis `checkDecl_sound` case in
Setlec/Model/Basis/Quot/Consistency.lean): checkIotaRules_inv and
checkIndMember_inv walk the (top-level-lifted) kernel functions and
package the RuleChecked bundles; checkIndMember_sound extends the
model per member under the BlockInstalled fold invariant (each
installed member's `_model` companion is stored, level-matched, and
val-equal).  Two findings the wiring surfaced, both fixed: (1)
RenameOk for the full block map is *unsatisfiable* before the recursor
is installed (clause 2 at the recursor's name contradicts its model's
presence) — phase 0 now runs on a pruned map f₀, and the kernel checks
that the recursor comes after all other members so the pruned/full
maps coincide where the statement facts need the full one; (2) the
kernel's rule-vs-recursor domain comparison stops at the motive/minor
prefix, so RuleChecked's hdomsPre is guarded by i < nP+1+nm (the
unguarded form also paired a rule field domain with the major-premise
domain — false for List.cons).  Supporting kernel hardening: members
reuse checkConstantVal, no member may be `_model`-shaped, the pinned
Eq basis must be present unshadowed at the recursor (its iota
statements are equations; the value facts flow from IndOk's pinned
clause), and constsResolve now also resolves proj struct names (the
renaming congruence needs it).  Arena after the flip: 52/92 — the
newly declining tests project out of PProd'/user structures, which
previously worked only because the alias delta-unfolded them to the
basis pair; recovering them is the generic-projection task, whose
model side needs EnvModel to record that every non-reserved stored
inductive-kind constant is val-equal to its stored `_model`.

Projection functions (2026-08-20): projections on modeled structures
are installed as *public projection functions* — degenerate recursors
(`nM = 0`, no motive, one rule `⟨T.mk, nF, λ p⃗ x⃗. x_i⟩`) named
`(T.proj).i` (a reserved name *shape*, rejected by `checkConstantVal`)
whose model value is the documented `T._model.proj_i` definition.
`checkIndDecl` installs them for single-constructor blocks after the
member fold (family freshness kernel-checked; fields with absent
`proj_i` artifacts are skipped), and `annotate` rewrites `.proj T i e`
into that constant applied to the type args and `e`, so the generic
iota machinery performs the reduction with no new core code.  The
kernel check is staged (`checkProjLookups`/`checkProjTy`/
`checkProjRule`/`checkProjIota` — small functions keep the monadic
inversions tractable): the public type is the model's renamed back
along `projBack` and pinned by the `projFwd` roundtrip; the rule is
`pisToLams` of the constructor's telescope; the `proj_i.iota` theorem
is pinned piecewise (telescope domains are the constructor's renamed
along `projFwd`; the equation's sides are the projection redex over
the `mk._model` spine and the field bvar; the equality's *type slot*
is not pinned — the fold's Eq collapse never reads it).  Soundness:
`proj_rule_fold` (Model/ProjInstall) discharges the rule's fold
obligation from the checked iota theorem, `extend_proj_fn` extends the
model (value := the model projection's), and `checkProjFn_sound`
carries the phase invariant `ProjPhaseInv` (parent, constructor, and
already-installed projections are val-equal to their `_model`
companions) through the fold.  The frontend currently still drops
`proj_i`/`iota` auxiliaries: keeping the artifacts without eta support
makes pair-eta (`mk (proj f) (proj f) ≡ f`) fail on modeled structures
and good tests get *rejected*; the flip that un-drops them lands
together with the eta capability (task: caps in env).

Eta capability (2026-08-20): a single-constructor block earns the eta
capability when the model documents it — `checkEtaThm` pins the
`T._model.eta` statement (level-matched theorem, parameter telescope
equal to the type-former model's, subject binder at `T._model p⃗`,
body `x = C._model p⃗ (proj_0 p⃗ x) …`) and `checkIndDecl` records
`{eta, etaCtor, etaParams, etaFields}` on the installed inductive.
The kernel's structural-eta rule (`structEtaCert`, in the stuck-term
fallback) then certifies `C p⃗ s⃗ ≡ b`: parameters/levels against `b`'s
whnf'd type, the type application and each installed projection
function's application to `b` against their telescopes (`iotaCerts`),
and each field against the corresponding projection.  Soundness: the
`EtaPins` carried through the block's install discharge the stored
public-name `EtaLaw` (`CapsOk`, since task #83) at the
family-completing member via `eta_rule_fold` + the group-local
identification — every member of the interpreted structure type is
the constructor's value applied to the projection functions';
`structEta_sound` consumes the law with a `TeleFit` built from the
certified telescopes (`certs_fit`) and interprets the synthetic
projection chains through `TeleFit.chainSlots`/`annotOk_spine` — no
value bridging: the law is already public-named.  With this the
frontend keeps the `proj_i`/`iota`/`eta` artifacts (only
`unitlike`/`ruleK` remain dropped): arena 63/92.  Remaining exit-1
violations: 053/073 (unit-like), 097 (rule K), and 084 (the
*dependent* projection's iota theorem transports along the previous
field's iota with `Eq.rec`, whose major is an opaque theorem — it
reduces only with rule K).

`_model` names are not special (2026-08-20, user directive): only the
inductive-declaration install path may look `_model` names up (pairing
a non-basis inductive with its model); no other code knows about them.
In particular the basis does *not* reserve `X._model` companions, the
kernel does not check for "shadowed" models, and input files are free
to declare `Eq._model` etc. as ordinary definitions.  The `IndOk`
pinned clause is guarded by reservedness alone: reserved names are
rejected at install, so a reserved stored constant can only be the
pinned declaration.  Accordingly the frontend does *not* drop the
stream's own basis `_model` declarations (task #27, 2026-08-21): the
`_model` companions the preprocessor may emit for basis blocks (e.g.
`Empty._model` and auxiliaries nested under it) flow through the
normal declaration pipeline and are checked on their merits — they are
ordinary defs/theorems built from earlier stream declarations, never
consulted by the pinned basis install (a basis inductive block matches
the pinned declarations, not the modeled path), so nothing conflicts
and no name-pattern skip is needed.  (Historical note: an earlier
iteration reserved the basis `_model` companions in the kernel and
therefore had to discard them in the frontend; the 2026-08-20
directive above removed the reservation, and the frontend drop went
with it.)

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

## Defeq-based modeled-recursor install (2026-08-21)

The iota-rule check against the model's `iota_j` theorem is
*semantic*, not syntactic (`checkIotaThm`): the stored theorem's
telescope is opened at free variables (`openPisAtFvars`), the body
must be an equation in the pinned `Eq`, the left side is
*structurally* the renamed recursor applied to the opened prefix
variables, `ni` index slots, and the canonical major (renamed
constructor at the parameter/field variables); everything else is
checked **definitionally** (`checkDefEqList` in the provisional
environment): the index slots against the constructor residual's
canonical tuple, the opened field-variable types against the renamed
constructor's field domains, the opened prefix types against the
renamed recursor's domains, the rule's λ-domains against the public
telescopes, and the equation's right side against the applied rule
rhs.  This makes the check insensitive to binder names, `optParam`
wrappers, and any reducible spelling differences in the stored model.
Soundness consumes the defeq pins through `isDefEqCore_sound` inside
the telescope walks (`Setlec/Model/IotaWalk.lean`): `pi_walk` /
`lam_walk` / `peel_walk` / `self_walk` transfer the fold fact's value
spines between the theorem's opened telescope, the public telescopes,
and the rule λs, with the frame-crossing congruence
(`interp_instSeq_fvarFrames`: instantiation interpretations along an
fvar spine are determined by the spine's *values*) bridging the
theorem's own opening frame and the fold clause's fit frames.
`modeled_rule_fold` (`Setlec/Model/IndInstall.lean`) is fully
multi-motive-general (all of `nP nM nm ni cnP cnF` abstract).

**Firing modes: canonical, nested, inert (2026-08-22, task #48).**  A
rule is *canonical* (`Expr.recRulePlain`) when its constructor-
parameter count is within the recursor prefix, the prefix fits under
the major's position, and the major's domain starts with the
recursor's own leading binders.  A *nested-auxiliary* rule (the
`Array.mk`/`List.nil`/`List.cons` rules of `Lean.Syntax.rec_1/rec_2`,
whose major lives at an inner type former) instead has constructor
parameters and levels that are **fixed instantiations** — exactly the
recursor type's major-premise domain application `D.{lvls} p⃗` (the
preprocessor emits `rec_1._model.iota_j` theorems for these rules
too, with the statement's major the constructor at `lvls` applied to
the `p⃗` instantiations and the field variables).  The stored flag is
a three-state `RecRuleFire` (`.plain` / `.nested lvls pins` /
`.inert`), computed once at install:

* `.plain` — `checkIotaThm` pins the theorem as before.
* `.nested lvls pins` — for non-canonical rules whose *shape*
  certifies (`nestedRuleShape`: the `iota_j` theorem exists, the
  recursor has no index premises — `majorIdx = rulePrefix`, the only
  sub-shape the soundness covers; an indexed nested-aux rule stays
  inert — the major domain is a constant-headed application of
  exactly `cnP` arguments, and the instantiations pass the syntactic
  well-formedness guards recorded in `EnvWF`), `checkIotaThmN`
  re-runs the `checkIotaThm` pin with the constructor at the stored
  `lvls` applied to the stored `pins` opened at the statement's
  prefix variables (`Expr.instSpine`) in place of the leading
  telescope variables, and the constructor-telescope walks at the
  `lvls`-instantiated type.  A certifiable shape whose theorem then
  fails the pin declines positively at install.
* `.inert` — everything else (no theorem, indexed shape).  `iotaRec`
  treats a *matched* inert rule (recursor fully applied, major whnfs
  to a constructor application of the rule's ctor at the right arity)
  as a positive detection of the unsupported feature and declines
  ("iota reduction over a nested auxiliary recursor rule") — a
  silently-stuck nested redex would surface as a spurious *reject*
  downstream (this is how `Lean.Syntax.brecOn_1.go`, init-prelude
  DECL 2217, originally failed).

At fire time both fireable modes run the same generic path; only the
two comparands differ (`recFireComparands`): the constructor's levels
are checked against the by-name linking (`.plain`) resp. the stored
`lvls` under the recursor's instantiation (`.nested`), and its
leading arguments `defEqList`-checked against the recursor's leading
arguments (`.plain`) resp. the stored `pins` instantiated at the
fire-time argument spine (`.nested`; `Expr.instSpine`, the kernel
spelling of the verification's `instSeq`).  The reduct is the same
rhs application in both modes.  Soundness: `RecRulesOk`'s fold clause
guards the canonical value-premises on `.plain` and carries a nested
premise (constructor level assignment = stored `lvls` evaluated under
the recursor's; constructor parameter values = stored `pins`
evaluated at the argument values, witnessed over a sanitized
free-variable spine so the fold consumer crosses frames by
value-determinedness); `iota_sound` produces it via
`nested_fire_premise` (`Setlec/Model/Core/NestedFire.lean`), reading
the comparand's annotation truthfulness off the recursor-type
telescope walk — its residual after the non-major arguments is a `∀`
over the instantiated major domain, which by `EnvWF`'s shape clause
*is* the constructor family applied to the stored instantiations —
and `modeled_rule_fold_nested` (`Setlec/Model/IndInstallN.lean`)
discharges the fold obligation from the checked theorem
(`NestedChecked` kit), the nested analogue of `modeled_rule_fold`.
With this the *last* init-prelude blocker is gone: the full stream
(3653 declarations) is accepted end to end in ~41s.

**Slim recursor metadata (2026-08-22, task #46).**  Stored recursor
metadata is exactly what the firing path reads.
`ConstantInfo.recInfo` keeps two sums instead of the four counts:
`majorIdx` (= numParams + numMotives + numMinors + numIndices, the
major premise's argument position) and `rulePrefix` (= numParams +
numMotives + numMinors, the length of the prefix a rule's rhs is
applied to); reduction, the install checks (`checkIotaThm` /
`checkIotaRules` consume only these sums — verified during the
refactor: nothing anywhere needs the individual counts), and the whole
model layer are stated over the sums, with the index count recovered
as `majorIdx - rulePrefix` where needed.  The frontend collapses the
four exported numbers at parse time.  `RecRule` gains two
install-computed fields (input rules carry parse placeholders `0` /
`false`): `ctorParams` — the constructor's parameter count, so
`iotaRec` no longer reads the counts off the per-fire `ctorInfo`
lookup (the lookup itself remains: the constructor's *type* and level
parameters still drive the level linking, the iota certificates and
the canonical-index residual) — and `fire`, the firing mode
(since task #48 the three-state `RecRuleFire`; historically a
`plain : Bool`): previously `Expr.recRulePlain` re-walked the
recursor type on every iota step (a per-step traversal of
install-time-known data, forbidden); now it is computed once per rule
at install (`checkIotaRule`, `checkProjFn`, the pinned basis blocks)
and `iotaRec` reads the flag.
Findings from the refactor: (1) with sums stored,
`rulePrefix ≤ majorIdx` is no longer true by construction — it is
folded into `recRulePlain` (one extra comparison at install) and
carried as a `RecRulesOk` conjunct (`fire ≠ .inert → rulePrefix ≤
majorIdx`), which `iota_sound`'s spine arithmetic consumes; (2) the
Prop-projection fallback `annotateProjRec` was the one genuine
individual-count consumer (it pinned the split `nM = 1 ∧ nm = 1 ∧
ni = 0`) — weakened to `majorIdx = rulePrefix = params + 2`, safe
because the fabricated elimination is re-annotated so the ordinary
rules re-check its shape; the `stdAxiomOk` shape checks similarly
weakened their splits to sums (the semantic content flows from the
type-pin comparison).  `RecRulesOk`'s fold clause states the spine
arithmetic over the *rule's* stored counts (`margs.length =
r.ctorParams + r.nfields` etc.), since those are what `iotaRec`
checks; the `ctorInfo` lookup stays a hypothesis only for the
constructor's type/levels.

**Projection table — de-basing the core (2026-08-22, task #18).**
The core knows no basis names for projections: every projection rule
is driven by a *projection table* keyed by (structure name, field
index).  An entry is a stored constant — `ConstantInfo.projInfo` with
a `ProjEntry` record `{structName, idx, levelParams, numParams, ctor,
numFields, ty, fieldSort, structSort, native, recExtraLevel}` — filed
under the reserved `projFnName` shape (`(T.proj).i`), looked up with
`Env.findProj?`.  Core consumption: `whnfCore` reduces `.proj T i (mk
p⃗ f⃗)` structurally through the entry (ctor/counts/certificates via
the generalized `projCert` over the entry's field/struct sorts);
`infer` types a bare `.proj` node as `piResidual` of the entry's
level-instantiated `ty` along the subject type's arguments and the
subject; `annotate` keeps the node when the subject's type head has a
`native` entry (normalizing the stored name to the type head) and
otherwise rewrites — `annotateProjElim` dispatches on what is stored
under the `projFnName` shape: a `recInfo` (artifact-installed
projection function → rewrite into its application, unchanged
behavior), a non-native `projInfo` *template* (Prop structure-likes →
fabricate the recursor elimination `annotateProjRec`, now entry-based;
the fabrication is re-annotated so its shape is re-checked per
instantiation, amortized by the template's install-time check), else
a single throw (`invalid` out-of-range if field 0 exists, otherwise
`notImplemented`).  Population is two-phase in `checkIndDecl`:
the artifact phase installs projection *functions* (as before —
scoped finding: bare `.proj` nodes on non-Prop modeled structures
have no compositional set interpretation, model bodies being opaque,
so the artifact route must keep rewriting into named constants whose
values are the model projections), then a second pass installs the
Prop-shape templates (`installProjTemplateStep`); templates must come
second because entries interleaved with the member fold would break
`RenameOk`/`projFwd` (template names have no `_model` companions).
The only `native = true` entries are the two pinned basis-pair
members `pairFstA`/`pairSndA` in `BasisKind.declsA psigmaK` (types
generated, sorts `u`/`v` under `max u v`), which replace the last
psigma special cases: `Setlec/Kernel/Core.lean` now contains *zero*
basis-pair names (remaining basis knowledge: nat-literal ops and the
`reservedBasisNames` recursor hints, by design).  Model side:
`EnvModel` gains a `ProjOk` clause — every stored *native* entry is
one of the two pinned pair entries and `PSigma'`/`PSigma'.mk` are the
pinned declarations — so the semantic proofs (`Whnf`/`Infer` claims,
`annotate_sound`) identify a native `.proj` as a pair projection and
interpret it with `sfst`/`ssnd` (values `pairFstVal`/`pairSndVal`,
lambda towers with computed classifiers); `ProjOk.cons`/`env_swap`
transport it, `extend_fresh` takes the corresponding hypothesis.

**Recursor group install.**  Mutual/nested blocks' rule right-hand
sides may mention sibling recursors, so no intermediate environment
may store a recursor whose rules dangle: `checkIndDecl` requires the
block's recursors to form a suffix, `checkIndRecs` provisions them
*rule-less* on top of the member fold (`provisionRecs` — per-member
`checkMemberVal`, exactly the non-recursor member check), checks every
rule against the fully provisioned `envSelf` (per-rule, local), and
re-attaches the checked rule lists.  Soundness mirrors this in
`Setlec/Model/Extend/Recs.lean` + `GroupSwap.lean`: the provisioning
phase is a fold of `extend_modeled_one` (recording `ProvFacts`), the
attachment is a *pointwise swap* of the consts list (`SwapList`,
rule-less vs. rules-attached recInfo at equal positions), and
`extend_rules_eq` transports the whole `EnvModel` across the swap in
one pass — per-item obligations (`SwapPair`: ConstWF, stored rule
constructors, `RecMemberOk` via `recMemberOk_of_kit`) are discharged
from the per-rule `RuleChecked` kits at the provisional model and
carried to the final environment by a levelParams-preserving
environment congruence.  There is no cross-recursor semantic content:
the group theorem is the composition of per-position swaps, done over
the consts list because the kernel's attachment-by-recons makes the
*intermediate* environments (some rules attached, later siblings
absent) ill-formed, so the model cannot be threaded through them
step-by-step.

**Batteries stay simp-shaped.**  `checkIotaThm`'s `Option`-shaped
checks go through `unwrapOr` (and `Env.findThm?`) so the function is
bind/ite-shaped; the pair-monad/fueled projection batteries then
reduce by plain `simp only` distribution (`fst/snd/atF` of bind, pure,
throw, ite, the ops atoms, `unwrapOr`, `checkDefEqList`) — `let some
… := … | throw` patterns compile to matcher applications that block
both `simp` and (at this term size) `split`, so new monad-polymorphic
kernel functions should prefer `unwrapOr`.

## Interned checking: the hash-consed arena core (2026-08-22, task #26)

The executable core operates on **arena indices**, nanoda's
expression-pointer design (`nanoda_lib/src/util.rs`: `Ptr` = integer
index into hash-consing `IndexSet`s; `expr.rs`: nodes carry cached
hashes and locally-nameless metadata; `TcCache` keyed by pointers).
Setlec's rendition:

* **Arena** (`Setlec/Kernel/IExpr.lean`): `EStore` = a node table
  (`Array ENode`, children are `EIdx` indices) plus the cons-table
  `HashMap ENode EIdx` — structurally equal terms get equal indices,
  so equality of interned terms is `Nat` comparison and hashing is
  `O(1)`.  The syntactic operations (`instantiate1I`, `abstract1I`,
  `instantiateLevelParamsI`, spine/telescope ops, the scope/leaf
  queries, and the memoized `readbackI`) traverse the DAG with
  per-call memo tables — shared subterms are visited once, where the
  `Expr` originals walk trees.
* **Interned twins** (`Setlec/Kernel/CoreI.lean`): every core body and
  helper has a hand-written twin over `EIdx` at the concrete monad
  `CheckIM := StateT IState CheckM`, mirroring its `Core.lean`
  original clause by clause (same record-call order, same
  short-circuits; the only extra effects are node views, interning,
  and cache fills).  `defeq`'s syntactic fast paths compare indices.
* **State** (`IState`): the arena, id-keyed memo caches for the five
  entry points (`HashMap EIdx EIdx`, pair-keyed for defeq), and lazy
  caches for level-instantiated stored constants (`constTyAt`,
  `constValAt`, `ruleRhsAt`, keyed by name and level list) — repeated
  delta-unfoldings of the same constant at the same levels stop
  rebuilding its value.  Lifetime: **one top-level entry-point call**
  (exactly the old `KCache`'s, and nanoda's per-`TypeChecker`
  temporary dag) — so the environment is fixed for every cache's
  lifetime and the bridge invariant stays call-local.
* **Environment index** (`FEnv`): executable lookups go through a
  `HashMap Name ConstantInfo` built once per entry call by folding
  `env.consts` from the back (newest insert wins), which makes the
  index's lookup function *equal* to `Env.find?` unconditionally
  (`mkFEnv_find?` — no freshness hypothesis, no invariant threading);
  the spec `Env.find?` (linear `List.find?` — 913k calls scanning
  973M list entries per init-prelude run before this change) and the
  whole Model/Extend stack are untouched.
* **Entry runners**: each `CheckerOps` entry interns its argument into
  a fresh arena, runs the interned knot, and reads the result back
  (`runEntryE`/`runEntryB`/`runEntryS` in `CoreI.lean`); `cachedOps`
  in `Setlec/Kernel/Checker.lean` is now this instantiation.
  **Linearity**: the arena and every cache are threaded strictly
  linearly through the state monad; every mutation detaches the
  component from the state record before updating (the `memoE`
  discipline), no `IO.Ref`s, no sharing of a mutable structure across
  binders.

**The verification seam** (the load-bearing decision).  Three options
were considered (see the task notes): (1) τ-generic core bodies (views
+ op records, instantiated at `Expr` and at indices, simulation by a
relational instantiation à la `PairM`) — rejected: it restructures the
match compilation of every body, which the entire existing proof stack
(`Model/Core/*`, `Verify/Deep|Disc|InferLemmas|Mono`, claims,
inversions) reduces through `simp only [XBody, …]` recipes; (2)
wrapper-level interning (intern at each memo call, bodies stay on
`Expr`) — rejected: interning is a full tree walk per call, the same
asymptotic disease as deep hashing (terms are DAGs; pure Lean cannot
see sharing), so the recursion itself must pass indices; (3)
**interned twins + a run-by-run denote-simulation** — chosen: purely
additive, the existing stack is untouched, and the seam sits entirely
below `CheckerOps` so `BridgeDecl`/`BridgeWfImp`/`BridgeWF`/
`ConsistencyC`/`Main` do not change at all — only the five
`cachedOps_*_bridge` lemmas in `Setlec/Verify/Bridge.lean` were
re-proven against the new definition, with identical statements.

**Faithfulness statement.**  A store is *canonical* when children sit
below their parents and the cons-table is exactly the node-table graph
(`EStore.WF`); then the structural denotation `denote : EStore → EIdx
→ Option Expr` is total on in-range indices and **injective**
(`denote_inj`) — index equality decides expression equality, which is
what makes the fast-path index comparisons verdict-preserving.  The
state invariant `ISOK env s` (`Setlec/Verify/SimI.lean`) carries: the
arena's `WF`; for each lazy constant cache, that entries denote the
level-instantiated stored data; and for each entry-point memo the
`CacheOK` shape transported along `denote` — every entry `i ↦ j` is
backed by expressions `a, b` with `denote i = some a`, `denote j =
some b`, and a pure run `∀ d, a.wscopedB d → whnfCore env F d a = .ok
b` at some fuel (inserts re-use the depth-invariance theorems, hits
consume at the call's depth — exactly the Expr-level bridge's
discipline).  The simulation relation `SimAt env s₀ P c p`: every
successful interned run of `c` from `s₀` preserves `ISOK`, extends the
arena, and its value is `P`-related (denotation + well-scopedness) to
a successful run of the fueled computation `p` at some fuel.  One walk
per twin body (`Setlec/Verify/DiscI1–6.lean`, mirroring the
`Verify/Disc.lean` walks site by site), five memo-wrapper steps
(`SimIKnot.lean`), one knot induction (`ssimI`, `BridgeI.lean`), and
three entry-runner bridges close the loop; the consistency layer
(`checkDeclsC_sound`, `no_proof_of_Empty_C`,
`no_proof_of_Empty_input_C`) keeps exactly its statements.

**Measured** (init-prelude probe, 8 GB limit; instructions are the
primary metric, `perf stat`):

| configuration | wall | instructions | peak RSS |
|---|---|---|---|
| Expr-level cached core (baseline) | 41.0 s | 590.2 G | 166 MB |
| interned core (this change) | 26.3 s | 306.4 G | 113 MB |

−48 % instructions, −36 % wall, −32 % RSS; arena suite 33.1 s → 30.8 s
(dominated by per-test process startup); verdicts identical everywhere
(90/92 + e2e 25/25).  Post-change profile: the per-entry-call `mkFEnv`
build plus structural `Name` hashing ≈ 15 % (a depth-capped `Name`
hash was tried and *regressed* — the `_model.iota_j`/`_model.proj_i`
naming convention makes truncated-suffix hashes collide across every
modeled inductive; solved structurally by the per-decl cache sharing
follow-up), the interned instantiation's per-call memo maps ≈ 13 %, `Level` ops (`simplify`/`leqCore`, semantic — untouched
by interning) ≈ 7 %, `Level.decEq` now only ≈ 3 %.  (An earlier
version of this note concluded from these numbers that level interning
was moot — **wrong**: the init-prelude profile under-represents deep
levels.  The scale harness (task #56) found `spine`/`telescope` at
exponent ~2.7 dominated 57–59 % by structural `Level` hashing — deep
`imax` trees re-hashed on every hash-cons/memo touch.  Level interning
landed as task #62 below.)

**Deferred follow-ups** (validated by the 2026-08-22 performance
audit, in expected-value order): intra-declaration cache sharing —
**landed**, see "Per-declaration state sharing" below;
Level/`BinderMeta.cod` interning (after the
env index the profile is dominated by `Level.decEq` — requires
level-ids inside `ENode`, i.e. reworking `Verify/IExpr.lean`);
parse-time interning with a persistent per-run store (nanoda's
export-file dag; entry calls currently intern their argument tree
each time); per-node cached scope data (loose-bvar bound, fvar range)
in the arena; a defeq failure cache.


## Per-declaration state sharing (2026-08-22, task #51)

One `IState` per **declaration**: every checker operation within one
`checkDecl` — annotate, inferType, isDefEq, ensureSort across all
phases, members and rules — runs in a single shared `CheckIM` state,
so the arena and the memo caches survive across entry calls instead of
being rebuilt per call.

**The flush discipline** (the load-bearing decision).  Cache entries
are only valid for the environment they were created under, and the
environment is not constant inside `checkIndDecl` (member folds, the
rule-less `envSelf`, the `envSelf → env₃` rule-filling swap).  A
runtime environment stamp was rejected: a *complete* cheap equality on
`Env` does not exist (lengths and heads collide exactly at the
`envSelf`/`env₃` swap, and structural comparison is `O(env)`), and an
incomplete check cannot back the bridge ("invariants over runtime
gates").  Instead the discipline is **driver-directed**: thin phase
drivers (`Setlec/Kernel/CheckerS.lean`) mirror `checkDecl`'s phase
structure and call `flushS` at every environment transition — the memo
and lazy-constant caches are dropped, the **arena survives** (it is
environment-independent: `EStore.WF` and `denote` mention no
environment, so `ISOK.fresh` re-establishes the invariant for *any*
environment from `store.WF` alone — `flushS_isok`).  Within a phase
nothing is checked at runtime; the walks prove `ISOK env_phase` holds
at every call site.  Single-environment stretches reuse the *generic*
checker functions verbatim, instantiated at `sharedOps fe : CheckerOps
CheckIM` (methods ignore the per-call env argument; the walks
instantiate them only at `fe.env`).  The iota phase is one flush for
the whole rule fold — every rule of every recursor of the block shares
one cache at `envSelf`.  Non-inductive declarations are the generic
`checkDecl` at `sharedOps` outright: one state, no flushes.

**Incremental index.**  `FEnv` is built once per declaration and
maintained across the provisional environments by `FEnv.push` — the
index of a cons-extension is one insert, and `mkFEnv_push` makes the
pushed index *definitionally* `mkFEnv` of the extended environment
(the `foldr` build peels its head), so the walks carry `fe = mkFEnv
env_phase` by `rfl`-steps and `ssimI` applies unchanged.  The recursor
group keeps the `env₂` snapshot and rebuilds the final environments
from it by pushes.  The install path's direct linear `Env.find?` call
sites are routed through the index in the drivers: the recursor
group's `Eq` pin, the projection-family guard, the artifact and
template install steps' lookups.  Still linear (inside untouched
generic code): `checkConstantVal`'s duplicate check, the iota checks'
`findThm?` model lookups, `checkIotaRule`'s constructor lookup,
`checkProjLookups`, and `indBlockCaps`' capability probes — routing
those needs a lookup method on `CheckerOps` (or twinning the checked
functions) and is left as follow-up.

**The bridge** extends the interned faithfulness layer to the
per-declaration lifetime with *no new state invariant*: `ISOK`/`SimAt`
(`Setlec/Verify/SimI.lean`) were already stated for arbitrary initial
states, so entries surviving across entry calls within a phase is just
`SimAt`-threading; `opE`/`opB`/`opS` runner simulations
(`Setlec/Verify/SimS.lean`) are the per-declaration analogs of the
entry-runner bridges, keeping the final state facts.  One `SimAt` walk
per single-environment checker function relates the `sharedOps` and
`fueledOpsM` instantiations of the *same generic body*
(`Setlec/Verify/BridgeS1.lean` non-inductive, `BridgeS2.lean`
inductive-install; per-site scoping facts mirror the `_wfimp` walks).
`Setlec/Model/BridgeS.lean` composes them along the thin drivers at
the run level — across a flush only `EStore.WF` is threaded — and
derives the intermediate `EnvWF` facts from the pure runs over the
public inversion kit (`ProvFacts`/`RulesChain`; the small `ConstWF`
helpers are replicated from `BridgeWF`'s private ones).  The pure runs
come from the existing `_datF` equations; twin-vs-generic matcher
constants (same source, different elaborations) are bridged by
`split` + definitional coercion of the phase equations, never by
rewriting.  Punchline: `checkDeclShared_bridge` — a successful
shared-state run over a well-formed environment is reproduced by
`checkDecl (fueledOps F)`.  `Setlec/Model/ConsistencyS.lean` restates
the consistency layer for `checkDeclsShared` (which `Main` now runs)
with identical statement shapes; `cachedOps`, `ConsistencyC` and the
whole existing stack are untouched (the change is purely additive,
like task #26).

**Out of scope**: cross-declaration cache sharing (provisional-env
interactions and an env-extension-stable `CacheOK` story) and carrying
the `FEnv` index across declarations (sound — the index has an
unconditional pointwise spec — but it changes the consistency
statement's shape); both are future work.  Flushing at every member
install also discards cross-member sharing within a block that an
extension-stable cache could keep.

**Measured** (init-prelude probe, 8 GB limit, same machine/day):

| configuration | wall | instructions | peak RSS |
|---|---|---|---|
| per-entry-call state (task #26) | 24.7 s | 284.7 G | 113 MB |
| per-declaration sharing (this change) | 15.9 s | 212.6 G | 112 MB |

−25 % instructions, −36 % wall (allocation/locality gains exceed the
instruction win); arena + e2e suite 107 s → 85 s; verdicts identical
everywhere (arena 90/92, e2e 45/45).

## init-prelude milestone and the lean4lean comparison (2026-08-22)

The full preprocessed `Init.Prelude` stream is accepted end to end:
exit 0, 3131 progress-reported declarations (3653 accepted constants),
**40.9 s wall / 166 MB peak RSS** under an 8 GB limit.

Baseline (same machine, 2026-08-21): lean4lean at `e0e3f6b`
(toolchain v4.33.0-rc2), `lean4lean --fresh Init.Prelude`: **0.37 s /
100 MB / 1975 declarations**, reading compacted `.olean` regions
directly.  The ~100x gap decomposes into known causes:

1. **Different work**: 1147 of the 3131 checked declarations (~37 %)
   are preprocessor `_model` artifacts — model definitions and large
   certification proofs lean4lean never sees — plus the install-time
   iota/projection/capability certification against them.
2. **No interning yet** (task #26): every memo lookup deep-hashes and
   deep-compares expressions; lean4lean inherits pointer equality and
   cached hashes from the Lean runtime.
3. **Text export parsing** versus mmap'd olean environment loading.
4. **Per-declaration fresh caches** (the `CacheOK` bridge assumes a
   fixed env per cache lifetime) versus a persistent kernel cache.
5. lean4lean is a port of the C++ kernel's algorithms (including
   `cheapProj`-style shortcuts we deliberately defer).

The main open lever is (2); (1) is the price of checking the models
rather than trusting the preprocessor, and is considered inherent.

### Fair comparison on the identical preprocessed stream (2026-08-22)

Reference checkers were run on the *same* preprocessed init-prelude
stream setlec checks (3136 decl blocks / 3653 constants, `_model`
artifacts included; `_tmp/perfcmp/`):

* official C++ kernel (arena `official-v4.33.0`): **0.31 s / 3.9 G
  instructions** — the headline fair row.  The raw-vs-preprocessed
  penalty for fast checkers is only ~1.8×, so the workload difference
  does NOT explain setlec's gap: setlec is ~129× (wall) / ~149×
  (instructions) behind on identical input.  Preprocessing itself is
  negligible (0.45 s; setlec −1 s when fed the preprocessed file
  directly).
* nanodatg (TG proof-carrying, the closest certifying analog):
  28.6–34.8 s raw, **467–565 s preprocessed** at ~1 GB RSS — setlec is
  currently the *fastest certifying checker* on this workload by
  12–14×, and with complete verification (nanodatg reports tens of
  thousands of open TG gaps).
* **Divergence finding**: on the preprocessed stream, upstream nanoda
  **panics** (`infer_proj prop`, tc.rs:471) and lean4lean (arena
  branch ecb3b66) **rejects** (`at PSigma'.fst: (kernel) invalid
  projection`) — while the official kernel accepts.  A real
  reimplementation divergence on Prop-structure projections; worth
  reporting upstream.

Perf attribution and the fix stack (Env index −30 %, interning,
per-declaration cache sharing, per-fire iota certification) are in the
2026-08-22 performance-audit notes (tasks #26, #49, #50).

## The verification-tax flag: SETLEC_NO_PROOF_CERTS (task #76)

`SETLEC_NO_PROOF_CERTS=1` (command-line alias: `--yolo`) is an
**unverified measurement mode**: it
selects, once in `Main`, a second driver stack
(`Setlec/Kernel/CoreNC.lean`, `Setlec/Kernel/CheckerNC.lean`) whose
core knot skips the infer/defeq calls that exist only to feed the
soundness proofs — the calls the reference kernels do not perform.
Purpose: keep the lean4lean/official-kernel comparison honest by
splitting the gap into *verification tax* (flag-off − flag-on) and
*engineering quality* (flag-on − official).

**Structure.**  The flag never reaches the kernel as data: `Main`
picks `checkDeclsShared` (default) or `checkDeclsSharedNC`.  The NC
stack is a verbatim duplicate of the shared-state drivers at
`sharedOpsNC`, whose knot (`coreKnotNC`) ties cert-skipping twins of
exactly the affected bodies (`iotaRecNC`, `majorToCtorNC`,
`whnfAppNC`/`betaPeelNC`, `inferSpineNC`, `structEtaCertWithNC`,
`structUnitCertNC`, `stuckIrrelNC`, and the three knot bodies that
reach them); every other body and all mirrors/phase drivers are the
shared (generic-in-ops) originals.  The default path is byte-identical
— no existing kernel/proof module changed — so every consistency
statement (`Setlec/Model/ConsistencyS.lean`) still speaks about what
the binary runs by default, and **no proof covers the flag-on path**.

**Skipped** (site list; reference citations in `CoreNC.lean`'s
header): the per-fire recursor/constructor telescope certifications
and the ordinary plain-rule parameter and canonical-index
re-comparisons in `iotaRec` (lean4lean's `inductiveReduceRec` checks
none of these), the possibly-Prop per-binder beta re-checks in
`whnfApp`/`betaPeel`, the possibly-Prop-gated infer-app argument
residue in `inferSpine`, and the type-former/per-projection telescope
certifications of the structure-eta and unit-like certificates (the
references' `tryEtaStructCore`/`isDefEqUnitLike` keep only the type
defeq and per-field checks, which stay).  **Kept always**: every
arity/ctor-identity/shape check, the ctor↔recursor level linkage, the
nested-rule comparand values, all front-door annotate/infer checking,
the install-time checks, and the K/eta fabrication type checks.
`projCertI` (possibly-Prop projection reduction) is proof-only by the
same reference comparison but outside the task-#76 site list and
still runs in both modes.

**Findings** (verdict-relevant checks the site list predicted as
proof-only):

1. *Projection-rule parameter comparison.*  Projection functions are
   a setlec-specific recursor encoding; the references reduce `.proj`
   nodes by direct field selection and never splice the outer
   application's parameters into a reduct.  Skipping the parameter
   comparison for projection-shaped rules rejects five good
   arena/e2e tests (`118/119_reduceCtorParamRefl`, `120_rTreeRec`,
   `121_rtreeRecReduction`, `080_RBTree`, `nested_rec`,
   `let_rec_rhs`) — it is part of matching reference behavior, not a
   proof artifact.  It stays in the NC path.
2. *K-rescue index comparison.*  At the time of this finding the
   certified `majorToCtor` K path certified the fabrication by
   `proofIrrel` only, the index comparison the official `toCtorWhenK`
   performs (`isDefEq appType (inferType newCtorApp)`) being subsumed
   by the major-slot telescope certificate of the then-ungated
   fire-path `iotaCerts`.  Skipping the certificates without restoring
   the reference check *accepts* arena `bad/098_ruleKbad`;
   `majorToCtorNC` therefore carries the official check verbatim —
   and since task #71 (major-slot certificate gated at nonzero
   motives) the certified `majorToCtorI` runs the same check, NC
   differing only in dropping the `proofIrrelI` certificate and the
   relocated telescope certification.

**Measured** (init-prelude probe, `perf stat` instructions, 8 GB
limit; verdicts identical in both modes — arena 90/92, e2e 48/48,
probe exit 0 / 3653 accepted):

| configuration | instructions | wall |
| --- | --- | --- |
| default (certified) | 204.9 G | 15.5 s |
| `SETLEC_NO_PROOF_CERTS=1` | 151.1 G | 10.4 s |
| official C++ kernel (same stream) | 3.9 G | 0.31 s |

Verification tax: **53.7 G ≈ 26 %** of the default run.  Engineering
gap: **~39×** over the official kernel (of the total ~53×).  The tax
is dominated by the per-fire telescope certifications; the remaining
gap is the interning/parsing/cache substrate (see the performance
roadmap).

## Bulk instantiation, lean4lean-style (task #50)

Chains of `instantiate1` that consume an argument spine copied the
whole codomain/body once per argument (lean4lean defers and
substitutes n arguments in one `instantiateRevRange` traversal).  The
bulk entry points:

* **`Expr.instantiateList e vs d`** (`Setlec/Kernel/ExprOps.lean`) —
  substitute the whole replacement list in one traversal, `vs[0]` for
  `bvar d` (innermost binder first — the natural accumulator order
  when peeling a telescope outermost-first).  Its semantics is **by
  construction the `instantiate1` fold**:
  `instantiateList e (v :: vs) d = (instantiateList e vs (d+1)).instantiate1 v d`
  holds *unconditionally* (`Setlec/Verify/InstList.lean`; a `bvar` hit
  recurses into its replacement with the earlier-listed entries,
  reproducing what the fold does on open replacements — identity on
  the `bvar`-closed replacements every call site passes).  Companion
  equations: `_nil`, `_append_one` (snoc), and
  `instSpine_eq_instantiateList` for the descending-cursor form.
* **`EStore.instantiateListI`** (`Setlec/Kernel/IExpr.lean`) — the
  interned twin, one memoized DAG traversal keyed
  `(node, live-prefix, cursor)` (nanoda's `ExprCache` discipline);
  `instantiateListIGo_spec` commutes it with `denote`.

**Converted sites** (interned executables only; the `Expr`-level
bodies stay the spec, so Model/Verify statements are unchanged):

* `piResidualI`, `instSpineI` (spanning shape), `iotaCertsI` — peel
  the raw telescope with an argument accumulator, substitute domains
  (small) per argument and the residual once; spec/sim statements kept
  (`piResidualI_spec`, `iotaCertsI_sim`), so all call sites and the
  Model layer are untouched.  `getAppArgsI` also went accumulator
  (linear instead of quadratic append).
* **`whnfCoreBodyI`'s beta** (`whnfAppI`/`betaPeelI`,
  `Setlec/Kernel/CoreI.lean`): the app case normalizes the spine head
  once and consumes the whole spine in a loop, batching consecutive
  λ-binders into one substitution (possibly-Prop certificates still
  run per binder, against the bulk-substituted *domain* only).
* **`inferBodyI`'s app case** (`inferSpineI`): the Π-telescope is
  walked with deferred substitution; syntactic `∀`s are peeled
  without copying the codomain, `whnf` runs only when the telescope
  is not syntactic (on a syntactic `∀` it is the identity).

**Verification seam** (`Setlec/Verify/BetaSpine.lean` + the reworked
walks in `DiscI4`): the loops have pure mirrors (`whnfApp`/`betaPeel`/
`inferSpine`, generic over the core record), and a *soundness of the
loop against the chained spec*: a successful loop run at the pure
fueled knot is reproduced by the original one-argument-at-a-time body
at some fuel (`whnfApp_sound_body`, `inferSpine_sound_body`).  The
crux is a snoc decomposition (`whnfApp_snoc` …): peeling the last
argument off a loop run yields a loop run of the prefix followed by
one body step, with `instantiateList_cons` splitting the bulk
substitutions and every mirror fuel-monotone via its `_atF` equation.
The interned walks compose their simulation against the mirror with
`SimAt.wr` (weaken the fueled side by a value-level implication) —
the `Expr`-level bodies, all Model/Core proofs, the claims, and the
bridge statements are untouched.  Observable change: none in verdicts
or stuck shapes (the loop replays exactly the per-level checks, in
order); the interned knot consumes *less recursion depth* per spine
(the per-prefix `whnfCore`/`infer` levels collapse into one loop),
which only matters within 100000 of `checkFuel` exhaustion.

**Measured** (init-prelude probe, `perf stat` instructions primary):
306.3 G / 26.2 s baseline → 301.7 G after the telescope helpers →
**285.1 G / 24.6 s** after the beta/infer spine loops (−6.9 %
instructions, −6 % wall); verdicts identical everywhere (90/92 arena
+ e2e 27/27; arena suite wall unchanged within noise, dominated by
per-test process startup).  Site attribution
beforehand (per-site clones of `instantiate1IGo`): beta chains 3.3 %
self + memo share, binder opens 2.8 %, infer-app 0.6 %, iotaCerts
0.3 %, telescope helpers 0.1 %.  The remaining instantiation cost is
binder *opening* (`fvar` substitution when descending under λ/∀ in
infer/defeq/annotate, one pass per binder) — batching those needs
lean4lean's `inferLambda`-style telescope loops across knot bodies, a
follow-up of the same shape as the beta loop.

## Testing: asymptotic scalability harness (2026-08-22, task #56)

`tests/scale.sh` catches superlinear checker behavior with doubling-n
growth tests.  `tests/scale/gen.py SHAPE N` emits self-contained
export-format streams (ndjson 3.1.0, like `tests/e2e/*`), one shape per
subsystem:

* `chain` — n defs `d_i : Type := d_{i-1}` plus `top : d_n :=
  ∀ p : Prop, p → p`, whose check forces the full n-step delta chain
  (env growth + unfold path);
* `spine` — `f : Prop → … → Prop` (n arrows) applied to n arguments
  (application-spine walking, Π stepping);
* `many` — n independent tiny defs (env insertion / per-decl setup);
* `telescope` — one def with a dependent Π/λ telescope of depth n
  (binder opening and instantiation).

The runner measures retired instructions (`perf stat`; wall-time
fallback), subtracts a measured 1-decl startup baseline (basis install,
~0.4 G instructions), and fits the growth exponent between successive
doublings; a shape PASSes iff the largest-step exponent is ≤ 1.3
(expected ~1.0 when healthy).  Deliberately **not** part of
`lake test` — run manually or as an optional CI job.

First measurement (2026-08-22, all four shapes FAIL — findings, not
yet fixed): `chain` 1.89 and `many` 1.88 (quadratic: `mkFEnv` rebuilds
the whole name-index `HashMap` from `env.consts` on every top-level
entry call, `Setlec/Kernel/CoreI.lean`); `spine` 2.72 and `telescope`
2.64 (cubic-ish: profiles are dominated by structural `Level`
hashing/equality — inferring a depth-k telescope/spine builds
O(k)-deep `imax` level trees, and every hash-cons/memo touch of a
`sort`/`const` node re-hashes them, an O(n) factor on top of the
per-binder walks).  These corroborate the performance-roadmap items
(memoize infer/whnf/defeq, incremental env index, interned levels);
re-run the harness after each to watch the exponents drop.

## Interned levels (2026-08-22, task #62)

Levels live in the arena alongside expressions: `EStore` gains
`lnodes : Array LNode` / `lcons : HashMap LNode LIdx` (`LNode` =
`zero/succ/max/imax/param` over `LIdx` children), and `ENode` carries
level *ids* — `sort (u : LIdx)`, `const (us : List LIdx)`, and binder
metadata as `IBinderMeta` (`bi`, `cod : Option LIdx`).  Hash-consing a
`sort`/`const` node now hashes a handful of `Nat`s instead of
re-hashing a deep `Level` tree on every memo touch, which was the
scale harness's dominant cost (`spine`/`telescope` at exponent ~2.7).

Interning happens at `internExprM`/`internL`; readback
(`readbackL`/`readbackBM`) reconstructs `Level`s only at the arena
boundary.  The hot level operations get interned twins, DAG-memoized
where recursive: `simplifyLIGo` (persistent memo `IState.lsimpC`),
`isNonZeroLIGo` (`lnzC`), `substLIGo`/`internLevelSubst(s)`,
`instantiateLevelParamsIGo`, and the full `leqCore` mutual family
(`leqCoreLI`/`leqRestLI`/`imaxRulesLI`/`imaxRulesRestLI`/
`imaxRulesRightLI`/`byCasesLI` plus `leqLI`/`isEquivLI`) as *pure*
arena functions threading the simplify memo — the monadic wrappers
(`isEquivLM` etc.) are single `modifyGet`s, so the faithfulness proofs
stay pure lemmas.  `isEquivLM` additionally carries a persistent
*result* cache (`eqvC : HashMap (LIdx × LIdx) Bool`): on a canonical
arena the index pair determines the level pair, so a decided
equivalence is never recomputed.

Verification: `denoteL : LIdx → Option Level` extends the denotation
layer (`denoteLList`, `denoteBM`); `EStore.WF` gains `levels_lt` /
`lchildren_lt` / `lcons_graph` clauses and canonicity gives
`denoteL_inj`.  Level-memo invariants (`LvlMemoInv`, `LvlQMemoInv`,
`EqvMemoInv`) mirror the expression memo invariants; `ISOK` gains the
`lsimp`/`lnz`/`eqv` clauses and the lazy stored-constant caches are
re-keyed by level-*index* lists (each entry carrying its key's
denotation).  The twin faithfulness of the `leqCore` family is
`Setlec/Verify/ILevel.lean` (~2 700 lines; spec-side reduction
equations for the fueled mutual family, per-arm `imaxRules` lemmas);
the walks in `Setlec/Verify/DiscI*.lean` consume the level ops through
`RelL` (`denoteL u = some l`) and the `*_eff` lemmas.  The `Expr`-level
spec and everything in `Setlec/Model/*` are untouched.

**Scale harness effect** (kernel change alone): `spine` 2.70 → 2.11,
`telescope` 2.62 → 1.94 (3.4×/3.6× absolute at n = 400); `chain`/
`many` unchanged (fixed by task #63 below).  The residual
`spine`/`telescope` ~n² is *not* level-related: profiles show the
per-binder opening walks — `instantiate1IGo`/`abstract1IGo` visit the
whole remaining telescope per binder, and the accumulator-based spine
walkers convert the accumulator per argument (`List.toArrayAux`/
`lengthTR`).  The fix is the official-kernel discipline — accumulate
fvars, bulk-instantiate only each *domain* against the accumulator,
instantiate the body once at the end (`instantiateListI` exists for
exactly this) — applied to the annotate/infer/whnf binder cases, plus
the deferred per-node scope data (loose-bvar bound) for O(1) identity
shortcuts.  That rework touches the `DiscI` binder walks and is left
as the next performance task.

**Shallow-level regression and its fix**: on the (shallow-level)
init-prelude stream the interned `leqCore` twin family was *slower*
than the structural ops — the `byCases` cascades interned every
intermediate level and threaded HashMap memos where the `Expr`-level
code allocated transient trees (445 G instructions vs 212.6 G pre-#62,
even after task #63's index threading; the result cache alone did not
help — the pairs are mostly distinct).  Resolution: `isEquivLM`
simplifies both sides on the arena (persistent memo), reads the small
*simplified* levels back and runs the **spec** `Level.leqCore` on
transient trees, caching the verdict per index pair — faithfulness is
`simplifyLIGo_spec` + `readbackL_spec` + the spec function itself.
This turned the regression into a win (init-prelude 171.7 G / 12.4 s,
−18 % vs the pre-#62 baseline).  The superseded pure `leqCoreLI`
family and its `ILevel` faithfulness proofs (~1 800 lines) were
deleted once the readback approach was confirmed.

## Cross-declaration environment index; kind-agnostic certificates (2026-08-22, task #63)

Two changes, one theme: no executable-path environment lookup walks
`env.consts`.

**`Env.findThm?` is gone.**  The iota-certificate checks consumed a
stored `_model.iota_j` *theorem*'s statement; the theorem-kind filter
was an over-restriction — any stored constant witnesses its type's
inhabitation in the model (`EnvModel.mem_type` is kind-agnostic).
`Env.findCV?` returns the stored constant's `ConstantVal`;
`PlainChecked`/`NestedChecked` carry a generic `ConstantInfo` plus its
`toConstantVal` equation, and the `Extend/Recs`, `BridgeWfImp`,
`BridgeS2` consumers use `find?_mem` directly.

**The index is threaded across declarations.**  `checkDeclSF :
FEnv → Declaration → CheckIM FEnv` replaces the per-declaration
`mkFEnv` rebuild: the index is built once (`mkFEnv Env.empty`) and
each accepted constant is one `FEnv.push` (definitionally `mkFEnv` of
the cons-extended environment, `mkFEnv_push`).  Every checker-side
lookup goes through the index: `Setlec/Kernel/CheckerS.lean` holds
`F`-mirrors of the generic checker functions (`checkConstantValF`,
`checkMemberValF`, the iota pipeline `checkIotaThmF/NF`,
`nestedRuleShapeF`, `checkIotaRuleF/RulesF`, the projection stages,
`checkDefnValF/ThmValF/OpaqueValF`, `installBasisDeclF`,
`checkDivModCertsF/PinF`) and indexed guard twins (`constsResolveF`,
`natOpStoredOkF`, `stdAxiomOkF`, `divMod*F`, `checkEtaThmF`,
`checkUnitThmF`, `indBlockCapsF`), extending the existing
`natOpGuardF` family.

Verification (`Setlec/Verify/CheckerF.lean`): under `mkFEnv` each
mirror *is* its generic counterpart — the mirrors differ only in pure
lookup subterms, which `mkFEnv_find?` rewrites away (`simp only`
plus a final defeq `rfl` across the distinct matcher constants).
Environment-extending mirrors are related in *push form*
(`checkDefnValF_push` …: mirror `= generic >>= pure ∘ mkFEnv`, proven
by monad-law normalization at `CheckIM`; `throw`-bind and
`push_mkFEnv` are definitional).  `checkDeclSF_nonind` assembles the
non-inductive branches, so `Setlec/Model/BridgeS.lean` rewrites the
mirrors away and reuses the existing single-environment walks; the
run lemmas thread the `fe = mkFEnv fe.env` shape through every push,
and `Setlec/Model/ConsistencyS.lean` folds the index with that shape
invariant.  The consistency statements' shapes are unchanged
(`checkDeclsShared : List Declaration → CheckM Env`).

**Measured**: scale harness `chain` 1.59 → **1.04**, `many` 1.56 →
**1.04** (PASS; `spine` 2.11 / `telescope` 1.94 remain, diagnosed
above); init-prelude 488 G → 445 G instructions from the threading
alone, then 171.7 G / 12.4 s with the readback `leqCore` (task #62
note above) — **−18 % instructions vs the pre-#62 baseline**
(208.3 G / 15.5 s, same machine/day).

**Follow-ups** (performance, in expected-value order): (1) the
binder-walk rework (accumulated fvars + bulk domain instantiation) for
`spine`/`telescope` and the real init-prelude binder costs — done,
task #72 below; (2) level-op constant factors on shallow levels —
avoid per-call memo/`Option` allocation in `leqCoreLI`'s node views
and `byCasesLI`'s four fresh-memo substitutions (persistent keyed
subst memo, or a small-level fast path); (3) per-node scope data for
O(1) instantiate/abstract identity shortcuts — done for instantiation
(the `bvarB` bound cache, task #72 below).

## Binder-opening discipline: telescope loops, chain-sharing intern, scope shortcut (2026-08-23, task #72)

The residual `spine`/`telescope` ~n² (exponent 1.94 each) had three
sources; all three are fixed, `tests/scale.sh` passes all four shapes
(chain 1.04, spine 1.29, many 1.04, telescope 1.17):

**1. Binder-telescope loops** (the official-kernel discipline;
lean4lean's `inferLambda`/`inferForall`, `Lean4Lean/TypeChecker.lean`).
The interned annotate/infer binder cases peeled one binder per knot
level, with a whole-body `instantiate1IGo` on the way in and a
whole-body `abstract1IGo` on the way out — O(n²) on a depth-n
telescope.  `annotatePisI`/`annotateLamsI`/`inferLamsI`
(`Setlec/Kernel/CoreI.lean`) now peel the whole raw chain in one loop:
opened free variables accumulate, only each binder's *domain* is
substituted on the way in (`instListM` against the accumulator;
domains are small), the leaf is annotated/inferred once on the
bulk-opened body, and the chain is rebuilt with one bulk
`abstractRange` per domain and one over the leaf
(`Expr.abstractRange` + `EStore.abstractRangeIGo`, the innermost-first
`abstract1` fold in one pass — `abstractRange_succ`).  The chained
re-inferences of freshly built binder nodes are value-determined by
the peel phase's domain sorts (an annotated `∀`'s type is
`imax`-algebra), so the out phase replays only the fallible checks —
the per-level "expected a sort" domain checks and λ-annotation
re-checks, in the chained order.  The lam cases of `inferBodyNC` share
`inferLamsI`; `coreKnotNC`'s annotate is the shared certified body, so
the `SETLEC_NO_PROOF_CERTS` knot gets the loops for free.

The λ-annotation loop is guarded on the node's loose-bvar bound (O(1)
from the `bvarB` cache): the chained tails re-open exactly the body
they just closed, which is the identity only on bvar-closed nodes —
disciplined inputs always are, and the unguarded per-binder body
remains as the (unreachable in practice) fallback arm.

**Verification seam** (`Setlec/Verify/BinderLoop.lean` +
`BinderLoopI.lean`; the `Expr`-level spec bodies are untouched): pure
mirrors of the loops (generic over the core record), `_atF`/`_mono`
batteries, and *soundness of each loop against the chained spec* — a
successful mirror run at the pure fueled knot is reproduced by the
original one-binder-at-a-time body at some fuel.  The induction is
direct (head-first, no snoc): the chained tails are folded as *wraps*
(`inferLamsWrap` …), the loop's out phase is identified with them
per-entry (the rebuild equality is the `abstractRange_succ` fold; the
λ-annotate wrap's reopen is `abstract1_instantiate1` with
`LeafCond`/`looseBVars` invariants carried through the peel via the
`annotateCore` leaf/scope preservation toolkit).  The interned walks
(`DiscI4`/`DiscI6` binder cases) relate the loops to the mirrors under
denotation only (`RelD`), then compose with `SimAt.wr` (mirror run →
chained run, via the soundness theorems) and `SimAt.wp` (result
scoping recovered from the chained run); `SimAt.bindR` remembers the
walked pre-checks' fueled runs to seed the wraps' domain facts.
Claims, Model, and the bridges are unchanged.

**2. Entry-boundary level interning** (`EStore.internExprFast`,
`Setlec/Kernel/IExpr.lean`).  An annotated telescope's codomain
annotations are `imax`-chains of depth O(n); each entry runner
re-interns the annotated expression into a fresh arena, and
`internLevel` walked each chain structurally — O(n²) *per entry call*
even though `readbackI` shares the chains in memory (one level memo
per readback).  `internExprFast` exploits exactly that sharing: at a
binder whose annotation is `imax _ (child's cod)` — pointer-checked by
`withPtrEq`, which is *definitionally* its structural continuation, so
proofs see plain equality — the already-interned child index is reused
instead of walking the tail.  `internExprFast_eq` proves it equal to
`internExpr` as a function (`internLevel_of_denoteL`: re-interning a
stored level is a pure lookup), so the entry-runner bridges rewrite it
away.  Raw inputs carry no codomain annotations, so the fallback
structural comparison never walks deep unequal trees.

**3. The scope shortcut** (`IState.bvarB` + `EStore.bvarBoundIGo`).
Each interned node's least loose-bvar bound is cached *persistently*
(a node's bound depends only on its immutable sub-DAG, so the cache
survives arena extension and every node is bounded at most once per
run); `inst1M`/`instListM` return their argument index untraversed
when the cursor is at or above the bound (`instantiate1_eq_self`/
`instantiateList_eq_self`; on a canonical arena the traversal would
rebuild the same index).  This is what makes `inferSpineI`'s deferred
residual substitutions O(1) on non-dependent telescopes (the `spine`
shape's remaining cost).  `ISOK` gains the `bvarB` clause
(`BoundMemoInv`).

**Measured** (init-prelude probe, instructions): 205.5 G / 15.6 s →
**187.8 G / 14.0 s** certified (−8.6 %), 151.8 G / 10.5 s →
**142.8 G / 9.7 s** with `SETLEC_NO_PROOF_CERTS=1` (−5.9 %); verdicts
identical everywhere (arena 90/92, e2e 48/48, both modes).  Remaining
known superlinear residues (small constants, below the harness gate at
its sizes): the per-prefix `inferSpineI` re-walk when `annotate`'s app
case infers every spine prefix against the root telescope (Σ O(i)
view-steps and per-prefix argument-list allocation; a spine loop in
`annotateBodyI`'s app case would remove it — **done, task #96**), the
`List.toArray` conversion inside `instantiateListI` per non-identity
call with a growing accumulator (**done, task #97**), and
`Expr.allLevelParamsDefined` walking deep codomain-annotation trees
once per declaration guard.

### Theorems are delta-unfoldable (verified 2026-08-23)

The kernel delta-unfolds theorems, with the implicit `opaque` hint
(unfold last) — matching the *current* official kernel: C++
`constant_info::has_value()` (`declaration.h:466`, byte-identical on
lean4 master as of 2026-08-20) includes theorems and is what
`type_checker::is_delta` consults.  Trap for the reader: lean4#12973
made the *elaborator-facing* `declaration::has_value` /
`ConstantInfo.value?` exclude theorems ("now treated like opaque
declarations"), but left the kernel predicate untouched — the two
`has_value`s differ.  Empirical confirmation: the official arena
binary accepts `good/undecidability/subject-reduction-redex` (whose
only unfoldable constants are theorems) and rejects it with the
theorems rewritten as axioms.  See lean4lean
`Lean4Lean/Declaration.lean` (`deltaValue?` doc comment) for the same
observation.

## Parse-time interning: the parser's sharing made structural (2026-08-23, task #78)

The export format shares subterms via table indices; the previous
frontend rebuilt plain `Expr` trees whose sharing was heap-pointer-only
— invisible to every structural traversal — so DAG-shaped input (arena
`good/perf/app-lam`: 24k table entries, ~10^1160 unshared tree) was
exponential in the raw syntactic passes and at the checker's per-entry
interning boundary.  The pipeline is now DAG-preserving end to end:

* **Parse into the arena** (`Setlec/Frontend/Export.lean`): expression-
  and level-table entries are interned directly into an `EStore` — one
  `intern` per record, children resolved to already-interned indices,
  `O(1)` per entry.  Declarations are `DeclP` records
  (`Setlec/Kernel/DeclI.lean`) carrying `EIdx`/`ConstantValP` fields;
  `parseExport : String → Except _ (EStore × Array DeclP)`.  `Expr`
  trees are read back (memoized, pointer-shared) only where a genuinely
  bounded consumer needs them: basis/quotient pin matching and
  inductive blocks (`.indDecl` still carries `ConstantInfo`s — the
  install pipeline compares member types/rule right-hand sides against
  `_model` artifacts with tree traversals).  Taint tracking (skipped
  axioms) is per-entry `O(1)` as before.
* **Budget re-scoped, not deleted.**  The unshared-tree-size budget
  (task #65) no longer applies to ordinary definition/theorem/opaque
  records — their whole pipeline is index-level, so `app-lam` (def
  value at 2^4000) and the former `dag_tower_declined` fixture (now
  `dag_tower`, expectation flipped to accept) check fine.  It stays,
  with reason, on the record kinds whose *stored* artifacts are later
  consumed by tree traversals: inductive and quotient blocks (readback
  + canon matching, `_model` comparison, iota statements), axiom
  records (standard-axiom pin matching walks the stored type), records
  whose name contains a `_model` component (iota/eta/unitlike
  statements are `openPisAtFvars`-opened at a later inductive install),
  and the certified `Nat` operations (`natOpNames`/`natDivModNames`:
  the install-time certification substitutes the stored value into the
  recurrence equations and re-interns the result).
* **Index-level drivers** (`Setlec/Kernel/CheckerS.lean`,
  `checkConstantValP`/`checkDefnValP`/`checkThmValP`/`checkOpaqueValP`,
  `checkDeclSP`, `checkDeclsSP`; NC twins in `CheckerNC.lean`): raw
  checks (`looseBVarsBoundedI`/`hasFvarI`) and post-annotate checks
  (`allLevelParamsDefinedI` — new walker with level-side companion —
  and the indexed `constsResolveFI`) run DAG-memoized on the arena;
  the knot entries are called on indices (no per-entry tree intern, no
  intermediate readbacks); the constant is read back once, at the
  environment push.  The spec `Env` still stores `Expr`s — the Model
  layer is untouched.
* **One `IState` per run** (nanoda's parse tier): `checkDeclsSP`
  validates the parse store once (`wfB`, the decidable counterpart of
  `EStore.WF`), seeds the fold's single state with it, and `flushS`
  drops only the environment-dependent caches at declaration
  boundaries and environment transitions — the arena, the interned
  environment, the loose-bvar-bound cache and the level-operation
  caches persist (all environment-free).  Per-declaration reduction
  temps accumulate in the arena for the whole run (no truncation —
  that is task #64's two-tier arena, deliberately not built here).
* **The interned environment** (`IState.ienv`): per accepted
  definition/theorem/opaque/axiom, the arena indices of the stored
  annotated type/value, each *tagged with its own denotation* — the
  very objects pushed into the `Env`.  `constTyAtM`/`constValAtM`
  consult it before falling back to tree interning; a use validates
  the tag against the current stored constant with a pointer test
  (`EStore.exprPtrBEq`, definitionally `==`), so the cache is
  *self-certifying*: its invariant (the `ienv` clause of `ISOK`) ties
  indices to tags only, never mentions the environment, and survives
  every flush and environment transition with no freshness lemmas.
  Consequence: delta-unfolding a stored DAG-shaped constant
  instantiates on the arena instead of re-interning a read-back tree
  (e2e `dag_tower_unfold`: a theorem forcing both sides' 2^28-node
  stored values open — accepted in 0.2 s).  The loose-bvar-bound cache
  became a dense array (`EStore.BMemo`, slot = bound+1) — on
  binder-heavy DAGs it holds an entry per node, and the hash map's
  ~48 B/entry was ~3 GB on app-lam.
* **Verification** (the parsed-index consistency chain):
  `wfB_wf : wfB = true → EStore.WF` and the walker specs live in
  `Setlec/Verify/ParseP.lean`, together with `denoteDeclP` — the
  parsed-declaration denotation that identifies a `DeclP` with the
  spec `Declaration`, total on in-range indices (the per-declaration
  `inRangeB` gate) and `Ext`-stable.  `Setlec/Verify/BridgeP.lean`
  walks the index-level drivers as `SimAt`s against the generic
  `checkDecl` at the fueled families **on the denoted declaration**
  (the knot simulations `ssimI` apply directly given the argument's
  denotation; `recordIConst` is sound by `ISOK.insertIEnv`).  `ISOK`
  gained the `ienv` clause; its environment-free residue `ISOKF`
  (arena canonicity + level caches + bound cache + `ienv`) threads the
  persistent state across declarations — `flushS_isok : ISOKF s →
  ISOK env' s.flushed` for any environment — and the shared-driver run
  lemmas (`Setlec/Model/BridgeS.lean`) now conclude `ISOKF` and arena
  extension.  `Setlec/Model/ConsistencyP.lean` restates the top-level
  statements for what the binary now runs, with **no hypotheses beyond
  acceptance** (the `wfB` and `inRangeB` gates are inside the checked
  function): `checkDeclsSP_sound`, `no_proof_of_Empty_SP`, and the
  stream-level `no_proof_of_Empty_input_SP` — a `def`/`thm` record
  whose parsed type index *denotes* `.const Empty []` in the parse
  store is never part of an accepted stream.  The `checkDeclsShared`
  statement family (`ConsistencyS`) is retained unchanged; axioms of
  the `_SP` family: `propext, Classical.choice, Quot.sound`.

**Measured.**  `good/perf/app-lam` **accepts**: 119 s / 7.6 GB peak RSS
(previous pipeline: declined by the budget; lean4lean: 3.95 s /
1.44 GB).  The dominant cost is inherent to per-binder-instantiation
kernels on this shape (the innermost body reads all 4000 binders, so
each binder open/abstract rebuilds the remaining ~24k-node DAG:
~64M arena nodes over the declaration; the references pay the same
traversals but their temporaries are garbage-collected, while the
single-tier arena retains them — task #64's truncation is the lever).
`beta-ladder` stays accepted (27 s).  Arena 90/92, e2e 49/49 (the two
new fixtures), scale.sh all-PASS (chain 1.04, spine 1.28, many 1.04,
telescope 1.13).

**The whole-arena copy-on-write strikes: root cause and fix.**  The
persistent arena initially regressed the certified init-prelude probe
(176.5 G → 272.8 G instructions; 391.7 G with `SETLEC_PROGRESS=1`);
`SETLEC_NO_PROOF_CERTS=1` looked unaffected only because its arena is
small.  gdb forensics (breakpoints on the runtime's
`lean_copy_expand_array_nonlinear` non-linearity gadget, `finish` +
hardware watchpoints on the fresh tables' refcount words, holder scans
over the heap) counted ~6100 whole-table copies per run — `nodes`
pushes and `cons` bucket usets finding their table at RC 2, ~2 per
declaration — and named two holders, both *compiler-liveness*
artifacts, no source-level sharing at all:

1. **Sinkable pure store reads.**  `withStore f` inlined to the pure
   application `f s.store`; whenever the result was not consumed
   before the next knot call, the Lean compiler *sank* the application
   past that call (profitable when the call can throw) — e.g.
   `inferBodyI`'s app case computed `getAppArgsI` only *after*
   `r.infer depth h` returned, keeping the projected `EStore` alive at
   RC 2 across the entire nested inference.  Every arena mutation
   inside such a window copies the shared tables.  Fix: `withStore` is
   `@[noinline]` — an opaque state-threading call cannot be reordered,
   so the projection lives and dies inside the callee.  (`viewI`'s
   result is always immediately matched — branch selection forces it
   before any later state op — so it stays inline.)
2. **The progress loop's boxed accumulator.**  `Main.lean`'s
   `SETLEC_PROGRESS` path was a `for`/`mut` loop; the compiled
   `forIn` keeps the previous iteration's `(fe, s)` state tuple live
   into the next step call, so the interned state *entered every
   declaration* at RC 2 and the first mutation struck (+110 G in both
   modes).  Fix: `progressLoop` — explicit tail recursion with the
   accumulators as plain arguments (and the per-iteration
   `IO.getEnv "SETLEC_STATS"` hoisted).

**After the fix** (same probe, same day): certified 181.7 G / 12.9 s
progress-off and 181.8 G / 13.0 s progress-on (parity with the
pre-#78 176.5 G / 12.5 s base, measured while a concurrent build
loaded the machine); NC 139.4 G / 9.0 s (*better* than its 142.8 G
base); big-table non-linear copies 6126 → 1 per run (the survivor is
the parse-result pair pinning the store during declaration 1 — the
compiler retains `.ok (store, decls)` into the fold; one small early
copy, not worth restructuring `checkMain` over).  The residual
certified +5.2 G (+2.9 %) over the pre-#78 base is the `withStore`
call boundary (a real call + closure per read that used to inline
away) plus the one-time parse of the whole export table into the
arena — the price of the fix and of the architecture, not a leftover
strike.  Two forensic
lessons recorded: RC-2 discovered at a mutation was *taken* far away
— walk holders with heap scans plus refcount-word watchpoints, don't
trust the striking frame; and freed-but-unreused shells (shallow
`lean_free_object` of destructured records) make post-hoc pointer
scans lie — only a watchpoint at the moment of the inc is
conclusive.

## Streaming frontend (2026-08-23, task #57)

The frontend no longer materializes the export text: `checkMain`
streams.  `Frontend.parseExportStream` reads the ndjson **line by
line** from a handle (explicit tail recursion with the parse `State`
as a plain argument — never a `for`/`while` loop, whose boxed state
tuple keeps the arena shared across the step and turns every insert
into a whole-table copy, the same pathology as the #78 progress
loop), feeds each record through the shared `feedLine` step (also the
body of the wholesale `parseExport`, kept for tests), and drops the
line; each line is newline-stripped exactly as `splitToList (· ==
'\n')` did (a `\r` before the newline is kept), so verdicts, error
messages and line numbers are unchanged, including malformed input
mid-stream (exit 3 at the same line; e2e `malformed_midstream`).
Parse-time interning (#78) is untouched: retained memory is the parse
arena, the tables and the `DeclP` records — proportional to the
arena, never to the text.  JSON strings are built fresh by
`Json.parse` (`acc.push`-style), so nothing retained pins a line
buffer; the read line is `copy`-detached before parsing as extra
insurance (core's `Handle.lines` pattern).

The **preprocessor spawn** no longer pipes: `preprocess` stream-scans
the input for `inductive`/`quot` records (ndjson keys cannot span
lines), and when the tool is needed it writes to a **temp file**
(`-o path`, `IO.FS.createTempFile`; honors `TMPDIR` — commonly tmpfs,
point it at a disk for huge streams) which `parseExportStream` then
reads and `checkMain` removes (`try`/`finally`).  This process never
holds input or output wholesale; the residual is the tool's *own*
working memory (~650 MB on init-full), unavoidable until
lean-inductive-models itself streams.  The diagnostic
failing-declaration second pass re-parses from the same file.

**Measured** (GNU time max RSS over the process tree, perf
instructions, same machine, before → after):

* init-prelude probe: 191.8 MB → 185.8 MB, 30.51 G → 29.53 G instr
  (−3.2 %), 3.0 s wall, verdict identical (exit 0, 3653 accepted).
* repro-extract-proof11-pre (20 MB): 242 MB → 233 MB, exit 0 / 2486
  accepted both sides.
* init-full-pre2 (335 MB, the largest stream): 3.07 GB → 650 MB peak
  (now the *preprocessor child's* own RSS; the checker itself peaks at
  548 MB, measured with an identity preprocessor), 26.8 s → 21.3 s,
  verdict identical — **exit 2 by design**, not a resource wall: the
  stream declines at `opaque Lean.reduceNat` (line ~2 446 395 of
  6 223 893, 39.3 % in), the first *use* of the skipped
  `Lean.trustCompiler` axiom, exactly the axiom-ceiling behavior
  documented above.  (The task's "~30 GB to parse init-full" predates
  #78/#84; at the current base the wholesale cost was the 3.07 GB —
  contents + preprocessor stdout + the eager per-line split all held
  at once — which streaming removes.)  Since the taint
  skip-and-continue (2026-08-24, below) the parse no longer dies
  there: the whole 6.2 M-line stream parses (exactly two taint skips,
  `Lean.reduceNat`/`Lean.reduceBool`, both via `Lean.trustCompiler`)
  and *checking* becomes the frontier — see the skip-and-continue
  section for the new numbers.

## Recursor-rule fold contract as total λ-equalities (2026-08-23, task #58)

`RecRulesOk` is restated per fireable rule as a **total λ-equality**:

    ∃ fvms bL, ruleLhsParts n cv rP r cvj = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧ fvms.length = rP + nfields ∧
      (closeLamsAt fvms bL).constsResolve env ∧
      ∀ ψ, AnnotOk (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed ψ (closeLamsAt fvms bL) = some Rv ∧
              interpClosed ψ rhs = some Rv

`ruleLhsParts` (Model/Interp.lean) is the canonical decomposition: the
recursor type's `rP`-prefix opened at fvars, the constructor type
instantiated at the parameter arguments (plain: the prefix variables;
nested: the stored pins at the stored levels), its fields opened, the
body the recursor applied to prefix ++ residual indices ++ the
constructor spine, and the frame's binder metas taken from the rule
rhs's own λ-tower.  Consumers (`iota_sound`) recover the redex by
`closeLamsAt` and never see fitting frames.

**Install-time derivation** (Model/IndInstall.lean, plain and nested):

* `modeled_stage` — the per-binder stage fact (frame annotation's
  interp = rule λ-domain's, plus `AnnotOk` and the frame-prefix
  invariant step), fire-agnostic given an abstract constructor-residual
  package (`ctor_pkg_plain` / `ctor_pkg_nested`, the latter walking the
  kernel's typed pin list `TypedListOk`).
* `modeled_bottom_plain` / `modeled_bottom_nested` — at the full frame,
  eliminate the checked `_model.iota_j` theorem's inhabitant
  (`TeleFitI.elim` + Eq collapse) into the value equation between the
  canonical body and the applied rhs; nested rules are index-free
  (`mI = rP`) with the major's parameters the level-instantiated pins.
* `TowerOk.of_stages` (Model/RuleFold.lean) — folds the flat stage
  facts and the bottom fact into the λ-tower equality at the canonical
  list valuations, tracking the rule-tower residual up to `ErasedEq`.
* `Extend/Recs.recMemberOk_of_kit` — derives each clause from the
  checked kits at the provisional environment and transports to the
  final one.  Nested renaming idempotence comes from blockNames
  containing no model-shaped names (`checkIndFold_modelfree`,
  `provisionRecs_modelfree`), threaded as a hypothesis.

The old fitting-frame machinery (`IndInstallN.lean`, whose elaboration
peaked at ~16 GB) is **deleted**; `IndInstall.lean` holds the whole
pipeline.  Projections were rebuilt on the same machinery
(`ProjInstall.lean`: `proj_bottom`/`proj_rule_eq` via `of_stages`).

**Kernel pins added for the contract** (install-time, once per
rule/projection; measured probe cost +0.02% instructions, no corpus
verdict changes — arena 90/92, e2e 48/48, init-prelude 0/3653):

* `checkIotaThm` (plain): the statement telescope's parameter domains
  are checked defeq (`checkDefEqList`) against the recursor type's
  instantiated domains, and the constructor's field domains against
  the instantiated constructor type's.
* `checkIotaThmN` (nested): the same walks against the
  level-instantiated constructor type, the pins checked as a typed
  list (`checkTypedList`), plus the arity pin
  `crest2.getAppArgs.length = cnP` (index-free canonical body).
* `checkProjShape`: the projection type strips to `nP + 1` binders
  with a const-headed residual applied to the `nP` parameters.
* `checkProjRule`: takes the projection type, opens both types at
  shared fvars with `checkDefEqList` domain pins, and runs
  `ops.inferType` on the rule rhs (interpretation-existence witness).

The official kernel constructs these objects itself (recursor/
projection rules are generated, so the shapes hold by construction);
setlec checks them because the artifacts arrive from the preprocessor
as input.  Failures are declines, not rejections.

## Direct install of simple structures (2026-08-23, task #82)

The first inductive class that needs **no `lean-inductive-models`
artifact**: a *simple structure* — non-recursive, single-constructor,
index-free, parameters and dependent fields allowed, with a **provably
nonzero result sort**.  For such a block the checker installs the type
former, the constructor, the recursor with its single rule and the
projection functions from the *reference checks alone*, and the
set-theoretic model is **constructed** rather than borrowed.

### The class, and why the sort must be nonzero

The model of `T p⃗` is the iterated dependent pair over the interpreted
field telescope, closed off by the singleton — literally the tower the
preprocessor builds syntactically out of `PSigma'`/`PUnit`, built
directly out of `SetTheory.sigmaSet` (`Setlec/Model/DirectTower.lean`).
`sigmaSet w` *collapses to a truth value at `w = 0`*, which destroys
`proj_i (mk f⃗) = f_i` for a `Prop` structure carrying data fields.
Rather than case-split the whole construction on the collapse, the
recognised class requires `Level.isNonZero` of the result sort
(**finding / narrowing**): `Prop` structures (`And`, `Iff`, `True`,
`Exists`, `Nonempty`, …) and `Sort u`-parametric ones (`PProd'`,
`PSigma'`) simply stay on the modeled path, which handles them today.
Measured on the init-prelude stream: of 149 inductive blocks, 117 have
the single-type/single-ctor/single-rec shape and **103 are recognised**
— every class-like structure (`Add`, `Monad`, `Prod`, `Subtype`,
`Fin`, `Array`, `String`, `UInt*`, …).

### Recognition (`Setlec/Kernel/Direct.lean`) — the reference checks

`directParts?` is a **conservative filter**: a block it rejects falls
through to the modeled path unchanged, so a negative answer never costs
a verdict.  The checks mirror what the reference kernels do when
*adding* an inductive declaration (citations: lean4lean
`Lean4Lean/Inductive/Add.lean`, a line-by-line port of the official
`src/kernel/inductive/inductive.cpp`; nanoda
`checker/src/inductive.rs`), restricted to this class:

* type former: a `∀`-telescope of exactly `numParams` binders ending in
  a `Sort` (`checkInductiveTypes`, `Add.lean:60-116`) — index-free
  means it ends there; the result level is `isNeverZero`
  (`Add.lean:101`), which here is *required*, not just observed.
* constructor: a `∀`-telescope ending in the type former applied to
  **exactly** the parameters at the declaration's own level parameters
  (`isValidIndAppIdx`, `Add.lean:157-165`, nanoda `is_valid_ind_app`);
  its parameter domains are the type former's (`Add.lean:220-222`,
  by `isDefEq` there and here — see below).
* non-recursive: every constructor binder domain already resolves in
  the *pre-block* environment.  This subsumes `checkPositivity` /
  `hasIndOcc` (`Add.lean:184-199`) for a single-inductive block and is
  exactly what the model needs: the type former's value is built from
  the field types' interpretations in the environment *before* the
  block, so a self-reference would be circular.
* per-field universe bound: each field's sort `≤` the result sort
  (`Add.lean:225-228`, nanoda `check_ctor`, `inductive.rs:809`); the
  `Prop` escape hatch there is unreachable in this class.
* recursor: **exactly** the generated shape (`Add.lean:477-483`) —
  a fresh elimination level parameter in front (`getRecLevelParams`,
  `Add.lean:416-417`; every nonzero-sorted structure is a large
  eliminator, `isLargeEliminator`, `Add.lean:257-259`), params, one
  dependent motive `∀ (t : T p⃗), Sort ℓ` (`Add.lean:326`), one minor
  premise over the constructor's field telescope ending in
  `motive (C p⃗ f⃗)` (`Add.lean:384-388`), no indices, the major, and
  the body `motive t`; and `majorIdx = rulePrefix = numParams + 2`.
* the single rule's right-hand side is `λ p⃗ motive minor f⃗, minor f⃗`
  (`mkRecRules`, `Add.lean:441-447`).

Skeleton checks are syntactic (`directShape`, run on the raw block for
recognition **and** re-run on the annotated constants at install).  The
binder-*domain* correspondences are deliberately **not** syntactic: the
references compare the constructor's parameter domains by `isDefEq` and
build the recursor's telescope from `whnf`-peeled domains, so a
syntactic pin would wrongly reject (measured: 29 of 103 recognised
blocks fail a syntactic parameter-domain pin, 22 fail a syntactic
minor-premise pin).  `checkDirectStruct` pins them **definitionally**
over one shared opening of the recursor's telescope — which is also
exactly the interpretation equalities the model's telescope walks
consume.

### Projections compose with the existing table

The direct path installs projection *functions* into the **same slot
family and same consumer** as the modeled path's `checkProjFn`: a
degenerate recursor (no motive, no minors, no indices, one rule
`λ p⃗ f⃗, f_i`) stored under `projFnName T i`, which is the name
`annotateProjElim` dispatches on — so `.proj` nodes on a direct
structure rewrite into `T.proj.i` applications exactly as on a modeled
one, and the generic iota machinery reduces them.  Only the projection
*type* comes from a different source: generated from the constructor
telescope (`directProjTy`: `∀ p⃗ (t : T p⃗), F_i[f_j := T.proj.j p⃗ t]`,
built with the capture-avoiding `Expr.instPisAtLift`, since the
substituted arguments are open) instead of read off a
`_model.proj_i` artifact.  No new projection mechanism is introduced,
and the `native = false` template entries stay what they are (the Prop
fallback).

**Finding**: the recursor-elimination *template* fallback
(`annotateProjRec`) cannot serve this class.  Its motive is constant in
the eliminated variable, so the minor `λ f⃗, f_i` only typechecks when
`F_i` does not mention earlier fields — fine for `Prop` structures
(proof irrelevance) but wrong for a *dependent* projection such as
`Sigma.snd`.  Installing real projection functions is therefore not an
optimisation but a requirement.

**Where the clause lives.**  The module split `CheckerBase ← Modeled ←
Checker` (task #83) puts `checkIndDecl` in `Modeled` and
`checkDirectStruct` in `Checker`, so `checkDirectStruct` is not in
scope inside `checkIndDecl`.  The direct clause therefore dispatches in
**`checkDecl`** (and its shared-state twin `checkDeclSF`), not inside
`checkIndDecl` — do not look for it there.

### Precedence: artifact-free, not artifact-first

The brief ordered the clauses *basis → direct → modeled*.  The landed
order is *basis → modeled (when the artifact is there) → direct*:
`directNoModel` requires that none of `T._model`, `C._model`,
`T.rec._model` and the `T._model.proj_j` family is stored.  Reason: the direct
install declares `eta := false` (the frame-relative-law obstacle, see
"The two frame-relative capabilities"), so firing the direct path
ahead of an available artifact would drop `eta` for every structure
that has one, which loses arena `109_structEta` (and
`082`/`083`/`084`/`096`, the dependent-projection tests, before
projection functions were added).  (The original finding here — that
`EtaLaw` was `_model`-named and only establishable at the former's
install — is superseded by task #83: the law is now public-named and
established at the family-completing member.  What keeps the
precedence is the missing direct-eta discharge alone.)
Gating on artifact *absence* keeps every preprocessed stream on exactly
today's route, byte for byte, and makes the direct path precisely the
**ind-models-free** route the endgame wants.  The endgame is unchanged:
once `lean-inductive-models` skips generation for this class, the
direct path takes over by absence, and lifting eta into it is a
separate, well-identified piece of work (the `EtaLaw` public-name
restatement landed with task #83; what remains is discharging the
frame-relative law from the direct construction).

Side effect, kept: three arena `bad` fixtures (`133_dup_ctor_def`,
`134_dup_rec_def`, `137_dup_ctor_rec`) are hand-written raw exports, so
the direct path sees them and **rejects** (exit 1, "duplicate
declaration `X.mk`" / "`X.rec`") where the modeled path *declined*
(exit 2, "missing model for `X`").  Reject is the reference-correct
verdict for a duplicate name.

Re-derived after the group-local restructure (2026-08-23): the flip is
unchanged and has nothing to do with the deleted `modelFamilyTaken`
guard — it is `checkConstantVal`'s ordinary duplicate check inside
`checkDirectStruct`, reached because `directParts?` recognises these
raw blocks.  Measured on the new master with the clause enabled: all
three still reject with the duplicate-declaration message, so the
expectation flips remain `2 → 1`.

### The constructed model

`Setlec/Model/DirectVal.lean` supplies the missing *introduction*
direction of the telescope machinery (everything existing —
`TeleFit.elim`, `closeLamsAt_fold` — is elimination-only):

* `teleLamV k d ρ ty S` — the `k`-binder λ-tower over the telescope
  `ty`, with each `lam`'s universe tag read off that binder's own
  codomain-sort annotation, and body `S` computed from the argument
  values;
* `teleLamV_mem` — it inhabits `⟦ty⟧` when the body inhabits the
  interpreted residual at every fitting spine;
* `teleLamV_fold` — applying it along a fitting spine computes the
  body.

`Setlec/Model/DirectTower.lean` supplies the structure's own value:
`sigmaTowerV` (iterated `sigmaSet` over the field telescope, closed by
`unitSet`), `tupleV` (iterated Kuratowski pair), `projV`, with
formation (`sigmaTowerV_mem_univ`, from the per-field universe bound
via cumulativity), introduction (`tupleV_mem`), the iota equation
(`projV_tupleV`) and **eta** (`sigmaTowerV_split`: every member is the
tuple of its own projections, and those projections fit the field
telescope).  The intended values are then

    ⟦T⟧      = teleLamV nP over the type former's telescope,
               body = sigmaTowerV over the constructor's field telescope
    ⟦C⟧      = teleLamV (nP+nF) over the constructor's telescope,
               body = tupleV of the field values
    ⟦T.rec⟧  = teleLamV (nP+2+1) over the recursor's telescope,
               body = the minor applied to the major's projections
    ⟦T.proj.i⟧ = teleLamV (nP+1), body = projV i of the subject

with `sigmaTowerV_split` supplying both the recursor's `mem_type`
(`motive x` is reachable from `motive (C p⃗ (projs x))` because
`tupleV (projs x) = x`) and the rule's fold equation
(`projV_tupleV`).

### Group-local identification (2026-08-23, task #83)

The `T↔T._model` identification is **group-local** — the actual
`lean-inductive-models` contract (upstream commit 572e6de, "Clarify
checker substitution scope"): a block's artifacts carry their source
declarations' exported types under one simultaneous **current-record**
rewrite; names belonging to any *other* inductive record remain source
(public) names, whether or not that record has a model.  Cross-group
references to `_model` *definitions* in model bodies are ordinary
stored-definition references, handled generically by
`defn_eq`/`mem_type` — no cross-group value linkage exists or is
needed.  The kernel side always was group-local
(`checkMemberVal`/`checkIndRecs` build the rename from
`blockNames = block.map (·.name)`, the current block only); task #83
made the verification match:

* **Post-install, the environment remembers nothing about install
  provenance.**  The former `ModeledOk` invariant — persistent
  `val n = val (n._model)` linkage clauses plus the capability laws —
  is deleted.  `EnvModel` keeps only provenance-abstract clauses; the
  capability laws live in `CapsOk` (`Setlec/Model/Interp.lean`):
  - `EtaLaw` is restated over **public** names (`caps.etaCtor`,
    `projFnName T j`), premised on the family being *stored* at the
    record's exact kinds and arities (`EtaFamilyStored`);
  - `UnitLaw` is unchanged (it only ever mentioned the former);
  - basis families stay exempt (`reservedBasisNames`); their eta/unit
    facts ride the pinned `IndOk` clauses as before.
* **The identification lives only inside the one block's install
  derivation.**  `BlockInstalled` (the member-fold invariant, now also
  carrying each member's checked rename fact) and the projection
  phase's `ProjPhaseInv` *are* the group-scoped identification; they
  are threaded through the block's extension proof and discarded at
  its end.  The public `EtaLaw` is discharged at the
  **family-completing member's** install — the constructor for a
  fieldless structure, the last projection function otherwise — by
  `modeled_caps_eta`/`modeled_caps_unit`
  (`Setlec/Model/ModeledCaps.lean`): `eta_rule_fold` at that member's
  environment plus the group identification rewrites the `_model`-
  valued law to the public names.  Mid-block — the former stored, its
  family pending — the premise fails and nothing is owed, which is
  what lets every intermediate environment carry a plain `EnvModel`.
* **`EtaFamiliesClosed`**, an env-only side invariant (every stored
  non-reserved eta-capable former has its capability constructor
  stored at the record's arities), is threaded through the consistency
  folds *next to* the model — it cannot be an `EnvModel` clause,
  because it is false in the in-block window.  Constructor-installing
  sites consume it to refute a fresh constructor completing an *older*
  former's family (that slot is already taken); the kinded/arity-pinned
  premises of `EtaFamilyStored` refute every other completion attempt
  (definitions, theorems, axioms, projection-table entries cannot
  complete a family at all, and projection-function names are only
  ever installed by a block for its own former).  The top-level
  consistency statements are unchanged in strength — the invariant
  starts trivially at the empty environment and is re-established per
  declaration.
* **No model-family guard.**  `modelFamilyTaken` (the
  `checkConstantVal` rejection of a companion declared after its
  constant) is deleted along with the linkage it protected: with the
  identification group-local, a late companion activates nothing.
  "`_model` names are not special" holds completely — no reservation,
  no shadow checks; `tests/e2e/src/model_name_plain.lean` (accepted)
  is the regression that none sneaks back.
* **The direct-structure installer is completely independent of
  modeled-inductive code**: no shared linkage clauses, no guards; its
  capability obligations are vacuous (`eta`/`unitlike` are `false`)
  and its extension steps discharge the same provenance-abstract
  clauses every other install does.  With `EtaLaw` public-named, the
  former blocker for a direct-install eta capability is gone (the
  frame-relative-law obstacle below still stands).

### The endgame: ind-models' skip rule must be dependency-aware

Once `lean-inductive-models` stops generating models for the direct
class, the direct path takes over by absence — but the skip has to be
computed over the *whole* export, not per declaration: a model may be
built out of an **earlier** model, so a type whose model some later
modeled construction references must keep its artifacts.  Leaf
structures skip; structures nested through by later modeled types keep
their models.  The constraint shrinks as the direct class grows.

Measured on the init-prelude stream: of 149 inductive blocks, exactly
**one** (`Trans`) has a model that references another block's model
(`LT`'s).  So the dependency is rare — nearly every simple structure is
a leaf and skippable — but real, and the tool has to compute it rather
than assume it away.

The checker is safe under **every** mixture of skipped and generated
models: the only failure mode is the decline/reject pinned by the
`direct_nested_dep_broken` fixture (a surviving artifact referencing a
model that was not generated → "unknown constant `X._model`", exit 1).
It never accepts such a stream.

**Hard preconditions: the two capabilities the direct install
declares `false`.**  It declares `eta := false` *and*
`unitlike := false`, which is safe only because the path is
absence-gated: today every structure that *has* an artifact keeps the
modeled route, and with it both capabilities.  The moment a skip rule
deploys, a directly installed structure would be the only one without
them — and for eta that **diverges from the reference kernels**: the
official kernel offers `to_cnstr_when_structure` to every non-`Prop`
single-constructor structure, so a stuck-major rescue that fires there
would stop firing here.  So before any skip rule can ship, both of the
following must land.

*Shared prerequisite — the frame-relocation lemma
(`TeleFit.reframe0`, not yet written).*  Both `EtaLaw` and `UnitLaw`
quantify over a parameter-telescope fit at an **arbitrary** frame,
while every constructed value is a λ-tower over the telescope's
*frame-0* opening, and `teleLamV_fold` is frame-matched.  So both need:
a value-spine fit of a **closed** telescope at any `(d, ρ)` yields one
at `(0, rho0 V)` with the same values.  The pieces exist —
`TeleFit.toTeleFitI`, `TeleFitI.sanitize`, `TeleFitI.instLev_down`,
`interp_instSeq_fvarFrames`, `peel_walk` — but `TeleFitI.toTeleFit`
reproduces whatever frame it is handed, so none of them lands at frame
0; the relocation has to be built explicitly (rebuild the canonical
opening at `0 … k-1` and lower the frames with `interp_lift`).  See
"The two frame-relative capabilities" above.

*1. `unitlike`.*  Needs nothing but the relocation lemma: the semantic
content is already proved (`directTyVal_unitlike` — a field-free direct
structure's tower is the singleton, so any two members coincide), and
`UnitLaw` is already free of `_model` names.  This is the cheaper of
the two and should land first, as the relocation lemma's first
consumer.

*2. `eta`.*  Additionally needs `EtaLaw` restated over public names:

* restate `EtaLaw` over the **public** constructor and projection-
  function names (`val caps.etaCtor`, `val (projFnName T j)`) instead
  of their `_model` companions;
* discharge it for the direct class from the constructions already
  proved — `directCtorVal`/`directProjVal` and `sigmaTowerV_split`
  (structure eta at the value level) give it essentially directly, and
  `directCtorVal_mem`/`directProj_body_mem` supply the memberships;
* the modeled path then derives the public form from its `_model` law
  plus the artifact linkage.  Note the ordering constraint this
  imposes: the public law mentions constants installed *after* the type
  former, so it must be premised on the block's constructor and
  projections being stored, and the modeled discharge moves from the
  type former's install to the block's last install (the linkage
  clause is exactly the record that makes that possible).  This is the
  reason the restatement was not folded into this landing.

### The install order, and why the type former's tower is guarded

**Finding (2026-08-23, the assembly).**  The four constants are
installed in the order the checker stores them, and the *first* of them
is the type former — the constructor's type ends in `T p⃗`, so it does
not resolve, cannot be annotated, and cannot be universe-checked until
`T` is stored.  So at the type former's own install the per-field
universe bound has not been checked yet: its semantic content
(`FieldTele`) is read off `inferTypeCore`/`ensureSortCore` runs in the
*extended* environment, and turning those into interpretation facts
needs `inferTypeCore_sound`, i.e. an `EnvModel` of that environment —
which is exactly what the type former's install is constructing.  A
plain "the tower is small" obligation at the type former is therefore
**circular**.

The fix is local to the constructed value: `directTyBody` is the
dependent-pair tower **guarded by its own smallness** (the tower when
it lands in `univ w`, the singleton otherwise).  Then

* the type former's `mem_type` is unconditional (`directTyVal_mem`
  takes no `FieldTele`), so its install goes through, and
* every later member of the block — the constructor, the recursor, the
  projections — *does* have the checked bound in scope, discharges the
  guard (`directTyBody_eq`) and sees the plain tower.

The junk branch is unreachable on any block the checker accepts.  The
alternative — proving that the core operations are invariant under a
fresh environment extension, so the bound could be re-read in the
pre-block environment — is a whole-core mutual induction and buys
nothing else.

### The two frame-relative capabilities

**Finding.**  `EtaLaw` and `UnitLaw` are the only `EnvModel` clauses
that quantify over a parameter-telescope fit at an **arbitrary** frame
(`d₁`, `ρ₁`), while every constructed value is a λ-tower over the
telescope's *frame-0* opening (`teleLamV … 0 (rho0 V)`).  Folding such
a tower needs a fit at frame 0 — `teleLamV_fold` is frame-matched — so
discharging either law needs to relocate a closed telescope's
value-spine fit onto the canonical frame-0 opening.  The missing piece
is one lemma, called `TeleFit.reframe0` below and spelled out once in
"The endgame" section: the existing kit (`TeleFit.toTeleFitI`,
`TeleFitI.sanitize`, `interp_instSeq_fvarFrames`, `peel_walk`) gets
close, but `TeleFitI.toTeleFit` reproduces the frame it is given, so
none of it lands at frame 0.

The direct install therefore declares **both** `eta := false` and
`unitlike := false`.  Claiming fewer capabilities only ever removes
reductions, so this is sound, and it costs nothing today: the path is
artifact-*absence* gated, so every structure that has a capability
today keeps the modeled route.  `directTyVal_unitlike` is proved and
kept — it is the whole semantic content of the unit-like law for this
class, waiting only on `TeleFit.reframe0`.  Both capabilities are
**endgame preconditions**, listed with eta's public-naming work in
"The endgame: ind-models' skip rule must be dependency-aware"; neither
is a precondition of this landing.

### Three shape decisions, all so the model reads the checks off the
frames it computes in

The direct path's checks differ from the phase-1 shape in three places.
All three are the *same* decision applied three times — **run each check
at the frame its own data lives at, and open every telescope at its own
variables** — and all three are reference-faithful: the references
compare a binder's domain in the local context of the binders before it,
which is exactly "frame `j`".

* `checkDirectCtor` opens the **constructor's own** parameter telescope
  (rather than instantiating it into the type former's).  That opening
  is where every value-spine fit of the constructor's type at the
  canonical frame lands (`TeleFit_open`), so the field types carry
  exactly the annotations the model's walks produce, and it is the
  telescope `directCRest` — hence the tower, the constructor value and
  the projections — is read off.
* `checkDirectDomsAt` runs the reference kernels' binder-domain
  comparisons **binder by binder at frame `off + j`**, with each
  telescope opened at *its* own variables.  It is used four times: the
  constructor stage's parameter comparison (`Add.lean:220-222`, nanoda
  `check_ctor`, at `off = 0`), and — the fourth instance of this one
  decision — the recursor stage's parameter comparison (`off = 0`), its
  minor-premise field domains (`off = nP + 2`), with the motive's and
  the major's domains pinned by single `isDefEq`s at frames `nP` and
  `nP + 2`.  Domain `j` is scoped at `off + j`, so that frame is precisely the
  context the references compare it in — with the binders before it in
  scope and no more.  Because neither side borrows the other's
  annotations, both carry their own frame conditions at every stage
  (`FrameOk.dom`) and `isDefEqCore_sound` applies at exactly the frame
  the model's walk is at: no lifting between frames, and no mixed-spine
  well-formedness.  This is what makes `DomsInterpEq.of_pins` a short
  induction rather than a re-derivation of `pi_walk` at growing frames.
* `checkDirectFieldUniv` infers each field's sort at **its own** frame
  (`nP + j`) rather than at the block's widest frame.  Depth invariance
  makes this the same verdict and removes a frame-padding step: the
  sorts come out at exactly the valuation the dependent-pair tower's
  recursion uses.

One further check is not a frame decision but a re-verification:
`checkDirectCtor` re-checks that every **annotated** opened field domain
resolves in the *pre-block* environment.  `directNonRec` says that of
the raw domains — it is the recognition filter — and the model needs it
of the annotated ones, because the type former's value was fixed one
install earlier, from those domains' interpretations in the pre-block
environment, so the later members' proofs must move that value across
the block's own extensions (`interp_mono` + `interp_cval_ext`).  Same
raw/annotated discipline `directShape` follows.

`Setlec/Model/DirectInstall.lean` assembles them and proves the
value-level content:

* `directTyVal_mem` — the type former inhabits its type, from the
  per-field universe bound alone;
* `directCtorVal_mem` — the constructor inhabits its type, splitting a
  fitting parameter+field walk (`TeleFit_split`) and closing with
  `tupleV_mem`;
* `directRec_body_mem` / `directProj_body_mem` — the semantic heart:
  a member of the tower *is* the tuple of its own projections, so the
  minor premise applied to those projections lands in `motive x`, and
  field `i` lands in the `i`-th (instantiated) field domain.  This is
  what makes the eliminator's conclusion reachable with no `_model`
  theorem involved;
* `directRec_iota` / `directProj_iota` — the two iota equations the
  stored rules' fold obligation reduces to once the λ-towers are folded
  away (`teleLamV_fold`).

Supporting telescope lemmas: `TeleFit_split`, `TeleFit_open` (a fitting
walk lands exactly where `openPisAtFvars` does), `TeleFit_rest_sort`
and `stripPis_instantiate1_body`.

### Status (complete, 2026-08-24)

The clause is **enabled**; the notes below record how the pieces landed
(items 1-7 of the plan at the end of this section are all done).

Landed and gate-green: the value-construction kit, the recognition
layer, the checks and the install (`checkDirectStruct` and its
shared-state twin `checkDirectStructS`), and a **raw** e2e fixture
(`tests/e2e/src/direct_struct_raw.lean` → `direct_struct_raw.ndjson`,
committed unfiltered, run by `tests/arena.sh` with
`SETLEC_INDUCTIVE_MODELS=/nonexistent` via the new `raw` marker in
`tests/e2e-expected.txt`).  With the clause enabled the fixture is
**accepted** (a structure with two parameters and two dependent fields,
a field-free structure, `rfl`s through both projection iota rules and
through the recursor rule) — verified by running it, and re-verified
after each subsequent change.

**The group-local restructure landed (task #83).**  `ModeledOk` and the
`modelFamilyTaken` guard are gone: the `T`↔`T._model` identification is
group-local to one block's install derivation and is discarded at its
end, so it was never a global environment invariant.  What replaces it
for the direct path is *nothing* — every clause the direct install used
to discharge vacuously has ceased to exist.  The two clauses that
remain, `CapsOk`'s `EtaLaw`/`UnitLaw`, are now stated over **public**
names and premised on `EtaFamilyStored`, and the direct install owes
neither: it claims `eta := false` and `unitlike := false`, and its
constructor cannot complete an *earlier* family because
`EtaFamiliesClosed` says a stored eta-capable former's constructor is
already stored while the direct block's names are fresh.

Two consequences worth recording:

* the direct install's obligations are now exactly `EnvModel`'s real
  clauses — `mem_type`, `val_params`, `annot_ok`, `rec_rules` — plus
  `EtaFamiliesClosed`, which the block preserves through
  `EtaFamiliesClosed.cons_nonind` (its former claims no eta, and its
  other members are not formers at all);
* the module split `CheckerBase ← Modeled ← Checker` puts `checkIndDecl`
  in `Modeled` and `checkDirectStruct` in `Checker`, so the direct
  clause dispatches in **`checkDecl`** rather than inside
  `checkIndDecl`; the shared-state copy mirrors it in `checkDeclSF`.

The environment assembly of the install soundness is complete: the type
former's extension, all four semantic obligations (`mem_type`,
`val_params`, `annot_ok`, both rule equalities), `extend_direct_struct`,
`checkDecl_sound`'s clause and the shared-state bridge.  The dispatch
lives in `checkDecl` (and its `S`/`NC`/`SP` copies) and the raw fixture
is pinned at *accept*.

Landed on the verification side, so that enabling the clause is
possible at all: the pair-monad projection batteries and the
fuel-indexed `_datF` battery for every new declaration-checker function
(`Setlec/Verify/BridgeDecl.lean`), and the run-level `wfOpsM`-to-pure
implications (`Setlec/Verify/BridgeWfImp.lean`, with the reusable
`checkConstantVal_typeWF`, `stripPis_WScoped` and
`openPisAtFvars_index`).  `checkDirectStruct_wfimp`'s intermediate
`EnvWF` hypotheses are *run-tied*, to be discharged in
`Setlec/Model/BridgeWF.lean` from the declaration inversions, exactly
as `installProjFnStep`'s are.  `Setlec/Kernel/CheckerNC.lean` carries
the cert-skipping twin.

Landed since (2026-08-23, the assembly pass):

* the reference `isDefEq` between the two parameter telescopes
  (`Add.lean:220-222`) is now checked, over the constructor's own
  opening.  The battery obstruction was **not** the distinct-instance
  trap the earlier pass diagnosed: `checkDefEqList`'s three commute
  lemmas (`_fst_dproj`, `_snd_dproj`, `_datF`) were simply missing from
  the `checkDirectCtor` batteries' simp sets.  Adding them makes all
  three fire; nothing about the call shape or the `PairM` instances
  needed changing.
* the install order finding and the guarded tower (see "The install
  order, and why the type former's tower is guarded"), which is what
  makes an inductive one-constant-at-a-time assembly possible at all;
* `FieldTele_of_walk` (`Setlec/Model/DirectExtend.lean`) is **landed**
  and applies verbatim: `checkDirectFieldUniv` runs in the environment
  carrying the type former, which is exactly the environment whose
  model is in hand when the *constructor* is installed.  What is still
  open on that front is not the lemma but its **input**: it takes a
  `FrameOk` of the opened field telescope, and supplying one from an
  actual run (`WScoped`/`looseBVarsBounded`/`LeavesBounded`/`FvarsOk`/
  `AnnotOk`/interpretability of the residual, at the frame the
  constructor's fit lands at) is part of item 2 below.  `FrameOk.dom`
  and `FrameOk.body` already carry it across each opened binder;
* **`extend_direct_ind`** (`Setlec/Model/DirectDecl.lean`): the type
  former's model extension, complete and sorry-free —
  `checkDirectInd_inv`, `mem_type` from `directTyVal_mem`,
  `val_params` from `directTyVal_params`, `annot_ok` from
  `annotate_sound`, every capability clause vacuous;
* `TeleFit.instLev_down`, the value-spine counterpart of
  `TeleFitI.instLev_down`.

Everything above was re-validated with the clause temporarily enabled
at each step: arena 90/92, `direct_struct_raw` accepted, the three
duplicate-declaration fixtures rejecting.

What remains, in dependency order (items 1 and 2 are landed, and so is
item 3 — see below; the head of item 4 is landed too):

1. ~~A cross-environment congruence for the constructed values.~~
   **Landed** (`InterpAgree`, `sigmaTowerV_congr`, `FieldTele_congr`,
   `directTyBody_congr`, `teleLamV_congr`, `directTyVal_congr` in
   `Setlec/Model/DirectInstall.lean`).  The towers read the telescope
   only through its binder domains' interpretations, and those domains
   resolve in the pre-block environment (now checked), so each is a
   `k`-indexed induction over the opened telescope.  The frame is not
   generalized: `teleLamV k d` evaluates its body at exactly `d + k`,
   which is the frame the install's own `openPisAtFvars` runs at.
   `FrameOk.ofTeleFit` (`Setlec/Model/DirectExtend.lean`) is landed
   too — it carries the frame conditions along a value-spine fit, which
   is how `FieldTele_of_walk`'s `FrameOk` input is obtained.

2. ~~The linchpin: transferring a value-spine fit between the two
   parameter telescopes.~~  **Landed.**  The constructor's `mem_type`
   needs `⟦T p⃗⟧ = tower` (`directCtorVal_mem`'s `hresid`), which folds
   the type former's value through `directTyVal_fold`.  That fold
   consumes a fit of the **type former's** telescope, at frame 0, with
   the parameter values the **constructor's** fit supplies — so the
   constructor's fit has to cross the checked parameter-domain
   `isDefEq`.  `pi_walk` is that transfer at a *fixed* frame along an
   expression spine, and `TeleFitI.toTeleFit` reproduces whatever frame
   it is handed, so nothing existing lands at frame 0.

   Three pieces, all in `Setlec/Model/DirectExtend.lean`:

   * `DomsInterpEq` — the semantic content: at every stage the two head
     domains interpret alike, and this continues on the bodies opened at
     the respective variables;
   * `TeleFit.transfer` — its consumer, a five-line induction producing
     the frame-0 fit at the same frames and valuation as the source, so
     both towers fold at one frame;
   * `DomsInterpEq.of_pins` — establishing it from
     `checkDirectParamDoms`'s per-frame pins.  This is short precisely
     because of the second shape decision above: each telescope is
     opened at its own variables, so both sides carry their own
     `FrameOk` and `isDefEqCore_sound` applies at exactly the frame the
     walk is at.

   `directCtor_field` and `directCtor_resid` then discharge the two
   obligations of `directCtorVal_mem` — the field telescope is small at
   every fitting parameter spine, and the opened residual interprets to
   the tower the constructor tuples into — and `directCtor_mem` is the
   constructor's `mem_type`.  What is left of this item is the
   `extend_basis_one` wiring, mirroring `extend_direct_ind`.

3. **`mem_type` for the recursor and the projections**, from
   `directRecVal_mem`/`directRec_body_mem` and
   `directProjVal_mem`/`directProj_body_mem`.  The shape prerequisite is
   landed and `checkDirectRecTy_inv` exposes every intermediate with each
   pin at the frame it was checked at.

   **The frame-relocation family is landed**
   (`Setlec/Model/DirectExtend.lean`).  The type former's value is a
   tower over the *constructor's* opening (field binders at `nP …`),
   while the recursor puts the motive and minor in between (field
   binders at `nP+2 …`), so the recursor's obligations need the tower
   and its fits moved across frames.  `DomsInterpEq` was therefore
   generalized to **`DomsAgree`** — two openings at *unrelated* frames
   whose domains interpret alike, with `DomsInterpEq` kept as the
   one-frame abbreviation the per-frame pins produce — and everything
   the openings determine now relocates on it:

   * `TeleFit.transfer` — a value-spine fit moves to the other frame;
   * `sigmaTowerV_reframe` — the dependent-pair towers coincide (via
     `sigma_congr`, so only the fibres *inside* each domain matter);
   * `FieldTele_reframe` — the per-field universe bound moves too;
   * `TeleFit.rho_above` and `TeleFit.rho_det` — a fit's end valuation
     is *determined* by its starting frame and its values, which is what
     lets two independently-built fits be identified.

   This is deliberately the `TeleFit.reframe0` family DESIGN records as
   the endgame precondition for the direct class's `eta`/`unitlike`:
   stated for the towers generally rather than for one call site, so
   those discharges can consume it unchanged when they land.

   *Rider resolved (coordinator):* the recursor's parameter pins keep
   targeting the **constructor's** parameter domains — no fifth
   pin-site change.  With the relocation in hand both routes work, so
   the one with zero additional kernel churn wins: the bridge belongs on
   the proof side (`DomsAgree` via transfer/relocation) and the kernel
   stays as close to the reference comparison set as possible.

   **All the `DomsAgree` bridges are landed** (2026-08-23):

   * `DomsAgree.of_pins` — from the install's per-frame `isDefEq` pins,
     at a **common** frame, both telescopes opened at their own
     variables;
   * `DomsAgree.of_pins_inst` — the same, but with the right-hand
     telescope walked by `Expr.instPisAt` at the **left telescope's**
     opening variables.  Both of the recursor's pin sites have that
     shape (`checkDirectRecTy` compares `fvarTypeD fvs[j]` against the
     domains an `instPisAt` walk produces), so the walk's bodies are
     instantiated at the *other* telescope's variables — which
     `DomsAgree` (each side opened at its own) meets only up to
     `ErasedEq`.  `FrameOk.body_at` carries the frame conditions onto
     that foreign opening and `DomsAgree.erasedEq_right` closes the gap
     at every stage;
   * `DomsAgree.of_erasedEq` (with `instPisAt_erasedEq_spines`) — one
     telescope along two **index-matched** spines;
   * **`DomsAgree.of_shift`** — one telescope at two *different base
     frames* with matching values.  Its core is
     **`DomsAgree.of_shiftSeq`**, stated on `instSeq` of a *closed*
     subterm rather than on a walk residual, because the recursor needs
     the shift both ways: the constructor's field telescope is an
     `instPisAt` residual, but the minor premise's is a **binder
     domain** of the recursor's telescope — an `instSeq` of a closed
     subterm and not a walk residual at all.  `of_shift` is the
     walk-residual corollary (`stripPis_add` + `instPisAt_stripPis`).
     The `instPisAt` snoc lemma DESIGN expected to be missing turned
     out to exist: `Expr.instPisAt_head`
     (`Setlec/Model/ProjInstall.lean`) both exhibits the residual's head
     binder as the `instSeq` and extends the walk by one argument;
   * `DomsAgree.trans`, `DomsAgree.symm` (one-directional by
     definition; a `FrameOk` on the left supplies the missing
     interpretability and flips it) and `DomsAgree.congr` (the relation
     moves across the block's own extensions along `InterpAgree`, like
     `sigmaTowerV_congr`, since the constructor stage's pins are checked
     one environment earlier than the recursor's).

   **The recursor's `TeleBody` is landed**: `directRec_body`
   (`Setlec/Model/DirectDecl.lean`) — at every fitting spine
   `p⃗ M mi t` the constructed body inhabits the interpreted residual
   `M t`.  The assembly:

   * the recursor's parameter fit is transferred onto the constructor's
     telescope (`of_pins_inst` at the recursor's parameter pins) and on
     to the type former's (the constructor stage's own pins), both
     landing at one frame and valuation (`TeleFit.rho_det`);
   * the tower relocates from the constructor's opening (frame `nP`) to
     the minor premise's (frame `nP+2`) along
     `of_shift ∘ (of_pins_inst, symm)` composed by `trans`, and
     `sigmaTowerV_reframe` / `FieldTele_reframe` move the tower and its
     universe bound with it;
   * the major's membership crosses the checked `isDefEq` against the
     family application, whose frame conditions are built from
     `FrameOk.openVars` (each opening variable is frame-ok at the fit's
     end) plus `annotOk_spine` at the type former's own `ChainSlots`;
   * the minor's conclusion `motive (C p⃗ f⃗)` folds the constructor's
     value to `tupleV f⃗` (`directCtorVal_fold`, the fold half of the
     split `directCtorVal_body`), and `directRec_body_mem` closes with
     structure eta.

   The three environment-crossing facts it consumes — the field
   telescope's universe bound, the type former's fold and the
   constructor's fold — are *hypotheses*, to be transported to the
   recursor's install environment by the caller; that is what
   `DomsAgree.congr`, `FieldTele_congr` and `directTyVal_congr` are for.

   Support landed with it: `FvarSpine.of_pointwise` (`InstFrames`),
   `openPisAtFvars_add`, `TeleFit_append`, `directCtorVal_congr`
   (`DirectInstall`), `interp_weaken_fit`, `FrameOk.weaken_top`,
   `FrameOk.weaken_fit`, `FrameOk.fvar`, `FrameOk.openVars`,
   `FrameOk.ofInstWalk` (`DirectExtend`), `stripPis_one` (`DirectDecl`).

   **The projections' frame pins (finding + fix, 2026-08-23).**

   `checkDirectProj` **annotates** the generated projection type
   (`ptyA ← ops.annotate env 0 pty`) and stores `ptyA`, because
   `directProjTy` builds its binders with `cod = none`
   (`replacePiBody` resets every kept binder to `⟨m.bi, none⟩`; the
   fresh subject binder is `⟨.default, none⟩`).  The *raw* `pty` is
   therefore **not interpretable at all** — `interpExpr` returns `none`
   on a `∀` whose `cod` is missing — and there is no
   annotate-preserves-interpretation lemma, nor can there be a useful
   one: `interpExpr` reads the `cod` level (`pi (v.eval φ) A B`), so two
   differently-but-validly annotated copies need not have equal
   interpretations.  (The modeled path never needs one: its projection
   type is a stored *model* type renamed back verbatim, pinned by
   `checkProjTy`'s roundtrip `==`.)

   So every semantic fact about the stored projection type must come
   from what the kernel checks **about `ptyA`** — the re-check
   discipline the other three stages follow (`checkDirectInd`'s result
   sort, `checkDirectCtor`'s residual, `checkDirectRecTy`'s
   `directShape` + domain pins).  The projection stage had broken it:
   of `ptyA` it knew only well-scopedness, resolution, `nP+1` binders
   and that it is a type; `checkProjShape` adds arities and
   `checkProjRule` pins only the **parameter** domains and the rule's
   λ-domains.  `directProjVal_mem`'s `TeleBody` was therefore not
   provable by anything.

   **Landed**: two definitional pins in `checkDirectProj` (and its
   `F` mirror), route (X) at the projection stage's own frames —

   * open `ptyA` at `nP` fvars; `isDefEq` the subject binder's domain
     against `Expr.mkAppN (.const T lps) fvsP` at frame `nP`;
   * open the subject; `isDefEq` the residual against the head domain of
     `Expr.instPisAt (fvsP ++ projArgs) cvCa.type` at frame `nP+1`,
     where `projArgs` are the **closed** applications
     `T.proj.j p⃗ t` (`j < i`) built from the opened variables.

   Both comparands are interpretable (`cvCa.type` is the annotated
   constructor type; the arguments are `fvar`s and applications), which
   is what `isDefEqCore_sound` needs, and both use plain
   `Expr.instPisAt` at closed arguments — so `directProjTy` is now a
   **validated generator** rather than a trusted one, and no
   `instantiate1Lift` theory is needed for the proof.

   *Verdict safety.*  The pins compare a **self-generated** artifact
   against the constructor telescope, so a failure means a generator
   bug, never bad input: `.notImplemented` (decline, exit 2) is the
   correct outcome, exactly as for the other direct-path shape
   re-checks.  Validated by temporarily enabling the direct clause:
   arena stays 90/92, `direct_struct_raw` still accepts (53 decls), and
   the only e2e changes are the four expectation flips item 7 owns.

   *Also landed, and now not on the critical path*
   (`Setlec/Verify/Subst.lean`): the substitution theory for
   `Expr.instantiate1Lift`, which had none —
   `instantiate1Lift_eq_self`, `instantiate1Lift_eq_instantiate1`,
   `instantiate1Lift_instantiate1` (the substitution lemma),
   `instSeq_instantiate1Lift`, `instSeqLift` with `instSeq_instSeqLift`
   (the collapse onto plain `instSeq` once the ambient variables are
   instantiated by a closed spine), `instSeqLift_forallE`,
   `stripPis_instantiate1Lift_full` and `instPisAtLift_head`.  It is
   what a proof against the *unpinned* kernel would have needed, and it
   is the theory any future consumer of `instPisAtLift` will want.

   **Item 3 is landed** (2026-08-23).  The projections' half is
   `directProj_facts` (`Setlec/Model/DirectDecl.lean`), split into

   * `checkDirectProj_inv` — the stage's data, in particular the two
     frame pins;
   * `directProj_param_stage` — the *parameter half*, at any fitting
     parameter spine: the fit crosses to the constructor's telescope
     (`DomsAgree.of_pins_inst_at` over `checkProjRule`'s parameter-domain
     `checkDefEqList`) and on to the type former's, the field telescope
     is small there, the type former's value is the tower over it, and
     the **subject-domain pin** identifies the subject binder's domain
     with that value;
   * `directProj_facts` — the λ-tower body obligation, plus the converse
     fit (the stored type is fit by every canonical spine `p⃗ t`), from
     which `directProj_mem` (`mem_type`) and `directProj_fold` (the
     stage's fold equation, via `teleLamV_fold`) both follow.

   The **residual pin** is discharged as DESIGN predicted: it identifies
   the stored residual with the `i`-th field domain walked at the
   parameters and at the *applications* `T.proj.j p⃗ t`, whose values are
   `projV j t` by `DirectProjInv` (the direct `ProjPhaseInv`, carrying
   per installed `j < i` the stored constant, its level parameters, a
   fit of its type at `p⃗ t`, and the fold equation).
   `interp_instSeq_frames` then identifies the pin's right-hand side
   with the `i`-th domain along the *canonical* field spine of `t`,
   where structure eta (`directProj_body_mem`, restated on that spine —
   the every-fitting-spine form is false) puts `projV i t`.

   Three findings worth keeping:

   * `checkProjRule`'s parameter-domain pins are checked at **one**
     frame (`nP + nF`), not per binder, so `DomsAgree` had to learn to
     consume a pin from above the walk's frame: `FrameOk.pad_exists` /
     `isDefEqCore_sound_at` (one padded valuation carries every frame-ok
     term up), and `DomsAgree.of_pins_inst_gen` generalizing
     `of_pins_inst` over the pins' frames, with the per-frame and
     fixed-frame instances as its two corollaries.
   * The pin's right-hand side is **not** an opened walk, so its frame
     conditions cannot come from `FrameOk.ofInstWalk`.  They come from
     `TeleFitI.rest_wf` fed by `TeleFitI.ofInstWalk` — the non-variable
     spine counterpart of `pi_walk`, whose per-stage memberships the
     *existing* `fit_mem_frames` supplies from the opened-side fit.
     `TeleFit.doms_at_end` and `TeleFit_nil_eq` are the two small
     supports.
   * `cases` on a `TeleFit` whose telescope is a stuck `instantiate1`
     cannot refute the `cons` constructor; `TeleFit_nil_eq` exists for
     exactly that.

4. **The rules' fold obligation** (`RecMemberOk`) for the recursor rule
   and the `nF` projection rules, through `TowerOk.of_stages`
   (`Setlec/Model/RuleFold.lean`): the per-stage facts are the
   install's definitional domain pins, the bottom fact is
   `teleLamV_fold` composed with `directRec_iota` / `directProj_iota`.

   **Landed (first step): `proj_rule_eq` is now provenance-free.**  Its
   proof turned out to be modeled-specific in exactly *one line* — the
   per-`ψ` bottom fact — so it is split into
   `proj_rule_eq_of_bottom` (`Setlec/Model/ProjInstall.lean`), which
   takes the bottom as a hypothesis and does everything else
   (`ruleLhsParts` computation, `FrameWf`, resolution, `modeled_stage`'s
   flat stage facts over the kernel's definitional pins,
   `TowerOk.of_stages`/`TowerOk.out`, and the transport across the fresh
   recursor extension), and the thin modeled wrapper `proj_rule_eq`,
   which passes `proj_bottom`.  Note `modeled_stage` itself is already
   provenance-free — it is stated over the stored type, the stored
   right-hand side and the kernel's pins.

   **Item 4 is landed** (2026-08-24).  Both rule obligations are
   discharged: `directProj_rule_eq` and `directRec_rule_eq`
   (`Setlec/Model/DirectDecl.lean`).

   The two bridges the projection needed are
   `TeleFit.of_framePref` — a `FramePref` over an opening spine *is* a
   value-spine fit of the opened telescope (the two valuation
   conventions are equal functions, `getD_snoc_eq_updV` plus the walk)
   — and `TeleFit.erasedEq`, a fit moving along an `Expr.ErasedEq`
   telescope, which identifies `crestP` (the constructor telescope at
   the projection type's opened parameters) with `crestC` (at its own)
   through `instPisAt_erasedEq_spines`.  `TeleFit.erasedEq` is
   preferred over `DomsAgree.of_erasedEq` here because it has no
   `stripPis` side condition.

   The generic half was split twice more.  `modeled_rule_eq_plain` now
   goes through **`rule_eq_of_bottom`** (`Setlec/Model/IndInstall.lean`),
   the single-environment "generic except the bottom" form DESIGN asked
   for; it turned out **not** to be what the direct recursor can use,
   because the direct rule's pins are checked in the *pre-recursor*
   environment while the canonical tower's body mentions the recursor
   itself.  What the direct recursor uses is
   **`rule_eq_of_bottom_ext`** — `proj_rule_eq_of_bottom` generalized
   from `rP = ctorParams` to `ctorParams ≤ rP`, with the projection case
   kept as a thin instance.  Its second generalization: it takes the
   *constructor-residual package* directly instead of the parameter-domain
   `DefEqListOk`, because the direct install pins those domains **per
   frame** (`checkDirectDomsAt` at frame `j`) rather than as one
   `checkDefEqList` at the master frame; the direct side builds the
   package with `FrameOk.ofInstWalk` (per-frame pins) plus the new
   **`FrameOk.getD_up`**, the upward companion of
   `interp_getD_canon`/`annotOk_getD_canon` (all six components at once,
   by iterating `FrameOk.weaken_top`).

   **Finding + fix (kernel, direct path only, 2026-08-24): the rule
   stage was pinning at the wrong frame.**  `checkDirectRule` opened the
   *minor premise's* copy of the field binders and pinned the stored
   rule's λ-domains against those, while `ruleLhsParts` — the frame the
   rule's total λ-equality is stated over — opens the **constructor's**
   field telescope at the rule prefix.  The two openings are index-matched
   and definitionally equal (`checkDirectRecTy` pins them), but the model
   cannot cross a definitional step it was not handed, so the stage facts
   were unprovable as the check stood.  `checkDirectRule` now opens
   `crest` itself (`openPisAtFvars p.nF crest (p.nP + 2)`), which is
   exactly the "route (X), at the stage's own frames" discipline
   `checkDirectProj` already follows, and the pin is `checkDefEqList`
   against that frame's annotations.  Verdict-neutral, verified with the
   clause temporarily enabled: arena 90/92, `direct_struct_raw` accepted,
   and the only e2e movement is item 7's four flips.  The alternative —
   a semantic bridge chaining the two per-frame pins through
   `ErasedEq` — would have meant a bespoke `modeled_stage` variant for
   the direct path alone, i.e. exactly the divergence from the shared
   machinery the re-check discipline exists to avoid.
5. **The chain**: **the model side is landed** (2026-08-24) —
   `extend_direct_struct` (`Setlec/Model/DirectDecl.lean`) installs the
   `3 + nF` constants one at a time and returns exactly
   `checkDecl_sound`'s shape, `Nonempty (EnvModel V envOut) ∧
   EtaFamiliesClosed envOut`.

   `extend_rec_swap` turned out to be unnecessary: `extend_basis_one`'s
   `hrecm` obligation is stated at precisely the `val'` the rule
   equalities are stated at (the extended valuation, agreeing with the
   base off the new name), so the recursor and each projection go in
   **with their rule in one step** (`extend_direct_rec`,
   `extend_direct_proj`).  The one place the members differ is the eta
   head obligation: a projection's name *is* projection-function-shaped,
   so it is refuted by `projFnName_inj` against the block's own former,
   whose `directCaps` claims no eta — the other three refute it by
   `Name.isProjFnShape`.

   The projection phase runs on **`DirectStageOk`**, a structure
   bundling what one field's install hands to the next: the two earlier
   members' `find?`s and resolutions, the four semantic stage facts
   (`frC`, `domsCT`, `fieldAt`, `tfold`, `cfold`) *at that environment
   and model*, and `DirectProjInv` up to `i`.  `direct_proj_step` is
   `extend_direct_proj` plus transport, `direct_proj_fold` is its
   induction over `List.range p.nF`, and `DirectStageOk.cons_zero` moves
   the stage-0 instance across any fresh non-former extension (that is
   how the recursor's install is crossed).

   The transport kit that makes this mechanical: `TeleFit_congr` and
   `TeleFit_congr'` (a value-spine fit crosses an `InterpAgree` in both
   directions, since every stage fact is stated over expressions that
   resolve one environment down), `FrameOk.extend_fresh` (all six
   components of a closed resolving type at once), and the existing
   `FieldTele_congr` / `sigmaTowerV_congr` / `DomsAgree.congr` /
   `directTyVal_congr`.

   **Item 5 is landed** (2026-08-24), including the `checkDecl_sound`
   clause: a recognised block takes `extend_direct_struct`, everything
   else `checkIndDecl_sound`, and `directParts?_inv`
   (`Setlec/Model/DirectDecl.lean`) supplies the three recognition
   facts.

   *Finding, on the reverted attempt.*  The inversion must follow the
   **compiled** shape of `directPartsCore?`, not its source shape: the
   match compiler hoists the two inner `match`es — the rule's
   `stripLams` (a conjunct *inside* the 13-fold guard) and the type
   former's `stripPis` (the `if`'s then-branch) — **out of** the `if`
   and evaluates them first.  The split order that works is therefore
   block shape, level parameters, `stripLams`, the guard, `stripPis`;
   the `if` also needs a `dsimp only at h` first, because the three
   `have T := …` binders block `split`.  With that, the guard is an
   ordinary `Bool.and_eq_true` chain (`.1.1.1.1.1.1.1.1.1.2` is the
   level-parameter conjunct, `.1.2` the `directShape` one) and
   `directShape` yields the nonzero sort once its own first scrutinee
   is identified with the recognition's `stripPis` (the split rebinds
   the sort variable; the two are equated through the two equations).
6. **Item 6 is landed** (2026-08-24): `checkDirectStructS`'s
   shared-state-to-pure bridge.  Three layers, mirroring the modeled
   path's:

   * `Setlec/Verify/CheckerF.lean` — the `F`-mirror equalities under
     `mkFEnv` (`checkDirectFieldUnivF_eq`, `checkDirectDomsAtF_eq`,
     `checkDirectRecTyF_eq`, `checkDirectRuleF_eq`, `directPartsF?_eq`,
     and the push forms `checkDirectIndF_push`, `checkDirectCtorF_push`,
     `checkDirectProjF_push`), so everything above is stated over the
     *generic* functions;
   * `Setlec/Verify/BridgeS3.lean` (new) — the five stages as `SimAt`s
     between `sharedOps` and `fueledOpsM`.  Each one is its
     `Setlec/Verify/BridgeWfImp.lean` `_wfimp` walk transcribed:
     identical per-site scoping facts, `SimAt.bind`/`SimAt.unwrapOr'`
     in place of `atF_bind_ok`/`unwrapOr_atF_ok`;
   * `Setlec/Model/BridgeS.lean` — `checkDirectStructS_run` (the five
     `flushS` transitions, one fuel join at the end) and
     `checkIndOrDirectSF_run`, the dispatch bridge both index drivers
     consume (`checkDeclSharedF_bridge` and
     `ConsistencyP.checkDeclSPStep_run`).

   `Setlec/Model/DirectWF.lean` (new) carries the `EnvWF` of the
   `3 + nF` environments the install walks (`direct_ind_wf`,
   `direct_ctor_wf`, `direct_rec_wf`, `direct_proj_wf`), read straight
   off the stage inversions; it sits below both bridges because
   `Setlec/Model/BridgeWF.lean`'s cached-driver chain needs exactly the
   same sequence to discharge `checkDirectStruct_wfimp`'s run-tied
   hypotheses.  Two consequences of writing those discharges:

   * **Finding + fix (kernel): the `F` mirror of `checkDirectRule` was
     stale.**  The route-(X) frame fix of 2026-08-24 changed the pure
     `checkDirectRule` to open `crest` at the rule prefix but left
     `checkDirectRuleF` opening the *minor premise's* copy (and doing a
     now-dead `instPisAt`).  Since `checkDirectRuleF` is what the
     binary runs, the mirrors have to agree before the clause can be
     enabled at all — the bridge is what makes such a drift a build
     failure rather than a silent divergence.  Fixed in
     `Setlec/Kernel/CheckerS.lean` (the `NC` driver reuses the same
     mirror).
   * `foldDirectProj_wfimp`/`checkDirectStruct_wfimp` now take their
     per-step `EnvWF` hypothesis over the **pure** run rather than the
     `wfOpsM` one.  The `wfOpsM` form was not dischargeable: it is
     universally quantified over `cvTa`/`cvCa`, while converting a
     `wfOpsM` projection run to a pure one needs the *checked*
     constructor type's closedness.  The pure form is what the caller
     has anyway (the fold already derives it).
7. **Item 7 is landed** (2026-08-24): the clause is enabled in
   `checkDecl`, `checkDeclSF`, `checkDeclSP`, `checkDeclNC` and
   `checkDeclSPNC` (`match directParts? env block with | some p =>
   checkDirectStruct ops env p | none => checkIndDecl ops env block`,
   and `directPartsF?`/`checkDirectStructS`/`checkDirectStructNC` in the
   index copies), with the four expectation flips
   (`direct_struct_raw` 2→0 in `tests/e2e-expected.txt`;
   `bad/tutorial/13{3,4,7}` 2→1 in `tests/arena-expected.txt`).

### Task #82 is complete (2026-08-24)

The direct simple-structure install is on by default, verified end to
end: `checkDecl_sound` covers it, and both executable drivers (the
shared-state one and the parsed-index one) bridge to it.  Gates: `lake
build` warning-free, `lake test`, arena 90/92 with e2e 56/56, `scale.sh`
all four shapes PASS, no `sorry`s, axioms of `no_proof_of_Empty`,
`no_proof_of_Empty_input`, `checkDecls_sound` and `checkDecl_sound`
exactly `[propext, Classical.choice, Quot.sound]`, and both init-prelude
probes (certified and `SETLEC_NO_PROOF_CERTS=1`) accept 3653
declarations at exit 0 — the preprocessed stream still takes the
modeled route byte for byte, since `directNoModel` defers to an
available artifact.

What the class still does *not* claim is `eta` and `unitlike` (see "The
two frame-relative capabilities"); that is the remaining work before
`lean-inductive-models` can stop generating artifacts for this class
and the direct path takes over by absence.

## Level `leqCore` was not short-circuiting: the 2x stupidity (2026-08-23)

Profiling the init-prelude probe put ~40 % of the whole run inside the
structural `Level` machinery (`rest`/`simplify`/`byCases`/`decEq` plus
their allocator traffic) — yet counters showed only ~263k `isEquivLM`
calls with ~9.4k cache misses.  The misses hid 166 **million**
`leqCore` iterations, 99.6 % of them inside a single declaration
(`Trans.mk._model`, whose PSigma/PProd model tower carries ~50-node
6-parameter `imax` levels).  Root cause: the monadic ports

    | .max a b, _ => return (← leqCore fuel a r diff) && (← leqCore fuel b r diff)

evaluated **both** operands of every `&&`/`||` before combining —
`Option` do-notation has no short-circuiting — so the exponential
`byCases`/`imax`-distribution case tree was explored exhaustively even
after a branch had already decided the verdict.  The references
(nanoda `level.rs::leq_core`, Rust `&&`) prune; a Python replay of the
exact miss set confirmed 938k iterations with pruning vs 166M without
(177x).  Fix: explicit `if ← … then … else pure false` chains in
`rest`/`byCases`/`isEquiv`/`isEquivList` (and `byCases` now substitutes
the succ-case only when the zero case held), the same short-circuit in
`isEquivLM`'s two `leqCore` runs, plus two cheap equality fast paths —
`isEquivLM` answers `some true` when the two *simplified arena indices*
are equal (622 of the 742 big miss pairs were syntactically identical
after simplification), and the spec `Level.isEquiv` gains the matching
`simplify l = simplify r` branch (the reference kernels' structural
fast path; the official kernel's `is_equivalent` is `l1 == l2 ||
normalize(l1) == normalize(l2)` and never runs a leq loop at all).
Semantics: the new code can only turn fuel-exhaustion `none`s (internal
errors, never verdicts) into decided verdicts; every previously decided
verdict is unchanged.

Verification delta: `Setlec/Verify/Level.lean` (helper lemmas restated
on the if-then-else shapes; `isEquiv_sound` gains the simplify-equality
branch via `eval_simplify`) and `Setlec/Verify/SimI.lean`
(`isEquivLM_eff` walks the new branches — the index-equality branch is
sound by `denoteL` functionality, the fall-through needs `denoteL_inj`
to know the spec's fast path also failed; `isEquivListLM` short-circuits
like its spec).  No other proof moved.

**Measured** (init-prelude probe, `perf stat` instructions, best of 2):

| configuration | before | after |
|---|---|---|
| setlec, certified (default) | 173.2 G / ~12.2 s | **82.4 G / ~6.1 s** (−52 %) |
| setlec, `--yolo` | 140.1 G / ~9.1 s | **49.3 G / ~3.6 s** (−65 %) |
| official C++ kernel | 3.9 G | 3.9 G |

The engineering gap drops from ~36x to **~12x**.  Gates: arena 90/92,
e2e 53/53, `lake test`, scale.sh all four shapes PASS, warning-free,
axioms pinned (`ConsistencyP` statement family unchanged).

Post-fix profile (NC mode): allocator/refcount traffic ~36 %,
`List.reverseAux` ~10 % (spine/iota list rebuilds — `take`/`++`/
`reverse` per reduction step), `instantiateListIGo` + its per-call
fresh `MemoNL` hash maps ~13 %.  Per-test ratios against the official
kernel on the arena `good/perf` corpus now range from **better than
official** (`discarded-argument-match`: 7.8 G vs 51.4 G) to ~100x
(`repeated-subproblem` 21 G vs 0.18 G, `shared-subterm` 36 G vs 0.4 G,
`shift-cascade` 23 G vs 0.3 G — sharing-heavy shapes dominated by
per-step list rebuilding and hash-map memo churn, where nanoda's
index caches decide in ~0).  Those are the next levers.

### Closing-entry revision (2026-08-23, post leqCore fix)

The "engineering gap" in the closing entry above was dominated by one
bug: `Level.leqCore`'s monadic `&&`/`||` never short-circuited (the
imax `byCases` tree, kept tractable by the references only through
pruning, was explored exhaustively — 177x redundancy).  Revised
triple on the identical stream, all gates green:

| configuration | instructions |
|---|---|
| setlec, certified | **~82-87 G** |
| setlec, `--yolo` | **~49 G** |
| official C++ kernel | 3.9 G |

Gap ~12x (from the misreported ~36x); next attributed lever: spine
list traffic + per-call instantiation memos (task #84, est. 2-4x on
sharing-heavy shapes).  Notable: setlec now BEATS the official kernel
on the discarded-argument perf tests (0.15-0.4x).

## Per-node loose-bvar cutoff in instantiation; leafGuardI (2026-08-23, task #84)

The four sharing-heavy outliers (`repeated-subproblem` 115x,
`shared-subterm` 97x, `shift-cascade` 80x, `grind-ring-5` 30x vs the
official kernel, `--yolo`) were re-profiled and decomposed into two
mechanisms — neither of which was the originally-suspected
`getAppArgs`/`mkAppN` list rebuilding (that traffic exists but is
on-par with nanoda's per-step `unfold_apps` vectors):

1. **Instantiation traversed closed sub-DAGs.**  nanoda's `inst_aux`
   returns immediately when `num_loose_bvars(e) <= offset` (a per-node
   field); our `instantiate1IGo`/`instantiateListIGo` walked and
   re-interned every node.  Fix: the traversals take a *read-only
   view* of the persistent loose-bvar-bound cache (`IState.bvarB`,
   task #72 — the root shortcut already existed; now it applies at
   every node) and return any node with `bound ≤ cursor` unchanged.
   The wrappers (`inst1M`/`instListM`/`instSpineM`/`piResidualM`)
   pre-fill the cache by running the root bound walk — and, crucially,
   over the *replacement roots* too (`bvarBoundsLGo`), so the `bvar`
   branch's recursion into a closed replacement prunes instantly.
   The prepass skips already-covered roots through the allocation-free
   `BMemo.covers`/`cutoff` slot reads (`Array.getD`; entering
   `bvarBoundIGo` per root allocated a pair each and sent the scale
   harness's telescope exponent to 1.40 — with the skip it is 1.17,
   all shapes PASS).
2. **The fabrication leaf guard was quadratic-to-exponential.**  The
   scoped-discipline guard in `majorToCtorI`/`majorToCtorNC` (and the
   projection-elimination fallbacks) recomputed `fvarLeavesI major`
   *inside* the `.all` lambda — once per leaf of the fabrication — and
   `fvarLeavesIGo`'s per-node `++` of memoized sub-lists materializes
   the *tree*-sized leaf-occurrence list on a shared DAG.  On
   `repeated-subproblem` this was 54 % of the run (`List.reverseAux`
   21 % alone).  Fix: `EStore.leafGuardI` — `hasFvarI`
   short-circuit (a term with no fvar passes trivially; one memoized
   DAG walk instead of two leaf-list materializations) and the base's
   leaf list hoisted out of the lambda.  Same Boolean
   (`fvarLeaves_eq_nil_of_not_hasFvar`); the exponential case remains
   reachable for fvar-carrying fabrications and is noted below.

Verification delta: `instantiate1IGo_spec`/`instantiateListIGo_spec`
gain the `BoundMemoInv` premise and a cutoff branch closed by
`instantiate1_eq_self`/`instantiateList_eq_self`; the wrapper specs
and SimI `_run`/`_eff` lemmas thread the new arguments;
`bvarBoundsLGo_inv` covers the prepass; `leafGuardI_spec` factors
through the raw list lemma; the DiscI3/DiscI6 mirrors restate the
guard.  The bound-cache section moved ahead of the instantiation
specs in `Verify/IExpr.lean`.  **No ISOK/SimAt statement changed.**

**Measured** (`perf stat` instructions, `--yolo` / certified; official
kernel in parentheses):

| test | before (yolo) | after (yolo) | after (cert) | ratio yolo |
|---|---|---|---|---|
| repeated-subproblem (0.18 G) | 21.2 G | **4.44 G** | 4.98 G | 24x |
| shared-subterm (0.37 G) | 36.3 G | **4.96 G** | 5.54 G | 13x |
| shift-cascade (0.29 G) | 23.3 G | **5.87 G** | 5.88 G | 20x |
| grind-ring-5 (13.7 G) | 416 G | **82.8 G** | 93.0 G | 6.1x |
| init-prelude probe (3.9 G) | 49.3 G | **23.8 G** | 30.9 G | 6.1x |

Init-prelude gap: certified ~7.9x, `--yolo` ~6.1x (from ~12x).
Gates: arena 90/92, e2e 53/53, `lake test`, scale.sh all-PASS,
warning-free.

**Remaining levers** (both need a persistent per-node *fvar* datum —
an `IState` cache clause mirroring `bvarB`, i.e. an ISOK extension
that needs sign-off before landing):

* `shift-cascade` (20x) is now ~47 % `abstractRangeIGo` under
  `annotateLams/PisI`: abstraction has no analog of the bound cutoff,
  so fvar-free sub-DAGs are rebuilt per telescope.  nanoda's
  `abstr_aux` prunes on `!has_fvars(e)`.  Plan: dense per-node
  fvar-range cache (`fvarB : BMemo`, range = max fvar idx + 1,
  not descending into fvar type annotations, matching the abstraction
  traversals), cutoff `range ≤ d`, new `Expr.fvarsBelow` predicate +
  `abstractRange_eq_self`, ISOK/ISOKF clause and `flushS` survival
  mirroring `bvarB` exactly.
* The same cache would make `leafGuardI`'s `hasFvarI` walk O(1) and
  close the guard's residual exponential case for good.

`repeated-subproblem`'s residual 24x is flat substrate overhead (RC
traffic, hash maps, per-run parse) over a tiny official baseline —
the same class as the remaining overall gap, no longer shape-specific.

## Per-node fvar-range cache; abstractRange cutoff; leafGuardI Bool walk (2026-08-23, task #86)

Both remaining levers from the task-#84 entry, landed as the planned
`bvarB` mirror:

1. **The fvar-range cache.**  `fvarRangeIGo`/`fvarRangesLGo` fill the
   persistent `IState.fvarB` (a second dense `BMemo`; range = max fvar
   index + 1, `0` = fvar-free, fvar type annotations not descended —
   matching the abstraction traversals).  `abstractRangeIGo` takes a
   read-only view and returns any node with cached `range ≤ d`
   unchanged (nanoda's `!has_fvars(e)` pruning in `abstr_aux`);
   `abstractRangeM` runs the root range walk as its prepass and
   short-circuits the whole call at `range ≤ d`, exactly `inst1M`'s
   shape.  Verification: the existing Prop `Expr.fvarsBelow`
   (`Verify/Shift.lean`) is the cache's soundness predicate — no new
   Bool mirror; `abstractRange_eq_self` (`Verify/AbstractRange.lean`,
   which now imports `Shift`) closes the cutoff branch; `FvarMemoInv`
   mirrors `BoundMemoInv`; ISOK/ISOKF gain the `fvarB` clause
   (survives `flushS` and every environment transition like `bvarB`);
   `abstractRangeM_eff` mirrors `inst1M_eff`.  No exported
   `SimAt`/`IEff` statement changed, so `BinderLoopI` and the DiscI
   walks compiled untouched.
2. **`leafGuardI`'s residual exponential case** (fvar-carrying
   fabrications): the guard's `.all` over the materialized
   `fvarLeavesI fab` list was tree-sized on shared DAGs.
   `leavesSubIGo` performs the fabrication-side containment check as
   one memoized Bool DAG walk (per-call memo, short-circuiting in
   `fvarLeaves` order); `leafGuardI` keeps signature and Boolean, so
   call sites and the DiscI3/DiscI6 guard restatements are untouched.
   `leavesSubIGo_spec` proves the walk against the `Expr`-level
   all-boolean through the `leaves_contains` membership transfer.
   Still materialized: the *base*-side `fvarLeavesI base` list (once
   per guard, tree-sized on adversarial shared bases) — noted as
   remaining.  The brief's `hasFvarI`-O(1) sub-item was *not* done:
   after the walk fix the guard is ~0.1 % of the worst profile, and
   under the eager design below it falls out for free.

**Measured** (`perf stat` instructions, `--yolo` / certified; official
kernel in parentheses; before = task #84 landing):

| test | before (yolo) | after (yolo) | after (cert) | ratio yolo |
|---|---|---|---|---|
| shift-cascade (0.29 G) | 5.87 G | **1.58 G** | 1.58 G | 5.5x |
| shared-subterm (0.37 G) | 4.96 G | **4.69 G** | 5.18 G | 13x |
| repeated-subproblem (0.18 G) | 4.44 G | **4.17 G** | 4.63 G | 23x |
| grind-ring-5 (13.7 G) | 82.8 G | **78.3 G** | 87.8 G | 5.7x |
| init-prelude probe (3.9 G) | 23.8 G | **23.2 G** | 29.4 G | 5.9x |

shift-cascade's ~47 % `abstractRangeIGo` share is gone; its residual
profile is parse + RC substrate (JSON parse alone ~8 %), the same
class as `repeated-subproblem`'s.  Gates: arena 90/92, e2e 53/53,
`lake test`, scale.sh all-PASS (spine 1.29 unchanged from master,
telescope 1.17 — no prepass regression), warning-free, axioms pinned.

**Follow-up design (settled with the user, task #87 family): eager
parallel derived-field arrays.**  The preferred long-term shape for
per-node derived data is *not* the lazy `BMemo` + prepass used here
but an eager array in `EStore` kept congruent with `nodes`: the arena
is append-only and children are interned before parents, so
`EStore.intern` (on cons-table miss, just before pushing the node) can
compute the node's datum in O(1) from the children's entries.  Reads
become `Array.getD`, the whole covers/prepass discipline disappears,
and the invariant is one total ISOK clause (length + pointwise spec).
Task #87 adds expr-level `hasLevelParam` and level-level `hasParam`
that way; `fvarB` (this task) and `bvarB` (#72/#84) should migrate to
the same pattern, which also makes `hasFvarI` O(1) for every caller.
This task shipped the lazy mirror because it was already built and
green when the eager design was settled.

## Eager derived per-node fields: bvar bound, fvar range, has-(level-)param (2026-08-23, task #87)

The settled eager-array design (previous entry) is now the *only*
per-node derived-data mechanism.  A derived field is an eager parallel
array in `EStore`, congruent with its node table (`field.size =
nodes.size`), computed inside `intern`/`internL` on a cons-table miss
in O(1) from the children's already-present entries (the arena is
append-only, children interned before parents); reads are
`Array.getD`; the invariant is part of `EStore.WF` — two total
clauses per field (size congruence + pointwise child recurrence),
maintained by `intern_wf`/`internL_wf` and validated once by `wfB` on
the parse store.  Derived fields never live inside `ENode` (they are
functions of the cons key and must not pollute it or its hash).
Coverage is total by construction: parse-time interning (task #78)
goes through `EStore.intern`/`internL` exclusively.

1. **`bvarBs`/`fvarBs` migration** (`Nat` arrays; loose-bvar bound and
   fvar range).  The lazy `BMemo` caches (`IState.bvarB` #72/#84,
   `IState.fvarB` #86), their prepasses (`bvarBoundsLGo`,
   `fvarRangesLGo`, per-wrapper root walks) and the whole
   covers/`BoundMemoInv`/`FvarMemoInv` discipline are **deleted**.
   The cutoffs fire identically off the store arrays; `hasFvarI` and
   `bvarBoundM` are O(1) reads (closing #86's deferred sub-item, and
   the fabrication leaf guard's `hasFvarI` walk with them).
2. **`lparamBs`** (`Bool`, level side; official kernel `level.cpp`
   `has_param`): `substLIGo` returns param-free levels unchanged
   (covers `substLI`/`substLIList`/`substLIBM` and every binder-cod
   annotation); `lparamsDefinedLIGo` short-circuits.
3. **`eparamBs`** (`Bool`, expression side; official kernel
   `instantiate.cpp:232` `has_univ_param`): at `.sort`/`.const`/
   binder-cod the recurrence reads `lparamBs`, else the disjunction of
   the children's entries (fvar annotations included, matching the
   traversal).  `instantiateLevelParamsIGo` returns level-param-free
   nodes unchanged — every `constTyAt`/`constValAt`/`ruleRhsAt` miss
   on a level-monomorphic constant is a whole-call identity;
   `allLevelParamsDefinedIGo` short-circuits.

Verification pattern (per field): a *spec function* on the tree side
(`Expr.bvarBound`, `Expr.fvarRange`, `Level.hasParam`,
`Expr.hasLevelParam`) with an exactness bridge to the Boolean it
serves (`looseBVarsBounded_iff`, `fvarsBelow_iff`,
`hasFvar_eq_false_iff`, `subst_eq_self`,
`instantiateLevelParams_eq_self`, `allLevelParamsDefined_of_not_*`);
one strong-induction lemma `WF.<field>D_exact` (`denote i = some x →
read i = specFn x`) via the pointwise WF clause; traversal cutoff
branches close by exactness + the `*_eq_self` lemma.  Exactness (not
just soundness) is what makes `hasFvarI`'s Boolean equal to
`Expr.hasFvar` — the memoized `hasFvarIGo`/`bvarBoundIGo`/
`fvarRangeIGo` walk specs are all gone.  ISOK/ISOKF lost their cache
clauses; no exported `SimAt`/`IEff` statement changed (`BinderLoopI`,
DiscI walks untouched).  Item-1 proof-mass delta: **-675 lines in
`Setlec/Verify/*`** (-860 total) — the migration is a net
simplification, as predicted.

**Measured** (`perf stat` instructions, `--yolo` / certified;
before = post-#86 baseline):

| test | before | after (yolo) | after (cert) |
|---|---|---|---|
| shift-cascade | 1.58 / 1.58 G | **1.57 G** | 1.57 G |
| shared-subterm | 4.69 / 5.18 G | **4.59 G** | 5.07 G |
| repeated-subproblem | 4.17 / 4.63 G | **4.08 G** | 4.52 G |
| grind-ring-5 | 78.3 / 87.8 G | **75.4 G** | 84.4 G |
| init-prelude probe | 23.2 / 29.4 G | **22.3 G** | 28.2 G |

~1-4 % across the board — the cutoffs already fired under the lazy
caches; the win is the deleted prepass/covers traffic plus the
level-instantiation pruning, and the structural simplification.
Gates: arena 90/92, e2e 53/53, `lake test`, scale all-PASS (spine
1.30 vs 1.29 on a master-built baseline binary — the pre-existing
exponent, delta within noise; telescope 1.13), warning-free, axioms
pinned.

**Parked: name interning (task #87 item 4).**  `NNode`/`NIdx` arena +
cons table beside `nodes`/`lnodes` (`.anonymous | .str NIdx String |
.num NIdx Nat`), ENode name fields becoming `NIdx`, parse-time intern
directly from the export's `#NS`/`#NI` name-table indices, FEnv index
and `blockNames` NIdx-keyed.  Scoped during this pass: it changes
`denoteNode`'s signature (a name-denotation layer), which touches
essentially every proof in `Verify/IExpr.lean`/`IExprOps.lean` and
all six DiscI walk files (~15 K proof lines) plus ~200 kernel
match sites — a full task of its own (the scale of the task-#62 level
interning), not a rider on this one.  Also noted: the export's
let-nondep flag cannot be threaded onto `ENode.letE` alone — an ENode
field absent from `Expr.letE` breaks canonicity (`denote_inj`); it
needs `Expr`-side threading first.

## Taint skip-and-continue for tolerated-axiom uses (2026-08-24)

User directive: keep the soundness semantics — uses of the tolerated
axiom whitelist (`sorryAx`, `Lean.trustCompiler`, `Lean.ofReduceNat`,
`Lean.ofReduceBool`) are never accepted — but maximize coverage.
Previously the frontend translated the taint sentinel into a
whole-stream decline at the first tainted record, so init-full died
39.3 % in (at `opaque Lean.reduceNat`, whose value uses
`Lean.trustCompiler`) with *nothing* checked.  Now:

* **Tolerated axiom records** are dropped in `processLine` *before*
  the type is parsed into checkable form at all (`Lean.ofReduceNat`'s
  own type references the tainted `Lean.reduceNat`; the old
  well-formedness check of the never-installed record bought nothing);
  the name goes into `State.taintedNames` (root = the axiom itself).
  Any *other* axiom record keeps the previous pipeline exactly:
  forwarded, well-formedness-checked (garbage records keep rejecting,
  arena `bad/011`), pinned standard axioms installed, the rest
  positively declined at their own record (arena 032/033 stay exit 2).
* **Tainted declarations are skipped, not fatal**: a read-only
  pre-scan (`declRecordScan` — declared names plus exactly the
  decl-level expression indices `getDeclEIdx'`/`getDeclExpr'` would
  consult, including inductive member types and rec-rule rhss) runs
  before `processLineCore`; on a taint hit the record is dropped, its
  names tainted (transitive users then skip too), and the skip is
  recorded in `State.taintSkipped` with its whitelisted root.  The
  pre-scan (rather than catching the thrown sentinel) matters for
  ownership: a catch handler closing over the state would hold a
  second live reference across the record's arena inserts, turning
  each into a whole-table copy.  The sentinel remains as a backstop
  mapped to the old decline.
* **Verdict**: `ParseResult.taintSkipped` flows to the driver; after
  the (full) check pass, a nonempty skip set turns exit 0 into 2 with
  a per-root summary on stderr (`Frontend.taintSummary`); rejects and
  errors during the pass keep their own exit codes (a later invalid
  declaration still rejects — pinned by the
  `taint_skip_continue`/`taint_skip_bad_later` e2e twins).  Streams
  with no tainted uses behave byte-identically to before.  Nothing
  tainted can be installed: skipped declarations are absent from
  `ParseResult.decls`, the only path into the checker, so the
  consistency statements (which quantify over the installed
  environment) are untouched — the frontend change is entirely outside
  the verified boundary.

**init-full measurement** (init-full-pre2, streaming, progress mode,
32 GB `ulimit -v` — 8 GB now OOMs: the full-stream arena is ~3× the
old 39.3 % one; child VSZ peaks ~14 GB): the whole 6 223 893-line /
58 609-record stream parses; exactly **two** declarations are skipped
by taint — `Lean.reduceNat` and `Lean.reduceBool`, both via
`Lean.trustCompiler` (`sorryAx`/`ofReduceNat`/`ofReduceBool` are
declared but unused in Init).  Checking then runs 20 156 declarations
accepted before the **new frontier**, a genuine finding in
previously-unchecked territory (the old run checked *nothing* on this
stream): `theorem
_private.Init.Data.Range.Polymorphic.SInt.0.Int32.instUpwardEnumerable_eq`
(stream line 2 113 351, 34.0 %) fails with `internal error: fuel
exhausted: whnfCore`, exit 3 — 91 s wall, 700 G instructions, 4.25 GB
peak RSS to that point.  The `--yolo` (cert-skipping) stack fails
identically at the same declaration, so the exhaustion is in the
shared reduction machinery (`checkFuel = 100000` knot layers), not the
proof-cert feeding.  Not fixed on this branch; the whnfCore fuel
ceiling on that declaration is its own task.

(Superseded in part by task #95 below: the whitelist shrank to
`sorryAx` — the compiler-trust family now *installs* — so the taint
machinery no longer fires on `Init` at all; it remains the mechanism
for `sorryAx` uses and is still covered by the `sorry_*`,
`tolerated_axiom_*` and `taint_skip_*` e2e fixtures, now spelled with
`sorryAx`.)

## The compiler-trust axiom family installs (2026-08-24, task #95)

`Lean.trustCompiler : True` is trivially realizable, and with it the
whole `Init` compiler-trust scaffolding — formerly the only taint
skips on the full-Init stream — installs with full soundness (user
design 2026-08-24).  No new meta-axiom: the consistency theorems still
depend on exactly `[propext, Classical.choice, Quot.sound]`.

* **`Lean.trustCompiler`** (axiom record): a pure branch of the
  `axiomDecl` arm.  Over the pinned `True` family (`trueCvA`,
  `trueIntroCvA` — shapes matched with `matchesPin`, capabilities
  ignored) and the pinned type (`trustCompilerA`), it is installed as
  an `axiomInfo` *realized by* `True.intro`: the pin guarantees
  everything the ordinary opaque check would have checked for that
  witness, and the model values the constant by the stored
  `True.intro`'s interpretation (`trustCompiler_key`,
  `Setlec/Model/TrustAxioms.lean`).  A non-pinned shape under the name
  declines.
* **Opaques are stored as `axiomInfo`** (parity finding, this task):
  `checkOpaqueVal` used to store `thmInfo` ("checked value, never
  delta-unfolded") — but task #66 made *theorem* values delta-unfold
  (official parity), which silently turned every stored opaque
  unfoldable: a reduction-strategy superset over the reference kernels
  (official `is_delta` never unfolds an opaque), latent until now and
  acute with `Lean.reduceBool` installed — it would have *computed*
  `reduceBool b`, accepting exactly the native-evaluation shapes that
  must stay stuck.  A checked `opaque` now stores `axiomInfo`: the
  value is a realizability witness, consumed by the model extension
  (the constant is valued by the witness's interpretation,
  `extend_model` at kind `axiomInfo`) and then discarded.  Nothing
  delta-unfolds it — official semantics exactly.
* **`Lean.reduceNat` / `Lean.reduceBool`** (opaque records): the
  ordinary opaque check plus the install gate `checkReducePin`
  (`reduceOpNames`): the stored constant must carry the pinned type
  (`reduceNatCvA`/`reduceBoolCvA`, over the pinned `Nat` basis
  resp. a standardly-shaped stored `Bool` — `reduceElemOk`), the
  witness value must be definitionally equal to the *build-time pin*
  of the toolchain's own defining expression
  (`Setlec/Kernel/TrustPins.lean`, `#gen_trust_pins` — the task-#53
  machinery reads the opaque's value from the toolchain prelude and
  zeta-expands the `have := trustCompiler` wrapper to the plain
  identity; drift declines, never silently), and the **identity
  certificate** must check: `value x ≡ x` over an opened `fvar` at the
  element type (depth 1).  The certificate is the semantic content;
  the pin defeq is only the gate that makes certificate failure a
  genuine internal error (the task-#47 role separation).
* **Model side**: `EnvModel` gains `reduce_ops : ReduceOpsOk` — a
  stored `axiomInfo` under a reduce-op name with the pinned type is
  interpreted as the identity on its element type, and the element
  inductive is stored.  Established at the opaque's install from the
  identity certificate (`reduceCert_sound`: `isDefEqCore_sound` at the
  certificate valuation, with the app-side typing from the pinned-type
  interpretation `interp_reduceOpTy` and the element facts
  `reduceElem_facts`); transported like `DivModOk`
  (`ReduceOpsOk.cons`, `.recRules_swap`, plus clauses in
  `extend_fresh`/`extend_rules_eq`/GroupSwap; `extend_basis_one` gets
  an auto-discharged trailing hypothesis, `extend_model` a
  caller-facing one).
* **`Lean.ofReduceNat` / `Lean.ofReduceBool`** (axiom records): pure
  pinned branches (the task-#34 standard-axioms machinery).
  `ofReduceAxOk` requires the pinned `Eq` basis, the element
  inductive, the reduce opaque stored with the pinned type, and the
  axiom's annotated type matched against the `AnnotateBasis`-generated
  pins (`ofReduceNatA`/`ofReduceBoolA`).  In the model the types
  interpret to `Prop`-level `pi`-towers whose hypothesis set *is* the
  conclusion set once `reduce_ops` rewrites `reduceNat a` to `a` — the
  proof point inhabits them (`ofReduce_key`); no `Eq` semantics is
  consumed (the equality applications stay abstract).
* **Honest limit**: an actual *use* of `ofReduceBool` needs
  `reduceBool b = true` by defeq, which is stuck on the opaque — such
  a proof only ever comes from untrusted native evaluation, and the
  declaration rejects at its own site (e2e `trust_native_use`,
  `badNative : reduceBool true = true := rfl` exits 1).  The accept
  twin `trust_family` (dependency-closure slice of the full-Init
  export, `scripts/mk_trust_fixture.py`) installs the five
  declarations plus a theorem using `ofReduceNat`'s type vacuously.

Milestone: init-full (streaming, 32 GB ulimit) now exits **0** in both
modes with **61 048 declarations accepted** — the former 61 043 plus
the five compiler-trust installs, zero skips.

## Name interning: NNode arena, NIdx in ENode (2026-08-24, task #88)

Names joined expressions and levels in the hash-cons arena.  `NNode =
.anonymous | .str (pre : NIdx) (s : String) | .num (pre : NIdx) (n :
Nat)`; `EStore` gains `nnodes`/`ncons` beside the node and level
tables, plus `rbNames : Array Name` — an eager derived array (task
#87 pattern, congruent with `nnodes`, filled at `internN` from
`NNode.nameOf`) so `readbackN` is a single array read returning the
*shared* `Name` value built once at intern time.  `ENode`'s name
slots (const, fvar, lam, forallE, letE, proj type-name) are `NIdx`;
name equality inside the arena is index equality; intern probes hash
a `Nat` prefix index + one segment instead of walking `Name` spines.
The parser interns directly from the export stream's name-table
indices (`{"in":i,...}`), so the stream's own sharing carries over
structurally; the taint pre-scan's `taintedNames` lookup goes through
`readbackN`, gated on the map being non-empty.

**Readback at the boundary** (CoreI/CoreNC): the environment stays
`Name`-keyed (`mkFEnv`'s shape is pinned by Model/BridgeS), so a
node-sourced `NIdx` is read back (`readbackNM`, O(1)) before
`fe.find?`; fixed-name pin dispatch uses `beqNameM` (structural
compare against the pin, alloc-free); fabrication sites intern
(`internNameM`, `projFnIdxM` for `(T.proj).i`).  The const caches are
index-keyed: `constTyAt`/`constValAt : (NIdx × List LIdx) → EIdx`,
`ruleRhsAt : (NIdx × NIdx × List LIdx) → EIdx`; `constTyAtM fe nI n
us` takes the index alongside its readback.

**Verification shape.**  `denoteNode den denL denN` gains the name
denotation as the LAST bind of each name-carrying case
(children-first order minimized proof churn across the ~15k restated
lines).  The `denoteN` layer mirrors levels: congruence, inversion,
totality, canonicity (`denoteN_inj`, `denoteN_eq_iff`), `Ext.name` +
`denoteN_mono`; `WF` gains `names_lt`/`nchildren_lt`/`ncons_graph`
and `rbNames_size`/`rbNames_spec`, with `WF.readbackN_eq_denoteN`
rewriting the O(1) readback to the denotation.  The ISOK const-cache
clauses carry `denoteN key = some name` existentials, and the
`constTyAtM_eff`-family lemmas take a `denoteN` premise the call
sites already have in scope from the const-node inversion.  Recipe
for inserting the new monadic steps (readback/beq/internName) into
existing SimAt/IEff walks: `bind_left` with the step's eff lemma,
shadow `hs`, then either transport facts (`replace hX := denote_mono
hextNew hX`) or fold exts (`have hext := hext.trans hextNew`).

**Gates** (all green): `lake build` warning-free, `lake test`, arena
90/92 + e2e 56/56, scale exponents 1.04/1.11 ≤ 1.3, soundness/
consistency axioms exactly `[propext, Classical.choice, Quot.sound]`.
Verdicts identical everywhere.

**Measured** (instructions, `perf stat` best-of-2, vs master 494ed3b):

| bench | yolo | cert |
|---|---|---|
| init-prelude probe | 21.88 G → 22.02 G (+0.6 %) | 27.79 G → 28.03 G (+0.9 %) |
| grind-ring-5 | 75.19 G → 76.39 G (+1.6 %) | 84.19 G → 85.31 G (+1.3 %) |
| shared-subterm | 4.31 G → 4.31 G (±0 %) | 4.79 G → 4.80 G (±0 %) |
| repeated-subproblem | 3.80 G → 3.79 G (−0.3 %) | 4.25 G → 4.23 G (−0.4 %) |

Net ≈ parity: the predicted removal happened — the grind profile
shows `Name` hashing gone from the intern path (master 1.77 %
`instHashableName_hash` + 1.30 % `Name` decEq vs branch <0.4 % +
0.92 %) — but the boundary conversions (readback + `beqNameM` pin
walks + name-side bookkeeping) cost roughly what the hashing saved on
these workloads, where `Name` work was only ~3 % to begin with.  The
value is architectural: `ENode` keys are now fully index-typed
(hash/compare O(1) in all three sorts), and every remaining
`Name`-priced operation is localized at one seam.  Remaining levers,
in profile order: the `Name`-keyed `fe.find?` itself (0.9 % decEq +
map probes; an `NIdx`-keyed env index would need the frontend to
intern install-time names and the Bridge to carry it), and gating the
`readbackNM` in `unfoldDefinitionI`/`reduceNatI` behind cheaper
checks.  Not pursued here: both trade the pinned `mkFEnv` interface
for low single-digit percents.

## FEnv linearity: the def path retained `fe` across the value check (2026-08-24)

**Finding** (linearity audit, `dbgTraceIfShared` probes at every
persistent-container mutation site).  Every `defnDecl` cost one full
copy of the `FEnv.idx` bucket array: the driver branches kept `fe`
live across `checkDefnValP`/`F` for the *conditional* Nat-op
certification (`certifyNatEqs (sharedOps fe) fe.env`,
`checkDivModPinF … fe fe2` — intentionally pre-insertion, see the
Nat-ops design), so the compiler pinned `fe` at RC 2 and the final
`fe.push` copied the whole hash map — a hidden O(n²) in the number of
definitions.  On the init-prelude probe: 2532 shared pushes, 2244 of
them one-per-def from `checkDefnValP` (the theorem path was already a
true tail call, zero copies — the target shape).

**Fix.**  The rare branch is a pure name test
(`natOpNames`/`natDivModNames`, 16 pinned names), so it is decided
*before* the value check: the common path tail-calls
`checkDefnValP`/`F` with `fe` consumed; the rare path keeps today's
exact behavior (still certifying against the pre-push `fe`).  Mirrored
in `checkDeclSF`, `checkDeclNC`, `checkDeclSPNC`.  `checkDeclSF_nonind`
and `checkDeclSP_sim` adapt by an early `by_cases` on the combined
condition — no statement changes, no verdict changes anywhere.

**Measured** (instructions, `perf stat -e instructions:u`).
init-prelude probe 27.98 G → 27.82 G (−0.6 %); copies 2532 → 297
(the residual is the per-inductive `provisionRecsS`/iota-fold and
basis sites, 144+144, bounded by block count — a known separate,
smaller lever).  `many` shape, extended series (startup-adjusted,
successive doubling exponents):

| n | base exp | fixed exp |
|---|---|---|
| 2000→4000 | 1.16 | 1.00 |
| 4000→8000 | 1.27 | 1.00 |
| 8000→16000 | 1.43 | 1.01 |

At n=16000 the fix halves total instructions (8.91 G → 4.54 G).
`tests/scale.sh` all four shapes PASS (chain 1.00, spine 1.26,
many 1.01, telescope 1.11).

**Gates** (all green): `lake build` warning-free, `lake test`, arena
90/92 + e2e 57/57, axioms of the four soundness/consistency theorems
exactly `[propext, Classical.choice, Quot.sound]`, no `sorry`s.

## Two measured asymptotic fixes: telescope and spine walks (2026-08-24, tasks #97/#96)

Scale-comparison profiling at n = 1600 (setlec vs official vs nanoda,
identical adjusted-instructions methodology) showed both references
flat (exponent ~1.0) where setlec was superlinear on two shapes:
`telescope` 1.11@400 → **1.32**@1600, `spine` 1.26@400 → **1.58**@1600.
Both were design bugs with known reference shapes; per the
match-reference ruling the fixes mirror what the references do, no
strategy changes.

**Task #97 — telescope: Array accumulators in the binder loops.**  The
binder-telescope loops (`inferLamsI`/`annotatePisI`/`annotateLamsI`)
kept the opened-fvar accumulator as a cons list; each per-binder
`instListM` converted it wholesale (`List.toArray`: `lengthTR` 10.1 %
+ `toArrayAux` 9.4 % of the n = 1600 run) — Σk = O(n²) bookkeeping.
lean4lean's `inferLambda`/`inferForall` loops push opened fvars onto
an `Array` and substitute with `instantiateRev` (innermost binder
**last**), never converting.  Mirrored: `instantiateRevIGo`/
`instantiateRevI` are `instantiateListIGo`/`instantiateListI` on the
reversed replacement array (same memo discipline, back-indexed `bvar`
hit), `instListRevM` the memoized wrapper with the bound shortcut; the
loops push.  Verification: one pointwise equality
`instantiateRevIGo_eq : instantiateRevIGo vs = instantiateListIGo
vs.reverse` transfers every existing spec; `instListRevM_eff` is
`instListM_eff` at the reversed read (`DenL fvs.toList.reverse ws`),
and the `BinderLoopI` walks restate the accumulator relation through
`toListRev_push`/`toListRev_singleton`.  Mirrors, chained spec, and
everything above unchanged.

**Task #96 — spine: annotate walks the spine once.**  The residue
flagged under task #85 above: `annotateBodyI`'s chained app case ran
`r.infer` on **every spine prefix**; each prefix (a distinct index —
memoization cannot help) re-decomposed the spine (`getAppFnI`/
`getAppArgsAccI`, ~15 %) and re-walked the root telescope through
`inferSpineI` with a `codNonZeroIM` gate probe per position (~7 % of
hash-lookup traffic — the `lnzC` memo *hits*; the quadratic was the
call count, Σ O(i) = O(n²)), plus per-prefix argument lists (~20 %
RC/alloc).  The official kernel's `infer` of an application walks the
spine once with an argument accumulator; annotation is setlec's own
extra pass, so its app case gets the same discipline:
`annotateSpineI` peels the head's raw Π-telescope against the whole
spine with deferred substitution (Array accumulator, task #97's
`instListRevM`), replaying exactly the chained per-application checks
in the chained order — argument annotated before the function part is
inferred, `whnf` skipped on a syntactic `∀` (where it is the
identity), substitute-and-normalize otherwise.  `inferSpineI`/
`inferSpineNC` accumulators went `Array` in the same stroke (both
knots share `annotateBodyI`, so certified and `--yolo` paths are both
covered).

Verification (`Setlec/Verify/AnnotSpine.lean` + `DiscI6`): the pure
mirror `annotateSpine`/`annotateApp` (generic over the core record)
with arm/`atF` equations, and the soundness of the loop against the
chained spec — `annotateApp_sound_body` reproduces a successful
mirror run in the chained `annotateBody` at some fuel, by forward
induction with two step lemmas: `annotateStep_chain` (the chained app
body succeeds on the loop's per-argument facts) and
`inferStep_extend` (the prefix-type fact `infer cur =
ty.instantiateList acc` extends by one argument through
`inferBody_app_pure` + `inferStep`, the loop's checks discharging the
possibly-Prop-gated re-check).  The interned walk `annotateSpineI_sim`
(mutual with its normalize-and-retry arm) simulates the mirror, and
`annotateBodyI_sim`'s app case composes it with the soundness bridge
via `SimAt.wr` — the same seam as `inferSpineI`'s task #50
construction.  The `Expr`-level spec and the Model layer are
untouched.

**Measured** (scalecmp dstreams, adjusted instructions, exponents per
doubling): telescope 1.01 flat through n = 1600 (was 1.32; absolute
4.1× at 1600), spine 0.99-1.01 flat through n = 1600 (was 1.58;
absolute 3.1× at 1600); chain/many unchanged (1.02-1.04).  Reference
comparison: setlec's exponents now match official/nanoda (~1.0) on
all four shapes.  Real streams improve too (vs master ffcc17a,
instructions): init-prelude probe 27.99 G → **26.44 G** certified
(−5.6 %), 21.73 G → **20.46 G** `--yolo` (−5.8 %); grind-ring-5
83.71 G → **78.15 G** certified (−6.6 %), 75.03 G → **70.45 G**
`--yolo` (−6.1 %).  Gates: `lake build` warning-free,
`lake test`, arena 90/92 + e2e 57/57, scale.sh all PASS, soundness/
consistency axioms exactly `[propext, Classical.choice, Quot.sound]`,
verdicts identical.

## Raw (annotation-free) storage: the erasure witness (2026-08-24, task #100)

The environment currently stores expression trees carrying binder
*codomain-sort annotations* (`BinderMeta.cod`), produced by the
`annotate` pass and consumed by the model: the structural `∀`/`λ`
interpretation needs the binder's Prop-or-not bit, and the annotation
is where it comes from.  The refactor removes them from storage — the
kernel stores and computes with **raw** trees — while the model keeps
its level source on the proof side.

### Why an annotation witness is forced

The alternative (drop annotation data from the model as well, deriving
the binder classifier semantically or structurally) is refuted, with
checked witnesses in `Setlec/Model/RawEnvNoAnnot.lean`:

* the interpretation reads its level argument only through the `v = 0`
  test (`pi_pos`/`lam_pos`), so what a binder needs is exactly one bit;
* that bit is **not** a function of the semantic data.  `⟦Nat.succ
  Nat.zero⟧ = pt` (the von Neumann `1` *is* the proof point) and
  `⟦PUnit⟧ = truthVal True`, so `fun (_ : PUnit) => (1 : Nat)` and
  `fun (_ : PUnit) => True.intro` present identical domain values and
  identical body-value functions while requiring different
  interpretations (`lam_interp_not_value_determined`);
* nor is it computable structurally: `Nat.imax` preserves the proof
  bit through application but destroys the codomain's sort, and large
  elimination makes the classifier whnf-dependent — computing it *is*
  the inference the annotation pass performs.

So the level source moves to a per-declaration **annotation witness**.

### The erasure view

A witness for a raw tree `e` is an annotated twin `ê` with
`ê.eraseCod = e`; a witness for a raw environment is an annotated
*shadow environment* that erases to it.  `interpExpr`, `AnnotOk`,
`EnvModel` and the whole `Extend*` tower then survive **verbatim** as
statements about the shadow; only the env-facing seam changes:

* `RawEnvModel V env = {aenv, erase_eq : aenv.eraseCod = env, model :
  EnvModel V aenv}` (`Setlec/Model/RawEnv.lean`);
* raw-side syntactic certificates (freshness, `hasFvar`,
  `constsResolve`, `looseBVarsBounded`) transfer across erasure —
  those predicates read no annotation;
* semantic obligations (`AnnotOk`, interpretations, and
  `allLevelParamsDefined`, which reads annotation levels and is
  therefore deliberately *not* raw-derivable) stay phrased on the
  witness;
* twin tracking through reduction rests on erasure being
  constructor-wise: it commutes with `instantiate1`,
  `instantiateList`, `instantiateLevelParams`, `abstract1` and
  `abstractRange`, so the existing substitution lemmas apply to the
  twin unchanged.

`Setlec/Model/Erasure.lean` is that seam library, plus the inversion
lemmas (`eraseCod_eq_app`, …) and the one family of syntactic
environment checks erasure does *not* preserve: the literal-support
guards.  `natLitSupported`/`strLitSupported` pin the *annotated*
stored types of the `Nat`/`String` basis declarations; their **raw
forms** (`natLitSupportedRaw`/`strLitSupportedRaw`) drop exactly the
`mb.cod` conjuncts, and the congruences
`natLitSupportedRaw_erase`/`strLitSupportedRaw_erase` say the
annotated guard on the witness implies the raw guard on what the
kernel stores — so a raw kernel's literal paths are open wherever the
model's are.  `extend_model_raw` is the split in miniature for a plain
definition install.

### The `codOf` memo

What the annotation stores, a raw kernel must recompute: the codomain
sort of a binder is `ensureSort ∘ infer` on the binder's body (the
`∀`-clause) resp. on the body's inferred type (the `λ`-clause).
`codOfCore` (`Setlec/Kernel/TypeChecker.lean`) is that composite at
the pure knot; `codOfI` (`Setlec/Kernel/CoreI.lean`) its interned,
memoized twin — memo `IState.codOfC : EIdx → LIdx`, depth-free like
the entry-point memos (by `codOfCore_depth_inv`), flushed with them at
environment transitions.  Both are knot-parametric, so the
cert-skipping knot uses them unchanged.

Verification mirrors the entry-point memos exactly: an `ISOK.codOfC`
clause (every entry backed by a pure `codOfCore` run at some fuel, at
every depth at which the key is well-scoped), `ISOK.insertCodOfC`, and
`codOfI_sim` — a hit consumes the backed entry, a miss runs
`infer`+`ensureSort` (`SimAt.bind` of `ih.infer` and
`ensureSortI_sim`) and re-inserts depth-universally.  The fueled
comparand is `codOfF`, with `codOfF_atF` and `codOfCore_mono` derived
from the family.

The memo is **not consumed for verdicts**: annotations remain the live
mechanism and nothing on a verdict path calls `codOfI`, so verdicts
are byte-identical by construction.  Feeding it from `annotate` was
considered and rejected as throwaway: `annotate` is what the
decoration pass replaces, so entries produced there would be produced
by `decorate` anyway.  Cost of carrying the extra `IState` field on
the init-prelude probe: 25.187 G → 25.203 G instructions, **+0.064 %**
(three runs each, spread < 2 M).
## Asymptotic scalability harness v2 (2026-08-24, task #98)

`tests/scale.sh` grew from 4 to 13 gated shapes, per-shape gates, a
deep mode, RSS gating, and a reference-comparison companion.  This
section is the harness's reference documentation; the 2026-08-22
section above records the original design and first findings.

**Generators are deduplicated.**  `tests/scale/gen.py` hash-conses
every name/level/expr table entry it emits.  Real lean4export never
emits two structurally identical entries, and consumers rely on it —
upstream nanoda crashes on duplicate entries.  Deduplication is part
of the format contract, folded into the emitter (there is no
postprocessing step to forget).  Every generated shape is validated
against the official kernel checker (all 12 stream shapes accepted by
official-v4.33.0 and upstream nanoda).

**Shapes** (`gen.py SHAPE N`; one subsystem each):

* `chain` — n-deep `d_i : Type := d_{i-1}` delta chain forced at the
  type level;
* `spine` — one application spine of n arguments;
* `many` — n independent tiny defs (env insertion / per-decl setup);
* `telescope` — one Π/λ telescope of depth n (binder opening);
* `dag` — one definition whose value is a *perfectly shared* binary
  DAG of depth n (`e_{i+1} = g e_i e_i`).  The expr table is O(n);
  any unmemoized structural traversal is O(2^n) — this shape turns a
  violation of the no-unmemoized-traversals invariant into an
  immediate catastrophic exponent/timeout, so its gate is tight;
* `delta` — n defs `d_i : Prop := (fun x : Prop => x) d_{i-1}` plus a
  proof of `d_n`, forcing n delta+beta whnf steps (value-level
  unfolding, complementing `chain`'s type-level chain);
* `ctors` — one inductive enum with n constructors, an n-rule
  recursor, and a use firing one iota step.  Note the export format
  itself is Θ(n²) bytes here (each rule RHS λ-binds all n minors), so
  2.0 is the *input-size floor* for this shape's exponent;
* `fields` — one structure with n `Prop` fields plus a use projecting
  every field.  Run twice: `fields-raw` (preprocessor disabled — the
  direct simple-structure install) and `fields-mod` (through the
  lean-inductive-models preprocessor — the modeled path);
* `fanout` — one def referencing all n predecessors (n const lookups
  inside a single declaration; guards per-lookup env-index copy bugs
  of the FEnv-linearity family, previous section);
* `lets` — one n-deep `letE` chain (lazy zeta);
* `lparams` — one def with n universe parameters, instantiated at a
  use (level instantiation + n-ary max normalization);
* `thm` — one theorem with a size-n proof value (`thm`-record path).

**Methodology.**  Retired instructions (`perf stat -e
instructions:u`), median of 3 runs; per-shape startup baseline = the
same shape at n=1 (covers basis install, IO, and the preprocessor's
fixed cost for the `-mod` shapes), subtracted before fitting; growth
exponent = log2 of the adjusted ratio per doubling; the gate applies
to the exponent at the **largest** step, where superlinearity reads
strongest (pre-fix `spine` read 1.26 at n=400 but 1.58 at n=1600).
Peak RSS is fitted the same way for the shapes whose retained state
grows with n (`chain`/`many`/`dag`/`thm`): max of 3 runs of the
process tree's `ru_maxrss` (a Python `getrusage(RUSAGE_CHILDREN)`
wrapper — portable, no GNU time dependency).  RSS is far noisier than
instructions: on master the adjusted retention at the largest
standard n is < 3 MB, inside allocator noise, so per-doubling RSS
exponents there are meaningless.  The RSS gate therefore has a signal
floor (16 MB adjusted at the top point — `dag`/`thm` legitimately
retain ~8 MB at the deep sizes): below it the shape passes as
"retention flat"; above it — where a real retention blowup lands at
once — the largest-step RSS exponent must meet a generous gate
(1.60).  Measured master retention: chain 0.7 MB @3200, many 2.3 MB
@3200, dag 7.7 MB @6400, thm 8.4 MB @6400 — all linear-or-flat.

**Modes.**  Standard (`tests/scale.sh`, also `--ci`): 4 points per
shape (n..8n), ~1 min measured (budget 2-3 min on a loaded machine) —
the merge-gate profile.  Deep (`--deep` / `SCALE_DEEP=1`): up to 6
points (n..32n, per-shape caps keep the superlinear shapes bounded),
~3-4 min measured (budget ~10 min) — for performance work and nightly
runs; borderline standard-mode readings become unambiguous here, so
the superlinear shapes carry separate deep-mode gates calibrated at
the deep sizes.  No wall-time fallback exists: without working perf
counters the harness prints a prominent SKIP notice and exits 0 (a
flaky gate is worse than an absent one).  Without the
lean-inductive-models preprocessor only the `-mod` shapes are
skipped, with a notice.  Deliberately **not** part of `lake test`
(`tests/SetlecTests.lean` is `#guard`-based build-time; scale needs a
built binary, perf, and a process per stream): CI should invoke
`tests/scale.sh --ci` as its own job step after `lake build`.

**Gate rationale.**  Per-shape gates = measured master exponent +
slack, not a blanket threshold.  Measured on master 4f63b6c and
re-confirmed identical (±0.01) on 6e29d67 after merging tasks
#95/#88 (2026-08-24, instructions adjusted per methodology; "std" =
largest standard step, "deep" = largest deep step):

| shape | std exponents per doubling | std | deep | gate std/deep | RSS |
|---|---|---|---|---|---|
| chain | 1.02 1.01 1.01 | 1.01 | 1.01 @3200 | 1.15 | flat |
| spine | 1.02 1.01 1.01 | 1.01 | 1.01 @1600 | 1.15 | — |
| many | 1.01 1.01 1.01 | 1.01 | 1.01 @3200 | 1.15 | flat |
| telescope | 1.03 1.01 1.01 | 1.01 | 1.01 @1600 | 1.15 | — |
| dag | 1.01 1.02 1.01 | 1.01 | 1.01 @6400 | 1.15 | flat |
| delta | 1.02 1.01 1.01 | 1.01 | 1.01 @3200 | 1.15 | — |
| fanout | 1.02 1.01 1.01 | 1.01 | 1.01 @3200 | 1.15 | — |
| lets | 1.02 1.01 1.00 | 1.00 | 1.01 @3200 | 1.15 | — |
| lparams | 1.16 1.32 1.49 | **1.49** | **1.78** @3200 | 1.65/1.95 | — |
| thm | 1.01 1.00 1.01 | 1.01 | 1.00 @6400 | 1.15 | flat |
| fields-raw | 1.76 2.02 2.31 | **2.31** | **2.74** @800 | 2.60/2.90 | — |
| ctors-mod | 2.09 2.31 2.58 | **2.58** | **2.76** @64 | 2.90/3.00 | — |
| fields-mod | 1.06 1.59 2.08 | **2.08** | **2.43** @128 | 2.40/2.70 | — |

The nine flat shapes gate at 1.15 (tight — regressions past ~n^1.15
fail immediately).  The four bold shapes are **superlinear on current
master** — findings recorded by this harness, gated at measured+slack
so they cannot silently get worse, to be fixed as their own tasks:

* `lparams` (1.49 → 1.78 deep, rising toward 2): profile is dominated
  by `Name` decidable equality under `Level.allParamsDefined`'s
  `List.elem` and `Name.nodup` — per-declaration well-formedness does
  O(n) linear list membership per parameter, O(n²) total.  The
  references share this shape: on the same series the official
  checker reads **1.41** and upstream nanoda **1.31** — a quadratic
  everyone has, but setlec's curve is the steepest.
* `fields-raw` (2.31 → 2.74 deep): the direct simple-structure
  install spends ~40 % in tree-level
  `Expr.instantiate1`/`instantiate1Lift` — per-field/projection
  telescope instantiation on unshared trees.  The official checker is
  **flat (1.07)** on the identical streams (nanoda reads 1.80), so
  linear is achievable and this is setlec-specific.
* `ctors-mod` (2.58 → 2.76 deep, against an input-size floor of 2.0,
  i.e. ~ (input bytes)^1.4): attribution by running the pipeline
  stages separately at n=64 puts ~3.4 G instructions in the
  preprocessor but ~72 G in the checker on the preprocessed stream
  (spread across `EStore.intern`, `instantiateListIGo`, `iotaRecI` —
  the modeled install's per-rule work over n rules).
* `fields-mod` (2.08 → 2.43 deep): both stages superlinear at n=64
  (preprocessor ~1.5 G, checker ~2.5 G).

**Reference comparison** stays a LOCAL script,
`tests/scale/compare.sh` (references are not on CI): the same
adjusted-median methodology applied identically to setlec, the
official kernel checker, and **upstream** nanoda (override binary
paths via `SET`/`OFF`/`NAN`).  2026-08-24 run: all three checkers
flat on chain/spine/many/telescope/dag/delta/fanout/lets/thm; all
three superlinear on lparams (setlec 1.49, official 1.41, nanoda
1.31); on fields official is flat (1.07) while nanoda (1.80) and the
setlec pipeline (2.62 through the preprocessor) are not.  Pitfall,
spelled in the script header: the `_tmp/nanodatg` clone is the
*certifying fork*, quadratic by design on several shapes — growth
comparisons must use upstream nanoda, built from ammkrn/nanoda_lib.
nanoda additionally *requires* structurally deduplicated table
entries (it crashes on duplicates), which is why the generator
hash-conses everything.

### Raw storage stage 3: decoration, and the erasure as a parameter (2026-08-24, task #100)

Three moves, all staged so the flip from the identity erasure to
`Env.eraseCod` is local.

**The erasure is a parameter.** `RawEnvModelE V er env` carries the
annotated shadow `aenv`, `erase_eq : er aenv = env`, and the unchanged
`EnvModel V aenv`.  `RawEnvModelId := RawEnvModelE V id` is the
transitional instantiation — annotations are still stored, so the
witness *is* the stored environment, and `ofEnvModel`/`toEnvModel` are
inverse — while `RawEnvModel := RawEnvModelE V Env.eraseCod` is the end
state.  `Setlec/Model/ConsistencyRaw.lean` restates `checkDecl_sound`,
`checkDecls_sound` and `no_constant_of_Empty` over that interface at
`id`: no content, all interface, so that consumers phrased against it
survive the flip untouched.

**Decoration.** A raw-storage kernel must put annotations back before
`infer`/`whnf`/`defeq` — which read them — can run.  `decorate`
(`Setlec/Model/Decorate.lean`) is the proof-side spec of that rebuild:
structural everywhere, filling each binder's `cod` from a `DecorMemo`
(the proof-side view of the interned `inferC`/`codOfC` pair — a
`∀`-binder's sort is `codOf` of its opened body, a `λ`-binder's is
`codOf` of that body's *inferred type*, hence two components).  It
performs **no** inference, reduction or definitional equality.

Its theorem is therefore syntactic, not semantic: `decorate_eq` says
that decorating the erasure of an annotated tree returns that tree
*exactly*, provided the memo agrees with its annotations at every
binder (`CodAgree`).  Truthfulness then costs nothing —
`decorate_sound` rewrites through the identification and hands the goal
to `annotate_sound`.  That is the point of the split: the decoration
pass carries no semantic burden of its own, because the annotations it
restores are the ones the annotation pass already justified.  All the
content sits in `CodAgree`, which the flip discharges from the memos'
`ISOK` clauses.

Two findings shaped the definition:

* **Two erasures.** `Expr.eraseCod` is hereditary — it descends into
  `fvar` type annotations, which is what makes twins survive binder
  opening during reduction simulation.  A decoration pass opens binders
  itself, at variables whose types it has *already* decorated, so its
  `fvar` clause must be the identity; the matching erasure is the
  shallow `Expr.eraseCodS`.  The two agree on `fvar`-free trees
  (`eraseCodS_eq`) — i.e. on everything a declaration stores, by the
  install-time certificate — so the top-level statement is unaffected,
  and the non-recursive `fvar` clause is also what makes `decorate`
  terminate on `sizeB` (the measure `AnnotOk` uses, for the same
  reason).
* **Decoration targets are let-free.**  `annotate`'s `letE` clause
  zeta-reduces (value transparency; an opened opaque let-variable was
  tried and rejects real streams).  So its output — and hence every
  decoration target — contains no `letE`, and `CodAgree`'s `letE`
  clause is `False`.  Correspondingly, what a raw-storage kernel keeps
  is the *erasure of the annotation pass's output*, not of the input
  record: `annotate` is not skeleton-preserving (it zeta-reduces lets
  and normalizes projection heads), so `(annotate e).eraseCod = e` is
  false in general and cannot be the storage contract.

**Install paths.**  `extend_model_raw` is now generic in the installed
`ConstantInfo`, so it covers every non-inductive path at once — axioms,
definitions, theorems, opaques, and the pinned `Nat`-operation /
`Nat.div`-`Nat.mod` / `reduce` families, whose extra obligations ride
through unchanged; `extend_model_raw_defn`/`_axiom`/`_thm` are its
instances.  The hypothesis split is the design's claim in miniature:
raw-side certificates (freshness, `hasFvar`, `constsResolve`,
`looseBVarsBounded`) transfer across erasure, witness-side obligations
(`AnnotOk`, interpretations, `allLevelParamsDefined`) stay on the
shadow.  For the remaining paths — inductive blocks, projections,
direct structures, basis pins — the mechanical content is
`RawEnvModelE.extend`/`extend_one`: *any* extension of the witness is
an extension of the raw environment it erases to, given that the
installed records erase to what is stored.  Each sibling is that
combinator applied to the `extend_*` lemma the path already uses; no
signature needs restating.
