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

Axioms: only the standard axioms are supported; anything else is
"declined" (lean kernel arena exit convention).  This is a deliberate
ceiling (owner ruling, 2026-08-21): the two tutorial tests scaffolded
by custom axioms (`032_letTypeDep`, `033_letRed`, declining precisely
at their `axiom` records) stay declined by design, so the vendored
tutorial snapshot tops out at 90/92 accepted — the full non-axiom
set.  Acceptance routes for custom axioms (opaque-with-witness,
unfoldable-definition storage, canonical-value models) were explored
and rejected: none is wanted.  `Quot.sound` is part
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
checker's guards, the preservation lemmas, and closedness of
checker-constructed statements (`buildIotaStmt_not_hasFvar`, the
`natOpEquations`/`substConst0` scoping lemmas).
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

### Inference re-checks; infer-only deferred

The official kernel's inference is *infer-only* inside reduction
(argument checks ran once, at declaration time).  Setlec's `inferBody`
**re-checks** the application argument (defeq against the domain) and
the λ-annotation (against the body's inferred sort), as the
pre-restructure checker did: the soundness claims re-derive their
membership slots (`⟦a⟧ ∈ ⟦domain⟧`, fibres-in-universe) from those
checks at the claims' own fuel.  Deriving them without the checks
would need the annotation-time facts, which live at a *different*
fuel — i.e. the fuel-determinism machinery of the refinement bridge —
plus a strengthened `AnnotOk` app clause.  Revisit once the bridge
lands; until then the speculative-inference-cannot-reject property is
weakened (a re-check could in principle fail on a reduced term whose
annotate-time check passed; not observed on the suite).

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
`mul`→`add`, `pow`→`mul`,`add`) and, for the `Bool`-valued ops, the
`Bool` constructors, all stored level-monomorphic.  Bodies cannot be
pinned instead: elaborator output is `brecOn`-compiled and is *not*
definitionally equal to the plain `Nat.rec` spelling at stuck majors —
only the recurrence equations are.  WF-recursive ops (`div`, `mod`,
`gcd`) and string literals remain deferred.

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
* The K rescue's explicit fabricated-type check (implied by the
  load-bearing iota certificates that run on the fabrication).

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
native `.letE`
(the frontend zeta expansion can duplicate exponentially on shared
exports); string literals; the performance substrate (cached hashes /
hash-consing, array spines, indexed environment, per-declaration cache
threading, possibly-Prop-gated iota certificates); per-loop fuel
budgets; instrumenting the possibly-Prop beta wedge (3.5) as an
internal-error signal; removing the codomain-annotation comparison in
binder defeq (documented deviation, benign for well-typed input).

## Stuck-major rescue: rule K and structure eta in iota (2026-08-20)

`majorToCtor` (in the mutual core, mirrored in the cached twin)
implements `to_cnstr_when_K` and `to_cnstr_when_structure`: a
recursor's major premise that does not whnf to a constructor
application is *replaced* by a fabricated one.

* **K**: for a K-flagged inductive proposition (single-rule recursor,
  zero-field constructor), the constructor applied to the first
  parameters of the major's reduced type.  Certified by `proofIrrel`
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
(`majorToCtor_claims` in `Setlec/Model/TypeChecker.lean`) assembles
the fabrication's `AnnotOk`/interpretation from the constructor
telescope's iota certificates (`certs_fit` + `TeleFit.chainSlots` +
`annotOk_spine`), the reduced type's argument spine, and (for eta) the
projection certificates; the value identification is proof irrelevance
(K) or the stored eta law via `structEtaWith_sound` (eta).

Zeta expansion required a fix along the way: let-values are *open*
terms, so substituting them under binders needs the lifting
substitution `instantiate1Lift` (`instantiate1`'s contract requires a
closed replacement; the old code silently corrupted nested lets —
surfaced by the preprocessor's let-heavy `iota_0` proofs).

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
function types, lambdas/apps with certified beta, lets (zeta-expanded in
the frontend), constants with delta unfolding, all five basis blocks
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
`EtaPins` carried through the member fold discharge, at the
inductive's install, the stored `EtaLaw` (ModeledOk's fourth clause)
via `eta_rule_fold` — every member of the interpreted structure type
is the constructor model applied to the projection models;
`structEta_sound` consumes the law with a `TeleFit` built from the
certified telescopes (`certs_fit`), interprets the synthetic
projection chains through `TeleFit.chainSlots`/`annotOk_spine`, and
bridges public values to the models' with `ModeledOk`.  With this the
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
pinned declaration.

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

**Canonical rules only; nested-aux rules are inert.**  A rule is
*canonical* (`Expr.recRulePlain`) when its constructor-parameter count
is within the recursor prefix and the major's domain starts with the
recursor's own leading binders.  Nested/auxiliary rules (e.g. the
`List.cons` rule of a nested recursor, whose major lives at an inner
type former) have no `iota_j` theorem and no provable fold fact — they
are stored **inert**: `iotaRec` guards on `recRulePlain` before firing
(runtime), `checkIotaRule` only consults the theorem for canonical
rules (install), and `RecRulesOk`'s fold clause hypothesizes
`recRulePlain` (soundness), so inert rules' obligations are vacuous.
No completeness is lost on the tutorial arena (no nested blocks) and
declines stay declines.

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
