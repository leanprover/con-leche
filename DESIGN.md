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
ceiling (owner ruling, 2026-08-21): acceptance routes for custom
axioms (opaque-with-witness, unfoldable-definition storage,
canonical-value models) were explored and rejected: none is wanted.
Refinement (user ruling, 2026-08-22): non-pinned axioms are
*invisible*; their uses are unsupported.  A non-pinned `axiom` record
no longer stops the run — the record is still well-formedness-checked
(the official kernel checks the declaration, so a garbage record such
as arena `bad/011_nonTypeAxiom` keeps rejecting) but nothing is
installed, and the frontend taints the axiom's name
(`State.skippedAxioms`, generalizing the previous `sorryAx`-only
mechanism): any later declaration whose type or value references a
skipped axiom is positively declined at its own record.  The two
tutorial tests scaffolded by custom axioms (`032_letTypeDep`,
`033_letRed`) thus now decline at their first *use* of the axiom
rather than at the `axiom` record — still exit 2, so the vendored
tutorial snapshot stays at 90/92 accepted, the full non-axiom set.
This lets streams like `Init.Core` run past `Lean.trustCompiler`
instead of dying there (the next blocker is then the first
declaration that *uses* it, e.g. `Lean.reduceNat`).  `Quot.sound` is part
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
  (frontend memory on the 336 MB export; the `Lean.trustCompiler`
  axiom declines by design — since 2026-08-22 at its first *use*, not
  its record; the `Unit.sizeOf` mismatch is fixed, see the basis
  `PUnit` rescue note) — the previous positive declines at
  `Nat.land`/`Nat.shiftRight`/… literal uses are gone.

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

The frontend zeta-expands every parsed type and value (the checker
works let-free); the recursor-rule `rhs` slot was the one parsed
expression missed (fixed 2026-08-22, task #60): a preprocessor-emitted
`let` in a modeled recursor's rule (`Std.Packages.PreorderOfLEArgs`)
hit install's `letE` decline.  The rule rhs now goes through the same
`.zetaExpand` — pure input normalization ahead of annotation; the
model layer only ever consumes the stored (annotated) rules.

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
(`proofIrrel_pt`); no new model obligations — `ModeledOk`'s eta
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
by interning) ≈ 7 %, `Level.decEq` now only ≈ 3 % (the audit's
level-interning priority was measured against a pointer-equality
proxy; with real interning the remaining level-comparison cost is
small).

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
