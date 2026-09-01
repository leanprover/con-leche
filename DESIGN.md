# Setlec — a verified Lean checker

Setlec is a checker for Lean declarations, implemented in Lean, verified in
Lean. The goal is a checker that is performance-competitive with lean4lean or
even the official kernel, together with a machine-checked consistency proof:

> For everything the checker accepts there is a model in a suitable set
> theory. In particular, no declaration of type `Empty` is ever accepted.

This document records the design decisions. It was distilled from the initial
project prompt and is updated as decisions evolve.

**Where the consistency proof lives** (since task #148 T7, 2026-08-29):
`Setlec/SetR/*`, whose fourteen `*_R` theorems — `checkDecls_sound_R`,
`no_proof_of_Empty{,_input}{,_C,_S,_SP}_R`, `checkDecl_sound_R`,
`no_constant_of_Empty_R` — stand hypothesis-free at exactly
`[propext, Classical.choice, Quot.sound]`. Its design record is
`Setlec/SetR/DESIGN.md`.

**Two tiers were retired at T7/T7b, by user ruling.** The direct `Expr`
set model and its consistency proof (`Setlec/Model/*`, 83 files / 62,992
lines, invariant `EnvModel`) and the declarative verification lane
(`Setlec/TTVerify/*`, 50 files / 33,808 lines, invariant `EnvTT`) are
deleted, together with the `--tt-model` mode the second was stated at.
The `Setlec/SetR/*` theorems replace both, claim for claim. Prose
references to those paths elsewhere in this document are historical
citations. `Setlec/TTVerify/DESIGN.md` is deliberately kept (its §0/§25
are the house practices); so is the declarative layer
`Setlec/TT/{Syntax,Subst,Const,Judgment}` + `Setlec/TT/Semantics/*`,
because `Setlec/SetR/*` consumes `VExpr`, `interp`, `bval` and
`HasType.const`/`HasType.sound` — see `Setlec/SetR/DESIGN.md` "T7b" for
the consumer measurement that fixed that boundary. Its design record is
`Setlec/TT/DESIGN.md`.

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
(`Expr.eraseNames`); the pins themselves carry only `.default` binder
annotations, matching the frontend's parse-time strip (task #142
below).  The interpretation never reads what is erased
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
  (`Setlec/SetTheory/*`, `Setlec/SetR/*`, `Setlec/Verify/*`). The
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
9. Load the `lean-rc-linearity` skill (`.claude/skills/lean-rc-linearity/`) before
   any task touching hot-path state threading, memo/arena mutation, or per-node
   arithmetic: it distills the Lean runtime's RC/linearity model together with this
   project's measured RC-2 incidents, diagnosis toolkit and codegen landmines.

## Environment notes

* Sandbox: `/tmp` and `/home` are tmpfs — large artifacts (repo checkouts,
  worktrees) go into `_tmp/` inside this repository (gitignored).
* If the checker may OOM, run it under a timeout and memory limit; a process
  eating all memory can kill the whole session.
* In a fresh worktree `_tmp/` is empty (gitignored), so the lean-inductive-models
  preprocessor is missing and every inductive fixture declines (exit 2) —
  `tests/arena.sh` then reports spurious CHANGE/FAIL lines.  Run it with
  `SETLEC_INDUCTIVE_MODELS=<main checkout>/_tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models`.
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
  scratch), then made *self-contained* by inlining every constant
  outside the op's own dependency cone and the guard-enforced ground
  (task #113 — see "Self-contained certificate proofs" below; an
  unjustifiable residual aborts generation loudly, i.e. fails the
  build).  At install each
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
  the supported streams and intersected per op.  Since task #113 they
  apply to the **pins only** (the certificate proofs are closed over
  the op's own dependency cone instead, see below).  The install-time
  `constsResolve` guards remain the actual gate; the allowlist only
  makes generation fail early and loudly.
* **Self-contained certificate proofs (task #113; supersedes the
  2026-08-24 "prefix allowlists vs. stream order" fix).**  A cert
  proof closed over a stream-*prefix* allowlist may reference any
  constant the supported streams happen to declare before the op —
  which a dependency-**sliced** stream (the cone-slicing debugging
  workflow) need not provide: historically `Nat.log2_terminates` on
  the Mathlib order, then `funext`/`Eq.subst`/`Eq.propIntro`/
  `of_decide_eq_true` on dependency slices ("pin ground constants
  absent" declines killing the slice before its target).  The proofs
  are therefore made *self-contained*: the generator inlines every
  constant outside `{the op itself (substituted at install)} ∪
  {guard-enforced ground: natOpDeps mirror + Nat/Bool/Eq statement
  machinery} ∪ {the op's transitive type/value dependency cone}` —
  the cone members are exactly what *any* stream declaring the op
  must declare first.  Beta/projection-of-constructor simplification
  (`simpStep`) cleans up the arithmetic instance sugar (`HMul.mk` …),
  and equation-compiler internals (`._f` functionals, `match_i`
  matchers) are force-inlined even when cone-resident: the export
  pipeline beta-inlines the brecOn functional into stored `go`
  values, so the *stream's* cone need not declare them.  A residual
  the rule cannot justify is a hard build error.  To keep the proofs
  inside their cones, `Setlec/PinGen/Certs.lean` avoids the stock
  lemmas whose proofs leave them: `WellFounded.Nat.fix_eq` (and the
  auto `eq_def`s of `gcd`) mention `funext` → `Quot.*`; instead a
  pointwise-congruence unfolding (`natFixGoCongr`/`natFixUnfold`,
  with per-op `dcongr`-based congruence hypotheses — first-order
  recursive occurrences never need function extensionality) derives
  the one-step equations; `log2` is proved from a mirror of its
  fuel-structural compiled value (`log2Go`, plain `Nat.rec` — no WF
  machinery), with the `n/2 ≤ f` fuel bound hand-derived from the
  file's own `div` certificates (`Nat.div_lt_self`'s stock proof
  pulls `Or`/`Exists`/`propext`/`Acc`).  Blob sizes stay far under
  the 2^25 tree budget (max ≈1.8 M unshared-tree / 8 k-node DAG per
  op, `Nat.xor`); a *naive* full inlining had exploded to 2^40
  saturated trees.  Each proof blob is spliced as its **own**
  definition (`…CertProofs_i`) with `…CertProofs` a shallow constant
  list: the model bridge (`Setlec/Model/DivModCert.lean`) reduces the
  list structure and must never zeta through the blobs' `let`-chains
  (kernel recursion depth; the blobs stay opaque to the model).
  Verification fixtures: `nat_land_cone`/`nat_log2_cone` (e2e) are
  *pure-cone* slices — the op's dependency closure plus only the
  guard-required ground ops, with `funext`-et-al positively absent —
  accepted end to end.  Diagnosis unchanged:
  `scripts/DumpNatOpPinConsts.lean` + `scripts/
  diagnose_natop_prefix.py` (the op self-ref stays a false positive).
  Rebuild caveat: Lake tracks neither the `include_str` json edge nor
  the certs module; `touch` does nothing (content-hash traces) —
  delete the `PinGen*`/`NatOpPins*` build artifacts to force
  regeneration.
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
attempted and deferred (see "Inference re-checks" above) and finally
landed as an off-by-default operating mode in task #134, once both
routes to skipping the re-check *with a proof* had been closed — the
static guard by measurement (task #124) and the metatheorem by
refutation (`spike/inferonly-metatheory`); see "The infer-only mode:
SETLEC_INFER_ONLY (task #134)".  The early
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
binder defeq (documented deviation, benign for well-typed input —
**relaxed to zero-ness agreement 2026-08-24**, see "the binder model"
above; full removal still needs sort-coherence metatheory).
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

### `PSigma'` is deliberately eta-inert (2026-08-25, task #61)

The inertness above was carried as an open finding; it is **closed as
a non-bug**, on two independent grounds.  Both were established
against the references and against real streams; the regression guard
is `tests/e2e/psigma_rec_eta.ndjson` (source
`tests/e2e/src/psigma_rec_eta.lean`, a *raw* fixture).

1. **The rescue is unobservable for `PSigma'`: its recursor is
   Prop-eliminating only.**  `PSigma'`'s result sort is `max u v`,
   which may be zero, so Lean's kernel derives a *small* eliminator —
   `motive : PSigma' α β → Sort 0`, two level parameters (the pinned
   `psigmaRecA`; confirmed against the preprocessed Init export).
   Everything the rescue could ever produce is therefore a **proof**
   of `motive (PSigma'.mk α β t.1 t.2)`, compared against a proof of
   `motive t`; those two propositions are identified by the
   *defeq-side* pair eta (`pairEtaCert`), and `proofIrrel` then
   identifies the terms.  The reduct can never enter a type — so
   wherever the official kernel reduces through
   `to_cnstr_when_structure` here, we reach the same verdict by proof
   irrelevance.  (The fixture pins exactly this agreement: official
   Lean 4.29.1 accepts it through the rescue, setlec accepts it
   through proof irrelevance, both exit 0.)
2. **No preprocessed stream even applies `PSigma'.rec`.**  The
   preprocessor splices only the inductive and its constructor, and
   derives `PSigma'.fst`/`.snd` (bodies: primitive `.proj`) and the
   large `PSigma'.rec'` (`fun … t => minor t.1 t.2`) as *ordinary
   definitions* — `PSigma'.rec` itself is never applied.  Measured on
   the whole preprocessed Init export (`_tmp/init-exports/
   init-full-pre2.ndjson`, 335 MB): `PSigma'.rec` occurs exactly once,
   inside its own inductive block record — zero `const` nodes; `rec'`
   has 15, `fst` 14.  Nor can a `.lean` source reach it: `PSigma'`
   cannot be written with Lean's `inductive` command (the surface
   checker refuses a result sort that may be `Prop`), and a
   differently-shaped `PSigma'` fails pin matching and is rejected as
   a reserved basis name.  The fixture therefore kernel-adds both the
   block (exactly as the preprocessor splices it) and the theorem.

**NOTE — queued rider, post-stage-6 (task #100 owns `Core.lean`).**
The eta branch of `majorToCtor` still gates on the *static*
`piResultIsProp cvT.type = false` rather than the official
instantiated `is_never_zero`.  For `PSigma'` the static test **passes
at every level assignment** (`max u v` is not syntactically `Prop`),
so the branch is entered even at `PSigma'.{0,0}`, where the official
rescue positively refuses — today that is masked *only* by the
certificate failing on the reserved-name gate.  Any change that lets
the reserved branch fire must therefore land together with the
one-line tightening to `piResultNeverZero cvT.levelParams ust
cvT.type` (already used by the `PUnit` 0-field fallback, and the
official `is_never_zero`); at a `Prop` instantiation the model's
`sigmaSet` collapses at `w = 0`, which is exactly the case the
official gate excludes.  Mirror it in `majorToCtorI`/`majorToCtorNC`.

**Fix shape, if the rescue is ever wanted here (recorded, not
implemented).**  No name-keyed special case: the environment already
distinguishes the two projection storages, so dispatch on the stored
entry kind.  Where `env.find? (projFnName T j)` is a **native
`.projInfo`** entry (the pinned pair's `pairFstA`/`pairSndA`),
fabricate `Expr.proj T j major` — literally the official
`expand_eta_struct`'s `mk_proj`, and the spelling `pairEtaCert`
already consumes — instead of the projection-function constant that
`etaFabArgs` builds for modeled structures (whose `structEtaProjCerts`
requires a `.recInfo` projection function).  Model side: the eta fact
comes from `EnvModel`'s `ProjOk` clause (`sfst`/`ssnd`) rather than
the `_model` value bridge, i.e. `EtaFamilyStored` gains a
native-entry disjunct instead of dropping its non-reserved conjunct.

Reference points for the comparison (v4.29.1
`src/kernel/inductive.cpp`): `is_structure_like` is purely shape-based
(one constructor, no indices, non-recursive — no eta flag, no name
list), `expand_eta_struct` fabricates `mk_proj(I, i, e)` per field,
and the caller's guard is `whnf (inferType eType) = .sort u` with
`u.isNeverZero` (lean4lean `Inductive/Reduce.lean:53-65`, used
unconditionally at line 94; nanoda `tc.rs:1015-1034`, refusing
`may_be_prop`; the C++ chain is `type_checker.cpp` `reduce_recursor` →
`inductive_reduce_rec`).

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
(documented at `defeqBody`'s ∀/λ clauses; **shrunk 2026-08-24**): the
official kernel compares no binder annotations in `isDefEq`; ours compares
**one bit** — *zero-ness agreement* of the two codomain-sort annotations,
the only thing the interpretation reads (`SetTheory.pi`/`lam` consume
their level solely through the `v = 0` test — `pi_level_indifferent`,
`Setlec/SetTheory/Derive/Pi.lean`).  The kernel check is the weakest
syntactic condition the soundness proof supports: both annotations
provably nonzero (`Level.isNonZero`, sound under every valuation) passes
outright; otherwise it falls back to full level equivalence, whose
per-valuation eval-equality gives the zero-agreement — accepting "both
*not provably* nonzero" instead would be unsound (`param u` vs `zero`
disagree under `u ↦ 1`).  `defeq_claims` consumes the agreement via
`pi_congr_zero_agree`/`lam_congr_zero_agree`.  The residual one-bit
comparison is verdict-neutral on truthfully annotated input (there the
codomain sorts of defeq binders are eval-equal, so old and new forms both
pass — probes byte-identical); dropping it entirely needs sort-coherence
metatheory we don't have yet; costs completeness/performance only.

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
blocks *up to binder names, binder annotations, and positional
level-parameter renaming* (`ConstantInfo.canon`): Lean's exports use
auto-bound universe names (`Eq.{u_1}`, `Eq.rec.{u, u_1}`) and hygienic
binder names, both semantically irrelevant, and `BinderInfo` is
display data no typing rule reads (task #142); the checker installs
the pinned (annotated) declarations.

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
  prefix fits under the major — `rulePrefix ≤ majorIdx`; index
  premises between the prefix and the major are supported since task
  #105 — the major domain is a constant-headed application of exactly
  `cnP + (majorIdx − rulePrefix)` arguments that splits into the
  parameter instantiations followed by *the index variables in
  order*; the instantiations are stored **lowered into the
  rule-prefix context** (`Expr.lowerBVars`, with the
  `Expr.liftLooseBVars` roundtrip certifying that no index variable
  occurs in them) and pass the syntactic well-formedness guards
  recorded in `EnvWF`), `checkIotaThmN` re-runs the `checkIotaThm`
  pin with the constructor at the stored `lvls` applied to the stored
  `pins` opened at the statement's prefix variables
  (`Expr.instSpine`) in place of the leading telescope variables, and
  the constructor-telescope walks at the `lvls`-instantiated type —
  the statement's index arguments flow through exactly as on the
  plain path (pinned `defEq` against the constructor residual's
  canonical tuple).  Two extra certificates back the soundness of the
  indexed shape: the raw constructor residual's head must be a
  *constant* (the family former — both residual walks then decompose
  argument-wise; a variable head could be captured by a pin), and the
  publicly instantiated pins must be *fixed points of the annotation
  pass* (`checkAnnotList`) — their annotation truthfulness at the
  canonical frame is no longer derivable from the recursor-type walk
  once index binders separate the prefix from the major domain, so it
  is validated once at insertion (`annotateCore_sound` consumes it).
  A certifiable shape whose theorem then fails the pin declines
  positively at install.
* `.inert` — everything else (no theorem, no certifiable shape).
  `iotaRec`
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
fire-time *leading*-argument spine — the stored pins live in the
rule-prefix context, so `.nested` instantiates them at
`args.take rulePrefix` (`.nested`; `Expr.instSpine`, the kernel
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

**Nested major pinned up to binder names (2026-08-24, Mathlib
frontier).**  `checkIotaThmN`'s canonical-major pin compares with
`Expr.eqUpToNames`, not `==`: unlike the plain major, whose arguments
are all opened variables, the stored pins can contain *binders*
(dependent nested occurrences — `Std.DTreeMap.Internal.Impl α
(fun _ => Lean.PrefixTreeNode α β cmp)`), and by the recorded owner
ruling ("member types match up to display-only binder names",
2026-08-21) a syntactic contract cannot hold at the binder-name level
— export arenas intern by name-insensitive expression equality, so
the theorem's pin spelling can drift from the recursor type's in
binder names only.  The full preprocessed Mathlib stream (301k decls)
declined at declaration 29,661 (`Lean.PrefixTreeNode.rec_3`, "iota
statement major mismatch") on exactly this: the public recursor
type's pin lambda binder is one hygienic name, the model theorem's
another.  A whole-stream census (6,887 inductive blocks, 11,347
recursor rules: 11,160 plain, 182 nested-exact) found exactly 5
name-only major mismatches in 2 blocks (`Lean.PrefixTreeNode.rec_3`,
`Lean.Json.rec_4/rec_5` — both nest dependently through tree maps),
zero mismatches beyond names, and zero indexed nested-aux rules.
The former indexed `.inert` limitation was retired by task #105 (see
the firing-modes entry above): `indexed_nested_aux.ndjson` (`TV`
nesting through an indexed `Vec`; `TV.rec_1` has
`majorIdx = rulePrefix + 1`) is accepted end to end.  Soundness
un-specializes `modeled_bottom_nested`/`ctor_pkg_nested` back to the
plain path's index handling: the canonical body's index tuple is the
constructor residual's (`ruleLhsAux` already carried it), the
statement's index-argument values are identified with the public
residual's through the kernel's index `defEq` pins
(`interp_instSeq_frames` across the two constructor walks, which
share the pin values), the pins' annotation truthfulness comes from
the `checkAnnotList` certificate instead of the major-domain
residual, and `nested_fire_premise` reads the fire-time comparand
values off the *prefix* of the instantiated major-domain spine
(`instSeq_liftLooseBVars_prefix`: a full-spine instantiation over a
lifted prefix-context pin only consumes the prefix).
Soundness rides the existing erasure bridge: the `NestedChecked` kit
records the major fact as `Expr.ErasedEq` (via
`ErasedEq.of_eqUpToNames`), and `modeled_bottom_nested` consumes it
through `interp_erasedEq`/`AnnotOk.erasedEq` instead of rewriting.
Regression fixture: `nested_pin_names.ndjson` (a dependent-pin nested
block whose iota-theorem majors carry perturbed pin binder names,
accepted; the firing is forced by a `rfl` on a concrete major).
With the pin relaxed (and the driver fixes merged) the full Mathlib
stream moves from declaration 29,661 (9.8 %) to **50,769 (16.9 %)**:
the new frontier is `Nat.log2`, "unsupported Nat.div/mod spelling
(pin ground constants absent)" — the Nat-ops certified-fast-path pin
allowlists (`scripts/natop_prefix.json`) were extracted from Init
streams and do not cover the Mathlib stream's ordering/spelling;
fixed by regenerating the allowlists over the Mathlib streams too
(see "Prefix allowlists vs. stream order" in the pin-ops section).

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

> **Superseded by task #147**: the flag and `--yolo` are retired.  The
> cert-skipping engine (`CoreNC`/`CheckerNC`) is now the `--no-model`
> lane, under a checking-mode front door it did not have — so the
> front-door caveats below (and the class-B escapes) no longer apply
> to any shipping mode.  The tax numbers remain the historical record.

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
limit; verdicts as expected in both modes — arena 90/92, e2e 48/48,
probe exit 0 / 3653 accepted; on the sense of "as expected" see the
verdict-agreement paragraph below):

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

**Amendment (task #134, 2026-08-27): this figure overstates the tax.**
`inferSpineNC` drops the per-argument application check at *every*
invocation, the driver's front door included — but the front-door
check is one the reference kernels perform (`check(e)` at
`infer_only = false`), so its share is engineering gap, not
certification.  Measured against the infer-only mode, which keeps the
front door and drops only the internal re-checks, the split is roughly
half and half; the honest decomposition is in "The infer-only mode:
SETLEC_INFER_ONLY (task #134)" below.  Everything else in this section
stands, including the site list — only the label on the front-door
share of the `inferSpine` bullet changes.

**Verdict agreement, stated exactly (task #139, 2026-08-27).**  Older
paragraphs in this document say the two modes' verdicts are
"identical".  That was never quite the contract and is not what the
suites check.  The accurate statement:

> The certified and the `SETLEC_NO_PROOF_CERTS=1` stacks agree on every
> verdict **except one acknowledged class-B divergence**: `inferSpineNC`
> drops the per-argument application check *everywhere*, the front door
> included (see the task-#134 amendment above), so a stream whose only
> defect is **inside an application argument** may be **accepted** under
> the flag and rejected — or declined — by the certified stack.  Every
> other flip is a bug in an NC twin.

**The class is the argument position, not the type mismatch (fuzz
campaign 2026-08-27, finding F1).**  The paragraph above used to read
"whose only defect is an application type mismatch", which understates
the mode: `inferSpineNC` does not merely skip the argument-vs-domain
`defeq`, it skips the argument's `infer` altogether.  Everything that
`infer` would have detected about a term appearing *only* in argument
position is therefore invisible under the flag — a wrong
universe-argument count on a constant, an application of a
non-function, a binder whose domain is not a sort, an unsupported
projection shape, as well as the type mismatch itself.  The certified
side of such a pair is correspondingly not always a reject: an
unsupported feature reachable only from an argument is a positive
decline (2) certified and an accept (0) under yolo.

The divergence is now **exercised**, not merely documented.  The
2026-08-27 audit found no *pre-existing* fixture diverging — the full
arena suite (138 expectation lines) and the then-67 e2e lines gave
identical exit codes in both modes — so the campaign built three
witnesses and landed them as e2e fixtures with `tests/yolo-expected.txt`
overrides:

| fixture | certified | yolo | escaping defect |
|---|---|---|---|
| `yolo_arg_escape.ndjson` | 1 | **0** | application type mismatch |
| `yolo_arg_escape_univs.ndjson` | 1 | **0** | universe-argument count |
| `yolo_decline_vs_accept.ndjson` | 2 | **0** | unsupported projection shape |

The first is the sharpest statement of the mode's honesty limit:
`theorem everything : ∀ p : Prop, p := fun p => (fun h : p => h)
(Eq.refl Nat Nat.zero)`.  The redex's *result* type really is `p`, so
only the argument check can see that `rfl : 0 = 0` is not a proof of
`p` — and `--yolo` accepts the stream.  A measurement run's exit code
is a measurement artefact, never a verdict; the certified stack is the
only thing that pronounces.  Note the contrast with the infer-only
mode, which keeps the driver's front door and therefore rejects
(resp. declines) all three exactly as the certified stack does.  The
audit and the sweep that keeps the statement true are in "The yolo
sweep" below.

## The infer-only mode: SETLEC_INFER_ONLY (task #134)

> **Superseded by task #147** (see "The three-mode setting"): the
> flag and its environment variable are retired — the infer-only
> internal discipline described below lives on as one third of
> `--no-model`, and the `coreKnotF` front-door pattern as
> `coreKnotFNC`.  The measurements and the assurance argument remain
> the record of why the discipline is shaped this way.

`SETLEC_INFER_ONLY=1` (command-line alias: `--infer-only`) is a
**supported operating mode**, off by default.  It is the reference
kernels' `infer_only` discipline: a declaration is checked *once*, at
the top, by the driver's front door; the inferences that reduction and
definitional equality perform on their own intermediate terms
re-derive types **without re-checking application arguments**.

**Structure** (`Setlec/Kernel/CoreIO.lean`,
`Setlec/Kernel/CheckerIO.lean`; the flag never reaches the kernel as
data — `Main` selects a driver, exactly as for the measurement mode).
Two knots, which is what "at internal invocations only" means:

* `coreKnotIO` — the **infer-only** knot, what every internal call
  sees.  Its `infer` is `inferBodyIO`, which differs from `inferBodyI`
  in exactly one clause: the application clause walks the Π-telescope
  with `inferSpineIO` instead of `inferSpineI`, i.e. without the
  per-argument `infer` + `defeq`.  `whnfCore`, `whnf`, `defeq`,
  `annotate` and every certificate they reach — `iotaCertsI`, the beta
  certificates of `whnfAppI`/`betaPeelI`, `projCertI`,
  `projParamCertI`, the structure-eta and unit-like certificates — are
  the certified bodies, unchanged and still running.
* `coreKnotF` — the **checking-mode** knot, the only one the driver
  holds.  `infer` is the certified `inferBodyI` tied to *itself*, so
  the per-argument re-check runs and checking mode propagates down the
  declaration's own term (the official kernel threads its `infer_only`
  argument through `infer_app`/`infer_lambda`/`infer_let` the same
  way); `annotate` likewise.  `whnfCore`/`whnf`/`defeq` are
  `coreKnotIO`'s, so the inferences *inside* reduction are infer-only.

The official kernel keeps one inference cache per flag value
(`m_st->m_infer_type[2]`); `coreKnotF` keeps its own, `IState.inferFC`,
so an infer-only result can never be served to a checking-mode query.
The share runs one way only — `memoEIO` reads `inferFC` before
`inferC`, which is sound because the two bodies return the same type
wherever both succeed — and `inferFC` is dropped wherever the other
index-carrying memos are (per declaration, and at every snapshot close
that truncates tier two).

**Scope.**  Only the def/thm/opaque value pipeline runs on this stack.
Install-only kinds (axioms, quotient/basis blocks, inductive blocks)
and the two rare pinned-certificate branches (structural Nat
operations, reduce pins) fall through to the shared, fully certified
`checkDeclSPPlain`; a declaration therefore runs on exactly one stack,
and the per-declaration flush keeps neither mode's memo from reaching
the other.  Three checks that the reference kernels *do* skip at
`infer_only` are **kept** here — the λ/∀ domain-sort checks, the `letE`
value conformance, and `projParamCertI` — because this mode narrows
exactly one site and a deviation in the strict direction needs no
argument.  The mode refuses to combine with `--yolo` or with the split
driver (`--install-only`/`--check-range`): either combination would
make a verdict's provenance unreadable.

### The assurance model — say it in full

* **Flag off (default).**  The fully verified checker.  Every
  consistency statement (`Setlec/Model/ConsistencyP.lean` and friends)
  is about this path and applies to it unchanged; the flag-off binary
  is byte-identical in behaviour to the pre-flag one, in the certified
  *and* the `SETLEC_NO_PROOF_CERTS` mode (the landing gate: stdout,
  stderr and exit status compared against a binary built from the
  pre-change tree, on init-prelude, plain and progress modes).
* **Flag on.**  Official-kernel `infer_only` discipline.  The verified
  claims cover flag-off; the flag-on argument is **reference-kernel
  parity, stated as parity and not smuggled in as verification**.  This
  is the same two-conditionality shape the `directStructsEnabled`
  hypothesis already has (`Setlec/TTVerify/DESIGN.md` §4): a named,
  visible configuration, not a hidden side condition.

The temptation to say more has already been tried and refuted.  The
metatheorem that would license the mode outright —
`Typable e → InferOnly e t → HasType e t` — is **false**, mechanized
as `InferOnlyRefuted` on the (never-merged) `spike/inferonly-metatheory`
branch, with a closed witness and the accompanying refutations of
level-guarded Π-domain injectivity and of unique typing.  It is false
for the reference kernels in exactly the same way; they do not rest on
it either.  What the mode rests on is an operational invariant — every
term whose type is re-derived internally is a reduct of a term the
front door checked — which is an argument about the *engine*, not a
theorem about the *terms*.  The static-guard route that would have
made the skip verifiable was separately refuted by measurement (task
#124, "The guard-capture census" below: the guard captures ~0 % of the
cost).  Both refutations are why the mode ships as a mode.

### It is not `SETLEC_NO_PROOF_CERTS`

|  | `SETLEC_NO_PROOF_CERTS=1` / `--yolo` | `SETLEC_INFER_ONLY=1` / `--infer-only` |
| --- | --- | --- |
| what it is | unverified **measurement** mode (task #76) | supported **operating** mode (task #134) |
| what it skips | whole certificate families: iota telescope certifications, beta re-checks, eta/unit-like certifications, *and* the application re-check everywhere | exactly one re-check — the per-argument application check — and only at internal invocations |
| the front door | also skips the argument checks there, so it checks *less* than the reference kernels do | full checking mode: the declaration's own applications are all checked, as `check(e)` does |
| purpose | price the verification tax; never to judge a stream | run real streams faster, at reference-kernel discipline |

The two are mutually exclusive on the command line for that reason: a
reader must be able to tell from the invocation which claim a verdict
carries.

### Measured

init-prelude probe (`_tmp/perfcmp/init-prelude.preprocessed.ndjson`,
`--pre`, `perf stat` instructions, medians of 3; all three modes accept
3653 declarations):

| configuration | instructions | wall |
| --- | --- | --- |
| default (certified) | 33.84 G | 3.01 s |
| `SETLEC_INFER_ONLY=1` | 23.71 G | 2.14 s |
| *diagnostic*: front door infer-only too | 14.89 G | — |
| `SETLEC_NO_PROOF_CERTS=1` | 11.34 G | 0.96 s |

The diagnostic row is one edit away at any time: point `coreKnotF`'s
`infer` at `inferBodyIO` instead of `inferBodyI`, and the front door
stops checking arguments too.  It is *not* a mode — it checks less
than the reference kernels do — but it is what isolates the front
door's share below.

`_tmp/std-time-cone/pre2.ndjson` (4215-declaration `Std.Time` cone, a
scratch build with `checkFuel` at 200 000 — the stream needs it; all
modes accept 6390 declarations):

| configuration | wall |
| --- | --- |
| default (certified) | 3 m 33 s |
| `SETLEC_INFER_ONLY=1` | 1 m 51 s |
| *diagnostic*: front door infer-only too | 5.6 s |
| `SETLEC_NO_PROOF_CERTS=1` | 4.9 s |

**Verdicts do not move.**  Every arena fixture (92 good, all bad) and
every e2e fixture was run in both modes at the landing commit: 90/92
accepted and 67/67 as expected with the flag on, and **not one
verdict differs** — no good stream moved, and no bad-input fixture
flipped from reject to accept.  That was not a foregone conclusion:
trusting subterms at internal re-derivations *may* accept a bad input
the certified mode rejects, and such a flip would be the mode's nature
rather than a bug.  As of this measurement the enumeration of flips is
empty; `tests/arena.sh --infer-only` is the opt-in sweep that would
surface a future one, and any flip it finds belongs in this paragraph.
A *good* stream changing verdict would be a real bug instead.

### The finding: half of the "verification tax" is the front door's

The diagnostic row above is the point.  Masking the argument re-check
*everywhere* — which is what `--yolo` does, and what task #124's census
measured — collapses init-prelude to 14.89 G and `Std.Time` to 5.6 s;
masking it only at internal invocations, keeping the front door as the
reference kernels have it, stops at 23.71 G and 1 m 51 s.  So the
application re-check decomposes into two halves that are *not the same
kind of thing*:

* **internal re-checks** — init-prelude 10.1 G (30 % of the run),
  `Std.Time` ~102 s (48 %).  Genuine verification tax: the reference
  kernels do not perform these, and this mode is exactly their removal.
* **front-door checks** — init-prelude 8.8 G (26 %), `Std.Time` ~105 s
  (49 %).  **Not a tax at all.**  `check(v)` in the official kernel
  runs `is_def_eq(a_type, d_type)` on every application argument of the
  declaration's value, and lean4lean's `check` does the same; the
  official kernel merely does it in well under a second.  This share is
  engineering gap, not certification.
* the certificate families themselves are the remainder: init-prelude
  3.6 G (11 %), `Std.Time` ~0.7 s — consistent with the ~4 s of 292 s
  the census attributed to them.

**Consequence for the numbers already recorded here.**  The task-#76
measurement (`SETLEC_NO_PROOF_CERTS`, "Verification tax: 53.7 G ≈ 26 %")
and the `Std.Time` line elsewhere in this document ("`--yolo` … 5.4 s
versus 3 m 51 s: a ~42× certified-mode tax") **overstate the tax**,
because `inferSpineNC` skips the front-door argument checks too.  The
task-#76 site list calls that residue proof-only, which is true of
internal invocations and false of the front door.  The honest split is
the one above, and the certified-mode tax on `Std.Time` is ~1.9×, not
~42×; the rest of that ratio is the engine's cost for checks the
reference kernels also run.  Nothing about the certified path changes —
only what the `--yolo` delta may be called.

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

### The master switch, and why it defaults on (2026-08-26, task #119)

> **Superseded by task #148 T0b (2026-08-27)**: the switch now ships
> `false`, the `<on>|<off>` expectation pairs collapsed to single codes
> and `tests/build-direct-off.sh` / `tests/arena.sh --direct-off` are
> gone.  The section below is the record of the on-by-default era and
> of the measurement the flip re-used; see "Direct structs off by
> default" at the end of this file for what changed and why.

`Setlec.directStructsEnabled` (`Setlec/Kernel/Direct.lean`) gates the
whole route in one place: `directParts?` and its indexed twin
`directPartsF?` conjoin it into their recognition test, so the pure
knot, the shared knot and the cert-skipping knot switch together and
every bridge between them is untouched — the switch cost **no proof
churn at all**, which is the point of gating recognition rather than
dispatch.

Switching it off is a plain **fall-through, never a decline**: a block
that would have been recognised simply takes the ordinary modeled
clause, and if it carries no `_model` companions it declines there, for
the modeled path's own reason and with the modeled path's own message.
No error or decline message is invented for the switch itself.  This is
what makes the off configuration meaningful — it is not "the direct
class is unsupported", it is "the modeled path, always".

The switch exists for the TTVerify bridge (task #119), whose denotation
reads a stored inductive through its checked `_model` artifacts and so
has nothing to read for a directly installed structure; the bridge's
theorems are stated for the off configuration.

**It defaults on, because off is measurably not verdict-neutral**
(measured 2026-08-26, arena + e2e + split + both init-prelude modes).
Five expectations move, all of them losses:

| fixture | on | off |
|---|---|---|
| `tests/e2e/direct_struct_raw.ndjson` (`raw` line) | 0 | 2 |
| `tests/e2e/direct_struct_raw.ndjson` (`pre` line) | 0 | 2 |
| `bad/tutorial/133_dup_ctor_def.ndjson` | 1 | 2 |
| `bad/tutorial/134_dup_rec_def.ndjson` | 1 | 2 |
| `bad/tutorial/137_dup_ctor_rec.ndjson` | 1 | 2 |

These are exactly the four expectation flips item 7 above bought,
read backwards.  Everything else is untouched: arena 90/92, the other
65 e2e lines, split 11/11, and both init-prelude probes still accept
3653 declarations — with the switch on the recognition test is
`true && …`, i.e. definitionally what it was before, so the shipped
behaviour is unchanged by construction.

So the configuration the bridge reasons about is **not** the shipped
one, and that gap is the bridge's to state plainly rather than the
switch's to paper over.

**Both configurations are tested (2026-08-26).**  The five moving
expectations are pinned, not merely written down: an expectation in
`tests/arena-expected.txt` / `tests/e2e-expected.txt` is either a single
exit code, as for every other fixture, or a **pair** `<on>|<off>`, and
`tests/arena.sh --direct-off` runs the whole suite (arena, e2e, split
driver) against a switched-off binary, applying the right-hand codes.
The common case does not grow — 5 of 205 expectation lines carry a pair
— and the default invocation is untouched in command, output shape and
cost: the off run is opt-in and builds nothing unless asked.

Since the switch is a compile-time constant, the off run needs a second
binary; `tests/build-direct-off.sh` produces one **without editing the
source tree**.  It mirrors the tracked sources (minus `tests/`) into
`_tmp/direct-off/` (gitignored), rewrites the one flag line there,
seeds `.lake` from the main tree's build once and runs `lake build
setlec` — 74 jobs, ~12 s warm, i.e. only `Direct.lean`'s cone.  It
insists on finding exactly one pristine `:= true` line, so a reworded
or already-flipped definition fails loudly instead of quietly testing
the shipped configuration twice.  Result: arena 90/92, e2e 67/67, split
11/11 in *both* configurations, against their respective expectations.

**What was checked, including what did not move.**  The five flips were
re-measured independently of the table above, by running both binaries
on each fixture rather than trusting the pinned codes; and the two
plausible neighbours were checked *and found unmoved*, which is the
half of the evidence a list of changes cannot supply:

| fixture | on | off | |
|---|---|---|---|
| `direct_struct_raw` (`raw`) | 0 | 2 | moves |
| `direct_struct_raw` (`pre`) | 0 | 2 | moves |
| `bad/tutorial/133_dup_ctor_def` | 1 | 2 | moves |
| `bad/tutorial/134_dup_rec_def` | 1 | 2 | moves |
| `bad/tutorial/137_dup_ctor_rec` | 1 | 2 | moves |
| `bad/tutorial/131_dup_defs` | 1 | 1 | **unmoved** |
| `bad/tutorial/136_dup_rec_def2` | 2 | 2 | **unmoved** |

Beyond the spot checks, the off suite passing with exactly five paired
lines *is* the completeness argument: any sixth fixture that moved
would have failed its single-code expectation, across all 137 arena
fixtures, 67 e2e lines and 11 split-driver cases.

**What is not covered in either configuration**: the init-prelude and
init-full streams.  "Both configurations pass" means the three suites
`tests/arena.sh` runs and nothing wider — the long streams were not
re-run for the off binary, and the on binary needs no re-run because it
is bit-identical to master's.  The claim above that both init-prelude
probes still accept 3653 declarations off is the switch author's
measurement, not the harness's; nothing runs it on a schedule.

The five moves are expected, not regressions, and split into two kinds.
The two `direct_struct_raw` lines explicitly test the direct route and
deliberately bypass generating a `_model` fallback, so of course they
decline when the route is off — the fixture's subject is gone.  The
three duplicate-declaration fixtures only change *reject → decline*,
which is the harmless direction in exit-code terms: 1 (invalid input
proof) becoming 2 (unsupported feature detected) never accepts anything
it should not, so what is lost is rejection sharpness, not soundness.

*No command-line flag.*  Making the switch settable at run time means
threading a `Bool` from `main` to `directParts?`, and the two routes
there are both expensive: through `CheckerOps` reaches only the pure
`checkDecl`, while the shared and cert-skipping drivers reach
`directPartsF?` through `FEnv` (660 `mkFEnv` references) or `IState`
plus a matching hypothesis on every `Bridge*` correspondence.  That is
a large, bridge-perturbing change to expose a switch whose only current
consumer is a proof; the compile-time constant is the whole feature
until something needs more.

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
## Mathlib-scoping driver fixes: wfB stack, diagnostic-pass linearity, --pre (2026-08-24)

Scoping the full Mathlib stream (727 k declaration records, ~5.8 GB
preprocessed) surfaced three driver-level defects; none touches a
verified statement.

**1. Store validation overflowed the stack at end of parse.**  The
full stream crashed "Stack overflow detected" (exit 134) right after
parsing at any default-sized stack; `LEAN_STACK_SIZE_KB=16777216`
(16 GiB) was needed to get past it.  Site (gdb on a synthetic
~150 k-node `spine` stream at `LEAN_STACK_SIZE_KB=8192`): 66 520
recursive frames of `EStore.wfBNodes` under `wfB` — the downward
shape `wfBNodes st (k+1) = wfBNodes st k && per-node k` recurses
*before* the conjunction, one C frame (~126 bytes) per **arena
node**; at Mathlib's arena size that is on the order of 10 GB of
stack.  Fix: the per-node check is factored out (`wfBNode1`, likewise
`wfBLNode1`/`wfBNNode1`) and folded by a tail-recursive upward walk
(`wfBNodesGo st i (m+1) = wfBNode1 st i && wfBNodesGo st (i+1) m` —
with `&&` the recursive call is in tail position, so the compiled
loop is constant-stack; verified by rerunning the repro at reduced
stack, and the full Mathlib parse passes `wfB` into checking at the
default stack).  `Setlec/Verify/ParseP.lean` gains one generic
extraction lemma (`wfBGo_one`); the `wfB*_facts` statements and
`wfB_wf` are unchanged.  Remaining deep recursions are proportional
to *expression depth* or *definitional-chain length* (inherent
checker walks; the scale shapes trip them only at artificially tiny
stacks), never to arena size.

**2. The RC-2 holder behind "non-progress is >20× slower" was the
diagnostic second pass, not the verified fold.**  A linearity audit
(throwaway `dbgTraceIfShared` probes at `EStore.intern`/`internL` and
`FEnv.push`, diag/linearity pattern) on an 800 k-line Mathlib prefix
(1663 declarations, then a decline): progress mode 0 arena copies;
plain mode 1259 `nodes@intern` + 1259 `cons@intern` + 623
`lnodes@internL` copies — but on a stream that *accepts*, plain mode
also shows 0.  `checkDeclsSP`'s `List.foldlM` is compiled as a
specialized tail-recursive loop threading the state uniquely
(confirmed in the generated C), so the verified fold was never the
holder.  The copies all came from `checkMain`'s *diagnostic second
pass* (error branch only — and every current big Mathlib stream ends
in a decline): its `for d in decls2` loop's boxed state tuple kept
the re-parsed arena shared (RC 2) into every step, so each
declaration's first arena mutation copied the whole node/hash tables
— the `lean_copy_expand_array`/`lean_del_core` tower in the scoping
perf samples, and a copy cost that grows with the arena, which is why
small streams never showed it.  Fix: `diagLoop`, explicit recursion
with the accumulators as plain arguments (exactly the
`progressLoop`/`parseExportStream` pattern; that trio now covers
every driver loop).  Copies drop to 0.  `checkDeclsSP` itself is
untouched — `checkDeclsSP_sound` and both `no_proof_of_Empty`
statements *and proofs* unchanged.

**3. `--pre`: skip preprocessing on already-preprocessed input.**
Preprocessed streams still contain `inductive` records (modeled
blocks are stored opaque), so `needsPreprocess` re-detects them and
re-spawns lean-inductive-models — ~12 wasted minutes on full Mathlib.
`--pre` is an explicit user assertion that the input is already
lean-inductive-models output: `checkMain` skips the detection scan
and the spawn entirely.  Deliberately *not* content sniffing (no
`_model`-name detection — barred by the names-not-special ruling);
the upstream already-preprocessed marker remains task #91.  `--help`
added; the e2e runner gains a `pre` mode (`std_axioms` under `--pre`
must *decline* at the raw `Iff` block — the verdict flip from its
plain line proves the spawn really was skipped; `direct_struct_raw`
under `--pre` direct-installs to the same verdict as its `raw` line).

**Measured** (prefix-log2 slice of Mathlib, 50 783 declaration
records, 283 MB preprocessed, `--pre`, same machine; both verdicts
exit 2 at the known `Lean.PrefixTreeNode.rec_3` iota-statement
frontier):

* pre-fix binary (master 6e29d67), plain mode: killed unfinished at
  the 40 min cap (scoping evidence: >1 h) — the second pass's
  per-declaration whole-arena copy strike
* post-fix, plain mode: **3 m 29 s** wall (205 s user, 4.1 GB RSS),
  including the diagnostic second pass, which now also *locates* the
  failing record ("[at inductive Lean.PrefixTreeNode]")
* post-fix, progress mode: 1 m 56 s (114 s user) — plain ≈ 1.9×
  progress, exactly the two passes an error stream costs
* full Mathlib (5.8 GB, 727 k records) at the **default stack**,
  `--pre`, progress: parses, passes `wfB`, and checks 29 660
  declarations to the known `Lean.PrefixTreeNode.rec_3` frontier
  decline in ~11 min (previously: stack overflow at end of parse;
  22 min with the 16 GiB-stack workaround plus ~7.5 min
  re-preprocessing)

### Raw storage stage 4a: `norm`, and the twin relation (2026-08-24, task #100)

Storage flips to the **parsed trees, untouched** — install stays pure
parse + intern (orchestrator ruling, option (iii) on the stage-3
finding).  The annotation pass is not skeleton-preserving, so the twin
relation generalizes from "erase the annotations" to

  `erase(ê) = norm(e)`

with `norm` (`Setlec/Model/Norm.lean`) a **pure proof-side**
normalization performing exactly the annotation pass's two
skeleton-changing clauses and nothing else:

* **zeta** — `annotateBody`'s `letE` clause annotates the body as its
  zeta reduct (value transparency; the `letE`-preserving variant is
  recorded as rejected in the task-#79 section).  `norm`'s `letE`
  clause is that expansion, so `norm`'s output is let-free and the
  model machinery keeps working in its let-free regime while the
  kernel keeps its lazy zeta.
* **projection rewrite** — the `proj` clause either keeps the node
  (with the structure name normalized to the scrutinee type's head) or
  rewrites it away (`annotateProjElim`).  This one is *not* a function
  of the expression — it reads the projection table and the whnf of an
  inferred type — so it enters `norm` as an **oracle**, exactly as
  binder annotations enter `decorate`.  Its agreement with the
  annotation pass is a hypothesis, discharged at the flip.

Fuel is the measure, as for `annotateCore` and for the same reason
(zeta expansion is not size-decreasing); every statement is at an
arbitrary fixed fuel, so no fuel bookkeeping leaks into the flip.

**The congruence layer, and what it buys.**  `norm_id` /
`norm_keep_id`: on a let-free tree whose projection nodes the oracle
keeps, `norm` is the identity — at *every* fuel.  That is the precise
form of "init-prelude-style streams are unaffected by the flip", and
with `Expr.TwinAt_keep` it collapses the twin relation to plain shallow
erasure on such streams.  `eraseCodS_norm`: `norm` commutes with the
shallow erasure (both leave `fvar` annotations alone, which is what
makes them commute on the nose), so the composite the raw model is
instantiated at is unambiguous.  `Expr.eraseCodS_instantiate1` extends
stage 3's shallow-erasure kit to arbitrary substitutions, which the
zeta clause needs.

**The value-transparency bridge is not new work.**  `interp_zeta_step`
and `AnnotOk_zeta_step` — one zeta step preserves the interpretation
and transports annotation truthfulness — are `interp_beta` and
`AnnotOk_beta`, the substitution lemmas task #79 already built for the
`whnfCore` zeta case, packaged at the `letE` clause.  They are the
seam where the kernel's lazy zeta and `norm`'s eager expansion meet.

**The raw model's parameter is now a relation.**  `RawEnvModelE V Twin
env` takes `Twin : Env → Env → Prop`, because the end state needs a map
on *each* side.  Three instantiations, one per stage:
`fun a e => a = e` (transitional), `fun a e => a.eraseCod = e`
(stage 3), and `Env.TwinAt O f` = `fun a e => a.eraseCodS = Env.norm O f e`
(the end state, `RawEnvModelN`).  `norm` and `eraseCodS` are lifted
through `ConstantVal`/`RecRule`/`RecRuleFire`/`ProjEntry`/`ConstantInfo`
to environments alongside `Env.eraseCod`.

**Handoff — what stage 4 still needs.**

* (b) *storage flip*: the kernel stores parse output; the guards and
  defeq move to the memoized `codOf` / raw forms.  Nothing in the model
  layer blocks this; `natLitSupportedRaw`/`strLitSupportedRaw` (stage 1)
  are the raw guard forms, and `codOfI` (stage 2) is the memo.
* (c) *ghost-run bisimulation*: raw run ≡ ghost run on the **canonical**
  twin, decisions aligned via memoized `codOf` against stored cods.
  The spike's warning stands: claims over arbitrary truthful twins are
  FALSE — canonical twins only.  `decorate_eq` (stage 3) is what makes
  "canonical" a definition rather than a choice: the twin is the unique
  tree the memo reconstructs.
* (d) *instantiation*: `RawEnvModelN` exists; what remains is
  re-proving `extend_model_raw` &co. at `Env.TwinAt` instead of plain
  erasure.  The certificate transfers need `norm` congruences for
  `hasFvar`/`looseBVarsBounded`/`constsResolve` (the erasure ones are
  stage 1); `norm` preserves none of them unconditionally — zeta
  expansion duplicates the value — so these are per-predicate lemmas
  with the substitution facts, not one-liners.  That is the first thing
  to write.

#### Finding: `norm`'s zeta needs the *lifting* substitution (2026-08-24)

The stage-4a `norm` used `Expr.instantiate1` for its zeta clause, by
analogy with `annotateBody`.  That is wrong for `norm`, and the reason
is instructive: `annotate` **opens** each binder into an `fvar` before
descending, so by the time its `letE` clause fires the term is
`bvar`-closed and the let value has no loose `bvar`s — the regime
`instantiate1` requires (it inserts the replacement *unshifted* at every
cursor depth).  `norm` recurses under binders *structurally*, without
opening, so its let values are open terms and `instantiate1` captures.

The discriminating case is a `let` under a binder whose value mentions
that binder, used under a further binder:

  `∀ y, let x := y; ∀ z, x`   must give   `∀ y, ∀ z, y`

— `bvar 1` under the inner binder.  Plain `instantiate1` inserts the
value unshifted and yields `∀ y, ∀ z, z`.  It is now a regression test.

The fix needs no new machinery: `Expr.instantiate1Lift` already exists
for exactly this situation (its docstring in
`Setlec/Kernel/ExprOps.lean` calls out "let-values are open terms"), and
`instantiate1Lift_eq_instantiate1` says the two agree on `bvar`-closed
replacements — so `norm_letE_closed` recovers the kernel's own form in
the kernel's own regime, which is the equation the flip will use.
`Expr.eraseCodS_liftLooseBVars` and `Expr.eraseCodS_instantiate1Lift`
extend the shallow-erasure kit to match.

The general lesson for the rest of task #100: a proof-side pass that
mirrors a kernel pass **must state which binder discipline it is in**.
The kernel is always in the opened regime; a structural proof-side
mirror is not, and every substitution it performs has to be the lifting
one.

#### Stage 4d groundwork: the `norm` congruences (2026-08-24)

The three install-time certificates the `extend_*_raw` lemmas consume
now transfer through `norm`, which is what gates re-proving those
lemmas at `Env.TwinAt` instead of plain erasure:

* `Expr.norm_hasFvar` — `norm` opens no binder, so it introduces no
  free variables and `fvar`-freeness is genuinely preserved;
* `Expr.norm_looseBVarsBounded` — the bound survives zeta;
* `Expr.norm_constsResolve` — constant resolution survives zeta.

Unlike stage 1's *erasure* congruences these are not invariances:
`norm` duplicates the let value, so each rests on the substitution fact
for the **lifting** substitution, and each of those in turn needs a
lifting lemma underneath (`instantiate1Lift` shifts what it inserts).
The five supporting facts —
`looseBVarsBounded_liftLooseBVars`, `constsResolve_liftLooseBVars`,
`hasFvar_lift`, and then `hasFvar_instantiate1Lift`,
`looseBVarsBounded_instantiate1Lift`, `constsResolve_instantiate1Lift`
— are proved here rather than in `Setlec/Verify/*` because they are
about the *proof-side* pass; if the kernel ever needs them they should
move.

Each congruence carries an **oracle hypothesis**: the projection
rewrite emits a term built from the environment, so only the annotation
pass knows it is well-formed.  That hypothesis is the same shape as
`CodAgree`'s — discharged at the flip from what the annotation pass
established, not proved here.

The interesting shape of `looseBVarsBounded_instantiate1Lift` is that
the bound moves: substituting a `k`-bounded value for the binder at
cursor `j` turns a `(k+1+j)`-bounded body into a `(k+j)`-bounded one.
That is the statement zeta needs at *every* binder depth, and it is why
the plain `looseBVarsBounded_instantiate1_gen` (stated at cursor `k`
with a `bvar`-closed replacement) does not serve a structural pass.

#### Handoff: the storage flip (task #100 stage 4b), call site by call site

The flip is far more surgical than the model-side work suggested.  In
the parsed-index driver (`Setlec/Kernel/CheckerS.lean`) every install
follows one shape:

```
  let jty ← (coreKnotI fe checkFuel).annotate 0 cv.type   -- working index
  …post-annotate guards on jty…
  let tyE ← readbackEM jty                                -- what gets STORED
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)
```

and for values (`checkDefnValP`, `checkThmValP`, `checkOpaqueValP`)
likewise `let vE ← readbackEM jv` … `fe.push (.defnInfo cvA vE hint)`.

So **storage is exactly the `readbackEM` argument**: the flip is
`readbackEM jty → readbackEM cv.type` and `readbackEM jv →
readbackEM value` — read back the *parsed* index instead of the
annotated one.  The annotated index stays as the working index; the
checks, `opSIx`, the defeq against `jty`, and the post-annotate guards
(`allLevelParamsDefinedI`, `constsResolveFI` on `jty`) are all
unchanged, because they are about the tree that was *checked*, not the
tree that is *stored*.  Sites: `CheckerS.lean:1334` (types),
`:1355`/`:1379` (defn/thm values), `:1447` (the direct-structure path),
and the inductive/recursor/projection installs alongside them.

Two decisions the flip has to make, neither settled here:

1. **`recordIConst cvA.name cvA.type jty (some (vE, jv))`** — the
   interned environment pairs a stored `Expr` tag with an arena index,
   and its `ISOK.ienv` clause says the index denotes the tag.  After the
   flip the stored `Expr` is raw while the index is annotated, so either
   the tag becomes the raw tree and the clause becomes "denotes the
   twin's erasure-normalization", or the entry carries both.  The
   second is cheaper for the bisimulation and costs one field.
2. **Guard retargeting** — `natLitSupportedF`/`strLitSupportedF` read
   the stored environment, so after the flip they must become the raw
   forms (`natLitSupportedRaw`/`strLitSupportedRaw`, stage 1, with
   `natLitSupportedRaw_erase` already proving the annotated guard implies
   them).  Everything else that reads storage goes through `FEnv`, so
   the sweep is "what does `mkFEnv`'s consumer inspect".

Leave `st.wfB` (`CheckerS.lean:1499`, `Main.lean:181`,
`CheckerNC.lean:434`) exactly as it is — the valid-by-construction
subtype arena is task #103 and comes after #100 settles.
(Overtaken: #100 was backlogged and the #103 wiring landed against the
annotated-storage checker — `wfB` and these seams are gone, see "Task
#103 wiring landed" below.)

For (c), the ghost-run bisimulation: anchor on `decorate_eq`.  It makes
"canonical twin" a *definition* rather than a choice — the twin is the
unique tree the memo reconstructs — which is what the spike's warning
demands (claims quantified over arbitrary truthful twins are false).
The raw run and the ghost run share the arena and the memos; the
decisions to align are exactly the ones that read a binder annotation
(`inferType`'s λ/∀ clauses, `isDefEq`'s binder comparison), and each
reads `codOf` on the raw side against the stored `cod` on the ghost
side.

### Raw storage stage 4d: the install combinators at `Env.TwinAt` (2026-08-24, task #100)

`RawEnvModelE` was already parametric in the twin relation, so moving
from plain erasure to the end-state relation is a re-proof of the
install combinators and nothing else.  `Setlec/Model/RawEnvN.lean` is
that re-proof: `RawEnvModelE.extendN` / `extend_oneN` and
`extend_model_rawN` with its `_defn` / `_axiom` / `_thm` instances,
all at `Env.TwinAt O f` (`aenv.eraseCodS = Env.norm O f env`).

Two things had to be built underneath:

* the **shallow**-erasure invariances (`Expr.hasFvar_eraseCodS`,
  `looseBVarsBounded_eraseCodS`, `constsResolve_eraseCodS`).  These are
  stage 1's erasure invariances with the `fvar` clause replaced by
  `rfl` — `eraseCodS` does not descend into annotations — plus name
  preservation on both sides (`Env.find?_eraseCodS`, `Env.find?_norm`),
  which is what turns a raw-side freshness certificate into a
  witness-side one and lets `constsResolve` cross between the two
  environments (`Expr.constsResolve_congr`, already in
  `Setlec/Verify/EnvWF.lean`);
* `NormOracleOk`, the bundle of the three oracle hypotheses the
  stage-4d-prep `norm` congruences carry (`hasFvar` / `bounded` /
  `consts` of the projection rewrite's output).  It is the twin of
  `CodAgree`: discharged at the flip from what the annotation pass
  established, never proved on its own.

Note the asymmetry the split makes visible: raw-side certificates ride
`norm_*` congruences *forward* (stored ⇒ witness), which is the
direction the install needs.  The guard sweep below needs the other
direction, and that is where the flip's remaining difficulty sits.

### Finding: the storage flip is all-or-nothing (2026-08-24, task #100)

The stage-4b handoff estimated the flip as surgical — "storage is
exactly the `readbackEM` argument".  A scouting build says otherwise,
and the finding is worth more than the estimate it replaces.

**The probe.**  The parsed-index non-inductive installs only
(`checkConstantValP` returning a raw `ConstantVal` beside the
annotated one; `checkDefnValP` / `checkThmValP` / `checkOpaqueValP` and
the axiom branch storing the parsed type and value; `recordIConst`
pairing the *stored raw object* as the tag with the *annotated* index,
which is decision 1's first option).  The immediate guards kept reading
the annotated `cvA`, so nothing about the tree that is *checked*
changed.  `Main` imports only `Setlec/Kernel/*` and
`Setlec/Frontend/*`, so the binary builds without the proof layers —
scouting a kernel change costs one `lake build setlec`.

**The result.**  arena 90/92 → **46/92**, e2e 62/62 → **27/62**,
init-prelude probe exit 0/3653 → **exit 2 in 0.5 s** at the first
modeled inductive (`LT`).  Every single failure is the same decline:
*"model type mismatch for `X`"* — the modeled-inductive syntactic
contract, which compares a block member's stored type against the
stored type of its `_model` counterpart.  The `_model` records arrive
as ordinary stream **definitions** (so they flipped) while the block
members are installed by the `Expr`-level inductive driver (so they did
not), and the two differ at every annotated binder.

**The lesson.**  Storage annotation-consistency is a *global* property
of the environment.  Every comparison between two stored trees — the
modeled-inductive contract is the loudest, but every
`ConstantVal.matchesPin`, every `fe.find? n == some cA` pin test, every
`_model` renaming comparison is one — silently breaks when one install
path has flipped and another has not.  There is no verdict-preserving
partial flip and no flag-gated intermediate: the flip lands across
every install path at once, or not at all.

The probe also produced a *positive* result, which is the mechanism
decision 1 rests on: the 46 arena tests that still pass, and the
absence of any exit 3, show that a raw stored tag paired with an
annotated arena index carries `constTyAtM` / `constValAtM` through
delta unfolding unchanged — the interned environment really is the
place the annotations can live.  What the probe shows missing is
*coverage*.

### Handoff: what the storage flip actually needs (task #100 stage 4b/4c)

Three chunks, in dependency order.  Only the third is model-side; the
first is the largest and is verdict-identical by construction, so it
can land on its own.

**A. The annotated shadow index (`ienv`) must become total.**  Today
only `checkDefnValP` / `checkThmValP` / `checkOpaqueValP` and the axiom
branch call `recordIConst`.  Everything else pushes a `ConstantInfo`
with no entry: inductive-block members and recursors
(`checkIndMemberS`, `provisionRecsS`, `checkIndRecsS`), projection
functions and elimination templates (`installProjFnStepS`,
`installProjTemplateStepS`), the direct-structure path
(`checkDirectStructS`), and the basis pins (`installBasisDeclF`).
Worse, two arena entry points have **no entry mechanism at all** and
intern the stored tree directly:

* `ruleRhsAtM` (`Setlec/Kernel/CoreI.lean`) — `internExprM rl.rhs`,
  the iota rule right-hand sides;
* `pinArgsI` — `internExprM p`, the `RecRuleFire.nested` pins.

After a flip these would intern *raw* trees, and the
annotation-reading clauses of `inferType` / `isDefEq` would meet
`cod = none`: an internal error (exit 3), not a verdict change.  So
chunk A is "every stored tree the kernel ever interns is reachable
through an annotated arena index", which needs new keyed entries for
rule RHSs and nested pins alongside the per-constant ones.  Note the
paths that *synthesize* their records (projection functions,
elimination templates, the direct-structure recursor) have no parsed
original, so their raw form is the erasure of what the checker built —
`Expr.eraseCodS` has to become a kernel function for them.

Chunk A changes no verdict (an ienv hit returns an index denoting the
same tree the fallback would have interned) and is provable in today's
framework: `ISOK.ienv` and `ISOK.insertIEnv` stay as they are, and each
install-path simulation gains one `recordIConst_eff` step.

*Why the arena index, and not `decorate`?*  Stage 2 (`codOfI`) and
stage 3 (`decorate`) were built for the other answer — recompute the
annotations on read, inference-free, from the codomain memo.  That
answer is only available for storage that is the annotation pass's
*output with its annotations dropped*: `decorate_eq` reconstructs
`ê` from `ê.eraseCodS`, and nothing else.  The stage-4a ruling stores
the **parsed** record, which differs from `ê.eraseCodS` by exactly the
two skeleton-changing clauses `norm` models (zeta, projection
rewrite) — so rebuilding the annotated tree from what is stored is not
decoration but re-running `annotate`, i.e. full inference, per
stored-constant read, against a memo (`annotC`) that is flushed at
every environment transition.  That is not affordable.  Under parsed
storage the annotated tree therefore has to be *retained* — which is
what the arena already does — and the flip's real content is making
every stored tree reachable through its arena index.  If a future
ruling moved storage to `eraseCodS` of the annotation pass's output,
chunk A would collapse to `decorate` at the four entry points and
chunk B would collapse to uniformly-erased comparands; that trade is
worth re-examining before chunk A is built.

**B. The guard sweep, and the congruence direction it needs.**  The
handoff's decision 2 (retarget `natLitSupportedF` / `strLitSupportedF`
to the stage-1 raw forms) is right in outline and wrong in direction.
Stage 1 proves `natLitSupportedRaw_erase : natLitSupported env = true →
natLitSupportedRaw env.eraseCod = true` — annotated ⇒ raw.  A raw
kernel *tests* the raw guard and the model *needs* the annotated one,
so the flip consumes the **converse**, which is not an erasure
invariance: it is true only because a binder's `cod` is a function of
the skeleton and the environment (the annotation pass recomputes it),
i.e. it is the same fact `decorate_eq` packages.  Every guard that
pin-matches a stored tree is in this class:
`natOpTyPinnedF` / `natOpStoredOkF`, `reduceStoredOkF`,
`ofReduceAxOkF`, `divModEnvGuardF`, `checkEtaThmF` / `checkUnitThmF`,
`directPartsF?`, the `fe.find? eqName = some eqA` tests, and the
modeled-inductive `_model` comparison.  Two ways out per guard, to be
decided guard by guard: prove the converse congruence, or keep the
guard on the *annotated* tree by reading it through the ienv index
(an arena-level guard).  The second preserves verdicts by construction
and is probably right for the pin-matching guards, whose comparands are
fixed annotated trees.

**C. The two-env seam.**  `SimAt env s₀ Rel (interned at `mkFEnv env`)
(pure at `env`)` carries **one** environment parameter, and
`mkFEnv env` occurs ~340 times across 18 `Setlec/Verify/*` modules.
After the flip the interned driver's `fe` is the raw environment while
the ghost pure run is at the annotated one, so either the sim's env
parameter splits into a linked pair (a large mechanical refactor whose
`find?`-agreement rewrites become per-field twin relations), or the raw
environment never reaches `coreKnotI` at all.  The cheap version of the
second — `FEnv`'s index keeps annotated records and only the
accumulated `Env` is raw — leaves the whole sim layer untouched and
makes the top-level theorem speak about the parsed trees, but retains
both trees at runtime, so it is a staging post, not the end state.
Recorded explicitly as a fork for the orchestrator: it buys the
*statement* half of task #100 (the accepted environment is the user's
trees) at ~2× stored-tree memory and without the *computation* half
(the kernel computing on raw trees).

`RawEnvModelN` and its install combinators (stage 4d, above) are the
landing point for whichever route C takes; nothing in the model layer
blocks any of them.

**Not a fork, for the record.**  Storing `eraseCodS` of the annotated
tree instead of the parsed tree would make chunk B's congruences
trivial (both sides of every comparison are uniformly erased) but
changes nothing about chunks A and C, and contradicts the stage-4a
ruling that storage is the parsed record untouched.  Computing the
erasure only at `checkDeclsSP`'s return is a one-line change that
buys the statement and nothing else — the kernel would still store and
compute with annotated trees throughout.
### Finding: annotation-free *consumption* is a kernel change the model cannot follow (2026-08-24, task #100)

The orchestrator's fork resolution on the all-or-nothing finding was to
invert the order: instead of building the annotated shadow index
(chunk A), first make the checker's **consumption** annotation-free —
every site that reads a binder's stored `cod` recomputes it with the
memoized `codOf` (stage 2) — so that the storage flip would need no
shadow.  That inversion was built and measured.  It works in the
kernel and is **blocked in the model**, for a reason that applies to
every site at once.  Both halves are recorded here; the scouting patch
is `_tmp/annotfree-consumption.patch` (kernel-only, `lake build
setlec`).

**The inventory** — every read of a stored `cod` on the checking path,
with what happens to it when the tree is raw:

| site (`Setlec/Kernel/CoreI.lean`) | reads | on `cod = none` today |
|---|---|---|
| `inferBodyI` `∀`-clause | the imax rule's codomain level | `throw .internal` (exit 3) |
| `inferBodyI` λ-clause / `inferLamsI` / `inferLamsOutI` | the λ-annotation, re-checked against the recomputed body sort and reused as the built `∀`'s meta | `throw .internal` (exit 3) |
| `defeqBodyI` `∀`/λ clauses | the two binder cods, compared with `isEquivLM` | `throw .internal` (exit 3) |
| `etaCertI` | λ-cod vs the function type's `∀`-cod | silently `false` — an accept can become a reject |
| `whnfAppI` / `betaPeelI` | the possibly-Prop beta gate | silently *no beta at all* — arbitrary verdict change |
| `codNonZeroIM` (← `inferSpineI`, `iotaCertsGIAux`) | the possibly-Prop iota/app-spine gate | `false` — certifies instead of skipping (verdict-preserving, slower) |
| `natCod1` / `natOpTyPinned` / the pin guards (`Setlec/Kernel/Core.lean`) | *stored* trees, at install time | chunk B, unchanged by this stage |

The recomputation is exactly what `annotateBody` does: a `∀`-binder's
slot is `codOf` of its opened body (`binderCodPiI`), a λ-binder's is
`codOf` of the opened body's *inferred type* (`binderCodLamI`); both
memoized through `codOfI`.  `ensureSortI`, `memoLI` and the `codOf`
pair move up in the file so the core bodies can call them.

**The kernel result: verdict-identical, +45.7 %.**  With every site
switched — the gates in their "always certify" form, which is what a
raw tree forces — the checker is bit-for-bit as accurate and
measurably slower:

* arena 90/92, e2e 64/64 (`tests/arena.sh` compares exit codes against
  the expectations file, so a clean run *is* the exit-code diff);
* init-prelude probe exit 0 (3653/3653);
* init-full exit 0, **61 048 declarations accepted**, output byte-identical
  to master's (301 s → 353 s wall, +17 % — the full stream is far more
  parse/IO-bound than the probe);
* init-prelude instructions 21.47 G → 31.27 G (**+45.7 %**).

The cost decomposes (init-prelude, `perf stat -e instructions:u`,
master = 21.47 G), and the decomposition is the interesting part:

| switched | G instr | Δ |
|---|---|---|
| master (annotations read everywhere) | 21.47 | — |
| `defeq` binder cods + `etaCertI` + `inferLams` via `codOf` | 21.61 | +0.6 % |
| ⋯ + `inferBodyI`'s `∀` clause via `codOf` | 22.87 | +6.5 % |
| ⋯ + beta gate always-certifying | 27.10 | +26.2 % |
| ⋯ + iota/app-spine gates always-certifying (fully annotation-free) | 31.27 | +45.7 % |
| (variant: beta gate via `codOf` instead of always-certifying) | 76.3 | +255 % |

So recomputation itself is nearly free where the checker already
inferred the relevant term (`defeq`, `etaCert`, the λ-telescope — the
λ-clause even gets *cheaper*: `inferLamsOutI`'s per-binder
`isEquivLM` re-check against the annotation disappears, the recomputed
`vcur` being the annotation's own definition).  What costs is the
**possibly-Prop gates**: they exist to *avoid* an inference, so paying
an inference to decide them (+255 %) is absurd and skipping them
(always certify, +39 % between them) is the only sane raw form.  Note
the gates degrade *gracefully* — `cod = none` already means "certify" —
so this half of the price is what a flip would pay even with no
consumption work at all.

**The model result: no consumption site is switchable.**  `interpExpr`
reads `m.cod` at every binder (`Setlec/Model/Interp.lean`); every
soundness clause is therefore stated at the *stored* level, and a
recomputed level is a different object with no connection to it:

* `Setlec/Model/Core/Infer.lean` `forallE` case interprets the node as
  `pi (v₀.eval φ) A B` with `v₀` from `m'.cod` and concludes membership
  in `univ ((imax u v₀).eval φ)` — returning `imax u v_computed`
  instead needs `v_computed ≈ v₀`;
* the same file's app case discharges the gate through
  `codNonZero_eq_true → mPi.cod = some v₀ → pi_pos` on the
  *interpreted* Π — the nonzero bit must be the interpretation's, not a
  recomputed one;
* `defeq`'s binder clause needs `(m₁.cod = 0) ↔ (m₂.cod = 0)` to equate
  the two interpretations, and `AnnotOk` cannot supply it: its clauses
  are semantic memberships (`w ∈ˢ univ (v.eval φ)`) and `univ` is
  cumulative (`univ_mono`), so the stored level is *not* recoverable
  from the interpretation — the same non-determination
  `Setlec/Model/RawEnvNoAnnot.lean` proves for the classifier bit.

The bridge the switch would need is `codOf(e) ≈ the stored cod` **at
every use site**, i.e. on reducts, after substitution, delta unfolding
and level instantiation — a syntactic sort-stability (subject
reduction for sorts) theory that the annotation-first design exists
precisely to avoid.  `decorate_eq` gives it for a tree that *is* the
annotation pass's output; nothing gives it for that tree's reducts.

**Three architectures, and the fork.**

1. **Chunk A (annotated arena index).**  Stored trees reach the
   checking path only through their annotated arena index, so every
   decision is made on inherited annotations, exactly as today.
   Verification unchanged; no runtime cost; the price is retaining the
   annotated trees in the arena (memory, ~2× on stored trees).
2. **Computed consumption + bisimulation against a stored-annotation
   shadow.**  Needs the bridge above at every site.  Not costed
   further: the bridge is a new theory, not a proof effort.
3. **Computed consumption + an interpretation parameterized by the
   `codOf` oracle.**  Make `interpExpr`/`AnnotOk` take the binder level
   from the same oracle the kernel reads, so truthfulness becomes
   self-establishing (`⟦b⟧ ∈ univ (codOf b)` *is* `infer_sound` +
   `ensureSort`).  This is the only route in which annotations
   disappear from the model too, and it is consistent with
   `RawEnvNoAnnot` (which says the bit must come from inference — here
   it does).  It re-signatures `interpExpr`, `AnnotOk` and every
   transport lemma in `Setlec/Model/*`, and it still pays the +39 %
   gate price, since an oracle-parameterized model does not make the
   gates cheap.

*Considered and rejected inside 2:* letting the shadow tree *be* the
decoration of the raw tree by the kernel's own memo, so that the
decisions agree by construction.  It collapses back to the bridge: the
model's transport lemmas (`AnnotOk_beta`, `AnnotOk_zeta_step`) produce
the reduct with its annotations **inherited by substitution**, while
the memo re-decorates the reduct from scratch, and the two coincide
only if `codOf` is stable under the checker's own substitutions — the
bridge again.

Recorded as a fork for the orchestrator; **nothing from this stage is
landed**, because the model-friendly-looking subset (infer's `∀`/λ
clauses, +6.5 %) turns out not to be model-friendly either, and would
be pure loss under architecture 1.

**What this changes in the flip map.**  Chunk A is *not* deleted: it is
the only route that keeps the verification, and it is now understood
not as "make the shadow total so raw trees never reach the checker" but
as "the checker's decisions must be made on annotated trees, because
the model's every clause is stated at the stored annotation".  Chunks B
(guard sweep) and C (two-env seam) are unaffected by this stage.
## fields-raw: the near-cubic direct install (2026-08-24, fix/fields-raw-cubic)

The harness's `fields-raw` finding (2.31 std / 2.74 deep against an
official-kernel 1.07 on identical streams) decomposed, by `perf` at
n=400/800 plus stage-by-stage neutralization experiments, into **three
cubic terms and a spec-inherent quadratic floor**.

### The cubic terms — fixed, comparands unchanged

* **Sequential telescope instantiation.**  `instPisAt`/`instLamsAt`/
  `openPisAtFvars` fold `instantiate1` over the argument list — one
  whole-telescope traversal per argument, quadratic per call, and the
  per-projection outer loop made it cubic (34% of the profile in
  `Expr.instantiate1`).  One-pass variants (`Expr.instPisAtF`,
  `Expr.instLamsAtF`, `openPisAtFvarsF`) peel the raw binders
  structurally while the pending substitutions accumulate, and apply
  them in a single `instantiateList` traversal per domain/residual.
  When the raw telescope is shorter than the argument list (a binder
  only *created* by substitution) the walk falls back to the
  sequential spec, so the equalities are **unconditional**
  (`Setlec/Verify/FastOps.lean`, on task #50's `instantiateList_cons`).
  The executable F-mirrors use the fast variants; the generic
  `Checker.lean` spec and every Model/Bridge proof keep seeing the
  sequential fold, reconnected by rewrites in `Verify/CheckerF.lean`.
* **`directProjTy` redoing earlier substitutions.**  Projection `i`'s
  generated type peeled the constructor telescope at `ps ++ projArgs i`
  from scratch — `Σᵢ i·n` `instantiate1Lift` traversals.  The peeled
  residual is now **threaded across the projection loop**
  (`directProjResid`, driver `checkDirectProjsS`): step `i → i+1` is a
  single `instantiate1Lift` with the next projection substitute.  The
  threaded value is pinned to the spec by `directProjResid_eq` /
  `directProjTy_eq_resid` (via the new `instPisAtLift_append`), so the
  comparands the model consumes are byte-identical; `BridgeS`'s
  projection-fold lemma became `checkDirectProjsS_run`, carrying the
  invariant `rt? = directProjResid … i` through the induction.
* **Positional `List` indexing** in `checkDirectDomsAtF`/
  `checkDirectFieldUnivF`/`domsMatchAux` (O(j) per access, 10% of the
  profile in `List.get?Internal`) — `Array` mirrors (`…FA`,
  `domsMatchAuxA`), converted once per call site.

**Measured** (fields-raw, adjusted instructions): total at n=800
119.2 G → 32.8 G; harness exponents 2.31 → **1.92** std, 2.74 →
**2.22** deep; gates recalibrated to 2.20/2.50 (measured + slack).
All other shapes unchanged (fields-mod 2.42 deep, ctors-mod 2.76,
lparams 1.78, the nine flat shapes 1.00–1.02); arena 90/92, e2e 62/62,
the four #82 verdict flips unchanged; init-core probe accepts.

### The remaining floor — a finding, not a bug in the walks

The official kernel is flat here because it installs **no projection
functions at all** (`.proj` is a kernel primitive); the direct path,
like the modeled path, installs one degenerate recursor per field
whose rule λ-binds the *whole* field telescope — Θ(n²) stored rule
material, and `checkDirectProj`/`checkProjRule` runs Θ(n) reference
checks (annotate, four wellformedness walks, a definitional
domain-pin list — Θ(n) `isDefEq` calls — and an inference) per
projection *by specification*.  Neutralization measurements at n=800
attribute what remains:

* `ops.annotate` of the rule RHS: 8.2 G, exactly n², ~12.7 K
  instructions per (projection, field) unit — the per-call
  intern → annotate → readback machinery constant;
* `allLevelParamsDefined(rhsA)` + re-intern for `ops.inferType`:
  18.2 G, n² **plus a genuine n³ component** — `annotate` tags every
  λ with an *unnormalized* imax-chain codomain sort (the references
  normalize with `mkLevelIMax'`-style smart constructors), so each
  rhsA carries O(n) level nodes per binder that every tree-level walk
  and re-intern re-traverses;
* the domain-pin `checkDefEqList`: 2.7 G, n² at ~4.2 K/unit (per-ops-
  call knot construction + interning + state threading);
* residual machinery: ~3.5 G n² + ~0.9 M fixed per projection
  (flush, stage overhead).

With *everything* above experimentally removed the deep top still
reads exponent ~1.75 — the floor is architectural.  Hitting the
official-like ≤1.3 at n=800 needs the marginal cost per (projection,
field) under ~400 instructions, which no comparand-preserving
instantiation fix can deliver; the candidate follow-ups are design
decisions in their own right: (a) an interned index-passing
projection phase in the style of the task-#78 parsed drivers (no
readback/re-intern, `allLevelParamsDefinedI` on the arena — the
`allLevelParamsDefinedI_spec` stock exists, but the mirror equalities
become state-conditional and the `BridgeS3` walks must carry them),
(b) normalizing the sorts `annotate` stores in binder tags (aligns
with the references; touches every stored type and the tag-reading
interpretation lemmas), or (c) changing what the direct install
stores per projection (route X: the comparands themselves).

## Correct-by-construction arena: ArenaWF + WFStore (2026-08-24, task #103)

Arena validity is now a property of the *type*.  `Setlec/Kernel/WFStore.lean`
defines `WFStore` — an `EStore` bundled with its invariant `EStore.WF` — so
downstream code never states, checks, or threads a well-formedness
hypothesis: every value of the type carries it (the `Std.HashMap` pattern).
The proof field is erased; the generated C represents `WFStore` exactly as
`EStore` (verified: `WFStore.empty` *is* the `EStore.empty` object, `ofRaw`
is the identity, each op calls the raw op and reuses the returned pair in
place), so the bundle is a zero-runtime-cost wrapper.

**Layering resolution.**  The layering rule is liberalized (user decision):
implementation may import a *self-contained data-structure verification* —
one that imports no other Model or Verify modules.  Accordingly the arena's
verification moved, as a pure reorganization (statements identical, all
existing proofs re-elaborate), from `Setlec/Verify/IExpr.lean` into the
kernel-layer `Setlec/Kernel/ArenaWF.lean`, which imports only
`Setlec.Kernel.IExpr`: the denotations (`denote`/`denoteL`/`denoteN`), the
child-list spec functions, `EStore.WF` with `empty_wf` and the
`intern*_wf` preservation lemmas, the whole-tree round-trips
(`internExpr_spec` etc.), canonicity (`denote_eq_iff`), the derived-field
spec functions (`Expr.bvarBound`, `Expr.fvarRange`, `Level.hasParam`,
`Expr.hasLevelParam`) with their exactness facts
(`WF.bvarBoundD_exact` …), and `internExprFast_eq`.
`Setlec/Verify/IExpr.lean` keeps everything that is *not* arena-intrinsic:
the traversal-operation commutation proofs, the memo invariants, and the
two bridges that mention `fvarsBelow` (`fvarsBelow_iff`,
`WF.fvarRangeD_le`) — those need `Setlec/Verify/Shift.lean`, which the
self-contained module must not import.

**The bundle interface** (`Setlec/Kernel/WFStore.lean`): constructors
`empty` / `ofRaw` (seed from a raw store + proof, e.g. `wfB_wf` at a trust
boundary); single-node `intern`/`internL`/`internN` taking the in-range
side conditions as erased hypotheses, plus checked `intern?`/`internL?`/
`internN?` variants that verify them at runtime (`O(children)` per record);
hypothesis-free whole-tree `internExpr`/`internExprFast`/`internLevel`/
`internLevels`/`internBM`/`internName`; the eager derived reads
(`bvarBoundD`, `fvarRangeD`, `lhasParamD`, `ehasParamD`, `readbackN`,
`beqNameI`) with unconditional exactness lemmas.  Every op satisfies a
definitional `*_raw`/`*_idx` equation exposing the raw op, and extraction
is just the field (`s.wf : s.raw.WF`), so the entire existing lemma
library applies to bundle results unchanged.  On the bundle the fast path
is *equal* to `internExpr` (`internExprFast_eq_internExpr`) — the WF
hypothesis of `internExprFast_eq` is in the type.

**Wiring plan (deferred — waits for task #100's storage flip to settle;
the checker does not consume the bundle yet).**  Call sites that change:

* `Setlec/Frontend/Export.lean`: the parse `State.store : EStore` becomes
  `WFStore`.  `State.intern'`/`internL'`/`internN'` — whose child indices
  come from the export tables' index-translation maps, i.e. untrusted
  input — go through the checked `intern?`/`internL?`/`internN?` (a
  `none` is a malformed export record, exit 1 territory); the
  `internLevels`/`internName` calls in the model-name path are already
  hypothesis-free.  The per-record guard replaces the one-shot sweep.
* `Setlec/Kernel/CheckerNC.lean` (~line 444): the `unless st.wfB` seam
  check and its "parse store not canonical" internal error are deleted —
  the parser hands over a `WFStore`, so there is nothing to validate.
* `Setlec/Kernel/CoreI.lean`: `IState.store` becomes `WFStore`.  The
  linearity dance (`{ s with store := EStore.empty }` take/put-back)
  carries over verbatim since the representation is identical.  The
  checker-internal single-node interns build nodes from indices obtained
  from the same (append-only) store; their in-range evidence comes from
  `intern_lt` + `Ext` monotonicity where the context has it, or the
  checked variants where threading it is not worth it.
* `Setlec/Kernel/CheckerS.lean`/`CheckerBase.lean`: entry runners intern
  via the bundle; `runEntryE`'s fresh arenas start from `WFStore.empty`.
* Deletions once no seam validates: `wfB`/`wfBNodes`/`wfBLNodes`/
  `wfBNNodes` (`Setlec/Kernel/IExpr.lean`), `wfB_wf` and the wfB-conjunct
  widening facts in `Setlec/Verify/ParseP.lean` (ParseP then certifies
  parse success only, not canonicity — the bundle carries it).  Until the
  flip, `WFStore.ofRaw st (wfB_wf h)` is the transitional seed.
* Verify-side payoff: proofs that thread `st.WF` hypotheses through
  `ISOK`/state invariants can take them from the bundle (`s.wf`),
  shrinking hypothesis plumbing incrementally; DAG verification is now
  independent of checker verification (the arena module has no checker
  imports).

## Task #103 wiring landed: the parse arena is a `WFStore` (2026-08-24)

The boundary wiring of the plan above is on master; one part is
deliberately parked (below).

* **Frontend** (`Setlec/Frontend/Export.lean`): `State.store` and
  `ParseResult.store` are `WFStore`.  The per-record helpers
  (`intern'`/`internL'`/`internN'`, now `M`-valued) go through the
  checked `intern?`/`internL?`/`internN?`; a `none` — an out-of-range
  arena index, unreachable in practice because children come from the
  export-index translation maps, which only ever hold indices returned
  by earlier interns — throws on the ordinary parse-error path
  (malformed input, exit 3, the same channel as an undefined table
  index; `malformed_midstream` and the whole e2e suite verdict-check
  unchanged).  The model-alias path routes its `.const` head through
  `intern?` too; `initState` seeds `WFStore.empty` with trivially
  discharged side conditions.  The per-record `O(children)` guard
  replaces the one-shot `O(nodes)` sweep.
* **Seams**: `checkDeclsSP`/`checkDeclsSPNC` take a `WFStore`; the
  `unless st.wfB` validation (and `Main.lean`'s progress-mode copy) is
  deleted — the drivers seed the interned state with `st.raw`, and the
  transitional `ofRaw + wfB_wf` seed never became necessary.
* **Deletions**: `wfB`/`wfBNode1`/`wfBNodesGo`/`wfBNodes` (and the
  L-/N-node variants) from `IExpr.lean`; `wfBGo_one`, the three
  `wfB*_facts` extractions and `wfB_wf` from `ParseP.lean` — ParseP now
  certifies walker specs and declaration denotation only; canonicity is
  the bundle's `wf` field.  `ConsistencyP`'s statements quantify over
  `WFStore` and read `st.wf` where they used to branch on `wfB` —
  soundness/no-proof-of-Empty proofs otherwise unchanged (still exactly
  [propext, Classical.choice, Quot.sound]).
* **Linearity** re-verified with a throwaway `dbgTraceIfShared` probe on
  the three parse intern sites: exactly one strike per run regardless
  of stream size — the first mutation of the persistent `initState`
  constant's two-node arena (top-level constants are persistent;
  pre-existing, `O(1)`) — and zero per-entry copies.  The checked
  `intern?` wrapper does not introduce a second live reference.
* **Performance**: neutral-or-better, measured in retired instructions
  (load-insensitive; wall-clock comparisons on this box are dominated
  by concurrent runs).  init-full (`--pre`, 325 MB, 61 048 accepted,
  exit 0, output byte-identical to master): 1.5413×10¹² vs
  1.5545×10¹² instructions — **−0.84 %** (−13.1 G): the deleted
  `O(nodes)` sweep (a hash-map lookup per node plus whole-map `toList`
  materializations, paid as startup latency between parse and first
  check) minus the added `O(children)` per-record checks.  Peak RSS at
  parity (5.90 vs 5.91 GB — the checker's own peak dominates the
  sweep's transient `toList`s on this stream).  Small probes at wall
  parity (init-prelude ~2.3 s both).

**Parked: the `IState.store` flip (`CoreI.lean`).**  Flipping the
checker-internal state's arena to `WFStore` needs kernel-layer
WF-preservation evidence for every mutating traversal op `CoreI`
applies to the store — `instantiate1I`/`instantiateListI`/
`instantiateRevI`, `abstract1I`, `abstractRangeI`, `mkAppNI`,
`instSpineI`, `piResidualI`, `pisToLamsI`, `instantiateLevelParamsI`,
`substLI`, `simplifyLIGo`, `isNonZeroLIGo`, `internLevelSubst(s)` —
whose `WF ∧ Ext ∧ denote` specs live in `Setlec/Verify/IExpr.lean`,
entangled with the denotation-commutation inductions that the module
split above deliberately keeps *out* of the self-contained arena
module.  The flip would further rewrite every `s.store` mention across
the `ISOK`/`SimAt` proof stack (18+ Verify/Model files) from `EStore`
to `WFStore.raw`.  Follow-up construction task, if the payoff (dropping
`ISOK.wf` and its threading) is wanted: prove WF-only *range-invariant*
preservation lemmas in `ArenaWF` (statement per op: `WF ∧ Ext ∧
result index in range ∧ memo indices in range` — no denotation, so
self-contained), lift the ops onto the bundle, then flip and drop the
`ISOK.wf` clause mechanically.  Until then `ISOK.wf` is fed from the
bundle at the seam (`ISOKF.fresh st.wf`), so the *provenance* of every
canonicity fact is already the bundle.

## Driver split: install phase / Bool-barrier check phase (2026-08-24, task #64 stage 1)

The two-tier arena's enabling restructure, built first and on its own
(the tier machinery itself is structure-internal — a parallel task in
`IExpr`/`ArenaWF`/`WFStore`).  The user's insight that makes the tiers
cheap to verify: if the per-declaration pipeline is split into an
*install* phase (everything that produces or stores state) followed by
a *check* phase that returns only success/failure, then at the moment
the check phase ends **no live reference into its temporaries can
exist** — dropping them needs no truncation-transport theory at all.

**The split.**  `checkDefnValP` / `checkThmValP` / `checkOpaqueValP`
(and their NC twins) are reordered install-first:

* install: the syntactic guards on the parsed value, its annotation
  (`jv`), the post-annotate guards, and the recording of the annotated
  indices — `readbackEM jv` and `recordIConst` moved *before* the
  conformance check.  These are state-only steps; nothing that can
  fail moved, so the error order is exactly the pre-split one.
* check: `infer jv` + `defeq` against `jty` — consumes the annotated
  indices, produces nothing.  `CHECK PHASE ENTRY`/`EXIT` comments mark
  the seam; the driver-level cert branches in `checkDeclSP` (Nat-op,
  div/mod and reduce pins) are check-phase too — the future tier
  bracket opens at the seam comment and closes after them, with the
  temp-tier truncation folded into the next step's flush point.
* the environment push stays last, `fe` consumed in tail position
  (the FEnv-linearity discipline is untouched).

Axiom, basis and inductive declarations are install-only for now:
their per-member conformance checks stay inside the install fold
(bounded per block; the reduction-temporary growth the split targets
lives in the def/thm/opaque stream).  Moving block-member checks into
the check phase is a later, measurement-driven refinement.

**The prefix view is positional — no counter field.**  The redirect's
"lookups during check(i) filtered to counter < i" is realized by
*value retention*, not filtering: the check phase receives the very
pre-push `FEnv` the install phase used (the push happens after the
check), so the declaration is not visible to its own conformance
check by construction.  Two reasons this beats a counter field:

1. *Linearity.*  A counter-filtered view of the post-push index would
   either retain the pre-push map across the push (the whole-bucket
   copy per definition that the FEnv-linearity fix killed) or thread
   bound-checking through every `find?`.  The retained pre-push value
   costs nothing: no push happens between install and check, so the
   map stays uniquely referenced.
2. *Proof reuse.*  The check phase's environment is the literal
   `mkFEnv env` value of the enclosing simulation, so every knot
   simulation (`ssimI`) applies unchanged.  A distinct bounded-view
   value would need find?-extensionality congruence across the whole
   sim layer (the ~340-site `mkFEnv` seam recorded at task #100 C).

The counter/prefix-view correctness statement is therefore the
existing one: `checkDeclSP_sim` says the whole install+check step is
reproduced by the pure `checkDecl` **at the pre-declaration
environment**, and the fold (`ConsistencyP`) is the induction over the
fold position — which *is* the installation counter.  A materialized
counter field becomes necessary only for re-checking against arbitrary
prefixes of a fully-installed environment (the `--check-range` rider
over a prior install-only run); parked below.

**Why verdict-identical, and why recordIConst-before-check is
invisible.**  The spec-relevant operation sequence (guards, annotate,
infer, defeq, certs — everything that can fail or reduce) is
unchanged; only `readbackEM`/`recordIConst` moved, and those are
state-only.  The early `ienv` entry for the current declaration is
unreachable during its own check: every consumer
(`constTyAtM`/`constValAtM`) is guarded by `fe.find?`, and `fe` is the
pre-push view.  Measured: arena 90/92, e2e 64/64, scale.sh all-PASS,
axioms unchanged.

**Bridge.**  The three `BridgeP` walks were restructured to the new
order (the `bind_left` blocks for readback/record moved before the
infer/defeq binds); their statements are unchanged, so
`ConsistencyP` and everything above it is untouched.

**Parked riders** (build after the tier bracket lands, so the seam is
wired once): install-only mode and `--check-range a:b` — in the
interleaved driver both are the check phase filtered to a range
(empty range = install-only), an unverified debug knob in the
`SETLEC_NO_PROOF_CERTS` style.  They need either a driver variant
with the check calls skipped or the counter-field machinery above;
neither falls out of the flat bodies naturally today.
*(Landed 2026-08-26 as task #108, on the counter-field machinery —
see "Install/check separation and selective checking" at the end of
this file.)*

**Handoff to the tier wiring** (when the structure-internal
`enableTierTwo`/`truncate` land): open the bracket at each
`CHECK PHASE ENTRY` comment; close it after the cert branches of the
same declaration (truncation can ride the next step's `flushS`, which
already drops every EIdx-carrying cache).  Dangling-safety is
driver-level and short: what survives a declaration step is the
arena, `ienv` (indices recorded at install, i.e. tier one), and the
level caches (`lsimpC`/`lnzC`/`eqvC` — levels and names are
single-tier and never truncated); everything else is flushed.  The
one instruction-cost consequence to re-measure: stored-content
re-interning during check (`ruleRhsAtM`, `pinArgsI`, const-cache
instantiations) lands tier-two and is rebuilt per declaration unless
its nodes already exist tier-one from install — the v1 experiment
bounded this class at +7–8 % instructions, accepted.

### Linearity of the reordered push: verified empirically (2026-08-24, task #64 stage 1)

Per this project's history (`withStore`, `progressLoop`, `diagLoop` —
every RC-2 holder so far was a compiler-liveness surprise found by
measurement), the use-then-consume argument for the deferred push was
verified with the `diag/linearity` probe pattern
(`dbgTraceIfShared`/`auditShared` at `FEnv.push`'s map-insert site,
`EStore.intern`'s table pushes, and per-site prepush tags on the three
value checkers), on the split branch AND on an identically-probed
pre-split master baseline; probes reverted after (throwaway branches
deleted; one ArenaWF `intern_eq` rfl needed a split-by-cases under the
probe wrapper — a probe artifact, not landed).

Init-prelude probe stream (3653 decls accepted), both driver modes,
**split ≡ baseline exactly**:

* `FEnv.idx@push` shared: 307 = 307 (default), 307 = 307 (NC) — all at
  the untagged install paths (inductive members/recursors/projections,
  basis, axioms) plus the two known deliberate retentions below;
  **zero** growth from the reorder.
* prepush tags: thm **0** (the dominant Mathlib kind — the check-phase
  knot and closures die before the push), defn 9 (= the Nat-op/divmod
  rare branch, the #99 deliberate retention), opaque 10 (= every
  opaque: the `checkDeclSP` reduce-pin branch retains `fe` across the
  call — **pre-existing**, fires identically in the baseline).
* multi-decl error stream (`taint_skip_bad_later`): mutation-site
  probe 0 = 0 in both modes; a benign `FE@checkThmValP` *struct*-shared
  ×2 (taint-path bookkeeping) identical in the baseline, with the idx
  map itself exclusive.

Generated-C confirmation (`CheckerS.c`, unprobed merged build,
`checkDefnValP`): the three `(coreKnotI fe checkFuel)` uses are CSE'd
into **one** knot record, destructured and `lean_dec_ref`'d
immediately (before any check runs); the last `fe`-capturing closure
(the consts-resolve `withStore` lambda) is consumed by its `withStore`
call on the next line; the final `FEnv_push(fe, …)` receives `fe`
with **no surviving `lean_inc_ref`** — the insert mutates in place.

### Settled shape for the parked counter/rider stage (user correction, 2026-08-24)

When the riders resume, the counter mechanism is **not** a filtered
view or any second `FEnv` value: entries carry their installation
counter, and visibility is a bound consulted *inside* `find?` —
cleanest as a `visibleBelow` field on `FEnv` itself.  No call-site
signature changes anywhere; setting the bound is an O(1) field update
on the single linearly-threaded `fe`; `find?` returns `none` for
entries at/above the bound.  Push-first, then check against the same
value with the bound set — trivially linear, no retention geometry,
no copies.  The remaining cost is only the sim-layer statement
threading (the pure comparand becomes the counter-prefix of the
environment; the `ConsistencyP` fold invariant already tracks the
per-step correspondence) — to be assessed as the cheap version of the
task-#100 chunk-C seam when the riders resume.  The landed stage 1
(positional pre-push value, interleaved default driver) stands.
## Two-tier arena internals: build-now-wire-later (2026-08-24, task #64)

The encapsulated arena (`EStore`) now carries the two-tier capability
*internally* — structure and proofs only, behavior-neutral until its
operations are called (the #103 pattern).  Nothing in the checker or
frontend calls the new ops yet; every existing test and the init-prelude
output are byte-identical.

**The structure** (`Setlec/Kernel/IExpr.lean`).  `EStore` gains a second
expression tier — `tnodes`/`tcons` plus second copies of the eager
derived arrays (`tbvarBs`/`tfvarBs`/`teparamBs`) — and an internal
`tierTwo : Bool` flag.  Names and levels stay single-tier (the #64
experiments' validation).  Interface additions are exactly two:
`enableTierTwo` (set the flag; subsequent interns append to tier two;
tier one is frozen) and `truncateTierTwo` (drop tier two wholesale —
`Array.shrink 0` keeps the arrays' capacity — and clear the flag).
Consumers stay tier-blind: `intern` dispatches on the flag (`internP`,
the pre-tier code path bit for bit, vs `internT`, which probes the
frozen tier-one cons-table *first* so tier-one content keeps its
canonical index and the tables stay disjoint), and
`getNode`/`bvarBoundD`/`fvarRangeD`/`ehasParamD` dispatch on the index:
a tier-one position reads the tier-one array exactly as before
(the dispatch *is* the bounds check the read always did), anything else
falls through to tier two at offset `i - tierTag`.  `EIdx` stays `Nat`
with the high bit internally meaningful; the tag constant lives behind
the single def `tierTag := 2^62` because large `Nat` literals compile to
a per-use GMP string parse in the generated C (measured landmine from
the experiments) while a top-level def is parsed once at init.

**The invariant** (`Setlec/Kernel/ArenaWF.lean`, self-contained).  The
key discipline: flag-off interns append tier one; flag-on interns append
tier two; hence tier one is frozen under flag-on operation and tier-one
nodes never reference tier-two indices (their children predate the
flag).  `TWF` states this: the 18 pre-tier clauses verbatim, plus
`flag_bound` (flag on → `nodes.size ≤ tierTag`), `toff_tnil` (flag off →
tier two empty), tier-two child/level/name ranges, the tier-two
cons-graph, cross-tier canonicity (`t_cons_fresh`, paid for by the probe
order), and the tier-two derived-entry recurrences (`nodeBvarBound` etc.
over the dispatching reads).  `WF` (the invariant every existing
consumer names) is now `structure WF extends TWF` plus `tier_off`:
statements and field projections are unchanged, so **`Setlec/Verify/*`
and `Setlec/Model/*` compile untouched** — this is the load-bearing
choice: `intern_node`/`intern_denote`/the round-trips are *false* for
flag-on stores, so the invariant those lemma statements quantify over
must entail flag-off; the flag-on regime gets its own `TWF` battery
(`intern_twf`, `internT_twf`, `internL_twf`/`internN_twf`,
`intern_getNode`, `intern_valid2`, `enableTierTwo_twf`).  The theorem
the eventual wiring consumes: `truncateTierTwo_wf : TWF → WF` (the store
re-enters the fully verified single-tier regime) together with the
identity family `truncateTierTwo_{nodes,cons,…,getNode,bvarBoundD,…,
denote,denoteL,denoteN}` — truncation changes *no* tier-one observation
(`denote` at every index: it reads only tier-one tables).  Lifted
through the bundles in `Setlec/Kernel/WFStore.lean`:
`WFStore.enableTierTwo : WFStore → TWFStore` (a second zero-cost bundle
carrying `TWF`), `TWFStore.intern/internL/internN`, and
`TWFStore.truncateTierTwo : TWFStore → WFStore`.

**Tag scheme decision (user-directed, decided on compiler evidence).**
Two candidate index encodings:

* *Low-bit* (`index = 2·offset + tier`): a total injection — both tiers
  unbounded, no size invariant, no guard, and div/mod-by-2 decode.
  Compiler facts (lean.h, v4.33.0): `lean_nat_div`, `lean_nat_mod`,
  `lean_nat_land`, and `lean_nat_shiftr` all have `static inline`
  scalar fast paths — only `lean_nat_shiftl` is out-of-line (which
  refines the packed-keys #89 extrapolation: the +55–73% there came
  through `<<<` pipelines; `>>>`/`&&&` decode is a few inline ALU ops).
  So decode cost alone does *not* disqualify low-bit.  What does is the
  loss of the **identity embedding**: tier-one indices become `2j`, so
  every existing read site (`nodes[e]?` across the traversal ops), the
  whole `denote`/WF/canonicity stack, and every Verify/Model proof that
  identifies index with position would re-base — the exact cascade the
  scheme was meant to avoid, and impossible to build behavior-neutrally
  (flag-off indices change).  Rejected for this task on that structural
  ground; recorded here with the compiled-code evidence.
* *High-bit* (`index = tierTag + offset`, adopted): tier one keeps
  identity positions, so the pre-tier code path and its entire proof
  stack survive unchanged, and the tier-one read dispatch costs zero
  beyond the bounds check the read already did.  The price is a bound:
  the split `i < tierTag ⇔ tier one` is only sound below the tag.  It
  is carried as the *invariant* `flag_bound`, established once by
  `enableTierTwo`'s guard (`nodes.size ≤ tierTag`, one comparison per
  enable — the #42 validate-at-insertion pattern), and consumed as
  theorems (`TWF.tierOne_lt_tag`, `tierTwo_idx_ge`,
  `tierTwo_idx_offset`, `TWF.getNode_tierTwo`): tier two itself needs
  no bound because `Nat` does not wrap.  **No proof anywhere appeals to
  practical unreachability.**

**Guard placement and the failure channel.**  The alternative of an
*unconditional* `nodes.size ≤ tierTag` clause with an insertion guard in
the tier-one intern was analyzed and rejected: a refusing intern is
false-at-the-cap for `intern_node`/`intern_denote`, so every whole-tree
round-trip (`internExpr_spec`) becomes conditional on an arithmetic
budget (`nodes.size + |e| ≤ tierTag`), and that hypothesis infects
ParseP and ConsistencyP — a Model-layer cascade for a state that cannot
occur.  With the flag-conditional bound no failure channel is needed at
all: if the enable guard ever failed (a 2^62-node tier one, ≥ 2^66
bytes), the flag stays off and the store keeps operating in the fully
verified single-tier mode — same verdicts, only truncation's memory
reclamation lost.  Graceful degradation, not an error; were a hard
refusal ever wanted instead, it would be decline (2), a positively
detected implementation limit like fuel — never exit 3.

**Why `Nat`-with-tag rather than `UInt64` indices**: `UInt64` would need
explicit bounds on *both* tiers plus mod-2^64 side conditions on every
index computation; `Nat`'s non-wrapping arithmetic gives tier-two
unboundedness and unique offset recovery for free, and the scalar-`Nat`
fast paths make the arithmetic native-width in practice.

**Behavior neutrality, measured.**  Nothing calls the new ops; the
flag-off `intern` is `internP` (the old body verbatim) behind one
predictable branch, and the derived reads keep the identical bounds
check with the tier-two fallback in the (cold) else branch.  init-full
prelude (`--pre`, exit 0), branch vs master, `perf stat -e
instructions:u`, median of 3: 21.406×10⁹ vs 21.296×10⁹ — **+0.52 %**,
well inside the experiments' ~+2 % dispatch envelope; stdout/stderr
byte-identical.  Full gates green: `lake build` warning-free,
`lake test` (including new `#guard`s exercising
enable/intern/truncate/tier-one-invariance at both the raw and bundle
level), arena 90/92 + e2e 64/64, `tests/scale.sh` all shapes PASS,
soundness axioms exactly `[propext, Classical.choice, Quot.sound]`, no
sorries.

**For the wiring** (follow-up): `IState.store` is still a raw `EStore`
(the #103 flip is parked), so the checker can call
`enableTierTwo`/`truncateTierTwo` directly at declaration boundaries and
thread `TWF` through the interior (or adopt `TWFStore` once the flip
lands).  The tier-blind traversal ops are *not* yet tier-aware — they
read `st.nodes[e]?` directly, which is correct for every store the
current system produces (flag-off); pointing them at `getNode`/the
dispatching derived reads, and extending the denote-faithfulness layer
(`Verify/IExpr`, ISOK) to tier-two indices, is the wiring's job, with
`truncateTierTwo`'s identity family as the interface.

## Low-bit tier encoding: the migration (2026-08-24, task #64, user ruling)

The high-bit entry above recorded the tag-scheme trade-off and adopted
high-bit on the structural ground that it kept the identity embedding.
The user overruled on elegance — measured-similar performance decides
for the *total* injection ("using the high bit in a Nat is very
random") — so the tier machinery was migrated wholesale: the public
`EIdx` is now `2 * position + tier` (tier one even, tier two odd).

**What the total injection buys.**  Both tiers unbounded; NO size
invariant, NO `flag_bound` clause, NO `enableTierTwo` guard and no
graceful-degradation story — the mode switch is one field write, and
the tier of an index is read off its parity unconditionally.  Every
tag-arithmetic lemma of the high-bit battery
(`tierTwo_idx_ge`/`tierTwo_idx_offset`/`TWF.tierOne_lt_tag`) collapsed
into a ~15-line `epos`/`etier` toolkit (`epos_eq : epos e = e / 2`,
`etier_eq : etier e = e % 2`, `epos_double`/`etier_double(1)`,
`even/odd_encode`, `lt_of_epos_lt('), even/odd_inj` — every use an
`omega` step; note the toolkit binders are spelled `Nat`, since `omega`
does not look through the `EIdx` abbreviation in relation types).
`getNode`/`bvarBoundD`/`fvarRangeD`/`ehasParamD` dispatch on
`etier e = 0`; `internP` returns `nodes.size + nodes.size`, `internT`
`tnodes.size + tnodes.size + 1`.  Encode is `p + p + t` — NOT `2 * p`
(`lean_nat_mul`'s inline path carries a hardware-division overflow
check) and NOT `<<<` (out-of-line, the #89 packed-keys landmine);
decode `>>> 1` / `&&& 1` are `static inline` scalar fast paths (the
scout's compiled-code evidence).

**The identity-embedding re-base** — the cascade the high-bit scheme
had avoided, paid once, mechanically:

* Spec seam: `node1? st i = if etier i = 0 then st.nodes[epos i]? else
  none` is the tier-one read the whole flag-off verification stack is
  built on; `denote` reads it (odd indices denote `none`, keeping
  denotation injective and truncation invisible to `denote` at every
  index), and `Valid1 st i = (etier i = 0 ∧ epos i < size)` replaces
  `i < size` as the currency of every in-range fact
  (`denote_valid1`/`intern_valid1`, `intern_wf`'s children hypothesis,
  `WFStore.intern?`'s runtime guard, `DeclP.inRange1`).  Statement
  arities are preserved (`denote_node`/`denote_some_inv`/`cons_graph`
  quantify over `node1?`), which kept the Verify ripple mechanical.
* `TWF` clauses restate for parity: tier-one children are even with
  positions strictly below (`children_lt : … → etier c = 0 ∧ epos c <
  p` — the frozen-tier-one discipline as an invariant), tier-two
  children are `Valid1 ∨ (odd ∧ epos < j)`, cons graphs pair parities
  with decoded reads.  `WF = TWF + tier_off` unchanged.
* Executables: the 52 traversal reads decode (`st.nodes[epos e]?`,
  scout patch), the derived recurrences decode children, the two
  range guards move to the encoded bound (`checkDeclSPStep` gets
  `size + size`; `inRangeB`/`intern?` additionally check parity —
  never false on parser output, which only mints even indices).
* Verify (~11 files): traversal-proof preludes derive `c < e` and
  `Valid1 c` from the position clause (`lt_of_epos_lt'`: an even
  index is below any index of greater position, either tier); the
  per-node `hde`/`hx` denotation facts became *conditional* on the
  input denoting — the low-bit subtlety: an odd index can alias a
  stored position, so the traversals' store/memo-preservation
  conclusions hold unconditionally while the denotation conclusion
  supplies evenness itself.  `denote_some_inv` consumers thread
  `node1?_nodes`; `Model/*` needed only the driver-bound spelling in
  `ConsistencyP`.

**Behavior and measurement.**  Verdict-identical: arena 90/92, e2e
64/64, `tests/scale.sh` all shapes PASS, `lake test` green, init-full
prelude (`--pre`) exit 0 with stdout/stderr byte-identical to the
high-bit master.  Instructions (`perf stat -e
instructions:u`, init-full `--pre`, 61048 decls accepted, median of 3,
vs the merged high-bit master): 1569.25×10⁹ vs 1550.42×10⁹ —
**+1.21 %** (runs deterministic to ~10⁻⁵).  Above the scout's +0.5 %
decode-only figure because the full design also pays the parity
dispatch in the three eager derived reads (`bvarBoundD` and twins:
`&&& 1` + compare + `>>> 1` on every read, where the high-bit scheme's
dispatch *was* the bounds check the read already did) — the measured
price of the total injection, reported for the ruling's
"measured-similar" premise.  The derived-read parity dispatch is the
residual cost site (optimizable later, e.g. by fusing the parity test
with the position bound); the migration landed as a single commit, so
a veto is a single-commit revert.  Soundness
axioms exactly `[propext, Classical.choice, Quot.sound]`; no sorries.

**For the wiring**: unchanged from the entry above, except the
truncation identity family is stated on parities
(`truncateTierTwo_getNode`/`_bvarBoundD`/… take `etier i = 0`;
`truncateTierTwo_denote`/`_node1?` remain index-unconditional), and
`intern?`-validated parser indices carry `Valid1` by construction.

## The check-phase tier bracket: wiring and measurement (2026-08-24, task #64)

The two-tier arena is now *callable*: knob-gated driver variants
(`SETLEC_TIER_BRACKET`, the `SETLEC_NO_PROOF_CERTS` pattern —
UNVERIFIED measurement variants; the consistency statements cover the
default drivers, which are byte-identical to before) run the
def/thm/opaque value pipeline with tier two enabled and release the
per-declaration temporaries.  Four modes, two axes:

* **Bracket extent**: modes 1/2 bracket the *check phase* (infer +
  defeq, the driver-split seam); modes 3/4 bracket the whole *value
  pipeline* — annotate, the post-annotate guards, the value readback
  and the check all run under tier two, and on success only the stored
  output's sub-DAG is *promoted* into the retained store
  (`Setlec/Kernel/Promote.lean`: index-memoized re-intern, `O(|output
  DAG|)`, never tree-shaped; opaques store nothing and promote
  nothing).  The rare cert branches (Nat-op/div-mod/reduce pins) and
  the install-only kinds stay on the default path (bounded content).
* **State discipline**: modes 1/3 are *fork-discard* (retain the
  pre-bracket `IState` value, run on a header copy with the flag set,
  `set` the retained value back — the RC release is the truncation;
  the snapshot argument of the RC-linearity skill, §5.1/5.2); modes
  2/4 are *in-place* (linear state, `enableTierTwo` at the seam,
  `truncateTierTwo` + `IState.flushed` at the close, detach-before-
  update).  In-place wins decisively: the fork pays a per-declaration
  copy-on-write of every shared component the check writes (level
  tables, memo buckets — `lean_copy_expand_array` at ~8 % of cycles)
  plus the discard's free traffic, and it *loses* the check phase's
  level-cache and level/name-table warmth; in-place keeps single-tier
  content (levels/names, `lsimpC`/`lnzC`/`eqvC` entries) across the
  close — only the `EIdx`-carrying memos are flushed, which the next
  declaration's `flushS` would have dropped anyway.  Promotion under
  in-place needs no level/name remapping at all (their bracket-time
  interns simply persist; the level/name bases are the harvest-time
  table sizes, so `promoteLGo`/`promoteNGo` are identity), and the
  tier-two node table is harvested *before* truncation — the
  truncating shrink on the then-shared array is an O(1) empty-array
  allocation.

**Flag-off discipline, stated and probed.**  Install-phase content
interns flag-off by construction: in modes 1/2 the bracket opens after
`recordIConst` (annotate output, `readbackEM` and the `ienv` record
are tier-one); in modes 3/4 the `ienv` record is written after the
close from the *promoted* (tier-one) index, paired with the readback
tree harvested from the snapshot.  Nothing the bracket interns can
escape: the bracket returns the verdict, and the pushed
`ConstantInfo` is built from `Expr` trees.  The `dbgTraceIfShared`
probe battery (internP node/cons pushes, `FEnv.idx@push`; identically
probed baseline): shared-mutation counts identical to the off-mode
baseline in all four modes (init-core: `internP` 1 = 1, a
pre-existing seed-handoff strike; `FEnv.idx@push` 445 → 434, fewer).

**FINDING (restrictions-are-findings): the total injection broke the
traversal order in the flag-on regime.**  The low-bit migration kept
the `child < parent` recursion guards of the ~20 traversal ops; under
`EIdx = 2·pos + tier` that order is wrong exactly when it matters — a
tier-two node (`2j+1`) is numerically *below* its tier-one children
whenever their positions exceed `j`, so every `<`-guarded descent
silently refused (ops returned identity/false; the first bracketed
declaration failed its own post-annotate guards).  The flag-off gates
could not see it: nothing on master exercises the flag.  The fix is
the tier-lexicographic order `emlt` (tier one below tier two,
positions within a tier — the order every arena node respects towards
its children, in both regimes) in the executable guards, with
termination by `(etier e, epos e)` (`emlt_lex`), the flag-off proof
bridge `emlt_of_even_lt` (flag-off children are even and `<` their
parent), and `emlt_induction` for the store-unconditional
function-equality proofs.  This is the executable face of the
identity-embedding objection the tag-scheme entry recorded: high-bit
kept `Nat` order compatible with the traversal for free; the total
injection pays for it with a two-comparison guard (part of the off-
mode instruction delta below).

**Measured (init-core, 110 k lines / 5965 decls; instructions
`perf stat -e instructions:u` median of 3; verdicts byte-identical to
off in all modes, arena 90/92 + e2e 64/64 byte-identical, scale.sh
all-PASS):**

| mode | retained arena (nodes) | instructions | vs off |
|---|---|---|---|
| off | 916,433 | 38.539 G | — |
| 1 fork check | 692,392 | 42.209 G | +9.5 % |
| 2 in-place check | 692,392 | 38.718 G | **+0.47 %** |
| 3 fork snapshot | 328,468 | 42.360 G | +9.9 % |
| 4 in-place snapshot | 328,468 | 39.720 G | **+3.1 %** |

The decomposition (`SETLEC_STATS` gains an end-of-run
ienv-reachability count — `REACH: n0=139652 … ienvReach=136792
storedAboveParse=72439`, identical in every mode): parse floor
139,652; parse + stored floor **(c) = 212,091**; check-phase
temporaries = 224 k (29 % of off-mode growth, dropped by modes 1/2);
annotate-side intermediates = 364 k (47 %, additionally dropped by
modes 3/4); the mode-4 residue above the floor (116 k) is the
unbracketed type-side work (`checkConstantValP`'s annotate + sort
check, the thm prop check) and block installs.  The perf pair is
RSS-unchanged (app-lam 8.03 GB, intra-declaration by design;
beta-ladder slightly lower), outputs identical.

**Measured (Mathlib prefix, 12 M lines / 101,326 decls accepted,
`_tmp/mathlib-scoping/prefix-12M-pre.ndjson`, `--pre`, RSS sampled at
2 s alongside the progress counter; verdict streams byte-identical to
off in modes 2 and 4; post-master-merge binary at 94d0aa7):**

| mode | retained arena (nodes) | growth/decl above floor | peak RSS | wall |
|---|---|---|---|---|
| off | 139,803,862 | 1,215.6 | 22.12 GB | 798 s |
| 2 in-place check | 122,162,895 | 1,041.5 | 15.95 GB (−27.9 %) | 803 s |
| 4 in-place snapshot | 32,377,242 | 155.4 | 9.39 GB (−57.5 %) | 781 s |

The decomposition inverts init-core's: `REACH: n0=11377543
ienvReach=11372143 storedAboveParse=5255409` (identical in all
modes), so the parse + stored floor is 16,632,952 nodes (164/decl).
Of the off-mode growth above that floor (123.2 M nodes), the
check-phase temporaries dropped by mode 2 are only 17.6 M (**14.3 %**
— vs init-core's 29 %); the annotate-side install-phase intermediates
additionally dropped by mode 4 are 89.8 M (**72.9 %** — vs 47 %); the
mode-4 residue is 15.7 M (12.8 %, the unbracketed type-side work and
block installs, ~4× the stored floor).  On Mathlib the annotate
intermediates dominate outright — the check-only bracket is *not*
sufficient as the memory lever; the value-pipeline bracket is.
Mode 4 reproduces the v1 wholesale-truncation profile almost exactly
(v1 on its ~2 M-line prefix: retained nodes 24.2 % of baseline, RSS
−56.6 %; mode 4 here: 23.2 %, −57.5 %) while keeping the default
drivers byte-identical and the promotion `O(|output DAG|)`.
Post-merge instruction envelope re-confirmed on init-core (median of
3): off 37.746 G, mode 2 +0.49 %, mode 4 +3.14 %, outputs
byte-identical across modes.  **Consequence for landing order:** the
flag-on verification battery should target mode 4 (in-place
value-pipeline snapshot + promotion) directly; mode 2 alone leaves
~86 % of the Mathlib-scale growth in place.

**Verification status.**  The four bracket modes are measurement
knobs; landing one as the *default* requires the flag-on interior
battery — `ISOK`/denote-faithfulness extended over `getNode` to
tier-two indices (a tier-aware denotation and the op-sim battery in
the flag-on regime), plus (modes 3/4) a promotion-correctness spec.
The `emlt` executable/termination layer landed *verified* (the
flag-off proofs bridge through `emlt_of_even_lt`; gates green,
axioms exactly `[propext, Classical.choice, Quot.sound]`).

## Projection-unification audit: what can and cannot go native (2026-08-24, task #107)

Task #107 asked for every structure's `.proj` to become first-class
(typed by a native `ProjEntry`, reduced by the generic structural
rule, interpreted through per-(type, index) model facts), deleting
`annotateProjElim`'s rewrite-to-application, `annotateProjRec`, and
the artificial `projFnName` rec-constants of both the modeled and the
direct install.  The audit (instrumented runs over init-prelude,
init-full, the arena set and the whole e2e suite; instrumentation not
landed) shows the target splits into one feasible slice and two
provably-permanent restrictions.  Restrictions are findings — both
are recorded here with their witnesses.

### Route census (instrumented, this worktree)

* **init-prelude** (`--pre`, exit 0): 155 artifact-route projection
  functions installed (`checkProjFn`); **5 template entries** —
  `ByteArray.IsValidUTF8` 0/1, `Nonempty` 0, `_wcore.Exists` 0/1, all
  definitely-`Prop` owners with data (or data-crossing) fields whose
  `_model.proj_i` artifacts the preprocessor correctly omits
  (`eligibleProjectionFieldsM` mirrors the kernel's `infer_proj`
  walk); **0 uses of `annotateProjRec`**; **0 direct installs** (the
  direct path is artifact-absence gated and preprocessed streams
  carry artifacts for everything); 496 annotate-time rewrites
  (`PProd'`/`PProd` dominate: 345).
* **init-full** (`--pre`, exit 0): 977 artifact-route projection
  functions; 7 template entries (the init-prelude five plus `Exists`
  0/1); **113 accepting uses of `annotateProjRec`, all on `Exists`
  fields 0 and 1** — witness/proof projections at instantiations
  where `α` collapses to `Prop` (`u = 0`), exactly the
  level-instantiation-dependent legality that per-declaration
  artifacts cannot express; 8 895 rewrites (`PProd` 3 565, `PProd'`
  1 911, `PSigma` 1 940 lead).
* **arena**: `annotateProjRec` is *load-bearing for verdicts on both
  sides*: the projProp family 087–092 (a `Prop` structure-like with
  `PUnit.{u}`/`PUnit.{v}` data fields interleaved with proof fields)
  runs entirely through template entries + the fallback — 087/089
  accept, 088/090–092 reject with the official `Prop`-restriction
  errors surfacing from the re-annotated elimination.  Direct
  installs appear only in raw `bad` duplicate-declaration tests
  (nF = 0).
* **e2e**: direct installs with fields only in `direct_struct_raw`
  (`Wrap` nF = 2, `Unit'` nF = 0); `prop_proj_raw` (= arena 087)
  accepts through the fallback; `direct_nested_dep` is preprocessed
  and takes the modeled route (`Box`).

### Finding A — the Prop template tail is permanent (kernel-parity)

A template-entry field cannot be served by a native entry even in
principle: whether `.proj T i e` is *legal* depends on the use site's
level instantiation (which crossed fields collapse to `Prop`), and a
native entry's single level-parametric `ty` cannot express that — the
official kernel makes exactly this per-use decision in `infer_proj`,
which is what `annotateProjRec`+`projFieldDom` re-create at the use
site's concrete levels.  Moreover a native entry whose field sort is
not `≤` the struct sort at every assignment is *semantically
incoherent*: with `structSort = 0 < fieldSort` (e.g. a `Bool` data
field of a `Prop` structure), proof irrelevance identifies `mk a ≡ mk
b` while the structural rule reduces their projections to `a` and
`b` — accepting such a reduction derives `false ≡ true`.  The current
`projCert` does not check the implication `structSort = 0 →
fieldSort = 0`; it doesn't need to *today* because the only native
entries (the pair's) satisfy `u ≤ max u v` level-arithmetically.  Any
future generalization of native entries must add that bound as an
install-time obligation (the direct class has it: nonzero result sort
+ `checkDirectFieldUniv`).  **Verdict: `annotateProjRec`, the
template entries and their install pass stay, unchanged.**

### Finding B — modeled structures cannot go native (semantic obstruction)

This upgrades the task-#18 scoped finding ("bare `.proj` nodes on
non-Prop modeled structures have no compositional set interpretation,
model bodies being opaque") from a proof-technique gap to a
*counterexample-backed impossibility* under the current artifact set.
A first-class `.proj T i e` carries neither the parent's levels nor
its parameters, so `interpExpr` must interpret it through a single
level- and parameter-free function `V → V` (the pair's `sfst`/`ssnd`
shape).  For an opaquely modeled `T` no such function needs to exist:
the checked artifacts (member types up to renaming, `proj_i` defs,
`iota`/`eta` theorems) do not pin the model up to *projection
coherence across instantiations*.  Witness (artifact-complete, fully
checkable, eta included): public `T (p : Nat) : Type` with one field
`x : {v // v = p}`; adversarial model `T._model := fun _ => PUnit'`,
`mk._model := fun _ _ => unit`, `proj_0._model := fun p _ => ⟨p,
rfl⟩` — `proj_0.iota` and `eta` are provable (the field type is a
subsingleton), every install check passes, yet `⟦mk 1 x⟧ = ⟦mk 2 y⟧`
while the two required reduction equations force different values of
any candidate interpretation at that one point.  So *no* definition
of the `.proj` clause supports the `Whnf` claim for modeled types;
the failure is not about how the proofs are written.  The only
escapes inspect model *bodies* (syntactically, or by pinning
`T._model ≡ PSigma'-tower` definitionally at install) — the first is
against the "models: public interface only" ruling, and both fail on
the preprocessor's packed nested fields, so the artifact route keeps
strictly more streams.  **Verdict: `checkProjFn`'s rules-carrying
projection functions and `annotateProjElim`'s rewrite stay for
modeled structures.**

### The feasible slice — direct structures join the pair (parked, not started)

The direct class is exactly the coherent class: nonzero result sort
(recognition) + the per-field universe bound (`checkDirectFieldUniv`)
give pair-style `projCert` soundness, and the model values are
*transparent* towers (`DirectTower`), so level/parameter-free
destructors exist by construction.  The revised #107 is therefore:
`checkDirectProj` installs a native `ProjEntry` (ty = `directProjTy`
switched to `.proj`-node spelling for the earlier-field substitutes;
`fieldSort` via `ensureSort` at the opened frame; `structSort :=
resSort`) instead of the degenerate recursor + rule, and the direct
route's `.proj` nodes stay first-class end to end.  Known work
items, sized during the audit:

* **Tower dialect**: `tupleV`/`projV` are unit-terminated
  (`⟨f₀,⟨…,∗⟩⟩`, `projV i = sfst ∘ ssnd^i`) while the pinned pair is
  bare (`sfst`/`ssnd`), so a single destructor family does not cover
  both.  Options: (iii) let the generalized `interpExpr` `.proj`
  clause consult `env.findProj?` and dispatch pair-vs-tower on the
  (ProjOk-pinned) `psigmaName` — precedent: the literal clauses
  already consult the env (`natLitSupported`); or (i) de-unitize the
  direct tower (last field bare) so `nF = 2` coincides with the pair.
  (iii) avoids reworking `DirectTower`/`DirectDecl` value shapes but
  makes the clause env-dependent, so the interp stability walks
  (extension lemmas) need `findProj?`-agreement conditions; staging
  is consistent (entry `i`'s `ty` mentions `.proj T j` only for
  `j < i`, already installed).
* **Kernel**: `checkDirectProj` (Checker.lean) + `checkDirectProjF`/
  `checkDirectProjsS` (CheckerS) switch to entry install;
  `Core`/`CoreI` need *no* changes (the annotate/infer/whnf `.proj`
  rules are already generic over native entries; the recInfo branch
  of `annotateProjElim` remains for the modeled route).
* **Model**: `ProjOk` generalizes from "exactly the two pair
  entries" to keyed per-entry clauses (pair ∨ direct-certified with
  the semantic facts); `interpExpr`/`AnnotOk` `.proj` clauses
  generalize; the three claim sites reworked (`Model/Core/Whnf.lean`
  ~273–500, `Model/Core/Infer.lean` ~377–522, `Model/Annotate.lean`
  ~369); `ProjOk.cons`/`env_swap`/`extend_fresh` transports pick up
  the new clause; `Model/DirectDecl.lean`'s projection stage
  (`checkDirectProj_inv`, `DirectProjInv`, `directProj_facts/_mem/
  _fold/_rule_eq`, `extend_direct_proj`, `direct_proj_step/_fold`)
  restates over `.proj`-node spelling — this is the bulk of the
  work; `directProjVal` and the fold equations carry the semantic
  content already.
* **Streams**: verdict-preservation surface is small (direct installs
  occur only in raw streams: arena `bad` dup tests, e2e
  `direct_struct_raw`); stored forms on the direct route change
  dialect, so any fixture pinning them regenerates via the
  documented export-fixture flow.

Payoff check before starting: today the direct path fires on *no
accepting arena/init stream* (artifact-absence gate), so the slice
buys internal uniformity and the #82 expansion's foundation, not
stream coverage.  If #82's gate ever widens, this slice is its
prerequisite; on its own it does not change a single verdict.

## Annotation erasure: the domain-relative collapse (2026-08-24, task #100)

The response to the "annotation-free consumption" fork above: a
**fourth architecture** — make the *model* level-free, so that neither
stored annotations nor a `codOf` oracle appear in any semantic
statement.  The canon-model spike validated it; its operator layer is
now landed as `Setlec/SetTheory/Derive/Collapse.lean` (evidence
included, nothing consumed yet), and the model flip itself is **blocked
on a kernel de-gating stage first** — a new finding, recorded below
with its countermodel.

### The operators (landed)

The spike's literal proposal — a global hereditary canonicalization
`canon : V → V` — is *refuted* (two formal horns, `Collapse.lean`:
`hereditary_canon_pt_not_fixed`, `hereditary_canon_pi_empty_not_prop`;
the root cause is that `∅` is both the empty function graph and
falsity, with `pt = {∅}` pinned).  The goal survives via a
*domain-relative* collapse needing no recursion:

* `pcol A g` — collapse a member of `piSet A B` to `pt` iff its
  applications on `A` are all `pt` (vacuously over `A = ∅`);
* `piC A B := image (pcol A) (piSet A B)`, `lamC A F := if (∀ x ∈ A,
  F x = pt) then pt else graph F A`; `app` unchanged.

`pcol A` is injective on `piSet A B`, so `piC` is a relabeling; the
full law battery is re-derived level-free (the old→new table is in the
module docstring).  Highlights: `pi_zero` becomes a **theorem**
(`piC_prop_eq`, conditional on truth-value fibres); beta and
elimination lose *all* side premises (`app_lamC`, `app_mem_piC`);
`piC_mem_univ` keeps the `imax` shape; `lam_ne_pt` is **false** (that
is the point); `lam_dom` weakens to `lamC_dom_of_ne` (premise `≠ pt`
instead of a nonzero level).  The `RawEnvNoAnnot` refutation is evaded,
not contradicted: its two witness λ-terms now receive the *same*
interpretation `pt`, and `mem_type` holds for both because the
type-side target moved from `piSet` to its collapse image
(`lamC_witnesses_identified`, `pt_mem_piC_punit_nat/_true`).  Basis
ports (PSigma projection with collapsed stored values, iota with a
collapsed minor premise, the full `Nat.rec.{0}` tower) all check out in
the same file.

### Finding: the annotation-guarded reduction gates are unsound-to-model under the collapse (2026-08-24, task #100)

The kernel's possibly-Prop gates decide *by stored annotation* that a
value cannot be the proof point.  Under the collapse that inference is
false at every level — an **empty-domain abstraction collapses to `pt`
no matter its codomain sort** — and the gates' soundness claims are
falsified outright, in the empty environment:

**Countermodel** (guarded beta, `WhnfCoreClaims`): take

    (fun (x : ∀ p : Prop, p) => Prop)  Prop

with the λ's `cod` annotated `1` (truthfully: the body is `Prop :
Sort 1`).  Under the collapse `⟦∀ p : Prop, p⟧ = piC univZero id = ∅`
(the `p := False` fibre is empty), so `⟦λ⟧ = lamC ∅ _ = pt` by the
vacuous collapse.  The flip-target `AnnotOk` app slot is *satisfiable*:
choose `A := {univZero}`, `B := fun _ => unitSet`; then `vf = pt ∈ˢ
piC A B` (`pt_mem_piC_iff`), `va = ⟦Prop⟧ = univZero ∈ˢ A`, fibres in
`univ 0`.  The `isNonZero` gate fires, beta produces `Prop`, and
interpretation is *not* preserved: `⟦redex⟧ = app pt univZero = pt ≠
univZero = ⟦Prop⟧`.  Under the *leveled* operators the same slot is
unsatisfiable — `⟦λ⟧ = graph _ ∅ = ∅`, and `∅ ∈ˢ pi vE A B` forces
`A = ∅` at `vE ≠ 0` and is impossible at `vE = 0` — which is precisely
the `lam_ne_pt`/domain-determination machinery the collapse removes *by
design* (it is how the witnesses get identified).  The set-level core
is checked in `Collapse.lean` (`lamC_empty`, `app_lamC_empty`,
`piC_univZero_id_empty`, `guarded_beta_countermodel_core`).

No `AnnotOk` strengthening repairs this.  The task-#73 impossibility
analysis extends from `Prop` to **every level**: under the collapse,
values do not determine domains whenever the domain can be empty
(`lamC D F = pt` for *every* `D` with all-`pt` values — in particular
every empty `D`), so an app-slot domain pin is unsound exactly as
before; and syntactic conjuncts ("if `f` whnf-reduces to a λ then
`va ∈ ⟦its domain⟧`") are not stable under substitution or delta (the
subject-reduction bridge the annotation design exists to avoid).  The
same construction kills each annotation-gated path:

* **guarded beta** (`whnfCoreBody`'s `v.isNonZero` branch) — the
  countermodel above;
* **the #49 gated app-spine/iota re-check skip** — its soundness
  recovers `⟦a⟧ ∈ ⟦domain⟧` by `eq_graph_app_of_mem_piSet` /
  `graph_ne_pt`, both false at collapsed values (same shape, body of a
  non-`pt`-containing type, e.g. a `PSigma` over an empty first
  component);
* **the guarded projection** (`mx.isNonZero`) — a constructor
  application's value collapses at instances with an empty field
  fibre, and the proj slot's existential levels cannot see it.

By contrast the **defeq binder-cod comparison** (zero-ness form, just
landed) and the **λ-annotation re-check** are not falsified — they
become *unnecessary* (level-free `lamC_congr`/`piC_congr` need no
zero-ness agreement), and deleting them only moves defeq toward
reference behavior (reference trees carry no cods at all).

### The amended migration order

The spike's order ("re-target Interp/AnnotOk → DefEq/Infer/Certs →
Whnf guarded beta → …") cannot be green-sequenced: the flip falsifies
the gated claims the moment `interpExpr` produces collapse values.
Amended order, each stage green:

1. **[landed]** `Derive/Collapse.lean` — operators, laws, refutation,
   evidence (this stage).
2. **[landed] Kernel de-gating** (prerequisite, *kernel + Verify +
   Model*): switch guarded beta, guarded proj and the #49
   app-spine/iota gates to their **always-certify** forms, and delete
   the defeq cod comparison and the λ-cod re-check *(amended on
   execution: the last two are NOT stage-2-deletable — see the
   stage-2 record below; they move into stage 3)*.  All of this was
   already built
   and measured verdict-identical in the annotation-free-consumption
   scouting (`_tmp/annotfree-consumption.patch`): beta certify
   +26.2 %, spine/iota certify ≈ +13 %, the rest ≈ free.  Those
   numbers *kept the annotate pass running*; the erasure end-state
   deletes the pass (a full inference sweep per declaration), so the
   net must be re-measured here.  Model side: the gated branches and
   their domain-determination proofs (`Core/Whnf.lean` beta,
   `Core/Infer.lean`/`Core/Certs.lean` #49 recovery, proj) *delete*;
   the certified branches already carry the needed `⟦a⟧ ∈ ⟦domain⟧`
   facts.  Verdict risk: accept-side identical on well-typed streams;
   the certify paths are stricter on adversarial ones (gates: arena +
   e2e + scale + init probes).  Touches `Kernel/Core.lean`/`CoreI` —
   coordinate with concurrent kernel work (#64).
3. **The model flip**: `pi`/`lam` become the collapse ops;
   `interpExpr`'s binder clauses go level-free (no `m.cod` reads);
   `AnnotOk` drops the cod conjuncts.  *Also in this stage (moved from
   stage 2): delete the defeq binder zero-ness comparison and the
   λ-annotation re-check in `inferBody`'s lam clause/`inferLamsOutI` —
   deletable exactly when the model stops reading levels
   (`piC_congr`/`lamC` membership need no level agreement).*  Shim
   design, recorded for the executor:
   * *Vestigial level*: `noncomputable abbrev pi (v : Nat) A B := piC
     A B` (same for `lam`) — definitional level-erasure, so the ~2000
     explicit-level call sites elaborate unchanged and interp-equation
     rewrites never see a level mismatch (goals display `piC`/`lamC`).
     The abbrevs die in stage 6.
   * *Compat surface* (old names, old signatures, one-line proofs from
     the collapse laws): `pi_congr`, `lam_congr`, `lam_mem`,
     `app_mem'`/`app_mem`, `app_lam'`/`app_lam`, `lam_eta`,
     `eq_of_mem_pi_app_eq`, `pi_mem_univ`, `IsTGUniverse.pi_mem`,
     `pi_level_indifferent` (now `rfl`), `pi/lam_congr_zero_agree`.
   * *False surface* (delete; ~65 call sites migrate): `pi_zero` (1),
     `pi_pos` (8), `lam_zero` (40), `lam_pos` (2), `mem_pi_zero` (6),
     `lam_ne_pt` (3), `lam_dom` (4), `pi_zero_mem_univZero` (1).
     Replacements per the `Collapse.lean` table; `lam_zero` sites need
     the in-context all-`pt` fibre facts (`lamC_of_forall`);
     `StdAxioms.pt_mem_pi_zero`'s premise moves from ∃-inhabitant to
     `pt`-membership (`pt_mem_piC_iff`), its ~10 axiom-install
     consumers adjust witnesses; `BasisLemmas.lam_pi_dom` /
     `Basis/Glue.lam_dom_of_ne` become `mem_piC_cases` dispatches
     (their `pt` branches are fed by the de-gated certified facts).
   * *`AnnotOk` flip shape*: binder clauses lose `∃ v, m.cod = some
     v`; the fibre-universe facts become **per-φ existential levels
     outside the domain quantifier** — `∃ vE, ∀ x A, interp ty = some
     A → x ∈ˢ A → ∃ w, interp body' = some w ∧ w ∈ˢ univ vE` —
     feeding `piC_mem_univ` at `mem_type`/sort obligations (the
     existential must be uniform in `x`; `annotate_sound` instantiates
     `vE := (stored cod).eval φ` while annotations exist, inferred
     sorts after stage 5).
4. **Iota walk / basis domain recovery**: `Glue`/`BasisLemmas`/
   `IotaWalk` via `mem_piC_cases` (collapsed branch: `app_pt`
   propagation, `pt` inhabits every fibre over the domain).
5. **Basis values**: the per-type `Install/Claims/Iota/RuleOk/AnnotOk`
   modules re-derive on the collapse laws (mostly premise deletions;
   `lam_zero`-style value computations become `lamC_of_forall`).
6. **Kernel-side erasure**: delete the annotate pass, `BinderMeta.cod`
   storage, the cod memos and the vestigial level parameters; the
   raw-storage chunks (A/B/C above) collapse to their raw forms — with
   the model level-free, no shadow environment and no `codOf` oracle
   is needed (architecture 4 supersedes the fork's 1–3).

### Stages 3–5 landed; the erasure migration's remainder is exactly stage 6 (2026-08-25, task #100)

**Landed** (branch `feat/100-flip`; gates: build warning-free, `lake
test`, arena 90/92, e2e 64/64, axioms exactly `[propext,
Classical.choice, Quot.sound]`, scale all-PASS, init-prelude
byte-identical to pre-flip master in both modes).  The flip's
execution absorbed stages 4 and 5 — they were not separable in
practice, because the false-surface deletion (stage 3's `lam_zero`/
`lam_dom`/… migration) *is* the iota-walk and basis-value rework:

* **Stage 3 (the model flip)** — `interpExpr`'s binder clauses are
  level-free; `AnnotOk`'s ∀-clause carries the subset-form cod tie
  (below), the λ-clause none; the vestigial `pi (v) A B := piC A B`
  abbrevs stand in at the ~2000 call sites; compat surface derived,
  false surface deleted (`Derive/Pi.lean` documents the replacement
  table).  Of the two moved deletions: the defeq binder cod
  comparison is **gone** (spec/interned/NC), the λ-annotation
  re-check is **restored** (see the finding below).
* **Stage 4 (iota walk / basis domain recovery)** — `IotaWalk`,
  `Basis/Glue`, `BasisLemmas` dispatch through `mem_piC_cases` /
  `≠ pt` premises; the guarded-beta/proj successors consume the
  de-gated certificates unconditionally in the soundness walks.
* **Stage 5 (basis values)** — every per-type
  `Install/Claims/Iota/RuleOk/AnnotOk` module re-derived on the
  collapse laws (`lamC_of_forall` value computations, if-form
  universe witnesses via `piC_mem_univ`, subset-form ties).
* **Also forced here** (collapse root cause, recorded below):
  modeled Eq-statement domains are *certified* —
  `checkIotaThm(N)`/`checkProjIota` run `checkIotaSidesTy`,
  eta/unit pin their type slots syntactically.

**What remains — stage 6 (kernel-side erasure), in one piece** (this
plan; see *Stage 6 landed* below for what actually happened):

1. Delete the annotate pass (`annotateCore` + `ops.annotate`
   surface), `BinderMeta.cod` storage, the cod memos, and the
   vestigial level parameters on `pi`/`lam` (the abbrevs die; goals
   then read `piC`/`lamC` directly).
2. The two loads that die *together with* the stored cod: the
   λ-annotation re-check (`Kernel/Core.lean` lam infer clause,
   `inferLamsOutI`) and the ∀-imax cod read — the ∀-clause then
   infers its codomain sort, and `AnnotOk`'s subset-form tie becomes
   self-establishing (`m.cod = none` renders the tie vacuous;
   `Interp.lean` says so at the clause).
3. The raw-storage flip is stage 6's implementation path: groundwork
   landed (raw-storage stages 4a `norm`/twin relation and 4d install
   combinators, above); the call-site-by-call-site plan for 4b/4c is
   in the two storage-flip handoffs (`stage 4b, call site by call
   site` and `what the storage flip actually needs`).  With the
   model level-free there is no shadow environment and no `codOf`
   oracle — architecture 4.
4. Gates unchanged: verdicts byte-identical (the deletion is
   consumption-side; the annotate pass's absence must not change
   verdicts on well-formed streams), plus the standard battery; the
   erasure finally recovers the de-gating's +55 % init-full
   certified cost by deleting the per-declaration inference sweep —
   re-measure then.

### Stage 6 landed: the annotations are gone (2026-08-26, task #100)

**Landed** (branch `feat/100-stage6`; gates: `lake build` warning-free,
`lake test`, arena 90/92, e2e 67/67, axioms exactly `[propext,
Classical.choice, Quot.sound]`, no `sorry`s, init-prelude
byte-identical — stdout, stderr and exit code — to master@3c883f3 in
**both** modes, 3653 declarations accepted).

**What is gone.**

* `BinderMeta.cod` / `IBinderMeta.cod` are **deleted fields**, not
  stored-as-`none`: both structures are now single-field records
  carrying only the display `BinderInfo`, and `denoteBM` is the
  identity on them (`ArenaWF.lean`).  `ENode`'s binder constructors
  carry the same erased meta, so the arena stores no annotation and
  the codomain-chain fast path (`internExprFast`/`internBMFast`) is
  deleted with it — `internExpr` everywhere.  Storage is uniformly
  raw on **every** install path: nothing rebuilds, decorates or
  re-annotates a binder, because there is nothing to put there.
* The **cod memos** are deleted: `codOfCore` (spec), `codOfBodyI` /
  `codOfI` and the `IState.codOfC` table (interned), `memoLI`, the
  fueled family `codOfF` and its depth-invariance/monotonicity
  lemmas, `ISOK`'s `codOfC` clause and `ISOK.insertCodOfC`, and the
  `codOfI_sim` walk.  Architecture 4 needs no `codOf` oracle, so the
  whole certificate apparatus for a decoration pass goes with the
  pass it would have fed.
* The two annotation *loads* die as planned: the λ-annotation
  re-check is gone (`inferBody`'s lam clause is the official-kernel
  `infer_lambda` shape — domain sort-checked, body inferred, ∀ rebuilt)
  and the ∀-imax cod read is gone (the ∀-clause **infers** its
  codomain sort; on the interned side that is the new `inferPisI`
  telescope loop, mirrored and verified like the λ one).  `etaCert`'s
  cod-agreement comparison and the defeq binder cod comparison are
  both gone.
* Model side: `annotate_sound` is **deleted**.  Its role is taken by
  `inferTypeCore_sound`, which no longer *consumes* an `AnnotOk` for
  its subject but *establishes* it — the inference run is the
  truthfulness witness.  `AnnotOk`'s binder clauses carry no level
  witnesses and no fibre-universe facts; its app clause is the
  domain-relative slot `∃ vf va A B, … ∧ vf ∈ˢ piC A B ∧ va ∈ˢ A`.
  Dead annotation hypotheses were deleted from `structUnit_sound`,
  `extend_proj_fn`, `ctor_pkg_nested`, `modeled_bottom_nested` and
  `modeled_rule_eq_nested` rather than underscored.

**What survives, and why (a finding) — and the name is now a
misnomer.**  Read this before reading any code that mentions
`annotate`: **`annotateCore` / `ops.annotate` / `annotateBodyI` compute
no annotation and store no annotation.  There is no annotation.  The
name is a leftover and is scheduled for a rename** (`normalizeCore` /
`ops.normalize` / `normalizeBodyI` — filed as its own mechanical task;
it did not ride along with this tentpole).  Do not infer from the
identifier that binder annotations still exist anywhere: they do not,
`BinderMeta` has one field, and every sort is inferred on demand.

The pass itself is not deleted, and cannot be: with the annotations
erased, its remaining clauses are the ones that change the
**skeleton** of the input, plus the leaf checks that only it is
positioned to make.  All four are **input normalization**, and the
first is permanent by the user's own goal statement:

1. the **projection rewrite** (`annotateProjElim` /
   `annotateProjRec`) — permanent per the #107 audit: modeled
   structures can never get a first-class `.proj`, and the Prop
   template tail is kernel-parity;
2. **zeta** — `letE` bodies are normalized to their zeta reducts;
   opened opaque let-variables reject real streams;
3. the **literal-support guards** (`Nat`/`String` literals are
   well-formed exactly when their basis declarations are stored);
4. the **`fvar` leaf scope check** — this pass is the entry point raw
   input passes through, so a dangling free variable in the input is
   rejected here.

Everything else in the pass is now structural recursion: the binder
clauses rebuild, the app clause annotates its two children (the
`annotateSpine`/`annotateSpineI` telescope walk is **deleted** — the
application rule's checks live in the driver's inference sweep, which
re-checks every argument unconditionally since the de-gating), and the
`letE` clause's own type/value checks moved to `inferBody`'s `letE`
clause (official `infer_let` order).  So the honest statement of the
end state is: **no annotation is computed or stored anywhere; every
sort the kernel needs is computed on demand by `infer` at the consumer
site; what used to compute them survives only as an input normalizer
that still, misleadingly, carries the name `annotate`.**

**Remaining cosmetic vestige.**  The level-erased abbrevs
`pi (_v) A B := piC A B` and `lam (_v) A F := lamC A F`
(`Derive/Pi.lean`) still stand at their ~2000 model-side call sites.
They are `noncomputable abbrev`s — reducible, so goals already display
`piC`/`lamC` and no proof depends on the discarded level.  Deleting
them is a pure rename across the model layer with no verdict, proof or
performance consequence; it is deliberately **not** part of this
stage and is filed as its own mechanical task.

**Not re-measured here.**  The stage's cost claim (the erasure
recovers the de-gating's +55 % init-full certified cost by deleting
the per-declaration inference sweep) is a measurement, and
measurements trail merges: init-full and `perf stat` runs were not in
this gate loop.

### Stage 3 finding: the λ-cod re-check is NOT flip-deletable; `AnnotOk` keeps a subset-form cod tie at ∀ (2026-08-25, task #100)

The stage-3 plan moved two deletions into the flip.  Executing it
split them:

* **The defeq binder cod comparison deleted, as planned.**  With the
  collapse ops the binder clauses' soundness closes by `piC_congr`/
  `lamC_congr` (no zero-agreement input), so the comparison is gone
  from `isDefEqCore`'s forallE/lam clauses (spec, interned twin, NC),
  and defeq matches the official kernel's no-annotation-comparison
  behavior.  `pi/lam_congr_zero_agree` retired with it.
* **The λ-annotation re-check is load-bearing through stage 5 and is
  restored** (`Kernel/Core.lean` lam infer clause, `inferLamsOutI`).
  The plan's argument ("`lamC` membership has no level") covers the
  membership conclusion but not `InferClaims`' *output* `AnnotOk`
  conjunct.  Two countermodels close all the alternatives:
  - the ∀-infer clause still reads the stored cod for the imax rule,
    and its membership conclusion (`piC A B ∈ univ ((imax u v₀).eval
    φ)`) is **false under a fully untied `AnnotOk`** — untruthful
    `cod = 0` over `Type`-level fibres gives a big `piC` that is not
    a truth value.  Type-expr *arguments* consume exactly this
    membership (app-slot at the defeq-checked domain), so it cannot
    be weakened away: `AnnotOk`'s ∀-clause must tie its level witness
    to the stored cod;
  - with the tie, the λ-infer clause's freshly built ∀ (reusing the
    λ's meta) needs `⟦bt⟧ ∈ univ (v.eval φ)` per domain member —
    obtainable *only* from the re-check's own inference chain
    (`ihi` at `bt` + `sort_result` + `isEquiv_sound`); no semantic
    invariant of the λ can supply it (the body's *type placement* is
    a fact about the kernel-computed `bt`, and kernel-run-mentioning
    invariant clauses do not transport across substitution — the
    subject-reduction bridge again).  Cert-driven re-inference inside
    whnf/defeq (proj/pairEta on inferred-type subterms) forces
    infer's output `AnnotOk` to be full-strength, so no
    weak/strong-split assignment is consistent either.

  The re-check and the ∀-imax read die *together* in stage 6, where
  the ∀-clause infers its codomain sort and the tie becomes
  self-establishing.
* **Modeled Eq-statement domains must be certified** (same collapse
  root cause, `lam_dom` fully dead): the modeled fold derivations
  (`modeled_bottom_plain/nested`, `eta/unit_rule_fold`,
  `proj_bottom`) used to pin the equation arguments' memberships off
  the *value* of the pinned `Eq` former.  Replacements, checked at
  install: `checkIotaThm(N)` and `checkProjIota` run
  `checkIotaSidesTy` at the opened statement telescope (both equation
  sides' inferred types ≡ the equation type — kernel certificates the
  soundness layer walks through `inferTypeCore_sound` +
  `isDefEqCore_sound`); `checkEtaThm`/`checkUnitThm` pin the
  statement's *type slot* syntactically (the family application), so
  those fold proofs read the domain off the pin and the walk's own
  frame memberships.  All four reject only statements the
  preprocessor never emits.  A syntactic pin for `checkProjIota`
  (field domain lifted past the remaining binders) was tried first
  and *rejects real streams* — the preprocessor emits hygienic binder
  names inside Π-shaped field domains (`Order.lt`'s
  `a._@…._hyg.0`), and dependent field types spelled through the
  earlier projections (`Subtype.property`'s slot is
  `p (Subtype._model.proj_0 … (Subtype.mk._model … v pr))`, not the
  lifted domain) — so the projection path certifies definitionally.
  `proj_bottom` consumes the rhs certificate over the statement's
  *own* opening: `openPisAtFvars` on the theorem type is `ErasedEq`
  to the master frame index-by-index (`instPisAt_erasedEq_spines`),
  `self_walk` establishes the opening's typing package from the
  master memberships transported along `interp_erasedEq`, and the two
  soundness lemmas pin the projected field's value into the equation
  type's value.
* **The tie's shape** (`Model/Interp.lean`): the ∀-clause's level
  witness gains one conjunct — `∃ vE, (∀ v, m.cod = some v → univ vE
  ⊆ˢ univ (v.eval φ)) ∧ ∀ x A, …` — a *subset-form* fact outside the
  domain quantifier, so establishment costs one small obligation per
  ∀-node (identity when the witness is the cod's evaluation;
  `univ_mono zero_le` at `vE = 0`; `univ_mono` by case-split + omega
  against the simplified raw-eval defs) instead of a duplicated
  fibre proof, and the conjunct is vacuous once annotations are
  erased.  The λ-clause carries no tie.

### Stage 2 record: kernel de-gating landed; two deletions are flip-blocked (2026-08-24, task #100)

**Landed.**  The three collapse-falsified annotation gates now run
their certificates unconditionally, in the spec core, the interned
core and the NC twins alike:

* **guarded beta** (`whnfCoreBody` app/lam, `whnfAppI`/`betaPeelI`) —
  every redex pays infer+defeq of the argument against the domain; the
  `mb.cod`/`isNonZero` read is gone (NC still beta-reduces
  unconditionally, now without the cod-presence read);
* **guarded projection** (`whnfCoreBody`/`whnfCoreBodyI`/NC proj
  clause) — `projCert` runs at every table-driven reduction; the
  `structSort`-nonzero skip is gone (`projCertI` stays outside the NC
  skip list, as before);
* **the #49 app-spine/iota gates** — `codNonZero`/`codNonZeroIM` are
  deleted; `iotaCertsG`/`iotaCertsGI(Aux)` are deleted with all call
  sites on the ungated `iotaCerts`/`iotaCertsI`; `inferBody`'s app
  clause and `inferSpineI` re-check every argument.

Verification shrank as predicted: the certify arms were the already
verified ones, so the change is mostly deletion — the gate-recovery
theorems (`certsG_fit` and its domain-determination proof,
`iotaCertsG_step_inv`, `codNonZero_eq_true`, `codNonZeroIM_eff`, the
gated `_atF`/`_snoc`/`_shift`/`_disc`/`_sim` branches across
`Verify/BetaSpine`, `Verify/Deep`, `Verify/Disc`, `Verify/DiscI1/3/4`,
`Verify/Fueled`, `Verify/PairM`, `Verify/SimI`) are gone, and the
model's beta/proj/app-slot proofs keep only the certified branch
(`Model/Core/Whnf.lean`, `Model/Core/Infer.lean`, `Model/Core/Iota.lean`
now consume `certs_fit`).  The domain-determination *lemmas* on the
`SetTheory` side (`lam_dom`, `graph_dom_of_mem_piSet`, …) remain for
the flip stage's false-surface accounting.

**Finding — the other two stage-2 items are load-bearing pre-flip.**
The plan also called for deleting the defeq binder cod comparison
(the zero-ness form) and the λ-annotation re-check in the lam infer
clause.  Both are *formally blocked* while the model is leveled, for
the reason the scout finding above already recorded on the defeq side:
`AnnotOk` supplies only cumulative `univ`-memberships, from which
zero-ness of a stored level is not recoverable.

* *defeq*: the binder clauses' soundness concludes
  `pi (v₁.eval φ) A B = pi (v₂.eval φ) A B` via
  `pi_congr_zero_agree`, whose zero-agreement input comes exactly from
  the retained comparison.  Countermodel to the deleted form: cods
  `param u` vs `zero`, both truthful over all-`pt` fibres (`pt ∈ univ 0
  ⊆ univ 1`); at `u ↦ 1` the interpretations are `piSet`-of-graphs vs
  a truth value — defeq true, interpretations unequal.
* *λ-re-check*: `interpExpr` reads the λ's **stored** cod `v`, while
  the certified fibre-universe fact is stated at the **recomputed**
  sort `v'`; the re-check's `Level.isEquiv v v'` is what transfers it
  (`Model/Core/Infer.lean`, `Level.isEquiv_sound heqv φ`) so that
  `lam (v.eval) A F ∈ pi (v.eval) A B` closes.  Without it, stored
  `v = 1` over a proof-valued body (truthful: the Prop is in
  `univ 0 ⊆ univ 1`) makes the λ a graph while the built Π interprets
  at the recomputed level 0 — membership fails.

Both deletions become sound exactly at the flip (level-free
`piC_congr`; `lamC` membership has no level), so they move into
stage 3, where `pi/lam_congr_zero_agree` retire with them.  The
migration-order text above is annotated accordingly.  Note the
asymmetry that fixes the order overall: the *gates* are falsified *by*
the flip (must de-gate before), while the *comparisons* are required
*until* the flip (must delete at/after) — stage 2 is exactly the
falsified set.

**Measured cost (this stage alone, annotate pass still running).**
Verdicts and outputs are byte-identical to master everywhere: arena
90/92, e2e 64/64, `lake test`, scale harness all-PASS
(thm 1.01/fields-raw 1.92/ctors-mod 2.68/fields-mod 2.06, all under
gates), and both init probes byte-identical in both modes.
Instructions (`perf stat -e instructions:u`, median of 3,
init-core probe):

| binary | certified | NC |
|---|---|---|
| master (c57da48) | 3.92 G | 3.01 G |
| de-gated | 4.89 G (**+24.7 %**) | 2.98 G (−1 %) |

init-full (61 048 declarations, single runs, output byte-identical in
both modes):

| binary | certified instr | certified wall | NC instr | NC wall |
|---|---|---|---|---|
| master (c57da48) | 230.1 G | 3:50 | 210.1 G | 3:30 |
| de-gated | 357.0 G (**+55.1 %**) | 5:57 | 208.7 G (−0.7 %) | 3:29 |

Peak RSS is unchanged (≈6.0 GB tree total in both).  The
certified-mode cost is the predicted tight-domain-loss price of
running the possibly-Prop certificates everywhere (scout: +26.2 % beta
+ ≈13 % spine/iota on the 2026-08 master; today's master is ~7× faster
in absolute terms, so the same absolute certificate work weighs more
relatively — +24.7 % on the mostly-Prop-light prelude, +55 % on the
full stream, whose defeq-heavy tail previously skipped certification
at almost every nonzero-annotated redex).  NC is flat-to-slightly
faster: it never ran these certs, and the beta path lost its cod read.
The end state recovers more than this: stage 6 deletes the annotate
pass (a full inference sweep per declaration) and the per-binder cod
storage; this stage's number is the *gate cost now*, reported on its
own as ordered.


## The snapshot bracket is the default, verified (2026-08-24, task #64 landing)

The mode-4 tier bracket (in-place value-pipeline snapshot + promotion,
the measurement winner: 23.2 % retained nodes / −57.5 % peak RSS /
+3.14 % instructions on the Mathlib prefix) is now THE default driver,
and the flag-on regime is fully verified — `checkDeclsSP_sound` /
`no_proof_of_Empty_SP` cover the shipping binary at exactly
`[propext, Classical.choice, Quot.sound]`.  The `SETLEC_TIER_BRACKET`
knob and modes 1–3 are retired; the measurement tables above remain
reproducible at the pre-flip commit 2794be4.

**The verified pipeline.**  `checkDeclSP` dispatches def/thm/opaque
values through the named seams `openSnapshotM` → `bracketValB4`
(annotate, post-annotate guards, readback, infer, defeq — shared
def/thm middle) → `closeSnapshotM` (harvest tier two, truncate in
place, flush the `EIdx`-carrying memos, promote the stored output's
sub-DAG); opaques discard via `closeDiscardM`.  The pinned-cert
branches (Nat-op/div-mod/reduce) and the install-only kinds run the
unbracketed `checkDeclSPPlain` — their dispatch conditions moved to
the *static header name* (`checkConstantValP` preserves it), so the
rare branch no longer re-runs the header check and the walks reuse the
Plain simulation whole.

**The verification battery, as landed** (each item its own commits):

1. *Tier-aware denotation.*  `EStore.denoteT` reads the dispatching
   `getNode` and recurses along the traversal order `emlt`; on `WF`
   stores it IS `denote`, on `TWF` stores it agrees with `denote` at
   every even index.  `Ext` gained the tier-two prefix clause and flag
   preservation (interns never flip the mode; the seams are
   deliberately *not* extensions).  The whole op-spec battery
   (IExpr/IExprOps/ILevel/ParseP walkers), the interned-core
   invariant `ISOK` (now `TWF` + `denoteT` clauses; the `ienv` clause
   alone stays on tier-one `denote` and survives the close) and the
   DiscI/knot/bridge chain were restated over `(TWF, denoteT)` — the
   flag-off proofs are the even-index special case, and
   `denoteT_some_inv` hands each traversal proof its `emlt` guards
   directly (most proofs got *shorter*).  Boundary walks thread the
   declaration-boundary flag-off witness along `Ext.flag`
   (`tierOffE`/`tierOffExt`), converting `denoteT` facts back to
   tier-one facts at the record states.
2. *Promotion correctness* (`Setlec/Verify/Promote.lean`):
   `promoteE_spec` — the index-memoized re-intern of a tier-two
   sub-DAG into any store carrying the snapshot's tier-one
   denotations yields a `WF` extension whose result index denotes,
   tier-one, exactly the snapshot's tier-aware denotation;
   `promoteLGo_lt`/`promoteNGo_lt` are the level/name identity claims
   (harvest-time bases bound every reference, `TWF.t_levels_lt`).
3. *Seam state theory* (`Setlec/Verify/BracketB4.lean`):
   `ISOK.enable` (the mode switch is invisible to every denotation),
   `ISOK.truncFlush` + `closeSnapshotM_eff`/`closeDiscardM_eff` (flush
   the `denoteT`-based caches — exactly the `EIdx`-carrying ones —
   truncate, promote; the level caches and `ienv` survive), and the
   `KeepsO` raw-table preservation that reconstitutes `Ext` across a
   whole bracketed declaration (tier two empty and flags equal at both
   ends).
4. *Driver walks.*  `bracketValB4_eff` decomposes the bracketed middle
   run and returns the fueled annotate/infer/defeq runs at one joined
   fuel; the val-sims assemble the generic `checkDefnVal`/`checkThmVal`
   /`checkOpaqueVal` runs from them, and `checkDeclSP_sim` feeds the
   unchanged consistency fold.

**Verdict identity and cost, re-measured post-flip.**  The flipped
binary is byte-identical (stdout+stderr+exit) to the pre-flip default
on init-core and on the 12 M-line Mathlib prefix (both accept 101,326
declarations); arena 90/92 + e2e 64/64, `scale.sh` PASS.  Instructions
(`perf stat -e instructions:u`, init-core `--pre`, median of 3):
7.0489 G bracketed vs 7.0489 G unbracketed — **+0.002 %**, far inside
the measured +3.14 % envelope (the envelope was measured at 94d0aa7
against a pre-merge baseline; the interim master perf work also
removed most of the bracket's re-walk overhead).  Peak RSS on the
log2 Mathlib prefix (`time -v`): 2.63 GB bracketed vs 6.31 GB
unbracketed — **−58.4 %**, the mode-4 profile as measured.

## Install/check separation and selective checking (2026-08-26, task #108)

The parked riders of task #64 (`--install-only`, `--check-range`) land,
on the counter mechanism the user settled there: **entries carry their
installation counter, and visibility is a bound consulted inside
`find?`** — not a filtered view, not a second `FEnv` value, not a
rebuilt environment.

**The structure** (`Setlec/Kernel/CoreI.lean`).  `FEnv.idx` maps a name
to `(counter, ConstantInfo)`, where the counter is the number of
constants installed before it — its position counted from the bottom of
`env.consts`.  `FEnv` gains `visibleBelow : Nat`, and `find?` returns
`none` for an entry whose counter is at or above it.  `visibleBelow`
doubles as *the next counter to hand out*, so `FEnv.push` is still one
`HashMap.insert` plus a field bump and the ordinary install-and-check
path keeps `visibleBelow = env.consts.length` — nothing is ever hidden
there, and `mkFEnv_push` is still `rfl`.  Restricting is
`FEnv.restrictTo k`, an `O(1)` field update on the single linearly
threaded index.  Blast radius: `.idx` is touched in exactly two places
(`find?`, `push`); every other consumer goes through `mkFEnv_find?` /
`mkFEnv_push`, so `Setlec/Verify/*` and `Setlec/Model/*` compiled
untouched.

**The meaning of the bound** (`Setlec/Verify/EnvBound.lean`, spec-side
only).  `idxSpec` is what the index holds; `Env.prefixTo k` is the
environment truncated to its first `k` installed constants (`consts` is
newest-first, so the prefix is the *tail*).  Three theorems:

* `mkFEnv_find?` — with nothing hidden the index *is* `Env.find?`
  (the pre-#108 statement, re-proved through the counters);
* `mkFEnv_find?_visibleBelow_some` — **unconditional soundness**:
  anything a bounded lookup returns is exactly what `Env.prefixTo k`
  returns.  A bounded lookup therefore *cannot* reach a constant
  installed at or after the bound.  This is the no-circularity fact:
  no declaration can be justified by one installed later.
* `mkFEnv_find?_visibleBelow` — the full equivalence
  `bounded find? = find? in the truncated environment`, under name
  uniqueness.  The hypothesis is exactly right and not a weakening:
  without it the only thing a bounded lookup can miss is an *older*
  constant shadowed by a same-named newer one — i.e. it returns
  *less*, the safe direction — and the checker rejects duplicate names
  at insertion (`checkConstantValP`), so the situation never arises on
  a stream it accepted.  (Invariant established at insertion, not a
  per-call gate; threading a `Nodup` invariant through the whole
  checker is a separate task and buys nothing the soundness direction
  does not already give.)

Plus `restrictTo_push_find?`: pushing the constant installed at counter
`k` onto the view at bound `k` is the same as raising the bound to
`k+1`.  That is what lets a re-check walk a declaration's *provisional*
environments (the two views `fe`/`fe2` the pinned-certificate branches
use) without pushing anything at all.

**The driver** (`Setlec/Kernel/Split.lean`, unverified debug path; the
default binary path is untouched and byte-identical).  Phase one
installs every declaration — syntactic guards, annotation, the
`IState.ienv` recording, the push — skipping every
`infer`/`defeq`/`ensureSort` call, and records for each declaration the
number of constants installed before it.  Phase two replays the check
phase of the selected declarations against the **final** environment
restricted to each declaration's own recorded bound, reusing the
annotated type/value indices phase one recorded (nothing is
re-annotated except an opaque's discarded witness).  The pinned
certificate branches (structural `Nat` ops, div/mod, `reduce*`
opaques) are check phase too and are replayed at the same two views the
interleaved driver used, `restrictTo k` and `restrictTo (k+1)`.
`flushS` runs at every step of both phases, so no memo entry ever
crosses a bound change.

*Rejected: hoisting the pinned branches into the install phase.*  The
first cut ran them wholesale at install, because `nat_add_levelpoly`
diverged — the interleaved driver *declines* at `natOpGuardF`, while a
split driver that installed `Nat.add` unguarded then reported a later
theorem as *invalid*.  Hoisting hides the divergence at the cost of a
silent coverage hole in exactly the feature whose purpose is selective
checking: `--install-only` would not actually be install-only, and
`--check-range` would leave those declarations permanently unchecked.
Replaying the branch at the two bounded views fixes it at the root
instead — `Nat.add`'s own check-phase guard now fires first, so the
stream declines as it should.  Evidence that the certificates really
run from the bounded view, not vacuously: `--check-range 484:485` on
the 562-declaration `nat_mod_perturbed` fixture reports
`unsupported Nat.div/mod spelling (Nat.mod)`.

*Not separable, by construction* (caveat 1): inductive blocks, basis
blocks and axioms validate their conditions as they are installed
(positivity, the provisional-environment walks, the standard-axiom
pins), so phase one runs the ordinary driver on them and phase two has
nothing to re-check.  `--check-range` covering an inductive block
therefore checks nothing extra there.  **Diagnostic-only**: a split run
never returns 0 and the interleaved path is byte-identical, so this
costs coverage of a *diagnostic* mode, never of a verdict.

**Env-extent audit** (the security argument).  Every environment
consultation the check phase performs is bounded, because on the
shared-state path there is exactly one environment value in scope:

1. *All lookups go through `FEnv.find?`.*  Every raw-`Env` guard family
   (`Setlec/Kernel/Core.lean`, `Checker.lean`, `StdAxioms.lean`,
   `TrustAxioms.lean`, `Direct.lean`, `Modeled.lean`) has an `F`/`S`
   mirror taking `fe` — `constsResolveFI`, `natOpGuardF`,
   `stdAxiomOkF`, `divMod*GuardF`, `reduce*OkF`, `directNonRecF`,
   `installProjTemplateS`, … — and only the mirrors are called from
   `checkDeclSP`/`recheckDeclSP`.  `findCV?` and `findProj?` are
   defined *in terms of* `find?`, so they inherit the bound.
2. *The `Env` arguments threaded to `CheckerOps` methods are inert.*
   `sharedOps fe` ignores its per-call environment argument and always
   uses the `fe` it was built with, so `ops.inferType fe.env …`,
   `checkDefEqList ops feSelf.env …`, `certifyNatEqs ops fe.env …`
   (the helpers pass `env` only to `ops` methods) all run at the
   bounded index.  `fe.env` is never *read* on this path except by
   `FEnv.push` and the final `pure fe.env`.
3. *`IState.ienv` is not an environment.*  It is name-keyed and
   contains every installed constant, but it is only ever reached
   *after* a successful `fe.find?` returned the constant, and the entry
   is then pointer-validated against the very object that lookup
   returned (`storedTyIdxM`/`storedValIdxM`); a mismatch falls back to
   a fresh interning.  It can therefore never introduce a constant the
   bounded lookup did not already yield.
4. *No memo entry crosses a bound.*  The environment-dependent caches
   (`constTyAt`, `constValAt`, `ruleRhsAt`, `whnfCoreC`, `whnfC`,
   `inferC`, `defeqC`, `annotC`) do not mention the environment in
   their keys and are flushed at every declaration step of both phases,
   exactly as in the interleaved driver.

The audit's empirical counterpart: the split driver at full range
agrees with the interleaved driver on **all 67 e2e fixtures** (modulo
`0 ↦ 2`, below) and reproduces every rejection and decline, including
the ones that turn on the pre-push/post-push distinction.  A wrongly
hidden constant would have shown up immediately as a spurious "unknown
constant".

**Exit-code discipline.**  Exit 0 means *everything in this stream was
checked and accepted*, so a split run never returns 0 — even at
`--check-range 0:` (the split driver is not the verified one).  A run
that checked less than the whole stream also never returns 1: a
skipped check might have *declined* first, which is the checker's
honest verdict, so a partial run downgrades `invalid` to a decline and
lets the message name the declaration.  `notImplemented` stays 2 and
`internal` stays 3 throughout.  `--yolo` cannot be combined with the
split flags.

Residual, documented divergence (caveat 2): at full range the split
driver can surface an install-phase error of a declaration *later* in
the stream than the one the interleaved driver stopped at (installation
no longer stops at the first failed check).  No e2e or arena fixture
exhibits it.  **Diagnostic-only**, for the same two reasons: a split
run never returns 0, and the interleaved path — the one whose verdict
the consistency chain covers — is byte-identical to master.  Both
caveats are therefore accepted as costs of a diagnostic mode, not of a
verdict.

**What it buys.**  `--check-range 484:485` on a 562-declaration stream
checks *one* declaration — `Nat.mod`, pinned certificate and all — and
reports its failure, after an install pass that costs a fraction of a
full check (init-prelude: 0.84 s install-only vs 3.1 s full).  That is
the frontier-investigation tool: reaching declaration N no longer
means re-checking the N−1 before it.

## Step-budget reduction loops: fuel stops being depth (2026-08-26, task #106)

**Scope, stated up front: this task did NOT clear the `Std.Time`
frontier.**  The two engine defects below are fixed and verified, and
the measurement stands, but at the default `checkFuel` the declaration
`Std.Time.Second.Offset.toDays._proof_1` still exits 3.  The *cause*
has been reclassified: it is not fuel accounting but the
**certified-mode tax** (task #90, ~42x by the table below), and the
frontier is reassigned there.  #106 is "engine work done, frontier
reassigned" — nothing in this section should be read as clearing it.

`checkFuel` is the knot's structural fuel: every call through the
`CoreFns` record costs one unit.  Before this task the *reduction
chains* went through the record too — `whnfCore`'s beta/iota/zeta/proj
chain, `whnf`'s literal-acceleration/delta loop, `defeq`'s lazy-delta
loop — so an ordinary unfolding chain cost one unit of the shared
**recursion-depth** budget (and one native stack frame) per *step*.
An unremarkable declaration could exhaust `checkFuel` without any
recursion being deep.

lean4lean makes exactly this distinction and is the model followed
here (`Lean4Lean/FuelConfig.lean`): local `while`-style loops get their
own step budgets (`FuelConfig.whnf = 100000`,
`FuelConfig.lazyDelta = 1000`), while `Methods.withFuel`
(`recDepth = 10000`) bounds only genuine mutual-recursion *nesting*.

### The shape: continuation-parameterized loop bodies

Each loop is split into a **step body with the continuation
abstracted** — the module's own open-recursion idiom, one more
parameter alongside the record `r` — and a **loop** that iterates it on
a budget:

* `whnfCoreStepM`/`whnfCoreLoopI` (interned; `whnfAppI`/`betaPeelI`
  thread the continuation, and their termination measures go back to
  the plain `(args.length, phase)` of task #50),
* `whnfStep`/`whnfLoop` (spec and interned),
* `defeqStep`/`defeqLoop` (spec, interned, cert-skipping).

Only the spine *head*'s normalization stays a knot call.  Because the
continuation is abstract, every existing proof battery applies with one
extra hypothesis about `k` (`PairM`'s `fst_step4k`/`snd_step4k` and
`Fueled`'s `atF_step4k` are the level-4 cascades parameterized over one
extra alternative), and each loop lemma is a plain induction on the
budget.  The budgets are `@[irreducible]`: the `Verify/Knot.lean` `rfl`
equations must not try to evaluate them, and proofs that need to peel
one iteration use the `*_succ` positivity witnesses instead.

### The idiom, named: open recursion one level down

This factoring is **the pattern for introducing any future loop into
the core**, not a one-off for this task.  The module's whole discipline
is that a body never calls itself — recursion is routed through the
`CoreFns` record `r`, and fuel lives only in the knot that ties it.  A
loop is the same situation one level down: the loop body must not call
*itself* either.  So abstract the loop's continuation as `k`, exactly
as `r` abstracts the knot's, and let a separate two-line `Loop`
function tie `k` to the budget.

The payoff is that `k` behaves like `r` in every proof battery.  Each
existing per-body lemma survives with **one extra hypothesis about
`k`** — a projection equation for `PairM`, an `atF` equation for
`Fueled`, a `SimAt` for the interned walks — and the loop lemma is then
a plain induction on the budget with that hypothesis discharged by the
induction hypothesis.  Concretely, `PairM`'s `fst_step4`/`snd_step4`
and `Fueled`'s `atF_step4` were re-expressed as `*_core4`, a macro
taking one extra tactic alternative, so `*_step4` is
`*_core4 (fail)` and `*_step4k hk` is `*_core4 (rw [hk])`: the
rewrite lists are not duplicated, and the cascades stay the same
cascades.  **That the batteries needed a parameter rather than a fork
is the evidence the factoring is right**; if a future loop cannot be
expressed this way, that is a signal to re-examine the loop, not to
duplicate the batteries.

Threading the *budget* through the loop bodies instead (the first
attempt) forces a lexicographic termination measure on the mutual
block and makes every battery induct on two things at once.  The
continuation form keeps `whnfAppI`/`betaPeelI` at task #50's plain
`(args.length, phase)` measure.

**`whnfCore` is looped on the interned side only.**  Its specification
body stays chained, because the refinement bridge is existential in the
knot fuel: `Verify/BetaSpine.lean` mirrors the loop at `Expr` level
(`whnfCoreStepM`/`whnfCoreLoopM`) and `whnfCoreLoop_ksound` /
`whnfCoreLoop_sound_body` reproduce a successful *loop* run by the
chained `whnfCoreBody` at some fuel — the same device task #50 used for
bulk beta, now also absorbing the loop steps.  `whnfApp_ksound` /
`betaPeel_ksound` are the new piece: they turn a run whose continuation
is merely *sound* into a run whose continuation **is** `whnfCore`, so
the existing `snoc`/`sound` machinery is unchanged.

**The obvious alternative is false — do not re-attempt it.**  The
tempting move is to thread *two* continuations through
`whnfApp_snoc`/`betaPeel_snoc` (the hypothesis run at `k`, the
conclusion's prefix run at a refined `k'`).  It does not work at budget
0: `betaPeel_snoc`'s `[]`-with-lambda-head case must produce a `w` with
`betaPeel … t acc [] = .ok w`, and that is `k' ((lam …).instantiateList
acc)` — so the conclusion needs the continuation to be **identity on
lambdas**, which the budget-0 continuation (a `throw`) is not.  Worse,
the hypothesis can hold *without ever calling the continuation* (the
beta certificate fails and the clause returns a stuck application), so
the lemma is genuinely false there rather than vacuous.  Every repair
along that line — budget monotonicity, continuation refinement,
reindexing the induction to keep the budget ≥ 1 — ends up needing the
soundness of the *same* budget it is proving.  Converting the run to
the `whnfCore` continuation up front sidesteps all of it, because
`whnfCore` **is** identity on lambdas (`whnfCore_lam`) and its
soundness is trivial.

Resisting the symmetry is the general lesson here: the specification
side is not looped because the bridge does not need it to be, and
making it symmetric would replace an existential over knot fuel with a
bounded budget that cannot absorb the interned side's different step
count (bulk beta counts *groups*, the chained spec counts *binders*).

### Eagerness the reference kernels do not have (Defect B)

* **Lazy delta decides before it materializes.**  `unfoldableHead`
  (official `is_delta`, lean4lean `isDelta`) is a pure head read; the
  unfolding is built only inside the branch that consumes it, and the
  same-head `defeqSpine` short-circuit runs *before* any unfolding, as
  `try_eq_const_app` does.  The former spelling built both sides'
  unfoldings in the match scrutinee before choosing a branch.
* **Stuck applications compare spine-wise** (`is_def_eq_app`): equal
  spine lengths, one head comparison, arguments pairwise
  (`defEqList`).  The former spelling recursed `defeq` on the *partial*
  applications, re-entering the whole body — syntactic fast path, two
  `whnfCore`s, proof irrelevance (two inferences!) and a lazy-delta
  decision — once per spine position, at one knot level each.  Nothing
  is lost: `whnfCore` has already normalized the function parts, and
  the `unfoldableHead` guards read the *head* constant, which the
  partial applications share.  Model side: `defeqApp_values`
  (`Model/Core/Certs.lean`) — both sides are the set-application fold
  of the head value over the argument values, and the folds agree
  componentwise.

### Measurement (the evidence, and the escalation for task #90)

`_tmp/std-time-cone/pre2.ndjson` — the 4215-declaration `Std.Time`
cone, progress mode, this machine:

| build | checkFuel | result |
|---|---|---|
| master | 100 000 | exit 3, `toDays._proof_1` (50 s) |
| master | 3 000 000 | accepted, 3 m 38 s |
| B1+B2 only | 200 000 / 400 000 | still exit 3 |
| **full change set** | 100 000 | still exit 3 |
| **full change set** | 200 000 | **accepted**, 3 m 51 s |
| full change set, `--yolo` | 100 000 | **accepted, 5.4 s** |

Instrumented maximum knot depth with the loops in place: **≈ 175 000**
(nothing below 2 830 000 of a 3 000 000 budget).  That is **2 × 86 400**
— seconds per day.  `Std.Time.Second.Offset.toDays` divides by 86 400,
and the residual depth is `defeq`/`infer` walking a `Nat.below` `PProd`
tower of height 86 400, one to two knot levels per tower level,
comparing a `Nat.below`-form side against a `Nat.rec`-form side (they
never become pointer-equal, so the whole tower is descended).

**That residual is genuine mutual-recursion nesting, not step
counting**: no budget change can turn it into iteration, and the
official kernel would recurse just as deep if asked.  It is only
*asked* because of our proof-feeding certificates (the per-argument
inference re-check — the deferred infer-only mode — the beta
certificate, and the iota telescope certificates).  `--yolo` skips
exactly those and checks the same stream in 5.4 s versus 3 m 51 s: a
**~42× certified-mode tax**, on the same engine and the same stream.
**Amendment (task #134): ~42× is too large a label for "tax".**
`--yolo` also drops the per-argument check at the driver's *front
door*, which the reference kernels perform; the mode that keeps it and
drops only the internal re-checks runs the same stream in 1 m 51 s.
The certified-mode tax on this stream is therefore **~1.9×**, and the
remaining ~20× is engineering gap on checks the references also run —
see "The infer-only mode: SETLEC_INFER_ONLY (task #134)".
That is the sharpest evidence yet for task #90 (*certified-mode tax —
reuse reductions between check and cert paths*), and it is where the
frontier actually lives.  It is also the measurement that makes a
further question worth asking, now under separate investigation:
whether a **TT-based soundness proof** could carry a well-typedness
invariant *through* reduction instead of re-deriving it at each node —
which would potentially validate a `--yolo` run outright, i.e. collapse
the 3 m 51 s column into the 5.4 s one rather than merely narrowing it.
See `Setlec/TT/DESIGN.md`.

**A failing stream now takes longer — this is not a regression.**  The
default-fuel run over `pre2.ndjson` went from 50 s (master) to 2 m 44 s
(here) *while still exiting 3*.  That is the intended consequence of
the loops: the same declaration now reduces far deeper before the
**nesting** budget runs out, so the checker does much more real work
before erroring.  Accepting runs are unaffected — init-prelude is
byte-identical in both modes and unchanged in wall time, and the arena
and e2e suites are unchanged.  A future reader benchmarking a *failing*
stream and finding it slower is measuring how much further the engine
got, not a slowdown.

`checkFuel` is therefore deliberately left at **100 000**.  Raising it
is a band-aid that will break: the required depth is proportional to a
numeric *literal* in the proof (86 400 here; `Std.Time` also deals in
nanoseconds, 86 400 000 000 000 per day), so no constant we could pick
survives the next declaration of this shape.

### Riders

* **Diagnostic second-pass misattribution.**  `Main.lean`'s `diagLoop`
  was handed `store2.raw.nodes.size` as the in-range bound where the
  verified run passes the *encoded* bound (`2 * nodes.size`, task #64
  low-bit), so `checkDeclSPStep` rejected the first declaration whose
  encoded indices exceeded it with "parsed declaration index out of
  range" and the second pass reported a declaration that never failed.
  **`instShiftRightUInt32` — long recorded as the "next blocker" after
  `toDays._proof_1` — was a phantom of exactly this bug**: it is what
  master's second pass printed, not what failed.  With the bound fixed
  the second pass agrees with progress mode.
* **Task #61 gate defect.**  The `majorToCtor` eta rescue's non-Prop
  guard is the *instantiated* `piResultNeverZero cvT.levelParams ust`
  test, not the static `piResultIsProp cvT.type = false`: a parametric
  `Sort u` passes the static test and is exactly the case a `Prop`
  instantiation collapses.  Mirrored into all three bodies
  (`majorToCtor`, `majorToCtorI`, `majorToCtorNC`) — a gate that is
  instantiated in one mirror and static in another is worse than
  either — and the now-redundant copy in the 0-field sub-branch is
  gone.

## The `.proj` clause certifies the constructor telescope (2026-08-26, task #126)

**The first change the TT bridge (task #119) asked of the checker — a
design output rather than a verification result.**

`whnfCoreBody`'s `.proj` clause reduces `proj i p` by whnf-ing the
subject to `e'`, matching `e'.getAppFn` against the table entry's
constructor, and running `projCert`.  `projCert` checks *levels*: the
field's type's sort against the entry's pinned `fieldSort` and the
subject's type's sort against its `structSort` — the collapse guard,
which is what the set model consumes (`projCert_inv` feeds
`Nat.max … = 0`; the memberships come from `AnnotOk`'s own `.proj`
clause, which inference establishes).

The layer's rules for the same reduction (`projFstMk`/`projSndMk`,
`Setlec/TT/*`) name four premises about the reduct's components, with
`⟦e'⟧ = psigmaMkT u v A B a b`:

```
⊢ A : .sort u    ⊢ B : arrow A (.sort v)    ⊢ a : A    ⊢ b : .app B a
```

`projCert` supplies **none of the four**: it never checks the sorts of
the parameters `A` and `B`, and its own typing fact is the field at its
*inferred* type rather than at the domain the rule names.  Those four
premises are exactly the four telescope domains of `PSigma'.mk`'s
stored type, so **one `iotaCerts` call on the constructor spine**
produces all of them — the call `iotaRec` already makes for its
constructor telescope, which the `.proj` clause did not.  That is
`projTeleCert` (spec), `projTeleCertI` (interned), run after `projCert`
and gating the reduction the same way.

**This is not a soundness bug, and the phrasing matters.**  Nothing
here says the reduction is wrong; the checker simply *certified less
than its rule needs*, so a typing derivation could not be rebuilt from
what it recorded.  A reader who finds this section must not go looking
for an unsoundness that is not there.  The set model is unaffected —
it never consumed the missing facts, and `Setlec/Model/Core/Whnf.lean`
takes the new conjunct as `-`.

Merely checking that the reduct's *inferred type* is pair-headed would
not do: by the bridge's "premises are supplied where the rule fires",
a typing at some other domain cannot be moved to the pinned one, so the
descent to the components would stay unjustified.

**Mirrors and their asymmetry.**  Spec (`Setlec/Kernel/Core.lean`),
interned (`Setlec/Kernel/CoreI.lean`) and the pure `whnfCoreStepM`
mirror (`Setlec/Verify/BetaSpine.lean`) all run it.  `CoreNC.lean`
**skips** it: the cert-skipping measurement mode exists to price the
calls that are there only for the proofs, and this is an `iotaCertsI`
telescope certification — the very family NC already skips at
`iotaRecNC`, `structEtaCertWithNC` and `structUnitCertNC`.  The
references reduce a `.proj` node by direct field selection and certify
nothing (lean4lean `projectCore`; official kernel `whnf_core`'s proj
case), so keeping it in NC would inflate the "verification tax" number
with work no reference kernel does.  (`projCertI` stays in NC: it is
outside the task-#76 site list, reported there as residue.)

**Verification.**  The proof-side mirrors are mechanical: `projTeleCertP`
+ fold (`Verify/Knot.lean`), `projTeleCert_atF` (`Fueled.lean`),
`_fst_proj`/`_snd_proj` (`PairM.lean`), `_mono` (`BetaSpine.lean`),
`_shift` (`Deep.lean`), `_disc` (`Disc.lean`), `projTeleCertI_sim`
(`DiscI2.lean`) and the `.proj` clause of the interned walk
(`DiscI4.lean`).  `whnf_proj_inv` grew one conjunct, and
`projTeleCert_inv` (`InferLemmas.lean`) turns a successful run into the
constructor lookup plus the `iotaCertsP` fact — the entry point for
`certs_fit` (set model) and `certs_typed` (bridge).

**Measured** (init-prelude probe, `perf stat -e instructions:u`, median
of 3; 188 `proj` records in the stream):

| mode | before | after | delta |
|---|---|---|---|
| certified | 33.891 G | 33.940 G | **+0.145 %** |
| `SETLEC_NO_PROOF_CERTS=1` | 11.501 G | 11.501 G | 0.00 % (skipped) |

Verdicts unmoved: init-prelude stdout/stderr byte-identical in both
modes, arena 90/92, e2e 67/67, split driver 11/11.  A telescope
certification that *failed* on real input would have shown up as a
decline here — it does not, which is the evidence that the checker was
always in a position to write these facts down.

## The `.proj` clause certifies the parameters' sorts (2026-08-26, task #129)

**The bridge's second request of the checker, and the sibling of task
#126 on the *inference* path.**  Read that section first: everything
about the framing carries over, including the phrasing that matters.

`inferBody`'s `.proj` clause types a projection node from its
projection-table entry: it whnfs the subject's inferred type, matches
the head against the table, checks the parameter and level counts, and
reads the field's residual off `entry.ty` with `piResidual`.  The
layer's rules for the same node (`projFst`/`projSnd`,
`Setlec/TT/Judgment.lean`) carry three premises:

```
⊢ A : .sort u      ⊢ B : arrow A (.sort v)      ⊢ p : psigmaT u v A B
```

The clause established the **third** — the head match *is* that fact —
and neither of the first two: it never inferred anything about `A` and
`B`.  Again this is not a soundness bug; the clause **certified less
than its rule needs**, so a typing derivation could not be rebuilt from
what it recorded.  The set model is unaffected (it takes these facts
from `AnnotOk`, and `Setlec/Model/Core/Infer.lean` takes the new
conjunct as `-`).

**The repair is one `iotaCerts` call, and it lands on `entry.ty`.**
The pinned first-projection type is

```
∀ {α : Sort u} {β : α → Sort v}, PSigma' α β → α
```

whose first `numParams` telescope domains are `Sort u` and
`α → Sort v` — *exactly* the two missing premises.  So the same
telescope walk `projTeleCert` makes at the redex, run here at
`entry.ty.instantiateLevelParams entry.levelParams us` against
`te.getAppArgs`, supplies both.  That is `projParamCert` (spec),
`projParamCertI` (interned), run after the count checks and before
`piResidual`, and it throws `.invalid` on failure like the application
rule's per-argument re-check.

**Why `iotaCerts` and not two `ensureSort`s** (the request's own
wording, `Setlec/TTVerify/DESIGN.md` §10.3): an `ensureSort` on `B`'s
inferred type cannot even be *stated* — `⊢ B : arrow A (.sort v)` is
not a sort judgement — and on `A` it would yield `⊢ A : .sort u'` at
the *inferred* level, which §10.1's rule ("premises are supplied where
the rule fires") forbids moving to the pinned `u`.  The telescope walk
gives each parameter its typing at the domain the rule names, and it
lands in currency the bridge already consumes: `iotaCertsP` →
`certs_typed` → `TeleTyped`, the same chain task #126 opened.

**Do not "simplify" this back to two `ensureSort`s.**  It looks like the
cheaper spelling of the same check and is not: it reintroduces the level
gap above, which no lemma in the bridge can close.  The two calls the
clause makes are an `infer`+`defeq` pair per parameter either way, so
there is nothing to win.

**Mirrors.**  Spec (`Setlec/Kernel/Core.lean`) and interned
(`Setlec/Kernel/CoreI.lean`) run it; the interned side reuses the `pty`
it already computed for `piResidualM`, so it costs a walk and no
lookup.  There is no `whnfCoreStepM`-style third mirror on this path.
`CoreNC.lean` **skips** it, and the judgement was made rather than
inherited: both references (`Lean4Lean`'s `inferProj`, the official
kernel's `infer_proj`) peel the telescope with
`r := binding_body(r).instantiate1 args[i]` per parameter, with no
`infer` and no `isDefEq` on `args[i]` — the parameters are substituted,
never typed.  The rationale is recorded in `CoreNC.lean`'s header
beside the task-#126 entry.

**The reduction path is untouched**: `whnfCoreBody`'s `.proj` clause
already has `projCert` and `projTeleCert`.

**Verification.**  `projParamCertP` + fold (`Verify/Knot.lean`),
`projParamCert_atF` (`Fueled.lean`), `_fst_proj`/`_snd_proj`
(`PairM.lean`, both cascades), the shift step inside `inferBody_shift`
(`Deep.lean`, via `iotaCerts_shift` at the entry's closed type),
`projParamCert_disc` (`Disc.lean`) and `projParamCertI_sim`
(`DiscI2.lean`, consumed by `DiscI4.lean`'s interned inference walk).
`inferTypeCore_proj_inv` grew one conjunct — existing consumers take it
as `-` — and `projParamCert_inv` (`InferLemmas.lean`) is the bridge's
direct entry point, turning a successful run into the `iotaCertsP`
fact.

**Measured** (init-prelude probe, `perf stat -e instructions:u`, median
of 3; 188 `proj` records in the stream):

| mode | before | after | delta |
|---|---|---|---|
| certified | 33.931 G | 33.966 G | **+0.102 %** |
| `SETLEC_NO_PROOF_CERTS=1` | 11.501 G | 11.501 G | 0.00 % (skipped) |

Verdicts unmoved: init-prelude stdout/stderr byte-identical in both
modes against a binary built from pre-change master, arena 90/92, e2e
67/67, split driver 11/11.  As at #126, a parameter certification that
*failed* on real input would have surfaced here as a rejection — it
does not, which is the evidence that the checker was always in a
position to write these two premises down.

## `pairEtaCert` certifies its own type arguments (2026-08-26, task #130)

**The bridge's third request of the checker, and the last of the
`iotaCerts`-family gaps.**  Read the task-#126 and task-#129 sections
first: the framing, the phrasing and the NC judgement all carry over.

`pairEtaCert` rescues a definitional equality between a fully applied
pinned pair constructor `a = PSigma'.mk pα pβ s₁ s₂` and a stuck `b`.
It ran four `defeq`s — `pα ~ A`, `pβ ~ B`, `s₁ ~ b.1`, `s₂ ~ b.2`,
where `PSigma'.{us'} A B` is the whnf of `b`'s inferred type — and
nothing else.  The rule those four justify is the layer's structure-η

```
psigmaEta : ⊢ A : .sort u → ⊢ B : arrow A (.sort v) →
            ⊢ p : psigmaT u v A B →
            ⊢ prf : eqE (psigmaT u v A B) p (psigmaMkT u v A B p.1 p.2)
```

whose third premise the inference of `b`'s type supplies, and whose
first two nothing supplied.  The certificate **certified less than its
rule needs**.  Not a soundness bug — nothing says the rescue is wrong,
only that a typing derivation could not be rebuilt from what the
checker recorded.  The set model is unaffected: `pairEta_sound`
(`Model/Core/PairEta.lean`) takes the two memberships from `AnnotOk`'s
*application* clause on `PSigma'.{us'} A B`, and takes the new
conjuncts as `-`.  Requested by the TT bridge, task #119,
`Setlec/TTVerify/DESIGN.md` §13; the premises are consumed twice over
by `psigmaEta_law`, so they are not droppable decoration.

**Why the bridge cannot reconstruct them.**  `HasType.app` fixes an
argument's type to the domain of the function type *used in that
application*, and a derivation of the whole application existentially
quantifies that domain away — so the layer will not let the bridge
descend into `PSigma' A B`'s derivation to recover `⊢ A : Sort u`.
Facts about arguments have to be certified where they are used.  The
set model's `AnnotOk` is exactly the annotation-truthfulness the bridge
dropped; re-importing it would be a large change buying one clause.

**The repair is task #129's certificate, verbatim.**  The pair type
*is* the native projection entry, so `projParamCert entry us' [A, B]`
— one `iotaCerts` walk on
`entry.ty.instantiateLevelParams entry.levelParams us'` — delivers both
premises at the domains the rule names.  The bridge-side conversion
already exists (`projEntry_tele_premises`, `Setlec/TTVerify/ProjStep.lean`),
so the pair's projection certificate and its η certificate now consume
the same evidence.  `projParamCert`/`projParamCertI` moved up in
`Core.lean`/`CoreI.lean` to sit above their new first caller; the
definitions are unchanged.

**Two deliberate deviations from the request's wording.**

* **The levels are `us'`, the *type*'s, not `us`, the constructor's.**
  `A` and `B` are the arguments of `PSigma'.{us'}`, and `psigmaEta`
  names its premises at the levels of `p`'s type; instantiating the
  entry at `us'` lands them there with no transport.  The two lists are
  `Level.isEquiv`-compared one line earlier, so this is a choice of
  spelling, not of strength.
* **Failure is `pure false`, not `.invalid`.**  Unlike #129's
  `inferBody` clause, `pairEtaCert` is a *rescue attempt*: `stuckIrrel`
  tries it in both argument orders and then four more certificates.
  Throwing would reject inputs that the reverse direction or a later
  rule still accepts.  For the same reason the call sits **last**,
  after the four `defeq`s: the verdict is unchanged either way, but
  running it last means it only fires on rescues that would otherwise
  have succeeded, and leaves the existing calls' error behavior exactly
  as it was.

**Mirrors.**  Spec (`Core.lean`) and interned (`CoreI.lean`, which
recovers the entry's type with the same `projFnIdxM`/`constTyAtM` pair
`inferBodyI` uses) run it.  `CoreNC.lean` **skips** it, and this mode
needed a new twin `pairEtaCertNC` — until now NC reused `pairEtaCertI`
outright, on the recorded grounds that it "performs no work the
references' `tryEtaStructCore` would not".  That claim was checked
again and is still true of the four `defeq`s and false of the new call:
lean4lean's `tryEtaStructCore` and the official kernel's
`type_checker::try_eta_struct_core` run one
`isDefEq (inferType t) (inferType s)` plus a per-field `isDefEq`
against the projections, and **never infer or compare the structure
type's parameters on their own**, let alone against a telescope.  The
parameter comparisons stay in NC (they are the interned spelling of
that single type-level `isDefEq`); the telescope walk goes, like every
other `iotaCertsI` in that mode.  Rationale recorded in `CoreNC.lean`'s
header.

**Verification.**  `pairEtaCert_fst_proj`/`_snd_proj` (`PairM.lean`)
and `pairEtaCert_atF` (`Fueled.lean`) unfold `projParamCert` so the
existing `iotaCerts` cascade steps apply; `pairEtaCert_shift`
(`Deep.lean`) gains an `iotaCerts_shift` step at the entry's closed
stored type; `pairEtaCert_disc` (`Disc.lean`) gains a
`projParamCert_disc` step (that lemma moved above its new first
caller); `pairEtaCertI_sim` (`DiscI2.lean`) gains the
`projFnIdxM_eff`/`constTyAtM_eff`/`projParamCertI_sim` walk and now
takes `EnvWF` (both call sites in `stuckIrrelI_sim` already had it).
`pairEtaCert_inv` (`InferLemmas.lean`) grew two conjuncts — the entry
lookup and the certificate — and `projParamCert_inv` converts the
second for the bridge with no new entry point.

**Measured** (init-prelude probe, `perf stat -e instructions:u`, median
of 3):

| mode | before | after | delta |
|---|---|---|---|
| certified | 37.682 G | 37.696 G | **+0.037 %** |
| `SETLEC_NO_PROOF_CERTS=1` | 15.221 G | 15.222 G | 0.00 % (noise; skipped) |

Cheaper than #129 (+0.102 %), as expected: pair-η rescues are rarer
than projection inferences, and the walk is two domains long.

Verdicts unmoved: init-prelude stdout/stderr byte-identical in both
modes against a binary built from pre-change master, arena 90/92, e2e
67/67, split driver 11/11.  The evidence is not vacuous — `e2e`'s
`psigma_rec_eta` fixture exists precisely to force a defeq-side pair-η
rescue at a neutral major, and it still accepts, so the new
certificate *succeeds* on a real firing rather than never running.

## The `V`-free checker-inversion tier moves to `Setlec/Verify` (2026-08-26, task #123)

`Setlec/Model/Extend/*` was written where its consumers were, not where
its statements belong.  Task #119's scout measured the consequence
(`Setlec/TTVerify/DESIGN.md` §14.1): the tier is checker *inversion* —
every `check*_inv` and every spec `Prop` is over `Env`/`Expr`, with no
valuation anywhere — and the declarative bridge, which may not import
`Setlec/Model/*`, would otherwise have to duplicate it.  This task
relocated that content, verbatim, to `Setlec/Verify/`.

**The criterion is the statement, not the proof.**  A declaration moves
iff its type *and* its proof's constant cone reach neither the
`SetTheory` class nor `ConstVal V`.  That second root matters: a handful
of predicates (`BlockInstalled`, `ProjPhaseInv`,
`ConstValParams.recRules_swap`) are `SetTheory`-free but still range
over a valuation `ConstVal V`, and "`V`-free" is the layering rule, not
"`SetTheory`-free".  They stay in `Model`.  The set was computed
mechanically (least fixed point over `Environment` constant
dependencies), not by reading.

**What the move is allowed to change: nothing but the file.**  The
enclosing `variable {V} [SetTheory V]` disappears in the target module,
so the `omit [SetTheory V] in` lines that decorated most of these
lemmas are dropped — a scope directive, not part of a statement.  The
purity claim was *checked*, not asserted: a structural dump of every
constant's `levelParams` and type, before and after, differs on eight
constants and only in hygienic binder names (`inst._@.…_hygCtx…`) —
i.e. nowhere modulo α.  No constant is added or removed apart from
renumbered `match_` auxiliaries.

**Shape.**  `Setlec/Verify/Extend/{Inversions,Iota}.lean` are whole-file
relocations (both modules were 100 % inversion); `Decl`, `Ind`,
`Modeled`, `Proj`, `Recs`, `Sibs`, `Transport` split, the `Model` file
keeping the valuation-carrying half and importing the `Verify` one.
Three enabling modules came out of files outside `Extend/`, because the
inversions depend on them: `Setlec/Verify/IotaWalkInv.lean`
(`DefEqListOk`/`TypedListOk`/`AnnotListOk` and their inversions, from
`Model/IotaWalk.lean` — without them 800 lines of `Extend/Iota.lean`
could not move), `Setlec/Verify/EnvPreds.lean` (`BasisBlocks`,
`RecCtorsStored`, `ProjOk`, `uN`/`vN`/`u1N`, `ConstantInfo.isBasis`) and
`Setlec/Verify/EnvGuards.lean` (`natLitSupported_inv`/`_congr`, the
`strLit` pair, `EtaFamilyStored`).

`Model/Extend/{Inversions,Iota}.lean` survive as import shims: their
siblings inherit `Model.*Install` and `Model.IotaWalk` through them, and
deleting them would push those imports around for no gain.

4 259 lines left `Setlec/Model/*`; the `annotOk_*` tier and every `*_sound` are
untouched, as they must be.  No `Setlec/Verify/*` module imports
`Setlec/Model/*` or `Setlec/SetTheory/*` (checked by grep), and no
checker source changed at all, so verdicts cannot have moved.


## pt-freshness: the proof-point re-choice and the battery (2026-08-26, task #109)

**Landed** (branch `feat/109-pt-freshness`; gates: `lake build`
warning-free, `lake test`, arena 90/92 / e2e 67/67 / split 11/11,
axioms exactly `[propext, Classical.choice, Quot.sound]` on the
consistency theorems and on every new lemma, init-prelude
byte-identical — stdout, stderr, exit — to master in both modes.  The
checker has no `SetTheory` import, so byte-identity is structural; no
kernel file changed.)

The proof point is re-chosen so that **no data-value encoding produces
it**, making "data values are never `pt`" provable — the foundation
both for restoring the de-gated possibly-Prop reduction gates (task
#100 stage 2 measured their removal at +24.7 % probe / +55.1 %
init-full certified) and for the task-#124 guard-clear route (iii).

### The re-choice, and the selection principle

`pt := {ptTag}` with `ptTag := {∅, {{∅}}}` (`Derive/Pt.lean`; the old
`pt = {∅}` **was** the von Neumann numeral `1` — `fun _ => (1 : Nat)`
interpreted to `pt`, so a freshness battery over it would have had to
exclude `Nat` itself).  The constraints, stated as the **selection
principle** because the next re-choice needs the criterion more than
the choice:

1. `pt` must be a singleton `{t}` whose tag `t` has an *empty member*
   (so neither `t` nor `pt` is a Kuratowski pair — pair elements are
   nonempty; the same anti-pair trick as the old `pt`, one level up);
2. `t` must not be a singleton (`{{a}} = kpair a a`, a writable pair
   value — this killed the `{{ω}}` candidate: `{{ω}} = ⟦⟨Nat, Nat⟩⟧`);
3. `t ≠ ∅` (`{∅} = vnat 1`, the old collision) and `t` must not
   itself be a writable value (`{vnat 2}` is the writable quotient
   class of `Quot.mk (· = 2 ∧ · = 2) 2` — killed that candidate);
4. **`t`'s members must not cohabit any writable type** — else `pt`
   is a writable singleton quotient class over that type.  Every
   rejected candidate died to a *writable* value; this clause is the
   generalizable content.  `ptTag`'s members `∅` (a `Nat` value) and
   `{{∅}} = kpair ∅ ∅` (a pair value) share no writable host — only
   `Type` holds both, and pinning `{{∅}}` there needs a type-equality
   to an unwritable type;
5. `t` must be hereditarily finite, so `IsTGUniverse.pt_mem` (and the
   whole `unitSet`/`univZero`/`truthVal` universe-closure chain)
   survives for arbitrary inhabited TG universes — this killed `{ω}`
   (false in `V_ω`), which also had a writable type-level collision:
   `⟦Quot (fun _ _ : Nat => True)⟧ = {ω}` — squashed `Nat` *was* that
   candidate `pt`.

Blast radius, measured: `pt` is irreducible, and its ∅-content was
consumed at exactly three sites outside `Pt.lean` (`graph_ne_pt`,
`ne_pt_of_mem_piSet`, `sigmaSet_ne_pt` — all re-proved via the tag's
empty member) plus the Collapse.lean evidence.  The Model layer
(65 k lines) needed **zero** changes.  `Collapse.lean`'s witness
lemmas restate (`lamC_witnesses_distinguished`: the `Nat` witness is
now a genuine graph, the `Prop` witness still collapses — the collapse
never *needed* the identification, only level-freedom; Horn A
re-proves through the tag's memberwise recursion).

### The battery (`Derive/PtFresh.lean`)

Collision lemmas per encoding: `vsucc_ne_pt` (succ images fresh even
off `ω`), `vnat_ne_pt`, `pt_not_mem_omega`, `pt_not_mem_sigmaPairs`,
`pt_not_mem_sigmaSet_pos`, `pt_not_mem_piSet`, `pt_not_mem_univZero`;
type-former values `omega`/`univ n`/`piC` are never `pt`
(`piC_ne_pt` is new and unconditional).  `PtFresh T := pt ∉ˢ T` with
`ne_pt_of_mem_fresh` (the namesake), the **existential** pi clause
`ptFresh_piC_iff : PtFresh (piC A B) ↔ ∃ x ∈ A, PtFresh (B x)`
(negation of `pt_mem_piC_iff` — over an empty domain every product
collapses, so nonemptiness is part of any sufficient condition), and
the consumer under-approximation `ptFresh_piC_of` (uniformly fresh
fibres over a nonempty domain).  **The nonemptiness conjunct is what
re-blocks the #100 de-gating countermodel by name**:
`(fun (x : ∀ p : Prop, p) => Prop) Prop` has `⟦∀ p : Prop, p⟧ = ∅`,
the ∃-inhabitant fails, and no restored gate can fire on it — the
gate that was unsound returns with precisely the premise whose absence
made it unsound.

Domain determination (task #124 route (iii)): `piSet_dom_eq` (graphs
determine domains *exactly*, both directions), `piC_dom_eq_of_ne_pt`
(a non-`pt` member of two collapsed products pins the domains equal),
`mem_dom_of_piC_of_ne_pt` / `mem_dom_of_piC_fresh` (the ambient
argument fact transfers to any computed domain, `≠ pt` discharged by
freshness).

### Hard walls (forced, recorded so they are not re-attempted)

* `pt ∈ univ (u+1)` is **forced** for every buildable proof point
  (`univZero ∈ univ 1` + transitivity ⟹ `unitSet ∈ univ 1` ⟹
  `pt ∈ univ 1`): sorts above `Prop` are never fresh
  (`not_ptFresh_univ_succ`), while `Prop` itself **is**
  (`ptFresh_univZero` — truth values are never `pt`, so predicates
  `A → Prop` keep genuine graph values, matching the old
  nonzero-sort classification of `Prop : Sort 1`).
* Unit-likes are non-fresh **by design** (`⟦PUnit⟧ = {pt}`,
  `not_ptFresh_unitSet`); inhabited propositions likewise.
* Quotients are not unconditionally fresh for *any* constructible
  `pt`: `quotSet_eq_pt_countermodel` (`Derive/Quot.lean`) exhibits
  `quotSet 1 ptTag R_total = pt` — classes are arbitrary nonempty
  definable subsets of the base.  **Never resurrect a
  `quotSet_ne_pt`**; the old `pt = {∅}` was the unique choice immune
  (∅ is never a class), which is exactly what the re-choice trades
  for data freshness.  The countermodel base is not a writable type —
  the obstruction is semantic, in the ∀-A-R quantification.

### The syntactic guard (authoritative clause list)

The consumers' static test, to be implemented with the gate
restoration (soundness `ptFreshTy env T = true → interp T = some vT →
PtFresh vT`): **fresh** — pinned `Nat`, `Empty`; `PSigma` at
`Level.isNonZero (max u v)`; `Sort 0`; `Π x:A. B` with `B` uniformly
fresh and `A` env-derivably nonempty (pinned inhabited basis types,
inductives with a constructor of nonempty argument types, pis into
nonempty, sorts).  **Excluded** — sorts ≥ 1, `Quot`, unit-likes,
props, variable-headed types, and (pending the install artifact
below) modeled inductives.  Note the convergence: the `PSigma` clause
is the *same* all-assignments `isNonZero` level test as the old
`codNonZero` gate — the battery's static tests converge on the old
gates' tests because both under-approximate the same semantic
boundary (which fibres can contain the proof point).  The task-#124
census classifier aligns with this list.

### Deferred (filed, not implemented here)

Modeled inductives need an **install-time freshness artifact**: the
opaque-model interface (mem_type + proj/iota/eta) cannot yield
`PtFresh ⟦T⟧` — a unit-like modeled structure's value set is
`{pt}`-shaped, so no interface-only argument exists.  Direction
approved (capability-pipeline shape: run the syntactic test on the
model's basis-typed type-level definition at install, store the
verdict as a checked capability, as eta did); execution is its own
task with its own gates.  Until it lands, modeled types stay outside
the guard.

## The guard-capture census (task #124, 2026-08-27, diag/124-guard-census)

Measured verdict on the static-guard route for skipping the `inferSpineI`
per-argument re-check: **the guard captures ~0% of the app-argument tax,
and Std.Time — predicted near-total — is the *worst* stream.**
`perf stat instructions:u`, medians; verdicts identical in all 53 timed
runs (3653/6390/61048 accepted, no movement).

The current verification tax (baseline certified vs all-app-arg-masked):
init-prelude 33.83G → 13.85G (tax 59% of the run, 2.4×);
Std.Time pre2 1645.5G → 54.7G (97%, 30×);
init-full 3130.2G → 551.9G (82%, 5.7×).

Capture with a **free** guard (upper bound; measured guard overhead
5–9% makes net negative everywhere): init-prelude 7.4%/4.1%
(G1/#109-clause guards), Std.Time 1.9%/1.0%, init-full 3.7%/1.5%.

**The mechanism — counts and cost are decoupled**: 54–70% of re-check
*sites* clear the guard, carrying ~0% of the *cost*. Guard-clear sites
are the **leaves** of the certificate recursion (infers of memoised
`Nat`/`Bool`/sort arguments); guard-kept sites are its **trunk** (the
`Nat.below`/`PProd` tower descents — `Nat.below` alone is 1.39M sites
on Std.Time). Masking the 61% of clear sites removes 5.6% of sites
*reached*; masking the 39% kept sites removes 82%. A static beta-peel
variant clearing 85.7% of Std.Time sites still captures nothing.

Residual at kept sites (Std.Time, #109 clauses): Sort≥1 21.4%
(hard wall), beta-redex domains 19.0%, other-inductive 12.1%,
recursor-headed 3.9%, Prop-typed 3.9%. The carved-universe option
(clearing Sort≥1 domains) is therefore also worthless for this
purpose: it moves sites, not cost.

Consequences: #124 route (iii) refuted by measurement; the certified
tax stands as the price of the only stateable soundness argument
(§ the certificate does the one thing nothing else can). #109's battery
retains its semantic value (domain determination, the restored-gate
option at ~5–8% free-guard ceiling on prelude-like streams — marginal
after guard overhead). Raw data: _tmp/census-124/, branch
diag/124-guard-census (never merged).

**What followed (task #134).**  With the guard route refuted here and
the metatheorem route refuted on `spike/inferonly-metatheory`, the
re-check ships as an *off-by-default mode* instead of a verified skip:
`SETLEC_INFER_ONLY=1` drops it at internal invocations only, keeping
the front door and every certificate family.  The census's
"all-app-arg-masked" column (init-prelude 13.85 G) is *not* what that
mode costs — it masks the front door too; the mode lands at 23.71 G.
The difference between those two columns is the front-door share,
which the reference kernels also pay: see "The infer-only mode:
SETLEC_INFER_ONLY (task #134)".

## The capability checks pin the model type's sort (2026-08-27, task #135)

**The fourth change the TT bridge (task #119) asked of the checker,
and the smallest — one `==` per check on values both checks already
computed.**  Siblings: tasks #126, #129, #130.

`checkEtaThmF` / `checkUnitThmF` (`Setlec/Kernel/CheckerS.lean`) pin
the shape of the model-side `T._model.eta` / `T._model.unitlike`
statement against the model former `T._model`.  Both stripped the
former's parameter telescope and threw the **residual away**
(`some (tbindersM, _)`), and both matched the statement's head as
`.const c [_ℓ]` and threw the **level away**.  Two computed-and-
discarded values, never compared — §0's third tell in
`Setlec/TTVerify/DESIGN.md`, read off the checker rather than off a
proof.

The bridge needs the comparison.  Each of `DeclIndTT`'s obligations
ends at a β-step whose premise is `Δ ⊢ Â : Sort ⟦ℓA⟧` — the equation's
type slot at *the level the statement's own `Eq.{ℓA}` carries*.  The
set model gets the corresponding membership from `AnnotOk`, which the
bridge dropped by design; and the natural replacement — inverting the
theorem's own derivation — is Π-injectivity, which `propext` refutes
in that layer.  A "stored types are types" invariant gives `Â : Sort u`
at *some* `u`; `u = ⟦ℓA⟧` is exactly the step nothing licenses.

**The check.**  Inside the statement-body match, where both values are
in scope:

```
tbodyM == Expr.sort ℓA
```

The type slot is already pinned (task #100) to `T._model p⃗`, so with
the residual pinned to `Sort ℓA` the slot's sort *is* the statement's
level, which is the fact the bridge consumes.  `EtaPins`
(`Setlec/Verify/Extend/Iota.lean`) gains `tbodyM = Expr.sort ℓA` as
the last conjunct of each half; `checkEtaThm_inv` / `checkUnitThm_inv`
forward it; `Setlec/Model/ModeledCaps.lean` takes it as `-` (the set
model never needed it and does not gain a proof obligation).

**Plain `==`, not `Level.isEquiv`.**  The requester measured the risk
before asking rather than arguing it: the two checks were instrumented
and the whole fixture corpus run — `_tmp/arena-tests` (182 streams,
including `init-prelude`) 347/347, `tests/e2e` 722/722, **1 069 calls,
zero counterexamples**.  Syntactic equality is what the real
preprocessor emits.  `Level.isEquiv` remains the fallback if a future
generator normalises levels differently; it would cost nothing.

**Mirrors — and there is no `CoreI`/`CoreNC` asymmetry to argue.**
This is an install-time syntactic `Bool` check, not a certificate, so
the cert-skipping mode is not a separate copy: `CheckerNC` calls the
*same* `indBlockCapsF`.  The surface is two places, both updated:

* `checkEtaThmF` / `checkUnitThmF` (`Setlec/Kernel/CheckerS.lean`) —
  the versions that execute, on both the S and NC drivers;
* `checkEtaThm` / `checkUnitThm` (`Setlec/Kernel/Modeled.lean`) — the
  `Env` versions.  These are never reached at runtime, but they are
  **not dead code to delete**: they are the domain of the two
  inversion theorems, pinned to the live ones by `checkEtaThmF_eq` /
  `checkUnitThmF_eq` (`Setlec/Verify/CheckerF.lean`).  Letting them
  diverge would break that pin, which is the point of having it.

`directCaps` (`Setlec/Kernel/Checker.lean`) needs nothing: the direct
simple-structure path claims neither capability.

**Gates.**  Build warning-free (touched oleans force-recompiled),
`lake test`, arena 90/92, e2e 67/67, split driver 11/11, infer-only
5/5 and the full `--infer-only` sweep, axioms exactly
`[propext, Classical.choice, Quot.sound]`, no sorries, init-prelude
byte-identical — stdout, stderr, exit — in the certified, the
`SETLEC_NO_PROOF_CERTS=1` and the `SETLEC_INFER_ONLY=1` modes against
a binary built from pre-change master.  Cost: 38.7993 G → 38.8037 G
instructions:u on init-prelude, **+0.011 %** (median of three) — an
`==` on two already-computed values, once per capability install.

**A byte-identical gate does not by itself prove a new conjunct
true**, only that no verdict moved — a capability silently dropped
everywhere would also be invisible if nothing consumed it.  So the
conjunct was negated and the binary rebuilt: init-prelude then
*rejects* (exit 1, at `PProd.rec._model`) and e2e falls to 29/67.  The
check is load-bearing and passes at the live sites; that is the
positive half of the measurement the byte-identity gate cannot give.

## The eta certificate certifies its own fabrication (2026-08-27, task #137)

**The `defeq` path was fabricating a constructor spine it never
typed.**  `Setlec/TTVerify/DESIGN.md` §14.7.8 established that
`majorToCtorI`'s eta rescue runs the task-#71 synthetic-spine
certificate and concluded "no checker change is owed for this
premise"; §14.7.10 (commit `0b409b2`) amended the conclusion, because
the callee has *two* callers and only one of them carries the guard:

| caller | line (pre-change) | constructor telescope certified? |
|---|---|---|
| `majorToCtorI`, eta rescue | CoreI:1251 | **yes** — `iotaCertsI … tyCtor (margs ++ projs)` two lines above |
| `structEtaCertI`, from `defeq` | CoreI:1111 | **no** — `infer b`, `whnf`, call |

`structEtaCertWithI` builds `projs = [proj_i targs b]` and compares the
constructor's field arguments against them, so the term
`c targs (proj_0 targs b) …` is *asserted* to be a well-typed
inhabitant of `T targs` — and on the `defeq` path nothing had checked
that spine against `c`'s own telescope.  The fix is the one line
§14.7.10 spelled out, placed in the **callee** so both consumers get
it, right after `projs` is built:

```lean
let tyCtor ← constTyAtM fe c cn us
if ← iotaCertsI r fe depth tyCtor (targs ++ projs) then …
```

**Measured before implemented.**  The check can only make the checker
stricter, so the thing to price was whether any accepted stream stops
being accepted.  An instrumented build ran the candidate certificate
at *both* sites and **discarded** its result (so instrumented verdicts
equal baseline verdicts), tagging each outcome with its caller:

| corpus | site | calls reaching the cert | `true` | `false` | throw |
|---|---|---|---|---|---|
| arena + e2e + split + infer-only sweep | `defeq` | 1 406 | **1 406** | 0 | 0 |
| arena + e2e + split + infer-only sweep | `major` | 276 | 276 | 0 | 0 |
| init-prelude, certified | `defeq` | 128 | **128** | 0 | 0 |
| init-prelude, certified | `major` | 19 | 19 | 0 | 0 |
| init-prelude, `SETLEC_INFER_ONLY=1` | `defeq` | 110 | **110** | 0 | 0 |
| init-prelude, `SETLEC_INFER_ONLY=1` | `major` | 19 | 19 | 0 | 0 |

**1 644 evaluations on the previously-unguarded `defeq` path, zero
counterexamples.**  (Entries into `structEtaCertWithI` are far more
numerous — 5 958 + 449 + 291 on the `defeq` path — most of them bail
at the capability guard long before the certificate; the table counts
the calls that actually reach it.)

**The caller-side call stays, and not out of caution.**  The two
spines *are* the same values: at the rescue site `a = fab =
c ust (margs ++ projs)`, so the callee reads back `c` and `ust` from
`fab`'s head and `targs = margs` from `tmaj`'s, `caps.etaCtor =
rl.ctor` and `caps.etaFields = cnF` are guarded, and `constTyAtM` is
memoised on `(nI, us)` — the callee's certificate is *literally the
same call*.  What is not the same is the **control flow**:
`majorToCtorI` gates the *whole* eta branch on it, so a failure
returns `major` immediately, whereas a failure inside
`structEtaCertWithI` falls through to the `caps.etaFields = 0` →
`proofIrrelI` rescue below.  Removing the caller's copy would make a
currently-unreachable rescue reachable — a verdict change, not a
redundancy elimination — so it stays.  Byte-identity therefore carries
no evidence about it either way, and that is stated rather than
implied.

**Mirrors.**  Three copies of this body exist and they were treated
differently, on the reason each exists:

* `structEtaCertWithI` (`Setlec/Kernel/CoreI.lean`) — the one that
  executes.  Changed.
* `structEtaCertWith` (`Setlec/Kernel/Core.lean`) — the `Env`/`Expr`
  spec the simulation and inversion theorems are stated against.
  Changed in step; letting it diverge would break the pin.
* `structEtaCertWithNC` (`Setlec/Kernel/CoreNC.lean`) — **unchanged by
  design**: this is the mode that prices out the `iotaCertsI` family,
  and it already skips the type-former and per-projection telescope
  certifications here, and `majorToCtorNC` already omits the
  caller-side one.  A mode that skips every other member of the family
  and keeps this one reports a meaningless number (the task-#126/#129
  judgement, applied again).

**What `SETLEC_NO_PROOF_CERTS=1` actually exercises: nothing of this.**
The instrumented run confirms it — that mode emitted *zero* trace
lines, because `structEtaCertNC` calls `structEtaCertWithNC`.  Its
byte-identity result is a control (the change did not leak into the
cert-skipping core), not a test of the new check.

**Verify fallout, and where the line was drawn.**  Three proofs about
the spec body needed the new step threaded through — `Deep.lean`'s
`structEtaCertWith_shift`, `Disc.lean`'s `structEtaCertWith_disc`,
`DiscI2.lean`'s `structEtaCertWith_unfold` / `structEtaCertWithI_sim`
— all mechanical (one `iotaCerts_shift` / `iotaCerts_disc` /
`constTyAtM_eff` + `iotaCertsI_sim` step apiece, plus hoisting the
already-present projection well-scopedness into a shared `have`).
`InferLemmas.lean`'s `structEtaCertWith_inv` steps *over* the new
certificate and its **statement is deliberately unchanged**: adding
the conjunct would break every existing destructuring of that
existential, and the conjunct is the bridge's to introduce when
`EtaLawTT` is re-signed (§14.7.10).  `Fueled.lean` and
`Model/Core/StructEta.lean` needed nothing.

**Gates.**  Build warning-free with the six touched modules' oleans
force-deleted and recompiled; `lake test`; arena 90/92; e2e 67/67;
split driver 11/11; infer-only 5/5 and the full `--infer-only` sweep
(90/92, 67/67); consistency axioms exactly
`[propext, Classical.choice, Quot.sound]`; no `sorry`s; init-prelude
byte-identical — stdout, stderr, exit — in the certified, the
`SETLEC_NO_PROOF_CERTS=1` and the `SETLEC_INFER_ONLY=1` modes against
a binary built from pre-change master.

**Cost: none measurable.**  init-prelude, `instructions:u`, median of
three: 38.8097 G before, 38.8036 G after — **−0.016 %**, i.e. inside
the run-to-run spread (the three samples straddle each other).  The
prior said the `defeq` path would run this far more often than the
rescue path and might need memoising; it runs it 128 times per
init-prelude and costs nothing, because everything it re-derives —
`constTyAtM`'s instantiation, and the `infer`/`defeq` of the very
arguments the surrounding `defEqList` just compared — is already in
the caches.  No memoisation is warranted.

**Negation probe.**  Byte-identity cannot show a new *check* is true,
only that no verdict moved, so the certificate was inverted
(`if !(← iotaCertsI …)`, which on this corpus is "always false" since
it never fails) and the binary rebuilt.  init-prelude then **rejects**
(exit 1, `type mismatch in definition PProd.rec._model`), arena falls
90/92 → **69/92**, e2e 67/67 → **29/67**, split 11/11 → 9/11,
infer-only 5/5 → 4/5.  The check is on the hot path for every
structure-eta defeq in the prelude, and it passes at every live site;
that is the positive half the byte-identity gate cannot give.

## The eta capability pins the constructor's residual (2026-08-27, task #136)

**#135's direct sibling, and the fifth change the TT bridge (task
#119) asked of the checker.**  Siblings: tasks #126, #129, #130, #135,
#137.  It landed on the second attempt, and the first attempt's
failure is the interesting part, so it is recorded rather than tidied
away.

**The gap** (`Setlec/TTVerify/DESIGN.md` §14.7.8–§14.7.11).
`EtaLawTT`'s eta-rescue branch fabricates the constructor spine and
gets, from task #71's synthetic-spine certificate, `⊢ fab : ⟦rest⟧`
where `rest` is the **constructor's telescope residual**.  The law's
premise wants `⊢ fab : T p⃗`.  Closing that needs "a stored
constructor's result type is its own family applied to the
parameters".  That fact is checked on the **direct** path —
`checkDirectCtor` (`Setlec/Kernel/Checker.lean:125`),
`cbody == directFam T lps nP nF` — and had no counterpart on the
**modeled** path, which is the one `EtaFoldTT` serves.  The
public → model chain (`checkMemberVal`'s `eqUpToNames`) transports a
shape but has nothing to transport *from*: models are stored opaque.

### The amendment trail

| | first attempt (`0afbd6a`, **not landed**) | landed |
|---|---|---|
| site | `indBlockCaps`/`indBlockCapsF`'s `eta` field | `checkIndDecl`'s single-constructor branch, after the member fold |
| subject | `cvC.type` — the **raw**, pre-install constructor | the **stored** constant, read back with `find?` |
| guard | a conjunct of the capability | `if caps.eta` on a hard install check |
| verdict | rejected by the requester | granted |

**The spec error, and why it matters.**  §14.7.9 requested the check
"where the data lives", `indBlockCapsF`, and measured it there — on
`cvC.type`.  But `CtorResidualPin` (`Setlec/TTVerify/DeclInd.lean`),
the bridge-side premise, is about the constructor's **stored**
`ConstantVal`.  Those are two different syntactic objects: the
environment contains only what `checkMemberVal` stored, which is
`checkConstantVal`'s **annotated** output, and every consumer reads
*that* — `constTyAt` at the fire site, and `EnvWF`, `has_type`,
`denote_declType` behind it.  **The raw type is never in the
environment.**  So checking it cannot avoid a bridge lemma
("annotation preserves a constructor's residual"); it can only add
one, over cod annotations, #85's pending `Level.simplify` and #117's
survivors — a lemma nothing else needs and that rots silently when
annotation changes.  The rule the episode yields: *check the object
the consumer reads*, and name the object precisely enough that
"measured" and "specified" cannot drift apart.

The generalisable half is not "look harder" (that was §14.7.8's
lesson).  It is that a fact is **about an object**, and a loose name
for the object — "the constructor's type" — silently admits two
different ones.

### The measurement, redone at the new site

Instrumenting the new site has *both* types in hand, so the re-run
reports them side by side.  Corpus: all 182 arena streams plus the 67
`tests/e2e` fixtures at their declared modes, **1356 single-constructor
modeled blocks**:

| `eta` | `unitlike` | raw residual is `directFam` | **stored** residual is `directFam` | blocks |
|---|---|---|---|---|
| true | false | true | true | 957 |
| true | true | true | true | 18 |
| false | true | true | true | 72 |
| false | false | true | true | 218 |
| false | false | **false** | **false** | **91** |

Three readings.

1. **The capability guard is load-bearing.**  975/975 eta-capable and
   90/90 unit-capable blocks satisfy the property; all 91 failures are
   blocks with *neither* capability, and they are exactly the *indexed*
   families — `Acc`, `HEq`, `Int.NonNeg`, `IndexedSingleton`,
   `IndexedUnit`, `SortElimProp`, `SortElimProp2` and the `_wcore`
   copies — whose residual is `T p⃗ i⃗`.  Unguarded, this check rejects
   91 real sites.  The suite would go green on the guarded form and red
   on the unguarded one, and only counting told which.
2. **Raw and stored never disagree**: 0 differences in 1356 blocks.
   That is free evidence about the annotate-shape question — and
   precisely *not* a licence to check the raw object, because the
   evidence is a corpus fact and the requirement is a proof obligation.
3. The numbers differ slightly from §14.7.9's (1377 blocks, 978/99)
   because that sweep and this one enumerate the corpus differently;
   the shape of the answer is identical.

### The check

`ctorResidualOk` (`Setlec/Kernel/Modeled.lean`) / `ctorResidualOkF`
(`Setlec/Kernel/CheckerS.lean`):

```
!eta ||
(match env'.find? ctorName with
 | some (.ctorInfo cvCA _ _) =>
   (match cvCA.type.stripPis (nP + nF) with
    | some (_, cbody) => cbody == directFam T lps nP nF
    | none => false)
 | _ => false)
```

fired once per single-constructor modeled block, between the recursor
group and the projection-family freshness check:

```
unless ctorResidualOk env₃ cvT.name cvC.name cvT.levelParams nP nF
    caps.eta do
  throw (.notImplemented "modeled structure: eta constructor residual")
```

The `find?` is not incidental: it *is* the point.  It reads the
constant exactly the way `constTyAt` reads it, so the inversion hands
the bridge `CtorResidualPin cvT.name cvT.levelParams cvCA nP nF` for
the very `cvCA` the environment holds — the discharge is `exact`, in
the shape `CtorResidualPin` was fixed in advance to have.

**A deviation from the ruling's letter, with its reason.**  §14.7.11
placed the check at the *member install* (`checkIndMember`), where the
annotated `cvA` is created and the guard would read
`ci.name == caps.etaCtor && caps.eta`.  `checkIndMember` does not have
the family name `T` in scope, and `IndCaps` does not carry it, so the
family the residual must name is unavailable there; threading a `T`
parameter would touch 46 call shapes and 121 references across
`Setlec/Model/*` and `Setlec/Verify/*`.  Running the check one step
later — same value, read back from the environment, still inside the
single-constructor branch where `cvT`, `cvC`, `nP`, `nF` and `caps` are
all in scope — costs three localised `by_cases` and gives the bridge a
*stronger* fact (the stored-and-found form).  `unitlike` does not need
it: its right-hand side is a law premise, not a fabricated spine.

### Mirror surface

Unlike #135's conjunct, the member install is **not** single-sourced —
the cert-skipping driver has its own copy — so this is three sites:

| site | file | role |
|---|---|---|
| `checkIndDecl` | `Setlec/Kernel/Modeled.lean` | the `Env` version; domain of the Model-side inversions |
| `checkIndDeclS` | `Setlec/Kernel/CheckerS.lean` | the version that executes |
| `checkIndDeclNC` | `Setlec/Kernel/CheckerNC.lean` | the cert-skipping driver's copy |

with the predicate itself in two (`ctorResidualOk`, `ctorResidualOkF`),
pinned by `ctorResidualOkF_eq` (`Setlec/Verify/CheckerF.lean`).  The
verification cost was three inserted `by_cases`, each next to the
existing projection-freshness one it is refuted exactly like:
`Setlec/Model/Extend/Decl.lean`, `Setlec/Model/BridgeWF.lean`,
`Setlec/Model/BridgeS.lean`.  No other proof moved.

**No verify-side carrier here.**  The first attempt tried to thread the
fact through `EtaPins` and could not, and the ruling confirmed why:
`EtaPins`' parameters reach only *model-side* constants, and this is a
fact about the **public** constructor — a category error, not a
plumbing difficulty.  The carrier is the bridge's own `EnvTT` field,
discharged from this install's inline inversion, and that work is the
bridge agent's.

### Gates

Build warning-free (touched oleans force-deleted and recompiled),
`lake test`, arena 90/92, e2e 67/67, split driver 11/11, infer-only
5/5 and the full `--infer-only` sweep, axioms exactly
`[propext, Classical.choice, Quot.sound]` on the nine consistency
theorems, no sorries, init-prelude byte-identical — stdout, stderr,
exit — in the certified, the `SETLEC_NO_PROOF_CERTS=1` and the
`SETLEC_INFER_ONLY=1` modes against a binary built from pre-change
master.  Cost: 38.7985 G → 38.7989 G instructions:u on init-prelude,
**+0.001 %** (median of three) — one `find?` and one `stripPis` per
modeled single-constructor block, and cheaper than the first attempt's
+0.021 % because it no longer runs inside the capability computation.

**Negation probe.**  Byte identity does not prove a conjunct *true*.
Negated (`!(cbody == directFam …)`) in both mirrors and rebuilt,
init-prelude **declines** at the first eta-capable block
(`not implemented yet: modeled structure: eta constructor residual [at
inductive LT]`, exit 2), arena falls to **67/92**, e2e to **32/67**,
split 8/11, infer-only 3/5.  Note the signature differs from #135's,
and correctly so: this is a hard install check, not a capability
conjunct, so a violation *declines* rather than silently dropping eta
and rejecting downstream.  Reverted; byte identity re-confirmed in all
three modes.

## The yolo sweep: a cert-skipping twin had drifted (2026-08-27, task #139)

> **Superseded by task #147**: `SETLEC_NO_PROOF_CERTS`/`--yolo` is
> retired; the sweep lives on as the `--no-model` sweep against
> `tests/no-model-expected.txt`, and the class-B argument-position
> escapes documented below are *caught again* by `--no-model`'s
> checking-mode front door (only the decline-vs-reject error-class
> divergence remains recorded).  The drift lesson stands.

**What drifted.**  Task #105 lowered the indexed nested-auxiliary
certification into the *prefix* context: a `.nested` rule's stored pins
are instantiated against the recursor application's `rP` prefix
arguments, not against its `mI` major-index prefix (the two coincide
only for unindexed nestings, where `majorIdx = rulePrefix`).  Commit
`b5788c6` moved the certified `iotaRecI` and the install side over —

```
-  pinArgsI cv.levelParams us (args.take mI) (mI - 1) pins
+  pinArgsI cv.levelParams us (args.take rP) (rP - 1) pins
```

— and did not move the cert-skipping twin `iotaRecNC`
(`Setlec/Kernel/CoreNC.lean`).  Two tokens, three days, one wrong
verdict: `SETLEC_NO_PROOF_CERTS=1` **rejected** (exit 1) the e2e
fixture `indexed_nested_aux.ndjson` that the certified stack accepts.
Fixed here by mirroring the same two tokens; nothing else in the NC
path changed.

The nested-rule comparand *values* are on the task-#76 "kept always"
list precisely because they are verdict-relevant — the twin was
supposed to track the original.  Nothing enforced that it did.

**Why the sweep exists.**  The harness ran the suites certified, with
`--direct-off`, and (since #134) with `--infer-only`; it never ran them
under `SETLEC_NO_PROOF_CERTS=1`.  The `<on>|<off>` expectation pairs in
`tests/arena-expected.txt` and `tests/e2e-expected.txt` look like a
mode column but are the task-#120 direct-structs switch, not this
flag.  So `tests/arena.sh` now closes the loop by default: after the
certified sections it re-runs **both** suites with the flag exported,
against the certified expectations plus `tests/yolo-expected.txt`.
`--no-yolo` skips it for a tight edit loop; `--direct-off` and
`--infer-only` skip it too, staying unchanged in cost.  Measured cost
of the extra pass: ~17 s arena + ~21 s e2e on a ~48 s certified run
(1 m 27 s total).  A mismatch prints `YOLO DIVERGENCE` and fails the
run; re-introducing the `mI` spelling and rebuilding reproduces exactly
one such line, at `indexed_nested_aux.ndjson`.

**What may be recorded, and what may not.**  `tests/yolo-expected.txt`
exists for one class of entry, the acknowledged **class-B** divergence:
`inferSpineNC` drops the per-argument application check *everywhere*,
the driver's front door included, so a stream whose only defect is
inside an application **argument** may be accepted under the flag.
That is a known property of the measurement mode (task #134's
amendment to the verification-tax section), not a bug, and a fixture
exhibiting it gets a line.  Every other flip is an NC twin that has
drifted: fix the twin, do not record the flip.  The file's header says
so.  (The wording of this class was tightened after the 2026-08-27
fuzz campaign's finding F1: the dropped check is the argument's whole
`infer`, so the class covers universe-argument counts, non-function
applications, non-sort binder domains and unsupported projection
shapes as well as type mismatches — and, since an unsupported feature
in argument position is a certified *decline*, a 2-vs-0 pair records
here exactly like a 1-vs-0 one.)

**The audit.**  With the fix in, the full arena suite (138 expectation
lines, 92 good) and the full e2e suite (67 lines, at their declared
`raw`/`pre` modes) give **identical** exit codes in both modes — zero
divergences, zero recorded overrides.  The class-B behaviour was real
but unexercised by any fixture then in the suites: none of the `bad/`
streams has its *only* defect inside an application argument.  The
stale "verdicts are identical in both modes" claim in the
verification-tax section is amended in place to the exact statement.
(Superseded on the fixture count by the campaign witnesses below: the
e2e suite is now 70 lines with three recorded overrides.)

**How thin the coverage was** (instrumented `iotaRecNC`, one trace line
per `.nested` comparand computation, whole corpus, reverted after the
count):

| fixture | rule | `mI` | `rP` | fires |
|---|---|---|---|---|
| `e2e/nested_rec.ndjson` | `Tree.rec_1` | 6 | 6 | 7 |
| `e2e/nested_pin_names.ndjson` | `PTree.rec_1` | 6 | 6 | 7 |
| `e2e/indexed_nested_aux.ndjson` | `TV.rec_1` | 7 | **6** | 5 |

That is the *entire* corpus: the 138 arena streams never fire a
`.nested` rule at all, and neither does init-prelude.  Of the three
fixtures that do, only one is an indexed nesting — and `mI ≠ rP` is
exactly the condition under which the two spellings differ.  So the
drift was reachable through **one fixture out of 205**, which is both
why it survived and why it was worth wiring the sweep in permanently
rather than auditing by hand.

### Gates

Build warning-free (touched oleans force-deleted and recompiled),
`lake test`, arena 90/92, e2e 67/67, split driver 11/11, infer-only
5/5, the new yolo sweep green (138 arena + 67 e2e agreeing), axioms
exactly `[propext, Classical.choice, Quot.sound]` on all thirteen
consistency theorems (`no_proof_of_Empty{,_input}` and
`checkDecl{,s}_sound` plus the `_S`, `_C` and `_SP` families), no
sorries.  Init-prelude (`_tmp/perfcmp/
init-prelude.preprocessed.ndjson`, `--pre`, 3653 declarations) is
**byte-identical** — stdout, stderr, exit 0 — against a binary built
from pre-change master in the certified, the `SETLEC_NO_PROOF_CERTS=1`
and the `SETLEC_INFER_ONLY=1` modes.  The certified identity is the
scope fence (only the NC path was touched); the *yolo* identity is
expected for the reason the table above gives — init-prelude fires no
`.nested` rule, so the changed line is never reached on that stream.

### Class B, exercised (2026-08-27 fuzz campaign, finding F1)

The campaign's first finding was that the class-B contract as written
understated the mode.  `inferSpineNC` does not skip the
argument-vs-domain `defeq`; it skips the argument's `infer`, so *any*
defect living only inside an application argument escapes the flag.
Three purpose-built streams are now committed as e2e fixtures, each
with a `tests/yolo-expected.txt` override — the file's first entries,
and the reason the sweep's summary line now reports a non-zero
"recorded divergences" count:

| fixture | mode | certified | yolo | escaping defect |
|---|---|---|---|---|
| `tests/e2e/yolo_arg_escape.ndjson` | `raw` | 1 | **0** | application type mismatch |
| `tests/e2e/yolo_arg_escape_univs.ndjson` | `raw` | 1 | **0** | universe-argument count |
| `tests/e2e/yolo_decline_vs_accept.ndjson` | — | 2 | **0** | unsupported projection shape |

`yolo_arg_escape` is the witness worth remembering: `theorem
everything : ∀ p : Prop, p := fun p => (fun h : p => h) (Eq.refl Nat
Nat.zero)` is **accepted** under `--yolo`.  The redex's result type is
`p`, so the argument check is the only thing that could see that
`rfl : 0 = 0` does not prove `p`.  `yolo_arg_escape_univs` (`def w9 :
Nat := (fun x : Nat => Nat.zero) Nat.zero.{1}`) pins that the class is
the argument *position* rather than one error kind, and
`yolo_decline_vs_accept` pins that a certified **decline** can be lost
the same way — a shape the header's original contract did not
anticipate, now covered there.

All three are rejected (resp. declined) identically to the certified
stack under `SETLEC_INFER_ONLY=1`, which keeps the driver's front
door: the escape is specific to the measurement stack, and the
`--infer-only` sweep needs no expectation entries for them.

Gates for this landing (tests and documentation only — no source
file changed, `lake build` rebuilt nothing): `lake build`
warning-free, `lake test`, arena 90/92, e2e **70/70**, split driver
11/11, infer-only 5/5, and the yolo sweep green at
`138 arena + 70 e2e as expected (3 recorded class-B divergences)`.
The sweep's summary line was reworded from "agree with certified" to
"as expected" at the same time: the overridden fixtures deliberately
do not agree, and the override count is printed so that a silently
emptied `tests/yolo-expected.txt` shows up there.  The full
`tests/arena.sh --infer-only` sweep is green as well (70/70 at the
certified expectations).

## Binder annotations are erased at the parser (task #142, 2026-08-27)

**The finding (fuzz campaign F2).**  A stream that is byte-for-byte a
good stream *except* that one binder of a pinned basis block carries a
different `BinderInfo` — `Nat.succ : {n : Nat} → Nat` — missed every
pin, fell through to the alias path, and was **rejected** (exit 1)
with `reserved basis name Nat`.  The official kernel accepts it:
binder annotations are display data, and kernel typing erases them.  A
false reject on an annotation-only deviation is the wrong verdict for
the wrong reason, and it was reachable by a one-character edit.

**The ruling (user).**  Remove `BinderInfo` during *parsing*.  The
frontend maps every binder annotation to `.default` as streams are
parsed, so annotation-only deviations cannot exist anywhere
downstream.

**Where the strip lives.**  `Setlec/Frontend/Export.lean`,
`parseExprEntry`: the `lam` and `forallE` entries intern `⟨.default⟩`.
`parseBinderInfo` still *parses* the field and still rejects an
unknown spelling as a malformed record — it just returns `Unit`.  That
is the only place stream input becomes an `Expr` binder, so it is the
only place the strip is needed.  No kernel logic was touched: nothing
in `Setlec/Kernel/*` branches on an annotation (`defeq` matches
`_m₁`/`_m₂`; `natOpTyPinned` matches `_mb`; `piBinderInfos` is
unused), which is what makes the strip verdict-neutral.

**Pin-side normalization** (the half that would otherwise *invert* the
bug — pins carry the real annotations of the toolchain signatures they
were generated from, so a one-sided strip would make them never
match).  The two pin comparisons need different treatment, because
their pin literals differ in how tightly they are pinned by proofs:

* **Basis blocks and the quotient bundle** (`ConstantInfo.canon`
  equality in the frontend).  Both sides go through `canonExpr`, so
  the annotation is erased *there*, beside the binder-name erasure
  that was already happening.  The pinned literals in
  `Setlec/Kernel/Basis/*` keep their real annotations — `TTVerify`
  pins them with `{ bi := .implicit } from rfl`, and rewriting them
  would be a large, conflict-prone diff for no gain.
* **Standard axioms and the compiler-trust family**
  (`ConstantVal.matchesPin`, via `Expr.eraseNames`).  Here the *pin
  literals* were normalized instead: every binder in
  `Setlec/Kernel/StdAxioms.lean` — raw and annotated forms alike — is
  now `⟨.default⟩`, including `propext`'s `{a b : Prop}`,
  `Iff.intro`'s and `Classical.choice`'s `{α}`.  Nothing pins those
  annotations (no `.implicit` occurs in any `Model/`, `Verify/` or
  `TTVerify/` file outside the basis blocks), and this route keeps
  `Expr.eraseNames` **and `Expr.ErasedEq` unchanged** — the model's
  "same denotation" relation still relates binder metadata, so
  `ErasedEq.of_eraseNames` + `interp_erasedEq` bridge a `matchesPin`
  hit exactly as before.  A regeneration through `AnnotateBasis.lean`
  must preserve this normalization (noted in the module header).

**Rejected alternative.**  Making `Expr.eraseNames` erase the
annotation and dropping the `m = m'` conjunct from `Expr.ErasedEq` was
tried first.  It is *semantically* correct — no interpretation clause
reads `BinderMeta`, whose only field is the display `BinderInfo` since
task #100 erased the codomain sort — but it does not stay mechanical:
`TowerOk.cons` shares the binder metadata between a frame and the λ it
opens *by construction* (`ruleLhs` copies the right-hand side's), so
`TowerOk.of_stages` stops going through, and the fallout reached
`RuleFold`, `InstFrames`, `TeleElim`, `ModeledCaps`, `IndBottom`,
`DeclInd` and `Inst` — including files another agent was editing.  The
pin-literal normalization achieves the same verdict with a two-file
diff.  If `ErasedEq` is ever wanted annotation-blind for its own sake,
it is a self-contained task whose real content is `TowerOk`.

**Preprocessor consistency is automatic**: the `_model` families the
preprocessor emits re-enter through the same `processLineCore`, so
model and public declarations are stripped identically — there is no
side channel.

**Fixtures.**  `tests/e2e/basis_binderinfo.ndjson` (a `Nat.succ`
binder) and `tests/e2e/basis_binderinfo_rec.ndjson` (a `Nat.rec`
binder), both `raw`, both expected **0**; they were exit 1 before.
Neither needs a `tests/yolo-expected.txt` entry — both modes accept.

**Gates** (all green): `lake build` warning-free with the touched
modules force-recompiled, `lake test`, arena 90/92, e2e **72/72**,
split driver 11/11, `--infer-only` sweep 90/92 + 72/72, yolo sweep
`138 arena + 72 e2e as expected (3 recorded class-B divergences)`,
soundness/consistency axioms exactly `[propext, Classical.choice,
Quot.sound]`, no sorries.  init-prelude (`--pre`, 3653 declarations)
is **byte-identical** in stdout, stderr and exit code across all three
modes (certified, `SETLEC_NO_PROOF_CERTS=1`, `SETLEC_INFER_ONLY=1`).

**Measured** (init-prelude, `perf stat -e instructions:u`, median of
3): 34.0160 G → 33.8651 G, **−0.44 %**.  The strip collapses binders
that differed only in annotation onto the same arena node, so the
parse arena shares slightly more — a small free win, not the point of
the change.

## The iota certificate certifies the slot's sort (2026-08-27, task #146)

**#135's direct sibling — form (2) of the same request — and the
seventh change the TT bridge (task #119) asked of the checker.**
Siblings: tasks #126, #129, #130, #135, #136, #137.

**The gap** (`Setlec/TTVerify/DESIGN.md` §17.3).  Every `IndBottom*TT`
fires `EqLawTT`, whose first β-step wants `⊢ ⟦αS⟧ : Sort ⟦ℓA⟧` — the
iota statement's equation type slot at the level the statement's own
`Eq.{ℓA}` carries.  #135 closed the *capability* half of this with a
syntactic pin (`tbodyM == Expr.sort ℓA`), but that pin is on the model
former's telescope residual; here the slot is a **motive application**
whose shape varies per rule, so no syntactic pin can serve it.
Inverting the theorem's own derivation is Π-injectivity, which
`propext` refutes (`Setlec/TTVerify/Inversion.lean`), and a "stored
types are types" invariant gives `Sort u` at *some* `u` — `u = ⟦ℓA⟧` is
exactly the missing step.

**The check.**  `checkIotaSidesTy` (`Setlec/Kernel/Modeled.lean`,
landed by task #100 stage 3) already holds `ops`, the depth, the slot
and both sides, and already certifies the two *sides* against the
slot.  It gains the slot itself, at the statement's own equation
level:

```
  let tα ← ops.inferType envSelf depth alphaS
  unless ← ops.isDefEq envSelf depth tα (.sort ℓA) do
    throw (.notImplemented s!"iota statement type slot sort for {cvName}")
```

The level reaches the call from each call site's own `Eq`-head match,
through the new total accessor `eqHeadLevel` (`Kernel/CheckerBase.lean`,
`.const _ [ℓ] => ℓ`, `.zero` off shape).  On the two recursor paths the
head has already passed `isEqHead`; on the projection path it has
already passed the `.app (.app (.app (.const c [_ℓ]) …) …) …` match
with `c = eqName`, and the level is read off *that* body
(`eqHeadLevel sbody.getAppFn`) — the same `ℓA` the inversion already
existentially binds, so the inversion needs no lemma relating the
closed statement body to its opened form.

**Semantic, not syntactic — because the request was form (2).**  §14.7.4
offered two forms; #135 landed form (1) where both values were syntactic
and `ops` was out of scope.  Here the certificate is a `defeq` against
`Sort ℓA`, which is what `IotaSlotSorted`
(`Setlec/TTVerify/IndBottom.lean`) was committed to in advance:

```
∃ tα, inferTypeCore env₀ F k αS = .ok tα ∧
  isDefEqCore env₀ F k tα (Expr.sort ℓA) = .ok true
```

The three inversions deliver that shape verbatim as their last
conjunct, so the bridge's swap is `exact`.

**Mirror surface.**  The predicate is **single-sourced** — `CheckerS`
and `CheckerNC` call the same `checkIotaSidesTy`, so unlike #136 there
is no cert-skipping copy — but its *call sites* are six, and every one
had to learn the level:

| site | file | role |
|---|---|---|
| `checkIotaThm` / `checkIotaThmN` / `checkProjIota` | `Setlec/Kernel/Modeled.lean` | the `Env` versions; domain of the inversions |
| `checkIotaThmF` / `checkIotaThmNF` / `checkProjIotaF` | `Setlec/Kernel/CheckerS.lean` | the versions that execute (S and NC drivers) |

pinned pairwise by `checkIotaThmF_eq` / `checkIotaThmNF_eq` /
`checkProjIotaF_eq` (`Setlec/Verify/CheckerF.lean`, all `simp <;> rfl`
— they re-proved unchanged, which is what makes them worth having).

**Verify-side threading.**  `PlainChecked` and `NestedChecked`
(`Setlec/Verify/Extend/Iota.lean`) and `checkProjIota_inv`
(`Setlec/Verify/Extend/Proj.lean`) gain the conjunct and their
inversions forward it (one `cases` pair each, plus `rw [hheadEq]` to
turn `eqHeadLevel tbody.getAppFn` into the bound `ℓA`).  The
operation-family transports take one more step apiece —
`checkIotaSidesTyS_sim` (`Verify/BridgeS2.lean`),
`checkIotaSidesTy_wfimp` (`Verify/BridgeWfImp.lean`), the two
`_dproj`s and `_datF` (`Verify/BridgeDecl.lean`); the new `isDefEq`
argument is a `.sort`, so its well-scopedness is `True`.  The set model
takes the conjunct as `-`: `Setlec/Model/Extend/Recs.lean` (both fire
modes) and `Setlec/Model/Extend/Proj.lean` gain one `-` in their
`obtain` patterns and no proof obligation — the model gets this
membership from `AnnotOk`, which is the premise the *bridge* dropped by
design.

**The risk, priced before the ask.**  The requester instrumented the
shared `checkIotaSidesTy` on both paths and ran the whole corpus
(arena incl. `init-prelude` + e2e): **3 895 / 3 895 calls pass**, zero
counterexamples (`Setlec/TTVerify/DESIGN.md` §17.3).  The landing
confirms it end to end: no fixture's verdict moved.

**Gates.**  Build warning-free with the ten touched modules' oleans
force-deleted and recompiled, `lake test`, arena 90/92, e2e 72/72,
split driver 11/11, infer-only 5/5 and the full `tests/arena.sh
--infer-only` sweep, the yolo sweep green
(`138 arena + 72 e2e as expected`), axioms exactly
`[propext, Classical.choice, Quot.sound]` on the nine consistency
theorems, no sorries, init-prelude byte-identical — stdout, stderr,
exit — in the certified, the `SETLEC_NO_PROOF_CERTS=1` and the
`SETLEC_INFER_ONLY=1` modes against a binary built from pre-change
master (all re-run against master `61a23c9` after merging it in).
Cost: 38.6530 G → 38.6714 G instructions:u on init-prelude,
**+0.048 %** (median of three) — one `inferType` and one `isDefEq` per
iota statement, and the most expensive of the seven bridge changes so
far, as a semantic certificate should be next to six syntactic ones.

**Negation probe.**  Byte identity does not prove a conjunct *true*.
Negated (`unless !(← ops.isDefEq …)`) in the single source and
rebuilt, init-prelude **declines** at the first modeled recursor
(`not implemented yet: iota statement type slot sort for LT.rec [at
inductive LT]`, exit 2), arena falls to **46/92**, e2e to **30/70**,
split 8/11, infer-only 3/5 (the e2e count is the pre-merge suite's 70).
The signature is #136's, not #135's, and
correctly so: this is a hard certificate inside an install check, so a
violation declines rather than silently dropping a capability.
Reverted; byte identity re-confirmed in all three modes.

## The `instListM` sites get a persistent memo (2026-08-27, task #145)

**One memo, eight call sites, nothing else.**  `instListM`
(`Setlec/Kernel/CoreI.lean`) — interned bulk instantiation — now
consults `IState.instC`, a persistent map
`(EIdx × List EIdx × Nat) → EIdx` from the *whole argument tuple* of
the pure operation to its result.  Everything else about the checker
is unchanged, and every verdict on every fixture is unchanged.

**Where the work was.**  A per-call-site census (`CPCENSUS`) and a
per-site memo bitmask (`CPMEMO`) over all 23 bulk-instantiation sites,
run over three streams and three lanes, put the whole win in the eight
`instListM` sites (the probe's group `list`, sites 0–7): the recursor
argument-certificate walk `iotaCertsIAux` (sites 0/1), `betaPeelI`
(2–5) and `betaPeelNC` (6/7).  All three walk a binder telescope
argument by argument while an accumulator grows one element at a time,
so the *same* `(telescope, argument prefix)` pair is instantiated once
per remaining argument — quadratic re-instantiation of a shape whose
result is a pure function of the arena.  On a 40 % Mathlib prefix the
census counts 1.57 M fires at those sites against 0.43 M distinct
keys.  Attribution, certified lane, same prefix: `list` −19.64 %,
`beta` −9.90 %, `iota` −8.46 %, `rev` (all fifteen `instListRevM`
sites together) −4.31 %.

**Why the `instListRevM` sites are deliberately left alone.**  They
are the binder loops (`inferLamsI`, `inferPisI`, `annotateLamsI`,
`annotatePisI`) and the application spines (`inferSpineI` and its
infer-only and cert-skipping twins) — the sites that exist *because*
they mirror the reference kernels' `instantiateRev` discipline
(task #97).  The match-reference ruling forbids drifting from the
references' strategy for a merely verdict-preserving gain; a memo is
not a strategy change, but it is still machinery the references do not
have, and machinery is carried only where the measurement pays for it.
Here it does not: adding the fifteen `rev` sites on top of `list` buys
a further −0.3 % on the `Std.Time` cone certified, *loses* 0.5 points
on the same cone infer-only (−3.77 % → −3.31 %), and costs another
+26 % peak RSS (13.3 GB → 16.1 GB).  Scoped out, and the scoping is
the measured configuration verbatim: `CPMEMO=255`.

**The null result is the control.**  With certificates skipped
(`SETLEC_NO_PROOF_CERTS=1`) the memo is worth **0.0 %** on all four
streams — the probe's 0.00 %, reproduced here as +0.03 % to +0.06 %,
i.e. the cost of the extra hash lookup and nothing more.  That is the
expected shape and the reason to believe the attribution: the
`iotaCertsIAux` and `betaPeelI` re-instantiation only happens because
the certificates re-walk telescopes the reduction itself does not,
so with the certificates gone there is nothing to collapse.  It also
prices the mechanism honestly — this is not a reduction speed-up, it
is the *certificate tax* getting cheaper.

**Keys are depth-free.**  The key is `(target, values, cursor)`: every
argument of `EStore.instantiateListI`, and nothing else.  The `cursor`
is that operation's own de Bruijn offset — at all eight sites the
default `0` — not the checker's ambient binder depth, so the entry is a
closed fact about a pure function and the #31 depth-free discipline is
satisfied by construction rather than by a side condition.

**The size knob.**  `instCCap` (`Setlec/Kernel/CoreI.lean`) bounds the
table at **32 000 000** entries; on overflow it is dropped whole and
refilled, no eviction policy.  Flushes come at environment
transitions, so only a single declaration can grow the table without
bound, and the cap guards that shape alone.  Measured peaks, certified
lane, via a throwaway peak counter: `init-prelude` **8 934**,
the 40 % Mathlib prefix **115 802**, and the `Std.Time` cone —
a stress stream that needs twice the shipped `checkFuel` to finish at
all — **18 318 022**, all of the last inside *one* flush epoch, for
13.6 GB peak RSS at roughly 170 bytes an entry.  The cap sits above
that worst case on purpose: the configuration that ships must be the
configuration that was measured, so the guard binds only past the most
pathological stream on record, at some 5 GB of memo.

An earlier guess of 16 M was measured and *rejected*: the `Std.Time`
cone tripped it (peak read back as exactly 16 000 000, RSS 12.5 GB
instead of 13.6 GB), i.e. the cap would have silently truncated the
configuration the numbers below were taken from.  The rule the value
follows is that the benchmarked configuration must be the shipped one;
the cap is a guard past the frontier, never a participant in it.

**A stricter knob, deliberately not taken.**  The `Std.Time` cone's
+26.7 % peak RSS is a heavy tax, and the analysis that excuses it —
one declaration's transient, bounded by `instCCap` — is an argument
about pathology, not a bound anyone would want on a hot path.  If that
trade is ever refused, the stricter form is a **per-declaration
flush**: `instC` is already dropped in `IState.flushed`, so moving it
to the driver's per-declaration boundary instead of the environment
transition is a one-line change on plumbing that exists.  It would cap
retention at one declaration's working set at the cost of the
cross-declaration hits — unmeasured, and not measured here because the
measured configuration is the one that ships.

**Verification: the memo is self-certifying, like `ienv`.**  `ISOK`
(`Setlec/Verify/SimI.lean`) gains one clause — every entry
`(i, vs, d) ↦ r` comes with `∃ a ws`, `denoteT i = some a`,
`DenL vs ws` and `denoteT r = some (a.instantiateList ws d)`.  No
environment, no fuel, no depth: a pure-substitution fact, `Ext`-stable
by `denoteT_mono` and `DenL.mono`, so it survives arena extension and
would survive every environment transition — `flushS` drops the table
regardless, because the tier bracket may *truncate* the arena its keys
index into (`ISOK.truncFlush`).  `instListM_eff` gains a hit case: the
entry is backed, `denoteT` is a function and `DenL` is functional
(`DenL.det`, new), so the cached index denotes the required
instantiation and the state is unchanged; the miss case inserts via
`ISOK.insertInstC`, generalised over the retained table so the
overflow branch (insert into the empty map) is the same lemma.  The
bracket-open transport takes one bullet (`DenL.of_denoteT_eq`, new).
The other twelve `ISOK` reconstruction sites take one field apiece.

**One casualty.**  `instListRevM_eq` — `instListRevM e vs d =
instListM e vs.toList.reverse d`, the task #97 identification — is
*no longer true*: one side memoizes and the other does not.  It is
deleted, and `instListRevM_eff` repeats the ten-line raw proof over
`instantiateRevI_eq` instead of routing through `instListM_eff`.  The
two remain equal at the spec level, which is all any caller used it
for.

**Measurements** (median of three, `instructions:u` and peak RSS;
`--pre` on preprocessed streams; the `Std.Time` cone against a pair of
`checkFuel := 200000` builds, since the shipped 100 000 does not
finish it):

| stream | lane | base | new | Δ instr | base RSS | new RSS | Δ RSS |
|---|---|---|---|---|---|---|---|
| init-prelude | certified | 33.72 G | 32.45 G | **−3.76 %** | 110.6 MB | 110.8 MB | +0.2 % |
| init-prelude | yolo | 11.36 G | 11.37 G | +0.06 % | 105.1 MB | 105.6 MB | +0.5 % |
| grind-ring-5 | certified | 127.60 G | 114.92 G | **−9.94 %** | 455.9 MB | 539.9 MB | +18.4 % |
| grind-ring-5 | yolo | 30.49 G | 30.50 G | +0.03 % | 162.5 MB | 162.1 MB | −0.3 % |
| Mathlib 40 % | certified | 1727.47 G | 1391.10 G | **−19.47 %** | 730.6 MB | 749.6 MB | +2.6 % |
| Mathlib 40 % | yolo | 176.06 G | 176.11 G | +0.03 % | 450.3 MB | 451.1 MB | +0.2 % |
| Std.Time cone | certified | 1648.15 G | 1556.13 G | **−5.58 %** | 10475 MB | 13273 MB | +26.7 % |
| Std.Time cone | yolo | 51.12 G | 51.15 G | +0.05 % | 181.4 MB | 182.2 MB | +0.5 % |

The probe predicted −6.04 % / +26.6 % on the `Std.Time` cone certified
and −19.64 % / +2.5 % on the Mathlib prefix; both reproduce (−5.58 %,
−19.47 %).  `init-prelude` and `grind-ring-5` were not in the probe
matrix: the first is the smallest win of the four and the second the
largest per-RSS-point, and `grind-ring-5`'s +18.4 % is the largest
memory cost any *shipped-fuel* stream pays.

**A new baseline to quote.**  `grind-ring-5`'s −9.94 % was not
predicted by the probe and is the surprise of the run; whoever picks
up the **#140** regression question after #147 should measure against
its *new* certified baseline of **114.92 G** instructions:u (`--pre`
on the preprocessed fixture, median of three), not the 127.60 G that
pre-#145 master reads.  Part of whatever #140 was chasing on that
fixture is now gone, and comparing across the two baselines would
double-count this task's win.

**Gates.**  Build warning-free (full recompile), `lake test`, arena
90/92, e2e 72/72, split driver 11/11, infer-only 5/5 and the full
`tests/arena.sh --infer-only` sweep, the yolo sweep green (138 arena +
72 e2e as expected), axioms exactly
`[propext, Classical.choice, Quot.sound]` on all thirteen consistency
theorems, no sorries.  Init-prelude
(`_tmp/perfcmp/init-prelude.preprocessed.ndjson`, `--pre`, 3653
declarations) **byte-identical** — stdout, stderr, exit 0 — against a
binary built from pre-change master in the certified, the
`SETLEC_NO_PROOF_CERTS=1` and the `SETLEC_INFER_ONLY=1` modes.  Byte
identity is the strong statement here: a memo that ever returned a
different index than the recomputation would move a verdict, and the
arena's hash-consing is exactly why it cannot.

## The three-mode setting (2026-08-27, task #147)

**The user-ruled shape.**  One three-valued mode replaces the flag
zoo.  `Setlec.CheckMode` (`Setlec/Kernel/Env.lean`) is validated once
at startup (`Main.lean`, `parseArgs`) and threaded as configuration —
the `directStructsEnabled` discipline; nothing re-reads flags at
runtime.

* **`--set-model` (the DEFAULT)** — the surface the set model proves.
  The seven TT-lane checks are **off**: #126 `projTeleCert` (the
  `whnfCore` `.proj` clause), #129 `projParamCert` (the `inferBody`
  `.proj` clause), #130 `pairEtaCert`'s `projParamCert` tail, #135's
  eta/unit statement-sort conjunct (`checkEtaThm{,F}` /
  `checkUnitThm{,F}`), #136's `ctorResidualOk`, #137's callee-side
  constructor-telescope `iotaCerts` in `structEtaCertWith`, and #146's
  iota-slot sort check in `checkIotaSidesTy`.  Every always-on
  certificate family (per-redex beta, per-argument application,
  proof-irrelevance chains, `etaCert`, `iotaCerts`, `projCert`) keeps
  running.
* **`--tt-model`** — the seven on: the pre-#147 certified behavior,
  and the surface `Setlec/TTVerify` reasons about.
* **`--no-model`** — the unverified lane, absorbing BOTH retired
  flags: a full checking-mode front door per declaration
  (official-kernel parity — NOT the old yolo mode's front-door skip),
  task #134's infer-only internal discipline, and no certificate
  families at all.  `--yolo`/`SETLEC_NO_PROOF_CERTS` and
  `--infer-only`/`SETLEC_INFER_ONLY` are retired as user-facing
  controls; both the flags and the environment variables now **exit 3
  with a pointer to the new modes** (never silently ignored — a
  verdict's provenance must be readable off the invocation).

**Kernel implementation.**  The mode is an explicit first argument on
exactly the call chains that reach the seven sites: the spec bodies
(`whnfCoreBody`/`inferBody`/`defeqBody` and the
`iotaRec`→`majorToCtor`→`structEtaCertWith`,
`stuckIrrel`→`pairEtaCert` chains), their interned twins, the knots
(`coreKnot`, `pureFns`, `cachedFns`, `coreKnotI`) and the shared
`...F` install checks; each site is spelled
`if mode.ttChecks then <check> else pure true` (Bool conjuncts as
`!mode.ttChecks || <conjunct>`).  The `--no-model` stack is
`Setlec/Kernel/CheckerNC.lean` re-pointed: `coreKnotFNC`
(`Setlec/Kernel/CoreNC.lean`) is the task-#134 `coreKnotF` pattern —
checking-mode `inferBodyI` at `.noModel` tied to itself over the
cert-skipping `coreKnotNC` internals, with the `inferFC` checking-mode
memo and its flush discipline — and the P-driver front doors run on
it.  `Setlec/Kernel/CoreIO.lean` and `CheckerIO.lean` (the retired
infer-only stack) and the old Declaration-level NC twin are deleted;
entry points renamed `checkDeclSPStepNM`/`checkDeclsSPNM`.

**Verify side.**  The seven checks' inversion conjuncts are stated as
`mode.ttChecks = true → conjunct` inside the existing inversions (the
#148 interface pin; `pairEtaCert_inv` alone needed the existential
restructured — `∃ entry` moved under the implication).  The **set
battery is mode-generic**: `checkDeclsSP_sound` and the
`no_proof_of_Empty*` families quantify `∀ {mode}` and so cover the
default — the #148 finding held with zero exceptions: no set-lane
proof consumed any of the seven (they dropped as `-` or vacuous
implications; any breakage here was declared a stop-and-report
finding, and none occurred).  The **TT battery** is pinned:
`CertifiedConfigTT` (one named Prop) became
`directStructsEnabled = false ∧ mode = .ttModel`, with
`.direct`/`.mode_eq`/`.ttChecks` extractors; the TTVerify step files
state their lemmas at a file-local `private abbrev mode := .ttModel`,
under which the gated bodies are *definitionally* the pre-#147 ones,
so the walks went through unchanged and consumers discharge the gated
conjuncts with `(h rfl)`.

**Config audit** (the #148 vacuity guard): `tests/SetlecTests.lean`
pins the compiled values — the `CheckMode` default, the
`CheckMode.ttChecks` wiring on all three constructors, and
`directStructsEnabled = true` — one `#guard` per value, each naming
the theorem family that depends on it.

**Tests.**  `tests/arena.sh` runs three sweeps: the certified sections
at the default, then both suites again with `--tt-model` (SAME
expectations — a divergence prints `TT-MODEL DIVERGENCE` and is a
finding) and with `--no-model` (certified expectations plus
`tests/no-model-expected.txt`, the successor of
`tests/yolo-expected.txt`).  `--no-sweeps` keeps the tight edit loop.
The mode_case section pins the two extra modes' smoke verdicts, the
`--no-model`+split refusal, and the retired flags/env vars erroring.
The three class-B fixtures of task #139 are **caught again** under
`--no-model` (the checking-mode front door sees the argument
positions): `yolo_arg_escape` 1, `yolo_arg_escape_univs` 1 — no
overrides needed — and `yolo_decline_vs_accept` is the one recorded
divergence (certified 2, no-model 1: the cert-free lane resolves the
unsupported-projection stream to "invalid: expected a sort" instead of
the annotation pass's positive decline — an error-class difference,
the lane's nature, recorded with its mechanism in the file header).

**Gates** (all green): `lake build` warning-free, `lake test`, arena
90/92, e2e 72/72, split 11/11, mode flags 10/10, tt-model sweep
`138 arena + 72 e2e identical to default`, no-model sweep
`138 arena + 72 e2e as expected (1 recorded divergence)`, axioms
exactly `[propext, Classical.choice, Quot.sound]` on the ten set-lane
consistency theorems and the six TT theorems, zero sorries.
init-prelude (`--pre`, 3653 declarations) is **byte-identical** —
stdout, stderr, exit — against the pre-change baseline binary in both
`--tt-model` vs old default and `--set-model` vs old default (every
one of the seven checks had landed byte-neutral, and stayed so in
aggregate).

**Negation probes** (the gating must not have made the checks dead at
`--tt-model`).  #146's slot-sort conjunct negated
(`isDefEq tα (.sort (.succ ℓA))`): `--tt-model` declines
`indexed_vec`/`nested_rec` (exit 2) while `--set-model` still accepts
— alive there, gated here.  #135's eta statement-sort conjunct negated
(`tbodyM != Expr.sort ℓA` in `checkEtaThmF`): 17 e2e fixtures flip to
reject under `--tt-model` (the eta capability is denied and
eta-dependent streams break) while `--set-model` is unaffected.  Both
probes reverted; suite re-verified green.

**Measured** (instructions:u; init-prelude median of 3, grind-ring-5
single runs; all runs accept — 3653 resp. 3946 declarations):

| stream | `--set-model` (default) | `--tt-model` | `--no-model` | old default | old `SETLEC_INFER_ONLY` |
| --- | --- | --- | --- | --- | --- |
| init-prelude | 33.88 G | 33.98 G | **16.16 G** | 33.88 G | 23.83 G |
| grind-ring-5 | 127.49 G | 128.06 G | **70.21 G** | 127.76 G | — |

The new default's tax relief (the seven checks off): **−0.31 %**
init-prelude, −0.45 % grind-ring-5 — the TT lane's whole check budget
is under half a percent, which is the number task #140 wanted
re-baselined.  `--no-model` versus the old infer-only mode: 16.16 G
vs 23.83 G (**−32 %** — the certificate families the old mode kept);
versus the old yolo mode's recorded 11.34 G it costs +42 % — the
checking-mode front door's price, paid deliberately (it is what
catches the class-B escapes).

## Owed records, landed with task #147

The three summaries below were owed by earlier tasks whose data was
preserved but whose DESIGN entries had not been written; the raw
files remain the source of truth.

### The certificate-cost decomposition (task #141; data in `_tmp/certprof-141/`)

Per-family leave-one-out on the `Std.Time` cone
(`_tmp/std-time-cone/pre2.ndjson`, fuel 200 000, infer-only lane,
`CPMASK` bitmask instrumentation — the patch is preserved as
`instrumentation.patch`): baseline 808.0 G instructions:u; the twelve
certificate families decompose as

* **family 2 (the per-redex beta argument re-check) dominates**:
  masking it alone drops 201.0 G = 24.9 % (13 719 078 fires — the
  count task #132 reproduced exactly); families 0/1 (iota recursor /
  constructor telescopes) cost 39.9 G and 15.7 G; every other family
  is ≤ 0.6 G alone;
* the joint mask is **superadditive**: families 0–10 together drop
  569.4 G (70.5 %) against ~257 G for the sum of singles — certified
  reducts feed later certificates, so families amplify each other;
  masking all twelve lands at 51.7 G, on the old yolo floor (51.1 G);
* the memoization probes (`memo.sh`; `CPMEMO` variants) refute the
  easy fix: memoizing certificate results recovers 0.7 %, memoizing
  instantiations 3.7 %, both 3.8 % — the cost is in *distinct*
  certificate work, not repetition.

Consequence: any attempt on the verification tax must attack family 2
structurally — which is what task #132 then tried and refuted.

### The beta-classifier spike, refuted (task #132; data and RESULTS.txt in `_tmp/beta-classifier-132/`)

The hypothesis: a cheap syntactic classifier (domain/body tier A/B/C —
structural domains, structural or modeled-former bodies) could clear a
large share of family-2 fires without running the re-check.  Measured
on the `Std.Time` cone and a Mathlib-40 % prefix, both lanes, with a
classify-but-skip-nothing control (`CPBETA=9`) to price the guard:

* the tiers capture **14.2–21.3 %** of *fires* on `Std.Time` but only
  **2.5–3.6 %** on Mathlib-40 % — and the captured fires are the cheap
  ones: idealised (zero-cost-guard) savings are **0.27–0.41 %** of the
  run, 1.31 % of the very family-2 cost the guard aims at;
* the guard itself costs **+1.9 % / +4.9 %**, so every net number is
  negative (as implemented: −1.6 % / −4.8 %);
* the residual is structural, not classifiable: 65 % of kept fires are
  nested-λ bodies whose innermost body fails the tier test;
* verdict-neutral throughout (every run accepts identically), so the
  refutation is purely about cost.

Gate was ≥ 15 % absolute capture; measured ≤ 0.41 % idealised — a miss
by ~45×, a #124-grade refutation.  Nothing landed; the base commit and
patch are recorded in the directory.

### The set-lane/seven-checks spike, verdict (task #148; design record in `_tmp/148-design/`)

The spike asked whether the set model's proofs consume any of the
seven TT-lane checks.  Verdict: **none** — every set-lane derivation
takes the seven conjuncts as discarded hypotheses (`-` patterns or,
after task #147, vacuous `mode.ttChecks = true → …` implications).
Task #147 is the mechanized confirmation: the whole set battery
(`checkDeclsSP_sound`, the `no_proof_of_Empty*` families and every
bridge beneath them) re-proved **mode-generically** with the seven
checks conditioned off at `--set-model`, with zero proof needing a
gated conjunct.  The cross-task interface this pins: inversion
lemmas state gated conjuncts as implications *inside* the existing
statements (no split lemmas were needed; the one structural change is
`pairEtaCert_inv`, whose `entry` existential moved under the
implication), so the upcoming set-lane bridge consumes the same
inversions the TT lane does.

## Direct structs off by default (2026-08-27, task #148 T0b)

**The user ruling.**  Direct-install structures are *optional and
removable*.  The #148 campaign — factoring `--set-model` through an
algorithmic relation family on the env-free TT syntax — writes no
direct-install rule, so the campaign's theorems would have to be
stated under a `directStructsEnabled = false` hypothesis.  With the
constant compiled `true` that hypothesis is FALSE and every theorem
under it is vacuous (the campaign's risk R4).  A vacuity guard is not
something to prove around; the configuration moves instead.

`Setlec.directStructsEnabled` (`Setlec/Kernel/Direct.lean`) therefore
now ships **`false`**.  Nothing else about the direct path changed: its
recognition layer, its install and its set-theoretic model
(`Setlec/Model/Direct*.lean`, ~7.6k lines) are all still there and
still proved — `checkDecl_sound` covers a clause the binary no longer
takes.  Deleting them is task #148 T7's commit, not this one's.

**Not mode-indexed, deliberately.**  `--tt-model` requires the switch
off already (`CertifiedConfigTT`), `--set-model` requires it off from
here on, so the only mode that could still carry the route is
`--no-model` — the unverified lane, where it buys nothing but a second
install implementation to keep alive.  Preserving it there means
threading `CheckMode` into `directParts?`/`directPartsF?` and hence
into the three knots and every bridge that mentions them: strictly
more machinery than the constant it would replace (the same argument
that refused a command-line flag in task #119).  So it stays one
compile-time constant and all three modes read it.

**Verdict effect: exactly the five expectations task #119 measured,
re-measured at the flip, no sixth.**

| fixture | before | after |
|---|---|---|
| `tests/e2e/direct_struct_raw.ndjson` (`raw` line) | 0 | 2 |
| `tests/e2e/direct_struct_raw.ndjson` (`pre` line) | 0 | 2 |
| `bad/tutorial/133_dup_ctor_def.ndjson` | 1 | 2 |
| `bad/tutorial/134_dup_rec_def.ndjson` | 1 | 2 |
| `bad/tutorial/137_dup_ctor_rec.ndjson` | 1 | 2 |

All five are **declines, and positive ones** — the exit-code
convention's requirement, checked and not assumed.  The switch is a
fall-through, not a decline of its own: the block takes the ordinary
modeled clause and declines there for the modeled path's own reason,
with the modeled path's own message.  Verified on the message, not
just the code — all five report

    setlec: not implemented yet: missing model for X [at inductive X]

(`X` = `Wrap`, `dup_ctor_def`, `dup_rec_def`, `dup_ctor_rec`), i.e. a
`.notImplemented` raised where the artifact is looked for: a
positively detected missing feature, not a failed internal
construction (which would be exit 3) and not a claim that the input is
invalid (exit 1).  The two neighbours task #119 checked for
*non*-movement were re-checked and are still unmoved:
`bad/tutorial/131_dup_defs` still rejects (its duplicate is a `def`,
caught before any block), `bad/tutorial/136_dup_rec_def2` still
declines for the same missing-model reason it always did.

No good stream regressed (campaign risk R5, the stop-and-report case):
arena stays **90/92** — the three arena movers are `bad/` fixtures, so
they never counted toward the accepted-good score, and reject → decline
is the harmless direction (nothing bad is accepted; only rejection
sharpness is lost).  The one good stream that moves,
`direct_struct_raw`, is the fixture *crafted for the direct route*: it
deliberately bypasses generating a `_model` fallback, so its decline is
the route's absence being reported, exactly as the campaign design
anticipated.  It is kept rather than deleted — it is the live witness
of what the route bought, and its `pre` line is now a *sharper* --pre
probe than before (an ignored `--pre` would spawn the preprocessor,
whose `_model` companions would make it accept).

Production streams are untouched, as predicted and as measured:
preprocessed streams always carry `_model` artifacts, so `directNoModel`
is false and the route was already dead on them.  init-prelude (`--pre`,
3653 declarations) is **byte-identical** — stdout, stderr and exit — to
a `9ffcbdf` baseline binary in all three modes.

**Test-machinery simplification.**  With the shipped configuration now
being the former "off" column, the task-#120 two-column machinery had
no second configuration left to describe:

* the `<on>|<off>` expectation pairs in `tests/arena-expected.txt` and
  `tests/e2e-expected.txt` collapse to single exit codes (5 of 205
  lines), with each fixture's pre-flip code recorded in a comment;
* `tests/arena.sh` loses `--direct-off` and its `pick` selector, and
  `tests/build-direct-off.sh` (the second-binary builder) is deleted.
  The recipe survives in the expectation-file headers and in
  `directStructsEnabled`'s docstring: flip the constant, restore the
  five codes.

The deliberate coverage cut: **the switched-on configuration is no
longer exercised by any suite.**  That is the point — it is no longer
a configuration anyone ships or reasons about, and its code is on T7's
deletion list.  Until then the direct path's *proofs* still build with
every `lake build`; only its runtime is unreachable.

**Config audit** (`tests/SetlecTests.lean`).  The task-#147 audit
block's third guard flips to `#guard directStructsEnabled == false`
and its comment is re-pointed: both verified lanes now assume the
switched-off configuration, so flipping the constant back is a
verification-scope change and fails `lake test` at that guard.
`CertifiedConfigTT`'s `directStructsEnabled = false` conjunct is
correspondingly **dischargeable by `rfl` at the shipped build** — noted
in its docstring; the `Prop` itself is left alone (it is the statement
of which configuration is certified, and #148's executors own any
restructuring).

**Gates** (all green): `lake build` warning-free with `Direct.lean`'s
whole cone force-recompiled, `lake test`, arena 90/92, e2e 72/72, split
11/11, mode flags 10/10, tt-model sweep identical to default, no-model
sweep as expected (1 recorded divergence, unchanged), axioms exactly
`[propext, Classical.choice, Quot.sound]`, zero sorries, init-prelude
byte-identical at all three modes.

## The λ-rule computes its codomain sort (2026-08-28, task #152)

**The eighth bridge-requested checker change, and the first with a
*user-granted exception* to the goal's no-new-checks clause.**  The
seven before it (tasks #126, #129, #130, #135, #136, #137, #146) all
certified something the checker already computed and discarded; this
one makes the checker compute something new, and can therefore *reject
streams the reference kernel accepts*.  The grant's rationale, on the
record: **front-door checks are cheap — they do not affect reduction,
and they benefit from the infer caches.**

### Why it was owed (`Setlec/SetR/DESIGN.md`, findings A3 → B5 → A5)

Task #100 stage 6 deleted the λ-annotation re-check along with the
stored annotations, leaving `inferBody`'s `.lam` clause in the
official-kernel `infer_lambda` shape: the domain is checked to be a
type, the body's type is inferred, and the `∀` is rebuilt.  The **∀**
clause four lines above *does* `ensureSort` its opened body's inferred
type — I6 has two sort premises where I7 has one, and that asymmetry
is what the #151 annotation lane ran into:

* **A3** — the λ codomain sort is not computed anywhere, so tier B's
  F4 has no premise-exact repair; five repairs were priced.
* **B5** — repair C (type-directed interpretation) is *refuted*: a
  proof argument's value must be `pt`, which is the codomain sort
  again.
* **A5** — repair B5′ (supply the sort as a *validity metatheorem*) is
  *refuted*: validity fails at the application clause, because
  `Infer`'s type slot is determined only up to `DefEq` and `HasSort`
  is not `DefEq`-stable (`hasSort_not_defEq_stable`).  Its consequence
  paragraph escalated the fork to the user: reinstate a kernel check
  (A), or bet on an unproved metatheory (B5″).

**The fork is resolved: A, mode-gated.**  `Setlec/SetR/DESIGN.md`'s
new section records it on the lane's side.

### The check

`inferBody`'s `.lam` clause (`Setlec/Kernel/Core.lean`), after the
body's type `bt` is inferred:

```
        if mode.verified && !body.isLam then
          let btt ← r.infer (depth + 1) bt
          let _ ← ensureSort r env (depth + 1) btt
          pure ()
```

— the ∀ clause's own `ensureSort` move, on the codomain.  It is
`HasSort (A :: Δ) B v` (`Setlec/SetR/Annot/Pass.lean`) in the shape the
checker computes it: infer, then whnf to a sort.

**Mode-gated on a new accessor.**  `CheckMode.verified`
(`Setlec/Kernel/Env.lean`) is ON at `.setModel` and `.ttModel`, OFF at
`.noModel`.  It is deliberately **not** `ttChecks`: the fact is a
premise of the *set* lane, so it must run at the default mode; and the
reference kernel's `infer_lambda` does not run it, so the
official-parity lane must not.  `tests/SetlecTests.lean` pins all three
values, in the #148 config-audit style.

### FINDING — the check fires once per λ **chain**, not per λ node

The requested form was per-node.  It is **not reproducible against the
interned checker** and was therefore landed chain-guarded
(`!body.isLam`: at the innermost binder of a λ-chain, on the chain's
body type).  The obstacle, stated so it is not rediscovered:

* The interned twin peels a whole λ-chain in one loop (`inferLamsI`,
  task #72), bulk-opens the residual, and **never materializes the
  intermediate opened body types** — the rebuild is a pure
  `abstractRange` fold with no knot calls.
* A per-node spec check would therefore have to be *manufactured* in
  `inferLams_sound` (`Setlec/Verify/BinderLoop.lean`) for every level
  the loop does not run: at level `j` it is `infer (∀ tyo_j B_j)`,
  whose ∀-rule needs the round trip
  `(bt.abstract1 (d+j)).instantiate1 (.fvar (d+j) n tyo_j) = bt`.  That
  needs `fvarConsistent` and boundedness for the running term at every
  level — the leaf-discipline package (`inferTypeCore_fvarLeaves`,
  `inferTypeCore_looseBVars`, `abstract1_instantiate1`) — which
  `inferLams_sound` does not carry and whose hypotheses would cascade
  up the interned simulation tower (`inferLamsI_tail_sim`,
  `Setlec/Verify/DiscI4.lean`), which is scope-only by design.  The ∀
  loop has no such problem because *its* intermediate values are
  literal sorts (`inferPisWrap_sort`, `whnf_sort`).
* The two alternatives were priced, not argued.  **De-telescoping the
  λ case at the verified modes** restores per-binder nested
  `instantiate1` — the pre-#72 cost on λ-towers, and `perf/app-lam`
  (4 000 binders, 384 G instructions today) is the fixture that would
  pay it.  **Checking every level inside the leaf phase** must rebuild
  each intermediate opened node, `O(k · size)` per chain — same
  fixture, same objection.

**The lane-side record is owed, deliberately.**  This section is the
resolution of `Setlec/SetR/DESIGN.md`'s A5 fork (repair **A**, granted
with the exception above); the matching "A5 RESOLVED" note belongs in
that file, but it was in flight under the T5 agent when this landed and
an edit collision there is not worth a doc placement.  Whoever touches
`Setlec/SetR/DESIGN.md` next should point A5's *Consequence* paragraph
here — the technical content the lane needs is the next two paragraphs.

**Nothing is lost to the lane, but the lane owes an induction.**  At an
outer binder the codomain is the inner λ's own `∀`-type, whose sort is
`imax` of the inner *domain*'s sort — checked at that binder, and
already in `inferTypeCore_lam_inv` — and the chain's body-type sort,
checked here.  `hasSort_pi_of` (`Setlec/SetR/Annot/Validity.lean`,
proved, and recorded in A5's case map as I7's free clause) is exactly
that step, so the bridge derives the per-node premise by a structural
induction along the chain.  A5's own table is the evidence that the
missing piece was never I7: it was I8.

### The inversion

`inferTypeCore_lam_inv` (`Setlec/Verify/InferLemmas.lean`) gains, in
the #147 implication form:

```
      (mode.verified = true → body.isLam = false → ∃ btt v,
        inferTypeCore mode env fuel (d + 1) bt = .ok btt ∧
        whnf mode env fuel (d + 1) btt = .ok (.sort v)) ∧
```

Its four consumers take it as `-`: `Setlec/Verify/InferLeaves.lean`
(three), `Setlec/Model/Core/Infer.lean`,
`Setlec/TTVerify/InferStep.lean`, `Setlec/SetR/Bridge/InferStruct.lean`
— no set-lane or TT-lane proof gained an obligation, the #148 finding
holding for the eighth time.

### Mirror surface

| site | file | role |
|---|---|---|
| `inferBody` `.lam` | `Setlec/Kernel/Core.lean` | the spec, and the inversion's domain |
| `inferLamsLeafI` | `Setlec/Kernel/CoreI.lean` | the interned twin (the binary), shared by `inferBodyI` and `inferBodyNC` |
| `inferLamsLeaf` | `Setlec/Verify/BinderLoop.lean` | the pure mirror the simulation goes through |
| `inferLamsTail` | `Setlec/Verify/BinderLoop.lean` | **new**: the chained λ-tail *at the residual* — the innermost node's check, then the (still pure) `inferLamsWrap` |

`inferBodyNC` passes `.noModel` explicitly (its lane's whole point is
parity), so the one shared loop serves all three modes.  The
identification theorems that had to move: `inferTypeCore_lam_eq`,
`inferLamsLeaf_atF`, `inferLamsLeaf_sound`, `inferLams_sound` (which
gains one hypothesis — the peel's accumulator holds only free
variables, so instantiation preserves the chain guard:
`isLam_instantiateList_fvars`), `inferLamsLeafI_sim`,
`inferLamsI_tail_sim`, `inferLamTail_atF`, plus the λ clause in
`Setlec/Verify/Disc.lean` (scoped-call discipline) and
`Setlec/Verify/Deep.lean` (shift commutation, with
`isLam_shiftFrom`).

### Gates

`lake build` warning-free with the touched modules' oleans
force-deleted and recompiled, `lake test` (including the three new
config guards), arena 90/92, e2e 72/72, split driver 11/11, mode flags
10/10, tt-model sweep `138 arena + 72 e2e identical to default`,
no-model sweep `138 arena + 72 e2e as expected (1 recorded
divergence)`, axioms exactly `[propext, Classical.choice, Quot.sound]`
on the ten set-lane consistency theorems and the three closed TT
theorems, zero sorries.  init-prelude is **verdict- and
byte-identical** — stdout, stderr, exit — in all three modes against a
binary built from pre-change master.

**Corpus-clean, which is the gate that matters here**: this is the
first change that *can* reject a stream the reference accepts (a λ
whose body type has no sort), so every fixture was re-run in every
mode and none moved — including `perf/grind-ring-5` (3 946
declarations) and `perf/app-lam` (97 declarations of 4 000-binder λ
towers), where the named hazard was a fuel-starved `whnf` on a huge
body type.  It did not materialize.

### Negation probe

Byte identity does not prove a new check *runs*.  Negated (the sort
branch swapped with the throw) in the interned leaf and rebuilt:
init-prelude **rejects** at `--set-model` *and* `--tt-model`
(`invalid: expected a sort [at def LT._model]`, exit 1) and still
**accepts** at `--no-model` (exit 0) — the check is alive in both
verified lanes and genuinely off in the parity lane, which is the
gating claim.  Arena falls to 23/92, e2e to 19/72, split 8/11, mode
flags 8/10.  Reverted; verdict identity re-confirmed in all three
modes.

### Cost

`instructions:u`, `--set-model`, median of 3:

| stream | before | after | Δ |
|---|---|---|---|
| init-prelude | 37.4338 G | 37.5153 G | **+0.22 %** |
| grind-ring-5 | 124.3972 G | 124.6520 G | **+0.20 %** |
| app-lam | 384.458 G | 384.380 G | −0.02 % (noise) |
| init-prelude `--no-model` | 20.9853 G | 20.9902 G | +0.02 % (noise) |

(measured against master `cfb5b1e`, after merging it in)

The prediction attached to the grant was "near-noise via the infer
memo — the body type was already inferred, so `ensureSort` is a `whnf`
of a memo-warm term".  The measurement says **a fifth of a percent, not
noise**, and the reason is worth recording: the check does not merely
`whnf` the body type, it **infers** it — `HasSort` is a fact about the
type's *own* type — and that inference is cold, because the body type
is a term the checker built rather than one it walked.  Its subterms
are memo-warm, which is why the figure is a fifth of a percent and not
a multiple.  `app-lam` is the reason the chain guard matters: one check
per λ-chain there rather than 4 000.

## Validated sort annotations: the design (2026-09-01, task #161)

**The user-granted pivot** (docs/sort-coherence-campaign-151.md §7): an
*unverified* annotate pass writes the sort levels of binders into the
term; annotations are first-class term components; the *verified*
checker **validates** them — at the front door against its own
inference, and inside defeq by level-equivalence wherever binders are
compared.  The collapse-free interpretation (`Setlec/SetR/Interp2`,
task #151's goal) reads its regime numerals off validated annotations.
Cross-run sort coherence thereby becomes a runtime-CHECKED property
(mismatch ⇒ decline), not a metatheorem — the six Θ walls
(campaign doc §2) are priced out of the program.  This section is the
design; no kernel code changes land with it.

**Two standing laws, stated first.**

1. **Annotations never steer reduction.**  No whnf/unfold/fire/eta
   decision may branch on an annotation.  They are *written* (the
   pass), *compared* (validation), and *read* (the model) — nothing
   else.  The task-#100 finding is the permanent evidence: every
   annotation-guarded reduction gate was falsified by the empty-domain
   countermodel ("the annotation-guarded reduction gates are
   unsound-to-model", this file).  Validation *compares two levels and
   declines on disagreement*; it never skips or redirects work.
2. **Every annotation mismatch is a decline (exit 2), never a
   reject.**  A mismatch can occur on a well-formed input the official
   kernel accepts (the residual coherence corners, e.g. cross-
   provenance binders in defeq); claiming "invalid" would be wrong.
   The mismatch throw is `.notImplemented` with a per-site message
   (`sort-annotation mismatch (<site>)`), which is also the
   measurement hook.  Pre-existing failures at the same clauses
   (non-sort domain, etc.) keep their current error classes.

### 1. Representation: `BinderMeta` regains levels — two of them

**Decision: in-node, as two mandatory `Level` fields on `BinderMeta`
(and `LIdx` fields on `IBinderMeta`).  `letE` carries no annotation.**

```
structure BinderMeta where       structure IBinderMeta where
  bi : BinderInfo                  bi : BinderInfo
  u  : Level  -- domain sort       u  : LIdx
  v  : Level  -- codomain sort     v  : LIdx
```

* **Why two levels.**  `Interp2`'s F4 refutation
  (`Setlec/SetR/DESIGN.md` "F4", mechanized as `lam_cod_sort_needed`
  in `Interp2/TierA.lean`) proves a structural interpretation's λ
  clause *cannot* be sound from the domain sort alone: the regime
  (squash vs graph) is the **codomain** sort's zero-ness.  `piR v A B`
  / `lamR v A F` dispatch on `v` only; `u` (the domain's sort) feeds
  the kinding tier (`piR_mem_univ`'s `imax u v`) and — decisively —
  makes the λ-chain validation *pure arithmetic* (below).  So
  `forallE`/`lam` both carry `(u, v)`: `ty : Sort u`, and the body's
  type (for λ) resp. the body (for ∀) has sort `v`.  The node's own
  sort is then `imax u v` for a ∀, read off the term with no
  inference.
* **Why not `letE`.**  `interp2`'s `letE` clause is ζ (substitute the
  value) and reads no annotation (`Setlec/SetR/DESIGN.md`, "The two
  regimes": "`letE`: ζ needs no annotation"); the kernel likewise
  ζ-eliminates `letE` before any structural comparison
  (`Core.lean:1487-1492`), so no defeq arm ever compares one.  An
  annotation there would be written and validated but never consumed.
  Revisit trigger, recorded: if a model clause ever reads the `letE`
  type slot, `interp2_letE` is the one clause to revisit — then the
  field is added.
* **Why in-node, not a side table.**  A side table keyed by `EIdx`
  must still be maintained by *every* node-producing walk
  (substitution, level instantiation, intern) — the same work as a
  field, plus a new failure class (missing entries) and a WF clause
  either way.  In-node keeps annotation identity = term identity
  (they are "first-class term components" per the grant), and the #31
  depth-free memo keys inherit automatically: keys are `EIdx`-based,
  and the annotation is inside the node.  Wrapper nodes were not
  seriously considered (every view/match breaks, term depth doubles).
* **Why on `BinderMeta` and not new constructor arguments.**  Pattern
  arity of `.lam n ty body m` / `.forallE n ty body m` is unchanged
  *everywhere* — the `m` variable absorbs the fields.  The migration
  collapses to: (a) literal `⟨.default⟩` constructions (parser,
  pins, basis — see the pin plan), (b) the walks that must *transform*
  annotations (level instantiation), (c) `internBM`/`denoteBM`/arena
  WF plumbing, (d) the pass and validation logic itself.  There is
  also a proof-side bonus precedent: `TowerOk.cons` shares binder
  metadata between a frame and the λ it opens *by construction*
  (task #142's rejected-alternative note), and the one in-flight
  binder manufacture site (below) copies its meta — which is exactly
  the annotation flow the validity lemma wants.
* **Hashing/equality.**  `Expr.hashB` already skips binder metadata
  (`Expr.lean:112-117`) — unchanged.  `ENode`'s derived `Hashable`
  includes `IBinderMeta` — annotations are part of interned node
  identity, `O(1)` via `LIdx`.  `DecidableEq` is full: the defeq
  syntactic fast path (`Core.lean:1734`) now sees annotations, so
  equivalent-but-unequal annotations miss the fast path and fall to
  congruence, where `Level.isEquiv` accepts — verdict-safe, cost
  bounded by normalization (next section).
* **Sharing.**  Annotations are a *deterministic, normalized function
  of the raw term and the environment*, so identical raw subtrees get
  identical annotations and re-share via the cons-table; the arena
  cost is one annotated twin of each binder spine beside its parsed
  raw form (the parse tree holds placeholders until the pass runs).
  Constant-factor; measured at T2.
* **Placeholders.**  The parser interns `⟨.default, .zero, .zero⟩`
  (`Frontend/Export.lean:372-381`).  Placeholders exist only
  pre-annotate and in `--no-model` (where nothing reads or validates
  them).  `canonExpr` (`Export.lean:76-78`) rebuilds metas wholesale
  and thus stays annotation-blind for basis pin canon automatically.
* **Migration cost estimate**: one session for the `Expr`-level sweep
  (compile-error-driven; patterns don't change), one for the interned
  side + `ArenaWF`/`WFStore` clauses (in-range invariants for the two
  `LIdx` fields, the task-#103 pattern).

### 2. The annotate pass: where the levels come from

The pass is the *existing* `annotateBody` (`Core.lean:2077`) /
`annotateBodyI` (`CoreI.lean:2283`) — the input normalizer that every
front door and every install path already threads through
(`ops.annotate` at `CheckerS.lean:393, 612, 681, 756, 777, 794, 816,
833, 854, 1031, 1066`; the driver's per-declaration front door).  **No
new pass and no new call sites.**  Its ∀/λ clauses
(`Core.lean:2107-2117`), today structural rebuilds, additionally write
the meta — gated on `mode.verified`:

* `u := simplify (sortOf ty')` — the annotated domain's sort;
* ∀: `v := simplify (sortOf body')`; λ: `v := simplify (sortOfType
  body')` — the sort of the body resp. of the body's type.

`sortOf` is `ensureSort ∘ infer` with two arithmetic shortcuts that
make the common case inference-free: a *binder* child's sort is
`imax u_c v_c` read off the child's already-written annotation, and a
`.sort w` child's sort is `succ w`.  Only atomic bodies (const/app
heads) infer — and those inferences share the knot's memos with the
validation sweep that follows, so the work is paid once and looked up
once.  (If measurement says otherwise, the deleted `codOf` memo
apparatus — task #100 stage 6, recoverable from git history — is the
prepared fallback; its `IState` slot, spec function and `ISOK` clause
pattern are all recorded in this file.)

* **Normalization at write** (task #85, folded in from the start):
  every written annotation is `Level.simplify`-normalized, minimizing
  syntactic divergence at fast paths and cons-tables.  Comparisons are
  by `Level.isEquiv` regardless, so normalization is a cost lever, not
  a soundness lever.
* **Determinism.**  The pass is a pure function of `(env, term, fuel)`
  — same algorithm at install and at use, so a stored constant's
  annotations and a use site's annotations of the same syntactic type
  agree syntactically, not just up to `isEquiv`.
* **Trust status.**  The pass stays OUT of the truthfulness story: no
  `annotate_sound` is resurrected.  Its verification obligations
  remain what they are today (scope discipline, the interned
  simulation).  Truthfulness of what it wrote is established by the
  validation sites, on the checker's own runs.
* The normalizer clauses (projection rewrite, ζ, literal guards, fvar
  scope) are untouched and stay unconditional in all modes.

### 3. Validation sites, exactly

**(a) Front door — `infer`, gated `mode.verified`** (the accessor task
#152 introduced, `Env.lean:54-56`).  The driver's per-declaration
inference sweep visits every node of every stored type and value, so
this is where input annotations become *validated* annotations.

* **∀ clause** (`Core.lean:1589-1598`; interned `inferPisI`,
  `CoreI.lean:1824-1838`): the loop already infers each opened
  domain's sort on the way in (`CoreI.lean:1833`) — compare it
  `isEquiv` against the node's `u`.  The rebuild fold `inferPisOutI`
  (`CoreI.lean:1800-1804`) computes exactly the per-node codomain
  sorts as its intermediates — compare each against the node's `v`.
  `O(1)` per binder, on data the loop already holds.
* **λ clause** (`Core.lean:1599-1630`; interned `inferLamsI` /
  `inferLamsLeafI`, `CoreI.lean:1759-1795`): the domain sort is
  inferred on the way in (`CoreI.lean:1789`, currently discarded —
  bind it) — compare against `u`.  The codomain: at the chain's
  innermost node the task-#152 check already computes the body type's
  sort (`CoreI.lean:1766-1771`, currently discarded — bind it) —
  compare against the innermost `v`; at every outer node `v_j` must be
  `isEquiv` to `imax u_{j+1} v_{j+1}` of the inner node's annotations
  — **pure level arithmetic**, no opened intermediate types needed.
  FINDING, recorded: this *dissolves task #152's per-chain
  restriction* — the obstruction was that the interned bulk loop
  never materializes intermediate opened body types, but the inner
  node's annotations ARE materialized, and the per-node fact is a
  function of those alone.  The λ-rule finally has its I7 sort
  premise per node, at `O(1)` each.
* **`letE` clause**: unchanged (`Core.lean:1682-1685`) — no
  annotation, nothing to validate.

**(b) Defeq — `defeqStep`'s binder arms.**

* `forallE`/`forallE` (`Core.lean:1872-1880`) and `lam`/`lam`
  (`:1881-1884`): after the domain defeq succeeds, compare `v₁`
  `isEquiv` `v₂`; mismatch throws the decline.  **`u` is deliberately
  not compared**: `piR`/`lamR` dispatch on `v` only, domain-value
  agreement flows from the domain defeq, and a `u` comparison would
  add decline surface with zero soundness payoff (two defeq domains
  may sit in different universes without harm).
* `etaCert` (`Core.lean:1027-1040`): the one-sided λ against the
  whnf'd `∀`-type of the stuck side — compare the λ's `v` against the
  ∀'s `v` (the regime agreement `lamR_eta` needs; this is the
  annotation-era successor of the cod-agreement comparison task #100
  deleted).
* `letE` arms: none exist (ζ in `whnfCore`, `Core.lean:1487-1492`).
* Everything else in defeq (proof irrelevance, lazy delta, spine
  congruence, stuck fallbacks) reads no annotation.

**(c) Install time — free, via the existing threading.**  Every
stored type, value, iota-rule RHS, projection rule, and pin
certificate already runs `ops.annotate` then `ops.inferType` on the
annotated result (`CheckerS.lean:393-398` types, `:756-762` values,
`:612-619` rule RHSs, `:681-705` proj rules, `:816-820`/`:833`/
`:854-855` nat-op/trust pins, `:1031-1049`/`:1066-1072`), so (a)
covers storage with **no new install calls**.  "Valid under all
valuations" is exactly what this buys: validation runs at the symbolic
level parameters, and `Level.isEquiv` decides evaluation-equality at
*every* assignment (`isEquiv_sound`), so symbolic validation plus
`Level.subst`/`eval` composition gives per-instantiation validity —
the checker computes the universal fact natively, no per-valuation
enumeration exists or is needed.

**Failure behavior, per site** (law 2): all eight comparison points
decline with a site-naming message — `(forall-domain)`,
`(forall-cod)`, `(lam-domain)`, `(lam-cod-leaf)`, `(lam-cod-chain)`,
`(defeq-forall)`, `(defeq-lam)`, `(eta)`.  Install-time mismatches
decline the declaration (existing convention).  Rationale: a mismatch
is a positively detected limitation of *this design* on possibly
official-accepted input; rejecting would claim the input is invalid.

### 4. The manufacture-site audit

Every kernel site that produces a binder node not present in the
input, with its annotation source and validity-lemma sketch.  The
headline result of the audit: **exactly one site manufactures a binder
in-flight from non-binder parts** (row 1); everything else is
substitution transport, install-time (pass-covered) construction, or
binder-free fabrication.

| # | site | what is built | annotation source | validity lemma sketch |
|---|---|---|---|---|
| 1 | λ-infer rebuilds the ∀ — `Core.lean:1629` `.forallE n ty (bt.abstract1 depth) mb` | a ∀ from the λ's parts | **the λ's own meta `mb`, copied verbatim** (automatic under the `BinderMeta` representation) | `AnnotValid(λ) → AnnotValid(∀)`: same domain so `u` transfers; the λ's `v` claims "body's type has sort `v`", which IS the ∀'s claim "codomain has sort `v`".  One lemma, against `interp2`'s clauses. |
| 2 | β / ζ / binder opening — `Core.lean:1436, 1492, 1596, 1605, 1879-1884` (`instantiate1`/`instantiateList`) | substitution instances | copied nodewise (annotations are `Level`s; term substitution never touches them — `Interp2` F3: numerals are carried, never read, by `liftN`/`inst`) | `AnnotOkV` closed under instantiation at a domain member, via `interp2_inst`; the member fact is the site's own certificate (β: `Core.lean:1434-1435`; ζ: the front door's `:1682-1685`; opening: the frame's fvar membership) |
| 3 | δ-unfolding — `Core.lean:175/180` (`value.instantiateLevelParams`) | stored value at instance levels | install-validated value annotations, level-substituted (the extended `Expr.instantiateLevelParams`) | `annotValid_instL`: symbolic validity at the params + the arity guard (`:174`) ⇒ validity at every instance; `Level.subst`/`eval` composition (already in `Verify/Level`) |
| 4 | ι-fire RHS — `Core.lean:1349-1350` (`rl.rhs.instantiateLevelParams` + `mkAppN`) | rule RHS at instance levels | rule RHS annotated+validated at install (`CheckerS.lean:612-619`); arity guard = checker change #9 (`Core.lean:1284`) | same as row 3; `mkAppN` builds only apps |
| 5 | K-rescue fabrication — `Core.lean:1095` | `ctor` applied to type args | **no binder built**; constituents are copied subterms of the whnf'd major type | none new (constituent transport) |
| 6 | η-rescue fabrication — `Core.lean:1158` + `etaFabArgs` `:1059-1062` | `ctor` applied to type args + projection applications | **no binder built** | none new.  The Θ (p1) hazard (`iotaEta`'s free `ust` existential) does not touch annotations: nothing here fabricates a binder |
| 7 | η comparison term — `Core.lean:1036-1038` `.app b (.fvar …)` | an app + fvar | fvar's type copied from the validated λ domain | none new; the *new check* here is the `v` agreement (site (b)) |
| 8 | proj expansion/template fallback — `annotateProjRec` `Core.lean:1990-2027` (motive λ `:2017`, minor via `pisToLams` `:2003`), `annotateProjElim` `:2036` | motive/minor λs | **re-annotated by the pass** (`r.annotate` at `:2021`/`:2051`) and re-checked by the ordinary rules — annotate-time, so front-door-validated | covered by pass+validation; no separate lemma |
| 9 | `pisToLams` at install — `CheckerS.lean:677`, `CheckerBase.lean:249` (`ExprOps.lean:481-484`) | proj-rule λ tower from the ctor's Π tower | the Π metas it copies are WRONG for λs (`v` differs) — **placeholder-grade**; both consumers feed `ops.annotate` (`CheckerS.lean:681`), which overwrites | rule + docstring on `pisToLams`: its meta copy is placeholder; every consumer must annotate before store/use (audit: both do) |
| 10 | nat-op cert substitution — `Expr.substConstAll` `Core.lean:629-640`, equations `:533` (binder-free by construction, `:532`) | cert statements with the op inlined | copied metas; statements re-annotated + inferred at install (`CheckerS.lean:816-820`) | covered by pass+validation |
| 11 | hand-built types — `TrustAxioms.lean:106-118`, `StdAxioms.lean` `*A` pins (`:137-385`), `Basis/*.lean` blocks, `NatOpPins`, `TrustPins`; `Direct.lean:218` (dead route, #148 T0b) | pinned ∀s | **regenerated** annotated literals via `AnnotateBasis.lean` (the lakefile root target built for exactly this in the pre-#100 era, still present) — `Expr.eraseNames`/`ErasedEq` stay untouched, the task-#142 route | pin-vs-stream agreement is syntactic (same deterministic pass on both sides); any miss surfaces as a measurable decline |
| 12 | literal expansions — `Core.lean:228-231, 324-330`; comparands `recFireComparands` `:1242-1252` (stored pins, install-annotated via `checkAnnotList` `CheckerS.lean:580`) | apps/consts only | rows 2/3 transports | none new |

Θ cross-reference: W1/W6 (rescue fabrication-from-annotations) → rows
5/6, burden zero (no binder fabricated); etaL/etaR residues → row 7
plus the `(eta)` check; projCong → already deleted by checker change
#10; the δ-sim residue → row 3.  The campaign's claim — "the residual
proof burden localizes to the manufacture-site audit, and the sites
are finitely many and already named" — survives contact with the
sources: one real lemma (row 1), two transport lemmas (rows 2–3), and
discipline notes.

### 5. Verification plan

**The invariant.**  `AnnotValidV` (working name; `AnnotOkV.lean` is
the seeded namespace): for every binder in every checker-touched term,
under every valuation `φ` and frame-consistent environment: the domain
interprets into `univ (u.eval φ)`-grade and every fibre's body-type
value lies in `univ (v.eval φ)` — tier B's premise shape, stated
against `piR`/`lamR` (`Interp2/Ops.lean`); the positive half is
already mechanized (`lamR_sound_at_every_regime`, `Interp2/TierA`).

* **Establishment**: at the front door, from the validation conjuncts
  of the run's own inversions — the same mechanism by which task #100
  stage 6 replaced `annotate_sound` with `inferTypeCore_sound`
  ("the inference run is the truthfulness witness").  Explicitly NOT
  the A5-refuted shape: no validity metatheorem over `Infer` is
  claimed (that was refuted at the application clause,
  `hasSort_not_defEq_stable`); the fact comes from the run's recorded
  comparisons, per term, per site.
* **Preservation**: `interp2_inst` (F3) for term substitution;
  `annotValid_instL` (new, small) for level substitution; the row-1
  lemma for the one in-flight manufacture.
* **Consumption**: the AVExpr swap per F4 — `Interp2/Syntax.lean`'s
  provisional node (which already carries `lam (u v)` / `pi (u v)`)
  is replaced by the annotated kernel syntax; `interp2` reads the
  regime numeral off validated `BinderMeta.v`.
* **What changes in `Verify/`**: `inferTypeCore_forall_inv` /
  `inferTypeCore_lam_inv` gain implication-form conjuncts
  (`mode.verified = true → isEquiv … = some true`) — the exact #147/
  #152 interface pattern, consumers take them as `-` until the SetR
  lane consumes them (the #148 finding, held eight times); the defeq
  binder-arm inversions gain the `v`-agreement conjunct; the interned
  simulation tower relates the extended metas (one `denoteBM` clause).
  **Untouched**: the whnf walks and every reduction-side proof (law 1:
  reduction never reads annotations), the scoped-call discipline, the
  fourteen `*_R` theorems' statements (they are mode-generic and gain
  nothing until the collapse-free interpretation replaces the
  collapse).
* **Θ-4 compliance**: no new statement concludes
  `∃ L', defeqLoop … = .ok true`; every new conjunct is an inversion
  of a run in the premises.
* **Parked-lane transfer**: `Interp2/*` wholesale (landed on master);
  the tier-A files (`Annot/Syntax,Pass,Validity,Kinding` —
  `hasSort_pi_of` is the λ-chain induction's step); the countermodels
  as regression guards (`lam_cod_sort_needed`, the #100 gated-beta
  countermodel, the Θ probes `delta151`/`inverse151`/the compound
  pair, kept as fixtures).  The Θ Engine's pure algebra
  (`Absorb`/`Engine.lean`) is NOT consumed — its purpose (classifying
  image walks) is what this design replaces with checks; it stays
  parked with the campaign record.  `SortCoh*`/`ThetaLock` retire in
  place.

### 6. Measurement plan

* **Counters**: the shipped mechanism is the eight per-site decline
  messages (grep-able per stream); a `CPMASK`-style instrumentation
  patch (task #141 pattern, kept in `_tmp/annot-161/`) counts
  comparisons and near-misses without shipping state.
* **Acceptance ladder**, each rung gated before the next: `lake
  build`/`lake test` → arena 90/92 + e2e, all modes → init-prelude
  (3653 decls; gate: **zero mismatch declines**, verdict-identical,
  `--no-model` byte-identical, cost ≤ +5 % instructions at
  `--set-model`) → grind-ring-5 and app-lam (the 4 000-binder chain
  fixture; per-node arithmetic must stay `O(n)` per chain) →
  init-full (gate: taint-frontier parity, zero mismatch declines) →
  Mathlib 40 % prefix (observation rung; measured, not gated).
* **Abort criteria**: (i) any mismatch decline on an
  official-accepted stream that survives one diagnosis session
  without a pass/normalization fix is a STOP-FINDING (report, per the
  standing rule); a systematic cross-provenance defeq mismatch class
  with no normalization repair kills the design — the record then
  goes to the campaign doc as its §9.  (ii) Cost: > +10 % at
  `--set-model` after memo sharing ⇒ redesign the pass's sort
  computation (the `codOf` memo revival) before proceeding; > +25 %
  ⇒ stop.  Expected: near the task-#152 scale (+0.2 % was one
  cold inference per λ chain; this adds `O(1)` comparisons per binder
  plus the pass's memo-shared inferences).

### 7. Mode integration

Gating is the existing `CheckMode.verified` accessor
(`Env.lean:54-56`) — **no new mode, no new flag**.

* `--set-model` (default): pass writes, all sites validate, the model
  (eventually) reads.
* `--no-model`: parser placeholders persist; the pass's sort
  computation and every validation site are off; the NC stack
  (`CoreNC`/`CheckerNC`) is untouched beyond the meta-arity ripple;
  gate: byte-identical to master.
* `ttChecks` stays constantly `false` (`Env.lean:43-44`, post-T7b);
  the seven gated sites are not touched.
* Master's current behavior remains available throughout: T1/T2 are
  write-only (verdict byte-identical in both modes, gated), so
  `--set-model` equals master until T3 lands, and `--no-model` equals
  master permanently.

### 8. Owed environment records (Θ batch-book handover, landed here as tasks)

Three install-checked facts are consumed nowhere because `EnvWF` never
records them; T4 adds them as invariant clauses with preservation at
install (the direction "invariants over runtime gates"):

1. **`r.nfields = cnF`** — checked at `CheckerS.lean:606-607`,
   unrecorded; it is `iotaK`'s result-determinism premise (the (p1)
   record: "`iotaK` IS result-deterministic — `cnF = 0` makes the
   reduct targs-independent — but its premise is unrecorded").
2. **nat-op stored-value coherence** — the pre-insertion
   certification against the substituted value
   (`CheckerS.lean:816-820`, the `Core.lean:436-462` presence-is-
   certificate contract), unrecorded.
3. **`defnInfo` type-value coherence** — `vtype ≡ cv.type` at install
   (`CheckerS.lean:761-762`), unrecorded.

### 9. Task breakdown

| task | content | gate | estimate |
|---|---|---|---|
| T1 | representation: `BinderMeta`/`IBinderMeta` fields; parser placeholders; `instantiateLevelParams` (+ interned `instantiateLevelParamsIGo`) map annotations; `internBM`/`denoteBM`/`ArenaWF`/`WFStore` clauses; `⟨.default⟩` literal sweep | build warning-free; **byte-identical verdicts, all modes** | 1–2 sessions, mechanical |
| T2 | the pass writes: `annotateBody`/`annotateBodyI` ∀/λ clauses + arithmetic shortcuts + simplify-at-write; `AnnotateBasis` regeneration of `Basis/*`, `StdAxioms` `*A`, `TrustAxioms`, pins; storage-uniformly-annotated audit | byte-identical verdicts (nothing reads yet); cost measured | ~2 sessions |
| T3 | validation: front-door ∀/λ (spec + interned loops), defeq `v` arms, `etaCert`, decline plumbing + per-site messages; negation probes (#147 style); ladder through init-full | ladder gates of §6 | 2–3 sessions |
| T4 | the three owed `EnvWF` records + inversions | build + proofs green | 1 session, parallel to T2 |
| T5 | `Verify/` inversion conjuncts (implication form), sim-tower meta clauses, consumers `-` | axioms pinned, zero sorries | ~2 sessions |
| T6 | the model phase: AVExpr swap (F4), `AnnotValidV` establishment from the front-door inversions, `annotValid_instL`, the row-1 lemma, the `interp2` bridge into the SetR lane | the lane's own ledger resumes; consumption probes first | research-paced |
| T7 | measurement closeout per rung; standing abort review | §6 criteria | continuous |

### 10. Top risks

1. **Cross-provenance defeq mismatches on real streams** — the
   unprovable coherence corners resurfacing as declines.  This is the
   design's premise made observable: mitigation is semantic
   comparison (`isEquiv`, never syntactic) + simplify normalization +
   the per-site decline messages; §6's abort criterion bounds the
   exposure.
2. **Cost** — the pre-#100 pass's inference sweep priced at roughly
   the front-door sweep, and annotations split binder-node sharing
   between raw and annotated twins.  Mitigation: memo sharing within
   the declaration, the arithmetic shortcuts (most `v`s are
   inference-free), measured gates at T2/T3 with hard thresholds.
3. **T6's establishment step** — threading frame/valuation
   quantifiers from the run inversions into `AnnotValidV` without
   resurrecting the refuted validity-metatheorem shape; and the audit
   table's completeness (a binder manufactured somewhere unlisted).
   Mitigation: probe-first discipline (a consumption probe on a
   nested-manufacture example before the lemma battery), and the
   table's grep-audit is re-runnable
   (`grep -n "\.forallE (\|\.lam (" Setlec/Kernel/*.lean`).

## Task #161 amendment 1: prop-only annotations, proof-first phasing (2026-09-01)

Two user directives amend the accepted design before any
implementation: (1) build the checker and the consistency proof first
— "annotating is untrusted and just engineering" — the pass moves to
the engineering tail; (2) audit whether the annotation needs the sort
*level* at all, or only prop-ness ("'always type' or 'prop if all
these parameters are zero' — simple to normalize and compare").

### The prop-only audit: VERDICT — prop-ness suffices; both levels drop

**(a) What `interp2` reads from `v`: the zero-test, nothing else.**
The operators are (`Interp2/Ops.lean:52-58`):

```
noncomputable def piR (v : Nat) (A : V) (B : V → V) : V :=
  if v = 0 then truthVal (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) else piSet A B
noncomputable def lamR (v : Nat) (A : V) (F : V → V) : V :=
  if v = 0 then pt else graph F A
```

— `v` occurs *only* in the `if v = 0` test; the graph branch does not
use its value.  The module states it outright (`Ops.lean:93-94`):
"`piR`/`lamR` read their numeral **only through the `v = 0` test**, so
annotations that agree on zero-ness are interchangeable", and proves
it as the zero-agreement battery `piR_zero_agree`/`lamR_zero_agree`/
`lamR_mem_zero_agree` (`Ops.lean:102-146`) — hypotheses of the shape
`v = 0 ↔ v' = 0`.  Task #100's own finding said the same thing a
tier earlier (this file, "Raw (annotation-free) storage"): "the
interpretation reads its level argument only through the `v = 0`
test (`pi_pos`/`lam_pos`), so what a binder needs is exactly one
bit."

**The F4 refutation forces the bit, not the level.**
`lam_cod_sort_needed` (`Interp2/TierA.lean:74-82`):

```
theorem lam_cod_sort_needed (L : Nat → V → (V → V) → V)
    (hL : ∀ (u v : Nat) (A : V) (F B : V → V),
      (∀ x, x ∈ˢ A → F x ∈ˢ B x) → L u A F ∈ˢ piR v A B) : False
```

Its witness is one fibre assignment read at `v = 0` and at `v = 1` —
the two readings differ exactly in the codomain's *zero-ness*.  A
clause handed the bit (`lamR (if bit then 0 else 1) …`) is sound at
both regimes (`lamR_sound_at_every_regime`, `TierA.lean:87-89`), so
F4 refutes bit-less clauses and nothing stronger.

**(b) `u` (the domain sort) is read nowhere — it drops entirely.**
`TierA.lean:21-22`, verbatim: "(`u` is not wrong, just not
sufficient: `interp2` reads it nowhere, tier C may.)"  The two uses
the accepted design kept `u` for both dissolve:

* *Kinding/universe placement*: `piR_mem_univ` (`Interp2/Univ.lean:73`)
  takes semantic `u v : Nat` supplied by its *consumer* — in the
  soundness walks those are the checker's own inferred sorts (the run
  computes them: `Core.lean:1593-1597` infers both `∀`-rule sorts,
  never reading an annotation), bridged to the annotation-driven
  value by `piR_zero_agree`/`lamR_mem_zero_agree` under the validated
  bit-agreement.  `Interp2/Value.lean`'s own convention is the
  precedent in the tree: bval towers already annotate every λ with
  the *result* sort — correct only up to zero-ness — and bridge to
  exact statements through `lamR_mem_zero_agree`; the exact numerals
  in its motive-space *statements* are model-side data, not reads
  from the syntax.
* *λ-chain validation arithmetic*: `imax_eq_zero_iff`
  (`Ops.lean:118-126`) — `imax x y = 0 ↔ y = 0` — makes prop-ness of
  every telescope suffix equal to prop-ness of the leaf, so the
  chain rules trivialize (below) and `u` is not needed even for
  validation.

**(c) Universe placement is recomputed semantically** — the syntax
supplies the dispatch bit only; every exact level in a membership or
placement fact flows from the checker's run (inferred sorts in the
inversion premises) into the model statements, exactly as in v1.
Re-open trigger, recorded: if tier C ever needs a *domain*-sort datum
read off the term, that is a new consumer and this verdict is
re-audited (the one place the record reserves it: `TierA.lean:22`
"tier C may").

**(d) The canonical normal form, verified.**  Define
`Z(l) := {φ | l.eval φ = 0}`.  Computing by induction:
`Z(zero) = all`; `Z(succ _) = ∅`; `Z(max a b) = Z(a) ∩ Z(b)`;
`Z(imax a b) = Z(b)` (since `eval (imax a b) φ = 0 ↔ eval b φ = 0` —
if `eval b φ ≠ 0` the `imax` is a `max ≥ eval b φ > 0`; this is
`imax_eq_zero_iff` at the eval level); `Z(param u) = {φ | φ u = 0}`.
So `Z(l)` is **always** either `∅` or `{φ | ∀ u ∈ P, φ u = 0}` for a
finite param set `P` (`P = ∅` = always).  The canonical datum:

```
inductive PropWhen where
  | never                        -- the codomain sort is never zero
  | ifAllZero (ps : List Name)   -- zero iff every param in ps is zero
                                 -- (canonical: sorted, deduplicated)
```

with `zeronessOf : Level → PropWhen` the one-pass computation
(`zero ↦ ifAllZero []`, `succ ↦ never`, `max ↦ ∩` [never absorbs,
else union], `imax a b ↦ zeronessOf b`, `param u ↦ ifAllZero [u]`).
**Distinct canonical forms denote distinct predicates** (`never` vs
`ifAllZero P`: the all-zero valuation separates; `ifAllZero P` vs
`ifAllZero Q`, `P ≠ Q`: a valuation sending a name in the difference
to `1` and the rest to `0` separates), so **datum equality is sound
AND complete for zero-ness agreement over all valuations** — no
`Level.isEquiv`, no `leqCore` fuel, no `simplify` subtleties: the #85
concern vanishes rather than being folded in.  Substitution has a
compositional pushforward `substPW`:
`substPW σ never = never` (a never-zero level stays never-zero under
substitution — evals compose); `substPW σ (ifAllZero P) =` the `∩`
over `u ∈ P` of `zeronessOf (σ u)`.  The commutation lemma
`zeronessOf_subst : zeronessOf (Level.subst ks vs l) =
substPW ks vs (zeronessOf l)` replaces the accepted design's
`annotValid_instL` in the δ/ι manufacture rows.

**(e) Validation stays cheap — cheaper.**  Front door: the checker
computes the codomain sort it already computes (`∀`: the
`inferPisLeafI` leaf sort, `CoreI.lean:1808-1817`; λ: the task-#152
leaf check, `CoreI.lean:1766-1771`), applies `zeronessOf` **once per
telescope**, and compares data for equality per node.  The chain
rules collapse: along a Π-telescope every node's datum equals the
leaf's (`Z(imax u rest) = Z(rest)`, iterated), and along a λ-chain
every node's datum equals the inner node's (the type of `body_j` is
the inner `∀`, whose sort's zero-ness is the inner codomain's) — so
outer-node validation is *datum equality with the neighbour*, no
arithmetic at all.  Defeq arms and `etaCert` compare data by
decidable equality.

**(f) What defeq compares, precisely: the canonical datum
syntactically — which IS the predicate, and predicate equality is
exactly the needed strength.**  The soundness statements quantify
over every valuation `φ` (the model is level-polymorphic, this file
"The model"), and the binder-congruence conclusion
`piR_zero_agree` needs `bit₁(φ) ↔ bit₂(φ)` at *every* `φ` — i.e.
`Z`-equality, i.e. (by (d)'s completeness) datum equality.  It is
also *minimal*: if two data differ, some `φ` separates them, and at
that `φ` the two interpretations genuinely diverge (one side a truth
value/`pt`, the other a `piSet`/graph — `piR_pos_not_mem_univZero`,
`Univ.lean:93`), so any weaker comparison would be unsound-to-model.
"Instance-level" comparison at the current declaration's parameters
is not a checker-side notion (parameters are symbols); everything the
checker holds is already instantiated into the declaration's context
by `substPW`-carrying walks, and the comparison of the resulting data
is the all-`φ` predicate agreement the model consumes.  Consequence
for the decline surface: annotation pairs that differ in level value
but agree in zero-ness — e.g. the λ-tower result-sort convention
(`Value.lean`), `Sort 3` vs `Sort 5` codomains — can no longer
mismatch; **every remaining mismatch is a genuine regime
disagreement**, the semantically dangerous case and nothing else.

### The re-specified representation (supersedes amendment target §1)

```
structure BinderMeta where     -- Expr.lean:72; IBinderMeta identical
  bi : BinderInfo              --   (denoteBM stays the identity)
  pw : PropWhen                -- codomain prop-ness, canonical form
```

**One datum per binder** — `u` and `v` are gone.  `letE` still
carries nothing (unchanged verdict).  Notes replacing the two-level
plan's:

* `PropWhen` lives beside `Level` in `Expr.lean`; the interned meta
  stores it **unchanged** (raw `Name`s).  Precedent: the level arena
  itself stores raw level-param names (`LNode.param (n : Name)`,
  `IExpr.lean:141`) — level params are outside the #88 name-interning
  regime already.  Lists are tiny (≤ a declaration's `levelParams`);
  if intern-probe hashing ever shows up in a profile, migrating `ps`
  to sorted `NIdx` lists is a recorded, mechanical follow-up.
* Canonical form (sorted, deduplicated `ps`) is a **producer
  discipline**: `zeronessOf`, `substPW`, and the parser all emit it;
  a total order `Name.leb` (structural lexicographic) is added for
  it.  Validation and defeq compare only producer outputs.
* `Expr.instantiateLevelParams` (`Expr.lean:190`) and
  `instantiateLevelParamsIGo` (`IExpr.lean:1356`) map `pw` by
  `substPW` — the one walk that transforms annotations (term
  substitution still never touches them).
* `Expr.hashB` still skips metas; `ENode` equality includes `pw`
  (first-class identity); the checker-diff summary of the accepted
  design otherwise stands with `isEquiv v₁ v₂` replaced by `pw₁ = pw₂`
  everywhere, and the eight decline sites keep their names.
* The `interp2` bridge evaluates the datum at a valuation:
  `pwHolds φ pw : Bool`, and the clause reads
  `piR (if pwHolds φ pw then 0 else 1) …` — `Interp2/Ops.lean`,
  `Univ.lean`, `Value.lean` need **no changes**; the zero-agreement
  battery is the designed bridge to exact-level statements.

### Proof-first phasing (supersedes amendment target §9)

The pass is untrusted engineering and moves last; the goal is the
consistency proof for the checker **on sort-annotated syntax** — the
capstone is `no_proof_of_Empty` for annotated input.  New order:

* **P1 — representation** (was T1, re-specified above): `PropWhen` +
  `zeronessOf`/`substPW`/canonicity lemmas, `BinderMeta.pw`, walks,
  parser, plumbing.  GATE: full battery + init-prelude
  **byte-identical** vs master, both modes (parser default `.never`,
  nothing reads it).
* **P2 — annotated input + validation semantics** (was T3): the
  export-format extension (below), hand-annotated pins/basis, the
  eight validation sites gated `mode.verified`, decline messages,
  hand-annotated fixtures in `tests/` exercising accept and each
  decline site.  GATE: `lake test` + the fixture family +
  `--no-model` byte-identical; **suite re-point** (needs
  ratification): from P2 on, `--set-model` on *unannotated* streams
  declines at the first Prop-codomain binder by design — the
  `--set-model` arena/init sweeps are suspended in favor of the
  annotated fixture suite until P5 restores them; `--no-model` keeps
  the full parity suite green throughout.
* **P3/P4 — the proof** (was T5/T6): inversion conjuncts
  (implication form) for the eight sites; `AnnotValidV` stated on the
  bit (per-binder: the datum's predicate agrees with the codomain
  sort's zero-ness under every `φ`); establishment from the run's
  validation conjuncts; preservation (`interp2_inst`,
  `zeronessOf_subst`, the row-1 λ→∀ meta-copy lemma); the AVExpr
  swap; the `interp2` bridge and the annotated-checker capstone.
  Plus P0-owed: the three environment records (unchanged).
* **P5 — the engineering tail** (was T2 + T7): the annotate pass
  (writes `zeronessOf` of the sorts it infers), `AnnotateBasis`
  regeneration, the measurement ladder (init-prelude → init-full →
  Mathlib) and the abort review.  Only here do real streams re-enter
  `--set-model`.

**The annotated-input format** (part of the checker's input spec now,
not of the pass): the export ndjson's `lam`/`forallE` expression
entries (`Frontend/Export.lean:371-382`) gain one **optional** field
`"pw"`: absent → `.never` (the parse default — a definite,
validatable claim, so T1 stays byte-identical and unannotated
fixtures fail loudly at P2, not silently); `"pw": "never"` →
`.never`; `"pw": [i₁, …]` → `.ifAllZero` over the stream's *name
table indices* (the format's existing index discipline), canonicalized
at parse.  Real exporters never emit the field; hand-written fixtures
and (later) the pass's internal output are its producers.

**Pins without the pass**: the pinned literals (`Basis/*`,
`StdAxioms` `*A` forms, `TrustAxioms.lean:106-118`) are
**hand-annotated** at P2 — their binders' codomain prop-ness is
statically evident, the counts are small, and the install-side
validation checks our hand annotations (a wrong one declines its own
install: self-correcting, mechanical to fix).  The elab-time
generated pins (#53: `NatOpPins`, `TrustPins`, `DivModPin`) compute
`pw` **at generation time** from the host elaborator's `inferType`
(trusted exactly as far as the pins already are, and re-validated by
our checker at install); the #113 module-strip interaction is
unchanged (`pw` is plain data in the same `ToExpr`-pinned literals).

### Revised risks

1. *(shrunk)* Cross-provenance defeq mismatches: only genuine regime
   disagreements remain (audit (f)); comparison is complete — the
   `isEquiv`-incompleteness and normalization decline classes are
   gone.  Abort criteria unchanged.
2. *(shrunk)* Cost: datum equality replaces level `isEquiv` at every
   site (no `leqCore`, no fuel); one `zeronessOf` per telescope.
   The pass-side cost question is deferred to P5 with the pass.
3. *(unchanged in kind)* P3/P4's establishment step and audit
   completeness — probe-first discipline stands.
4. *(new)* Proof-first ordering defers real-stream feedback to P5: a
   defect in the annotation language would surface late.  Mitigation:
   the P2 fixture family is drawn from real declaration shapes
   (including a λ-tower with the result-sort convention, a
   parametric `Sort u` codomain, and an `imax`-sorted telescope), and
   the audit's (d)-completeness lemma is mechanized at P1, not
   assumed.
5. *(new)* Hand-annotated pins: a wrong `pw` declines its own basis
   install — loud, local, mechanical; the generated pins compute
   theirs, leaving only the small hand-written set.

## Task #161 P1 SEAL: the representation lands (2026-09-01)

**Landed** (branch `agent/annot-v2`): `BinderMeta`/`IBinderMeta` carry
`pw : PropWhen`; the walks, the arena, and every proof tier adapted;
parser and all pinned literals at the placeholder `⟨.default, .never⟩`.

**Amendment 2 — the datum is a raw set, not a sorted canonical form
(in-flight revision of amendment 1(d), forced by proofs).**  The
ratified design ordered `ps` sorted and deduplicated so that `=`
decides zero-ness agreement.  Implementation falsified two things
about any *normalizing* `substPW`:

* `Expr.instantiateLevelParams_self` (`Verify/InstLevels.lean`, nine
  consumers in `SetR/Install/BasisS.lean`, `Interp2/Claims2U.lean`,
  `Interp2/Step2/Whnf.lean`) is FALSE for non-canonical metas — even
  the empty substitution re-sorts;
* the composition law is FALSE outright for data with parameters
  outside the inner substitution's domain — for *any* representation
  (`pw = ifAllZero [n]`, `n ∉ ps`, `n ∈ ks`: the left side
  substitutes `n`, the composed right side cannot).

The repairs, both landed:

* **`substPW` is the shape-preserving `PropWhen.bindZ`** (each
  parameter becomes its replacement's `zeronessOf`, intersected;
  `inter` is `never`-absorption plus list *append* — no sort, no
  dedup).  `substPW_self` and `zeronessOf_subst` then hold
  *unconditionally and syntactically* (`Verify/PropWhen.lean`), and
  `Name.leb`, `mergeNames` and the sorted-extensionality battery were
  never needed — deleted before landing.
* **Completeness moved from `=` to the containment test
  `PropWhen.equiv`** — `equiv_iff_holds`: `equiv p q = true ↔ ∀ φ,
  p.holds φ = q.holds φ`, sound AND complete, fuel-free (the
  separating valuations: all-zeros, and the indicator of a
  disagreeing name).  The P2 validation and defeq sites compare with
  `equiv`, never `==`; kernel reduction still never reads `pw`.
* **`PropWhen.paramsDefined` folded into
  `Expr.allLevelParamsDefined`** (binder clauses) — the composition
  counterexample above is exactly the level side's own definedness
  hypothesis surfacing for the datum; `substPW_comp` holds under it
  (`Verify/PropWhen.lean`), and `substPW_paramsDefined` mirrors
  `Level.allParamsDefined_subst`.

**Findings, recorded:**

1. **The has-param shortcut must see `pw`** — `Expr.hasLevelParam`,
   `ENode.hasLParamOf` (eager `eparamBs`, task #87), `nodeHasLParam`
   and `allLevelParamsDefinedIGo` all gained the `pw` clause: the
   interned level-instantiation walk shortcuts on `ehasParamD`
   (`IExpr.lean`), and with `instantiateLevelParams` now substituting
   into metas the shortcut's exactness lemmas
   (`instantiateLevelParams_eq_self`, `ehasParamD_exact`) demanded it.
   `PropWhen.hasParams=false ⇒ substPW = id` (`substPW_eq_self`,
   `ArenaWF.lean`) is the meta half of the shortcut's soundness.
2. **The annotate normalizer must carry the whole meta** —
   `AnnotBinderEntry`/`AnnotBinderEntryX` now thread `IBinderMeta`/
   `BinderMeta` (was `BinderInfo`) through
   `annotatePisI`/`annotateLamsI` and their pure mirrors: a
   loop that rebuilt `⟨bi⟩` would ERASE input annotations before
   validation could see them — a P2-blocking bug caught by types at
   P1.  `DenAStk` relates the entries' metas by `denoteBM`, the
   `DenILE` precedent.
3. **The parked SortCoh lane's `CertZip.lam/forallE` were too
   narrow** — they shared one meta across both sides; instantiation
   at different level lists now produces different (`substPW`-ed)
   metas.  Generalized to two metas (`SortCoh/Discharge.lean`,
   `ZipLamHeadCase`, consumers); no claim strengthened or weakened —
   the zip never related metas.
4. The interned pushforward is `substPWI` over the memoized
   `zeronessOfLIGo` (level DAGs; `PWMemo` per call), with the
   correspondence battery `PWMemoInv`/`zeronessOfLIGo_spec`/
   `substPWI_spec`/`substLIBM_spec` (`Verify/IExpr.lean`) feeding the
   `instantiateLevelParamsIGo` walk spec.  TODO(#161-P5): one shared
   `PWMemo` per instantiation call if profiling demands.

**The P1 battery** (all green): `lake build` warning-free (352 jobs),
`lake test`, arena **90/92**, e2e **72/72**, split driver **11/11**,
mode flags **9/9**, no-model sweep as expected (1 recorded
divergence, unchanged), zero sorries, axioms exactly
`[propext, Classical.choice, Quot.sound]` on
`no_proof_of_Empty_R`/`no_proof_of_Empty_input_R`/
`checkDecls_sound_R` and on the new battery
(`equiv_iff_holds`, `zeronessOf_sound`, `zeronessOf_subst`,
`substPW_self`, `substPW_comp`).  **init-prelude (`--pre`, 3653
declarations) is BYTE-IDENTICAL — stdout, stderr, exit — against the
master binary in BOTH modes** (`--set-model`, `--no-model`): the
placeholder representation is verdict-inert, as designed.  Branch base
= master (`99987a5f`), no divergence to merge.

**Suite policy (ratified with amendment 1, recorded here):** from P2
until P5, `--set-model`'s arena/init sweeps are suspended in favor of
the annotated fixture suite (annotated syntax is the checker's input
language per the goal statement); `--no-model` keeps the full parity
suite green throughout.  Real streams re-enter `--set-model` when the
pass lands (P5).

### Task #161 ledger note: the implementation phase targets a cached checker variant (user heads-up, 2026-09-01)

Binding for the LATER implementation/performance phase (P5+), not for
P2–P4: the two-tier arena design (task #64) is expected **not** to
survive the preprocessor era.  The implementation phase should build a
**cached checker variant** — derived fields + hashmaps,
official-kernel/lean4lean-style — instead of extending the arena
machinery.  Consequence recorded for the parked P5 items: the
`PWMemo`-sharing TODO (`IExpr.lean`, `substPWI`) should assume the
cached-variant world, not the two-tier arena.  No action in P2–P4.

### Task #161 ledger note: PropWhen is consumed interface-only from P3 on (user directive, 2026-09-01)

A canonical subtype-encapsulated set type (`ZeroSet`/`ZPropWhen`,
sorted-nodup by construction — the Std.HashMap pattern) is prepared on
the side (branch `agent/annot-set`) as the P5-candidate representation
and the documentation of the needed operations and laws.  BINDING for
the big proof (P3/P4): statements consume `PropWhen` only through the
operation/law interface — `holds`, `equiv` + `equiv_iff_holds`,
`substPW` + `substPW_self`/`substPW_comp`, `zeronessOf` +
`zeronessOf_sound`/`zeronessOf_subst`, `paramsDefined` — never through
`List` internals, param-list pattern matching, or order-dependent
reasoning, so the later swap is an interface re-instantiation, not a
proof rewrite, and the big proof never carries the representation
invariant.  A proof step wanting a fact outside the battery = a
missing LAW: state it, add it to the battery (both representations),
report the addition.  P2 is unchanged (`equiv` at validation sites).

## Task #161 P2 SEAL: the validated checker lands (2026-09-01)

**Landed** (branch `agent/annot-v2`): the six validation sites, the
annotated input surface, the fixture suite, and the full proof-stack
adaptation.  The verified mode (`--set-model`) now checks every
binder's `pw` claim; `--no-model` remains official parity (no reads).

**The decline surface** (all `CheckError.notImplemented`, exit 2, all
gated `mode.verified`, annotations never steer reduction):

| site             | where                                        |
|------------------|----------------------------------------------|
| `(forall-cod)`   | `inferBody` ∀: `zeronessOf v ≃ mb.pw` after `ensureSort` of the codomain |
| `(lam-cod-leaf)` | `inferBody` λ, body not a λ: against the #152 body-type sort |
| `(lam-cod-chain)`| `inferBody` λ, body a λ: `mb.pw ≃` the inner λ's `pw` (`Expr.lamPw`) |
| `(defeq-forall)` | `defeqStep` ∀-congruence, after both defeqs succeed |
| `(defeq-lam)`    | `defeqStep` λ-congruence, ditto              |
| `(eta)`          | `etaCert`, after the η defeq succeeds        |

The defeq/eta checks run LAST so a benign certificate fallthrough
(`pure false`) is untouched: a mismatch fires only where the
comparison was otherwise about to succeed.

**Input surface**: optional `"pw"` field on `lam`/`forallE` export
records (`Frontend/Export.lean`) — absent or `"never"` = the codomain
is never a proposition; an array of name-table indices = `ifAllZero`
over those level parameters (`[]` = always).  Unannotated streams
parse unchanged and *decline* at their first Prop-codomain binder
(init-prelude: `(forall-cod)` at `LT.rec._model`).
`allLevelParamsDefined` covers `pw.paramsDefined`, so an out-of-scope
parameter in a `pw` is the same reject as one in a level.

**FINDING (P3/P4's statement, discovered as a test-writing wall): the
three defensive sites are unreachable through the spec knot.**  Every
path to the structural congruence arms and to `etaCert`'s comparison
first infers both compared expressions (`proofIrrel` runs before them
and infers `a`, `b` AND their types — no short-circuit in the monad),
and the front door validates every binder an infer walks.  Two valid
annotations of level-equivalent codomain sorts are semantically equal
zero-sets, and `equiv` is complete — so they always pass.  Attempted
countermodels (invalid ∀ meta on an fvar's stored type) decline at
`(forall-cod)` inside `proofIrrel` instead.  Consequences:
* the annotated fixture suite covers the three front-door sites
  end-to-end (`tests/annot/annot_decline_*.ndjson`); the defensive
  sites are unit-tested in `tests/SetlecTests.lean` against a stub
  `CoreFns` whose `infer` does not walk, plus a direct `etaCert` call
  (an fvar's stored type is returned, not walked — the one real-knot
  crack, and `proofIrrel` seals it at any composite call site);
* P3/P4 should get the invariant "validated exprs stay validated"
  essentially for free at these sites — the checks are pure defense,
  kept because the checker never trusts (invariants-over-runtime-gates
  is about *hypotheses*, not about dropping validation).

**The annotated fixture suite** (`tests/annot/`,
`tests/annot-expected.txt`; hand-written streams): five accepts (Sort
u identity; the imax telescope; `max u v` with the type spelling
`[u,v]` and the value `[v,u]` — equivalent-but-unequal lists pass the
chain rule and the final defeq; the impredicative always-`[]`; a
Type-only stream with no annotations at all) + the three declines +
the split-driver pair (`annot_split_good`/`annot_split_bad`, bad at
declaration index 2).

**Suite state (ratified policy in force)**: `tests/arena.sh`'s
certified sweep runs the annot suite (10/10); the arena + e2e suites
run under `--no-model` against the unchanged certified expectations —
138 arena + 72 e2e + 10 annot as expected, 4 recorded divergences (1
pre-existing error-class line + the 3 annot declines, recorded in
`tests/no-model-expected.txt` as the parity lane's nature).  Split
driver 11/11 and mode flags 9/9 on the annotated smoke pair, same
properties, `badDecl` selectivity message included.

**The P2 battery** (all green): `lake build` warning-free, `lake
test`, the harness as above, zero sorries, axioms exactly
`[propext, Classical.choice, Quot.sound]` on `no_proof_of_Empty_R` /
`no_proof_of_Empty_input_R` / `checkDecls_sound_R` (the consistency
theorems now cover the *validating* checker) and on the PropWhen
battery.  init-prelude (`--pre`, `--no-model`) BYTE-IDENTICAL to the
master binary — stdout, stderr, exit; at `--set-model` it positively
declines, as the policy prescribes until P5.

**Merged at the seal**, per the coordinator action item:
`agent/annot-set` @ `339e0d74` (the canonical `ZeroSet`/`ZPropWhen`
side module — 4 new files + the import/test lines, additive, battery
green post-merge).  The P3/P4 interface-only discipline (previous
ledger note) is unchanged by the merge: `PropWhen` stays the one
concrete type.

**Not in P2 (deliberate)**: no annotate pass (P5); no basis/pin
annotation — the fixture fragment is constant-free, and the pinned
basis literals stay `.never` (`PinGen.lean` fills `⟨bi, .never⟩`);
the pins' own Prop binders will need the generator route at P5.

## Task #161 P3.1 SEAL: the bit laws, `denoteP`, and the unconditional level crossing (2026-09-01)

P3/P4 go-order received (decline-surface review passed).  This is the
first goal-phase seal: the piece-1/piece-3 groundwork and the pivot's
first full payoff, all **proved** (no conditional forms).

**The route, fixed by survey before writing anything.**  The
collapse-free lane (`Interp2/*`, task #151) reads binder regimes off
`AVExpr` numerals that `denote2` computes by *running the checker*
(`sortOfE`/`lamSortE`) — the canonical-annotations resolution of WALL
3 — and its frontier is exactly the runs' stability: residue 9
(`BinderSortAgree2`, `Step2/DefEqRun.lean`: two independent sort runs
on defeq'd bodies agree), `Denote2InstLevels` riding the *open*
checker metatheorems `SortOfEInstLevels`/`LamSortEInstLevels`
(`Step2/Levels.lean`, false-as-stated over a bare `Env`,
`Step2/LevelsInst.lean`), and the Θ-frozen `EnvExtendStable`/
`Denote2Total` family (`Keys2Bundle.lean`).  The P2 checker validates
the *input's own* data at exactly the shapes these residues need:
`interp2` reads numerals only through the `v = 0` test
(`piR_zero_agree`/`lamR_zero_agree`), and the datum's bit at a ground
valuation is that test.

**Landed, all proved:**

* **The bit-law battery** (both representations, as the ruling
  requires): `PropWhen.holds_eq_of_equiv` (a passed comparison =
  equal bits at every valuation), `PropWhen.holds_of_equiv_zeronessOf`
  (a passed validation site = the computed sort's true zero bit — the
  establishment law, reading the P2 run-inversion conjunct), and
  `Level.holds_substPW` (the pushforward's semantic reading:
  instantiate-then-read = read-at-`Level.substFn` — the crossing law).
  Mirrors: `ZPropWhen.holds_eq_of_equiv`,
  `Level.holds_of_equiv_zeronessOfZ` (`holds_substPWZ` predated,
  canonicity's primitive).
* **`denoteP`** (`Annot/Bit.lean`): `denote2`'s recursion with every
  binder numeral `pwBit φ m.pw` — no checker runs, **no fuel, no
  mode**.  `pwBit` lands in `{0,1}`, so checker-`equiv` data give
  *equal* numerals (`pwBit_eq_of_equiv`) — the `zero_agree` step
  becomes `rfl`-shaped where residue 9 lived.  The `pi` `u`-slot is
  filled with `0`: `interp2`/`AnnotOk2` never read it, amendment 1
  dropped the domain datum deliberately; a consumer that turns out to
  read `u` is a named finding against the amendment, not a plumbing
  gap.  `denoteP_erase` links to `denote` exactly as `denote2_erase`.
* **`denotePInstLevels`** (`Step2/BitLevels.lean`) — the level
  crossing, **unconditional and exact**:
  `denoteP acval env φ d (e.instantiateLevelParams ks us) =
  denoteP acval env (substFn φ ks us) d e`.  An *equality* (no fuel
  slack, no `EnvWF`, no checker residue) where `Denote2InstLevels` is
  a one-directional implication conditional on two open metatheorems.
  Binder step = `pwBit_substPW`; constant step = `acval_params` +
  `substFn_map_subst` as in the canonical walk.
* **The λ→∀ meta copy, named** (piece 3): `infer_lam_meta_copy`
  (`Verify/InferLemmas.lean`) — the inferred type of a λ is a ∀
  carrying the λ's own meta (definitional in the λ clause), so the
  inferred type needs no ∀-front-door pass: the λ's chain/leaf check
  *is* the copied datum's validation, and both `denoteP` readings
  dispatch on the same `pwBit φ m.pw`.
* **The defensive-sites invariant, named** (the coordinator's
  mandate): `DefensiveSitesQuiet` (`Verify/AnnotDefense.lean`) —
  on inference-successful inputs, `isDefEqCore` never declines at
  `(defeq-forall)`/`(defeq-lam)`/`(eta)`.  Statement only; to be
  decided by proof or refutation, never assumed; the kernel checks
  stay either way.

**P3.2 (next, its own statement seal): `AnnotValidV` on the bit.**
Design constraints fixed here: it must be establishable from the run
inversions (the refuted `ValidInfer` metatheorem shape —
`Annot/Validity.lean`, I8/`DefEq`-crossing — is OFF the table),
preserved via `interp2_inst` + the bit laws, and shaped by its
*consumers*: the `AnnotOk2` binder components (`v = 0 → fibres are
truth values`) and the Step2 ladder's per-lemma premises, which the
P3.2 survey walks before the definition is frozen.  The three owed
`EnvWF` records (nfields = cnF; nat-op stored-value; defnInfo
type-value) fold where those invariants state them — none was
naturally stated by P3.1's pieces, so they remain owed.

**Battery**: full build warning-free, `lake test`, harness (annot
10/10, no-model sweep 138+72+10, split 11/11, mode 9/9), zero
sorries; axioms on the new theorems exactly the standard three or
fewer.

## Task #161 P3.2/P3.3 statement seal: AnnotValidV frozen, the P-generation claims frozen (2026-09-01)

**Dispatch protocol in force** (user reminder): statements, the
establishment architecture, first worked example per proof species,
and review stay on the lane lead; stated-and-recipe'd theorem lists go
to ONE serial Opus worker per batch, own worktree off the lane branch,
full battery per report, reviewed before merge.

**Frozen this seal, with worked examples proved:**

* `AnnotValidV` (`Annot/ValidV.lean`) — bit validity, on the bit.
  The `pi` clause carries the one new fact (`v = 0 →` codomain fibres
  are truth values — the regime fact `AnnotOk2` has no home for at a
  bare product); the λ clause carries *nothing* (the λ-side regime
  facts are `AnnotOk2`'s fibre package, and the chain rule's semantic
  content is `piR_zero_mem_univZero` — impredicativity, no run);
  every other clause is the hereditary `AnnotOk2` environment
  discipline, so the substitution metatheory rides identical
  rewrites.  Worked examples: `pwBit_zero_mem_univZero` (the
  establishment species — run conjunct + semantic sort membership ⇒
  `univZero`) and `AnnotValidV_liftN` (the transport species).
  Establishment is at checker visit sites from run inversions ONLY;
  the refuted `ValidInfer` metatheorem shape is off the table by
  construction.
* `Claims2P` (`Interp2/Claims2P.lean`) — the ladder's statements over
  `denoteP`: `AnnotOkP := AnnotOk2 ∧ AnnotValidV` as the currency,
  `CtxOkP` (fuel-free context discipline; the historical
  `CtxOk2`/`CtxOk2Ann` split merged), four dual-success claims with
  the annotation fuels gone, `CheckStep2P`, and `checkSound2P`
  (proved — the generic induction).  The module docstring carries the
  residue-transformation ledger: `BinderSortAgree2` → the P2 defeq-arm
  inversions (bits canonical in `{0,1}`); `LamCodSort2` → the λ front
  door + impredicativity; `SortOfE/LamSortEInstLevels` →
  `denotePInstLevels` (proved); `SortAgree` → dropped
  (`denoteP_envExtend`, batch 1).

**Batch 1 (Opus, running)**: the `denoteP` lemma surface — clause
equations, inversions, depth shift (minus `EnvWF`), closedness,
install-tier congruences, environment crossing (minus `SortAgree`) —
21 mirrors, graded VERIFIED/HINT, two worked examples pre-landed.

**Sequencing from here**: P3.4 `CtxOkP` kit + frame mirrors (next
batch after review) → P3.5 the lane lead's worked ∀ clause of
`CheckStep2P`'s infer quarter (the establishment architecture in
context) → clause batches per quarter → the step assembly →
install/env tier (`EnvS2` fields for stored-type validity — where the
three owed `EnvWF` records fold if natural) → the P capstone
(`no_proof_of_Empty` over the collapse-free model).

### Task #161 P3.5 interim: the infer quarter at 6/11, the campaign map (2026-09-01)

**Landed by the lane lead** (species examples, all proved, standard
axioms): `infer_{sort,bvar,fvar,const,forallE,lam}_claimP`
(`Step2/InferP.lean`).  The two binder clauses are the architecture
validations: the ∀ clause's four moves (run inversion → `SortSemP` →
one-line establishment → the `piR_zero_agree` numeral bridge), and the
λ clause's chain case, where `LamCodSort2` dissolves into
**impredicativity** (`piR_zero_mem_univZero`) via the meta copy — no
run, the model's own law.  New routed residues, both by design:
`SortSemP` (the `SortSem2` transpose, becomes available at the top
induction) and `AcvalValidP` (leaf bit-validity — the `AnnotValidV`
companion of `acval_ok2`, discharged at the install tier).

**Batch 1 (merged @ `492a9e36`)**: the full `denoteP` lemma surface,
21/21 — including `denoteP_envExtend` from
`FindPreserved`+`LitGuardsAgree` alone (the `SortAgree` Θ-residue
**gone by construction**) and the depth shift without `EnvWF`.
Deviation recorded in-file: `denoteP_agree_same` collapses to
`Option.some.inj` (no fuel to reconcile) — kept for its consumers.
Worker findings recorded in memory: fresh worktrees need
`SETLEC_INDUCTIVE_MODELS` for the harness, and worktree bases must be
verified.

**Batch 2 (running)**: CtxOkP open family, `AnnotValidV_inst` pair +
`AnnotOkP` transports, `denoteP_substFvarAt`/`denoteP_beta` (the
substitution crossing — `BetaCross2C`'s successor as a *syntactic*
equation, the interp2/AnnotOk2 slack deleted).

**The remaining map** (canonical-lane mirror mass ≈ 11k lines):

* **Batch 3** — infer quarter completion: `natLit`/`strLit`/`proj`
  (routed-residue transposes + spine gradings via `AcvalValidP`),
  `letE` (ζ via `denoteP_beta`), `app` (the β/kind split), and the
  two `TODO(#161-P3.5)` `hCop` premises replaced by `CtxOkP.openS`.
* **Batch 4** — the whnf/whnfCore quarters (`Whnf.lean` 3.2k):
  `Delta2P` stays routed (fuel-free form; the install tier discharges
  it through the P env structure's `acval_defnP` + the *proved*
  `denotePInstLevels` — the canonical lane's `delta2_refuted` wall
  falls with the fuel); ζ/β rows on `denoteP_beta`; iota/nat/str rows
  currency-mechanical.
* **Batch 5** — the defeq quarter (`DefEqRun.lean` 4.7k): residue 9's
  uses replaced by the arm's own check extraction (positive form of
  the P2 extraction idiom) + `pwBit_eq_of_equiv`; the v1 relational
  scaffolding (`defeqR_at`, `CtxOkR`) is kept verbatim — it works
  through erasure, and `denoteP_erase` lands on the same `denote`.
* **Then**: the step assembly (`checkStep2P_of_quarters`, at
  `μ.verified = true`), the install/env tier (the P env structure:
  `acval_defnP` fuel-free, `AcvalValidP` established from the front
  door; the three owed `EnvWF` records fold here if natural), and the
  P capstone: `no_proof_of_Empty` over the collapse-free model.

### Task #161 P4 design: the P environment invariant (drafted while the quarter batches run, 2026-09-01)

`EnvS2PM (μ) (env)` — the install tier's target, landing as **new
structure + bridge** (the seal-18 pattern `EnvS2U → EnvS2UM` set):

* kept verbatim: `base : EnvS V env` (v1 containment), `acval`,
  `acval_erase`, `acval_closed`, `acval_params`;
* `acval_ainst` — the inst-invariance twin of `acval_closed` (batch
  2's finding: the two leaf invariances are independent equations on
  the `AVExpr` side; both discharge at install from one
  `VExpr.bvarsBelow` fact of the built leaf's erasure);
* `acval_okP : ∀ n ψ ρ, AnnotOkP V ρ (acval n ψ)` — upgrades
  `acval_ok2` and **discharges the routed `AcvalValidP`**;
* `acval_defnP`/`acval_thmP` in **existence form**, fuel-free:
  `denoteP acval env φ 0 value = some (acval cv.name φ)`.  The
  canonical fields are uniqueness-form because all-fuel existence was
  *refuted* (`envS2_defn_lam_refuted` — `denote2` fails on binders at
  small fuel); `denoteP` has no fuel and fails only out-of-fragment,
  which a checked value never is.  With existence, `DeltaP`
  discharges from the field + `denotePInstLevels` — the delta
  crossing's last conditional piece;
* `mem_typeP` — the `interp2` membership at `denoteP` readings.

**Establishment (the P `DeclStep`)**: the front-door runs of a
declaration's type and value, fed to `InferClaims2P`'s conclusions
(from `checkSound2P` at the step assembly), yield exactly
`acval_okP`/`mem_typeP` for the new leaf; `AnnotValidV` of the leaf is
the claims' own conclusion — establishment stays at run inversions,
never a metatheorem.  The three owed `EnvWF` records (nfields = cnF;
nat-op stored-value; defnInfo type-value) fold into `EnvWF` when the
install-tier proofs demand them — that is their natural home, not the
quarters'.

**Capstone shape**: `checkDecls_sound_P : … → Nonempty (EnvS2PM μ env')`
by the declaration fold; `no_proof_of_Empty_P` reads `mem_typeP` at
the `Empty` pin (`Interp2/EmptyPin2.lean`) — the collapse-free model
consuming the validated annotations, which is the task's goal
statement.

## Task #161 P3.6 SEAL: the quarter campaign lands — `checkSoundP_of_inputs` (2026-09-01)

**The four P-tier soundness claims hold at every fuel** —
`checkSoundP_of_inputs` (`Step2/AssemblyP.lean`), proved, standard
axioms — over the validated-annotation reading, at a validating mode,
conditional on three routed input bundles (`WhnfInputsP`,
`DefEqInputsP`, `InferInputsP`).

**The campaign in numbers**: three concurrent serial Opus batches
(infer completion 11/11 clauses; the whnf/whnfCore quarters, 886
lines; the defeq quarter, 1233 lines), zero skips, zero walls, zero
kept-against-plan premises; every deviation was a *discharge* the
canonical lane could not afford (`deltaP_of` outright,
`Denote2Inst1B` retired, `acval_inst_self` in-file — deduplicated to
`OkPTransport` at the merge — the app clause needing neither
`SortSemP` nor the mode).

**Where the canonical frontier stood vs. where the P frontier
stands**: `Capstone2E`'s fifteen residues included the whole Θ-frozen
sort-stability family; the P bundles contain NONE of it.  What
remains: (a) install-tier obligations (`ConstTypeP`, `AcvalValidP`,
`AcvalDefnInstP`, `NatHeads2`, `SortSemP`, str/proj/iota/nat clause
residues) — the `EnvS2PM` seal's bill, per the P4 design note; (b)
the totality factors (`denoteP` successes the dual-success shape
cannot produce) — heavily overlapping, target of one consolidation
seal; `denoteP` fails only out of fragment and checker outputs stay
in fragment, and the fuel mechanism behind the canonical lane's
existence refutations is gone.

**Findings recorded by the batches**, all accepted at review: the
defeq extraction's `hμ` is load-bearing (at an unverified mode the
arm check passes vacuously — the theorem is *correctly* impossible
there); `AnnotValidV_inst`'s premise is validity of the substituted
term (the predicates are genuinely independent); the `AVExpr` leaf
invariances split into a lift/inst pair; dual success charges the
threading clauses totality residues (`InferReadsP`/`WhnfReadsP`).

**Next**: the `EnvS2PM` install tier (discharges bundle (a),
establishes `AcvalValidP` from the front door, folds the owed `EnvWF`
records where demanded), the totality consolidation seal (bundle
(b)), then the capstone `no_proof_of_Empty_P`.

### Task #161 P4 FINDING: the carrier must slim — `EnvS2Core` (2026-09-01)

The P fold can never supply an `EnvS2UM`: it must store each new leaf
as the value's **`denoteP` reading** (bit numerals — otherwise
`DeltaP` is false), while `acval_defn`/`acval_thm` insist a
successful **`denote2`** reading is the leaf, and the two differ at
every binder whose sort evaluates above 1.  One valuation cannot
serve both currencies.  Measured before fixing: the P surface reads
NONE of the denote2 fields — so the carrier slims
(`Annot/EnvS2Core.lean`: `EnvS2U` minus the three denote2 fields and
the mode index; `toCore` projections landed).  Batch 8 = the
mechanical signature sweep of the P surface (`EnvS2UM V μ env` →
`EnvS2Core V env`) + re-homing the three `acval` helper lemmas the
level crossing reads + `EnvS2PM.base2 : EnvS2Core`; runs after
batches 6/7 merge so the sweep is single-shot.

## Task #161 P4 frontier-transformation record (running tally, 2026-09-01)

The design's publishable evidence: what the canonical (sort-run)
interp2 lane routes undischarged at its frontier (`Capstone2E`'s
fifteen, plus the quarter-level residues feeding them) versus the
validated-annotation (P) lane after batches 1-7 + the lead's seals.

**Dissolved or proved outright in P (canonical status in parens):**

| canonical residue | P status |
|---|---|
| `BinderSortAgree2` — residue 9 (routed, Θ-shaped) | DEAD: the P2 defeq arms' own run certificates + `pwBit_eq_of_equiv` |
| `LamCodSort2` (routed) | DEAD: leaf = front-door conjunct; chain = impredicativity (`piR_zero_mem_univZero`) |
| `SortSem2` (routed, off-induction) | DERIVED: `sortSemAtP_of_claims` — the annotation fuel's removal makes every use induction-bounded |
| `SortOfE/LamSortEInstLevels` (open metatheorems, false over bare `Env`) | PROVED: `denotePInstLevels`, unconditional equality |
| `SortAgree` (env crossing, Θ) | PROVED-FREE: `denoteP_envExtend` from `FindPreserved`+`LitGuardsAgree` |
| `EnvExtendStable` (frozen on Θ) | not needed: the crossing above is the whole obligation |
| `BetaCross2C` (routed) | THEOREM: `denoteP_beta` — syntactic equation, transports by `AnnotOkP_inst0` |
| `Denote2Inst1B` (routed) | RETIRED: `denoteP_beta` directly; both leaf premises discharged (`acval_inst_self`) |
| `Delta2B` (routed; slack; `delta2_refuted` wall) | DISCHARGED: `deltaP_of` from the existence-form field + the proved crossing |
| `Denote2ModeAgree` (routed) | GONE: one reading per subject (`denoteP_agree_same` = `Option.some.inj`) |
| `TypeOk2` (routed) | GONE: the P claims conclude `AnnotOkP` of the returned type |
| `CtxOk2R` (routed, believed false) | GONE: one currency (`CtxOkP`) |
| `EtaCert2D` (routed) | PROVED: `etaCertStepP_of_claims` — `lamR_eta` is regime-uniform; the P2 `(eta)` certificate identifies the annotations |
| `AppCongrStuck2D`, `DefEqSpine2D` (routed) | PROVED: `appCongrStuckP_of_claims`, `defEqSpineP_of_claims` |
| `ProofIrrel2D` (routed) | PROVED (Prop branch): `proofIrrelPQ_of_claims` — no heterogeneity side condition at `interp2`; unit-like branch → caps tier |
| `Denote2StrLit2A` (routed) | PROVED: purely syntactic (`denotePStrLit_of_guard`) |
| `InferExists2E` + the dual-success totality family | DISCHARGED from `EnvS2PM` fields + the `ReadsP` walk (post batch-8 repair of the refutable-as-stated `InferReadsP` — batch-6 finding) |
| `ConstType2C` (routed) | DERIVED: `EnvS2PM.constTypeP` |

**Still routed in P, by discharge tier:**
install (`InferStrLitStepP`, `InferProjStepP`, proj-reads pair);
iota (`IotaStepP`, `IotaReadsP`);
literal (`ReduceNatStepP`/`PQ`, `ReduceNatReadsP`);
caps/structure (`UnitIrrelPQ`, `PairEtaIrrelP`, `StructEtaIrrelP`,
`StructUnitIrrelP`).
These are the P capstone's remaining bill — every one names semantic
content the canonical lane also never built (it froze earlier, on the
sort-stability family), so the table above is the design's measured
claim: **validated annotations dissolve the coherence frontier;
what remains is the ordinary semantic content of the checker's
features.**

### Task #161 P4 batch 8: the carrier sweep, done + `InferReadsP` repaired (2026-09-01)

**The sweep landed.**  The whole P surface is now stated over
`EnvS2Core V env` — `Claims2P` (`CtxOkP`, the four claim families,
`CheckStep2P`/`checkSound2P`), `CtxOkPKit`, `OkPTransport`,
`BitLevels`, `InferP`, `WhnfP`, `DefEqP`, `AssemblyP`, `IrrelP`,
`StuckP`, `ReadsP`, and `EnvS2PM.base2`.  (`BitInstall`/`BitExtend`
bound no `EnvS2UM` and were untouched.)  Every P theorem is thereby
strictly *stronger*; no content changed.  `EnvS2UM.toCore` and
`EnvS2U.toCore` stay for canonical-lane interop.

Canonical helpers the P surface consumed at the fat carrier were
transposed body-for-body, each beside its consumer, canonical files
untouched: `AcvalParams2`/`acvalParams2` → `AcvalParamsP`/
`acvalParamsP` (`Annot/EnvS2Core.lean`); `acval_isEmpty`/
`acval_oneParam`/`acval_scalar`/`acval_one`/`acval_natPair` → the
`…P` names in `Step2/BitLevels.lean` (the first two came along because
`acval_scalar`/`acval_one` call them); `NatHeads2` → `NatHeadsP`
(`Step2/InferP.lean`).

**Two spots the sweep was not purely mechanical**, both because the
carrier no longer pins the mode: (i) `DeltaP`'s `μ` became a genuinely
unused binder (only `m`'s type ever mentioned it) and is dropped —
`DenotePDeltaP`, its statement-identical twin, never had one; (ii)
fourteen P-tier `Prop`s whose *bodies* run the checker at `μ` now take
`μ` explicitly (`DefEqStepAtP`, `ProofIrrelPQ`, `ReduceNatStepPQ`,
`DefEqSpineP`, `DefEqStuckP`, `StuckIrrelPQ`, `AppCongrStuckP`,
`EtaCertStepP`, `WhnfCoreReductExistsP`, `PairEtaIrrelP`,
`StructEtaIrrelP`, `StructUnitIrrelP`, `UnitIrrelPQ`,
`ReadsInputsP`), as `Claims2P`'s four families already did —
otherwise `μ` is an unsolvable implicit at every use site.

**The batch-6 `InferReadsP` FINDING is repaired.**  As stated the
residue was *refutable*: `inferBody`'s `.fvar` clause returns the
leaf's stored annotation and `denoteP`'s `fvar` clause never reads it,
so `.fvar 0 n (.const c [])` at `d = 1` with `c ∉ env` satisfies every
premise while the returned type does not read.  The sanctioned repair
landed: `InferReadsP` now carries `LeafReadsP m φ d e` (the leaf
weakening of `CtxOkP`, moved with its kit from `Step2/ReadsP.lean` to
`Step2/InferP.lean`).  Consequences: `InferReadsCP` — batch 6's
leaf-premised stand-in — is *deleted*, the walk proves `InferReadsP`
itself, `inferReadsP_of` closes the residue from `ReadsInputsP`
**alone**, and the flagged (refutable) `LeafReadsAllP` is deleted.
Every consumer paid nothing: `sortSemAtP_of_claims`,
`infer_letE_claimP`, `infer_app_claimP`, `prop_side_pt`/
`proofIrrelPQ_of_claims`, `etaCertStepP_of_claims` each already held a
`CtxOkP` at the same depth, and discharge the new premise by
`LeafReadsP.of_ctxOkP`.  All six totality residues of the batch-6
consolidation are now discharged outright.
