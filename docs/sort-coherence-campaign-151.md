# The sort-coherence campaign (task #151): what was tried and where we failed

Status: both lanes PARKED by user directive (2026-09-01), superseded by
the validated-annotation design (checker-validated sort annotations;
see §7).  This document is the campaign's citable summary.  The full
design memory is the `docs/SetR-DESIGN.md` ledger (branch
`agent/cert-tax`, final SHA f46e96850f5cbbed8a4bf0e5a720e3ba0227972c) and the batch book
`ConLeche/SetR/Annot/SortCoh/ThetaRunBatch.md` (branch
`agent/theta-runbatch`, final SHA cb2c2ed3); the NbE lane's
record is on `agent/nbe-lr` (final SHA eb3591d2).  Literature survey:
`docs/lit-standardization-setmodels-2026-09.md`; diagnosis and
strategy: the retrospective memo (docs/retrospective-2026-09-01.md).

## 1. The goal, and why it needs sort coherence

Task #151: make the set-theoretic interpretation collapse-free — the
model must read a binder's sort off the term without the empty-domain
λ/pt collapse (the campaign's oldest countermodel: an empty-domain λ
collapsing to `pt` inside a `{pt}`-domain Π, which falsified the gated
whnf/infer claims at #100 and reappeared, unprompted, as the NbE
lane's induction-starver).  The missing metatheorem family is SORT
COHERENCE: when the checker's runs compare or transform terms
(substitution telescopes, defeq loops, certificate fires), the sorts
the model needs must agree across the runs.  Concretely the frozen
junction obligations `ZipWhnfSortAgree`/`ZipSortOfAgree`
(`SortCoh/Discharge.lean`) and, behind them, the Θ walk's lock with
its census of three sorries (`layerRunCell_of`, `runStepF_step`,
`thetaLoopLock_of` in `ThetaLock.lean`).

Root diagnosis (retrospective memo, corroborated in print): this is
subject-reduction-strength metatheory for an UNTYPED algorithm of a
theory whose untyped metatheory is broken — Carneiro's thesis §3.1.1
(Lean's defeq is a non-transitive underapproximation; SR and CR fail);
lean4lean's own repo holds the corresponding injectivity statements as
sorries under "theorems which we can't prove :(" (Conjectures 2.7/2.9).
Every refutation in our record instantiates one mechanism: a θ-entry's
argument does work at the image that the core lacks — Lévy
redex-creation case III, where backward simulation is false in pure
λ-calculus already.

## 2. The Θ lane: the six walls

Each wall is mechanized (a countermodel in `_tmp/*.lean` probe files,
sealed in the batch book).  Walls 1–4 are DIRECTION failures
(image→core transport); wall 5 is a PRESERVATION failure; wall 6 is
the ι-RESCUE ASYMMETRY.

* **W1 — annotation-transport** (`rawReach_leaves_sub` refuted):
  `substAK` erases substituted-fvar annotation chains, and the K/eta
  rescue FABRICATES its reduction spine from the erased annotation —
  image traces are not core traces dressed up.  Honest replacements:
  `substAK_fvarLeaves_sub`/`_hit` (union tether, insertion-implies-
  occurrence).
* **W2 — the δ-sim mirror** (`ThetaDefeqSimF` refuted; witnesses
  `delta151`/`cert151`): a defeq-tier substitution simulation is
  false — one witness (an fvar-headed application whose image
  converges) killed six statements in one sweep.  Consequence:
  the whnf-only sim tiers are the strongest true form
  (`SubstSim.lean:302`; no defeq mirror exists tree-wide).
* **W3 — the β-fire convergence witness** (`inverse151`): the image
  β-fires to a sort while the core is stuck at the fvar-headed
  application — verbatim Lévy creation type III.  This killed the
  disposal's routes (a) and (b) and forced the waiver family.
* **W4 — non-head descent** (the compound pair
  `compound_head_is_const`/`compound_is_in`): a top-level in-zone-headed
  atom is blind to a rec application whose MAJOR is the witness —
  the induction-strength gap, caught by a consumption probe before the
  induction ran.  Fix: the hereditary atom `InZoneHeadedIn`
  (all app components + proj scrutinees + the fvar zone leaf).
* **W5 — preservation failure** (countermodel
  `((fun _ : Sort 0 => fvar d) (Sort 0)) (Sort 0)`): `InZoneHeadedIn`
  is NOT backward-preserved along mirror steps — β CREATES the
  property.  Different in kind from W1–W4; no re-routing touches it.
  Fix: conclude about the run's ENDPOINT, not the original core
  (forward inductions deliver endpoint facts).
* **W6 — ι-rescue asymmetry** (source-pinned at
  `Core.lean` `iotaRec`:1267 → `majorToCtor`:1074): on a non-ctor
  major the core enters a rescue that runs `infer` + `whnf` THE IMAGE
  NEVER PERFORMS — the work bound is REVERSED, and `infer` on an
  fvar-headed application is the δ-sim witness's own throwing call, so
  the core's machine run may ERROR where the image lands.  Fix: the
  waiver's negative arm (see §3).

## 3. The Θ lane: refuted routes and ratified survivors

Refuted/superseded routes (each with its killing evidence):

* **Disposal route (a)** (refutation at the sort landing via
  `subst₁/₂_eq_sort_inv`): ratified, then found COMPRESSED at its
  first move (the pin step asserted, not specified — the C0 anchor's
  blind spot: anchors verify existence, not mechanism); repaired
  ((c)-at-the-reduct), then overtaken by W5/W6.
* **Disposal route (b)** (carry the telescope to the landing): priced
  fallback only; never viable alone.
* **Route (c)/(D) stuck-state arms**: evolved through (D) (endpoint
  equation), killed in part by the FUEL-VACUITY kill (`fppvac151`:
  `whnfLoop` at budget 0 errors for EVERY term by rfl — a bare error
  disjunct is trivially inhabited), into the surviving R1 form.
* **Det-sync** (commit cea710e, the scar): 1-1 stepwise sync of two
  machine runs across the opened/substituted boundary has no
  determinism to use — "the per-step relation IS the substitution
  simulation."  Its lesson produced the lockstep design (below).
* **Two-trace joins (Θ-2)**: killed by the (p1) falsifier —
  `iotaEta`'s fabricated projection fields carry a free `ust`
  existential: two distinct RawReach-frozen endpoints from one source
  under `EnvWF` — gate-free RawReach is NOT confluent.  (`iotaK` IS
  result-deterministic — `cnF = 0` makes the reduct targs-independent
  — but its premise is unrecorded: install checks `r.nfields = cnF`
  (`CheckerS.lean:606`) and `EnvWF` never carries it; finding
  recorded, fix shape noted.)
* **Completeness-of-defeq conclusions** (the Θ-4 guardrail): any
  lemma concluding `∃ L', defeqLoop … = .ok true` on transformed
  inputs bets against non-transitivity (Carneiro §3.1.1).  Standing
  statement-design rule: RUNS IN PREMISES, INDUCTIVE RELATIONS IN
  CONCLUSIONS.  (Flagged collision: the ratified-but-unimplemented
  `ThetaDefeqFireT` v2.2 concludes the lock's own inherited `hhead`
  shape.)

Ratified survivors (all landed, standard axioms, census unchanged):

* **`InZoneHeadedIn`** with its battery (`not_in_nil`, `sort_not_in`,
  `below_zone_fvar_not_in`, `leaf_imp_in`, the compound pair) — the
  hereditary waiver atom; its `.app`-argument breadth is LOAD-BEARING
  (it supplies the lockstep's absorb arm at enclosing rewrites; never
  narrow it).
* **The R1 lock restatement**: waiver =
  `(∃ fuel W, whnfLoop … core = .ok W ∧ InZoneHeadedIn d Γ W) ∨
  (¬ ∃ fuel W, whnfLoop … core = .ok W)` — both arms function-graph
  facts, depth-pinned to the composite depth; flat consumers refute
  the negative arm BY EXHIBITION of the lock's own landing.  The one
  supplier is the negative-completion lemma (a classifying
  fuel-dichotomy is FALSE: non-fuel throws exist).
* **`Engine.lean`** (between Species and ThetaLock; seal 4df1eb64):
  the payload-free absorbing relation `Absorb` (zone clause at the
  hereditary shape, N unconstrained — RuS's payload dropped because
  gate-free RawReach has no argument congruence), its full consumer
  battery (endpoint inversion = the lock's two disjuncts verbatim;
  ZoneFree exactness; spine exactness as ten per-shape inversion
  lemmas), the cursor-general substitution lemma with stated-first
  suppliers, `Absorb.rebase_of_in` (coarsening by clause choice = one
  constructor application, because payload-free), the machine kit
  (`whnfLoop_to_reaches`, throw-freeness, the `TerminalStep` triple —
  continuation-free; the naive `∀k`-stuck shape is unsatisfiable, it
  is the refuted CoreIdemF), and `AbsorbLockstepF` frozen as a claim.
  Probe record: the (m9) enclosing-rewrite absorb case PASSES; the
  risk-2 core-only arms were in pre-probe at parking.
* Earlier permanent yield consumed by the above: the anchored seam
  engine (R1/Align.lean), the fc-sliced trio, TeleBuilt/RowBuilt
  provenance (two construction sites tree-wide; datum-indexed
  inductive), the carriage (Columned twins on ThetaRelB), checker
  change #10 (projection-name guard; the projCong residue DELETED),
  the etaHead row (doubly-refuting disposal), census 5 → 4 → 3.

Literature identification (survey doc §1(a), B.4): the forward
dichotomy IS van Daalen's Reduction-under-Substitution / Square
Brackets Lemma (Endrullis–de Vrijer RTA 2008) — published, and NEVER
MECHANIZED IN ANY PROVER; the convergence witness is Lévy creation
type III; Accattoli–Guerrieri Lemma 42 (backward simulation holds
exactly for INERT entries) matches the waiver's scope to the letter.
Landing the SqBL engine remains a publishable artifact for whoever
resumes.

## 4. The NbE lane (task #159)

Class verdict for the pilot's four transport classes:
(1) substitution transport — DELETED from the machine's soundness,
conserved at one adequacy point; (2) sort agreement — absent from
soundness, conserved as the single `CodeConv` lemma at the adequacy
tier (the same theorem-shaped hole a third time, far cheaper: one
conv lemma family at the front door); (3) typing boundary — conserved,
re-clothed as per-event ledgers / Kripke LR; (4) machine partiality —
FOUND-THEN-DISSOLVED: it relocates no burden, it dictates definitions
(convergence baked into the relations — the candidates/CR move; a
fueled NbE machine forces it).

Eight statement refutations, one pattern rule: DENOTATION GUARDS
CANNOT SEE MACHINE PROPERTIES — a guard quantified over denotations
cannot deliver conclusions about the machine's syntactic outputs; the
guard-vs-conclusion distinction is load-bearing.

Sealed chain at parking: Codes → CodesK (Kripke; one-line
monotonicity) → PER symmetry (non-diagonal probe) → transitivity
half-dissolved (simultaneous structural induction) → convergence
baked in with the ACCEPTANCE TEST (BLR_symm/BLR_trans unconditional +
CodesKUnique premise-free, or the redefinition is wrong) → the
environment-weakening tier (397 lines, typing-free, vs the campaign's
~8.6k typing-conditional transport tier — the cost of Extend/Transport
is the cost of TERM SUBSTITUTION, not environment extension) →
`FinalCoherence` stated as the ledgers-must-meet target.  Remaining:
`BinaryFTK` (the risk concentration, ~800–1500 lines — simultaneously
the normalization content, the class-2 discharge, and the documented
head-position hard case) → `CodesKUnique`/`BLRTrans` → `CodeConv` →
`LRFundamental` → `EnvLRFromBuilt` → `FinalCoherence` → capstone.

## 5. The discipline instruments, with their catch record

* **Take-the-waiver** (tests statements): a waiver provable for
  arbitrary rows is a vacuous theorem wearing a disjunction.  Caught:
  the (F) fire-config arm (over-absorption), the bare error disjunct
  (`fppvac151`).
* **Consumption probe** (tests inductions): prove the step lemma on a
  minimal compound example first.  Caught: W4 (non-head descent)
  BEFORE the induction ran — predicted cross-lane, built from the
  tree's own witness, kept as the regression pair.
* **Per-clause coverage / mechanism coverage** (tests
  specifications): "which fact turns this reduction into that
  equation?" asked clause-by-clause; anchors verify existence, not
  mechanism (the C0 blind spot).  Caught: the disposal contract's
  compressed pin step — at implementation, not ratification; the rule
  exists so the next one is caught at ratification.
* **Acceptance test** (tests redefinitions): a redefinition ruled
  correct must make its motivating obstructions vanish AS THEOREMS,
  NOT PREMISES.
* **Quote-the-statement** (tests the checker itself): four recorded
  instances of asserting a lemma's or branch's scope from its name
  (etaCert's partner-only infer; the (m7) reversed bound; KnotFuelDet
  linking successes only; the CoreIdemF-refuted stuck shape) — two
  caught by review, two by implementers against tombstones.  The
  probe-first gate caught failure at the flagged-uncertain item every
  time it ran.

## 6. Standing prohibitions (with evidence)

* No non-standard axioms (user ruling; the battery pins
  propext/Classical.choice/Quot.sound).
* Conditional theorems are no better than sorries (user ruling,
  verbatim); residue architectures are internal scaffolding only.
* Θ-4: no completeness-of-defeq conclusions on transformed inputs —
  the verdict-stability tripwire, corroborated in print (Carneiro
  §3.1.1; lean4lean's sorried conjectures; the shipped kernel is
  itself verdict-incoherent at these corners — lean4#2258/#12520/
  #3213 — so verdict-narrowing deviations are FINDINGS, reported per
  the standing rule).
* No strategy supersets over the reference reduction; invariants over
  runtime gates; no unmemoized traversals; the R1 license prohibition
  (nothing discharges from `ZipSortOfAgree` itself).

## 7. Why the pivot

The new design (unverified annotation pass + checker-VALIDATED sort
annotations: the checker adds level comparisons at binders; defeq
compares annotations by level comparison; the model reads levels off
validated annotations) converts cross-run sort coherence from a
PROVEN METATHEOREM into a CHECKED PROPERTY.  It is the campaign's own
Θ-3 exit generalized from per-entry to whole-term, in the established
checker-change lane (#10, #152, the #126–#146 certification-of-
discarded-intermediates species), and it is what the reference
algorithm family itself does (the kernel re-infers types of neutrals
exactly where our residues sat — Lennon-Bertrand §4.4; lean4lean's
`isDefEqProofIrrel`).

What the campaign contributes to it: the residual proof burden
localizes to the ANNOTATION-MANUFACTURE-SITE AUDIT, and the campaign
has already enumerated those sites and their hazards — the K/eta
rescue rows (fabrication from annotations; W1/W6), η-expansion
(etaCert's partner-only inference), recursor-rule instantiation
(the iota lanes), and the nat-op types (the GMP pin family) — plus
the instruments (§5) to audit them with.  The six walls are the
evidence that the metatheorem route's price was real; the validated-
annotation route pays at manufacture sites instead, which are
finitely many and already named.

## 8. Branches

* `master` @ 46db5d1 — untouched by the campaign's WIP (three-sorry
  census unchanged on the lanes).
* `agent/cert-tax` @ f46e96850f5cbbed8a4bf0e5a720e3ba0227972c — the design ledger (this
  document's source of record).
* `agent/theta-runbatch` @ cb2c2ed3 — the Θ implementation
  lane: Engine.lean, the lock restatement, the batch book.
* `agent/nbe-lr` @ eb3591d2 — the NbE lane; `agent/nbe-pilot`
  @ 5e5fea0 (pilot, parked).
* `agent/sortspec-pilot` @ 55a92dc (parked, unmerged);
  `agent/carriage-probe` @ 954676c (red evidence — never merge).
