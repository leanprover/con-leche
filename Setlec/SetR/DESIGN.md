# Setlec/SetR — the mode-indexed algorithmic relation family (task #148)

This is the campaign's §-file for the `Setlec/SetR/*` tier.  The
campaign design document (architecture, the full rule tables, the task
sequence, the risk register) is the #148 design deliverable; this file
records what T2 **built**, where it **deviates** from the design's §1
as written, and what T3 (bridge) and T4 (soundness) need to know that
the design document does not say.  House practices are
`Setlec/TTVerify/DESIGN.md` §0/§25 (binding).

## Promoted practices (binding here; candidates for §0/§25)

Six rules earned promotion by recurring across unrelated
stages.  They sit at the top of this file because they are checks to
run *while designing*, not lessons to read afterwards.

**P1 — a helper premised on a whole environment bundle cannot
establish any field of that bundle.**  `EnvSHyp` carries `caps_ok`, so
`fireS` — premised on the bundle — could not be used to prove a
capability law (finding 6).  The repair was not to weaken the bundle
but to premise the *helper* on the fields it actually uses:
`fireS` used two of nine, both only at `eqName`, now `EqFormerKeyV`.
**Check this at the moment a field is ADDED to a bundle**, by asking
which helpers its own supplier will have to run; checking it when the
supplier is written is already too late, because by then the helper's
signature is load-bearing everywhere.

**P1a — a practice tells you a route is closed; it does not tell you
which of the open ones to take.**  P1 correctly ruled out consing the
projection recursor with its rule (stage 5b).  The remedy taken —
provision, fire, swap — was not merely more expensive than the right
one (re-aim the helper *below*, at the model's own name); it was
**blocked**, needing a transport nothing tools.  The failure was not a
misread premise but *stopping at the first remedy*.  The concrete
check: **before building around a closed route, read the sibling
lane's record for the same obstacle.**  `TTVerify/DeclIndProj.lean`'s
"Where the bottom runs" had the answer in prose, and both lanes'
DESIGN files exist precisely so this lookup is cheap.

**P2 — read a premise for the environment it quantifies over and the
degenerate case it admits, not for the data it supplies.**  Three
instances in one session, all of them the record failing against its
own author:

* finding 6 — `unitLawKeyS`'s inputs were checked for *availability*
  and not for *which environment* its `EnvS` sat at;
* `MemberUnitS` — `caps.unitlike = true` was read as "the artifacts
  exist" when over an abstract `caps` it says nothing at all;
* `MemberEtaS` — `EtaFamilyStored` was read from its name and purpose
  ("the family is complete, so it cannot be") instead of its text,
  where `etaFields = 0` makes the projection conjunct vacuous and the
  family completes inside the member fold.

The concrete check: for every premise of a statement you are about to
freeze, name (a) the environment each of its lookups is at, (b) what
it says when its numeric parameters are `0`, and (c) what it says when
its `IndCaps`/`ConstantVal` arguments are abstract rather than the
checker's output.

**P3 — truthfulness does not transport along an interpretation
equality.**  The `Eq` bridge (`quotInv_interpS`) proves
`interp ρ (quotInvV E …) = interp ρ (quotInvT …)`, and that moves
*memberships* across but nothing else: `AnnotOkV` is defined by
recursion on the `VExpr`, so the two sides have genuinely different
truthfulness obligations and the bridged one needs its own package
(`quotInv_annotS`).  The check is mechanical: **whenever a `htype`
obligation is discharged by rewriting the denoted type, ask separately
who supplies `AnnotOkV` of the type you actually stored.**  When the
answer needs more than the laws in the bundle, look for a *membership*
already in it before proposing a new field — `EnvS.mem_type` at the
stored constant was the whole answer here (`eqV_memS`), and the
worry that `EqLawV` was too weak was a failure to read the bundle.

*Corollary of P2, worth its own line:* **read the annotated
declaration, not the raw pin.**  `eqBasis`/`quotBasis` show
`Eq.rec`/`Quot.ind` rules that differ from the `eqRecA`/`quotIndA` the
installer actually stores (`.inert` vs `.plain`); a block docstring
written from the raw pin claimed two vacuous iota obligations that
were not vacuous at all.  The declaration under `…A` is the one the
proofs are about.

**P4 — this campaign's leverage comes from facts the model makes
available, not from objects the syntax makes constructible.**  Promoted
after two independently-proposed architectural alternatives died on
exactly this axis, neither of them for the reason its proposer
expected:

* the **tagged model** (pair every value with its ground level, so
  `interp` determines sort) would have supplied real facts — the
  refutations that forced the annotation architecture all use one
  device, a carrier shared across two levels, and tagging removes it.
  It died because the *syntax* already carries the sort more
  fundamentally: `denote2`'s `lamSortE` computes the λ codomain
  numeral at the empty domain, where no value can be read at all.
  Redundant-by-annotations, not wrong.
* the **ETT target** (`HasType` as the soundness skeleton) would have
  supplied a shorter model half — `HasType.sound` is 262 landed lines
  against the `Sound/*` tier's 4,295.  It died because the
  certificate-removal campaign's whole engine is *semantic recovery*
  (`piR_dom_unique`'s graph rigidity replacing a deleted runtime
  check), and a bridge into a declarative theory needs **derivations**,
  which rigidity cannot manufacture.  Its advertised win — "`AnnotOk`
  has no counterpart in the layer" — is precisely the absence that
  makes the removals impossible there.

So: **test a proposed alternative against P4 before pricing it.**  Ask
what it makes *derivable* that is not derivable now, and whether the
consumers need a fact or an object.  An alternative that only relocates
where the sort information lives, or that trades a semantic invariant
for a syntactic one, is not an alternative — it is the same design
paying different rent.  Both memos are in this file; both cost
estimates were sound and both were beside the point.

**P5 — a witness law and an inhabitation law are different lemmas, and
a regime tag decides which one a proof needs.**  `lamR_mem` is a
*witness* law: it concludes `lamR v A F ∈ˢ piR v A B` from the
pointwise `∀ x ∈ˢ A, F x ∈ˢ B x`.  At `v = 0` the product is a truth
value, and what membership of the canonical proof actually needs is
only that each fibre is **inhabited** — strictly weaker.  While a
tower's *value* carries an explicit `if v = 0 then pt` tag the
distinction never surfaces, because the leaf discharges pointwise;
delete the tag (as `psigmaMkV2` did, correctly, since the annotation
squashes the tower anyway) and the kind-`0` argument **moves from the
leaf to the root**, where only the inhabitation law will do.

The concrete check, and it is cheap: **when a value-level regime tag
goes, look for the weaker introduction law before assuming the proof
transposes.**  Here it did not exist — `pt_mem_piR_zero` had to be
added to `Interp2/Ops.lean` — and once it did, it served `psigmaMk`
*and* all three `pt`-valued propositions, which had looked like a
separate "inhabitation tail" and were in fact the same missing lemma.
Cost of finding it late: one seal.  Cost of the rule: one line.

## T2 inventory (this tier, as landed)

| file | content |
|---|---|
| `Rel.lean` | the five mutually inductive relations (`Red` 14 rules, `Infer` 10, `DefEq` 14, `Tele` 2, `DefEqL` 2 — 42 constructors), parametrized `(μ : CheckMode) (env : Env) (cval : TConstVal) (φ : Name → Nat)` over `List VExpr` contexts; the term-level spine helpers (`natLitV`, `succV`, `projSpinesV`, `etaFabArgsV`, `piResidualV`) |
| `Weaken.lean` | **M1**: the mutual weakening metatheory — `{Red,Infer,DefEq,Tele,DefEqL}.weakenN` along `LiftCtx` (reused from `Verify/Denote/HasTypeSubst.lean`), plus the `weakenHead` corollaries and the new lift-commutation support lemmas (`liftN_inst0`, `liftN_mkAppN`, `piResidualV_liftN`, `instRevChain_liftN(_high)`, `projSpinesV_liftN`, `etaFabArgsV_liftN`) |
| `CtxOkR.lean` | the context correspondence with the slack design (`Infer`-up-to-`DefEq` at each leaf) and its plumbing (`nil`, `open`, `openWith`, `weakenTop`, `app`), consuming M1 |
| `Decl.lean` | the `DeclR` per-kind `Prop`s (`DeclDefnR`, `DeclThmR`, `DeclOpaqueR`, `DeclAxiomR`, `DeclBasisR`, `DeclIndR`), the canonical-context helpers (`OpenCtxR`, `DefEqListW`, `TypedListW`, `IotaSidesTyR`), and the proved dispatch `checkDeclR_of` |
| `Examples.lean` | the sanity derivations (beta on a closed term, `Infer` through an app, a `Tele` chain, a weakened derivation) — build-compiled tests |

Elaboration cost is a non-issue: the whole mutual block elaborates in
~1.3 s, the tier builds in ~25 s cold.  **No seam split was needed**
(the design's ≤20 GB contingency for the wide rules never came close
to firing — the widest constructor, R11, has 27 hypotheses and is
cheap; wide *inductives* are not wide *eliminations*).

**M1's status: proved, as stated** (risk R3 did not fire).  The slack
design's cost landed exactly where the design priced it: one mutual
induction, consumed only inside `CtxOkR`.  Because Lean's `induction`
tactic does not drive mutual `Prop` families, the 42 cases are proved
once as standalone lemmas matching the recursor minor premises, and
each `weakenN` is a term-mode application of its recursor to the same
42 lemmas — the pattern to copy for any future induction over the
family (T4's soundness induction will need it).

## Deviations from the design's §1, with reasons

**D1 — closedness is an explicit side condition, not a consequence of
`denoteClosed`.**  The design says "closed side conditions must be
spelled `denoteClosed` … the weakening lemma depends on it", relying on
"instantiated stored types and rule rhs's are closed by
`constsResolve`+`looseBVarsBounded`".  That inference is an
*environment invariant*, not a property of the rule's own data:
`denote` at depth 0 maps an ill-scoped `fvar` to `.bvar 0`
(`denote_bvarsBelow` requires `WScoped`/`looseBVarsBounded`
hypotheses), so `denoteClosed … = some v` alone does **not** entail
`VExpr.Closed v`.  Each rule therefore carries the closedness of its
denoted stored objects as an explicit V-free side condition
(`VExpr.Closed TV/TVj/R/T/TP/TFv/TPv j/SC/V`), and R11's nested
premise takes `VExpr.bvarsBelow rP vp` as a hypothesis of its
implication.  The bridge discharges these by `denote_bvarsBelow` with
the checker's own scoping facts (which its claims already thread);
soundness may consume or ignore them.  The alternative — an `EnvWF`
hypothesis on M1 with per-case scoping derivations — was rejected as
strictly more work with a worse interface.

**D2 — R11's conclusion subject is the original spine.**  The design
table writes the conclusion as `mkAppN (cval n ψ) (xs.take mI ++ [m])`
(major already normalized) *and* gives premises 1–2 normalizing
`xs[mI] ⇝ m₀ ⇝ m`.  Both cannot be meant: with the normalized subject
the premises are unconsumable, and the bridge could not reach the rule
at all — `Red` has no argument congruence, and `iotaRec` normalizes the
major *internally*, stepping from the original spine directly to the
contractum.  R11's subject here is `mkAppN (cval n ψ) xs` (with
`xs.length = mI + 1`, the major unreduced at slot `mI`); the `Tele`
premise keeps the design's `xs.take mI ++ [m]` spine, which is the
checker's own `iotaCerts` argument.  Recorded as a finding against the
design table's spelling, resolved in the only readable direction.

**D3 — `rP ≤ mI` is an R11 side condition.**  *(Amended 2026-08-28:
guarded on `.nested` fires — see the fourth T4 amendment record.)*
Not checked per-fire by
`iotaRec`; supplied by `EnvWF` (as `RecRulesTT` concludes it).  M1
needs it: the nested premise's `instRevChain (xs.take rP) vp` commutes
with lifting only at chain arity `rP` (`instRevChain_liftN` wants
`bvarsBelow (xs.take rP).length vp`, and `(xs.take rP).length = rP`
needs `rP ≤ xs.length`).  V-free, bridge-dischargeable, one line.

**D4 — the rescues take `DefEq` premises where the design inlines
certificate packs.**  R12/R14's "proof-irrelevance pack (D8)" and
R13's "`structEtaCertWith` pack of D10" enter as a single premise
`DefEq μ Δ fab m₀`: `proofIrrel` succeeds through *either* D8 or D9
(its unit branch — the design's D8-only reading would under-cover the
checker), and D10's conclusion *is* `fab ≡ m₀`, so the bridge builds
the premise through exactly the inversion the design names and passes
the resulting derivation.  Premise-exactness is preserved — the
derivations reachable at that premise from a set-mode run are exactly
the D8/D9/D10 applications; soundness consumes the premise through
`DefEq`-sound regardless of which rule concluded it.

**D5 — one string-literal rule (`Red.strLitCtor`) serves R7 and R16.**
Per the design's own R16 row ("= R7's shape at the iota major").  The
rule carries the `denoteClosed` fact for `strLitToConstructor s` as a
side condition rather than relying on the near-`rfl` identification
with `strLitT` — the honest transpose; the bridge discharges it from
the `denote` clause equations.

**D6 — `DeclIndR`'s statement granularity (T3/T5 refinement points).**
The value kinds, the axiom/basis kinds, `checkDeclR_of`, the member
fold (`MemberValR` — full), the recursor provisioning, and the
canonical iota-theorem pack (`IotaThmR` — transposed pin-for-pin from
`checkIotaThm`) are stated at full fidelity.  Two places are
signature-stable but flagged for refinement when their first consumer
is elaborated (the house rule: do not freeze a statement no consumer
has exercised):
  * `ProjFnR` quantifies the stored rule's `rhsA` without transposing
    `checkProjRule`/`checkProjShape`'s synthesis (their outputs are
    pinned by the installed entry; the walks are T5's `proj_rules`
    supplier);
  * `ProjInstallR`/`TemplatesR`'s per-field skip conditions
    (`installProjFnStep`/`installProjTemplateStep`) are stated as
    disjunctions at entry granularity.
The canonical-context discipline is fixed and non-negotiable, though:
every positive-depth run is stated over the **pinned** context of the
opened annotations' denotations (`OpenCtxR`) or the `Nat` entries —
an existential context would be vacuous-premise-unsound (an
uninhabited entry empties `Sat`), the exact trap R4 warns about one
level up.

**D7 — D14/`litSuccApp` is stated in one orientation.**  The design
says "both orientations"; `DefEq.symm` composes the other, and the
checker's two clauses are symmetric images.  Ditto D10/D12/D13's
mirrored directions (per the design's own "(+ mirror) via D2").

## What T3 and T4 need to know (beyond the design doc)

* **Mutual induction pattern**: `induction h using Red.rec (motive_2
  := …) …` works with explicit motives for all *other* family members
  (the target's motive is inferred), but case names collide (`refl`,
  `trans`, `nil`, `cons` appear twice) — use positional bullets or the
  `Weaken.lean` pattern (shared case lemmas + term-mode recursor
  application).  Inversion by `cases h` works normally.
* **`μ` is phantom in T2**: no rule reads it — the family as written is
  the set-mode certificate inventory (the seven tt-only checks are
  absent by premise-exactness, not by mode-gating).  A future [tt]
  instance that needs them would add `μ.ttChecks = true →` premises;
  nothing in M1/CtxOkR depends on `μ`'s value.
* **The slack lives in the bridge statement**: `Infer` has the plain
  `bvar` rule; the bridge's infer-claim must be stated as
  `∃ T', Infer … v T' ∧ DefEq … T' ⟦t⟧` (design §0 decision 1), and
  `CtxOkR`'s leaf packages have exactly that shape — `CtxOkR.openWith`
  takes the new head's package in slack form (`hnew`), which is what
  the binder-congruence clauses of `defeqStep` will feed it (the
  second side's annotation enters through the `DefEq` component).
* **D1's closedness side conditions are the bridge's to supply**, via
  `denote_bvarsBelow hcl d e hws hb` — the `WScoped`/`looseBVars`
  facts are the same ones `WhnfCoreClaimsTT`-shaped statements already
  thread; budget one extra conjunct per denote fact.
* **`hcl : ∀ n ψ, VExpr.Closed (cval n ψ)`** is the one ambient
  hypothesis of M1/`CtxOkR` — it is `EnvTT.cval_closed`'s shape and
  will be an `EnvS` field; every consumer has it.
* `DefEqL.length_eq` supplies D7's redundant length side condition at
  rule-application sites.
* The recursor argument order for term-mode `*.rec` application is
  constructor declaration order across the whole mutual block (Red's
  14, then Infer's 10, then DefEq's 14, then Tele's 2, then DefEqL's
  2); `Weaken.lean`'s five theorems are the template.

## T2 gate record

Landed on master (see the commit trailer for the battery record):
`lake build` warning-free with the tier force-recompiled, `lake test`,
arena + e2e + split + mode sweeps unchanged (proof-side only — no
binary file in the build cone is touched), zero sorries, and the
`Setlec.SetR` examples' axioms exactly `[propext, Classical.choice,
Quot.sound]` or fewer (the family's constructors and M1 use no
classical reasoning; the axiom audit runs on the examples and the five
`weakenN`s).

## T3 — the bridge (`Setlec/SetR/Bridge/*`)

### Inventory (as landed)

| file | content |
|---|---|
| `Bridge/Env.lean` | `EnvR` — the seven **V-free** environment facts the bridge consumes (`cval`, `cval_closed`, `wf`, `val_params`, `ty_denotes`, `defn_eq`, `thm_ok`), plus `CtxOkR.of_subset`.  Every field is an `EnvTT` field or an immediate consequence; T5's `EnvS` supplies an `EnvR` by projection (one adapter).  `ty_denotes` is deliberately the *weakest* form of `mem_type` — the bridge needs a denotation to name, never a membership, and that is what keeps it free of semantic content |
| `Bridge/Claims.lean` | `WhnfCoreClaimsR`, `WhnfClaimsR`, `DefEqClaimsR`, `InferClaimsR`, `CheckStepR`, the proved fuel-zero case (`checkSoundR`), the three fuel-generic wrappers, and the frame packages (`frame_inferR`, `whnfCore_packageR`, `whnf_packageR`) |
| `Bridge/WhnfCore.lean` | the six leaf clauses (R1), zeta (R5), beta (R4), the `.app` clause (R3/R4/R11 dispatch), the delta step (`denote_delta_stepR` — an **identity**), the loop budget induction (`Red.trans` chaining) and `whnf_claimsR`; obligations `IotaStepR`, `ProjStepR`, `ReduceNatStepR` |
| `Bridge/Infer.lean` | I1–I5 (`sort`, `fvar`, `const`, `litNat`, `litStr`) + the `bvar` refutation, and `infer_claimsR`'s dispatch; obligations `InferPiStepR`, `InferLamStepR`, `InferAppStepR`, `InferLetStepR`, `InferProjStepR` |
| `Bridge/DefEq.lean` | `CtxOkR.openCong` (**the batch-(a) headline**), the loop/continuation factoring (`DefEqContR`, `DefEqStepR`, `defeqLoop_claimR`, `defeq_claimsR`), the full `defeqStep_claimR` (syntactic short-circuit, both `whnfCore` moves, literal acceleration, all four lazy-delta branches), `delta_packageR`, and the assembly `checkStepR_of` over a `StepObligationsR` bundle; obligations `ProofIrrelStepR`, `DefEqStuckStepR`, `DefEqSpineStepR` |

One relocation was forced and made: `denote_params_ext` / `denote_instLevels`
(and their four private helpers) moved from `Setlec/TTVerify/Extend.lean` to
the new `Setlec/Verify/Denote/Levels.lean`, statements unchanged.  They are
V-free and lane-independent — the campaign design's T1 lists exactly this
kind of move — and both lanes now import them from below rather than the
`SetR` tier importing `TTVerify`.

**Batch (a) result — risk R3's binder-congruence detection point passes.**
`CtxOkR.openCong` is the slack design working exactly as §0 decision 1
predicts: the second side of a `∀`/`λ` congruence is opened with its own
annotation while the context holds the first side's denotation, and the
leaf package is the plain `Infer.bvar` plus the domain certificate weakened
by M1 (`DefEq.weakenHead`).  `CtxOkR.openWith`'s `hnew` argument has
precisely that shape; nothing had to be pushed anywhere.

### FINDING (blocking, campaign-level): `Red`-at-an-inferred-type premises do not compose with the slack

**The claim in the campaign design's §0 decision 1 — "this composes
because every checker certificate is an infer+defeq *pair* and every rule
premise below is such a pair" — is false for the rules as written (here
and in the design's own §1 tables).**  A large family of premises is an
infer + **`Red`** pair, and `Red` is not `DefEq`: the slack cannot be
absorbed at those sites, in either direction.

*The shape.*  Wherever the checker does

```
    t ← infer x ;  w ← whnf t ;  match w with | Shape => …
```

the rules transpose it as `Infer μ Δ x tx → Red μ Δ tx Shape → …`
(with the **same** `tx`).  What the bridge can produce, from
`InferClaimsR` + `WhnfClaimsR`, is

```
    Infer μ Δ ⟦x⟧ T' ,   DefEq μ Δ T' ⟦t⟧ ,   Red μ Δ ⟦t⟧ Shape
```

— an `Infer` at `T'`, a `DefEq` to the checker's inferred type, and the
reduction from *that*.  There is no rule of `Red` that lets a `DefEq`
prefix be absorbed (correctly so: `Red` is directed reduction), and
`Infer` has no `conv`.  So the premise pair is unreachable.

Mechanized at `.forallE` (`inferTypeCore_forall_inv` → `Infer.pi`): the
whole clause elaborates up to the residual goal

```
    ∃ tA, Infer μ Δ A tA ∧ Red μ Δ tA (.sort (u.eval φ))
```

from `hAT : Infer μ Δ A T'`, `hslack : DefEq μ Δ T' vtty`,
`hRw : Red μ Δ vtty (.sort (u.eval φ))` — unreachable.  The *`DefEq`-shaped*
version of the same goal,

```
    ∃ tA, Infer μ Δ A tA ∧ DefEq μ Δ tA (.sort (u.eval φ))
```

is `⟨T', hAT, hslack.trans (DefEq.ofRed hRw)⟩` — one line.  Both were
elaborated against the landed tier before this note was written.

*Affected premise pairs* (every "reduce an inferred type to a shape" site):
I6 `pi` (×2), I7 `lam`, I8 `app`, I9 `proj`, I10 `letE`, R6 `projRed`
(×2, through a doubled `Infer`), R12 `rescueK`, R13 `rescueEta`,
R14 `rescueUnit0`, D8 `irrelProp` (×2, doubled `Infer`), D9 `irrelUnit`
(×2), D10 `structEta`, D11 `structUnit` (×2), D12 `pairEta`, D13 `eta`.
Premises that are infer+**defeq** pairs — `Tele.cons`, I8's argument
re-check, I10's value check, R4 `beta` — compose on the nose and are
already discharged in the landed batches; so do the binder congruences.

*Candidate repairs, with their cost.*  All of them move the same
obligation onto T4, which is why this is a campaign decision and not a
bridge fix:

* **A — `Red μ Δ tx Shape` becomes `DefEq μ Δ tx Shape`** at the sites
  above.  Bridge cost: nil (one `DefEq.trans` per site, shown above).
  Premise-exactness is preserved in the design's own sense (`Red ⊆ DefEq`
  by D4; the checker's certificate at that site is unchanged).  Soundness
  cost: `DefEq`-sound takes `AnnotOkV` of both sides, and the *right* side
  is no longer produced by `Red`-sound.  Per shape:
  `.sort u` — free (`AnnotOkV` of a sort is `True`): covers I6, I7, I10,
  D8, R6.  `cval c ψ` — free from `EnvS.annot_okV`: covers D9.
  `mkAppN (cval T ψ) ts` **with** a `Tele` premise over `ts` — plausible
  via a new "`AnnotOkV` of a `cval`-headed spine from `TeleFitV`" lemma:
  covers D10, D11, and R12–R14 partially.  **`.pi A B` (I8, D13) and the
  `Tele`-less `cval`-spines (I9 — `projParamCert` is tt-only, D12) have
  no replacement source**; those four rules need a decision.
* **B — insert the slack explicitly** (`Infer μ Δ x tx → DefEq μ Δ tx sx →
  Red μ Δ sx Shape`).  Bridge cost nil; soundness cost identical to A
  (`Red`-sound now needs `AnnotOkV sx`, which only the `DefEq` premise
  could supply).  No improvement over A.
* **C — add `Infer.conv : Infer μ Δ v T → DefEq μ Δ T T' → Infer μ Δ v T'`**
  and drop the slack everywhere (`CtxOkR` back to identity form, the
  bridge claim on the nose, the bridge becoming a line-for-line mirror of
  the TT lane's `CheckStepTT`).  Bridge cost: strongly *negative* — this
  is the cheapest bridge of the three.  Soundness cost: exactly one site
  — the `conv` case needs `AnnotOkV T'`, which `Infer`-sound cannot
  conclude and `DefEq`-sound cannot cross.  This is the design's own R3
  fallback ("the `Infer.bvarConv` twist rule … its known cost is the
  AnnotOkV-of-`T` circularity").

*The common root.*  Every repair reduces to one question: **can
`AnnotOkV` cross a `DefEq`?**  It cannot in general — a biconditional
`AnnotOkV a ↔ AnnotOkV b` fails at `DefEq.ofRed` + `DefEq.symm` (the
contractum of a β-redex carries no `AnnotOkV` for the redex's λ
annotation), and the one-directional forms fail at `irrelProp`, which
relates arbitrary proofs.  So the obligation has to be discharged
site-by-site from each rule's *other* premises, and repair A is the shape
that makes the most sites free.  **Recommendation: A, with the four
residual rules (I8, I9, D12, D13) carrying whatever additional premise
T4 finds it needs — those four are exactly the sites where the campaign
design already flagged "semantic domain determination" as the recovery
route (design §1.3's I9 row, §1.2's D12 row), so the audit that produced
"no finding #1" is the audit to re-run there.**

Until that decision lands, the five `Infer*StepR` obligations and the
three reduction/defeq obligations in `Bridge/*` are stated but not
discharged: batches (b)–(g) all pass through at least one affected
premise pair, so discharging any of them now would mean freezing a rule
shape the decision may change.

### Notes for the batches that follow

* **The D1 closedness discharge, once.**  Every `VExpr.Closed`/`bvarsBelow`
  side condition of the family is discharged by `denote_closed hcl hnf hbd`
  (for `denoteClosed` of a stored, `hasFvar = false`, `looseBVarsBounded`
  expression — `EnvR.wf` supplies the last two per kind) or by
  `denote_bvarsBelow hcl` at positive depth.  `infer_const_claimR` is the
  worked instance: `m.ty_denotes` names the `VExpr`, `denote_instLevels`
  moves it onto the instantiated type, `denote_closed` closes it, and
  `denote_lift` re-reads it at the ambient depth.  Every other stored-type
  and rule-`rhs` side condition in R11/R12–R14/D10–D12 follows the same
  four moves; budget one extra conjunct per `denote` fact and nothing else.
* **`μ` stays generic.**  The claims are stated at an arbitrary `mode`,
  with the relation's index taken to be that mode: task #147's seven gated
  certificates are *extra* facts a `.ttModel` run establishes, handed back
  by the inversions as `mode.ttChecks = true →` implications, which the
  bridge never consumes.  Fixing `mode := .setModel` would be a gratuitous
  restriction, and the generic form costs nothing.
* **The obligation boundaries are the checker's own function boundaries**
  (`iotaRecP`, `reduceNatP`, `proofIrrelP`, `defeqSpineP`, and `whnfCore`/
  `inferTypeCore` restricted to one `Expr` shape).  A *case restriction* is
  legitimate; a *stage split* inside a `do` block is not, and none is used
  — `defeqStep_claimR` is one proof for that reason.

## T4 — DECISION on the slack/`Red` finding: repair A, no extra premises (2026-08-27)

**Decided by the soundness side, as the interface record.**  All 20
`Red`-at-an-inferred-type premises (T3's list: I6 ×2, I7, I8, I9, I10,
R6 ×2, R12–R14, D8 ×2, D9 ×2, D10, D11 ×2, D12, D13) are now
`DefEq μ Δ tx Shape` in `Setlec/SetR/Rel.lean`, and the two
declaration-level front doors with the same shape (`ConstantValR`'s
`ensureSort` pair and the thm-kind's `sort 0` pair in
`Setlec/SetR/Decl.lean`) follow suit.  Subject-side reductions (R6's
`Red p P`, R7's chain, R8–R10's argument whnfs, R11's major chain)
stay `Red`.  `Weaken.lean`'s affected cases re-signed (`RedW → DeqW`
in the IH slots); `CtxOkR` untouched (it never applies an affected
rule); `Examples.lean` adjusted.  **The four residual rules (I8, I9,
D12, D13) carry no additional premise** — the re-run of the
"semantic domain determination" audit found every needed fact
derivable from set-mode certificates (below), so there is **no
finding #1**.

**Why repair C was rejected.**  `Infer.conv` buys the cheapest bridge
but breaks the certificate-inventory reading of `Infer` (a rule with
no checker counterpart), puts a conv case into every future inversion
of an `Infer` premise (R6's soundness *must* invert its `Infer P te`
premise — see below — and D12/I9 may), and its one concentrated
obligation (AnnotOkV crossing) is exactly the impossible one.  Repair
A's per-site obligations all discharge.

### The soundness architecture that makes A free (binding for T4/T5/T6)

The analysis that settled the repair also settled the soundness
statement shapes, which **diverge from the campaign design's §0
decision 2 as written** in three ways.  Root cause (agreeing with
T3's "common root", proved independently on this side): `AnnotOkV`
cannot cross a `DefEq` in either direction — the biconditional dies at
`ofRed` + `symm` (a truthful contractum does not rebuild the redex's
hereditary λ-clause), one-directional forms die at `symm` alone — *and*
`DefEq.trans`'s free middle term already makes any
`AnnotOkV`-hypothesis-carrying DefEq-sound non-inductive (the middle
has no truthfulness source).  Both problems have one solution: the
equality lane must not touch `AnnotOkV` at all.

* **DefEq-sound is unconditional**: `∀ ρ, Sat V Δ ρ → ⟦a⟧ρ = ⟦b⟧ρ`.
  No `AnnotOkV` hypotheses (stronger than the design's "takes AnnotOkV
  of both sides"), no `AnnotOkV` conclusions.  `symm`/`trans` become
  trivial; D5/D6/D13's binder premises are consumed at *membership*
  extensions (`Sat_cons`), which need no truthfulness.
* **Red-sound**: `∀ ρ, Sat → ⟦v⟧ρ = ⟦w⟧ρ ∧ (AnnotOkV ρ v → AnnotOkV ρ w)`
  — the equality is unconditional too; the transport conjunct is the
  design's forward preservation, and stays (its consumers: reduct
  truthfulness at whnf sites in the T5/T6 folds).
* **Infer-sound**: `∀ ρ, Sat → AnnotOkV ρ v ∧ ⟦v⟧ρ ∈ˢ ⟦T⟧ρ` — the
  design's third conjunct (`AnnotOkV T`) is **dropped**.  Its only
  intra-induction source was `Red`-transport along the type-whnf
  premise (gone under repair A), and the consumer audit found nothing
  that needs it: every `AnnotOkV`-package the hard rules use is
  rebuilt from memberships + pinned-value rigidity (below), and T5's
  stored-type truthfulness comes from the *type front door's* subject
  conjunct (`Infer ⟦type'⟧ tT` gives `AnnotOkV ⟦type'⟧`), never from a
  value inference's type slot.
* **Consequently `SatA` degenerates to `Sat`** (`TT/Semantics/
  Soundness.lean`, reused): the per-entry `AnnotOkV` component of the
  design's `SatA` had exactly one consumer — I2's type conclusion —
  which died with the type conjunct.  Binder congruences then extend
  contexts by membership alone, which is what makes their cases
  provable at all.
* **Tele-sound**: `∀ ρ, Sat → TeleFitV ρ T as rest ∧
  (∀ a ∈ as, AnnotOkV ρ a) ∧ (AnnotOkV ρ T → AnnotOkV ρ rest)`;
  **DefEqL-sound**: `∀ ρ, Sat → as.map (interp ρ) = bs.map (interp ρ)`.

### The four residual rules, discharged (the re-run audit)

* **I8 `app`**: the membership needs only `⟦f⟧ ∈ ⟦tf⟧ = piC ⟦A⟧ _`
  and `⟦a⟧ ∈ ⟦ta⟧ = ⟦A⟧` (two unconditional `DefEq`-eqs), then
  `app_mem_piC` + `interp_inst0`; the subject package is those two
  memberships.  `AnnotOkV A` is *not* needed — that worry was an
  artifact of the old motive shape.
* **I9 `proj` / D12 `pairEta`**: the sigma package comes from
  **pinned-value rigidity**, not from the type's truthfulness:
  `⟦TE⟧ = app (app (psigmaV u v) ⟦ps₀⟧) ⟦ps₁⟧` with the former pinned
  (`proj_ok` + `basis_pinned`).  If `⟦ps₀⟧ ∉ univ u` the partial
  application is an off-domain application of a non-`pt` graph, hence
  `empty` (`app_graph_of_not_mem`, `psigmaV ≠ pt` by witness), so the
  premise membership `⟦p⟧ ∈ ⟦TE⟧` is vacuous; same for `⟦ps₁⟧` against
  the fibre space; on-domain, `psigmaV_app` folds `⟦TE⟧` to a
  `sigmaSet` *with* the domain memberships in hand.  Membership in the
  pinned former's application **self-certifies the domains**.  D12
  additionally uses `psigmaEta_law` (+ the `Nat.max = 0` collapse
  branch, where both sides are `pt`).
* **D13 `eta`**: `⟦b₁⟧ = app ⟦b⟧ x` for `x ∈ ⟦A₁⟧` comes from the
  binder premise at a `Sat`-extension; `lamC_congr` + `lamC_eta` close
  it.  No truthfulness of `A₁` enters.
* **R6 `projRed`** (the doubled-`Infer` sites): the collapse branch
  (`fieldSort`-eval 0) is the certificate chains + `mem_univ_zero` +
  `sfst_pt`/`ssnd_pt`.  The no-collapse branch obtains the constructor
  spine's component memberships by **inverting the `Infer P te`
  premise** (relational `cases`; the I3-alternative head is handled by
  `annot_okV`/`mem_type`) — the exact transpose of the model's own
  `inferTypeCore_app_inv'` walk (`Setlec/Model/Core/Whnf.lean:539-741`),
  which is the mechanized witness that set-mode certificates suffice.

**For T5/T6**: `EnvS`'s semantic fields will be consumed in
membership/interp-equality form only (`RecRulesV`, `CapsOkV`,
`NatOpsV`, `DivModV` hypotheses are `TeleFitV` fits and memberships;
`mem_type` carries the membership *and* the denoted type's `AnnotOkV`
— supplied by the type front door's subject conjunct; `annot_okV`
unchanged).  Nothing consumes an `AnnotOkV`-of-inferred-type fact.

### T4 addendum — finding 2 (projection congruence), repaired in the same amendment

Two accepting checker paths had no rule: `whnfCoreBody`'s `.proj`
clause returns the stuck `.proj sn i e'` after reducing the scrutinee
on every non-firing branch (`Core.lean:1431-1475`), and `defeqStep`'s
stuck block accepts `.proj` vs `.proj` on index equality plus
scrutinee defeq (`Core.lean:1884-1889`).  Added `Red.projArg` and
`DefEq.projCong` (each: scrutinee premise only — the checker runs no
certificate on those paths), **appended at the end of the respective
constructor lists** so the T2 rules keep their relative recursor
positions (all `*.rec` applications after `Red`'s block still shift by
one — `Weaken.lean`'s five applications show the new order:
`wkRedProjArg` after the rescues, `wkDeqProjCong` after
`wkDeqLitSuccApp`).  Soundness verified against the T4 architecture
before landing: the equality is `congrArg` on the scrutinee's
(unconditional) equality through `interp_proj`; `Red.projArg`'s
forward `AnnotOkV` transport holds because the `.proj` clause of
`AnnotOkV` is the scrutinee's truthfulness plus `i < 2` plus a
*value-level* sigma package on `⟦e⟧`, and the package rides the
scrutinee equality.

### T4 — the dropped-conclusion consumer check (run before landing, per protocol)

The three reshapes were checked against every planned T5/T6 consumer
in the campaign design's §2/§4 tables:

* **`EnvS.annot_okV`** is built from the *value* front door's
  **subject** conjunct (`Infer [] ⟦value'⟧ tv` gives
  `AnnotOkV ⟦value'⟧`), which survives unchanged.  ✓
* **`EnvS.mem_type`'s membership** is the value front door's `mem`
  plus the `DefEq tv ⟦type'⟧` certificate — and here the two reshapes
  are *linked*: with the old weak DefEq-sound this step needed
  `AnnotOkV tv` (exactly the dropped conjunct); with the unconditional
  DefEq-sound it needs nothing.  Dropping the type conjunct is
  consistent *only* together with the unconditional form — neither
  reshape is separable.  ✓
* **`EnvS.mem_type`'s `AnnotOkV`-of-the-denoted-type component** (what
  I3-sound consumes) comes from the *type* front door's subject
  conjunct (`Infer [] ⟦type'⟧ tT` gives `AnnotOkV ⟦type'⟧`) — present
  for every declaration kind.  ✓
* **`RecRulesV`/#146-avoidance** ("the slot's membership comes from
  the statement's own AnnotOkV"): the statement is the `_model.iota_j`
  member's stored *type*, and its `AnnotOkV` is again the member's
  type-front-door **subject** conjunct; the tower elimination
  (`app_mem_piC` chain + `eq_lawV` + `mem_eqv`) consumes memberships
  and that subject-side fact only.  Same for the eta/unit law
  derivations from `_model.eta`/`_model.unitlike`.  ✓
* No planned consumer reads the `AnnotOkV` of a value's *inferred*
  type (`tv`/`tT` slots) anywhere in §2's supplier column; the
  conjunct is consumerless as dropped.  ✓

### T4 amendment, second increment — R6 carries the constructor spine's telescope certificate

Batch (e)'s audit found the one place where the relational abstraction
loses a fact the checker's run contains: R6's `Infer Δ P te` premise.
The model's proj-reduction soundness (`Model/Core/Whnf.lean:639-741`)
recovers the constructor components' canonical memberships by
*inverting the infer run* (`inferTypeCore_app_inv'` four deep — the
run is syntax-directed, so the inversion is deterministic).  The
relational counterpart — `cases` on the `Infer` premise — is **not**
deterministic: `Infer.const`'s subject `cval n ψ` overlaps app-shaped
terms, and in that alternative the component certificates are
unreachable (and the value-level packages provably cannot substitute —
the partial-collapse scenario of the #100 note).  So R6 now carries
`denoteClosed` of the constructor's instantiated stored type (+ D1
closedness) and a `Tele μ Δ TC vs restC` premise — the infer run's own
per-argument re-checks, exposed, by the same premise-exactness
argument as repair A.  Bridge cost: the inversion walk the model
already performs, packaged as `Tele.cons` chains (the pinned
constructor type is concrete, so the domain alignments are
computations).  With it, R6's soundness is `TeleFitV_psigmaMk` (the
four component memberships) + `psigmaMkV_app`'s fold, and the
`Nat.max = 0` collapse branch closes from the field certificate's
sort chain — no inversion, no AnnotOkV.

### T4 batch (e) record — the proj rules land

`Sound/Proj.lean`: `projEntry_pins` (the `ProjOkT` + stored-name
identification), the three pinned-type denote computations
(`denote_pairFstTy_eq`/`denote_pairSndTy_eq`/`denote_psigmaMkTy_eq`),
the two concrete `piResidualV` walks, `TeleFitV_psigmaMk`, and the two
cases: I9's sigma package and residual membership come from
`mem_psigmaV_app` (rigidity — the #129-replacement, "membership
self-certifies the domains") + `sfst_mem`/`ssnd_mem`; R6 as above.
`EnvSHyp` gained `proj_ok : ProjOkT env`.

## T4 — COMPLETE: the soundness half lands

### Inventory (as landed)

| file | content |
|---|---|
| `AnnotOkV.lean` | `AnnotOkV` (the `AnnotOk` transpose; cons-extension, `eqE`/`prf` leaves, definedness conjuncts dropped incl. the `lam` clause's junk `∃ B, w ∈ˢ B` companion), clause equations, `interp` invariance below a bound, the two-lemma substitution metatheory (`AnnotOkV_liftN`/`AnnotOkV_inst` as biconditionals, `AnnotOkV_inst0`), `TeleFitV` + `appN`/`rest_annot`/`appN_annot` |
| `Sound/Motives.lean` | the five motives (`RedS`/`InfS`/`DeqS`/`TeleS`/`DeqLS`, the graded architecture), `EnvSHyp` (nine fields: `cval_closed`, `annot_okV`, `mem_type`, `basis_pinned`, `caps_ok`, `proj_ok`, `nat_ops`, `div_mod`, `rec_rules`), the law shapes (`EtaLawV`/`UnitLawV`/`CapsOkV`, `NatOpsV`, `DivModClausesV`/`DivModV`, `IotaIndexPinV`/`RecRulesV`), `interp_mkAppN_map` |
| `Sound/Struct.lean` | Red refl/trans/appFn/beta/zeta/projArg; Infer sort/bvar/const/pi/lam/app/letE; DefEq structural core + congruences + D14; Tele/DefEqL |
| `Sound/Irrel.lean` | D8/D9 (proof irrelevance; `unitLike_eq_punit` via `basis_pinned`), D13 (λ-eta) |
| `Sound/Rigidity.lean` | off-domain-emptiness eliminations (`app_lamC_of_not_mem`, `psigmaV_ne_pt`, `mem_psigmaV_app`, `psigmaMkV_zero`) |
| `Sound/Stuck.lean` | D10/D11 (the capability-law consumers), D12 (pair eta by rigidity), R12–R14 (rescues; `fab_annot`) |
| `Sound/Proj.lean` | I9/R6 (`projEntry_pins`, pinned-type denote computations, concrete `piResidualV` walks, `TeleFitV_psigmaMk`) |
| `Sound/Lit.lean` | I4/I5/R7/R8 (`natLit_facts`/`strLit_facts` — `mem_type`-based, `denoteClosed_strLitToConstructor`) |
| `Sound/NatOps.lean` + `Sound/NatOpsWf.lean` | R9/R10 (equation plumbing + sixteen per-op literal meta-inductions, the model's WF bodies transposed 1:1; PinGen certificates for the bit ops) |
| `Sound/Iota.lean` | R11 (the `RecRulesV` consumer; spine split + index pin + fired contract) |
| `Sound/Main.lean` | the five theorems `{Red,Infer,DefEq,Tele,DefEqL}.sound` — one recursor application each over the 46 case lemmas |

### For T5 (the interface, in one place)

`EnvSHyp V env cval φ` is what T5's `EnvS` must discharge, by
projection.  Statement shapes deliberately frozen by this tier's
consumers (the house rule); the suppliers named per field in the
docstrings.  Notes:

* `mem_type` carries the **denoted type's `AnnotOkV`** beside the
  membership — supplied by the *type front door's* subject conjunct
  (`Infer ⟦type'⟧ tT` → `Infer.sound`'s first component), never by a
  value inference's type slot (that conjunct no longer exists).
* `RecRulesV` concludes the equality **and** the applied reduct's
  truthfulness under argument truthfulness (the `RecRulesOk`
  `AnnotOk`-of-rhs clause, fired); its hypotheses are memberships
  (`TeleFitV`), pointwise interp-equalities, and the `IotaIndexPinV`
  existential — nothing `AnnotOkV`-conditional.
* The laws (`EtaLawV`/`UnitLawV`) are the *model's* `EtaLaw`/`UnitLaw`
  transposes (not `EtaLawTT`'s re-signed form): no #135/#136/#137
  content, the fabrication side unconditioned.
* `NatOpsV` is equation-based (the `NatOpsOk` transpose); `DivModV` is
  clause-based over `DivModClausesV` (the `DivModOk` transpose) —
  both keyed exactly on what `certifyNatEqs`/`checkDivModPin`
  certify, consumable from `Decl.lean`'s packs through the
  unconditional `DefEq.sound`.
* Relocations made for lane-sharing: `BasisPinnedTT` →
  `Verify/Denote/Pinned.lean`; `unitLike_eq_punit` /
  `pairLike_eq_psigma` / `pinnedInfoT_recInfo_cases` →
  `Verify/PinnedShapes.lean` (generalized to `BasisPinnedTT`);
  `natOpGuard_inv`/`intro`/`cons` → `Verify/EnvGuards.lean`.

**No finding #1**: every case closed on set-mode certificates alone;
the two relation amendments (repair A; R6's telescope exposure) were
premise-*shape* corrections, not new checks.
### Batch (f) landed — and what premise-exactness cost here

`Bridge/ReduceNat.lean` discharges `ReduceNatStepR` (R8 `natSucc`,
R9 `natOp1`, R10 `natOp2`), so **`WhnfClaimsR` at `fuel + 1` is closed**
(`whnf_claimsR_closed`), and `Bridge/Step.lean` assembles `CheckStepR`
from the remaining ten obligations.  The batch is repair-independent:
R8–R10 have no `Infer` premise, so the finding above cannot reach them.

The scale is the number worth recording.  The TT lane's counterpart
(`Setlec/TTVerify/NatOpsStep.lean`) is ~1 900 lines and almost all of it
is *content*: sixteen `natOps_*_closed` meta-inductions transporting
each stored recurrence to the layer's numerals, on top of identifying
`natLitT` with `numeral` through the pinned basis valuations.  Here the
whole batch is ~430 lines of branch dispatch plus four denotation facts
(`denote_natLitV`, `denote_rawNatLitR`, `denote_natOpResultR`, the two
application-shape inversions), because **the rules are stated over
`cval` and `natLitV` directly**: `natLitV cval φ n` *is* `denote`'s own
literal clause, so nothing has to be pinned, and the fold's value enters
as the side condition `denoteClosed cval env φ (natOpResult c n₁ n₂) =
some V`, which the bridge *computes*.  The recurrences never appear —
they are the soundness tier's business, where `EnvS.nat_ops` consumes
them once.  Quote this when sizing (b)–(g): the ratio is roughly 4:1 in
the bridge's favour, and it is entirely the two-pack discipline.

Two more V-free relocations were forced and made, both verbatim:
`natOpGuard_deps` / `natOpGuard_bools` / `natOp_stored` from
`TTVerify/NatOpsStep.lean` to `Setlec/Verify/EnvGuards.lean` (whose
docstring already claims to be the home of the guards' V-free
readings), and a new `natOpResult_atom` beside `natOpResult_shape` in
`Setlec/Verify/InferLemmas.lean` — the strengthening a *denoting*
consumer needs, since "some constant" is not enough when `natOpGuard`
pins exactly `boolTrueName`/`boolFalseName`.

### FINDING 2 (raised at batch (f); **repaired** by T4's addendum above): the family has no projection congruence

*Status: resolved.*  `Red.projArg` and `DefEq.projCong` landed with the
repair-A amendment (see "T4 addendum — finding 2" above), appended at
the end of their constructor lists so the T2 rules keep their recursor
positions.  The record below is the finding as raised, kept because its
case-by-case verification of the stuck block is what batch (d) writes
straight through.

Two accepting paths of the checker have **no rule to bridge to** — this
is an incompleteness of the premise-exact inventory, not an unsoundness,
and it is independent of Finding 1's repair choice.

* **`Red` has no `projArg`.**  `whnfCoreBody`'s `.proj` clause
  (`Core.lean:1431-1475`) reduces its scrutinee with `whnf` (and expands
  a string literal) *before* consulting the projection table, and
  **every** non-firing branch returns `pure (.proj sn i e')` — the
  reduced scrutinee under the projection.  That is the common case (a
  stuck scrutinee, a non-native entry, a failed `projCert`).  So the
  bridge owes `Red μ Δ (.proj i ⟦pe⟧) (.proj i ⟦e'⟧)` from
  `Red μ Δ ⟦pe⟧ ⟦e'⟧`, and no constructor concludes it: of `Red`'s
  fourteen, only `refl`, `trans` and `projRed` can conclude at a `.proj`
  subject, and `projRed`'s conclusion is the selected *field*, never a
  projection.  Missing rule:
  `| projArg {Δ i p p'} : Red μ Δ p p' → Red μ Δ (.proj i p) (.proj i p')`.
* **`DefEq` has no `projCong`.**  `defeqStep`'s stuck block
  (`Core.lean:1884-1889`) compares `.proj s₁ i₁ e₁` with
  `.proj s₂ i₂ e₂` by `i₁ == i₂` plus `r.defeq e₁ e₂`, and returns
  `true`.  The bridge owes `DefEq μ Δ (.proj i v₁) (.proj i v₂)` from
  `DefEq μ Δ v₁ v₂`; none of D1–D14 concludes it (`appCong` is about
  `mkAppN`, and the eta/unit rules are shape-pinned).  Missing rule:
  `| projCong {Δ i a b} : DefEq μ Δ a b → DefEq μ Δ (.proj i a) (.proj i b)`.

Both are **trivially sound** — `interp (.proj i v)` is `sfst`/`ssnd` of
`interp v`, so each case is a `congrArg` on the premise's equation, and
`AnnotOkV` of both sides is already a hypothesis of `DefEq`-soundness
(for `Red`-soundness, `AnnotOkV (.proj i p')` follows from the reduct's
own `AnnotOkV` conjunct plus the subject's `i < 2`).  Both are pure
*additions* to the mutual block, so the cost is two more cases in
`Weaken.lean`'s 42-case recursor application (mechanical: the `.proj`
lift commutation is already there for `Infer.proj`) and two more in
T4's soundness induction.

Consequence for the batches (as raised; now unblocked): `ProjStepR`
(batch e) cannot be discharged
without `Red.projArg`, and `DefEqStuckStepR` cannot be discharged even
in its congruence-only portion without `DefEq.projCong` — the `.proj` /
`.proj` case sits in the same match as `.forallE`/`.lam`/`.app`, so the
clause cannot be split around it at a legitimate boundary (a case
restriction on the *input space* would have to name the stuck block's
own configuration, which is what `DefEqStuckStepR` already is).  The
congruence portion is therefore held until the two rules land with the
Finding 1 repair, rather than being split at a fabricated boundary.

For the record, what the congruence portion *is* — verified by reading
each case against its rule, and blocked only by the two above:
`sort`/`sort` (D1, via `Level.isEquiv_sound`), `lit`/`lit` (D1),
the two `lit (.natVal 0)`/`Nat.zero` pairs (D1 — `natLitV … 0` is the
`Nat.zero` valuation), `fvar`/`fvar` at equal index (D1),
`const`/`const` under `isEquivList` (D1, via `EnvR.val_params`), the two
`lit (.natVal (k+1))`/`Nat.succ`-application pairs (D14 + D2 — and the
`natLitSupported` side condition comes for free from the subject's own
`denote` fact), `forallE`/`forallE` (D5, through `CtxOkR.openCong`),
`lam`/`lam` (D6, likewise), `app`/`app` (D7, through `defEqList`'s
inversion and a `DefEqL` list induction).  The two string-literal
expansion cases need `denoteClosed … (strLitToConstructor s)` — R7's own
side condition — which is content the `Setlec/Verify/StrLitExpr.lean`
tier should supply; the one-sided λ cases are D13 and so are held by
Finding 1.

## T3 — batches (a-rest) + (b) + the spine part of (d), against the settled shapes

Repair A is transparent to everything T3 had already landed: batch (a)
and batch (f) rebuilt **with no edit to any `Bridge/*` file** (verified
by pre-flight against T4's amendment before it landed, and again after
the merge).  The reason is worth one line, because it is the criterion
for judging any future rule reshape: the bridge only ever *applies*
`Red.{refl,trans,appFn,beta,zeta,natSucc,natOp1,natOp2}`,
`Infer.{sort,bvar,const,litNat,litStr}` and
`DefEq.{refl,symm,trans,ofRed}` in those batches — `Red.beta`'s premise
pair was already infer+defeq, and R8–R10 have no `Infer` premise at all.
A reshape of a *premise* is invisible to a clause that does not
construct that rule.

### Landed

| file | content |
|---|---|
| `Bridge/InferStruct.lean` | `inferShapeR` / `inferSortR` (**the repair's whole bridge-side content**), `frame_openR`, and I6/I7/I8/I10 — `InferPiStepR`, `InferLamStepR`, `InferAppStepR`, `InferLetStepR` all discharged |
| `Bridge/Spine.lean` | `denote_const_congrR`, `defEqL_of_defEqListR`, `frame_spineR`, and `DefEqSpineStepR` discharged (D7's second entry point) |

`inferShapeR` is the measurement of repair A on this side: *one* lemma,
six lines, used four times here and at every `Infer`+shape site of the
remaining batches.  The slack composes with the reduction claim through
`DefEq.ofRed`, which is precisely what the repair made possible.

One more V-free relocation, verbatim: `substFn_of_evalEqList` from
`TTVerify/DefEqStep.lean` to `Setlec/Verify/Level.lean` (a statement
about levels alone; both lanes' same-head spine short-circuits need it).

### FINDING 3 — RESOLVED 2026-08-28 (T4 amendment, third increment): the *doubled*-`Infer` premise chains do not compose either

Repair A converted the `Red`-at-an-inferred-type premises.  It did not
touch a second, smaller family that has the same defect for the same
reason — flagged parenthetically in Finding 1's list ("D8 ×2, doubled
`Infer`"; "R6 ×2, doubled `Infer`") and now hit head-on at batch (c).

*The shape.*  Two rules chain `Infer` premises so that the **subject**
of the second is the **type** produced by the first:

```
    D8 irrelProp : Infer Δ a ta → Infer Δ ta sta → DefEq Δ sta (.sort 0) → …
    R6 projRed   : Infer Δ fv ta → Infer Δ ta tta → DefEq Δ tta (.sort _) → …
                   Infer Δ P  te → Infer Δ te tte → DefEq Δ tte (.sort _) → …
```

The checker's corresponding moves are `ta ← infer a; sta ← infer ta`,
so the bridge gets `Infer Δ ⟦a⟧ T₁` with `DefEq Δ T₁ ⟦ta⟧` from the
first, and `Infer Δ ⟦ta⟧ T₂` with `DefEq Δ T₂ (.sort 0)` from the
second — an `Infer` **at `⟦ta⟧`**, not at `T₁`.  The rule wants both at
one `ta`, and the slack sits between them exactly as before.

Mechanized at `proofIrrel`'s `Prop` branch: the clause elaborates up to
the residual goal

```
    ∃ TA SA, Infer Δ va TA ∧ Infer Δ TA SA ∧ DefEq Δ SA (.sort 0)
```

from `hI1 : Infer Δ va T₁`, `hD1 : DefEq Δ T₁ vta`,
`hI2 : Infer Δ vta T₂`, `hD2 : DefEq Δ T₂ (.sort 0)` — unreachable.
The **one-linking-`DefEq`** version of the same goal,

```
    ∃ TA TA' SA, Infer Δ va TA ∧ DefEq Δ TA TA' ∧
                 Infer Δ TA' SA ∧ DefEq Δ SA (.sort 0)
```

is `⟨T₁, vta, T₂, hI1, hD1, hI2, hD2⟩` — one line.  Both elaborated
against the landed tier before this note was written.

*Repair (proposed): insert the linking `DefEq`*, i.e. exactly repair A's
move one premise earlier —

```
    D8 : Infer Δ a ta → DefEq Δ ta ta' → Infer Δ ta' sta →
         DefEq Δ sta (.sort 0) → …           (and the same for b)
    R6 : Infer Δ fv ta → DefEq Δ ta ta' → Infer Δ ta' tta → …  (×2)
```

**Soundness is free under T4's settled architecture**, and strictly
cheaper than repair A was: `DefEq`-sound is *unconditional*
(no `AnnotOkV` on either side), so the linking premise contributes only
`⟦ta⟧ = ⟦ta'⟧`, and D8's chain becomes
`⟦a⟧ ∈ ⟦ta⟧ = ⟦ta'⟧ ∈ ⟦sta⟧ = univ 0`, closed by `mem_univ_zero`
exactly as `sortCert_pt` does today (`Model/Core/Claims.lean:225-262` —
the model's own proof already threads the equality rather than an
identity).  R6's two chains are the same statement at the field and at
the subject.  No `AnnotOkV`, no new premise beyond the equation.

*Scope.*  Four premise pairs in two rules.  Blocked until it lands:
`ProofIrrelStepR` (batch c) and `ProjStepR` (batch e, via R6) directly;
`DefEqStuckStepR` (batch d) because `stuckIrrel`'s cascade ends in
`proofIrrel`; and `IotaStepR` (batch g) because R12/R14's
proof-irrelevance premise is built through D8/D9.  Everything else in
those batches is unaffected — D9, D10, D11, D12, D13, R11 and R13 all
have single `Infer`+`DefEq` pairs and compose today.

### T4 amendment, third increment — finding 3 applied (linking `DefEq` in the doubled-`Infer` chains)

Applied as proposed, T4 owning the shapes: the four premise pairs —
D8 `irrelProp`'s two chains (`ta`/`tb` sides) and R6 `projRed`'s two
(field and subject) — each gained the linking `DefEq` (`ta ↝ ta'`,
`tb ↝ tb'`, `te ↝ te'`), with the second `Infer` re-subjected at the
primed variable.  `Weaken.lean`'s two cases re-signed (two/two new
`DeqW` IH slots); the soundness cost was exactly as priced —
**free under the T4 architecture**: `DefEq`-sound being unconditional,
the linking premise contributes only the equality, and the chains
close by `mem_univ_zero` threaded through it (`sndDeqIrrelProp`,
`sndRedProjRed`'s collapse branch) — the same equality-not-identity
threading as the model's `sortCert_pt`.

**The sweep, recorded** (so the two findings' pattern cannot produce a
finding 4 of the same shape): every `Infer` premise of `Rel.lean` and
`Decl.lean` was enumerated and its subject classified.  After this
amendment the only `Infer` premises whose subject is another premise's
*produced type* are the four primed-and-linked ones; every other
subject is a rule component (subject/argument/binder-body/fabrication
spine) or a declaration front door's denoted stored object.  The
extended-context premises (I6's `B`, I7's `b`) have binder-body
subjects.  No further doubled chains exist.

## T5 — the install layer (in progress; stages a1–a3 landed)

### Inventory (as landed so far)

| file | content |
|---|---|
| `Setlec/Verify/Denote/Install.lean` | **relocated** (T1/T3 precedent, statements unchanged, namespace kept): the V-free install-transport core of `TTVerify/Extend.lean` — `EnvExtends`/`denote_mono`, `denote_cval_congr`, `LitAgree`, `denote_env_shrink`/`denote_install`, the guard monotonicity family, `Installs`, `BasisPinnedTT.cons`, `ProjOkT.cons`, `divModNames_agree` — plus `cvalAt` (from `DeclValue.lean`) and `cvalWith` (from `DeclAxiom.lean`) |
| `Setlec/Verify/Denote/SubstConst.lean` | **relocated + generalized**: `shallowE`, `denote_substConst0` over a bare valuation + closedness (the generalization the original's docstring predicted) |
| `EnvS.lean` | `EnvS` (the invariant; `EnvTT` transposed with membership-form semantic fields — module docstring has the row-by-row table), `.empty`, `EnvS.toHyp` (discharges T4's frozen `EnvSHyp` by projection; the `mem_type` crossing via `denote_instLevels`), `EqLawV`/`ReduceOpsV` (+ `.empty` laws), the declaration-level consequences |
| `Install/Cons.lean` | the per-field `.cons` transports (`EqLawV`, `ReduceOpsV`, `NatOpsV`, `DivModV`, `CapsOkV`, `RecRulesV`; `mem_type`/`defn_eq`/`thm_ok` movers) + the assembler `EnvS.cons` (transpose of `EnvTT.cons` minus `ctor_residual`) |
| `Install/Value.lean` | `typeFrontS`/`valueKeyS` (the front doors through T4's soundness at `Sat`-trivial `[]`), `extendValueS`, the `DivModPinS`/`ReducePinS` obligations |
| `Install/ValueKinds.lean` | `declThmS` (complete), `declOpaqueS` (mod `ReducePinS` — now discharged), `declDefnS` (mod `DivModPinS`; the structural-`Nat` pack discharged **inline**: `NatEqsR` already carries the substituted equations' denotations, so the derivation is `denote_substConst0` + `DefEq.sound` at a two-entry `Sat`) |
| `Install/Axiom.lean` | `extendAxiomS`, `StdAxiomKeyS`/`OfReduceKeyS` obligations, `trustCompilerKeyS` (discharged), `declAxiomS` |
| `Install/ReducePin.lean` | `reducePinS` — the compiler-trust identity from the certificate through the unconditional `DefEq.sound` at a one-entry `Sat` |

### Decisions/deviations so far

* **`proj_rules` absorbed into `rec_rules`** (design §2 listed it as a
  separate field): the projection functions are stored *recursors*
  (`ProjFnR` installs `.recInfo` entries), R11 is their only [set]
  consumer, and `RecRulesV` is keyed on every stored `recInfo` — a
  separate field would state the same law twice.
* `EnvS` quantifies `φ` (the fields hold at every assignment);
  `EnvSHyp` fixes one — `EnvS.toHyp` instantiates.  The `mem_type`
  field keeps `EnvTT.has_type`'s keying (membership at each `φ`,
  uninstantiated stored type); the projection to `EnvSHyp.mem_type`'s
  I3-keyed instantiated form crosses via `denote_instLevels`.
* The [set] transports are lighter than their TT twins exactly as the
  design predicts: `interp`/`AnnotOkV`/`TeleFitV`/`IotaIndexPinV`
  components are env-free and pass through untouched; only `denote`
  facts move and `cval` occurrences rewrite.

### DECISION (T5, 2026-08-28) — D6 refinement: the positive-depth walk packs go to bridge-shaped quantified contexts

The first consumer of `IotaWalksR`/`IotaThmR`/`IotaSidesTyR` (the
plain bottom's `Sat`-construction) cannot fire them as pinned:
building `Sat Δm (value chain)` needs, at each telescope step, the
domain walk's interp-equality — whose `DefEq.sound` reading demands a
**full** `Sat Δm`, circularly.  The TT lane's padding trick
(`IndBottom.lean`: untouched inner slots are `.sort 0`, instantiated
with `dummyPropT`) transposes exactly — `pt ∈ˢ univ 0` makes `.sort 0`
slots `Sat`-free — but only if the walk derivations are available *at
padded contexts*, which the `OpenCtxR`-pinned form cannot supply while
the bridge's claims (`∀ Δ, CtxOkR … → DefEq …`) can: `CtxOkR`
constrains only the leaves the subject touches, so one checker run
yields the derivation at every padded context.  Therefore the
positive-depth packs are refined (D6's reserved refinement, exercised
by their first consumer) from pinned `OpenCtxR` contexts to the
bridge's own quantified form: each certified comparison carries
`∀ Δ, CtxOkR … lhs → CtxOkR … rhs → DefEq μ Δ ⟦lhs⟧ ⟦rhs⟧` (and
`TypedListW`/`IotaSidesTyR` likewise).  This is **not** the vacuity
trap D6 warns about — that was existentially quantified contexts; the
universal form is precisely what the bridge proves.  `DivModCertR`'s
pinned `[Nat, Nat, H1, H2]` context stays (its subjects touch every
slot; no padding is ever needed).  Bridge cost: nil (the claims are
already `∀ Δ`-shaped).  Consumer cost: a `CtxOkR`-construction lemma
at the padded pinned contexts (the `ctxOk_of_openers` transpose).
## T3 — batch (c) and the first two thirds of batch (d)

Finding 3's amendment landed and the affected clauses went through
without incident.  What this pass added:

| file | content |
|---|---|
| `Bridge/Irrel.lean` | `unitLike_denote` and **`ProofIrrelStepR` proved** — D9's unit branch and D8's `Prop` branch |
| `Bridge/Certs.lean` | `DenoteSpine.det`, **`certs_teleR`** (the `iotaCerts` → `Tele` walk), `denote_declTypeR`, `frame_declTypeR` |
| `Bridge/StuckIrrel.lean` | `PairEtaCertStepR` / `StructEtaCertStepR` obligations, **`StructUnitCertStepR` proved** (D11), and **`stuckIrrel_stepR`** — the cascade's dispatch |
| `Bridge/Eta.lean` | **`EtaCertStepR` proved** (D13) |
| `Bridge/StrLitR.lean` | `denote_strLitCtorR`, `frame_strLitCtorR` — R7's two side conditions, at any depth |

Three observations worth keeping.

**`certs_teleR` is the one consumer of the inference claim that needs
no conversion at all.**  `Tele.cons` is `Infer Δ a ta → DefEq Δ ta A →
…` and `iotaCerts`'s step is `infer arg` then `defeq ta dom` — the same
pair in the same order — so each step is two induction hypotheses and
the constructor, with no `inferShapeR` in between.  Everywhere else the
slack has to be composed; here the rule was already shaped to take it.
That is the two-pack discipline at its sharpest, and `certs_teleR` is
reused by D10, D11, R6, R11 and R12–R14.

**D13 measures premise-exactness against the TT lane directly.**  The
TT lane's `etaCert_stepTT` has to *retype* `b` at the λ's domain
(`congrPi`) before `HasType.eta` fires, then compose with `congrLam`;
here the rule names the domain mismatch as its own premise
(`DefEq Δ A₂ A₁`), so the clause is four bridge moves and one
constructor.  The retyping happens once, in the rule, instead of once
per use.

**One more V-free relocation, and this one was forced by three
consumers at once.**  `denote_strLitToConstructor`'s chain (the six
shape lemmas, `denote_nilTerm`/`denote_consTerm`/`denote_strLitList`,
plus `substFn_nil` and `denote_const_nolevels`) was stranded in
`TTVerify/{StrLitStep,NatOpsStep}.lean` behind an `EnvTT` argument it
never used beyond level insensitivity.  Relocated to
`Setlec/Verify/Denote/StrLit.lean` and **generalized from `EnvTT` to
`ValParams`**; the `EnvTT`-shaped statements stay where their consumers
are, each now one line over the generalized form, so there is exactly
one proof.  `denote_const_nolevels`'s 45 call sites and `substFn_nil`'s
are untouched (same name, same signature, same namespace).

### Outstanding after this pass

| obligation | batch | what it needs |
|---|---|---|
| `DefEqStuckStepR` | d | the seventeen-case match itself.  Every case's rule is verified in the finding-2 record above (and `.proj`/`.proj` now has `DefEq.projCong`); the two string cases now have their side conditions from `Bridge/StrLitR.lean`, the two binder cases fire `CtxOkR.openCong`, the two one-sided-λ cases call `etaCert_stepR`, and every fallthrough calls `stuckIrrel_stepR` |
| `PairEtaCertStepR` | d | D12, from `pairEtaCert_inv` (its `mode.ttChecks` conjunct vacuous) |
| `StructEtaCertStepR` | d | D10, from `structEtaCert_inv` / `structEtaCertWith_inv` + `structEtaProjCerts_inv`, through `certs_teleR` |
| `ProjStepR`, `InferProjStepR` | e | R6 (with T4's `Tele` premise) and I9 |
| `IotaStepR` | g | R11 + the R12–R14 rescues |

## T3 — batch (d) closed: the whole defeq quarter stands

`DefEqClaimsR` at `fuel + 1` now has **no outstanding step**
(`defeq_claimsR_full`), and so does `WhnfClaimsR`
(`whnf_claimsR_closed`, batch f).  What is left of `CheckStepR` is the
projection clauses (batch e) and the iota clause (batch g).

| file | content |
|---|---|
| `Bridge/Stuck.lean` | **`DefEqStuckStepR` proved** — the seventeen-case match, `split at h` in the checker's own order |
| `Bridge/EtaCerts.lean` | `DenoteSpine.map_list`, `choose_fun`, **`StructEtaCertStepR` (D10)** and **`PairEtaCertStepR` (D12)** proved |
| `Bridge/DefEqClosed.lean` | `stuckIrrel_stepR_closed`, `defeq_claimsR_full` |

Four notes worth keeping.

**`split at h` delivers the stuck block's seventeen cases in the
checker's source order.**  That is not luck: the block is one `match`
on `(a', b')`, so its compiled decision tree *is* the case list, and the
bridge's dispatch is the checker's dispatch with the rule names filled
in.  The DESIGN record of finding 2 (written before the rules existed)
predicted each case's rule; all seventeen landed on the predicted rule.

**Cases 7–8 need no reduction rule at all.**  The checker expands the
string literal and compares `strLitToConstructor st` against the other
side; `denote_strLitCtorR` says that expression denotes to *the same
`VExpr`* as the literal, so the recursive verdict already **is** the
equation wanted.  R7 is not invoked here — it is invoked at the `.proj`
and iota-major sites, where the *reduct* is what moves.  Cases 3–4 are
`DefEq.refl` for the same kind of reason (`natLitV cval φ 0` is
literally the `Nat.zero` valuation).

**`CtxOkR.openCong` has exactly two consumers**, cases 11 and 12, and
they are why the slack design exists.  `binder_congrR` factors them:
they differ only in the `denote` clause and the congruence rule.

**D10 is the campaign's first use of choice, and it is bookkeeping.**
`structEtaProjCerts_inv` gives one existential per field index while the
rule quantifies six *functions* of the index; `choose_fun` (one
`Classical.choose` per index) closes the gap.  No content passes through
it — the per-field facts are the same ones the inversion returns.  The
one genuinely new lemma is `DenoteSpine.map_list`: the field comparands
are a `List.range cnF |>.map`, `projSpinesV` is the same map on the
`VExpr` side, so the spine denotes pointwise.

Both eta certificates discard a `mode.ttChecks = true →` conjunct
(#130's `projParamCert` in D12, #137's constructor telescope in D10) —
premise-exactness, visible as a `-` in the `obtain` pattern.

### T3 — the owed R6 `Tele`-walk verification: **T4's claim holds**

T4's second amendment exposed R6's constructor-spine telescope as a
premise, arguing "the bridge cost is the inversion walk the model
already performs at `Model/Core/Whnf.lean:639-741`".  Checked at the
clause, against the set-mode inversions:

* **The walk is not `certs_teleR`'s.**  `whnf_proj_inv` delivers
  `projTeleCertP` (task #126) only under `mode.ttChecks = true`, so at
  `--set-model` there is *no* `iotaCerts` run on the constructor spine.
  Anyone reaching for `certs_teleR` here will find nothing to invert —
  worth stating, because that is the obvious first move.
* **It is the `projCert` infer run's walk, and it is available.**
  `projCert_inv` returns `inferTypeCore … e₃ = .ok te` on the
  *constructor application*, and `inferTypeCore_app_inv` peels it one
  argument at a time, each step yielding `infer arg = ta` plus
  `defeq ta dom` — which is exactly `Tele.cons`'s premise pair, in the
  checker's own order.  This is precisely what the model does: the
  cited range walks four `inferTypeCore_app_inv'` steps down the pinned
  `PSigma'.mk` type, computing the four domains concretely
  (`Sort u`, `α → Sort v`, `α`, `β a`) and using `whnf_forallE_eq` to
  say the `whnf` of a concrete `∀` is itself.
* **The alignment step is the one real cost**, and T4 named it: the
  infer walk's domains come from `whnf` of the partial application's
  inferred type, while `Tele` peels the *stored* type syntactically.
  They agree because the entry is pinned (`ProjOkT`) and the pinned
  constructor's stored type is a literal `∀`-tower, on which `whnf` is
  the identity.  So the alignment is a computation, as claimed — but it
  is a computation that needs the pin.

**Consequence for `EnvR` (interface note for T5/T6).**  The bridge's
R6 clause therefore needs `ProjOkT env`, which `EnvR` does not yet
carry — `EnvSHyp` gained `proj_ok` for the same reason on the soundness
side.  It will be added with its first consumer (batch e), not before;
T5's `EnvS → EnvR` adapter should expect one more V-free field, already
present in `EnvS`.

No finding: the claim is verified as stated, with the two caveats above
recorded so batch (e) does not start down the `certs_teleR` path.

## T3 — batch (e), first half: I9 lands; R6's remaining shape

`Bridge/Proj.lean`: **`InferProjStepR` proved** (I9), together with
three pieces the rest of (e) and (g) reuse —
`denote_piResidualR` (`denote` commutes with `piResidual`),
`denote_closedExprR` (a *pinned* closed expression's denotation is
depth-independent and closed, where `EnvR.wf` does not apply because
the expression is not a stored declaration's type), and
`denote_entryTyR` (the pinned entry's type, denoted, with its
closedness).

`Setlec/SetR/ProjPins.lean` is new: `projEntry_pins`,
`denote_pairFstTy_eq`, `denote_pairSndTy_eq`, `denote_psigmaMkTy_eq`
and the two `piResidualV` walks, **relocated verbatim** out of
`Setlec/SetR/Sound/Proj.lean`.  The soundness tier built them first and
the bridge needs exactly the same facts; they are V-free (`denote`,
`Env.find?`, `ProjOkT`), so they sit below both tiers with one proof.
`EnvR` gained `proj_ok : ProjOkT env` with this, its first consumer —
the interface note from the R6 verification, now cashed.

**`denote_piResidualR` is the `.proj` analogue of `certs_teleR`**: like
it, it needed no conversion, because the rule was already shaped to
take what the checker computes.  Two rules out of the family have that
property and both are the ones whose premises were transposed from a
*walk* rather than from a single certificate — worth noting as the
shape to aim for when a rule is designed.

### What R6 still needs (the walk, made precise)

The verification above established that R6's `Tele TC vs restC` comes
from inverting the `inferTypeCore e₃` run that `projCert` performs.
Writing it needs three things, in this order:

1. **Three fuel-lifted inversions relocated.**  `whnf_forallE_eq`,
   `inferTypeCore_app_inv'` and `inferTypeCore_const_inv` are `private`
   in `Setlec/Model/Core/Whnf.lean:27-70`.  All three are V-free and
   general (they are `*_mono`-lifted forms of existing inversions), and
   the model's own comment calls them "fuel-lifted inversions for the
   certificate walk of the native pair projection" — i.e. exactly this
   walk.  They belong in `Setlec/Verify/InferLemmas.lean`.
2. **The four-step concrete walk.**  `inferTypeCore_app_inv'` peels the
   constructor application one argument at a time; at each step
   `whnf_forallE_eq` says the whnf of the pinned type's `∀` is itself,
   which is what aligns the walk's domains with `Tele`'s syntactic
   peeling of `TC` (`denote_psigmaMkTy_eq`'s concrete form).  Each step
   then yields `Infer Δ ⟦arg⟧ ⟦ta⟧` and `DefEq Δ ⟦ta⟧ A` — `Tele.cons`.
3. **The scrutinee reduction**, which is where `Red.projArg` (finding
   2's rule) and R7 fire: `whnf_proj_inv` reduces the scrutinee with
   `whnf` and expands a string literal with `projLitToCtor`
   (`projLitToCtorP_inv` + `denote_strLitCtorR`), and *every non-firing
   branch* returns `.proj sn i e'` — the case `Red.projArg` exists for.

Batch (g)'s R11 additionally reuses (1) and `certs_teleR`; its rescues
R12–R14 reuse `denote_declTypeR`, `certs_teleR` and the D8/D9 and D10
certificates already proved.

## T3 — batch (e) closed: `ProjStepR` and `InferProjStepR` both proved

`Bridge/ProjRed.lean` discharges R6, the scrutinee's reduction (R7 at
the `.proj` site) and the stuck branch.  `CheckStepR`'s only remaining
obligation is `IotaStepR` (batch g).

**The stuck branch is `Red.projArg`'s reason to exist.**  Finding 2
predicted it from reading the clause; here it fires: *every* non-firing
branch of `whnfCoreBody`'s `.proj` clause returns the reduced scrutinee
under the projection, and no other rule concludes at a `.proj` subject
whose scrutinee moved.

**The walk is general, not concrete — and that was the right call.**
The model performs R6's constructor-spine walk *concretely*: four
`inferTypeCore_app_inv'` steps down the pinned `PSigma'.mk` type with
each domain computed by hand (`Model/Core/Whnf.lean:560-741`).  The
bridge does it once, generically, in `tele_of_inferSpineR`:

* `inferTypeCore_app_inv'` peels one argument at a time, right to left
  (the way an application chain is built), each step yielding
  `infer arg` and `defeq ta dom` — `Tele.cons`'s pair, in the checker's
  order;
* the alignment between the walk's `whnf`'d domains and `Tele`'s
  *syntactic* peeling is `whnf_forallE_self`: **a `∀`-tower is its own
  whnf**.  The tower witness is `stripPis` — which the checker's own
  installs already pin, and which survives instantiation
  (`stripPis_instantiate1`), so the invariant carries down the walk;
* `Tele.snoc` reassembles, since the peeling runs right to left while
  `Tele` is built left to right.

Cost: about the same as the concrete version at this one site.  Payoff:
batch (g)'s R11 recursor and constructor telescopes are *the same walk
at a different arity*, and neither of those types is pinned — so the
concrete route would not have transferred at all.  Recording it as the
general lesson: **when a rule's premise is a telescope, prove the walk
from the `stripPis` witness the checker already pins, not from the
shape of whichever type happens to be at hand.**

### What batch (g) needs, and one risk to settle first

`IotaStepR` is `CheckStepR`'s last obligation.  `iotaRec_inv` is
comprehensive — it returns every side condition R11 names — and the
reusable machinery is in place: `certs_teleR` for the two `iotaCerts`
telescopes, `tele_of_inferSpineR` for anything the walk reaches,
`denote_declTypeR` for the stored types, `defEqL_of_defEqListR` for the
comparand lists, `denote_strLitCtorR` for R16 at the major, and D8/D9
(`proofIrrel_stepR`) and D10 (`structEtaCert_stepR`) for the R12–R14
rescues through `majorToCtor_inv`.  Two things are *not* in place:

**1. A new `EnvR` field: the rule's right-hand side denotes.**  R11
carries `denoteClosed cval env φ (rl.rhs.instantiateLevelParams …) =
some R` (+ D1 closedness).  `EnvR.ty_denotes` covers stored *types*
only, and `EnvWF` gives the rhs's `hasFvar = false`, `constsResolve`
and `looseBVarsBounded 0` but **not** its denotability (`constsResolve`
gives existence, not the level-arity matches `denote`'s `.const` clause
needs).  `EnvS.rec_rules` carries exactly this fact, so the field is
`EnvS`-backed like `proj_ok`; add it with its consumer.

**2. RISK — `rP ≤ mI` may not be suppliable for `.plain` fires.**
R11 states `rP ≤ mI` as an unconditional side condition (deviation D3),
recorded as "supplier: `EnvWF`".  Reading `Setlec/Verify/EnvWF.lean:57`,
`EnvWF` concludes `rP ≤ mI` **only inside the `.nested` branch**
(`∀ lvls pins, fire r = .nested lvls pins → rP ≤ mI ∧ …`); nothing in
the `.plain` case relates the two, and `iotaRec` does not check it
per-fire.  D3's own justification is M1's nested-premise chain arity, so
the condition is only *needed* where it is *available*.  Two resolutions,
to settle before writing the clause rather than during:

* move `rP ≤ mI` inside R11's nested premise (where M1 uses it), leaving
  `.plain` fires unencumbered — the smaller change, and it matches the
  reason the condition exists; or
* have the install layer establish it unconditionally and expose it
  (an `EnvR`/`EnvS` field), if some consumer needs it for `.plain` too.

The first looks right on the evidence, but it is a rule-shape change and
therefore T4's call, not the bridge's.

### T4 amendment, fourth increment — D3's `rP ≤ mI` guarded on `.nested` fires

T3's pre-iota risk record was right and the ruling adopted its
resolution: `EnvWF` concludes `rP ≤ mI` only in the `.nested` branch
(`Verify/EnvWF.lean:57`), `iotaRec` never checks it per-fire, and D3's
own justification (M1's pin-chain arity) needs it only there — so
R11's side condition became `∀ lvls pins, rl.fire = .nested lvls pins
→ rP ≤ mI` (same premise slot; `wkRedIota` consumes it inside its
nested case, where the `instRevChain` lift lives).

**The coordinator's verification question, answered**: yes,
`sndRedIota`'s equality consumes `rP ≤ mI` *unconditionally* — the
reduct-spine alignment `(xs.take mI).take rP = xs.take rP` (the
`take_take` step) is fire-kind-independent — so the plain branch does
need the fact, and it takes the flagged alternative route: it is
already an **install-layer fact**, `RecRulesV`'s first conclusion
(`rP ≤ mI ∧ …`, mirroring `RecRulesTT`, whose TT-lane install
derivation proves it for plain rules from the provisioning shape
pins).  `sndRedIota` now reads it off `henv.rec_rules` instead of the
rule; the rule's premise stays exactly what the bridge can discharge.

## T3 — batch (g) part 1: the rescues land; R11's recipe

`Bridge/Major.lean` discharges `MajorStepR` — R12 (K), R13 (structural
eta), R14 (the 0-field fallthrough) and the identity.  These are
amendment-independent, so they landed ahead of R11.

**`majorToCtor_inv` carries the fabrication's frame conditions with
it** (`wscopedB`, the loose-bvar bound, the leaf-subset fact), so the
clause needs no scope bookkeeping of its own — the checker's guards were
recorded by the inversion.  That is the first clause in the bridge where
that happens, and it is worth noting as a property of well-written
inversions: an inversion that returns the *frames* as well as the
certificates saves its consumer a page.

R13 is what `structEtaCertWith_stepR` was factored out for: the
certificate is already stated at the `tmaj` `majorToCtor` computed, so
the wrapper's own reduction must not be redone.

### R11, fully specified

T4's D3 amendment landed (`rP ≤ mI` guarded on `.nested`), so the shape
is frozen.  Everything R11 needs is now available; recording the map so
the clause is a transcription:

| premise | source |
|---|---|
| the recursor/rule/constructor lookups, lengths, `stripPis` | `iotaRec_inv`, directly |
| the level guard at `[]` | `iotaRec_inv`'s guard at `e.getAppArgs`, plus `(recFireComparands … args rP).1 = (… [] rP).1` — the `.1` component reads no arguments in *either* fire branch (`Core.lean:1241-1251`), so this is `cases rl.fire <;> rfl` |
| `TV`, `TVj` denote (+ D1 closedness) | `denote_declTypeR` |
| `R` denotes (+ closedness) | `EnvR.rec_rhs_denotes` + `denote_closedExprR` |
| premises 1–2 (major whnf, rescue) | `WhnfClaimsR` + `litMajorToCtorP_inv`/`denote_strLitCtorR` (R16) + `MajorStepR` |
| premise 3 `.plain` | `defEqL_of_defEqListR`; `recFireComparands`'s `.2` is `args.take ctorParams` in that branch |
| premise 3' `.nested` | `denote_openRev` — `recFireComparands`'s `.2` is `pins.map (Expr.instSpine (args.take rP) (rP-1) ∘ …)`, which is exactly that lemma's `instSeq`-at-`as.length-1` shape, with `as := args.take rP` |
| premises 4–5 (the two telescopes) | `certs_teleR` |
| premise 6 (the index decomposition) | `denote_piResidualR` identifies the `Tele` residual with `⟦residual⟧`, `denote_mkAppN_inv` splits it into `H`/`cargs`, and `DefEqL.length_eq` gives the length disjunct |

**One more `EnvR` field is needed, and it is the D3 amendment's mirror
image.**  Premise 6's disjunct `mI = rP ∨ cargs.length = ctorParams +
(mI - rP)` follows from `DefEqL.length_eq` *except* when `mI < rP` on a
`.plain` fire — the exact case the amendment removed from the rule's
premises.  T4's verification found the same thing on the soundness side
and answered it from `henv.rec_rules`' first component (the install
layer carries the unconditional `rP ≤ mI`).  The bridge needs the same
fact from the same place: `EnvR.rec_params_le`, backed by the identical
`EnvS` component.  This is not a new finding — it is the *other half* of
the D3 split, and it lands with R11.

## T3 — **`CheckStepR` is closed**: the bridge half is done

`Bridge/Main.lean`: **`checkStepR : CheckStepR mode`** with no
outstanding obligation, and `checkBridge` — the four claims at every
fuel.  A successful `--set-model` checker run yields a derivation of the
relation family.

| quarter | closed by | batch |
|---|---|---|
| `WhnfCoreClaimsR` | `whnfCore_claimsR` + `iota_stepR` + `proj_stepR` | a/b, e, g |
| `WhnfClaimsR` | `whnf_claimsR_closed` | f |
| `DefEqClaimsR` | `defeq_claimsR_full` | a, c, d |
| `InferClaimsR` | `infer_claimsR` + the five structural clauses + `inferProj_stepR` | a, b, e |

`Bridge/Step.lean` is deleted: `StepObligationsR` recorded ten named
obligations and all ten are discharged, so keeping it would name work
that no longer exists.

**What the bridge is conditional on is exactly `EnvR`** — nine V-free
environment facts, every one either a field of `EnvTT`/`EnvS` or an
immediate consequence.  There is no `SetTheory`, no membership and no
interpretation anywhere in the tier.  That is the factoring the campaign
was for, and it is now a fact rather than a plan.

### R11's four non-transcription points

`iotaRec_inv` returns every side condition R11 names, so the clause is
mostly transcription.  Four places are not, and each turned out to be a
small general fact rather than iota-specific work:

* **the level guard reads no arguments** — `recFireComparands`'s `.1`
  component ignores its `args` in *both* fire branches, so the rule's
  spelling at `[]` and the checker's at the real spine agree by
  `cases … <;> rfl` (`recFireComparands_fst_nil`);
* **the `Nat`-literal major conversion is invisible to the denotation**
  (`denote_litToCtorIfNat`) — design §7.2's "`litToCtorIfNat`
  contributes zero rules", discharged rather than asserted;
* **the residual is the telescope's** — the `Tele` premise's residual
  and the checker's `piResidual` are the same walk (`Tele.residual` +
  `denote_piResidualR`), so premise 6's index decomposition is
  `denote_mkAppN_inv` applied to that one shared value;
* **only one nested comparand is known to denote.**  The rule
  hypothesises exactly the `i`-th pin's opening, so the component must
  be pulled out of `defEqList` *syntactically* (`defEqListP_get`), not
  through a whole-list `DenoteSpine`.  Reaching for the list-level lemma
  first is the natural move and it fails on the `none` case — **the
  premise's shape tells you which extraction it wants**, and that is
  worth stating generally: a premise quantified at one index wants a
  pointwise inversion, not a spine one.

The nested pin bridge itself is `denote_openRev` +
`denote_openRev_base` — the checker's comparand is
`instSpine (args.take rP) (rP-1) pin` and the rule's is
`instRevChain (xs.take rP) ⟦openRev 0 rP pin⟧`, which is exactly that
identity plus its base-independence.

### Closing tally

Findings raised and resolved: three (the slack/`Red` non-composition,
the missing projection congruences, the doubled-`Infer` chains), each
mechanized in both directions — the unreachable goal *and* the repaired
variant — before being routed.  Rule amendments consumed: four (repair
A, the two congruences, D3's split), none of which required an edit to
an already-landed bridge clause.  Relocations out of misfiled homes:
six.  The two conversion-free rules remain `certs_teleR`'s and
`denote_piResidualR`'s — both transposed from *walks*.

## T5 c2 — the plain bottom, landed (2026-08-28)

`indBottomPlainS : IndBottomPlainS V` (`Install/IndBottomPlainS.lean`)
glues six sealed stages (`Install/IndStagesS.lean`):

* `zipperS` — Sat + statement fit at `zs := xs.take rP ++ ys.drop cnP`;
* `fireS` — the equation's truth through `eq_lawV` (slot-sort by
  `piC_dom_unique` graph rigidity — the #146-avoidance route, as
  designed);
* `reductS` / `pointS` — the two sides identified with the reduct and
  the fired redex (full-spine `instPisAt_denote_cross` +
  `teleFitV_rest_eq` + `IotaIndexPinV` on the index branch);
* `annotS` — the truthfulness transport.  **Decision (mirrors the
  model's `TowerOk`)**: the reduct's `AnnotOkV` app-packages come from
  the rule rhs's *own* λ-tower, read through the new
  `instLamsAt_denoteTele`; the fired spine's layer memberships
  (`annotMemS`) go Sat → statement annotation → walked recursor/ctor
  domain (`hdePre`/`hdeFld`) → renamed-equal canonical P-annotation
  (`instPisAt_renEq`, no walk) → walked rhs λ-domain (`hdeLam`) →
  lift/chain absorption (`shiftE_chainE_take`) down to the layer's own
  depth; the descent (`lamTowerStepS`) β-walks the tower with
  `lamC_mem_upair` packages.  P-frame walk subjects fire at the
  statement context through `ctxOkR_of_walked_openers`, the
  `Infer`-up-to-`DefEq` slack filled by the annotation identification
  (`annotPFrameEqS`) — no second context, no padding induction.
* **Statement amendment**: both bottoms now carry the lam-domain walk
  pack (`hdeLam`), the `instLamsAt` run, `crestP`'s field opening and
  the `stripLams` pin — present in `IotaThmR`/`IotaThmNR` all along,
  omitted from the c1 statements.

No finding-#1: every law derived from set-mode install checks.

## T5 c3 — the nested bottom, landed (2026-08-28); **risk R1 cleared**

`indBottomNestedS : IndBottomNestedS V`
(`Install/IndBottomNestedS.lean`).  The headline is that it reuses the
plain bottom's six stages *unchanged in content*: the stages were first
made **parameter-spine-generic** (one commit, no proof step lost), and
the nested fire is then an instantiation.

### The generalization (`IndStagesS.lean`, all six stages)

`zipFieldTermEq`, `zipperS`, `pointS`, `annotPFrameEqS`, `annotMemS`,
`annotS` no longer mention `fvs.take cnP` / `xs.take cnP`.  They take

| hypothesis | what it says | plain | nested |
|---|---|---|---|
| `hsplen`/`hspLeaf`/`hspScope` | the constructor run's expression spine: length, leaves among the openers below `rP + (q + 1 - cnP)`, frame-scoped | the openers `fvs.take cnP ++ fvs.drop rP` | `pins.map (instSpine (fvs.take rP) (rP-1) ∘ renameConsts f) ++ fvs.drop rP` |
| `hmixlen`/`hmixsp` | the **crossing datum**: position `q` denotes to `w0`, and the mixed value there is `instSeq zs (rP+cnF-1) w0` | `xs.take cnP ++ ys.drop cnP` | `pinWs.map (instSeq zs …) ++ ys.drop cnP` |
| `hmixFldEq`/`hmixPar`/`hmixVal` | the mixed values read as the constructor's own spine | `hpar` | `hparP` through `pinCrossS` |
| `hpsRen` | the canonical and renamed parameter spines are pointwise `RenEqT` (the annot stages) | `RenEqT.fvar` | `instSeq_renameConsts` ∘ `instSeq_erasedEq_args` |
| `hmaj`/`hctorHead` (`pointS`) | the major, **up to `ErasedEq`**, under an abstract head that denotes to the fire-site constructor valuation | `ErasedEq.rfl`, parameter-mapped head | the stored `lvls` |

`cnP ≤ rP` and the plain level-agreement premise disappear from all six
stages — they were only ever needed to *read* the plain spine.

**The lesson, stated generally**: a stage that consumes a spine should
name what it needs of it (leaves, scope, crossing) rather than the
spine's construction.  Both fires then supply the same five facts, and
the nested lane costs one lemma plus an assembly instead of a second
copy of the stages.  (The TT lane mirrored instead — `nestedMixedFit` +
`zipperStageN` + `pointStageN`, ~1 500 lines; here the delta is ~130
lines of stage signature and ~430 lines of assembly.)

### The one new fact: `pinCrossS` (`Install/IndNestedS.lean`)

```
VExpr.instSeq zs (rP + cnF - 1)
    ⟦ instSpine (fvs.take rP) (rP - 1) (pin.renameConsts f) ⟧
  = VExpr.instRevChain (xs.take rP) ⟦ openRev 0 rP pin ⟧
```

an **identity of `VExpr`s** — `denote_openRev` (real-argument
instantiation read through the reverse opening) puts the frame's own
bvar spine in front, `denote_openRev_base` moves the opened denotation
to base 0, `nestedChain` slides the reverse chain onto the fired spine,
and `denote_renameConsts` erases the rename.  Nothing interpretive
happens, so the two `interp_instRevChain*` lemmas a first attempt
reached for were **retracted**: the pointwise-agreement route is not
needed at all when the crossing is syntactic.

### RISK R1: cleared, no finding

The rule's parameter premise is quantified over the pin's **value**
(`∀ vp, denote … rP (openRev 0 rP pin) = some vp → bvarsBelow rP vp →
interp ρ (ys.getD i) = interp ρ (instRevChain (xs.take rP) vp)`) — the
design's §8.1-corrected shape.  Nothing in the derivation asks whether
a pin *fits in a clause*, so the task-#13 wall is never approached; the
value-quantified form is consumed exactly once, in `hmixPar`, against
the `vp` that `pinCrossS` produced.

**Where the pins' values come from** (the one thing the plain bottom
had for free): the statement's own pin walk `_hTypedP : TypedListW …
(pins.map (instSpine (fvsP.take rP) (rP-1))) cdomsP` — the checker's
`checkTypedList` run — denotes the *canonical* instantiations at the
recursor frame, and `denote_openRev` read backwards turns that into the
existence of `⟦openRev 0 rP pin⟧`.  Premise-exactness holds: no fact is
used that a `--set-model` run does not establish.

### The remaining nested deltas, all bookkeeping

* the constructor tower is denoted at the **stored** levels: `hlev` +
  `Level.substFn_map_subst` gives `substFn φ cvjLps usj ≐ substFn ψ'
  cvjLps lvls` on `cvj.levelParams`, and `denote_params_ext` moves the
  tower there;
* the residual arity is `instPisAt_residual_arity_const`, **not** the
  `_fvar` version — a nested run's spine is not a variable spine, which
  is exactly why `IndBottomNestedS` carries `_hCstripsHead`'s
  constant-head witness where the plain statement carries `_hCstrips`;
* the major is matched by `denote_erasedEq` (the pin form is `ErasedEq`
  to the checker's, not syntactically equal — the #105 "major pin is
  `eqUpToNames` not `==`" record, cashed here).

No finding-#1: every law derived from set-mode install checks.

### What c4/c5 need (scoped while c3 was landing, not yet started)

**c4 — the projection bottom.**  It is *not* an instantiation of the
plain/nested stages, and the reason is worth recording so nobody starts
down that path: the projection install runs a **different set of
checks**.  `checkProjIota` (`Kernel/Modeled.lean:512-553`) pins the
statement's telescope domains to the constructor's renamed ones
**syntactically** (`domsMatchAux`) instead of walking them
(`hdePre`/`hdeFld`), and the reduct is the rule λ-tower's β-contractum
(`stripLams` to `.bvar (nF-1-i)`) instead of a `DefEqAtW` walk
(`hdeRhs`).  So `zipperS`'s two inputs are unavailable and `reductS`'s
one input is unavailable; the TT lane wrote a third zipper/point pair
for exactly this reason (`IndBottomProj.lean` + `pointStageP`).  What
*does* transfer: `fireS` (generic in `zs`), `annotS`/`annotMemS` (the
lam-domain walk `checkDefEqList … ldoms` **is** run — `checkProjRule`'s
second `checkDefEqList`), and all six stages' parameter-spine
abstraction (a projection fire is `mI = rP = cnP`, so it is a *plain*
spine).

Before the proof, `ProjFnR` must be refined — this is D6's **reserved**
refinement point, and its first consumer is exactly this bottom.  The
faithful transposition, read off the checker:

| source | to add to `ProjFnR` |
|---|---|
| `checkProjShape` (`CheckerBase.lean:234`) | `(pty.stripPis nP).isSome`; `cvj.type.stripPis (nP+nF) = some (cbinders, cbody)`; `cbody.getAppArgs.length = nP`; `∃ c us, cbody.getAppFn = .const c us` |
| `checkProjRule` (`CheckerBase.lean:247`) | `Expr.pisToLams (nP+nF) cvj.type (.bvar (nF-1-i)) = some rhs` + its scoping; `rhsA`'s four wellformedness pins; `rhsA.stripLams (nP+nF) = some (rbinders, .bvar (nF-1-i))`; `domsMatchAux (fun _ e => e) rbinders cbindersR 0 0 (nP+nF)`; the two frame runs (`openPisAtFvars nP pty 0`, `instPisAt fvsP cvj.type`, `openPisAtFvars nF crestP nP`, `instLamsAt (fvsP ++ xFvs) rhsA`) and the **two** `DefEqListW`s over them; the rhs front door (`ops.inferType env' 0 rhsA`) |
| `checkProjIota` (`Modeled.lean:512`) | `tcv.type.stripPis (nP+nF) = some (sbinders, sbody)`; `domsMatchAux (renameConsts (projFwd T ctorName nF)) sbinders cbindersR 0 0 (nP+nF)`; `sbody`'s four-app `Eq` shape with `lhsC == lhsS` (the canonical model spine) and `rhsC == .bvar (nF-1-i)` |

The `IotaSlotSorted` premise the TT statement carries (`#146`) has **no**
[set] counterpart — the plain bottom's `fireS` already recovers the
slot's universe membership from the statement's own truthfulness plus
`Eq`-former graph rigidity, and the projection bottom reuses `fireS`
unchanged.

**c5 — the eta/unit laws.**  The template is the *model*'s
`modeled_caps_eta` (`Model/ModeledCaps.lean:134-…`, ~360 lines),
transposed to `denote`: consume `EtaPins` (V-free, environment-derived
— **not** a `Decl.lean` field), the `_model.eta` theorem's front doors,
and the three public/model valuation identifications (`hvT`/`hvC`/`hvP`).
No `#135/#136/#137` content enters: `EtaLawV`'s fabrication side is
unconditioned, so the law is the statement's equation read at a
`Sat`-constructed chain, exactly as `fireS` reads the iota equation.
`UnitLawV` is the same shape with the two memberships in place of the
fabrication.

## T5 c4 — the projection bottom, landed (2026-08-28)

`indBottomProjS : IndBottomProjS V` (`Install/IndBottomProjS.lean`),
together with **D6's reserved `ProjFnR` refinement**, in one increment
(the house rule: a statement is refined only with its consumer).

### The refinement, read off the checker

`ProjFnR` now carries what its first consumer reads: `checkProjShape`'s
constructor telescope + residual arity/head, `checkProjRule`'s λ-tower
shape (`stripLams` to `.bvar (nF-1-i)`) with its `domsMatchAux`-pinned
domains, its four wellformedness pins and its rhs front door, and
`checkProjIota`'s `domsMatchAux` domain pin.  **Deliberately still
untransposed**: `checkProjRule`'s two `checkDefEqList` frame walks and
its `instPisAt`/`openPisAtFvars` runs — the bottom reaches its λ-tower
context through the *syntactic* pins, so no consumer exercises them.

### Why it is smaller than the TT lane's, not larger

The pre-c4 scoping note (above) predicted a third zipper/point pair.
It was wrong in the useful direction: **`pointS` and `fireS` are reused
verbatim** and only the zipper and the reduct change, each shrinking to
a few dozen lines, because the projection install's pins are
*syntactic* where the iota install's are *walks*:

| | plain/nested | projection |
|---|---|---|
| statement context | fired domain walks (`hdePre`/`hdeFld`), strong induction over the frame (`zipperS`) | `Γs = Γj` outright: `towerCtxEqD` on `checkProjIota`'s `domsMatchAux` + `PiTele.det`; the fit is `hfitC` read at the fired spine through `hpar` |
| λ-tower context | `annotPFrameEqS` ∘ `annotMemS` (P-frame identification, `hdeLam`) | `Γlam = Γj` outright: `towerCtxEq` on `checkProjRule`'s `domsMatchAux` |
| reduct | `reductS` (the rhs walk `hdeRhs`) | β: `lamTowerStepS` at the zipper's *own* memberships, `projBodyValue` naming the contractum |
| truthfulness | `annotS` | the same `lamTowerStepS` call's second component |

So the whole P-frame (`fvsP`/`xFvsP`/`hcinstP`/`hopenXP`/`hinstLam`/
`hdeLam`/`hdePars`) is **absent** from `IndBottomProjS`.  ~490 lines of
assembly against the TT lane's ~886 plus `pointStageP`.

A projection fire is a `.plain` fire at `mI = rP = cnP`: its spine is
the frame's openers, its **mixed value spine is the fired spine
itself**, and its index walk is `Forall2 _ [] []`.  That is what makes
`pointS` reusable, and it is the c3 spine abstraction paying a second
time.

**No `IotaSlotSorted`** (the TT statement's one unsupplied premise, #146):
`fireS` recovers the slot's universe membership from the statement's own
truthfulness plus `Eq`-former graph rigidity, unchanged.

Two V-free additions, both shared-tier: `towerCtxEqD` (the denote-level
form of `towerCtxEq` — a *renamed* domain pin needs it; `towerCtxEq` is
now its syntactic corollary), and `instPisAt_isSome_of_stripPis`
**relocated verbatim** (the seventh relocation) from
`Setlec/Model/InstFrames.lean` to `Setlec/Verify/InstSpine.lean`, where
both lanes see it — it sat behind a `SetTheory` section variable it
never used.

## FINDING 4 (c5, raised and diagnosed; **repair identified, not landed**): `EqLawV` cannot supply the eta/unit laws' fabricated side

**`EnvS` has no handle on `cval eqName` strong enough to type the eta
statement's right-hand side.**  Mechanized (`pinnedDirectT eqName ψ =
none` — `Eq` is one of the four reserved names the layer *derives*
rather than carries, `Verify/Denote/Pinned.lean:40-59`), so
`EnvS.basis_pinned` says nothing about `Eq`'s valuation, and the only
other handle is `EqLawV`.

*The shape.*  `EqLawV`'s computation clause takes **both** sides'
memberships in the slot as premises, and its only rigidity conjunct is
`interp ρ (cval eqName ψ) ≠ pt` — about the **bare head**.  Firing the
`T._model.eta` statement therefore needs:

* the left side (`.bvar 0`, the major) in the slot — **free**, from
  `Sat`: `checkEtaThm` pins the major's binder domain to
  `T._model p⃗`, which is the slot; and
* the right side (`C._model p⃗ (proj_j p⃗ x)…`) in the slot — **not
  available**.  Unlike the three iota bottoms, whose sides are
  certified by `checkIotaSidesTy` (`IotaSidesTyR`, which `fireS`
  consumes), `checkEtaThm`/`checkUnitThm` are pure `Bool` shape
  matches: they run **no** side certification, and their one
  slot-sort conjunct (`tbodyM == Expr.sort ℓA`, task #135) is
  **`mode.ttChecks`-gated**, i.e. absent at `--set-model`.

*Why the model lane does not hit it.*  `eta_rule_fold`
(`Model/EtaInstall.lean:553-559`) obtains exactly this membership from
the statement's own `AnnotOk` package plus `lam_dom_of_ne` applied to
`eqVal_app₂ hαu hvlmem` — i.e. from the **concrete** `eqVal`, which the
model has by definition and the [set] `EnvS` does not.  The naive
substitutes all fail: `mem_type` for `Eq` plus two `app_mem_piC` steps
gives `app (app vEq vα) vL ∈ piC ⟦vα⟧ (fun _ => univ 0)`, and
`piC_dom_unique` against `AnnotOkV`'s level-3 package then needs
`app (app vEq vα) vL ≠ pt` — which is *true* (`truthVal_ne_pt`) but not
derivable from a typing, since `pt ∈ˢ piC A (fun _ => univ 0)` holds.

*The repair (one clause, and it makes the interface **smaller**).*
Replace `EqLawV`'s computation clause by `eqVal_app₂`'s transpose:

```
    ∀ (ρ : Nat → V) (A a : VExpr),
      interp V ρ A ∈ˢ univ (ψ uN) → interp V ρ a ∈ˢ interp V ρ A →
      app (app (interp V ρ (cval eqName ψ)) (interp V ρ A))
          (interp V ρ a)
        = lamC (interp V ρ A) (fun y => eqv (interp V ρ a) y)
```

From it: the present three-membership clause follows by `app_lamC`; the
partial application's non-`pt` fact by `lamC_ne_pt_of_witness` (witness
`a ∈ A`, `eqv _ _ ≠ pt`); and the fabricated side's membership by
`lamC_dom_of_ne` against the statement's own `AnnotOkV`.  Supplier: the
basis install, by the *same* computation `Model/Basis/Eq/Install.lean`
already performs — nothing new is assumed, the fact is moved from the
model's definitional knowledge into the [set] invariant where the
install can pass it on.

*Scope and status.*  `EqLawV` is an `EnvS`-only field (**not** in T4's
frozen `EnvSHyp`), its supplier is unwritten, and its three present
consumers (the iota bottoms' `heqlaw`) use only the computation clause
— so the change costs `EqLawV.empty` (vacuous) and `EqLawV.cons`
(transport) and touches no frozen statement.  It is **not landed**: per
the house rule it lands with its consumer, and its consumer is the
unwritten eta-law derivation.  Recording it here so that pass starts
from a solved design problem.

## T5 c5 — finding 4's repair landed; the eta law lands with it (2026-08-28)

### The repair, as approved

`EqLawV`'s computation clause is now `eqVal_app₂`'s transpose — the
**two-fold** application is the truth-set abstraction over the slot:

```
    ∀ ρ A a, ⟦A⟧ ∈ˢ univ (ψ uN) → ⟦a⟧ ∈ˢ ⟦A⟧ →
      app (app ⟦cval eqName ψ⟧ ⟦A⟧) ⟦a⟧ = lamC ⟦A⟧ (fun y => eqv ⟦a⟧ y)
```

`EqLawV.app₃` recovers the earlier three-fold clause (one `app_lamC`),
and `EqLawV.dom` is the new consequence — the two-fold application is a
`lamC` with a non-`pt` value, so **anything the statement's own
truthfulness offers it as an argument already inhabits the slot**.  The
interface got *smaller*, not larger.

**Classification, explicitly**: this is **not finding #1**.  No checker
check is missing — the fact is derivable from the basis install's
existing computation (`Model/Basis/Eq/Install.lean:77`); it is an
interface field stated too weakly for a consumer its designer had not
met.  Same class as `EnvR.rec_rhs_denotes`.

`fireS` correspondingly takes the two sides' memberships as a
quantified hypothesis — with the slot's universe fact, which its own
rigidity block derives, handed to the caller — instead of
`IotaSidesTyR`.  The certified route is factored out as `sidesMemS`,
which the three iota bottoms call.  `fireS`'s `μ` became phantom and is
gone.  **That factoring is what lets the eta law reuse `fireS` rather
than mirror it**, and it is the general shape: a stage should take the
*fact* its consumers differ on, not the certificate one of them
happens to have.

### `etaLawKeyS` (`Install/EtaLawS.lean`, 537 lines)

`fireS` at `rP := caps.etaParams`, `cnF := 1`.  The statement's
telescope is the model former's parameters followed by the major; its
body is the pinned `Eq`-spine; the two sides are:

* **left** (`.bvar 0`, the major) — free from `Sat`: `checkEtaThm`
  pins the major's binder domain to `T._model p⃗`, which *is* the slot;
* **right** (the fabricated constructor application) — `EqLawV.dom`
  against the statement's own `AnnotOkV`, extracted at the third
  application by `annotOkV_descend` + `AnnotOkV_app`.

The two contexts are identified by `towerCtxEq` on `checkEtaThm`'s
`domsMatchAux` (the statement's parameter domains are the model
former's), and the public type former enters through `RenEqT.denote`.
The final identification is `interp_mkAppN_map` + `interp_closed` +
the three valuation identifications `hvT`/`hvC`/`hvP`.

**The universe-cohabitation wall, dodged.**  The naive route to the
fabricated side's membership — `mem_type` for `Eq` plus two
`app_mem_piC` steps, then `piC_dom_unique` — dies because
`pt ∈ˢ piC A (fun _ => univ 0)` *holds*: the proof point cohabits the
Prop-valued function space, so a typing cannot separate `Eq α a` from
`pt`.  `lamC`-rigidity separates them instead (the value is
`truthVal _ ≠ pt`).  Worth flagging for #151: in a world where the
wall goes away the naive route would work and `EqLawV` could stay at
the three-fold clause.

### c5 COMPLETE — the unit law's value-vs-expression bridge, built

`unitLawKeyS` landed with the bridge below.  The record of the problem
is kept because the bridge is reusable.

`UnitLawV` quantifies its two members as **values**  `UnitLawV` quantifies its two
members as **values** (`x y : V`) while the whole firing apparatus is
`VExpr`-spine-based (`TeleFitV`/`chainE`/`hfit.appN_val` apply the
theorem's inhabitant along a spine of `VExpr`s).  `EtaLawV` does not
hit this — its major is a `VExpr`.

The bridge, priced: fire at the shifted valuation
`ρ'' := cons y (cons x ρ)` with spine
`zs'' := xs.map (·.liftN 2) ++ [.bvar 1, .bvar 0]`, so that
`interp ρ'' (.bvar 1) = x` and `interp ρ'' (.bvar 0) = y` and
`interp ρ'' (liftN 2 a) = interp ρ a` (`interp_liftN` + a
`shiftE`-of-`cons` computation).  The one real cost is transporting the
given fit's memberships from `chainE ρ (xs.take m)` to
`chainE ρ'' (zs''.take m)`: the two valuations agree below `m` and
diverge above it, so each tower domain needs `interp_congr_below`
against its own `bvarsBelow m` (from `denote_bvarsBelow` on the
binder's opened domain).  No `Sat`/`TeleFitV` transport lemma exists
yet — and it turned out **not to be needed as a lemma**: the transport
is one `interp_congr_below` per position against
**`PiTele.bvarsBelow`**, the piece that *was* missing and is now in the
shared tier:

> a `∀`-tower's `i`-th domain, over a subject bounded by `d`, mentions
> no de Bruijn index at or above `d + i`.

That is the general fact behind "a context entry only reads the
context below it", it is a 25-line induction on `PiTele`, and it is
what any future *"fire this statement at a valuation my caller
supplies"* obligation will want.  Recording the shape: **when two
valuations agree below a context's depth, `PiTele.bvarsBelow` +
`interp_congr_below` is the transport — no `Sat`/`TeleFitV`
congruence lemma is required.**

The unit law is otherwise *easier* than the eta law, and the reason is
worth one line: **both** of its sides are frame variables (`.bvar 1`
and `.bvar 0`), whose binder domains `checkUnitThm` pins to the family
application — so `Sat` supplies both memberships and finding 4's
rigidity is not needed at all.  Only the eta law fabricates a side.

## T5 — the per-kind dispatch, and `declIndS` stage 1 (2026-08-28)

`declStepS` (`Install/Step.lean`) is the `checkDeclR_sound`-shaped
lemma T6 consumes: **a `DeclR` derivation extends an `EnvS`**, by pure
dispatch over the six kinds.  Four go through the landed kind lemmas
(`declDefnS`/`declThmS`/`declOpaqueS`/`declAxiomS`); the two remaining
are named as obligations in the house pattern —

* `DeclBasisS` — supplier: the basis install;
* `DeclIndS` — supplier: the block install (the member fold, the
  recursor group consuming the three iota bottoms, the capability
  record consuming `etaLawKeyS`/`unitLawKeyS`, the projection installs
  and the templates).

So the per-kind lemma set is **closed modulo those two**, and T6 can
be written against `declStepS` today.

`indMemberS` (`Install/IndMemberS.lean`) is `declIndS`'s stage 1 and
`extendAxiomS`'s sibling: a checked non-recursor block member
(`.indInfo`/`.ctorInfo`) installed **at the model artifact's
valuation** — `cval T ψ := cval (T._model) ψ`, which is exactly the
identification `etaLawKeyS`/`unitLawKeyS` consume as `hvT`/`hvC`.  Two
`EnvS.cons` obligations stay parameters, as in the TT lane
(`checkIndMemberTT`): at a single member's install the family's
constructor and projections need not be stored yet, so only the block
fold can discharge `hheadEta`/`hheadUnit`.  Everything else is vacuous
by kind or refuted by the member's non-reservedness.

### FINDING 5 — **RESOLVED 2026-08-28: option 3, the folds run the valuation**

The decision, with its rationale, then the record of the finding as
raised.

**Decided**: `IndMembersR`, `ProvisionRecsR`, `IndRecsFoldR`,
`ProjInstallR` and `TemplatesR` are re-signed to **thread the running
valuation** — `Env → TConstVal → … → Env → TConstVal → Prop` — with
each step's valuation being the one the install builds,
`cvalModeled cval n := cvalWith cval n (fun ψ => cval (n.str "_model") ψ)`
(and, for a projection function, `cval (projModelName T i)` — the
identification `etaLawKeyS` consumes as `hvP`).  `DeclIndR`
existentially closes the final valuation.

Three reasons, in the campaign's vocabulary:

1. **Faithfulness / bridge-dischargeability.**  The checker threads a
   running *environment* through the block; the bridge inverts
   `checkIndDecl`'s fold member by member, and each inversion hands
   over facts about the **current** env — the running valuation is
   what the inversion delivers on the nose.  Pre-block is semantically
   wrong for `k > 1`; post-block is right only via a
   not-mentioned-freshness adjustment the bridge would owe at *every*
   member.
2. **It puts blocks on the single-declaration kinds' discipline.**
   `declThmS` takes the pre-*declaration* `cval`, which for a single
   declaration *is* the running valuation at its own check time (the
   entry is added after).  A block differs only in one `DeclR` step
   installing many members incrementally; option 3 makes that the same
   discipline rather than a special case.
3. **No unstated T6 obligation** — correct by construction.  Any
   running-vs-final agreement lemma (freshness-based; members never
   forward-reference) is proved at a consumption site that *wants* the
   final form, instead of being a silent precondition of the assembly.

`indMemberS` was re-signed to match (it already built exactly
`cvalModeled`, so the agreement is now literal) and to **expose its
valuation** — `∃ m₂, m₂.cval = cvalModeled m.cval cvA.name` rather than
`Nonempty` — which is what lets the fold compose.

*The finding as raised.*

`IndMembersR` — and equally `IndRecsR`'s `ProvisionRecsR`/
`IndRecsFoldR`, `ProjInstallR` and `TemplatesR` — thread **one**
`cval` unchanged through the fold, while each step's environment
grows.  The step's front door is `ConstantValR μ F env'ₖ cval …`,
whose last conjunct reads `denoteClosed cval env'ₖ φ type'` and
`Infer μ env'ₖ cval …`.  A later member's type *does* mention earlier
block members (a constructor targets its family), so which valuation
`cval` denotes is not a detail.

Two readings, and they are not equivalent:

* **`cval` = the declaration's pre-block valuation** (what every
  landed consumer passes — `declThmS` and friends take
  `h : DeclXR μ F env m.cval …`).  Then for member `k > 1` the front
  door speaks about the *junk* valuation the block members had before
  they were installed, and the install cannot use it: the fact is
  about the wrong function and no transport recovers it.
* **`cval` = the post-block valuation**.  Then the fold is correct —
  on every name in `env'ₖ` the post-block valuation agrees with the
  running one — but T6 must **construct the final valuation before
  consuming the relation**.  That is possible (it is
  `cvalWith … (T ↦ cval (T._model)) …` over the block's names, all of
  whose model artifacts are already in `env₀`), but it is a real
  obligation on T6 and nothing in the tier says so.

The third option is to **index the folds by the running valuation**,
which is what the install actually builds:

```
  | env', cval, ci :: rest, env₂, cval₂ =>
    ∃ cvA, MemberValR μ F env' cval blockNames ci.toConstantVal cvA ∧
      … IndMembersR … ⟨.indInfo cvA caps :: env'.consts⟩
          (cvalWith cval cvA.name
            (fun ψ => cval (cvA.name.str "_model") ψ)) rest env₂ cval₂
```

so the relation and `indMemberS` agree **by construction** and no
side condition on T6 is needed.  This is the same class as finding 4
(a statement fixed before meeting its consumer) but, unlike it, the
present statement is *defensible* under the second reading — so the
choice is a design decision, not a repair, and it is recorded here
rather than taken.  `declIndS` stage 2 (the member fold) is blocked on
it; stage 1 is not.

# Task #151 tier B — the collapse-free two-regime interpretation

`Setlec/SetR/Interp2/*` (landed: `Ops`, `Syntax`, `Interp`, `Kit`,
`Univ`, `TierA`).  Imports `Setlec/SetTheory/Basic.lean` and nothing else — no
checker, no model layer, and in particular **no module built over the
collapse operators**.  Zero edits to existing files outside this
document and `Setlec/SetR.lean`.

## The two regimes

`interp2 V ρ e : V` is total on annotated terms, term-directed and
environment-free.  Every binder carries the numeral its regime is
chosen by; **no clause inspects a semantic value**, which is the whole
point — the inspection "is this value everywhere the proof point over
its domain?" *is* the domain-relative collapse (task #100).

The dispatch lives in two operators (`Interp2/Ops.lean`), and nowhere
else:

| | `v = 0` — squash | `v ≠ 0` — graph |
|---|---|---|
| `piR v A B` | `truthVal (∀ x ∈ A, B x inhabited)` | `piSet A B` |
| `lamR v A F` | `pt` | `graph F A` |

These are the **pre-#100 `SetTheory.pi`/`SetTheory.lam`** (see the git
history of `Derive/Pi.lean`, commit `19d070d^`), restated in the
`Setlec.SetR.Interp2` namespace so that `Setlec/SetTheory/*` is
untouched.  What is new is not the operators but that the *numeral now
comes from the term* — tier A's annotation pass — rather than from a
checker-side stored annotation the model had to re-derive.  The law
battery is that file's, plus the inversion laws only the
annotation-driven definition can have.

The remaining clauses are annotation-free: `sort u ↦ univ u`,
`app f a ↦ app ⟦f⟧ ⟦a⟧`, `eqE _ a b ↦ eqv ⟦a⟧ ⟦b⟧`, `proj ↦
sfst`/`ssnd`, `letE ↦` ζ (substitute the value), `prf ↦ pt`.

**Application needs no annotation, and this is not luck.**
`SetTheory.app`'s proof-point tag (`app pt a = pt`) *is* the squash
regime's β, and `app_graph` *is* the graph regime's; the two clauses of
the one operator already match the two regimes.  So `interp2`'s `app`
case is uniform.

**`letE`.**  ζ needs no annotation, so tier A's `letE` annotation
decision does not reach this clause.  If tier A lands a `letE` whose
type slot is semantically load-bearing, `interp2_letE` is the one and
only clause to revisit.

## What replaced the collapse at each of its former sites

| collapse fact | replacement | note |
|---|---|---|
| `mem_piC_cases` (member is `pt` **or** a graph) | `mem_piR_pos` — member **is** a graph | no dispatch; every consumer that split now does not |
| `app_lamC` (β with no premises, via the `pt` branch) | `app_lamR_pos` (β, `v ≠ 0`, premise-free) + `app_lamR` (β at `v = 0`, fibre-universe premise) | the `v = 0` premise is the pre-#100 one |
| `piC_dom_unique` (needs `f ≠ pt`) | `piR_dom_unique` — **no side condition** | supplying `≠ pt` is what the collapse made hard (T5 c5) |
| `lamC_empty` (every empty-domain λ is `pt`) | `lamR_pos_empty` — the empty **graph** | this clause is the #100 countermodel; it is gone |
| `piC_empty = unitSet` at every codomain | `piR_pos_empty = {∅}` at `v ≠ 0` | truth only in the squash regime |
| `piC_prop_eq` (`Prop` products *compute* to truth values) | `piR_zero` — by definition | |
| `piC_mem_univ` + `piC_mem_univ_max` ("may land smaller") | `piR_mem_univ` — the `imax` rule, **sharp** (`piR_pos_not_mem_univZero`) | the regimes are disjoint |
| `pt_mem_piC_iff` | `not_pt_mem_piR_pos` — the point inhabits **no** graph-regime product | |
| `lamC_eta`, `eq_of_mem_piC_app_eq` | `lamR_eta`, `eq_of_mem_piR_app_eq` | unchanged in shape |

## `pt` is demoted, not deleted

The brief asked for "no `pt` anywhere".  **That is not achievable, and
the reason is a finding, not an omission.**  `SetTheory` fixes
`univ 0 = power unitSet = power (sing pt)`, so a proposition *is* a
subset of the canonical singleton and the unique inhabitant of a true
proposition *is* `pt`.  Any two-regime interpretation must give the
squash regime's values *some* canonical point, and `SetTheory` has
already chosen which.  Removing it would mean re-deriving `univZero`
over a different singleton — an edit to `Setlec/SetTheory/*` with no
payoff, since renaming the point changes nothing.

What *is* achievable, and is delivered, is the demotion:

* `pt` occurs in **exactly two definition bodies**: `lamR`'s `v = 0`
  branch and `interp2`'s `.prf` clause.  Both are the canonical proof,
  in the regime where every value is the canonical proof.
* No definition and no proof in `Interp2/*` **tests** whether a value
  is `pt`.  (`pcol`/`lamC` do; that test is the collapse.)
* The graph regime never produces, contains or consults it:
  `lamR_ne_pt`, `not_pt_mem_piR_pos`, `mem_piR_pos`'s fourth clause.
* No junk point is needed: off-domain application is the canonical `∅`
  (`app_off_dom_piR_pos`, `interp2_app_off_dom`), and that off-domain
  behaviour is *canonical*, which is what makes on-domain agreement
  total agreement (`interp2_pi_ext`).

## The universe question, assessed

**Question (transformed).**  The record's version — "`pt ∈ univ (u+1)`
was forced for transitive chains" — does not survive the removal of the
collapse, because what forced it was that a `Type`-level abstraction
could *be* `pt`.  The live question becomes: *can anything the
`SetTheory` universe tower happens to contain break the graph inversion
at a universe-codomain product?*

**Answer: no, and structurally so.**  `piR v A B` at `v ≠ 0` is
`piSet A B`, carved out by **separation**: `f ∈ piSet A B` iff
`f ⊆ sigmaPairs A B` and `f` is total and single-valued on `A`
(`mem_piR_pos_iff`).  That is a property of `f`'s own members.
Universe transitivity says members of members of `U` are in `U` — it
enlarges `U`, and can never add a member to a set defined by
separation.  `interp2_univ_cod_inversion` is the universe-codomain
instance, and it is proved *by the general lemma with no extra
hypothesis*: the inversion is fibre-blind.

**Verdict on the parked contingency.**  The non-transitive-chain
re-choice is **not needed, and there is nothing left for it to fix**.
`Setlec/SetTheory/Core.lean`'s transitivity clause and the ω-chain stay
exactly as they are; this layer imposes no new demand on the class.
(The prognosis in the brief was "no"; it is confirmed, mechanized in
`Interp2/Univ.lean`.)

## Findings

**F1 — the T5 c5 universe-cohabitation wall is exactly the
empty-domain case, and it is gone here.**  This section recorded (T5
c5) that "`pt ∈ˢ piC A (fun _ => univ 0)` *holds*: the proof point
cohabits the Prop-valued function space, so a typing cannot separate
`Eq α a` from `pt`."  Mechanized (`Univ.lean`):

```
pt_not_mem_univZero    : ¬ (pt : V) ∈ˢ univZero
pt_mem_piC_univZero_iff : (pt : V) ∈ˢ piC A (fun _ => univ 0) ↔ A = empty
```

So the cohabitation is **not** general: it is precisely the case where
the domain cannot be shown nonempty.  The dodge (separating the two by
`lamC`-rigidity rather than by typing) was therefore right *as taken* —
a derivation quantified over an unknown `α` cannot rule the empty case
out — but the wall is narrower than recorded, and under `interp2` it
does not exist at all: `piR v ∅ B = {∅}`, and
`not_pt_mem_piR_empty` closes even that case.  **Consequence for T5
c5**: in the two-regime world the naive route works and `EqLawV` can
stay at the three-fold clause, as the DESIGN note anticipated.

**F2 — the regime split is sharp, so the annotation is a fact about
the value, not a bound on it.**  `piR_pos_not_mem_univZero`: a
graph-regime product with inhabited fibres is never a truth value.
Under the collapse only the one-directional `piC_mem_univ_max` is
available ("collapsed values may land *smaller*"), which is why
level-blind reasoning about interpreted binders needs side conditions
there and none here.

**F3 — the substitution stack transposes unchanged.**
`interp2_liftN`/`interp2_inst`/`interp2_inst0`/`interp2_mkAppN` are
`Setlec/TT/Semantics/Interp.lean`'s, line for line modulo the extra
numeral fields.  Removing the collapse costs nothing in the
substitution metatheory — as predicted, because `interp2` is
structural and the numerals are carried, never read, by `liftN`/`inst`.

## Scope: what is deliberately **not** here

* **The built-in constants.**  `AVExpr` has no `const` case and
  `interp2` no `bval` clause.  `Setlec.TT.bval`'s values are `lamC`
  towers — collapse-built — and rebuilding them as `lamR` towers is a
  separate landing, because each constant's *application law* then
  acquires the pre-#100 shape: at `u = 0` the whole tower is the
  canonical proof, so `natRecV_app` and friends regain the
  `v = 0 → fibres are truth values` premise that `app_lamC` had made
  unnecessary.  Mechanically portable (the pre-#100 `app_lam'` is the
  template), but it is a law-surface change, not an interpretation
  change, and nothing in the interpretation, the kit or the universe
  assessment depends on it.
* **`sigmaSet`.**  Already two-regime (`Derive/Sigma.lean` dispatches
  on `w = 0`), so `proj ↦ sfst`/`ssnd` needs nothing; it is the
  precedent this tier follows.
* **Soundness against a judgment.**  There is no `AVExpr` typing
  relation to be sound against until tier A's `Annot/Kinding.lean`
  lands.

## F4 — the `λ` node must carry its **codomain** sort (blocks the swap)

Tier A's `Annot/Syntax.lean` landed with `lam (u) ty body`, `u` being
the *domain*'s sort — faithful to `Rel.lean`'s I7, which has one
`DefEq … (.sort u)` premise and it is the domain's (I6, ∀-formation,
has two).  **`pi (u v)` is exactly what tier B needs; `lam (u)` is not
the numeral tier B reads.**  A λ is squashed iff the product it
inhabits is a proposition iff the *body's type* has sort `0`; the
domain's sort says nothing about that.

Mechanized in `Interp2/TierA.lean`:

```
lam_cod_sort_needed :
  ∀ (L : Nat → V → (V → V) → V),
    (∀ u v A F B, (∀ x ∈ A, F x ∈ B x) → L u A F ∈ˢ piR v A B) → False
```

`L` is exactly the shape a structural, environment-free interpretation's
λ clause has — a function of the node's annotation, the domain's value
and the body's fibre function.  The witness is `A = {•}`,
`F = fun _ => •`, `B = fun _ => {•}`: at `v = 0` proof irrelevance
forces `L 0 {•} F = •`, at `v = 1` graph-hood forces
`L 0 {•} F ≠ •`, and the two readings share *every argument of `L`*.
`lamR_sound_at_every_regime` is the positive half: with `v` in hand the
clause is sound at both regimes with the same premise.

**The fix is one numeral** — `lam (u v) ty body`, `v` the sort of the
body's type — which is what `Interp2/Syntax.lean`'s provisional node
already carries.  The premise is not in I7 as stated: supplying it
means I7 gains the opened-body sort premise (`Infer (A :: Δ) b B`,
`DefEq (A :: Δ) tB (.sort v)`) that its sibling I6 already has.

**Consequence for the #100 de-gating plan.**  The kernel's λ-codomain
`ensureSort` is listed there for deletion ("delete defeq cod comparison
+ λ-cod re-check — pure relaxation toward reference").  It is
**load-bearing for tier B**: it is where the λ codomain sort comes
from.  De-gating may drop the *comparison*, but the sort must still be
computed and stored, or the two-regime interpretation has no annotation
to read at `lam`.  Since the whole point of #151 is that the
interpretation reads annotations instead of values, this is a
requirement on the annotation pass, not a regression.

## Coordination: the `AVExpr` swap

`Interp2/Syntax.lean` is **tier B's provisional `AVExpr`**.  It mirrors
`Setlec.TT.VExpr` constructor for constructor, minus `const` (above),
plus the annotations `lam (v)` and `pi (u v)`; `liftN`/`inst` carry the
numerals through untouched.

**The swap is blocked on F4**, not on scheduling: tier A's node cannot
be interpreted (F4 is a refutation, not a preference).  Once `lam`
gains its codomain numeral the swap is: delete `Interp2/Syntax.lean`,
re-point `Interp2/Interp.lean`'s import, reconcile the `lam` field
order, and add the `const` clause (separate landing).  Nothing in
`Kit.lean`, `Univ.lean` or `TierA.lean` reads the syntax except through
`interp2`, so the blast radius is `Interp.lean`'s nine clauses and the
`AVExpr.liftN`/`inst` simp lemmas that `Kit.lean`'s two inductions
cite.  Tier A's `erase`/`erase_liftN`/`erase_inst` are unaffected —
they are what tier B's substitution stack would compose with.

## T5 — `declIndS` stage 2: the member fold (2026-08-28)

`indMembersS` (`Install/IndMembersS.lean`) runs `indMemberS` along
`IndMembersR`, carrying the running valuation and the block invariant
**`BlockInstalledTT`** — reused from the TT lane *verbatim*
(`Verify/Extend/Block.lean`), because it is `TConstVal`-stated and
V-free, and its `.step` is exactly the per-member preservation the
fold needs.  That is the eighth shared-tier reuse and the cheapest of
them: no transposition at all.

Three obligations stay named, their suppliers outside the fold:

* `MemberKeyS` — the member's *semantic* content: the model
  artifact's value inhabits the member's renamed type.  Supplier: the
  model definition's own `mem_type`, transported across
  `MemberValR`'s `eqUpToNames` pin, using the block invariant to
  identify the public names' valuations with the model names'.
* `MemberEtaS` / `MemberUnitS` — `EnvS.cons`'s capability head
  obligations.  They are **vacuous at every member but the one that
  completes the family** (`EtaFamilyStored` is false until the
  constructor and every projection are stored), and at that member the
  block assembly discharges them through `etaLawKeyS`/`unitLawKeyS`.
  Deferring them is the TT lane's own choice (`checkIndMemberTT` takes
  them as hypotheses) and for the same reason.

### `declIndS` stage 2b: the provisioning fold

`indMemberS` was generalized to admit a **rule-less** `.recInfo` head:
`EnvS.cons`'s two rule head obligations are vacuous over an *empty
rule list* rather than by kind, which is exactly what the recursor
provisioning installs.  The shared step is `memberInstallS`, and both
folds are three lines each over it — `indMembersS` (the non-recursor
members) and `provisionRecsS` (the group's recursors, yielding the
**self** environment, its valuation, and the block invariant there).

That self environment is the precondition for stage 3: the iota
bottoms' walks live in `envSelf`, not in the accumulator, so the
bottoms are applied at `EnvS V envSelf`.

### Stage 3's architecture, settled before writing it (a near-miss worth recording)

The obvious route — cons-fold the ruled recursors onto `env₂`, one
`EnvS.cons` per recursor — is **wrong**, and it is worth saying why,
because the cons-fold is what stages 1–2 condition you to reach for.
At intermediate step `i` the accumulator holds recursors `1..i` but
not `i+1..k`, while `IotaRuleR` only requires
`rhsA.constsResolve envSelf = true` — the *self* environment, which
holds all of them.  A rule right-hand side that mentions a sibling
recursor therefore fails to denote at the intermediate accumulator,
so `RecRulesV` — which is keyed on *every* stored `recInfo` — would be
unprovable there and no intermediate `EnvS` exists.

The TT lane does not cons-fold: it installs the group **by the
rule-list swap** (`EnvTT.swap`, `TTVerify/EnvSwap.lean`).  Provision
*all* recursors rule-less (that is `provisionRecsS`, landed), then
replace each entry's `[]` by its checked `rules'`.  The environment's
*names* never change, so `denote` and the valuation are untouched and
the ordering problem does not arise.  `IndRecsFoldR`'s cons-fold from
`env₂` produces exactly `envSelf` with the rule lists replaced (same
order, same names), so the swap route matches the relation.

What stage 3 therefore needs, in order:

1. **`EnvS.swap`** — the `EnvTT.swap` transpose (~300 lines there).
   Its V-free half is **already shared**: `SwapPairSh`, `SwapShList`,
   `swapSh_find?_corr`, `ProvFacts.*` in
   `Setlec/Verify/Extend/Recs.lean`.
2. **`iotaRuleS`** — the per-rule bridge from `IotaRuleR` to
   `RecRulesV.cons`'s `hhead` clause, firing `indBottomPlainS` on the
   `.plain` branch and `indBottomNestedS` on the `.nested` one
   (`.inert` is excluded by the clause's own premise).  Its glue is
   available: `BlockInstalledTT.renameOkT` gives the bottoms' `hro`,
   `Expr.recRulePlain`'s two `decide`s give `cnP ≤ rP` and `rP ≤ mI`,
   `EnvWF` gives the syntactic guards, and `mS.mem_type` at the
   `iota_j` theorem gives `hthm`.
3. the group install over 1–2.

Then: the capability record (stage 4, on `etaLawKeyS`/`unitLawKeyS`
through `MemberEtaS`/`MemberUnitS`), the projection installs (stage 5,
on `indBottomProjS`), the templates (stage 6 — note a template entry
has no model artifact, so the install must *choose* its valuation; an
inhabitant of `univ 0` such as `VExpr.eqE (.sort 0) .prf .prf` is
truthful and closed, which is why `TemplatesR`'s step leaves the
valuation existential), the `DeclIndS` assembly, and `DeclBasisS`.

# Task #151 tier A — the sort-annotation pass

Non-invasive by construction: three **new** modules under
`Setlec/SetR/Annot/*`, plus the lib-root registration.  `denote`, the
relation family (`Rel.lean`), the bridge (`Bridge/*`) and the soundness
half (`Sound/*`) are untouched — tier A *consumes* the landed
`Sound/Main.lean` and adds nothing to it.  That is the tiering
rationale: the annotated syntax and the pass that produces it are a
decoration on top of a finished lane, so they can be landed, reviewed
and revised without moving anything the campaign already verified.

## Inventory (as landed)

| file | content |
|---|---|
| `Annot/Syntax.lean` | `AVExpr` (the sort-annotated `VExpr`), `erase`, the de Bruijn kit (`liftN`/`inst`/`mkAppN`) with clause equations, and the erase-commutations `erase_liftN` / `erase_inst` / `erase_mkAppN` |
| `Annot/Pass.lean` | `HasSort` (the sort fact) + `HasSort.ofConv`; `ZetaEq` + `ZetaEq.refl`; the `Annotates` relation; `Annotates.zetaEq` (the erase contract); the literal-spine closures; `CvalAnnot` (the one environment hypothesis); **`Infer.annotates`** and **`Tele.annotates`** (existence, one recursor application over the 44 minor premises) |
| `Annot/Kinding.lean` | `ZetaEq.interp_eq`; `interp_eq_univ_of_sortFact`; **`sortFact_unique`** (+ the linked form); `HasSort.mem_univ` / `HasSort.annotOkV`; `Annotates.interp_erase` |

## The rulings, and where they came from

* **Ground numerals.**  `VExpr` already evaluates every level
  expression at its use site, so an annotation is a `Nat`.  There is no
  level substitution to commute with — which is exactly what makes the
  substitution kit *inert*: `erase_liftN`/`erase_inst` hold because
  nothing in `liftN`/`inst` reads or writes a numeral slot.
* **Annotations are cached premises.**  A slot exists where a rule's own
  premises supply the fact *and* a consumer reads it.  Hence
  `pi (u v) A B` (I6 has two `DefEq … (.sort _)` premises),
  `lam (u) A b` (I7 has one, the domain's), **`letE` with no sort**
  (I10 supplies one but `interp` reads neither the annotation nor its
  sort — `let` is not a type former, so there is nothing to grade), and
  `eqE` keeping its unannotated, unread type slot as `VExpr` does.
* **The sort fact is `DefEq`-shaped, not `Red`-shaped.**  The brief
  writes the premise as `Red tA (.sort u)`; the landed family says
  `Infer Δ A tA → DefEq Δ tA (.sort u)`, per T4's **repair A** (above).
  `HasSort` is spelled at the landed shape, which is also what makes it
  **conversion-invariant on the type side** (`HasSort.ofConv`, one
  `DefEq.trans`) — the property a cached premise has to have.

## Per-tree sort correctness; no cross-tree claim

`Annotates`' binder clauses **are** the invariant: a derivation of
`Annotates … Δ (.lam A b) (.lam u Aa ba)` contains a `HasSort … Δ A u`
by construction, and `cases`/`rec` hands it to tier C.  So correctness
is *per tree*, and its two eliminations are proved here:
`HasSort.mem_univ` (`⟦A⟧ρ ∈ˢ univ u` at any satisfying `ρ`) and
`HasSort.annotOkV` (the domain's truthfulness).

### NEGATIVE RESULT A4 (standing) — membership-form kinding is false; kinds thread through *shared inferred types*

**The rule for every consumer, tier C included: a level is recovered
from an equality of universes, never from a typing.**  The hoped-for
form

```
    interp V ρ A ∈ˢ univ u → interp V ρ A ∈ˢ univ v → u = v
```

is **false**, and not by an accident of this model: the tower is
cumulative (`SetTheory.univ_mono : m ≤ n → univ m ⊆ˢ univ n`), so a
membership fixes only a **lower bound** on the sort.  Every set that
inhabits `univ u` inhabits every `univ v` above it, so no pair of
memberships can separate two levels.  The *only* handle the tower
offers is `SetTheory.univ_inj` (`univ u = univ v → u = v`, relocated
below), and reaching it needs the two sort facts to be about the
**same type** — which is why `sortFact_unique` is stated at one `tA`
and why `sortFact_unique_of_conv` needs a linking `DefEq` rather than
two independent typings.

Two consequences, both binding:

* **No cross-tree coherence is claimed at tier A.**  Two annotations of
  one term, justified by unrelated derivations, are not shown to carry
  the same numerals, and cannot be by any argument at this tier.
* **Tier C threads kinds through shared inferred types.**  Wherever two
  binder sorts must agree, the statement has to name the type they are
  both facts about (or a `DefEq` between the two inferred types), and
  the agreement is then `sortFact_unique`/`sortFact_unique_of_conv` at
  a satisfying `ρ`.  Contexts with no satisfying `ρ` are vacuous under
  the `∀ ρ, Sat V Δ ρ → …` shape every statement already has, so the
  two mechanisms together cover the space — but the "read the level
  back off a membership" shortcut must never be reached for.  It is the
  natural first move and it is unsound.

## Unique kinding, semantic form (the statement tier C consumes)

```
    sortFact_unique (henv : EnvSHyp V env cval φ)
      (hu : DefEq μ env cval φ Δ tA (.sort u))
      (hv : DefEq μ env cval φ Δ tA (.sort v))
      (hρ : Sat V Δ ρ) : u = v
```

Route: `DefEq`-soundness is *unconditional* under `Sat` (the T4
architecture), so both premises read as equalities at the one value
`interp V ρ tA` — `univ u = interp V ρ tA = univ v` — and `univ_inj`
recovers the numeral.  `sortFact_unique_of_conv` is the same with a
linking `DefEq` between two inferred types.

**`univ_inj` did not exist; it does now, in its home** (the campaign's
**eighth relocation**, done verbatim in its own commit).  Searched
`Setlec/SetTheory/Derive/*`: `Univ.lean` had `univ_mono`,
`univ_mem_univ`, `univ_subset_succ`; `Derive/Empty.lean` has
`not_mem_self`; injectivity was absent.  It is proved from those three
(`u < v` gives `univ u ∈ˢ univ (u+1) ⊆ˢ univ v`, and the equality would
put a set inside itself) and now sits beside `univ_mono` in
`Setlec/SetTheory/Derive/Univ.lean`, with A4's warning in its
docstring — the two facts belong together, since `univ_mono` is
precisely why `univ_inj` is the only handle.  A general fact about the
tower with no #151 content; `Annot/Kinding.lean` consumes it as
`SetTheory.univ_inj`.

## FINDING A1 — the `let` body is not certified un-instantiated

I10 certifies the let body **only** in instantiated form
(`Infer Δ (b.inst v) B`); a derivation contains no sub-derivation about
`b` in the extended context `T :: Δ`, so the binder sorts *inside* `b`
have no justification there.  Recovering one needs substitution
admissibility for the family (`HasSort (T :: Δ) C u` ↔
`HasSort Δ (C.inst v) u`), and the family's only metatheory is
weakening (M1).

**Resolved, in the premise-exact direction**: `Annotates` has **no
structural `letE` clause**; a `let` node is annotated by the annotation
of its zeta contractum (`Annotates.zeta`), which is exactly what the
checker's own premise supplies.  Semantically free —
`interp ρ (.letE T v b) = interp ρ (b.inst v)` (`interp_inst0`).

The price is that the erase contract is exact only *up to zeta*, and
that is what `ZetaEq` records: `Annotates.zetaEq : ZetaEq e ea.erase`,
with `ZetaEq.interp_eq` its semantic reading and
`Annotates.interp_erase` the form tier C uses
(`interp ρ ea.erase = interp ρ e`).  `AVExpr.letE` is **kept** —
`AVExpr` stays a faithful variant of `VExpr` and `erase` stays
surjective — but the pass never emits it.

## FINDING A2 — reduction is annotation-opaque

The existence theorem's motives are graded exactly like T4's soundness:
`Infer` carries the content, `Tele` carries its spine's arguments, and
**`Red`/`DefEq`/`DefEqL` carry nothing**.  That is forced, not lazy:

* `Red.beta`'s subject `.app (.lam A b) a` has a λ whose **domain sort
  no premise supplies** (R4's premises are the argument's
  `Infer`+`DefEq` pair only), and `Red.zeta`'s subject is premise-free
  altogether — so "the subject of a reduction is annotatable" is false;
* even the *transport* reading ("if the redex is annotatable so is the
  contractum") is unavailable: it needs
  `Annotates (A :: Δ) b ba → Annotates Δ a aa →
   Annotates Δ (b.inst a) (ba.inst aa)`, i.e. substitution
  admissibility for `HasSort` again.

Tier C must therefore not expect to move an annotation across a `Red`
step.  (`AnnotOkV` *does* transport — `RedS`'s second conjunct — because
it is a semantic predicate; `Annotates` is a derivation-backed one.)

## The one environment hypothesis

I3/I4/I5's subjects are stored-constant valuations (`cval n ψ`,
`natLitV`, `strLitT`), arbitrary `VExpr`s as far as this tier is
concerned, so their binders' sorts cannot come from the derivation.
`CvalAnnot` supplies them, and it is the exact analogue of
`EnvSHyp.annot_okV` — the field a future `EnvS` component discharges.
The two literal subjects follow from it by `Annotates.app` alone
(`Annotates.natLitT` / `Annotates.charListT`).

## FINDING A3 (**blocking, campaign-level**) — the λ codomain sort is *not computed by the checker*, so tier B's F4 has no premise-exact repair

Tier B's F4 (above) is correct as a refutation: a term-directed,
environment-free λ clause needs the **codomain** sort, and `lam (u)`
does not carry it.  Its **corollary is not**: F4 states that "the
kernel's λ-codomain `ensureSort` … is where the λ codomain sort comes
from" and that de-gating "may drop the comparison, but the sort must
still be computed".  Read against the landed checker, **it is already
gone, deliberately, and nothing computes it**:

* `Setlec/Kernel/Core.lean:1588-1600` — the λ clause, with its own
  comment: *"The body's type is not sort-checked here (task #100 stage
  6: the official-kernel `infer_lambda` shape — the λ-annotation
  re-check died with the stored annotations …)"*.  It runs
  `r.infer (depth+1) (body.instantiate1 …)` and rebuilds the `∀`.  No
  `whnf`, no `ensureSort`, at either mode (the clause is not
  `ttChecks`-gated).  Compare the **∀** clause four lines above
  (`Core.lean:1578-1587`), which *does* call `ensureSort` on the opened
  body — that asymmetry is exactly why I6 has two sort premises and I7
  has one.
* `Setlec/Verify/InferLemmas.lean:149-157` — `inferTypeCore_lam_inv`
  returns `∃ tty u bt, infer ty = tty ∧ whnf tty = .sort u ∧
  infer (body…) = bt ∧ t = .forallE …`.  The **domain**'s sort and no
  more; there is no conjunct to invert for the codomain.
* `Setlec/Kernel/Expr.lean:72-74` — `BinderMeta` is `⟨bi⟩`.  The
  codomain-sort slot the task-#49-era annotate pass filled was deleted
  with the decoration apparatus in #100 stage 6 (DESIGN.md's stage-6
  record: the cod memos, `codOfCore`/`codOfI`/`IState.codOfC`,
  `internBMFast`, `annotate_sound` — all deleted).

**Consequence: the requested I7 amendment cannot be landed.**  Adding
`Infer (A :: Δ) b B → DefEq (A :: Δ) tB (.sort v)`-shaped premises to
I7 would break premise-exactness (design §0) *and* would make the
bridge clause `infer_lam_claimR` (`Bridge/InferStruct.lean:175-190`)
undischargeable — there is no `whnf bt = .ok (.sort v)` fact in the
inversion — so **`checkStepR`, a landed COMPLETE theorem, would stop
being provable**.  This is precisely the stop condition the amendment
request named ("a bridge inversion lacking the conjunct"), and it is
recorded rather than taken.  Tier A's `lam (u)` is therefore left as
landed, and the `AVExpr` swap stays blocked.

**Repairs, priced** (the decision is campaign-level, like findings 1–3):

* **A — restore the computation in the kernel's λ clause.**  One line
  (`let _v ← ensureSort r env (depth+1) bt`, the ∀ clause's own move).
  Cost: it is a *kernel* change, so it lands outside SetR — the
  interned/`CheckerS`/`CoreNC` mirrors and their sim proofs,
  `inferTypeCore_lam_inv`'s re-sign and its two consumers
  (`Model/Core/Infer.lean:208`, `Bridge/InferStruct.lean:190`), and the
  model lane (which ignores the fact — a `-`).  Two risks: it makes the
  checker **stricter than the reference kernel** (Lean's `infer_lambda`
  does not sort-check the body's type), so it can only *lose*
  completeness — arena 90/92 and e2e 72/72 are the measurement, and any
  loss is a "restrictions are findings" report; and it reverses part of
  #100 stage 6, which that record calls "pure relaxation toward
  reference".  Perf: one extra `whnf` per λ node.
* **B — read `v` off the λ's *type*.**  Available only where the λ's
  type is a stored declaration type (whose front door *does* run
  `ensureSort`, `Checker.lean:272/380`); a λ's inferred type is
  **built**, not inferred, so no `Infer.pi` derivation exists for it in
  general.  Partial and non-compositional; not a repair.
* **C — make the interpretation type-directed** (interpret annotated
  *derivations*, or annotate the λ from the `∀` that types it).  The
  `∀` node's annotation *is* available (I6 runs both `ensureSort`s), so
  this is the repair that needs no kernel change; the cost is tier B's
  `interp2` losing term-directedness, which is an architectural
  decision on tier B's side, not a threading task.
* **D — squash at the rule, not at the interpretation** (λ always a
  graph; proof irrelevance handled by D8/D9 alone).  Reduces to C: the
  membership at a `v = 0` product still has to know it is at `v = 0`.

**Value inspection is not an escape** — tier B's own
`lam_cod_sort_needed` witness has `F x = pt` on both readings, so a
clause that inspects the fibre's *values* fails for the same reason a
clause on `(u, A, F)` does.  That is the point of #151.

### A3 — RULING: **option C** (2026-08-28)

The split moves to the **soundness judgment** (truth-at-`0` /
membership-at-positive), not to the λ node.  Consequences, all
recorded as settled:

* **No kernel change.**  `Core.lean`'s λ clause stays the
  official-kernel `infer_lambda` shape; #100 stage 6 is not reversed;
  the checker does not become stricter than the reference kernel, so
  the completeness risk option A carried never has to be measured.
* **No I7 amendment.**  `Rel.lean` is untouched, premise-exactness
  holds, and `checkStepR` stays proved — which was the whole reason the
  amendment was stopped.
* **`AVExpr.lam` stays as landed**, with the domain numeral only.  It
  is the numeral I7 *does* supply; whether any consumer reads it is
  tier B's C-increment to say, and if the answer is no the follow-up is
  a one-constructor simplification to an unannotated `lam` (nothing
  outside `Annot/Syntax.lean` and `Annotates.lam` would move — `erase`,
  the substitution kit and both erase-commutations are
  annotation-blind by construction).
* **The `AVExpr` swap unblocks when tier B's C-increment lands.**  Tier
  B's F4 stands as a correct refutation of a *term-directed* λ clause;
  option C is the architectural answer to it, and F4's corollary about
  the kernel's `ensureSort` is retracted by the citations above.

## Tier A gate record

`lake build` of the three modules warning-free; `lake test`; arena
90/92, e2e 72/72, split 11/11, mode flags 10/10, tt-model sweep
identical, no-model sweep as expected (1 recorded divergence); axioms
exactly `[propext, Classical.choice, Quot.sound]` or fewer on every
theorem of the tier (`erase_liftN`/`erase_inst` need only `propext`;
`erase_mkAppN` and `ZetaEq.refl` need none); zero sorries; binary cone
untouched (three proof-only modules in `SetlecSetR`, imported by
nothing else).

# Task #151 tier B — option C assessed, and B2 (the constants' towers)

## FINDING B5 (**blocking**) — option C is refuted: the wall is the *proof argument*, not the λ

The F4/A3 impasse was ruled repaired by **option C**: move the
two-regime split from the λ *value* to the soundness *judgment* —
`⟦lam …⟧` uniformly the graph, `pi u v` keeping both numerals, and the
conclusion **graded by the type's kind** (membership above `0`, *truth*
of the type's interpretation at `0`, with the subject never consulted).

Mechanized in `Setlec/SetR/Interp2/Graded.lean` (`Real k x T` is the
graded conclusion, and each rule is stated semantically over the data
it has, as `TierA.lean`'s refutation is).  **Two of the three
representative rules work; the third has a wall.**

| rule | status |
|---|---|
| **I7** (λ), both regimes | ✅ `graded_lam` — *one* statement covers both regimes and reads **no** codomain annotation.  C buys exactly what it promised here. |
| **D8** (proof irrelevance) | ✅ `graded_proof_irrel` — free: the kind-`0` conclusion does not mention the subject. |
| **I8** (app), argument at a positive kind | ✅ `graded_app` — both codomain regimes, one proof. |
| **I8** (app), argument at kind `0` | ❌ `graded_app_zero_dom_refuted` (positive codomain), `graded_app_zero_dom_zero_cod_refuted` (`Prop` codomain) |

**The wall.**  Applying a function to a **proof** needs the proof's
*value* to inhabit its proposition; the graded conclusion at kind `0`
supplies only the proposition's *truth*.  Under C a proof-λ's value is
a graph — concretely `⟦fun (x : False) => x⟧ = graph _ ∅ = ∅`
(`proof_lam_value_ne_pt`) — so `app ⟦f⟧ ⟦a⟧` is off-domain junk `∅`
and the fibre at that junk is empty.  Both witnesses use `A = {•}`,
`B x = ⟦x = •⟧` (a legitimate `Sort 1`-valued family by cumulativity,
`eqvFamily_mem_univ_one`) and the proof argument `∅`.

**Why no re-grading escapes it** (`proof_value_forced`): equality
reflection and `propext` force a proposition's interpretation to be a
subset of the canonical singleton — `propext`'s own graded conclusion
is `eqv ⟦A⟧ ⟦B⟧` inhabited, i.e. `⟦A⟧ = ⟦B⟧`, which fails for
equi-inhabited propositions unless propositions *are* truth values —
so a proof whose value is ever consumed **is** `pt`.  Recovering "which
terms are proofs" is the λ codomain sort again.  Option C therefore
relocates the requirement; it does not remove it.

**Not a corner case.**  `Quot.lift` takes the invariance proof,
`Classical.choice` takes `¬¬A`, `Empty.rec` takes the subject: every
one is an `I8` step at `u = 0`, and each appears in the basis
constants' own application laws (`quotLiftV2_app`, `choiceV2_app` —
both take the proof argument's *membership*, `Interp2/Value.lean`).

**The guard, restated correctly.**  "Kinds are conversion-invariant so
regimes can't mix across `DefEq`" is true *syntactically* (tier A's
unique kinding) and **false semantically**: `kind_not_semantic`
exhibits `unitSet ∈ univ 0` **and** `unitSet ∈ univ 1`.  Cumulativity
means no value-level fact excludes a `DefEq` relating a kind-`0` type
to a kind-`1` one, so any graded statement must carry its kind as data
and can never recover it from `V`.

### Repair B5′ — supply the λ codomain sort as a **metatheorem**, not a runtime check

A3's repair list prices A (kernel change — a new runtime `ensureSort`
that can reject, ruled out), B (read `v` off the λ's type — partial),
C (type-directed interpretation — refuted above) and D (reduces to C).
A fifth is not on the list and appears to dominate:

> The λ codomain sort exists in the **metatheory** even though the
> checker never computes it.  Tier A's `Annotates` is a *relational*
> pass over derivations with existence theorems — not executable kernel
> code — so it may obtain `v` from a **validity (regularity) lemma**
> for the family: *if `Infer Δ b B` then `B` has a sort*, i.e.
> `∃ v, DefEq Δ tB (.sort v)` for `Infer Δ B tB`.

This needs **no I7 premise** (so premise-exactness and
`infer_lam_claimR` are untouched), **no kernel change** (so no new
rejection path and no reversal of #100 stage 6), and no runtime cost.
It answers A3's objection to repair B — "no `Infer.pi` derivation
exists for a built type" — because validity *constructs* the sorting
of the built type from the sortings of its parts rather than reading it
off a derivation.

**What to check before adopting** (tier A's call, since it is their
family): whether validity is provable for `Infer` as landed — the
usual obligations are that stored declaration types are well-sorted
(the `EnvS` invariant should give this), that `whnf`/`DefEq` preserve
sortedness, and the recursor/projection clauses.  If validity fails for
a clause, that clause is the finding.  Recorded as the proposal, not
taken.

## B2 — the built-in constants' towers (`Interp2/Value.lean`)

`Setlec/TT/Semantics/Value.lean`'s `bval` restated over `piR`/`lamR`
(`bval2`).  **Independent of the F4/A3/B5 decision**: `bval2` is
indexed by the constant and its level list, never by a λ *node*, so it
neither needs nor supplies a binder annotation.

*Annotation convention.*  Every λ in a tower carries the tower's
**result sort** `r`.  That is not the exact `imax` fold at each binder,
but it agrees with it on the only thing `piR`/`lamR` read
(`imax x y = 0 ↔ y = 0`, `imax_eq_zero_iff`), and
`lamR_mem_zero_agree` is the bridge for a consumer wanting the exact
annotation.  *Domains* carry exact sorts, because that is what
consumers' hypotheses are stated with: motive spaces are
`piR (r+1) …`, the relation space is `piR (max u 1) …` (`A → Prop` is a
*type* — its codomain `Prop = Sort 0` lives in `Sort 1`, a place it is
easy to get wrong), and the invariance / double-negation spaces are
`piR 0 …` throughout.

*The law surface, as priced.*  Each application law splits by regime:
at `r ≠ 0` it is `app_lamR_pos` — **fewer** hypotheses than the
collapse version needed; at `r = 0` the tower *is* the canonical proof
and the law holds only because both sides are, which is the pre-#100
`v = 0 → the fibres are truth values` premise resurfacing.  **No
statement grew a premise**: each law discharges the `r = 0` case from
its own motive/fibre hypothesis (`natRecV2_app` from `hM`,
`punitRecV2_app` from `hM`, `quotMkV2_app` from `hA`, `choiceV2_app`
from `hh` via `exists_mem_of_dneg2`).  The one place a premise *is*
taken is `quotLiftR_mem`'s `hB0 : v = 0 → B ∈ˢ univZero` — the codomain
is an argument there, so no other hypothesis carries it.

*Two values change.*

* **`Empty.rec` was `pt`; it no longer is.**  Under the collapse its
  inner λ has an empty domain and `lamC_empty` collapses at *every*
  level; two-regime it is `lamR v … (lamR v ∅ …)` — the empty graph at
  `v ≠ 0` (`emptyRecV2_ne_pt`), the canonical proof at `v = 0`
  (`emptyRecV2_zero`).  This is the #100 countermodel's cause showing
  up in the basis.
* **`SetTheory.quotLift` is `lamC`-built**, so tier B carries
  `quotLiftR` — the same abstraction at an annotation.  It is the
  **only** `SetTheory` operator this file must replace: `natrec`,
  `schoice`, `quotSet`, `quotClass`, `qrep`, `sigmaSet`, `sfst`/`ssnd`
  are collapse-free, and `sigmaSet`/`quotSet`/`quotClass` are already
  *annotation-driven* — the recorded precedent this tier follows.

`PSigma'.mk`'s explicit `if max u v = 0 then pt` tag is **gone from the
definition** (the annotation squashes the whole tower at `0`), though
`psigmaMkV2_app` still states the `if`-form so its consumers are
unchanged.

*Coordination with tier A.*  `Interp2/Syntax.lean` now carries
`const (c : BConst) (us : List Nat)` — tier A's node **verbatim** — and
`interp2`'s clause is `bval2 V c us`.  The provisional syntax's only
remaining difference from tier A's is the `lam` numeral, i.e. exactly
the F4/A3/B5 decision.

## Housekeeping

`Setlec/SetR/Interp2/Value.lean` reached master in commit `121fded`
**swept from another agent's shared working tree while it was still
unbuilt and unimported** (the same sweep the tier-A record notes for
`Annot/*`).  It is compiled and wired as of this branch.  Tier B works
in `.claude/worktrees/tier-b` on `feat/151-tierB` from here.
## T5 stage 3 landed (2026-08-28) — the recursor group, end to end

`iotaRuleS` (`Install/IotaRuleS.lean`) and `indRecsS`
(`Install/IndRecsS.lean`) close stage 3.  Three records worth keeping.

### The rule kits are checked against the accumulator, not the self env

`IotaRulesR`'s environment argument is `IndRecsFoldR`'s *running
accumulator* — `envSelf` with some of the group's recursors already
carrying their rules.  So the natural-looking hypothesis

> every lookup in the kit's environment is a lookup in `envSelf`

is **false**, and false exactly at the group's own recursors.
`iotaRuleS.hup` is therefore a *correspondence*: a lookup either agrees
or differs only in a recursor's rule list.  Its three uses survive:
two are at non-recursor kinds (the constructor, `Eq`), and the third —
the `iota_j` statement's stored entry — reads only `toConstantVal`,
which a swap preserves.  (That third one is why the correspondence has
to carry the swapped entry's `ConstantVal`, not merely say "or it is
some recursor".)

This is also why `indRecsFoldS` runs the **provisioning and the
install fold in step**, as one induction over `recs`: the pairing is
what makes the correspondence available at each kit.  The provisioning
alone cannot supply it (it never sees the ruled entries) and the
install fold alone cannot either (it never sees the rule-less ones).

### Two keyings of the same information, both needed

`indRecsFoldS` returns the swapped entries' facts twice — once keyed
by **membership** (`∀ c ∈ env₃.consts`) and once by **`find?`**.  That
is not redundancy: `EnvWF` quantifies over `env.consts` while
`RecCtorsStored`/`RecRulesV` key on lookups, and *nothing in `EnvS`
forbids two entries under one name*, so neither form implies the
other.  Both thread through the induction for free — the `find?`
form's base case is exactly provisioning monotonicity, the membership
form's is provisioning's `mem` monotonicity.

A general lesson for the tier: when a fold's output feeds both a
list-quantified and a lookup-quantified consumer, produce both; do not
try to bridge them with a nodup invariant the structure does not have.

### `RecRuleLawV`, factored

`RecRulesV` (`Sound/Motives.lean`) is now `∀ stored recursor, ∀ fired
rule, RecRuleLawV …`.  A *single rule's* law is what `iotaRuleS` hands
back and what has to cross the rule-list swap, and it deserved a name;
`RecRuleLawV.swapS` is its transport, five lines, because the law
reads the environment only through `denote` and the constructor's
lookup.

Two relocations came with the stage, both verbatim, both because the
fact is about `Expr` or `denote` and neither lane owns it:
`recRulePlain_leT`/`_le_mIT`/`recFireComparands_plain`/`_nested` to
`Verify/InstSpine.lean` (the residue T1 did not cover), and
`nestedLvlsLength` to `Verify/Denote/IndFrame.lean` — the nested
bottom's `hlvlsLen`, which **no checker comparison establishes**: it is
forced semantically, the statement's major applying `f ctor` at `lvls`
and `denote`'s `.const` clause being guarded on the stored arity.

## FINDING 6 (**blocking, stage 4**) — the capability keys are stated one environment too late

**Raised at the stage-3/4 boundary, before any of stage 4 was
written.**  Not finding-#1 territory (no missing checker check); the
same class as FINDING 4 and `EnvR.rec_rhs_denotes` — an interface
stated for the environment its designer had, not the one its consumer
has.  It is **blocking**: stage 4 cannot start until it is decided.

### The wall

`EnvS.cons`'s `hheadUnit` obligation is

```
∀ cv caps, c₀ = .indInfo cv caps → caps.unitlike = true →
  reservedBasisNames.contains c₀.name = false →
  UnitLawV V ⟨c₀ :: env.consts⟩ cval' c₀.name cv caps
```

— the law **at the extension**, with only `m : EnvS V env` in hand.
`unitLawKeyS : UnitLawKeyS V` (c5) instead takes
`mS : EnvS V envS` and concludes `UnitLawV V envS mS.cval …`.  Applying
it at `envS := ⟨c₀ :: env.consts⟩` needs an `EnvS` there, which is what
`EnvS.cons` is *building*.

And the circle is real, not cosmetic.  `unitLawKeyS` uses `mS` five
times: `cval_closed`, `val_params`, `mem_type`, `wf`, and
`toHyp ψ'` — the last feeding `fireS`.  `EnvSHyp` **contains
`caps_ok : CapsOkV`**, so "the bundle at the extension" already
contains the very law being proved.  `etaLawKeyS` has the identical
shape (same five uses, same single `fireS` call), so stage 5's
projection install hits the same wall.

### Why it is repairable, and cheaply

The apparent circularity dissolves once one notices **where the
semantic content actually comes from**.  `UnitLawKeyS`'s hypotheses are
*all syntactic pins* (`stripPis`, `getAppArgs`, `eqUpToNames`) — there
is not one `Infer`/`DefEq` walk among them.  The only semantics enter
through `mS.mem_type` of the `T._model.unitlike` **theorem**, and that
theorem is stored in `env`, below the extension.  So every soundness
run can happen at `env`, with `m.toHyp` — no circularity — and only
the *statement* needs moving up.

The TT lane already does exactly this: `modeledCapsUnitTT`
(`TTVerify/DeclIndMember.lean:329`) takes the pre-extension `m`,
pulls the artifacts' lookups down with `member_below`, and pushes the
denotations up with `hi.denoteUp`.  It takes `hcl`/`hvp` as *explicit
hypotheses* rather than as `m`-fields, which is precisely the shape
that dodges the bundle.

### Priced options

1. **One-step-ahead restatement** (recommended).  Give
   `UnitLawKeyS`/`EtaLawKeyS` `mS : EnvS V env`, an abstract `cval'`,
   `hi : Installs env mS.cval cval' c₀`, the artifacts' lookups **at
   `env`**, and the conclusion at `⟨c₀ :: env.consts⟩`.  The bodies
   survive: they run at `env` throughout (so `fireS` gets
   `mS.toHyp ψ'`, valid), and the boundary transport is
   `Installs.denoteUp` plus `denote_cval_congr` off the fresh name —
   both already in `Verify/Denote/Install.lean`.  The consumer's
   pull-down is `member_below`, already shared.  Estimated cost:
   the two signatures, ~40 lines of boundary plumbing each, plus the
   `cval'`-for-`mS.cval` renaming through two ~450-line proofs (a
   mechanical substitution, since `mS.cval` appears there only as *a*
   valuation).
2. **Weaken `EnvS.cons`'s obligation** to receive the fields it has
   already established.  Rejected on inspection: `toHyp` needs
   `caps_ok`, so the obligation cannot be handed a usable bundle no
   matter how `EnvS.cons` is re-ordered.
3. **Split `EnvSHyp`** into a caps-free core plus `caps_ok`, and
   premise `fireS` on the core.  Cleanest in principle and would also
   pay off wherever else the bundle is over-strong, but it re-signs a
   T4-frozen interface and every `fireS` caller; strictly more
   expensive than (1) for the same payoff here.

**Not affected**: `MemberKeyS` (states and concludes at the same
environment), and the three value-kind obligations.

## FINDING 6 RESOLVED (2026-08-28) — option 1, the one-step-ahead restatement

Decided by the coordinator, landed as priced.  The classification line
stands verbatim: **not finding-#1 — an interface stated for the
environment its designer had, not the one its consumer has**, the same
class as FINDING 4 and `EnvR.rec_rhs_denotes`.

### What changed

`EtaLawKeyS`/`UnitLawKeyS` now take, alongside the model `mS` at the
*smaller* environment, an installed valuation and its install:

```
{cval' : TConstVal} {c₀ : ConstantInfo}
(_hi : Installs envS mS.cval cval' c₀)
(_hcl : ∀ n ψ, VExpr.Closed (cval' n ψ))
(_hresT : ∀ us, (cvT.type.instantiateLevelParams …).constsResolve envS = true)
```

and conclude `EtaLawV V ⟨c₀ :: envS.consts⟩ cval' …`.  Every pin that
mentioned `mS.cval` now mentions `cval'`; the two proof bodies were a
**mechanical substitution** — they compiled unchanged on the first
attempt — because `mS.cval` occurred in them only as *a valuation*.

Five bridge points needed real content, all in the new
`Install/CvalStep.lean`:

| bridge | how |
|---|---|
| `denote_cvalStep` | the valuation change at a fixed environment — *unconditional*, since `denote` returns `none` at an unresolved constant |
| `EnvS.mem_type_step` | the artifacts' front doors at `cval'` |
| `EqLawV.cvalStep`, `EqFormerKeyV.cvalStep` | the pinned `Eq`'s law and firing key at `cval'` |
| `EtaLawV.up` / `UnitLawV.up` | the statement's own move, `Installs.denoteDown` ∘ the valuation change |

`hcl` had to become a *hypothesis* rather than a derived fact: `cval'`
at `c₀.name` is only pinned down when `c₀` is the family's former, its
constructor, or one of its projections, and the key must also hold at
installs that are none of those.  The consumer has it — it is
`EnvS.cons`'s own `hclosed` obligation.

### The load-bearing sub-repair: `fireS` no longer takes `EnvSHyp`

The circularity was never in the key lemmas' *content*; it was in one
parameter.  `fireS` took the whole `EnvSHyp` and used exactly two of
its nine fields — `cval_closed` and `mem_type`, both only at
`eqName`.  Those two are now `EqFormerKeyV`, and
`EnvSHyp.eqFormerKey` builds it at the sites that have a bundle (the
three iota bottoms, unchanged one line each).

This is **not** option 3.  Option 3 was to split the T4-frozen
`EnvSHyp` itself and re-sign every consumer of the bundle across the
tier.  What landed narrows *one internal helper's* parameter to the
facts it already used, at five call sites, all inside `Install/`.
`EnvSHyp` is untouched.

**General lesson, worth carrying past T5**: a helper premised on a
whole environment bundle cannot be used to *establish* any field of
that bundle.  When a bundle field's own proof runs through a shared
engine, the engine must be premised on the fields it uses, not on the
bundle.  Check this at the point a new `EnvSHyp` field is added, not
at the point its supplier is written.

### `nestedLvlsLength` — for the #151 record

Stage 3b's relocation is another instance of the pattern #151 is
about: **information the semantic side demands that the syntax never
carried.**  `hlvlsLen` (`lvls.length = cvj.levelParams.length`) is
established by *no checker comparison*.  It is forced only
semantically — the statement's major applies the constructor family at
`lvls`, and `denote`'s `.const` clause is guarded on the stored arity,
so a mismatched `lvls` makes the statement fail to denote at all.  The
checker never has to look; the model has to prove it.

## T5 stage 4 (2026-08-28) — the asymmetric discharges, and a correction

### `MemberUnitS`: discharged, after being re-signed

The obligation as first stated was **not provable**, and the reason is
worth keeping: `caps.unitlike = true` on an *abstract* `caps` says
nothing.  The caps an install stores are `indBlockCaps`' output, and
its two Booleans are exactly `checkEtaThm`/`checkUnitThm`, which invert
to the artifacts' shape pins.  That inversion is the shared, V-free
`EtaPins` (`Verify/Extend/Iota.lean`), and it is what `unitLawKeyS`
consumes.  So `MemberUnitS` now takes `MemberValR` + `BlockInstalledTT`
+ `EtaPins`, in the same shape the Model lane's `checkIndMember_sound`
has always used, and the block folds thread it with `EtaPins.step`.

The discharge itself is short, and confirms c5's observation: the
unit-like law is the *easy* half of the pair because it fabricates no
side — both of its subjects are given, so all that is left is moving
the model's facts onto the installed valuation.

### `MemberEtaS`: **not** a member-fold discharge — the handoff was wrong

The T5 handoff said `MemberEtaS` is "gated and therefore vacuous during
both member folds".  That is **false**, and the counterexample is
inside `EtaFamilyStored` itself: with `caps.etaFields = 0` the
projection conjunct is vacuous, so the family completes as soon as its
*constructor* is stored — which happens inside the member fold.  A
0-field eta-capable structure is exactly that case.

Working the cases out properly:

| case | why |
|---|---|
| family already complete in `env` | **impossible** — the head disjunct puts `c₀.name` at `T`, the ctor, or a projection, and `c₀.name` is fresh |
| `projFnName T j = c₀.name` | **impossible** — `ConstantValR` pins `cv.name.isProjFnShape = false` |
| completing, `etaFields > 0` | refuted, but only from `DeclIndR`'s `(envR.find? (projFnName cvT.name j)).isNone` conjunct — an **assembly-level** fact |
| completing, `etaFields = 0` | **live**; `etaLawKeyS` fires with its projection premise vacuous |

Both live rows need facts the fold does not have (the run's freshness
facts; the block's identification of `T`).  So `MemberEtaS` stays a
*forwarded* obligation, discharged at the `DeclIndS` assembly — which
is precisely what the Model lane already does and says:

> the eta head obligation is *forwarded* to the caller … only the
> caller knows whether the member completes a family
> (`Model/Extend/Ind.lean:22`)

It is re-signed then, with its consumer, per the house rule.  The
asymmetry the handoff named is real; its *explanation* was not.

**Method note**: the handoff's error came from reasoning about
`EtaFamilyStored` from its name and purpose rather than from its
text.  Both wrong steps this session (this one and finding 6's
"`unitLawKeyS`'s inputs are available there") were of that shape —
a premise checked for the *data* it needs and not for the *environment*
or the *degenerate case* it quantifies over.

## Stage 5's shape, scoped (2026-08-28)

Scoped from `ProjFnR` and `EnvS.cons` before writing any of it, so the
next pass starts from the obligation list rather than deriving it.

One field's install is `EnvS.cons` at
`c₀ = .recInfo ⟨projFnName T i, lps, pty⟩ nP nP [rule]` with
`cval'' = cvalWith cval (projFnName T i) (fun ψ => cval (projModelName T i) ψ)`.
Of `EnvS.cons`'s sixteen obligations:

| obligation | source |
|---|---|
| `hwf` | `ProjFnR`'s syntactic pins on `pty` and `rhsA` |
| `hheadCtors` | `ProjFnR`'s first conjunct (the constructor's lookup) |
| `hheadRec` | **`indBottomProjS`** — the only heavy one, and it is already proved (c4) |
| `hclosed`, `hparams`, `hannot` | `m`'s fields at `projModelName T i` |
| `htype` | **new named obligation** (`ProjKeyS`) — the model projection's value inhabits the *renamed-back* public type `pty`; the projection counterpart of `MemberKeyS` |
| `hheadEta` | the live capability case — see below |
| `hheadUnit`, `hheadProj`, `hheadProjPair`, `hheadNat`, `hheadDivMod`, `hheadReduce` | vacuous: the head is a `.recInfo` |
| `hempty`, `hheadEq`, `hheadBasis` | name distinctness (`isProjFnShape`) |

The fold threads the invariant
`∀ j ≤ i, ∀ ψ, cval (projFnName T j) ψ = cval (projModelName T j) ψ`.
It survives later steps because step `k` writes only `projFnName T k`,
which is neither `projFnName T j` (`k ≠ j`) nor `projModelName T j`.

**The eta head, at a projection install** — *corrected 2026-08-28,
after landing stage 5a*.  The prediction above (that `ProjEtaS` would
be forwarded like `MemberEtaS`) was **wrong**, and wrong for the P2
reason yet again: the head disjunct had to be read, not summarised.
At a projection install the head is a `.recInfo`, so

* `T' = c₀.name` puts a `.recInfo` where the family's own lookup
  demands an `.indInfo`, and
* `caps.etaCtor = c₀.name` puts one where `EtaFamilyStored` demands a
  `.ctorInfo`,

both immediately absurd.  Only the projection disjunct survives, and
it *pins* `T' = T` and the field index.  So the obligation is
discharged **in-fold**, by `etaLawKeyS` one environment ahead — which
is exactly the shape finding 6 produced.  This also makes the Model
lane's `hbshape` premise unnecessary here: refuting by the stored
*kind* is cheaper than refuting by the name's shape, and independent
of the block.

## T5 stage 5a landed; what `projFnS` still needs (2026-08-28)

`ProjPhaseInvS`, `projFwd_renameOkT` and `projProvisionS` are in
`Install/ProjInstallS.lean`, warning- and sorry-free.

### The architecture is forced, not chosen — **retracted 2026-08-28**

The claim was: the projection recursor cannot be consed with its rule
and then have `indBottomProjS` fire at the result (P1 — the bottom is
premised on an `EnvS`, and `hheadRec` is a field of that bundle), so
*provision → fire → swap* is mandatory.

**The P1 diagnosis is right; the remedy was wrong, and it was not the
cheap one.**  P1 says the helper cannot be premised on the bundle *at
the environment where its conclusion lives*.  Provisioning is one way
out.  The other — the one that costs nothing — is to **re-aim the
helper below**: `checkProjFn` runs every one of its checks *before*
the recursor is stored, so the whole kit already lives at the base
environment, and instantiating the bottom at
`Rn := projModelName T i` (the model's name, which the pinned
statement's head names anyway) makes its conclusion a law about
`cval (T._model.proj_i)` — which at the cons is definitionally the
installed constant's valuation, by `cvalWith_self`.

The provisioning route additionally needs the sides pack transported
from the base to the extended environment, and **nothing tools that**
(the relation family has context weakening, not environment
monotonicity).  So the retracted plan was not merely more expensive:
it was blocked.

The TT lane records the same reading at `TTVerify/DeclIndProj.lean`'s
"Where the bottom runs", which is where it should have been read
first.  Recorded as a **P2 near-miss of a new kind**: not a premise
misread, but *a practice applied without looking for its second
remedy*.  P1 tells you a route is closed; it does not tell you which
of the open ones to take.

Two premises the Model lane's `checkProjFn_sound` carries turned out
to be unnecessary: `hbshape` (see the corrected note above) and
`hptyB` (the roundtrip equation alone identifies the denotation).

### `projFnS`'s remaining work, precisely

1. **The phase invariant at `env₀`** (the rule-less extension): the
   `j = i` conjunct is `cvalWith_self`, the rest is `hinv` transported
   over a fresh cons.  This is what `projFwd_renameOkT` then consumes,
   and note that at `env₀` the *pruned* and *full* projection maps
   coincide, because `projFnName T i` is stored there — which is why
   the Model lane's separate `f`/`f₀` pair is not needed.
2. **The bottom's pins**, all from `ProjFnR` transported up by
   freshness; `_hrhsKey`'s semantic form comes from `Infer.sound` at
   `env'` with `m.toHyp` (the `iotaRuleS` pattern).
3. **The bridge** from `indBottomProjS`'s conclusion to
   `RecRuleLawV`'s body.  Three small gaps, all already tooled:
   `recFireComparands_plain` (relocated in stage 3b) for the level
   comparand, `ProjFnR`'s `hctor` plus injectivity for the `find?`
   premise that fixes `cvj cnP cnF`, and `mI = rP = nP` for `rP ≤ mI`.
   The `.inert` case is vacuous against `RecRulesV`'s own
   `fire ≠ .inert`.
4. **The swap**: `SwapShList.cons (Or.inr ⟨…⟩) (SwapShList.of_eq _)`,
   `SwapNResS` at the head from `reservedBasisNames_not_num`, and the
   three global facts (`EnvWF`, `RecCtorsStored`, `RecRulesV`) as in
   `indRecsS`.

### Landed, 5b part 1

`projPhaseInvS_cons` (parameterised by the head entry, since the
invariant never reads a rule list), `projFwd_model_self`, the
generalised `projConsS` (the rule list is the caller's), and
`projFnS`.  Two supporting facts were needed and are now shared:
`Name.str_str_ne` (`Verify/EnvWF.lean`) and the twelfth relocation —
`openPisAtFvars_instSeq`, `range_map_getD_prefix`/`_suffix` and
`projStmtParts` to `Verify/Denote/TeleOpen.lean`.

`ProjFnR` gained the pin it was missing: `checkProjIota`'s **body
match**.  The relation stopped at the domain match and the sides pack,
so the statement's `Eq`-spine shape — which the bottom needs and the
checker does pin — was absent.  D6 reserved exactly this refinement
for its first consumer, and `projFnS` is it.  (`ProjFnR` has no
producer yet — that is T6 — so the refinement cost nothing.)

Then the fold (`projInstallS`) threads `ProjPhaseInvS` +
`BlockInstalledTT` over `List.range nF`, with the skip branch a no-op.

## T5 stages 5–6 landed; what the `DeclIndS` assembly needs (2026-08-28)

Stages 1–6 are done.  `Install/ProjInstallS.lean` holds
`ProjPhaseInvS`, `projFwd_renameOkT`, `projPhaseInvS_cons`,
`projFwd_model_self`, `projConsS`, `projFnS`, `projInstallS`,
`templateVal`, `templateConsS`, `templatesS` — all sorry-free.

### Two relation refinements landed with their consumers

* **`ProjFnR` gained `checkProjIota`'s body match.**  The relation
  stopped at the domain match and the sides pack, so the statement's
  pinned `Eq`-spine — which the projection bottom needs, and which the
  checker does pin — was simply absent.  D6 reserved that refinement
  for its first consumer; `projFnS` is it.
* **`TemplatesR` lost its valuation entirely.**  The other block folds
  thread a `TConstVal` because their members *alias* their model
  artifacts, a checker-side fact.  A template entry exists precisely
  because the field has no artifact — nothing to alias — and the
  relation as written (`∃ Vt, cval'' = cvalWith cval … Vt`) forced the
  soundness side to model a valuation the relation had picked
  *arbitrarily*, which is not provable.  Dropping it is simpler and
  strictly more faithful: `installProjTemplate` never touches a value.
  This is a **P2 instance in a new place**: the premise was read for
  what it supplied (a valuation) and not for the fact that it
  quantified the valuation existentially, i.e. universally for the
  consumer.

### The eta head, discharged three different ways

Worth collecting, because each is cheaper than the last and none is
the vacuity argument the T5 handoff predicted:

| site | why |
|---|---|
| member fold | **forwarded** — needs assembly-level facts (stage 4) |
| projection install | the head is a `.recInfo`, so the first two head disjuncts want an `.indInfo`/`.ctorInfo` and get a `.recInfo`; the surviving disjunct pins `T` and the index, and `etaLawKeyS` fires |
| template install | the head is a `.projInfo`, so **every** `EtaFamilyStored` lookup finds the wrong kind |

### The assembly's remaining work, precisely

`declIndS` composes `indMembersS`, `indRecsS`, `projInstallS`,
`templatesS`.  All four exist; what is missing is **monotonicity
plumbing** the folds do not currently expose.  Enumerated:

1. `BlockInstalledTT blockNames env cval` **at the start** — vacuous,
   but only because no block name is stored in `env`, which is the
   chain of `ConstantValR` freshness facts.  Needs a small lemma over
   `IndMembersR`/`ProvisionRecsR`.
2. `hbn` for both folds — pure list reasoning from
   `blockNames = block.map (·.name)` and `block = nonrecs ++ recs`.
3. `hall` for `indRecsS` — needs `indMembersS` to report *each
   installed member is stored*.
4. `hpinsT` at `envR` — `EtaPins` is built at `env` by
   `checkEtaThm_inv`/`checkUnitThm_inv` (shared; the Model lane's
   `hpinsT0` at `Extend/Decl.lean:161` is the pattern), then moved up
   by `EtaPins.step` through the member conses and by
   `EtaPins.transport` across the group swap.  **`indRecsS` should
   return its `SwapCongr envSelf env₃`** — it already computes it.
5. `hCblock`/`hFields` — `rfl` from `indBlockCaps`, once the stored
   `T` is known to carry the fold's `caps`.
6. `ProjPhaseInvS … envR cvalR` — the `T`/ctor conjuncts from
   `BlockInstalledTT` at `envR`; the projection conjunct is vacuous by
   `DeclIndR`'s own `(envR.find? (projFnName cvT.name j)).isNone`
   conjunct.
7. `hbshape` and `hTnres` — from each member's `ConstantValR`
   (`isProjFnShape = false`, `reservedBasisNames.contains = false`).

So the shape of the work is: **re-sign the four folds to report what
they preserve**, then the assembly is bookkeeping.  The TT lane's
`declIndTT` (`TTVerify/DeclIndDecl.lean:77`, ~1050 lines) is the
template; expect the [set] one to be comparable.

`DeclBasisS` is independent of all of this
(`TTVerify/DeclBasis.lean` is its template).

## T5 — `declIndS` lands; the inventory T6 consumes (2026-08-28)

`Install/DeclIndS.lean` discharges `DeclIndS`, the sixth and last
per-kind obligation of `declStepS`'s dispatch.  With it, **everything
in T5 except `DeclBasisS` is done.**

### What the assembly needed, and where P1a paid

Read the sibling lane first: `declIndTT` uses separate V-free
monotonicity lemmas *about the checker run* rather than fold-returned
facts.  In [set] the folds already compute the same information, so
the analogues are relational and small — `indMembersR_mono`,
`_stored`, `_fresh`, `_nameGuards`, `_indEntry`;
`provisionRecsS_fresh`, `_nameGuards`; `indRecsR_fresh`,
`_nameGuards` — plus `indRecsS` returning the non-recursor transport
and `isSome` congruence it already had in scope.  That transport is
**exactly** `EtaPins.transport`'s `hkeep` premise, which is why it was
worth returning rather than re-deriving.

`etaPins_of_indBlockCaps` is the one new ingredient: the capability
record's two Booleans *are* `checkEtaThm`/`checkUnitThm`, so they
invert to the artifacts' shape pins.  Paid once at the assembly, for
the whole block.

A trap worth naming: the block's two **singleton-filter pins cannot be
consumed by writing their predicate out** — the `match`'s elaborated
form differs from anything one types.  `hmemFil`/`hsingle` are generic
in the predicate so unification takes the relation's own.

### T6's interface: the open obligations, complete

`declStepS` is proved from six; `declIndS` from two more.  What
remains open, and nothing else:

| obligation | where | note |
|---|---|---|
| `MemberKeyS` | `Install/IndMembersS.lean` | the block member's key: the model artifact inhabits the checked member's type |
| `MemberEtaS` | `Install/IndMembersS.lean` | the eta head at a member install — **forwarded by design** (stage 4's record) |
| `DivModPinS` | `Install/Value.lean` | |
| `StdAxiomKeyS` | `Install/Axiom.lean` | |
| `OfReduceKeyS` | `Install/Axiom.lean` | |
| `DeclBasisS` | `Install/Step.lean` | the pinned basis blocks — see below |

Proved in T5: `reducePinS`, `memberUnitS`, `etaLawKeyS`,
`unitLawKeyS`, `indBottomPlainS`, `indBottomNestedS`,
`indBottomProjS`, `declIndS`, and the per-kind value/axiom lemmas
`declDefnS`/`declThmS`/`declOpaqueS`/`declAxiomS`.

### `DeclBasisS`, scoped — **and there is no shortcut**

`BasisInstallR` is trivial (a fold of fresh conses of the *pinned*
declarations, `kind.declsA`), so the work is entirely `EnvS.cons`'s
~20 obligations per pinned constant, over six kinds
(`eqK`/`natK`/`psigmaK`/`punitK`/`emptyK`/`quotK`).  The TT lane's
counterpart, `TTVerify/DeclBasis.lean`, is **4766 lines** — the
largest file in the campaign.  Expect comparable, though the shared
V-free backbone (`pinnedDirectT`, `BasisPinnedTT`, `ProjOkT`,
`RecCtorsStored`) should take a real bite out of it.

**The obvious shortcut does not exist, and it is worth recording why**
so nobody spends a day on it.  One might hope to transport the *Model*
lane's basis install (`Setlec/Model/*`), since `EnvS` and `EnvModel`
are both set-model structures where `EnvTT` is a typing structure.
They are not interchangeable in the needed direction:

* `EnvModel.val : ConstVal V = Name → (Name → Nat) → V` — a set
  **element**;
* `EnvS.cval : TConstVal = Name → (Name → Nat) → VExpr` — a
  **syntactic representative**, interpreted afterwards by `interp ρ`.

`EnvS` is strictly finer: committing to a `VExpr` is what makes
`AnnotOkV` and the `interp`-equalities statable at all.  From
`val n φ : V` no `VExpr` can be recovered, so the transport runs
`EnvS → EnvModel`, never back.  The pinned valuations must therefore
be given as `VExpr`s — which is exactly what the shared
`pinnedDirectT` already does, and which is the right starting point.

## `DeclBasisS`: the `Empty` pilot, and what it measured (2026-08-28)

`Install/BasisS.lean` holds the shared half — `basisEtaVacuousS`,
`basisUnitVacuousS`, `cvalS_pinned`, `extendBasisS` — plus the `Empty`
block (`extendEmptyS`, `extendEmptyRecS`, `declBasisS_emptyK`).

### The saving that is real: `HasType.sound`

`EnvS.cons`'s `htype` wants
`interp ρ (val φ) ∈ˢ interp ρ t`; the TT lane's counterpart proves
`HasType [] (val φ) t`; and **`HasType.sound`
(`TT/Semantics/Soundness.lean`) turns the second into the first**.  So
every pinned constant's *membership* is one application away from the
derivation the TT lane already writes, and the two lanes do the same
type computation rather than two different ones.

This does **not** couple the lanes: `Setlec/SetR/*` does not import
`Setlec/TTVerify/*` and must not.  What both sit on is `Setlec/TT/*` —
the judgment and its soundness — which is shared already.

### The cost that is real: `AnnotOkV`

The [set] lane's extra conjunct is `AnnotOkV ρ t`, and there is **no
general `HasType → AnnotOkV` lemma** to lean on.  It would need
well-formed *contexts*: `AnnotOkV`'s `lam`/`pi` clauses demand the
binder domain be truthful, and TT's rules do not premise a λ-domain's
sort, so a garbage domain types fine and is not truthful.  Per
constant it is mechanical — unfold, and each application node's
premise comes from the binder's own `Sat` membership — but it is not
free.

### The measurement, and a correction to the size expectation

The campaign constant "[set] transpositions come in at roughly half
the TT lane's size" **does not hold for this file's non-recursor
content**.  `Empty` is TT 159 lines vs [set] 173 — about 1.1×, because
TT's content there is a `HasType.const` one-liner while [set] adds the
`AnnotOkV` computation.  The half-size saving comes from *fired-form
eliminations replacing `Deq` assembly*, which is recursor content —
so expect it in `Nat`, `PSigma'`, `Quot` and `Eq`, and **not** in the
type computations.

Blocks remaining, with TT-lane sizes as the yardstick: `PUnit` 379,
`Quot` 481, `Nat` 624, `Eq` 729, the `Eq`-bridged families 830,
`PSigma'` 1025 — 4068 TT lines.  A mixed factor puts the [set] total
at roughly **2500–3500 lines**.  This is the campaign's largest single
remaining piece and is properly several sessions; the per-block
sub-stage discipline (one block, landed with the battery) is what
keeps it tractable.

## `DeclBasisS` continued: `PUnit`'s non-recursor half, and the two
levers the next pass should pull first (2026-08-28)

Landed on top of the `Empty` pilot: `denote_const_pinS` (a pinned
constant already stored denotes to its pin), `extendPUnitS`,
`extendPUnitUnitS`.  Both compiled first try — the non-recursor
constants are now a rote pattern.

### Lever 1 (found, used): the layer's iota laws are **value**
equations

`punitRecV_app`, `natRecV_app`, `psigmaV_app`, … in
`TT/Semantics/Value.lean` take *membership* hypotheses and conclude
`app (app … ) … = …` as an equation between elements.  Membership is
the [set] lane's currency, so a recursor's `hheadRec` reads its iota
law straight off one of these and β-reduces the reduct with
`app_lamC`.  The TT lane instead assembles a `Deq` chain out of typing
rules and cannot use them.  **This is where the campaign's "[set] is
half the size" constant comes from**, and it applies to recursor
content only — the earlier measurement (`Empty` at 1.1×) stands for
type computations.

### Lever 2 (identified, NOT yet built): `AnnotOkV_bconst_type`

`EnvS.cons`'s `htype` wants `AnnotOkV ρ t` beside the membership, and
for every pinned constant `t` is `BConst.type c us`.  So **one lemma
kills that obligation for the whole basis**:

```
theorem AnnotOkV_bconst_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    AnnotOkV V ρ (BConst.type c us)
```

It is true and mostly automatic.  A `cases c` followed by
`simp only [BConst.type, arrow, AnnotOkV_*, interp_*, …]` and a
`repeat' first | trivial | exact ⟨_, _, ‹_›, ‹_›⟩ | … | apply And.intro
| intro _` loop closes all but **24 goals, confined to six
constants** — `natRec`, `psigmaMk`, `quotMk`, `quotLift`, `quotInd`,
`quotSound`.  Every residual goal has the same shape:

```
∃ A B, <bval c us, or a partial application of one> ∈ˢ piC A B ∧ <arg> ∈ˢ A
```

and the fact that discharges it is **`bval_mem_type`**
(`TT/Semantics/ConstOk.lean:245`), `bval V c us ∈ˢ interp V ρ
(BConst.type c us)`, composed with `app_mem_piC` once per application
already consumed.  Two blind attempts at a generic closer (`exact
⟨_, _, bval_mem_type _ _ _, ‹_›⟩` and a `simpa … using` variant) both
failed to fire, almost certainly because the `∃ A B` metavariables are
not solved through `interp (BConst.type …)`'s unfolding.  **Do not
guess a third**: write the six cases out, `show`-ing the `piC` form
explicitly.  That is perhaps forty lines and it unblocks every
remaining constant's `htype`.

### Order for the next pass

1. `AnnotOkV_bconst_type` (six explicit cases) — unblocks all `htype`s.
2. `extendPUnitRecS` — the lane's first recursor; its `hheadRec` is
   `punitRecV_app` plus two `app_lamC` β-steps, and its `AnnotOkV`
   transport conjunct is `TeleFitV.appN_annot`
   (`SetR/AnnotOkV.lean:333`), which is the factory for exactly that.
   Land the `PUnit` block.
3. `Nat`, `Quot`, `Eq`, `PSigma'`, the `Eq`-bridged families — in that
   order (increasing recursor complexity), one block per landing.

Two more relocations came with this pass: `projFnName_ne_reserved` to
`Verify/EnvGuards.lean` (thirteenth) and the `Expr.instantiate1_*`
simp set to `Verify/Subst.lean` (fourteenth) — both V-free, both
needed by each lane's basis file.

## Lever 2 landed; `extendPUnitRecS`'s exact blocker (2026-08-28)

### `AnnotOkV_bconst_type` is proved — every pinned type is truthful

Built longhand as the record instructed, and the record's diagnosis
was right in substance but wrong in cause.  **Why the generic closers
failed**: the `∃ A B` metavariables must be fixed by the *head*'s
membership, and `bval_mem_type` cannot supply them with `c` and `us`
left as placeholders — there is nothing to solve them from.  Naming
the constant (`bval_mem_type V .quot [lv us 0] ρ`) fixes it, and 22 of
the 24 close as one-liners.  The other two need `rename_i`: their head
is a bound *relation* applied to one side, and an anonymous
`assumption` picks the wrong binder.

Its payoff is immediate and permanent: `AnnotOkV_bconst_type (V := V)
_ _ ρ` is now the whole of every pinned constant's truthfulness
obligation, verified against `PUnit.rec`'s.

### `extendPUnitRecS`: everything but the rule, and where it stops

Written and compiling except `hheadRec`; backed out to keep the tree
green.  Inside `hheadRec`, the structure, the level substitutions
(`hsu`/`hsu1` — state them with the *expanded* names
`Name.anonymous.str "u"`, not `uN`, or the `simp only` will not
match), the constructor identification and the choice of `R` are all
settled.  The step that does not go through is the **denotation of
`R`**:

```
denoteClosed cval ⟨punitRecA :: env.consts⟩ φ
    (rhs.instantiateLevelParams lps [w1, w2])
  = some (.lam (.pi (punitT …) (.sort …)) (.lam (.app (.bvar 0) (punitUnitT …)) (.bvar 0)))
```

Facts established, so the next pass need not re-derive them:

* `rw [denoteClosed]` **does** fire (checked directly).  The goal
  display re-folds `denote … 0 …` back to `denoteClosed`, which is
  misleading — do not read the pretty-printed goal as evidence that it
  did not.
* the TT lane's simp set does **not** finish it here, and a trailing
  full `simp` reports *no progress*, so the residue is not a missing
  rewrite in that set;
* `denote_bvar` is `none` — a bare `.bvar` never denotes.  The λ
  bodies must be opened through `Expr.instantiate1` at an `fvar`,
  which `denote_lam` does and the simp set does provide
  (`Expr.instantiate1_bvar` + `reduceIte` + `denote_fvar`).

**The lane difference to check first**: the TT lane's `hheadRec`
concludes about `denote cval env φ d …` at an *arbitrary depth*
`d`, while `RecRuleLawV` uses `denoteClosed`, i.e. depth `0`.  The
tactic was transposed verbatim; that is the one place the two
obligations are not the same shape, and it is the first thing to
examine.  Do **not** iterate on the simp set blind — three attempts
here produced no information, which is what the stop was for.

## `DeclBasisS`: the `PUnit` block lands — the recursor recipe (2026-08-28)

`declBasisS_punitK` closes the second of six blocks, and with it the
lane's **first recursor**.  The recipe below is what the remaining
four (`Nat`, `Quot`×2, `Eq`, `PSigma'`) follow.

### Why the TT tactic could not be transposed, and what replaced it

`RecRuleLawV` speaks `denoteClosed` — depth **0** — where the TT
lane's `hheadRec` speaks `denote … φ d` at an arbitrary depth.  The
tactic was therefore not transposed at all; the λ-tower is **walked by
hand at depth 0**:

```
rw [denoteClosed]                       -- fires; the goal display
                                        -- re-folds it, ignore that
simp only [Expr.instantiateLevelParams, …, hsu, hsu1]
rw [denote_lam, denote_forallE, hPc' 0 φ w2]
simp only [Expr.instantiate1_*, Nat.reduceAdd, reduceIte]
rw [denote_lam, denote_app, denote_fvar, hUc' 1 φ w2]
simp [Expr.instantiate1_bvar, denote_fvar]
```

`denote_lam`/`denote_forallE` expose a `match` whose **scrutinee must
be rewritten before it reduces**, and at depth 0 every scrutinee is
one of the block's own pinned constants — which is exactly what makes
the walk finite and mechanical.  Two traps, both paid for once:

* the level substitutions must be stated with the **expanded** names
  (`Name.anonymous.str "u"`), never `uN`/`u1N`, or `simp only` will
  not match — and the same holds for the *constant* names, hence the
  `hPc'`/`hUc'` copies normalised by `simp only [punitName, …]`;
* `0 + 1` is not the literal `1`: `Nat.reduceAdd` must be in the set
  before `reduceIte` can fire on `if 0 = 1`.

### Lever 1, cashed

The law itself is three lines once the memberships are in hand:
`punitRecV_app V hM hm pt_mem_unitSet` — the layer's iota law as a
**value equation** — then `app_lamC hM`, `app_lamC hm` for the
reduct's two β-steps.  The TT lane needs a `Deq` chain assembled from
typing rules for the same step.  This is the half-size constant,
confirmed at the first recursor.

### The truthfulness conjunct

`RecRuleLawV`'s second component is two `AnnotOkV_app` steps, each fed
by the binder membership `TeleFitV` already supplies, plus `lamC_mem`
twice for the reduct's own membership.  **Supply the `∃ A B` fibres
explicitly** — the same lesson as lever 2's postmortem, in a second
place: an existential whose witness must come from a `piC` membership
will not solve its metavariables by unification.

**Longhand-first for existential-head goals** is now the informal
practice this and lever 2 both point at.

## `DeclBasisS`: the `Nat` block lands — the recipe repeats (2026-08-28)

Third of six.  `Nat.rec` is the recipe's second recursor and the first
with **two** rules, one of them recursive in the constant being
installed.

### The recipe held, and one part was free

The block's **five denotation helpers**
(`denote_natRec_constsS`, `denote_natRec_typeS`,
`denote_natRec_zeroRhsS`, `denote_natRec_succRhsS`) transposed from
the TT lane by **pure mechanical substitution** — `EnvTT → EnvS V`,
`cvalSet → cvalWith`, `cval_pinned → cvalS_pinned` — and compiled with
**zero edits**.  They are stated at an *arbitrary* depth, so the
depth-0 problem never touches them; it lives only in how a lane's
`hheadRec` consumes them.  The three non-recursor constants likewise
went in first try.

### What was genuinely new

* **The recursive occurrence.**  `Nat.rec`'s `succ` right-hand side
  mentions `Nat.rec`, which the *self* valuation supplies
  (`cvalWith_self`) — and its truthfulness and value are one lemma,
  `hspine`, proved once from `bval_mem_type` + `app_mem_piC` and then
  used at both the `AnnotOkV` node and the reduct's equality.
* **`natStepSpace` needs a `piC_congr` bridge.**  The minor premise's
  denoted type is `piC ω (fun k => piC (M k) (fun _ => M (app natSuccV k)))`
  while the layer's `natStepSpace` says `M (natsucc k)`.  They differ
  by `natSuccV_app`, which needs `k ∈ ω` — i.e. exactly `piC_congr`'s
  fibre hypothesis.  Expect the same shape wherever a constructor
  appears inside a minor premise's type.
* **`natrec_succ` exists** (`SetTheory/Basic.lean:100`) stated with
  `natsucc`; `natrec_vsucc` is stated with `vsucc` and, despite
  `natsucc := vsucc`, is **not** accepted against a `natsucc` goal.
  Use the wrapper.

### Three traps for the remaining blocks

1. Level substitutions **and** constant names must be written expanded.
2. `Level.substFn φ [uN] [w] uN` does not reduce on its own — supply
   `show … = w.eval φ from by simp [Level.substFn, uN]`.
3. The `∃ A B` fibres of every `AnnotOkV_app` must be given
   explicitly; `t2''`/`t3''`-style `have`s in the binders' own
   environment (`interp_inst0` one way, a `piC_congr` bridge the
   other) are what make the four-argument assembly a single `exact`.

## T5 HANDOFF (2026-08-28) — state, plans, traps

Written at a sealed boundary (tree clean, all gates green) rather than
part-way into stage 3, per the session-length protocol.  Everything
*done* is recorded above; this section is only what the next pass
needs.

### Exact remaining state

| piece | state |
|---|---|
| c0–c5 | **done** — the three iota bottoms, the projection bottom, `etaLawKeyS`, `unitLawKeyS` |
| `declStepS` | **done** — per-kind dispatch; the set is closed modulo `DeclBasisS`/`DeclIndS`, so **T6 can be written today** |
| `declIndS` 1 | **done** — `indMemberS` (one member, at the model's valuation; admits a rule-less `.recInfo` head) |
| `declIndS` 2 | **done** — `memberInstallS`, `indMembersS` (non-recursor members), `provisionRecsS` (rule-less recursors ⇒ `EnvS V envSelf`) |
| `declIndS` 3 | **done** — `EnvS.swap` (3a), `iotaRuleS` (3b), `indRecsS` (3c) |
| `declIndS` 4 | **done** — `memberUnitS` discharged; `MemberEtaS` forwarded to the assembly (see the stage-4 record) |
| `declIndS` 5 | **done** — `projConsS`, `projFnS`, `projInstallS` |
| `declIndS` 6 | **done** — `templateVal`, `templateConsS`, `templatesS`; `TemplatesR` re-signed valuation-free |
| `DeclIndS` assembly | **done** — `Install/DeclIndS.lean` |
| `DeclBasisS` | **in progress** — infrastructure, lever 2, and the `Empty`, `PUnit`, `Nat` blocks landed; three left (`Quot`, `Eq`, `PSigma'` + the `Eq`-bridged families) plus the dispatch |

Open obligations, all in the house pattern: `DeclBasisS`, `DeclIndS`,
`MemberKeyS`, `MemberEtaS`, `MemberUnitS`, `DivModPinS`,
`StdAxiomKeyS`, `OfReduceKeyS`.

### The two named capability obligations: discharge plan

They are **not** symmetric, and the difference is easy to miss.

* **`MemberEtaS` is gated and therefore vacuous during both member
  folds.**  Its premise `EtaFamilyStored ⟨c₀ :: env⟩ T caps` demands
  the eta constructor stored *and* **every** `projFnName T j`
  (`j < caps.etaFields`) stored as a `.recInfo`.  The member and
  provisioning folds install only `.indInfo`/`.ctorInfo`/rule-less
  `.recInfo` block members — never a projection function — so the
  premise is false throughout and the obligation is discharged by
  refuting it.  The refutation's own input is already in `DeclIndR`:
  the conjunct `(List.range nF).all (fun j => (envR.find? (projFnName
  cvT.name j)).isNone) = true`.  `MemberEtaS` only becomes *live* in
  **stage 5**, at the projection install that completes the family,
  and there it is `etaLawKeyS` — whose `hvP` is exactly the valuation
  `ProjInstallR`'s step now records, `cval (projModelName T i)`.
* **`MemberUnitS` is not gated** — its premise is just
  `c₀ = .indInfo cv caps` with `caps.unitlike = true`, so it fires at
  the family member's *own* install, inside the member fold.  Its
  discharge is `unitLawKeyS`, and its inputs are available there:
  invert `checkUnitThm`'s Boolean (which is what
  `caps.unitlike = true` means, `caps := indBlockCaps μ env cvT cvC nP
  nF`) into `UnitLawKeyS`'s statement pins; `hvT` is definitional
  (`cvalModeled`'s `cvalWith_self`); `hrenT` is `MemberValR`'s
  `eqUpToNames` pin read as `RenEqT` against the block renaming, whose
  `RenameOkT` is `BlockInstalledTT.renameOkT`.

So: **stage 4 is really "discharge `MemberUnitS` at the member fold and
`MemberEtaS` at the projection fold"**, not a separate installer.

### The template entries' valuation, and why `TemplatesR` leaves it existential

A `.projInfo` template entry exists *precisely because* the field has
no `T._model.proj_i` artifact — so, unlike every other block entry,
there is no model valuation to copy and `cvalModeled` does not apply.
`installProjTemplate` stores `ty := .sort .zero`, so
`EnvS.cons`'s `htype` needs a valuation that is closed, truthful, and
a member of `interp ρ (.sort 0) = univ 0`.  **`VExpr.eqE (.sort 0)
.prf .prf`** is the intended choice: `eqv_mem_univ` gives the
membership, `AnnotOkV`'s `eqE` clause is a leaf (so truthfulness is
immediate), and it is closed.  The relation records only that the step
is a fresh-name `cvalWith` extension — dictating the choice there
would freeze an install decision the relation has no business making.

### Working-memory traps (things that will bite)

1. **Do not cons-fold the ruled recursors** — see the stage-3
   architecture section.  `provisionRecsS` + `EnvS.swap` is the route.
2. **The bottoms fire at `envSelf`, not at the accumulator.**  Their
   walks (`IotaWalksR`) are stated at the provisioned environment.
   That is why `provisionRecsS` hands back an `EnvS V envSelf`.
3. **`indMemberS` returns `∃ m₂, m₂.cval = cvalModeled …`, not
   `Nonempty`.**  Deliberate: the folds compose through the valuation
   equation.  Do not "simplify" it back to `Nonempty` (the value
   kinds' shape).
4. **`fireS` no longer takes `IotaSidesTyR`.**  It takes the two
   sides' memberships, quantified, with the slot's universe fact
   handed to the caller; `sidesMemS` is the certified route the three
   iota bottoms use.  A fourth firing site supplies memberships, by
   whatever means it has.
5. **`EqLawV` is stated at the *two*-fold application.**
   `EqLawV.app₃` is the old three-fold form; `EqLawV.dom` is the
   rigidity.  Do not re-derive either.
6. **`pinnedDirectT eqName = none`** — `basis_pinned` says *nothing*
   about `Eq`'s valuation.  Anyone reaching for a concrete `eqVal` in
   the [set] lane must go through `EqLawV`.
7. **No Mathlib**: `set` is unavailable — use
   `obtain ⟨x, hx⟩ : ∃ x, x = e := ⟨_, rfl⟩`; `le_refl` is
   `Nat.le_refl`; `List.map f [a,b,c]` does not reduce under `rw`
   (`simp only [List.map_cons, List.map_nil]` first).
8. **`obtain rfl : a = b` may eliminate the variable you still need**
   when both sides are locals.  Use `have` + an explicit rewrite where
   the other side is used later (this cost two debug cycles in c3 and
   one in c5).
9. `EnvS.cons`'s obligation list is long and positional; `indMemberS`
   and `extendAxiomS` are the two worked patterns — copy the nearer
   one rather than re-deriving the order.

## FINDING A5 (**blocking, campaign-level**) — B5′ is refuted: validity fails for `Infer` as landed, at I8

Tier A's check of tier B's repair **B5′** (`Setlec/SetR/Annot/Validity.lean`).
The proposal was to supply the λ codomain numeral from a metatheorem —

> if `Infer Δ b B` then `B` has a sort: `∃ v, HasSort Δ B v`

— with no I7 premise, no kernel change and no runtime cost.  **The
metatheorem is false**, mechanized as `validity_refuted`, and the failing
clause is **I8** (application), not the one the hazard note named.

### The case map, mechanized where it is free

| clause | status |
|---|---|
| I1 `sort`, I6 `pi` | **free** — `hasSort_sort` (the inferred type is a sort) |
| I2 `bvar` | **free modulo a context invariant** — `CtxSorted`, maintained by `CtxSorted.cons` (M1's `weakenHead` + `liftN_liftN_add`); both proved |
| I3 `const`, I4/I5 literals | **environment obligations** — the type front door runs `ensureSort` (`Kernel/Checker.lean:272,380`) and the literal guards pin `Nat`/`String`, so an `EnvS` field can expose them.  Not refuted; not needed, since I8 fails first |
| **I7 `lam`** | **free — and it is B5′'s payoff, proved**: `hasSort_pi_of` builds `HasSort Δ (.pi A B) (imax u v)` from I6's own shape, with `v` delivered by validity's induction hypothesis at the body.  B5′'s architecture is right about the clause it was designed for |
| **I8 `app`** | **REFUTED** |
| I9 `proj` | not reached |
| I10 `letE` | **free** — the type is the IH's, at `Infer Δ (b.inst v) B` |

### Why I8 fails — and it is not the substitution hazard

The hazard note predicted the obstacle would be substitution
admissibility (which the family indeed lacks — finding A1).  Substitution
is **necessary but not sufficient**, and the real wall sits one step
earlier.  I8's conclusion type is `B.inst a`, where `B` comes from the
premise `DefEq Δ tf (.pi A B)` — a **conversion**, not a derivation about
`.pi A B`.  Before substituting one must obtain `HasSort (A :: Δ) B v`,
and the only thing in hand is the induction hypothesis `HasSort Δ tf w`
at the *converted* type.  Crossing from one to the other is `HasSort`
crossing a `DefEq`, i.e. **the campaign's known-impossible move**: T3's
"common root", T4's `AnnotOkV`-cannot-cross-`DefEq` record, and the
reason repair C (`Infer.conv`) was rejected in the first place.
`DefEq.symm` forces any one-directional preservation claim into a
biconditional, and `DefEq.ofRed` + `Red.zeta` then relates a sorted term
to an unsorted one in a single **premise-free** step.

### The countermodel

`junkTy = let (_ : prf) := prf; Sort 1`.  `Red.zeta` is premise-free, so
`DefEq Δ (.sort 1) junkTy` holds in *every* environment and context
(`defEq_junkTy`); at the **empty** environment `junkTy` is not inferable
at all (`not_infer_junkTy`, via `infer_shape_empty` — I3 needs a lookup,
I4/I5 need the literal guards), hence unsorted.  `DefEq.piCong` carries it
into a codomain and I8 substitutes it into its own conclusion:

```
    Infer μ ∅ cval φ [Sort 0] ((λ (_ : Sort 0) => Sort 0) (bvar 0)) junkTy
```

with `junkTy` unsorted (`infer_cx` + `junkTy_unsorted`).  The context is
sorted (`ctxSorted_cx`), the empty environment satisfies `EnvS.empty`, and
the valuation may be taken to satisfy `CvalAnnot` — **the refutation
survives every hypothesis validity could reasonably carry**.

**What the counterexample really says** (`infer_cx_good`): the *same*
subject also infers the perfectly sorted type `Sort 1`, by taking I8's
conversion premise to be `DefEq.refl`.  The failure is not a bad term.  It
is that `Infer`'s type slot is determined only **up to `DefEq`** — which
is premise-exactly what the checker's `whnf`-then-match does — while
`HasSort` is not `DefEq`-stable.  Stated generally, and this is the
takeaway worth keeping:

> **No property of an inferred type that is not `DefEq`-stable is a
> theorem of this family.**  `hasSort_not_defEq_stable` is the instance;
> validity is a corollary of it.

### Scope, stated honestly

This refutes validity **for the relation**, which is what B5′ needs (the
annotation pass is a theorem about derivations, so a derivation without
the property is a counterexample).  It does **not** show a `--set-model`
run can *produce* that derivation: the bridge's image is a sub-family that
nothing characterizes, and premise-exactness deliberately keeps the
relation larger than the image (design §0).  A validity restricted to the
image would need that characterization first — a new metatheory, not a
lemma.

### B5″ — the surviving variant, NOT checked, and the reason it may survive

The refutation is specific to the *syntactic* sort fact.  Its semantic
shadow

```
    SemValid : Infer Δ e T → ∃ v, ∀ ρ, Sat V Δ ρ → interp V ρ T ∈ˢ univ v
```

is **not** refuted by this counterexample, and cannot be: `⟦junkTy⟧ρ`
*is* `univ 1` (zeta is invisible to `interp`, `interp_inst0`), so the
counterexample is semantically well-sorted.  If tier C's graded soundness
consumes the numeral as `⟦B⟧ρ ∈ˢ univ v` rather than as a derivation —
which is what `HasSort.mem_univ` already delivers at every *justified*
binder — then B5″ is the statement to check next, and B5′'s architecture
survives with a semantic justification in place of a syntactic one.

**Its own named hazard, before anyone starts**: I8 would need to recover a
*fibre's* universe from the **product's** — `piC ⟦A⟧ B̂ ∈ˢ univ w` plus
`⟦a⟧ ∈ˢ ⟦A⟧` giving `B̂ ⟦a⟧ ∈ˢ univ v`.  That implication is **false
set-theoretically**: if any other fibre is empty then `piC ⟦A⟧ B̂ = ∅`,
which inhabits `univ 0` no matter how large the fibre at `⟦a⟧` is.  So
B5″ needs either a syntactic bound on `B` (an induction with a context
bound, whose own base case `∃ v, ∀ ρ, Sat V [] ρ → ρ 0 ∈ˢ univ v` is
false at the empty context) or a strengthening of I8's premises.  Not
mechanized here — flagged so the next pass starts from a stated risk
rather than discovering it.

### Consequence

Repairs A (kernel computation), B (read `v` off the λ's type), C
(type-directed interpretation, refuted at B5), D (reduces to C) and now
B5′ (validity) are all closed or refuted.  What remains on the table is
B5″ above, or A — and A conflicts with the goal's no-new-checks clause.
**Escalated to the user**, per the amendment protocol: this is a fork
between reinstating a kernel check and a metatheory whose feasibility is
unproved, and it is not a choice tier A should make silently.

**Resolved (#152, master `40bae4b`): repair A** — the λ-rule computes
its codomain sort, under `CheckMode.verified`.  The full resolution
trail is in the main `DESIGN.md`'s section *"The λ-rule computes its
codomain sort"*; this note exists only so the fork above is not read as
still open.


## T5 COMPLETE (2026-08-28) — the basis blocks, and `DeclBasisS`

`DeclBasisS` is discharged.  With it the T5 inventory is closed: every
obligation `declStepS` takes that T5 owned is now a theorem, and the
interface T6 inherits is exactly

    MemberKeyS   MemberEtaS   DivModPinS   StdAxiomKeyS   OfReduceKeyS

(`ReducePinS`, `DeclIndS` and `DeclBasisS` are supplied).

### The five blocks, and what each cost

`Setlec/SetR/Install/BasisS.lean` installs `Empty`, `PUnit`, `Nat`,
`Quot`, `Eq` and `PSigma'` — one `declBasisS_*K` per kind, dispatched
by `declBasisS`.  The campaign-wide ratio held: the *recursor* content
is roughly half the TT lane's, because a layer value equation replaces
a `Deq` chain; the *type* content is slightly more, because `AnnotOkV`
has no TT counterpart.

Where the two lanes diverge most:

* **`Quot.ind`** — proof irrelevance.  `bval .quotInd = pt` collapses
  the fired side by `app_pt`; the reduct sits in the motive's fibre,
  which the motive's own membership puts in `univ 0`; `mem_univ_zero`
  equates them.  The TT lane assembles `HasType.proofIrrel` and a
  β-spine.
* **`Eq.rec`** — a member of `eqv a b` *is* a proof that `a = b`
  (`mem_eqv`) and *is* `pt` (`mem_univ_zero` on `eqv_mem_univ`), so
  the transport is two rewrites where TT needs `proofIrrel` plus a
  `congrApp` pair.
* **`Eq`** — `EqLawV` is discharged *from the tower*: two `app_lamC`s
  for the equation, `lamC_ne_pt_of_witness` at the unit proposition
  for the rigidity clause.
* **`PSigma'.rec`** — the block's eta law in disguise: the motive must
  land at the constructor spine where the tower supplies the two
  projections, and `psigmaEta_law` closes exactly that gap.
* **`Quot.lift`/`Quot.sound`** — the `Eq` bridge (P3 above), the only
  place where the stored type and the layer's own type differ.

### Relocations

Relocation #17 (`inst_chain1..4`, `inst_absorb21..54`) moved from
`TTVerify/DeclBasis.lean` to `Verify/Denote/SubstAlgebra.lean`, in the
`Setlec.TT` namespace so both lanes see them unqualified.  A
substitution identity is shared tier, not lane-local: both lanes'
recursor iotas walk the same telescopes and both need the same
cancellations.

### The transposition recipe, as it finally stood

Depth-arbitrary `denote_*` helpers transpose with **zero edits** under
`EnvTT → EnvS V`, `cvalSet → cvalWith` (plus the `S` suffix on names
already taken).  The install skeletons transpose with three edits:
drop TT's residual argument, insert `hannot` between `hparams` and
`htype`, and replace the `HasType` obligation with the pair
`⟨HasType.sound … , AnnotOkV_bconst_type …⟩` (for pinned-constant
valuations) or a bespoke membership/truthfulness pair (for tower
valuations).  The *iotas* do not transpose at all and are written
natively: normalise the `TeleFitV` entries with the `inst_chain`/
`inst_absorb` set plus `interp_*`, then `app_lamC` down both sides.


## T6 — the assembly opens; FINDING 7 (2026-08-28)

### What T6 needs, surveyed

`checkDeclR_of` (the dispatch) and `declStepS` (the `DeclR → EnvS`
step) both already exist.  What the assembly is missing is the **six
per-kind bridges** `checkDecl … = .ok env₂ → Decl*R …`: none of
`DeclDefnR`, `DeclThmR`, `DeclOpaqueR`, `DeclAxiomR`, `DeclBasisR`,
`DeclIndR` had a producer.  Their sub-relations `ConstantValR` and
`ValueFrontR` are likewise consumed in the install tier and produced
nowhere, so the value-kind bridges are the tier's bulk; `Bridge/Main`'s
`checkBridge` supplies their `Infer`/`DefEq` components, and
`Verify/Extend/Inversions.lean`'s `checkConstantVal_inv` their
syntactic ones.

Landed here: relocation #18 (`installBasisDecl_inv` from
`TTVerify/DeclBasis.lean` to `Verify/Extend/Inversions.lean` — both
lanes invert the same fold), `foldlM_installBasisDecl_invR`,
`declBasisR` (the `basisDecl` bridge), and `EnvS.toEnvR`.

### FINDING 7 — `EnvR`'s recursor fields were unsuppliable

Building `EnvS.toEnvR` — the projection the whole assembly runs
through — exposed that two `EnvR` fields were stated more strongly
than `EnvS` can supply:

* `rec_rhs_denotes` quantified over **all** rules and **all** level
  lists; `EnvS.rec_rules` (`RecRulesV`) speaks only of rules with
  `fire ≠ .inert`, and only at `us.length = cv.levelParams.length`.
* `rec_params_le` concluded `rP ≤ mI` from the recursor's *lookup
  alone*; `RecRulesV` yields it only inside `RecRuleLawV`, i.e. again
  only for a non-inert rule.

Both field docstrings asserted "`EnvS.rec_rules` carries it" — the
record failing against its own author, P2's signature failure mode,
for the third time in the campaign.

**Why the repair is narrowing, not a new field.**  `Empty.rec` stores
**no rules at all**, so no install could ever supply an unguarded
`rP ≤ mI`; a new unguarded `EnvS` field would have been owed by every
install for a fact nothing consumes.  And both fields are consumed at
exactly one site — the iota fire path in `Bridge/Iota.lean` — where
the fired rule, `hfire : rl.fire ≠ .inert` and the level-length split
`hlenU` are all already in scope.  So the fields were narrowed to
their consumption; `EnvR` had no supplier yet, so nothing else moved,
and the three use sites take three extra arguments each.

**The check this earns**, beside P1's ("check when a field is ADDED,
which helpers its supplier must run"): *when a structure's field
docstring names its intended supplier, elaborate the projection
against that supplier before the structure is frozen.*  `EnvR` was
frozen in T3 with the supplier named in prose and unbuilt; the
mismatch survived T4 and T5 untouched because nothing had reason to
construct an `EnvR` until the assembly did.

### T6 handoff — the ordered remainder

1. ~~**`ConstantValR` / `ValueFrontR` bridges**~~ **LANDED** — the gate
   for four of the six branches.  Ingredients: `checkConstantVal_inv`
   and `fueledOps_*` (`Verify/Extend/Inversions.lean`) for the syntactic
   conjuncts; `checkBridge` (`Bridge/Main.lean`) at `EnvS.toEnvR` for the
   `Infer`/`DefEq` conjuncts; the `denoteClosed` existentials come from
   `EnvR.ty_denotes` and the annotate output's `constsResolve`.  Note both
   relations quantify over **every** `φ`, so the bridge must be run at an
   arbitrary assignment — `checkBridge` already is.
2. ~~**`declDefnR`**~~ **LANDED** (all five value/basis branches are
   through) — each was its
   branch's `simp only [checkDecl, …]` inversion over (1), plus its own
   conditional pack (`NatEqsR`/`DivModPinR` at `defn`, the sort-is-`Prop`
   conjunct at `thm`, `ReducePinR` at `opaque`, the four shape gates at
   `axiom`).  The Model lane's `checkDecl_sound`
   (`Model/Consistency.lean:488-2513`) inverts exactly these branches and
   is the template — read it for the inversion order, not for its
   conclusions.
3. **`declIndR`** — the big one; `DeclIndR` is `Decl.lean:771+`.  Expect
   it to dominate the tier the way `IndBottom` dominated T5's.
4. **`checkDeclR_sound`** = `checkDeclR_of` ∘ (1-3), composed with
   `declStepS` and the five open obligations threaded at the assembly
   level, then the `checkDecls` fold (transpose `foldlM_TT`,
   `TTVerify/Consistency.lean:83`).
5. **The thirteen `*_R` theorems** (§4 of the design doc).  Counted from
   the checklist they are *fourteen* names: `checkDecl_sound`,
   `checkDecls_sound`, `no_proof_of_Empty{,_input}`,
   `no_constant_of_Empty`, and the `_S`/`_C`/`_SP` triples
   (`checkDecls*_sound`, `no_proof_of_Empty*`, `no_proof_of_Empty_input*`).
   Flag the discrepancy when reporting rather than dropping one.
   `no_proof_of_Empty_R` takes the §3 route: a stored constant of type
   `Empty` gives `interp (cval c ψ) ∈ˢ interp ⟦Empty⟧ = SetTheory.empty`
   (`EnvS.mem_type` + `empty_pinned` + `interp_emptyT`), refuted by
   `not_mem_empty`.
6. **Axiom audit** on all of them, then the checkpoint commit with BOTH
   lanes green.

### T6 progress — the front doors are through

`constantValR_of` and `valueFrontR_of` land in `Bridge/Decl.lean`, with
`closed0_framesR`.  Both are the same script the TT lane's `value_key`
runs, re-aimed at the relation family: `checkConstantVal_inv` (or the
branch's own `annotate` inversion) for the syntactic conjuncts, then
`checkBridge` at `EnvS.toEnvR` for the `Infer`/`DefEq` ones, at an
arbitrary `φ`.

Two shape notes for the branches that consume them:

* `constantValR_of` returns the annotated type's **two closedness
  facts** beside the relation — every branch needs them for its own
  value front door and for `EnvWF`, and re-deriving them per branch is
  the duplication the TT lane accumulated.
* `valueFrontR_of` takes the `ConstantValR` as a hypothesis rather
  than re-deriving the type's denotation: `ValueFrontR` asks for
  `denoteClosed … type' = some Tv`, which is exactly what
  `ConstantValR`'s own `∀ φ` component already produced.  Nothing in
  the checker's value branch re-infers the type.

The `thm` branch's extra conjunct (`DefEq … sT (.sort 0)`) is
`ConstantValR`'s last component at `u.eval φ = 0`, and
`Level.isEquiv_sound` (`Verify/Level.lean:314`) supplies that from the
checker's `Level.isEquiv u .zero` guard — checked, so the branch is
unblocked.

### T6 progress — four of six branches bridged

`declBasisR`, `declThmR`, `declAxiomR`, `declOpaqueR`.  All three of
the new ones compiled first try off the recipe: the branch's own
`simp only [checkDecl, check*Val, fueledOps_*, Bind.bind, Except.bind]`
inversion, `constantValR_of`, `valueFrontR_of`, and the branch's own
tail.

* `thmDecl` — the extra `DefEq … sT (.sort 0)` conjunct is
  `ConstantValR`'s last component read at `u.eval φ = 0`, which
  `Level.isEquiv_sound` supplies from the checker's own guard.
* `axiomDecl` — a pure dispatch on Boolean shape gates; nothing
  semantic past `ConstantValR`.  The axioms' *content* is the install
  layer's `StdAxiomKeyS`/`OfReduceKeyS`, not the bridge's.
* `opaqueDecl` — parametric in the compiler-trust pin's own inversion
  (`checkReducePin → ReducePinR`), exactly as the TT lane parameterises
  `declDefnTT` on `NatOpPinTT`/`DivModPinTT`.  Keeping each pin pack
  out of the branch script is what stops the branch from growing a
  second subject.

**`declDefnR` is the branch left of the four**, and it is the one with
two conditional packs rather than one (`certifyNatEqs → NatEqsR` and
`checkDivModPin → DivModPinR`), plus a `match` on the just-consed
environment's own lookup.  Its dispatch should be resolved **once**
into a `have` yielding the triple (`env₂ = …`, the natOp conjunct, the
divMod conjunct) and only then assembled — resolving it separately per
conjunct triplicates the four-level `by_cases` nest.  The `hdm`
parameter must be phrased over the *annotated* value the environment
actually stores, not over the source `value`: `DivModPinR`'s last
argument is `value'`.

### T6 progress — `declDefnR`; the `cases h : e` goal-rewrite trap

`declDefnR` lands, and with it **five of the six branches**; only
`declIndR` remains.

Two notes for anyone reading the branch:

* The `do` sequencing **inlines the div/mod block into every leaf** of
  the `Nat`-op dispatch, so the "resolve the dispatch once" discipline
  buys less than it looks: the shared `tail` lemma that would have
  factored it has to match the inlined `if`/`match` term
  *syntactically*, and stating that shape is more brittle than
  repeating the four-line resolution at the two surviving leaves.  The
  discipline that did pay is resolving **`env₂` and both packs in one
  `have`** rather than once per conjunct.
* **`cases hcert : e with` rewrites the GOAL too**, not just the
  hypothesis it names.  After `cases hcert : certifyNatEqs … with
  | ok v =>`, the `key` statement's own `certifyNatEqs … = .ok true`
  conjunct has already become `Except.ok true = Except.ok true`, so
  the conjunct is discharged by `rfl` and passing `hcert` is a type
  error.  Same for `checkDivModPin`.  Cost: one round trip; worth a
  line here because the error message ("expected type
  `Except.ok true = Except.ok true`") reads like a bug in the
  statement rather than the tactic doing its job.

## FINDING 8 — the `indDecl` bridge cannot be unconditional (2026-08-28)

`memberValR_of` lands (`checkMemberVal` = `checkConstantVal` plus four
model-artifact inversions), and with it the shape of the remaining
work became clear — and blocked.

**The observation.**  The three front doors are now stated over
`EnvR`, the weakest thing they use.  That sharpens the difficulty:
`MemberValR μ F env'ₖ cval …` contains `ConstantValR`, whose last
conjunct is `Infer μ env'ₖ cval φ [] Tv tT ∧ DefEq …`.  The only
producer of `Infer` is `checkBridge`, which takes an `EnvR env'ₖ`.
So producing `IndMembersR` **for the whole member list** requires an
`EnvR` at every *intermediate* environment of the fold — and nothing
in the campaign builds an `EnvR` for an extended environment except
by projecting one out of an `EnvS`, which is what the *install* layer
produces while consuming the very relation being built.

The two tiers were designed to meet at `IndMembersR` (`indMembersS`
takes the whole relation and returns `EnvS env₂`), and that meeting
point is unreachable by either side alone.  The same holds for
`IndRecsR` and for `ProjInstallR`'s `ProjFnR` steps; it does **not**
hold for `TemplatesR` (no front door — a pure stored-data install,
which is why `templatesR_of` inverted outright) nor for any of the
five value/basis branches (one front door, at the *base*
environment).

**Two resolutions, and they differ in what they cost.**

1. **Interleave, and output both.**  Walk each fold once, at every
   step running `memberValR_of` at `m.toEnvR` and then the install's
   own step (`memberInstallS`) to get the next `EnvS`; accumulate the
   relation alongside.  The fold's conclusion is then
   `∃ m₂ : EnvS V env₂, … ∧ IndMembersR …`, so `checkDeclR_of`,
   `DeclR` and `declStepS` all stay usable unchanged and `DeclR`
   keeps its design-instrument role (§6: the relations *are* the
   certificate inventory).  Cost: the four folds' orchestration is
   written twice — once in `declIndS` (T5), once in the bridge —
   though every *sub*-theorem is reused.  Consequence for the
   assembly: the `indDecl` branch's bridge is conditional on `EnvS`,
   unlike the other five.
2. **An `EnvR`-only install layer.**  Prove `EnvR`-preservation across
   the member / provision / rule-swap / projection installs (ten
   fields × four kinds), so the bridge walks the folds alone and
   `declIndR` is unconditional like its five siblings.  Cost: a
   parallel install layer for a strictly weaker invariant, whose
   substantive field (`ty_denotes` at the extended environment) is
   most of the work `mem_type`'s install already does.

**Recommendation: (1).**  It is strictly less new proof, it reuses
T5's install theorems rather than shadowing them with weaker twins,
and the asymmetry it introduces is honest — the `indDecl` branch
*is* the one whose relation quantifies over intermediate
environments, and a bridge for it was never going to be as free of
the invariant as the others.  (2) buys unconditionality for the ind
branch at the price of maintaining two invariants that must be kept
in step forever.

**DECIDED: option 1 — interleave, output both.**  Three grounds beyond
the above:

* the conditionality is **not an asymmetry at the theorem the user
  sees**: `checkDeclR_sound` was always `EnvS env → … → EnvS env₂`
  shaped, so an `EnvS`-conditional `indDecl` branch matches the final
  composition exactly.  The unconditional five siblings are the bonus,
  not the norm;
* it is the classical **combined-induction** shape — the fold carries
  the invariant that feeds the next step's typing.  The model's own
  install proof works this way, and fighting it with a parallel weaker
  invariant is exactly the two-invariants-forever maintenance shape
  this campaign exists to delete;
* the pattern isolated above is the finding's durable content.

**The recognition rule** (belongs beside the P-rules):

> **A bridge must interleave with its install exactly when the
> relation it produces quantifies over environments the fold
> creates.**

Check it by asking, of each conjunct of the target relation, *which*
environment its lookups and derivations are at.  A conjunct at the
base environment is bridgeable alone; a conjunct at an intermediate
environment is not, and no amount of weakening the invariant changes
that — it only moves which invariant has to be rebuilt there.
`TemplatesR` passes (no front door at all); the five value/basis
branches pass (one front door, at the base environment);
`IndMembersR`, `IndRecsR` and `ProjFnR` fail.

### Finding 8, implemented — the interleaved walk works

`Setlec/SetR/Bridge/DeclInd.lean` opens with `indMembersRS`: literally
`indMembersS`' induction with `memberValR_of` inserted at each step to
*produce* the front door instead of consuming it, accumulating the
relation and the invariant together.  It went through unchanged
otherwise — every side-condition thread (`hbn`, `EtaPins.step`,
`BlockInstalledTT`) is the install's own, and `memberInstallS` is
called exactly as `indMembersS` calls it.

That is the decision's practical confirmation: the orchestration is
written a second time, and it is *only* orchestration — no
sub-theorem, no invariant, and no side condition is duplicated.  The
remaining two folds (`indRecsRS` over `checkIndRecs`, `projInstallRS`
over `installProjFnStep` with `ProjFnR`) follow the same three lines
per step: checker step, bridge at `m.toEnvR`, install step.

One shape note for them: the fold hypothesis `h` never mentions the
running valuation (it is the *checker's* fold, which has none), so the
recursive call takes `h` unchanged — a `rw [hm₁cval] at h` there
fails, and the reflex to "step everything" is what makes it look like
the valuation threading has a hole when it does not.

### T6 — the `indDecl` scorecard, and the two rocks left

Applying the recognition rule to all four `indDecl` folds gives a
clean discrimination, which is the finding's real payoff:

| fold | front door at | verdict |
|---|---|---|
| `TemplatesR` | *none* | plain bridge (`templatesR_of`) |
| `IndMembersR` | the accumulator | **interleave** (`indMembersRS`) |
| `ProvisionRecsR` | the accumulator | **interleave** (`provisionRecsRS`) |
| `IndRecsFoldR` → `IotaRulesR` | the fixed `envSelf` | plain bridge |
| `ProjInstallR` → `ProjFnR` | the accumulator | **interleave** |

`IndRecsFoldR` passes `envSelf`/`cvalSelf`, not the accumulator's, so
one `EnvR envSelf` serves the whole rules fold; `ProjFnR` has
`Infer μ env' cval φ [] Rv t` at the accumulator, so the projection
fold is the last interleave.

**What is left of the branch is two inversions**, and neither is
orchestration:

1. **`RuleChecked → IotaRuleR`** (non-interleaved, at `envSelf`).
   `Verify/Extend/Iota.lean` already carries the syntactic content:
   `checkIotaRules_inv` → `RuleChecked`, whose `PlainChecked` field is
   `IotaThmR` in all but three respects — `PlainChecked` quantifies
   the theorem's *name* existentially where `IotaThmR` pins it to
   `(cvName._model).iota_j`; the shape comparisons are propositional
   `=` there and Boolean `==` here; and `DefEqListOk` has to become
   the relation's `DefEqL`, which is a `checkBridge` consumption at
   the one `EnvR envSelf`.  The nested case (`NestedChecked` →
   `IotaThmNR`) is the same three respects again.  Plus `IotaRuleR`'s
   own `Infer`-at-`envSelf` conjunct, which is `constantValR_of`'s
   inference step at the rule's annotated right-hand side.
2. **`installProjFnStep → ProjFnR`** (interleaved, template
   `indMembersRS`; the install side is `projFnS`).

Then `declIndRS` assembles the five, `checkDeclR_sound` dispatches the
six branches through `checkDeclR_of` and composes with `declStepS`,
and the fold transposes `foldlM_TT`.

## FINDING 9 — rock 1's third respect is not a diff (2026-08-28)

The three-respects decomposition of `RuleChecked → IotaRuleR` holds
for two of the three.  The **name pin** does not, and the reason is
worth stating exactly because it looked like the cheapest of the
three.

`IotaThmR`'s first conjunct is
`env'.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt` —
the theorem looked up **by its pinned name**.  `PlainChecked`
(`Verify/Extend/Iota.lean:36`) instead opens with
`∃ thmName ci, env.find? thmName = some ci ∧ ci.toConstantVal = cvt`.
`checkIotaThm_inv`'s *proof* instantiates that existential at the
pinned name; its *statement* forgets it.  From outside, nothing
identifies the two: no conjunct of `PlainChecked` determines
`thmName`, so an additive "name lemma" proved alongside cannot be
glued to it — the two lookups are about possibly-different names
yielding possibly-different `ci`.

**The pin is load-bearing**, so weakening `IotaThmR` is not available:
`Install/IotaRuleS.lean:139` looks the statement up at exactly
`(cvA.name._model).iota_j` in the *self* environment, to carry the
stored theorem across the group's environment step.  That is the
install side's own use, in T5-landed code.

So the fork is:

1. **Pin the name in the shared tier.**  `PlainChecked` gains the rule
   index `j` and states the lookup at the pinned name.  But
   `PlainChecked` is applied inside `RuleChecked`, which has no `j`,
   and `RuleChecked` is consumed as `∀ r' ∈ rules', RuleChecked … r'`
   by `checkIotaRules_inv` — so the conclusion's *shape* has to become
   indexed, not just its arity.  Blast radius: 11 references over 7
   files, spanning `Model/*` (retiring in T7) and `TTVerify/*` (kept).
2. **Re-derive on the [set] side.**  A `checkIotaThm_invR` concluding
   `IotaThmR` directly, reusing `checkIotaThm_inv`'s script with the
   lookup left pinned — roughly 200 lines, duplicated against a shared
   file, and the same again for `checkIotaThmN`/`IotaThmNR`.

Neither is obviously right.  (1) is the anti-duplication answer the
campaign has taken everywhere else (the front doors, the relocations),
but it is the first change that reaches *into* the kept TT lane's
consumed statements rather than merely relocating beside them.  (2)
keeps both lanes untouched at the cost of the largest duplication the
[set] tier would contain.

A third reading worth ruling out explicitly: making `PlainChecked`
take `thmName` as a parameter and existentially quantifying it *at
`RuleChecked`* preserves today's information exactly, so it does not
help — the pin has to be present where `checkIotaThm` established it,
which is inside the per-rule inversion.

**DECIDED: option 1 — pin in the shared tier.**  The precedent check
resolves it: this is not the campaign's first edit to shared-inversion
statements the TT lane consumes (#135 and #146 threaded new conjuncts
through these same inversions, `checkIotaThm_inv` included).  The
class is established: *recording in the statement what the proof
already establishes* is a strengthening no consumer can be harmed by.

**Implemented — with one correction worth keeping.**  My first attempt
*replaced* `∃ thmName ci, env.find? thmName = some ci ∧
ci.toConstantVal = cvt` with `env.findCV? pinned = some cvt`.  That is
not a strengthening: it deletes the `ConstantInfo`, which both lanes
consume downstream (five sites broke with `Unknown identifier
thmName`/`ci`/`hfthm`/`hcvt`).  The rule is exact and I violated it on
the first pass: **one conjunct to DISCARD, never a field to
reconstruct.**  The landed shape keeps all four and appends
`thmName = (cvA.name.str "_model").str s!"iota_{j}"`.

The genuinely new part — `RuleChecked` gaining `j`, consumed under
`∀ r' ∈ rules'` — was mechanical after all: `checkIotaRules_inv`'s
conclusion becomes `∀ k r', rules'[k]? = some r' → RuleChecked … (j+k)
r'`, mirroring the checker's own loop accumulator, and each consumer
boundary re-existentialises the index (`∀ r' ∈ rules', ∃ j,
RuleChecked … j r'`) via `List.getElem?_of_mem`.  Consumers that never
look at the index gained one `⟨jj, …⟩` binder; the one that is
*about* a single rule (`ruleChecked_rhs_facts`) took `j` as a
parameter instead.  Total: 8 files, all edits positional.

### T6 — the walk layer factors through one lemma

Rock 1's second and third respects turn out to be one lemma and one
mechanical conversion.

Every `iota_j` statement walk the checker runs is a `checkDefEqList`
or a single `isDefEq`, and every one lands in the relation as
`DefEqAtW`/`DefEqListW`.  Those differ from what `DefEqClaimsR`
delivers in **exactly one respect**: they assert the two *denotations
exist*, where the claim takes them as inputs.  The `∀ Δ` quantification
over correlating contexts and the two `CtxOkR` premises match the
claim's shape verbatim.

So `defEqAtW_of` and `defEqListW_of` (landed) are the whole walk
layer, and what remains to supply per element is a denotation and
three frame facts (`WScoped`, `looseBVarsBounded`, `LeavesBounded`).
Both come from the opened statement's own type — `EnvR.ty_denotes` at
the `iota_j` theorem, decomposed through the `openPisAtFvars`
machinery (`Verify/Denote/TeleOpen.lean`, whose V-free parts were
relocated in T1 and extended in T5).  That decomposition is the D6
"quantified-context walk" the install side's docstrings name, and it
is the last piece of rock 1 with any content: after it, `IotaThmR`
from `PlainChecked` is Bool-vs-Prop conversion plus a rename of
bound existentials (`PlainChecked`'s `rrest`/`restP`/`crest2`/`ldoms`
are `IotaThmR`'s `lrest`/`crest2`/`ldoms`/`ldomsL` — the lists are
the same, the names are not; write the witness in `IotaThmR`'s order,
not `PlainChecked`'s).

### T6 — D6's walk is assembly, not derivation

Entering the quantified-context decomposition revised its cost
downward.  I had it recorded as "the last piece of rock 1 with any
content"; on inspection the content is already built, in
`Verify/Denote/IndFrame.lean`:

* `openPisAtFvars_denoteTele` — an opened telescope whose subject
  denotes yields the opened body's denotation *and* each opener's
  annotation denoted at its own depth, against the `.pi` tower's
  context;
* `instPisAt_fvar_denote_defined` — an `instPisAt` run at frame
  variables of a denoting subject has a denoting residual;
* `instPisAt_denote_cross` — the domain lists' correspondence.

So the decomposition is a *composition* of three existing lemmas with
`EnvR.ty_denotes`, not a new induction.  `stmtType_denotes` and
`stmtOpened_denotes` (landed) are that composition's entry point: from
a `find?` of the `iota_j` statement to the opened body's denotation
and every opener's, which is exactly the per-element input
`defEqAtW_of` wants.

Two depth traps in the composition, both from `openPisAtFvars`'s
opening depth being an explicit parameter: the tele lemma concludes at
`j + k` and at `j + i`, and with `j = 0` those are `0 + k`/`0 + i`,
which do not match `k`/`i` syntactically.  Both need `Nat.zero_add`
rewrites — the second one *under* the `∀ i x` binder, so it has to be
done after `refine … fun i x hx => ?_` rather than by rewriting the
hypothesis.

Revised remaining shape: rock 1 is now **entirely assembly** — the
walks (`defEqListW_of` per element, fed by `stmtOpened_denotes`), the
Bool-vs-Prop conversions, and the permuted-name rename.

### The relocations were the point

Eighteen relocations across the campaign, each recorded at the time as
housekeeping.  They are not.  **They are why the [set] lane keeps
finding its lemmas already built.**

The pattern repeats too often to be luck: `inst_chain*` (#17) turned
every recursor iota's substitution bookkeeping into a rewrite;
`installBasisDecl_inv` (#18) made the basis-block bridge an induction
with no lemma of its own; `TeleOpen`'s V-free parts (T1, extended in
T5) plus `IndFrame`'s denote-tele machinery turned D6's
quantified-context walk — recorded twice as "the last derivation with
content" — into a composition of three existing lemmas.  Each
relocation converted a *future derivation* into a *composition*, and
the conversions compound: the walk layer collapsed to one lemma
(`defEqAtW_of`) only because both the claims tier and the denote tier
were already neutral ground.

That is the campaign's quiet second thesis, alongside premise
exactness: **a lemma in a lane-specific file is a lemma the other lane
will re-derive; a lemma in the shared tier is a lemma the other lane
will compose.**  The cost of relocating is one commit and a namespace
decision; the cost of not relocating is paid later, at the width of
whatever the second lane needs.

The operational form, for the next campaign: when a lemma is proved in
a lane-specific file and its statement mentions **nothing lane-specific**,
relocate it *then* — not when the second consumer appears.  By the
time the second consumer appears, the cheap moment has passed and the
choice is between a duplication and a blast radius (finding 9's fork,
exactly).

### T6 — the `IotaThmR` witness, validated

The ~40-component witness was elaborated against the real statements
with the two walk conjuncts stubbed.  **Everything else typechecks**,
so the permutation table below is confirmed and the remaining
assembly is exactly the two walks.

Destructure `PlainChecked` in its own order:

    thmName cvt ci fvs tbody ℓA αS lhsS rhsS cdoms cres rdoms rrest
    fvsP restP cdomsP crestP xFvsP crest2 ldoms lrest
    hfthm hcvt hpin hlpt hopen hheadEq hargs3 hlhead hlarity hlpre
    hmaj hcstrip hcinst hclen hdeIdx hdeFld hrinst hdePre hopenP
    hcinstP hdeP hopenX hlinst hdeLam hdeRhs hty1 hty2 hty3

then `subst hpin` and give `IotaThmR`'s witnesses in **its** order:

    cvt fvs tbody
    cdoms cres rdoms fvsP cdomsP crestP xFvsP restP crest2 rrest
    ldoms lrest

i.e. the four permuted slots are `restP ↦ crest2`, `crest2 ↦ ldoms`,
`rrest ↦ lrest`, `ldoms ↦ ldomsL` (and `lrest ↦ lrest2`).  Writing
them in `PlainChecked`'s order typechecks *partway* and then fails
deep in the walks, which is the worst place to discover it — hence
the table.

Three mechanical points that worked:

* the `findCV?` conjunct is
  `rw [Env.findCV?, hfthm, Option.map_some, hcvt]`;
* `isEqHead tbody.getAppFn = true` and
  `tbody.getAppArgs.length = 3` are `rw [hheadEq]; rfl` and
  `rw [hargs3]; rfl`;
* every Bool-vs-Prop conjunct is `by simpa using h…` — `simpa`
  discharges the `beq_iff_eq` *and* reduces
  `[αS, lhsS, rhsS].getD 1 (.bvar 0)` to `lhsS` in one step, which a
  `rw` cannot (the `getD` blocks the rewrite's pattern match, and the
  obvious `List.getD_cons_*` simp lemmas do not fire on it).

### T6 — the last missing piece, and where it went

`instPisAt_denote_doms` (`Verify/Denote/IndFrame.lean`): every domain
an `instPisAt` run collects denotes, when the subject does.  It is the
list half of `instPisAt_fvar_denote_defined` — the same induction,
returning the `dom` each step already denotes instead of discarding
it — and it was the one fact the walks needed that nothing supplied.

It went into the **shared tier**, not into `SetR/`, on the relocation
thesis's operational form: its statement mentions `Expr.instPisAt`,
`denote` and nothing lane-specific, so the cheap moment to place it
neutrally is now, while it has one consumer, not later when the TT
lane's own walks want it.

With it, **every input the two walk conjuncts need now exists**:

| walk input | source |
|---|---|
| opened body denotes | `stmtOpened_denotes` |
| each opener's annotation denotes | `stmtOpened_denotes` |
| each `instPisAt` domain denotes | `instPisAt_denote_doms` |
| each `instPisAt` residual denotes | `instPisAt_fvar_denote_defined` |
| frames (`WScoped`/bounded/`LeavesBounded`) | `instPisAt_leaves`, `instPisAt_bounded`, `closed0_framesR` |
| the comparison itself | `defEqAtW_of` / `defEqListW_of` |

The one remaining mechanical concern is **depth**: `openPisAtFvars`
delivers each opener's annotation at *its own* depth `i`, while the
walks run at `depth = rP + cnF`.  Lifting is `denote_lift` (the same
step `denote_closedExprR` takes).  Nothing else about the walks is
open.

### T6 — `iotaThmR_of`'s real signature

`opener_denotes_at` lands: the depth crossing, in the definedness-only
form the walks consume (`DefEqAtW` names its values existentially, so
nothing needs the lifted value itself).

Working the walks against the real statements turned up an interface
detail that would waste a session if discovered mid-proof.
**`iotaThmR_of` cannot take `PlainChecked` alone.**  Its two walks run
at `envSelf` (`PlainChecked`'s `env₀`), but the data they need is
looked up at `env'` (`PlainChecked`'s `env`):

* the walk's right-hand lists are `instPisAt` runs on
  `cvj.type` / `cvA.type`, and `instPisAt_denote_doms` needs those
  *subjects to denote at `envSelf`* — which needs the constructor and
  the recursor **stored in `envSelf`**;
* `PlainChecked` only gives `env'.find? r.ctor = some (.ctorInfo cvj
  cnP cnF)`.

Both facts hold — `envSelf` is `env₂` (post-member-fold, so the
constructor is in it) extended with the rule-less recursors (so `cvA`
is in it), while `env'` is the *rules-fold accumulator* over the same
base — but they are the **fold's** facts, not the per-rule inversion's.
So the signature is

    iotaThmR_of (m : EnvR envSelf)
      (hctorSelf : envSelf.find? r.ctor = some (.ctorInfo cvj cnP cnF))
      (hrecSelf  : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
      (h : PlainChecked μ F env' envSelf f cvA mI rP cnP cnF j
             { r with rhs := rhsA } cvj) : IotaThmR …

and the caller (`indRecsRS`'s rules fold) supplies the two lookups
from `ProvisionRecsR`'s output.  This is not a finding — nothing is
mis-stated — but it is the difference between an inversion lemma and a
fold-context lemma, and getting it wrong costs a rewrite of a
40-component witness.

### T6 — the walks' left-hand side, fully supplied

`opener_walk_pack`: everything `defEqListW_of` needs about a
statement walk's **left**-hand list — the three frame facts and the
denotation, all at the walk's depth — for a telescope opened from a
stored, closed subject at depth `0`.  Assembled from four existing
frame lemmas (`openPisAtFvars_bounded`/`_WScoped`/`_index`/`_leaves`)
plus `stmtOpened_denotes` and `opener_denotes_at`.  No new induction.

Every statement walk's left list is `(fvs…).map Expr.fvarTypeD` for
some opening, so this lemma covers all six at once.

Three details that cost a round trip each and are worth transcribing:

* `openPisAtFvars_WScoped` concludes `WScoped (0 + k) x` for the
  **fvar**, not its annotation; `rw [Expr.WScoped]` unfolds it to
  `(0+i) < (0+k) ∧ WScoped (0+i) ty`, and both need `Nat.zero_add`
  (the depth trap, third instance);
* the annotation's `LeavesBounded` is the interesting conjunct: it
  holds because the *subject* is `hasFvar`-free, so
  `openPisAtFvars_leaves` forces every leaf of an opener's annotation
  to be **itself an opener**, whose annotation `openPisAtFvars_bounded`
  bounds.  Without the subject's closedness there is nothing to say;
* `(Expr.fvar i nm ty).fvarLeaves` is `(i, nm, ty) :: ty.fvarLeaves`,
  so the leaf of the annotation embeds by `List.mem_cons_of_mem`, not
  by an append lemma.

What remains for the walks is the **right**-hand lists (`instPisAt`
outputs), whose denotations are `instPisAt_denote_doms` and whose
frames are `instPisAt_leaves`/`instPisAt_bounded` — the same shape of
package, against lemmas that already exist.

### T6 — both walk packages, and the walk layer is closed

`instPisAt_walk_pack` lands, the right-hand twin of
`opener_walk_pack`, assembled from `instPisAt_WScoped`,
`instPisAt_bounded`, `instPisAt_leaves` and `instPisAt_denote_doms`.
It compiled first try — the analogy held exactly, which is what one
should expect when both sides' frame lemmas were written by the same
hand for the same reason.

**The walk layer is now closed.**  Its whole content is four lemmas:

    defEqAtW_of        one comparison, from `DefEqClaimsR`
    defEqListW_of      the list fold
    opener_walk_pack   every walk's LEFT list  (all six)
    instPisAt_walk_pack  every walk's RIGHT list (all six)

Two packs cover twelve lists because every statement walk compares a
`(fvs…).map fvarTypeD` against an `instPisAt` output — the design's
economy showing again, and the reason the walks looked like the
campaign's big rock and are not.

What is left of `IotaThmR` is now purely assembly: instantiate the two
packs at the statement's own openings, feed `defEqListW_of`, and fill
the validated witness's two stubs.  `IotaThmNR` is the same against
`NestedChecked` (whose extra content — the stored `lvls`/`pins`, the
generalized major pin — is *syntactic*, so it adds witnesses, not
walks).

### Convergence file — the rock that dissolved

Worth stating plainly, because it is the campaign's economy thesis at
its cleanest and the shape recurs.

The `iota_j` statement walks were, on the tally, six walks each
needing per-element denotations and three frame facts on both sides —
twelve lists, and the design doc's own risk register called this the
campaign's big rock.  The walk layer closed at **four lemmas**:

    defEqAtW_of          one comparison, from `DefEqClaimsR`
    defEqListW_of        the list fold
    opener_walk_pack     every walk's LEFT list   (all six)
    instPisAt_walk_pack  every walk's RIGHT list  (all six)

plus `opener_fvar_pack`, which supplies the right pack's *spine*
hypothesis (the opener fvars themselves rather than their
annotations — two of its four conjuncts are free by computation).

Two packs cover most of twelve lists because **almost every statement
walk compares the same two shapes**: a `(fvs…).map fvarTypeD` against
an `instPisAt` output.  The rock was real when the tally was "six
walks each needing everything"; it dissolved once the shape was named.

**Correction (recorded rather than quietly fixed).**  "The same two
shapes" was too strong, and assembling `IotaWalksR` is where it shows.
There is a **third** shape: the *index* walk compares
`(largs.drop rP).take (mI - rP)` against `cres.getAppArgs.drop cnP` —
**application spine arguments**, not annotations and not `instPisAt`
domains.  Its denotations come from a different place again,
`denote_mkAppN_inv` (`Verify/Denote/Tele.lean`), which inverts a
denoting `mkAppN` into its head plus a `DenoteSpine` over the
arguments.

So the honest tally is **three shapes over twelve lists**, not two.
The economy claim survives intact — the point was never the number,
it was that the count is over *shapes* and not over *instances* — but
the number was wrong, and a convergence file that rounds its own
evidence in its favour is worth less than one that does not.

That is the general lesson and it is not about walks: *a tally over
instances is not an estimate — count the distinct shapes first.*  The
same move retired the six copies `BasisChain` replaced (§14.4), the
four `IndBottom` runs' shared statement walks, and now this.

### T6 — the walks are closed, not merely supplied

`storedType_pack` (a stored constant's type at any depth, from
`EnvR.wf` + `ty_denotes` + `opener_denotes_at`) and then `stmtWalk_of`:

    stmtWalk_of : … → DefEqListOk μ F env D
                        ((fvsP.take cnP).map fvarTypeD) cdomsP
                → DefEqListW μ env cval φ D
                        ((fvsP.take cnP).map fvarTypeD) cdomsP

That is **the** shape every `iota_j` walk has — a prefix of an opened
telescope's annotations against the domains an `instPisAt` run
collects from a stored type — so the walk layer is now closed as a
single consumable lemma rather than a kit to be re-assembled per
site.  Six lemmas total:

    defEqAtW_of  defEqListW_of
    opener_walk_pack  opener_fvar_pack  instPisAt_walk_pack
    stmtWalk_of

One assembly note: `instPisAt_walk_pack`'s spine hypothesis wants a
*three*-component package (frames only) while `opener_fvar_pack`
hands back *four* (frames + denotation), because the same pack serves
the pack's other argument, which wants the denotation alone.  Project
rather than re-derive — the mismatch is deliberate, not an oversight.

### T6 — `IotaWalksR`'s three shapes

For the assembly, the six components of `IotaWalksR` sort as:

| component | left | right | shape |
|---|---|---|---|
| `idxL/idxR` | `(largs.drop rP).take (mI-rP)` | `cres.getAppArgs.drop cnP` | **spine** |
| `domL/domR` | `xFvs.map fvarTypeD` | `cdoms.drop cnP` | annot / instPisAt |
| `preL/preR` | `(fvs.take rP).map fvarTypeD` | `rdoms` | annot / instPisAt |
| `lamL/lamR` | `(fvsP ++ xFvsP).map fvarTypeD` | `ldomsL` | annot / instLamsAt |
| `rhsS` vs applied | — | — | single `DefEqAtW` |
| `IotaSidesTyR` | — | — | its own pack |

`stmtWalk_of` serves rows 2–4 (with `take`/`drop`/`++` variations on
the left list — the pack is index-based, so a sublist is a projection,
not a re-derivation).  Row 1 needs the spine source above.  Rows 5–6
are single comparisons.

### T6 — all three walk shapes are packaged

`spine_walk_pack` closes the third shape: the frames descend from the
application's own (`Expr.WScoped.getAppArgs`,
`looseBVarsBounded_getAppArgs`, `fvarLeaves_getAppArgs`) and the
denotations from `denote_mkAppN_inv` after
`← Expr.mkAppN_getApp`.

`DenoteSpine` has `.take`/`.drop`/`.append`/`.length`/`.map` but **no
member accessor**, so extracting "this argument denotes" from it is a
three-line induction, written inline.  If a third consumer appears,
that is a `DenoteSpine.mem` for `Verify/Denote/Tele.lean` — flagged
now rather than after the duplication, per the relocation rule.

The walk layer's final inventory, seven lemmas covering all twelve
lists across three shapes:

    defEqAtW_of   defEqListW_of                  the comparison core
    opener_walk_pack  opener_fvar_pack           shape 1 (annotations)
    instPisAt_walk_pack  storedType_pack         shape 2 (domains)
    spine_walk_pack                              shape 3 (spines)
    stmtWalk_of                                  the common entry point

### T6 — stub 2's last unknown, resolved

Three of `IotaWalksR`'s six rows compare against `instPisAt` runs
whose subject is **renamed**: `cvA.type.renameConsts f`,
`cvj.type.renameConsts f`.  A renamed type is not a stored type, so
`storedType_pack` does not reach it and the question was whether
stub 2 hides another derivation.

It does not.  `denote_renameConsts` (`Verify/Denote/Rename.lean:66`)
gives `denote cval env φ d (e.renameConsts f) = denote cval env φ d e`
outright, under `RenameOkT cval env f` — and that premise is **already
built at exactly the site the bridge's rules fold will occupy**:
`Install/IndRecsS.lean:575` constructs
`RenameOkT mS.cval envSelf (fun n => …)` for the block renaming, with
a generic producer in `Verify/Extend/Block.lean:119`.

So every input to both stubs now exists, and `IotaThmR` is
transcription against three recorded tables: the witness permutation,
the six-row walk table, and the seven-lemma inventory.  The remaining
per-row work is choosing which pack serves which side and projecting
the `take`/`drop`/`++` variants — no new lemma, no new premise.

*Method note.*  This stretch produced no code, and that was the right
call: the question "does stub 2 hide another derivation?" is answered
by two greps, and answering it before writing the 40-component
witness is worth more than a partial witness would have been.  A
stretch that converts an unknown into a citation is a stretch that
did its job.

## T6 — `stmtWalk_of` reaches one row, not three (correction #2)

Transcribing `IotaThmR` validated **stub 1** — the parameter-domain
walk is exactly `stmtWalk_of m hrecSelf hcvR hctorSelf hcvC hopenP
(by omega) hcinstP hdeP`, and the whole witness above it elaborates
with the recorded permutation.  Assembling **stub 2** corrected the
walk table's pack assignments, which had been optimistic:

`stmtWalk_of` was written against a *stored* subject
(`storedType_pack` at a `find?`).  Rows 2 and 3 of `IotaWalksR`
compare against `instPisAt` runs on **renamed** subjects
(`cvA.type.renameConsts f`, `cvj.type.renameConsts f`), and row 2's
left list is a `drop` of the opening rather than a `take`.  So
`stmtWalk_of` serves the stub-1 row and no other; it is a convenience,
not the entry point.

**The entry point is `defEqListW_of` plus the three packs**, and the
per-row work is supplying the two element packages.  That was always
the design — `stmtWalk_of` over-specialised it, and the table
recorded the over-specialisation as if it were coverage.

### What the renamed rows need

One package, `renamedType_pack`, mirroring `storedType_pack` through
`denote_renameConsts`.  Its three frame conjuncts need
`renameConsts` preservation:

* `looseBVarsBounded` — **exists**
  (`Verify/Denote/IndFrame.lean:1131`, `:2204`);
* `WScoped` and the `fvarLeaves` index set — **do not**, and both are
  short structural inductions (renaming touches constants, never
  fvars or bvars; an fvar's *annotation* is renamed, which is exactly
  why `LeavesBounded` survives by the `looseBVarsBounded` lemma).

Per the relocation rule applied prospectively for the third time,
those two belong in the shared tier beside their existing sibling,
not in `SetR/` — their statements mention nothing lane-specific and
the TT lane's own renamed walks will want them.

*Method note.*  Two corrections to this file now, both from
assembling rather than planning: the shape count (two → three) and
the pack coverage (three rows → one).  Both were optimistic in the
same direction, which is worth naming: **a table written while
proving the easy row will overstate what that row's lemma covers.**
Write coverage claims after the hard row, or write them as
conjectures.

### T6 — the renamed rows are supplied

Three lemmas, all landed:

* `wscoped_renameConsts` and `leavesBounded_renameConsts` in the
  **shared tier** (`Verify/Denote/IndFrame.lean`), the prospective
  relocation rule's third application — renaming touches `const`
  heads and `proj` structure names, never `fvar` indices or `bvar`s,
  so neither statement is lane-specific and the TT lane's renamed
  walks will want both;
* `renamedType_pack` in the bridge, every conjunct its unrenamed twin
  composed with a preservation lemma, and the denotation
  `denote_renameConsts` under the `RenameOkT` the fold builds.

Two mechanical notes, both of which cost round trips:

* **`LeavesBounded` under renaming is far cleaner through an
  equation.**  The direct induction leaves one open goal per
  constructor after `simp_all`; proving
  `(e.renameConsts f).fvarLeaves = e.fvarLeaves.map (fun l => (l.1,
  l.2.1, l.2.2.renameConsts f))` first makes the consequence four
  lines.  General shape: *when a predicate over a derived list
  resists induction, prove the list's own equation instead.*
* **Do not give a shared-tier lemma a dotted `Expr.` prefix inside
  `namespace Setlec.TTVerify`.**  The prefix resolves against the
  enclosing `Setlec`, and the resulting constant is reachable under
  neither `Setlec.Expr.…` nor `Setlec.TTVerify.Expr.…` from a
  consumer that opens both.  Plain identifiers (`wscoped_renameConsts`)
  resolve unambiguously.  Also: `lake env lean` type-checks a file
  without installing its `.olean`, so a consumer keeps seeing the old
  one — `lake build <module>` between the two edits.

### T6 — `opener_walk_pack_gen`, and over-specialisation for the third time

`IotaWalksR`'s λ-row opens an `instPisAt` **residual** (`crestP`) at
depth `rP`, not a stored type at depth `0`, so `opener_walk_pack` does
not reach it — the third instance of the same mistake, after
`stmtWalk_of` (correction #2) and the two-shapes claim (correction #1).

`opener_walk_pack_gen` takes the subject's own package and its opening
depth.  It is not merely more general but **simpler**: the specialised
proof used the subject's `hasFvar`-freeness to argue that every leaf
of an opener's annotation must itself be an opener, where the general
form just uses the subject's own `LeavesBounded` for that branch.

*The habit, now with three instances.*  Each time I proved a lemma
against the first site that needed it and then wrote down coverage for
sites I had not tried.  The specialisation was never wrong — it was
always *true of its site* — and that is exactly what makes it
seductive.  The rule earned:

> **Generalise at the second site, not the third.**  A lemma written
> for one site and then claimed for others should either be
> re-elaborated at the hardest remaining site before the claim is
> recorded, or written with the site-specific inputs already
> abstracted.  The second is usually cheaper, and — as here — often
> yields the shorter proof.

## T6 — `iotaThmR_of`'s complete signature (traced)

Tracing every environment requirement of the six rows, before writing
them, gives the final signature.  Recording it here rather than
discovering it mid-witness, per the signature-fact discipline that
already saved one rewrite.

    iotaThmR_of (m : EnvR envSelf)
      (hro       : RenameOkT m.cval envSelf f)
      (hrecSelf  : envSelf.find? cvA.name = some ciR)
      (hcvR      : ciR.toConstantVal = cvA)
      (hctorSelf : envSelf.find? r.ctor  = some ciC)
      (hcvC      : ciC.toConstantVal = cvj)
      (htransfer : ∀ n ci, env'.find? n = some ci →
                     ∃ ci', envSelf.find? n = some ci' ∧
                       ci'.toConstantVal = ci.toConstantVal)
      (h : PlainChecked μ F env' envSelf f cvA mI rP cnP cnF j
             { r with rhs := rhsA } cvj)

`htransfer` is the new one, and it is why: `PlainChecked` finds the
`iota_j` **statement** at `env'`, while the walks need its type to
denote at `envSelf`.

**Corrected on first use.**  I first wrote it as *non-recursor
verbatim* transfer, reasoning that a statement is a
`defnInfo`/`thmInfo` and never a recursor.  That reasoning is sound
about the *world* and useless about the *proof*: nothing in
`PlainChecked` records the statement's kind, so the side condition
cannot be discharged.  `Install/IotaRuleS.lean:135` already says what
the right form is, in a comment: *"only the stored `ConstantVal`
matters, so a swapped entry (were the statement's name a recursor's)
serves just as well."*  So the transfer is of the **`ConstantVal`**,
which holds for every kind — recursors included, since installing
rules changes an entry's rules and not its `ConstantVal`.

The lesson, and it is the fourth face of the same habit: *a premise
justified by what is true of the data, rather than by what the
hypotheses in scope can prove, is not a premise — it is a wish.*  The
discipline caught it within the stretch this time (on first use, at
the cost of one grep) rather than after a witness rewrite, which is
the whole return on tracing before writing.

**Why the third environment fact appears only now.**  The signature
note recorded two (the constructor and recursor at `envSelf`) because
those are what the *`instPisAt` subjects* need.  The statement's own
type is needed by the *openers*, and I traced the subjects before the
openers.  The general form: a walk's environment requirements come
from **both** of its lists, and the left list's subject is the
statement itself.

With this, every row's inputs are named:

| row | left pack | right pack |
|---|---|---|
| idx | `spine_walk_pack` at `lhsS` (via `tbody`) | `spine_walk_pack` at `cres` |
| dom | `opener_walk_pack_gen` at the statement | `instPisAt_walk_pack` (`hcinst`) |
| pre | `opener_walk_pack_gen` at the statement | `instPisAt_walk_pack` (`hrinst`, `renamedType_pack`) |
| lam | `opener_walk_pack_gen` ×2 (`hopenP`, then `hopenX` at the residual) | `instPisAt_walk_pack` (`hlinst`) |
| rhs | single `defEqAtW_of` | — |
| sides | `IotaSidesTyR` from `hty1`/`hty2`/`hty3` | — |

### T6 — the sixth row's pack, traced

`IotaWalksR`'s last component, `IotaSidesTyR`, is the two side typings:
each side's inferred type is `DefEq` to the statement's `αS`, at every
correlating context.  It is `InferClaimsR` composed with
`DefEqClaimsR` — the same two-step `constantValR_of` runs at a
declaration's type — with two shape notes traced before writing:

* **The denotations are the caller's.**  `InferClaimsR` produces
  `denote lhsS = some Lv` only *inside* its `CtxOkR` premise, which
  `IotaSidesTyR` quantifies over `Δ`.  So `Lv`/`Rv` cannot be produced
  outside the binder and must be hypotheses — which the caller has,
  from `spine_walk_pack` at `tbody`.  Same discipline as every other
  pack: definedness in, comparison out.
* **`DefEqClaimsR` at the second step needs `CtxOkR … Δ tl` for the
  *inferred* type**, which is not a sub-expression of anything in
  scope.  The tool is `CtxOkR.of_subset` (`Bridge/Env.lean:115`) fed by
  `inferTypeCore_fvarLeaves` (`Verify/InferLeaves.lean:840`): an
  inferred type's leaves are a subset of its input's, so the input's
  `CtxOkR` transports.  That pairing is not obvious from either
  lemma's name and is the reason this row looked harder than it is.

With it, **every one of `IotaWalksR`'s six rows has a named pack and
every pack has named inputs.**  Nothing in `IotaThmR` is untraced;
what remains is writing.

## T6 — a vacuity near-miss, recorded against myself

Writing `iotaThmR_of` I could not state the six walk rows as a
hypothesis — they mention `PlainChecked`'s own bound existentials, so
there is nothing to quantify over outside the destructuring.  Wanting
to land the witness (which *is* real work: the 40-component
permutation and stub 1), I parameterised the missing half as

    (hwalks : ∀ φ : Name → Nat, False)

and discharged the last goal with `(hwalks _).elim`.  It compiled.
The battery was green.  **The theorem was vacuous** — its hypothesis
is unsatisfiable, so it says nothing, and no consumer could ever
apply it.

Caught before committing, but only just, and the mechanism that
caught it was noticing `False` in my own signature — not any gate.
That is the point worth recording:

* `lake build`, `lake test` and the arena **cannot** detect this.  A
  vacuous theorem is a true theorem.
* `#print axioms` cannot detect it either: no axiom is used.
* The no-`sorry` rule cannot detect it.  **A `sorry` is louder than a
  false premise** — it is flagged by the compiler, tracked by the
  gate, and impossible to forget.  Reaching for an unsatisfiable
  hypothesis to avoid a `sorry` inverts the safety ordering.

The design doc already names this hazard for the *product* (§4's R4
vacuity guard, on `CertifiedConfigS`); it applies with equal force to
the *scaffolding*.  The rule:

> **An unprovable premise is not a decomposition.**  Before
> parameterising a lemma on a hypothesis, name who will discharge it.
> If the answer is "nobody, it is a placeholder", the honest forms are
> a `sorry` (visible, gated) or not landing the lemma — never a
> premise that cannot hold.

Concretely for T6: `iotaThmR_of` is **not landed**, and will not be
until the six rows are written.  Everything about them is traced; what
is missing is the writing, and no signature trick substitutes for it.

### …and the backstop that does exist

Two additions to the near-miss record, both from the review:

**1. The assembly is the vacuity gate for scaffolding.**  A
false-premised helper cannot survive to the fourteen: the final
theorems are hypothesis-free modulo `EnvS` and the mode
configuration, and nobody downstream can discharge `False`.  So the
*product* is structurally protected — the exposure window is exactly
the interval in which a helper is claimed as "landed" while the
assembly that would expose it is unwritten.  In a campaign whose
cadence is per-stretch landings across compaction boundaries, that
window is the whole working period, and the interim claims are what
the coordinator reads.  The rule above closes precisely that window;
it does not add a guarantee the endgame lacks.

**2. Audit when the rule changes, not only when the code does.**
Having written the rule, I re-checked every hypothesis I had
parameterised across T6's stretches for a named discharger.  All
clean — but they had been *unchecked*, which is a different state from
*checked and clean*, and only the second is evidence.  A new rule
applies retroactively to the work already done under its absence;
running that pass is part of adopting the rule, not optional
diligence.

### T6 walk layer: the fifth over-specialisation instance (2026-08-28)

`opener_fvar_pack` was written against the *stored-subject, depth-0* site
and needed generalising the moment a second site appeared — exactly as
`opener_walk_pack` had.  `opener_fvar_pack_gen` (arbitrary subject with
package, arbitrary opening depth, `d₀ + k ≤ D`) now sits beside
`opener_walk_pack_gen`; both are in `Bridge/Decl.lean`.

Applying the recorded rule *generalise at the second site, not the third*:
the walk-pack family is now written in `_gen` form first, and the
specialised variants are kept only where they already have consumers.

**Recipe validated on row 2 (the ctor-domain row) of `iotaThmR_of`:**
`defEqListW_of` with, on the left, `opener_walk_pack_gen` + the fvar
facts from `opener_fvar_pack_gen` — both instantiated with an *explicit*
`(D := rP + cnF)`, since `D` appears only in the conclusion and `omega`
cannot see the intended depth otherwise (this was the spurious
"omega could not prove the goal") — and on the right
`instPisAt_walk_pack` fed by `storedType_pack` at the ctor, transported
across the rename by `denote_renameConsts hro`,
`wscoped_renameConsts`, `leavesBounded_renameConsts`.  A `List.drop cnP`
on the right side is absorbed by `List.mem_of_mem_drop`.

Rows 3 (rec-param domains) and 4 (λ-row domains) are the same shape at
different takes/drops; rows 1, 5, 6 remain.

### `iotaThmR_of` landed whole — the six rows, and what they cost

The lemma the vacuity rule held out of the repo is in, with no
`sorry` and no unsatisfiable premise.  The final shape of the work:
**six rows, five new packs, one retraction.**

Each row is `defEqListW_of` (or `defEqAtW_of`) over a *left* package
and a *right* package; the whole difficulty was that the campaign had
built domain-side packs only, and four of the six rows want something
else.  The packs added:

| pack | what it packages | why the domains pack could not serve |
|---|---|---|
| `instPisAt_res_pack` | the `instPisAt` **residual** | every frame lemma computes it and the domains pack discards it |
| `opener_body_pack_gen` | the **opened body** | ditto for the three opener frame lemmas |
| `instLamsAt_walk_pack` | the λ **domains** | no λ-side pack existed at all |
| `mkAppN_walk_pack` | a **built** spine | `spine_walk_pack` reads spines, it does not build them |
| `rhs_pack` | a stored fireable rule's **rhs** | not a stored *type*, so `storedType_pack` misses it |

Shared-tier support these needed, none of which existed in either
lane: `instPisAt_denote_res`, `instLamsAt_bounded`,
`instLamsAt_index_WScoped`.

**The signature change the λ-row forced, and the rule in it.**  The
λ-row needs `rhsA` to *denote*, which is `EnvR.rec_rhs_denotes`, which
is stated at a stored `recInfo` and a stored fireable rule.  So
`hrecSelf` was narrowed from a bare `ConstantInfo` lookup to
`envSelf.find? cvA.name = some (.recInfo cvA mI rP rules)`, plus rule
membership and non-inertness.  This is *not* the vacuity trap in
disguise: the discharger was named before the premise was written (the
iota fold walks exactly the stored rules, so it has all three).  The
distinction worth keeping: **a premise is legitimate when you can name
its supplier before you write it; it is a wish when you can only name
what is true of the world.**

*Two traps for the `_gen` family's users, both hit here:*

1. **A depth premise that fails to `omega` is usually an inference
   failure, not a false goal.**  `D` occurs only in the `_gen` packs'
   *conclusions*, so at a `have` there is nothing to fix it and
   `omega` is staring at a metavariable.  Supply `(D := …)`.  The same
   shape bit again at `mkAppN_walk_pack`, where `g` and `as` are
   determined only by the goal and an `obtain` has no goal: supply
   `(g := …) (as := …)`.
2. **The `hsp` premises are triples, the packs return quadruples.**
   `instPisAt_walk_pack`/`instLamsAt_walk_pack` want
   `WScoped ∧ bounded ∧ LeavesBounded` (the denotation travels
   separately, indexed); a pack's output must be projected, not
   passed.  Three of the five call sites needed this and all three
   error messages were identical.

**Retraction, recorded against myself.**  `CtxOkR.of_subset` was
written into `CtxOkR.lean` and deleted minutes later — it has existed
in `Bridge/Env.lean` since the bridge was built.  The inventory search
that the campaign's own rules require *before writing any helper* was
not run; nothing but the duplicate-declaration error caught it.  The
five packs above were all inventory-checked first and all five were
genuinely absent, so the practice works when applied — the failure was
skipping it on the one helper that looked too small to be worth a
grep.  **Size is not a reason to skip the inventory check; it is the
best predictor that the helper already exists.**

### `IotaThmNR`: every input traced but one — the assembly plan

Traced ahead of writing, per the trace-before-write discipline.  The
nested pack is *not* "the plain pack plus witnesses" (my earlier
estimate, and the fourth time a tally has understated a shape count):
its six `IotaWalksR` rows sit at a **different constructor spine** and
a **level-instantiated** constructor type, and it carries a seventh
row that is `TypedListW`, not `DefEqListW`.

**Inputs that already exist** (no new lemma needed):

* the constructor type at `lvls`, packaged — `denote_declTypeR` +
  `frame_declTypeR` (`Bridge/Certs.lean:141,171`), which are exactly
  "a stored declaration's type at a level instantiation"; the plain
  path never needed them because its constructor is at the identity
  instantiation;
* the pins' **syntactic** frame facts — `nestedRuleShape` itself
  certifies `!p.hasFvar && p.looseBVarsBounded rP &&
  p.constsResolve envSelf && p.allLevelParamsDefined lps`
  (`Kernel/Modeled.lean:177-178`).  Read the *shape function*, not the
  premise bundle: `NestedChecked` carries the pin facts only by
  carrying `nestedRuleShape`'s verdict;
* `instSpine` transport of those facts — `instSpine_WScoped`,
  `instSpine_closed`, `fvarLeaves_instSpine`
  (`Verify/InstSpine.lean:42,55,~80`), all three already proved;
* rows 1–6 themselves — the five packs `iotaThmR_of` needed, unchanged.

**The one open input: the pins' denotation.**  `TypedListW`'s
`TypedAtW` puts `∃ Ev, denote … p = some Ev` *outside* its `∀ Δ`, and
the soundness side genuinely consumes it
(`Install/IndBottomNestedS.lean:328-345` reads the pins' canonical
values back through `denote_openRev`) — so it cannot be weakened away.
It is also not free: `constsResolve` records that a pin's constants
*exist*, not that their level arities match `denote`'s `.const`
clause, which is the same gap `EnvR.rec_rhs_denotes` was added to
close for rule right-hand sides.

The route that should work, to be confirmed first thing next stretch:
`TypedListOk` gives `inferTypeCore … p = .ok t`, and `InferClaimsR`
turns that into the denotation — but it demands a `CtxOkR … Δ p`, and
`TypedAtW`'s existential has no `Δ` in scope.  The campaign's own
device for this is `OpenCtxR` (`SetR/Decl.lean:61`, "the opened
variables' annotations at their own depths", pinned rather than
existential *precisely* so it is not vacuous-premise-unsound).  So the
missing step is a **canonical-context lemma**: an `openPisAtFvars`
opening yields a `Δ` with `OpenCtxR`, and `CtxOkR … Δ e` for anything
whose leaves are among the openers.  Check whether one exists before
building it; if it does not, it is the next stretch's single new
derivation and everything else is transcription.

*The estimate that keeps failing.*  Four times now a stretch has been
sized by counting instances rather than shapes, and four times the
shape count was higher.  The nested pack was called "witnesses, not
walks" before anyone read `nestedRuleShape`.  The discipline that
works is the one applied here: **trace every input to a named
supplier before writing a line, and let the one input that has no
supplier be the stretch's stated risk.**

### The pins' denotations: two spellings, two different sources

The `IotaThmNR` trace's single open input turned out to be **two**
inputs, and the second was invisible until the first was solved.  The
nested pack's pins appear at two spellings:

* `pinsP = pins.map (instSpine (fvsP.take rP) (rP-1))` — at the
  *recursor type's* openers, unrenamed;
* `pinsF = pins.map (instSpine (fvs.take rP) (rP-1) ∘ renameConsts f)`
  — at the *statement's* openers, renamed.

They are different expressions and neither denotation gives the other:
`denote` returns `none` on a loose `.bvar` (`Verify/Denote.lean`'s
catch-all clause), so there is no "denote the bare pin once and
re-instantiate" route — the `instSpine` that closes the pin is
load-bearing, and it closes it at two different spines.

**`pinsP` denotes because the checker inferred its type.**
`TypedListOk` gives the verdict; `denote_of_inferR` converts it, at a
context built by `openPisAtFvars_ctxOkR` on `hopenP` (depth `rP`),
covered onto the pin by `CtxOkR.of_cover` + `fvarLeaves_instSpine`,
and lifted to the walk depth `rP + cnF` by `CtxOkR.weakenN`.

**`pinsF` denotes because the statement's own major does.**  Nothing
in `NestedChecked` infers a type for `pinsF` — but `hmaj` says the
statement's major is `Expr.ErasedEq` to
`mkAppN (.const (f r.ctor) lvls) (pinsF ++ xFvs)`, the major is a
spine argument of `lhsS` (which denotes), and **`denote_erasedEq`
already exists** (`Verify/Denote/Inst.lean:265`) — its own docstring
says it: *the pin's tolerance and the denotation's blindness are the
same set of syntax*.  So `spine_walk_pack` on `lhsS`, then
`denote_erasedEq hmaj`, then `denote_mkAppN_inv`.

The three *syntactic* facts are not `ErasedEq`-transportable (erasure
forgets fvar annotations, `WScoped` does not), so they are taken
directly at both spellings by `instSpine_pin_pack` — stated over an
abstract spine, gen-first, because the second call site was known
before the first was written.

*The estimate, corrected once more.*  "One open input" was itself an
undercount, for the same reason as the four before it: the two pin
spellings are one *instance count* and two *shapes*.  The rule now has
a fifth confirmation and a sharper form: **when the same object
appears under two different instantiations, that is two inputs until
you have produced the transport that makes it one.**  What saved the
estimate was that both sources already existed — the campaign's
lemmas keep turning out to be built, which is the inventory rule's
positive half.

`IotaThmNR` is now transcription: every input named, every supplier
existing.

### `IotaThmNR` transcribed — the trace's dividend, measured

`iotaThmNR_of` compiled **with no `sorry` on the first full attempt**,
both bullets, ~250 lines.  That is what a complete trace buys: the
previous stretch converted every input into a named supplier, and this
one was typing.  The only work left at write time was arithmetic
(`cnF + rP = rP + cnF`) and one recorded-trap recurrence.

**One finding on the way in.**  `IotaThmNR` demanded `eqUpToNames` on
the nested major, and `NestedChecked` **cannot supply it**: the
checker does test `eqUpToNames`, but `checkIotaThmN_inv` weakens it
through `ErasedEq.of_eqUpToNames`, which is sound only in that
direction — `eqUpToNames` still compares `fvar` annotations, which
`ErasedEq` drops.  The campaign's own spec asked for something
strictly stronger than the checker's own inversion delivers.

Nor was the stronger form wanted: `IndBottomNestedS` takes the pin as
`_hmaj` (*unused*), and the soundness argument reads the major through
`denote_erasedEq`.  Decisive evidence: the two SetR call sites were
already applying `ErasedEq.of_eqUpToNames` by hand, so **dropping the
wrapper was the entire diff**.  `IotaThmNR` now carries `ErasedEq`.
No final claim changes — the conjunct is unused downstream, so a
weaker intermediate relation leaves the theorems untouched.

The general shape, worth a line: **when a spec and an inversion
disagree, check which one the consumer reads before deciding which to
move.**  Here the consumer had already voted, twice, in the source.

**Recorded trap, recurring.**  `DenoteSpine.mem_denotes` declared
inside `namespace Setlec.SetR` resolves as
`Setlec.SetR.DenoteSpine.mem_denotes` and is reachable under neither
path — the dotted-prefix trap, hit again.  Renamed to the plain
`denoteSpine_mem_denotes`.  It was extracted from an inline `have`
inside `spine_walk_pack` on the *second* consumer appearing, which is
the relocation rule applied at its stated threshold.

New shared helpers this stretch: `opener_denotes_below` (denotability
descends along the depth index — `opener_denotes_at`'s equation read
backwards, needed because the pins are denoted at the walk depth but
their residual is taken at the opening depth), `getLastD_mem`,
`typedListOk_infer`, `denoteSpine_mem_denotes`.

### A premise with the right supplier at the wrong environment

`iotaThmR_of`'s λ-row needed the rule's right-hand side to denote, and
I narrowed its recursor premise to a stored `recInfo` plus rule
membership so that `EnvR.rec_rhs_denotes` could supply it.  The
supplier check was run and passed — and it was still wrong.

`RuleChecked`'s `env₀` is the **provisional** environment, the one
carrying the block's *rule-less* recursors (its own docstring says so).
The rule is not stored there, so `rec_rhs_denotes` has nothing to say
about it, and no caller could ever discharge the premise.  It was
satisfiable in the abstract and unreachable in fact.

The real supplier was in `IotaRuleR`'s own text all along: the fold
carries `inferTypeCore … 0 rhsA = .ok rhsTy`, which `InferClaimsR`
turns into the denotation at the empty context.  Both `iotaThmR_of`
and `iotaThmNR_of` now take `hrhsnf`/`hrhsb`/`hrhsDen` directly and
lift with `denote_closedExprR`; `rhs_pack` is **retracted** (it was
correct, and had no caller left).

This is a subtler cousin of the vacuity trap, and it deserves its own
line beside the legitimacy rule:

> **Naming a supplier is not enough — name the *environment* the
> supplier speaks at, and check it is the one the caller holds.**

Which is P2, verbatim, applied to a premise I wrote myself.  P2 has
been on this file's first page since T5 and I ran it on other people's
premises and not on my own.  The cheap mechanical form: when a new
premise mentions an environment variable, write down which of the
caller's environments it is (`env`, `env₀`/provisional, `envSelf`,
`env'`) *before* writing the signature.

### The iota layer closes: `iotaRuleR_of` and the rules fold

`IotaRuleR` is a relation between the *input* rule and the *returned*
one, and `RuleChecked` is stated over the returned rule alone — so
three facts the checker plainly establishes had been dropped by the
inversions.  All three were landed **additively**, in the same tail on
`checkIotaRule_inv`, with `RuleChecked` untouched (so the TT lane sees
no change at all):

1. the input-to-output link (`r' = {r with rhs, ctorParams, fire}`
   and the raw rhs's well-formedness);
2. `fire = .inert → nestedRuleShape … = none` — `checkIotaThmN`
   returns `.inert` only from a `none` shape (a `some` shape whose
   theorem then fails is a positive *decline*), which
   `checkIotaThmN_inv`'s inert disjunct had not said;
3. `fire = .nested lvls pins → nestedRuleShape … = some (lvls, pins)`
   — `IotaThmNR`'s own first conjunct, which `RuleChecked` records
   only in *decomposed* form.

(3) is where the recorded rule earned its keep: the decomposition is
enough to *rebuild* the shape verdict from `nestedRuleShape`'s guards,
and that is precisely **a field to reconstruct**.  Pinning it was four
lines; reconstructing it would have been a lemma about the checker's
own control flow.

**The `cases h : e` trap fired four times in this stretch alone** —
each time the goal was rewritten and the honest witness was `rfl`, not
the named hypothesis.  It is now the single most frequent error in the
campaign.  Companion trap, new: `nomatch hc, fun …` parses `nomatch`
greedily over the comma; inside an anonymous constructor every
`nomatch` lambda needs parentheses.

With `iotaRulesR_of` the whole iota layer — the campaign's largest
single rock — is closed.

### Rock 2 landed — and the vacuity gate fired, exactly as designed

`projFnR_of` (`checkProjFn → ProjFnR`, the last of the six `DeclR`
front doors) and `projInstallRS` (the interleaved fold) are in.  Five
stage inversions transcribe; the two semantic conjuncts were already
machined:

* the rule's front door is `checkProjRule`'s own depth-`0`
  `inferTypeCore` verdict through `InferClaimsR` — the same three
  lines as `iotaRuleR_of`'s;
* the sides pack is `iotaSidesTyR_of`, fed by **`projStmtParts`**,
  which turns the statement's *pin* into its opened spine and returns
  it as a literal three-element list — so the `getD 0/1/2` slots
  `IotaSidesTyR` names are its entries, and the membership side
  conditions are `by simp`.

One additive pin on the way: `checkProjTy_inv` was dropping the
`(pty.stripPis (nP+1)).isSome` guard that `ProjFnR` records.  Four
consumers, all taking a discard.

**The vacuity gate fired.**  The earlier `projInstallR_of` was
parametric in
`hfn : ∀ {e e' cval i}, … → ProjFnR μ F e cval …` — a `ProjFnR` at a
*universally quantified valuation*.  `ProjFnR`'s rule front door and
sides pack are semantic, so no such thing is provable: the lemma was
**vacuously premised**, and it compiled, and it sat in the tree.  It
was caught by exactly the mechanism the record predicted — *the
assembly is the vacuity gate for scaffolding*: `projFnR_of` needs an
`EnvR e` and therefore cannot discharge `hfn`, so the obligation could
not be closed and the lemma had to be retracted.  Finding 8's
scorecard had already put `ProjFnR` in the interleave column; the
plain form was written before the scorecard and never revisited.

Worth stating as a check, since the backstop is late by construction:
**a premise quantified over a valuation with no invariant attached is
the signature of the vacuity trap** — an `EnvR`/`EnvS`-free `cval` in
a hypothesis about a semantic relation should be read as "unprovable"
on sight, not at assembly time.

### The vacuity sweep, and a base-environment correction

**Sweep (clean).**  Applying the new early check — *a valuation with
no invariant attached in a semantic hypothesis reads as unprovable on
sight* — across `Setlec/SetR/*`: the only shape that matters is a
**valuation bound *inside* a hypothesis**, not a valuation parameter
of the theorem.  The discriminator is exactly what separated
`projInstallR_of`'s `hfn : ∀ {e e' cval i}, …` (quantified inside, and
so demanding the relation at *every* valuation) from `checkDeclR_of`'s
`{cval}` (a theorem parameter the caller instantiates once at
`m.cval`).  With that discriminator, the sweep over every `SetR`
theorem binding a `TConstVal` returns **one hit and it is the one
already retracted**; the `Install/*` helpers that take a `…R` relation
at a free `cval` all conclude *syntactic* facts (freshness,
monotonicity, name guards) and are P1-correct.

**Correction found on the way into `indRecsRS`.**  `IndRecsFoldR`
passed the running **accumulator** to `IotaRulesR`, but
`checkIndRecs` runs every `checkIotaRules` at `env₂` — the fixed
pre-group environment — and the accumulator only *collects* results.
So the relation asked for a strengthening the checker does not
deliver, and the bridge would have owed a monotonicity transport of
`IotaRulesR`/`IotaRuleR`/`IotaThmR`/`IotaThmNR` along the accumulator.
Worse, that transport is not even *true* without an extra pin: the
inert branch needs `nestedRuleShape … = none` to survive, and
`nestedRuleShape`'s only environment dependence is an `isSome` guard
that a growing environment can flip.

The previous stretch's rule decided it: **check which environment the
consumer reads.**  `indRecsFoldS` consumes `IotaRulesR` only through
`FoldUpS · envSelf` and `find? eqName`, both of which the *base*
satisfies a fortiori.  So `IndRecsFoldR` now takes `envBase`
explicitly and names it, `indRecsFoldS` takes `FoldUpS envBase
envSelf` and the base's `Eq` lookup as fixed premises, and the
accumulator keeps its real job — collecting the installed recursors.

The general form is worth keeping beside the P2 line: **a fold's
relation should name the environment its checker actually ran at, not
the one its accumulator happens to be holding.**  The two coincide
only at the first step, which is why this kind of slip survives every
`nil`-case sanity check.

### `indRecsRS` — and the base-environment fix paying for itself

With `IndRecsFoldR` re-based, `indRecsFoldRS` is **thirty lines and
compiled first try**: nothing in the relation depends on the
accumulator any more, so the fold is a plain induction calling
`iotaRulesR_of` at the fixed `mS.toEnvR`.  Had the relation kept
naming `acc`, this same fold would have owed a four-relation
monotonicity transport plus an unprovable side condition.  That is the
clearest measurement yet of what naming the wrong environment costs:
**the difference between a thirty-line induction and a blocked one.**

`indRecsRS` itself is the phase's shape, transcribed: empty case,
pinned-`Eq` guard, `provisionRecsRS` (interleaved — its per-recursor
`MemberValR` sits at the growing accumulator), then the rules fold
(not interleaved).  It produces `IndRecsR` *alone*; the caller runs
`indRecsS` on it for the invariant, which is what "does not
interleave" means operationally.

Relocation applied at its stated threshold: `blockRenameOkT` (the
block renaming is sound at the provisional environment) was inline in
`indRecsS` and moved out when `indRecsFoldRS` became its **second**
consumer — not on first sighting, not on the third.

The three interleaved walks are now `indMembersRS`, `provisionRecsRS`,
`projInstallRS`; the two non-interleaved bridges are `templatesR_of`
and `indRecsRS`.  Finding 8's four-fold scorecard is fully cashed.

### `declIndRS` traced — one new obligation, and it is a *direction*
### problem, not a size problem

`declIndS`'s body is ~100 lines of premise derivation feeding the four
install folds.  `declIndRS` reuses all of it with the folds replaced
by their `RS` counterparts — with **one circularity**, found by
tracing rather than by writing:

`indMembersRS` takes `BlockInstalledTT blockNames env m.cval` as an
*input*.  In `declIndS` that comes from `hI0gen`, which proves it
**vacuously** — no block name is stored at the base — using
`indMembersR_fresh` / `indRecsR_fresh`, i.e. **from the relations**.
But in the bridge the relations are what we are producing.  The
implication runs the wrong way.

So the one thing `declIndRS` needs that does not exist is a
**checker-side** twin of that freshness argument:

> from `checkIndDecl … env block = .ok env₂`, conclude
> `∀ ci ∈ block, env.find? ci.name = none`

— a fold-freshness induction over `checkIndMember` (whose
`checkMemberVal` checks freshness at its own accumulator, and the
accumulator only grows) and over `provisionRecs` inside
`checkIndRecs`.  It mirrors `indMembersR_fresh`/`indRecsR_fresh`
exactly, on the other side of the bridge.

*Why this is worth a line beyond its size.*  Every previous missing
input in this campaign was a **missing fact**; this one is a fact that
exists, proved, in the right file, pointing the wrong way.  The
recognition rule:

> **When a bridge reuses an install's derivation, check each premise
> for which side it is derived *from*.  A premise the install gets
> from the relation is a premise the bridge must get from the
> checker.**

That is the same shape as finding 8 (the install consumes what the
bridge produces) one level down, at the *premises* rather than the
relation — and it is the last place it can hide, because
`checkDeclR_sound` and the fold above it take no invariants at all.

Everything else in `declIndRS` is transcription: `indMembersRS`,
`indRecsRS` + `indRecsS`, the four projection premises verbatim from
`declIndS` (extraction to a shared lemma is the cleanup once both are
stable — the interface is wide enough that doing it before the second
consumer compiles would be guessing), `projInstallRS`,
`templatesR_of`.

### `declIndRS` landed — and the "new obligation" was already built

The trace's one open item was a **direction** problem, and its
resolution was the inventory rule's positive half for the fourth time:
`checkIndMember_fold_names` and `checkIndFold_mono`
(`Verify/Extend/Ind.lean`) and `provisionRecs_fresh`
(`Verify/Extend/Recs.lean`) all existed.  Only the last hop was
missing — `checkIndRecs_fresh`, ten lines unfolding the phase down to
`provisionRecs_fresh` — and with it the base `BlockInstalledTT` comes
from the *checker's verdict* instead of from the relations.

`declIndRS` is then `declIndS` with the five folds swapped for their
bridge twins.  The single-constructor arm and the generic arm both
went through; the whole thing is `split at h` down the phase structure
(the `unless`/`match` chain) and then the premise derivation verbatim.

*One tactic note worth keeping.*  `rw [if_pos hguard] at h` fails on
`checkIndDecl`'s split guard even though the `if` is at the head of
`h` — the `Decidable` instance `by_cases` produces is not the one the
`if` carries, so the pattern does not match.  **`split at h` is the
robust form for a checker `unless`**, and it hands back the guard as a
named hypothesis in the positive branch, which is what the relation
wants anyway.

Not extracted: the ~60 lines of projection premises now appear in both
`declIndS` and `declIndRS`.  The interface is wide (two relations, two
`EnvS`s, five block facts) and the relocation rule says to extract on
the second consumer — which this is — so it is queued, deliberately,
until the assembly above it is stable.  Recording the debt rather than
paying it mid-assembly is the judgment; the alternative was to guess a
signature while both consumers were still moving.

The `indDecl` branch is now bridged end to end.  What remains is
`checkDeclR_sound` (the six-way dispatch), the `checkDecls` fold, and
the fourteen.

### The assembly: `checkDeclR_sound` and the fold — plus the trap's
### third instance, in the dispatch itself

`Setlec/SetR/Bridge/Sound.lean` closes the per-declaration route:
`checkDeclR_sound` (six-way dispatch) and `foldlM_R` (the `checkDecls`
fold, carrying `EnvS` along by `declStepS`).  It is the transpose of
the TT lane's `checkDeclTT` / `foldlM_TT` pair, line for line.

**The unattached-premise trap, third instance — and it was in
`checkDeclR_of`.**  Its six branch obligations re-quantified `env`
*inside* each hypothesis while `cval` stayed fixed at the theorem
level:

```
(hdefn : ∀ {env env₂ …}, checkDecl … env (.defnDecl …) = .ok env₂ →
   DeclDefnR μ F env cval …)
```

`DeclDefnR` contains `ConstantValR`, hence `Infer`, hence a semantic
claim about a valuation that is *not* the one belonging to the
quantified environment.  No caller can discharge it: `declDefnR` is
proved at `m.cval` for `m`'s own `env`.  Found by trying to apply the
dispatch, which is the structural backstop again — and, again, on a
lemma that predated the rule.  The fix is one binder: the dispatch
runs at **one** environment and never needed the generality.

Three instances now, all the same shape and all pre-existing:
`projInstallR_of`'s `hfn`, `checkDeclR_of`'s six, and (differently
sourced) the recursor premise re-aimed two stretches ago.  The
preemption is stated and now demonstrated: **an `EnvR`/`EnvS`-free
valuation inside a hypothesis about a semantic relation is
unprovable; the parameter/premise distinction is the whole test.**

**A dependence made visible.**  `checkDecl`'s `indDecl` clause is not
`checkIndDecl` — it first consults `directParts?`, whose
direct-structure arm `DeclR` does not model.  The route is sound
because `directStructsEnabled` is the compile-time constant `false`.
That is now a *named* lemma, `directParts?_none`, discharged in
exactly one place, so the audit can find the dependence instead of
having it hide inside a `simp` set.  If the direct path is ever
enabled (task #82's gate), this lemma is where the campaign breaks —
by design.

The three obligations left as named hypotheses (`NatEqsBridgeR`,
`DivModPinBridgeR`, `ReducePinBridgeR`) are all stated **attached**:
each quantifies over an `EnvS V env` and speaks at that `m`'s own
valuation.  That is deliberate, and it is the rule above applied
prospectively rather than retroactively for once.

### Three of the fourteen land; the other eleven are a different shape

`Setlec/SetR/Main.lean` carries `no_constant_of_Empty_R`,
`checkDecls_sound_R` and `no_proof_of_Empty_R` — the three stated over
`checkDecls` at `fueledOps`.  `no_proof_of_Empty_R` takes the §3 route
exactly as planned: `EnvS.mem_type` at the stored constant gives
`interp ρ (cval c ψ) ∈ˢ interp ρ t`, `empty_pinned` identifies `t` as
`emptyT u`, `interp_emptyT` collapses it to `SetTheory.empty`, and
`not_mem_empty` closes.  Nine lines.

**The other eleven are not more of the same.**  Each `_S`/`_C`/`_SP`
variant re-runs its *own* driver fold — `foldlM_soundS`,
`foldlM_soundC`, `foldSP` in the Model lane — because the drivers are
different functions (`checkDeclsShared`, `cachedOps`,
`checkDeclsSP` over parsed indices), not different arguments to one.
So the remaining work is three driver-fold inductions, each
transposing an existing Model-lane one, and then eight corollaries
that are two lines each.  Counting them as "eleven theorems" overstates
the work by about three; counting them as "three folds" understates it
by the parsed-index one, which carries the store's `WF` and `Ext`
threading.  The honest unit is **three folds and eight corollaries**.

*Axiom audit, on everything landed.*  All three of the fourteen, plus
`checkDeclR_sound`, `foldlM_R`, `declIndRS`, `iotaThmR_of`,
`iotaThmNR_of`, `iotaRulesR_of`, `projFnR_of`, `indRecsRS`,
`projInstallRS`: `[propext, Classical.choice, Quot.sound]`, exactly.
Zero `sorry` in the tree (the six textual hits are all the word
`sorryAx` in prose).

### The three carried obligations, audited against the trap family

The coordinator is right that a carried hypothesis is where an
undischargeable premise could hide from every gate.  Applying the
campaign's own tests to all three, with evidence, before building:

**They do not have the vacuity signature.**  Each is stated
*attached* — `∀ {env} (m : EnvS V env) …`, concluding at `m.cval` for
`m`'s own `env`.  That is the parameter/premise test the third trap
instance sharpened, and all three pass it by construction.

**Each has a named supplier at a named environment.**

| obligation | supplier | environment |
|---|---|---|
| `NatEqsBridgeR` | `DefEqClaimsR` (via `checkBridge`) on `certifyNatEqs`' per-pair `isDefEqCore … 2` verdict | the *defn site's* `env` — the same one `declDefnR` is proved at |
| `DivModPinBridgeR` | `InferClaimsR` + `DefEqClaimsR` on `checkDivModPin`'s certificate verdicts at depth `4` | ditto |
| `ReducePinBridgeR` | `DefEqClaimsR` on `checkReducePin`'s two identity verdicts at depths `0` and `1` | ditto |

**Positive evidence they are true.**  Each is the transpose of a fact
the *Model lane already proves*, from the *same* checker verdicts at
the *same* environment: `certifyNatEqs_inv` / `natop_eqs_sound`
(`Model/Consistency.lean:89,151`), `checkReducePin_run_inv` (`:354`),
and the div/mod certificate block.  And the SetR versions are
**strictly easier** than the Model ones: `NatEqsR` asks only for the
relation family's `DefEq`, which `DefEqClaimsR` yields directly —
none of the interp-level recurrence `natop_eqs_sound` establishes is
needed.

**What is genuinely missing, and it is not machinery — it is three
frame packages.**  Each equation/certificate side needs the four
inputs every bridge consumes (`WScoped`, `looseBVarsBounded`,
`LeavesBounded`, `denote`) plus a `CtxOkR` at the *canonical* context
the checker used:

* `WScoped 2` is already supplied — `natOpEquations_wscopedB`
  (`Verify/BridgeWfImp.lean:2048`), plus `natOpEquations_shallow`
  already in `SetR/Install/ValueKinds.lean`;
* the leaf and denotation facts are not, and must come from the
  generated pins' shape (finitely many op names, so per-name
  computation) transported across `Expr.substConst0 c value'` using
  `value'`'s facts from `ValueFrontR`;
* the canonical contexts are `[natVR, natVR]` (depth 2),
  `[H2, H1, natVR, natVR]` (depth 4) and `[E]` (depth 1) — this is
  `Decl.lean`'s own "pinned `Nat` entries" note, and no `CtxOkR`
  producer for them exists yet.  It is the sibling of
  `openPisAtFvars_ctxOkR`: same shape, canonical entries instead of
  opener annotations.

**Honest size.**  One shared piece (the canonical-context `CtxOkR`
family) and three instantiations, the div/mod one the largest because
its certificates are `Infer`-side at depth 4 with optional hypothesis
slots.  That is a stretch, not a session, and it is the *only* thing
between the current spine and hypothesis-free theorems.

**The gate is not cleared.**  Reporting this rather than claiming it,
per the rule the campaign has been running on: a premise nobody has
discharged is a premise, however good the evidence.

### The shared blocker, removed: `CtxOkR.constCtx`

The one piece all three carried obligations wait on is built.
`CtxOkR.constCtx` (`SetR/CtxOkR.lean`) discharges the correspondence
at a context every entry of which is one **closed** valuation `A`,
against an expression all of whose fvar leaves carry the *same*
annotation denoting `A`.  Fifteen lines: the leaf's `Infer` is
`Infer.bvar` at `List.replicate`, and the lift collapses because `A`
is closed (`VExpr.liftN_eq_self_of_closed`).

That is exactly the `[natVR, natVR]` / `[H2, H1, natVR, natVR]` /
`[E]` shape the three obligations need, generalised once rather than
three times — the sibling of `openPisAtFvars_ctxOkR`, canonical
entries instead of an opening's annotations.

What remains per obligation is now only its own **frame package** for
the equation/certificate sides: the leaf and denotation facts of the
generated pins, transported across `Expr.substConst0 c value'`.
`WScoped` is already supplied (`natOpEquations_wscopedB`).

### FINDING — the audit checked attachment and missed the *other*
### quantifier

Last stretch's audit cleared all three carried obligations on the
attachment test.  Attempting the first discharge shows that test was
**necessary and not sufficient**: two of the three are over-general in
a *second* quantifier, and their conclusions assert things their
hypotheses do not determine.

* `NatEqsBridgeR` quantifies `{eqs}` freely and concludes
  `NatEqsR … eqs`, which demands `denote … 2 eq.1 = some L`.  The
  hypothesis is only `certifyNatEqs … = .ok true`, i.e. `isDefEqCore`
  verdicts — and a verdict does **not** imply its subjects denote
  (`DefEqClaimsR` takes the frame facts as *inputs*).  For arbitrary
  `eqs` the claim is not warranted.
* `DivModPinBridgeR` quantifies `{v}` freely and concludes
  `DivModPinR … n v`, but `checkDivModPin ops env env' c` **does not
  take a value** — it reads one out of `env'`.  So `v` is free in the
  conclusion and absent from the hypothesis.  The same over-generality
  is in `declDefnR`'s own `hdm`, which is where mine inherited it;
  `DeclDefnR`'s conjunct correctly names the branch's `value'`.
* `ReducePinBridgeR` is clean: its `value` appears in the
  `checkReducePin` verdict.

The test, in its sufficient form:

> **An obligation is dischargeable only if every free variable of its
> conclusion is determined by its hypotheses.**  Attachment (the
> valuation) is one instance of this; `eqs` and `v` are two more, and
> they hid behind it because attachment is the instance the campaign
> had a name for.

This is the trap family's fourth and fifth members, and — as with the
first three — both compiled and both sat in the tree.

### The right factoring, and the first discharge

Rather than constrain `eqs` to the checker's own list (which drags the
`natOpEquations` computation into the obligation), the bridge is split
at the seam it already has:

* **`NatEqFrameR`** — one side's frame package: the three syntactic
  facts, the `Nat`-annotated-leaf shape, and the denotation;
* **`natEqsBridge_of`** — *proved*: given a frame package for both
  sides of every pair and `natName` stored at zero level parameters,
  the `certifyNatEqs` verdict yields `NatEqsR`.  The context is
  `CtxOkR.constCtx` at the pinned entries, and
  `List.replicate 2 (natVR …)` unifies with `[natVR, natVR]`
  definitionally, so the canonical-context lemma lands with no
  adapter.

So the **semantic half of the `Nat` obligation is discharged**, at
exactly `[propext, Classical.choice, Quot.sound]`.  What remains is
purely syntactic: `NatEqFrameR` for `natOpEquations`' substituted
sides — a finite case analysis over `natOpNames` transported across
`Expr.substConst0`, with `WScoped` already supplied by
`natOpEquations_wscopedB`.  No semantic content, and it belongs in
`declDefnR` where the equation list is known.

The div/mod obligation needs the same split *plus* the `v`-freeness
repair in `declDefnR`.

### A named check can mask the unnamed instances of its own principle

Worth its own line, because it is the *mechanism* behind the last
finding rather than the finding itself.

The campaign named **attachment** — "a valuation with no invariant
attached in a semantic hypothesis reads as unprovable on sight" —
after the trap's third instance.  The name made that instance cheap to
check and, for the same reason, made it the *only* instance anyone
checked.  `eqs` and `v` are the identical principle at a different
variable, and both survived an audit that was looking hard, in the
right place, at the right lemmas.

> **When a check earns a name, re-derive the principle it came from
> and enumerate the other variables it applies to.**  A named check is
> a searchlight: it makes one spot bright and the rest darker.

The general principle, which should now be the one carried:
*every free variable of a conclusion must be determined by the
hypotheses.*  Attachment is its instance at the valuation.

### `NatEqFrameR`'s syntactic half: the characterisation exists, in
### the other lane

The remaining `Nat` work is `NatEqFrameR` for `natOpEquations`'
substituted sides.  A seven-way case split over `natOpNames` is *not*
the right shape, and does not need to be: the TT lane already
characterised the fragment.

`natFragOk` (`TTVerify/NatOpPin.lean:44`) is a four-constructor
decidable grammar — `sort`; `fvar` at index `0`/`1` annotated
`Nat`; `const` either the operation itself or stored at matching level
arity; `app` — and `natOpEquations_frag` (`:204`) proves every
equation side satisfies it from exactly the storage facts
`natOpGuard` provides.  **`NatEqFrameR` from `natFragOk` is one
structural induction over that grammar**, not a case analysis: the
leaf-shape conjunct is the `fvar` clause verbatim, `LeavesBounded` is
free (annotations are `.const natName []`), and the denotation is the
`const` clause's arity match.

**The obstacle is layering, and it is the relocation rule's exact
case.**  `Setlec/SetR/*` must not import `Setlec/TTVerify/*` — the two
routes are independent by design.  But the block is *V-free*:
`natFragOk`, `shallowE_of_natFragOk`, `storedNoLevels`,
`natFragOk_const`, `natFragOk_self`, `natOpEquations_frag`, the
`storedNoLevels_*` helpers, `ne_of_mem_natOpNames`, and the four
`natOpGuard_*` lemmas mention nothing lane-specific.  Only
`natFrag_subst_facts` (`:73`) takes an `EnvTT`, and it stays.

So the route is: **relocate the V-free block to `Setlec/Verify/`**
(the TT lane imports `Verify`, so it keeps everything by re-export),
then one induction.  That is the relocation thesis at its stated
threshold — a second consumer, and a statement with nothing
lane-specific in it — and it is the cheapest correct move rather than
duplicating a grammar into the SetR tier.

Recorded rather than started: a file split with a cross-lane consumer
is not something to leave half-done at a session boundary.

### Obligation 1 CLOSED — `certifyNatEqs` needs no hypothesis

The relocation predicted the shape and the shape held.

`Setlec/Verify/NatOpFrag.lean` now carries the V-free fragment
characterisation (`natFragOk` and its fourteen companions); only
`natFrag_subst_facts`, stated over an `EnvTT`, stayed behind.  The
namespace is kept as `Setlec.TTVerify`, following the convention the
TT lane already grew into for shared files
(`Verify/Denote/SubstConst.lean` is `Setlec/Verify/*` in
`Setlec.TTVerify` too), so **nothing downstream re-qualified** — the
TT lane's certified theorems are byte-identical in their axiom
dependencies and the tt-model sweep is unchanged.

On top of it, three lemmas and one deletion:

* `natEqFrame_of_frag` — `NatEqFrameR` from `natFragOk`, **one
  structural induction over four constructors**, exactly as predicted;
  no case analysis over `natOpNames` anywhere;
* `natEqsBridge_of` — the semantic half (landed last stretch);
* `natEqsR_of_certs` — the two joined, with the descent from the
  post-insertion guard to the pre-insertion environment via
  `storedNoLevels_of_cons` at the names `ne_of_mem_natOpNames`
  separates from the operation.  That descent block is `natOpPinTT`'s,
  line for line — the clearest possible evidence that the relocation
  put the characterisation at the right height;
* **`declDefnR`'s `hnat` is deleted.**  It is no longer a hypothesis
  of anything: `declDefnR` discharges it internally, and
  `NatEqsBridgeR` is gone from `checkDeclR_sound`,
  `checkDecls_sound_R` and `no_proof_of_Empty_R`.

`no_proof_of_Empty_R` is down from **eleven carried hypotheses to
ten**, and the one removed was the first of the three the retirement
gate names.

*One structural note earned on the way.*  `opener_denotes_at` had to
move earlier in `Bridge/Decl.lean` — the value branches now need it,
and it had been sitting after them.  A seven-line lemma with no
dependencies migrating upward is the cheapest kind of file-order
change and is worth doing eagerly rather than threading a hypothesis
around it.

### Obligations 2 and 3, traced from the sibling lane

Both follow obligation 1's pattern exactly — relocate a V-free
inversion, then discharge — with one wrinkle each, found by reading
the TT lane first (P1a).

**Reduce (obligation 3).**  `checkReducePin_inv`
(`TTVerify/ReducePin.lean:94`) is V-free and relocatable, and
`reducePinTT` (`:140`) is the discharge template — including the
`CtxOk` at the single-element context, which is `CtxOkR.constCtx`'s
shape again.  *The wrinkle:* the TT inversion **drops the pin side**.
It returns `reduceElemOk`, the annotate output and the depth-`1`
identity certificate, but not `pinA` nor `isDefEqCore … 0 valA pinA` —
and `ReducePinR` demands the `DefEq [] V P` against the pin.  So the
relocation must come with an **additive strengthening** of the
inversion (the proof already has both in scope at `hpa`/`hp1`; it
discards them), in the now-familiar shape: append, never reconstruct.

**Div/mod (obligation 2).**  Same route through
`checkDivModPin`, plus the `v`-freeness repair.  The consumer question
the coordinator asked to settle first has a clear answer in the
source: `checkDivModPin ops env env' c` **takes no value** — it reads
`env'.find? c` and binds `value'` there.  So the free `v` must be
replaced by a *bound* one, introduced with its storage hypothesis:

```
∃ value', env'.find? c = some (.defnInfo _ value' _) ∧
  DivModPinR μ F env env' m.cval c value'
```

and `DeclDefnR`'s own conjunct already names the branch's `value'`, so
the consumers agree with that reading — the same "the consumers have
already voted" test that settled the `ErasedEq` granularity.

Both are the same stretch's work: one relocation, one additive
inversion pin, one discharge each.

### Obligation 3 CLOSED — and the pin conjunct was dead weight

`Setlec/Verify/ReducePinInv.lean` takes `reduceElem_shape` and
`checkReducePin_inv` out of the TT lane, with the **additive
strengthening** the trace predicted: the inversion now records both
guards, both annotate outputs and *both* `isDefEq` verdicts.  The TT
lane's own consumer takes a nine-way destructuring with seven
discards and is otherwise untouched; its certified theorems and the
tt-model sweep are unchanged.

`reducePinR_of` then discharges `ReducePinR`, and **`declOpaqueR`'s
`hrp` is deleted**.  Two obligations down; `no_proof_of_Empty_R`
carries **nine**.

**The finding on the way.**  `ReducePinR` demanded a `DefEq` between
the annotated value and the *pin*, and the pin's own denotation has no
supplier.  Before building one, the consumer test: `reducePinS`
destructured that conjunct as `hpinDeq` and **never used it**.  The TT
lane had already written down why —

> *the first `isDefEq` (`valA ≡ pin`) is the elaborator-drift gate — it
> exists so a toolchain change surfaces as a decline rather than
> silently — and the bridge needs nothing from it, which is the
> expected shape: a gate that protects the checker's other guarantees
> leaves the derivation layer alone.*

So the conjunct is gone from `ReducePinR`.  This is the third time the
consumers have decided a spec question (after the `ErasedEq`
granularity and `IndRecsFoldR`'s base environment), and the third time
the answer was already written in the source before anyone asked.
Worth stating as the *positive* form of the searchlight rule:

> **When a spec asks for something with no supplier, read the
> consumers before building one.  A conjunct nobody reads is not a
> gap in the machinery; it is a gap in the spec.**

### SCOPING FINDING — "hypothesis-free" is not T6's to deliver alone

Supplying the three install obligations that were *already proved*
(`declBasisS`, `reducePinS`, `declIndS hkey heta` — carried as
hypotheses by oversight) takes `no_proof_of_Empty_R` from nine to
**six**.  Enumerating what is left makes the gate's real shape visible:

| hypothesis | tier | status |
|---|---|---|
| `hdmR : DivModPinBridgeR` | **T6 (mine)** | open — the last bridge obligation |
| `hkey : MemberKeyS` | T4/T5 install | open, named in this file since T5 |
| `heta : MemberEtaS` | T4/T5 install | open (§"not a member-fold discharge") |
| `hdm : DivModPinS` | T4/T5 install | open (`Install/Value.lean`) |
| `hstd : StdAxiomKeyS` | T4/T5 install | open (`Install/Axiom.lean`) |
| `hofr : OfReduceKeyS` | T4/T5 install | open (`Install/Axiom.lean`) |

**Five of the six are not T6's.**  They are the install tier's own
named obligations, recorded in this file since T5, and they are the
difference between the `SetR` route and the Model route — whose
`no_proof_of_Empty` *is* hypothesis-free because its install tier is
complete.

So the retirement gate as stated ("the `_R` family stands
hypothesis-free") is a **T4/T5 + T6** milestone, not a T6 one.  T6 can
close its own three bridge obligations — two are done — and can
reduce the carried set to exactly the install tier's open list.  It
cannot make that list empty.

This is worth stating plainly rather than discovering at the
checkpoint: **a gate phrased over a theorem's whole hypothesis list
prices in every tier that theorem depends on.**  The gate is right;
its owner is the campaign, not the stretch.

### Div/mod: two repairs land, and the remainder is a genuine rock

Two things were cheap and independently correct, so they landed first:

* **the `v`-freeness repair.**  `hdm` now takes
  `annotateCore μ env F 0 value = .ok v`, which *determines* `v`.
  Left free, the conclusion asserted the pack for an arbitrary value,
  which `checkDivModPin` cannot warrant — it takes no value and reads
  one out of `env'`.  Consumers voted; `DeclDefnR`'s own conjunct
  names the branch's `value'`.
* **the pin conjunct is gone from `DivModPinR`**, for the reason
  `ReducePinR`'s went: it is the elaborator-drift gate,
  **`DivModPinTT` does not record it either**, and the pin's
  denotation has no supplier.

`checkDivModPin_inv` and `checkDivModCerts_inv` are **already in the
shared tier** (`Verify/DivModInv.lean`) — no relocation needed, and
they deliver the guards, the storage that determines `v`, the pin
annotate, and `CertRuns (CertRunFacts …)`.

**But the remainder is a rock, and for a reason the previous two did
not have.**  For `Nat` and `reduce`, the TT lane's reusable content
was *syntactic* (`natFragOk`, `checkReducePin_inv`) and therefore
V-free and relocatable.  Div/mod's is not: `TTVerify/DivModPin.lean`'s
machinery — `Frames4`, `dmCtx4`, `dmCtx4_x/y/h1/h2`, `frag_frames`,
`cert_extractT` — is stated over `EnvTT`, `HasType` and the TT lane's
own frame notion.  Only `certGuard_proof` and `natOpCod_shape` look
relocatable.

So `DivModCertR` needs, written fresh on the `SetR` side:

1. a **heterogeneous** canonical-context lemma — `CtxOkR` at
   `[H2, H1, natVR, natVR]`, where the two hypothesis slots carry
   *different* annotations.  `CtxOkR.constCtx` is the homogeneous
   case and does not reach it;
2. frame packages for the certificate statements and the applied
   proof at depth `4`, across `substConstAll`/`substConst0` — the
   `natFragOk` story again but over a richer fragment (the statements
   are `Eq.{1}` equations with `ble` guards, not a four-constructor
   spine);
3. the `Infer`-side transport, which `NatEqsR` did not need.

**Sized honestly: comparable to `iotaThmR_of`.**  That is T6's last
bridge obligation and its largest, and it is the one place where the
sibling lane's work does *not* transpose — recorded because the
inventory rule has been right so often that its exception deserves
naming.

### The two traces the campaign asked for

**(A) The driver folds need a relocation that is not free.**
`checkDeclsC_sound` runs `foldlM_soundC`, whose whole content is
`checkDecl_bridge` (`Model/BridgeWF.lean:903`): from a `cachedOps`
run, produce a fuel `F` with the same `fueledOps` verdict.  The `SetR`
fold is then `foldlM_R` with that step inserted, and the obligations
re-quantified over `F` (they are `F`-indexed).  `_S` and `_SP` are the
same with their own driver bridges.

`Model/BridgeWF.lean` is **entirely V-free** (zero `SetTheory`), as is
`Model/DirectWF.lean` — but `DirectWF` imports `Model.Extend`, whose
umbrella pulls in the set model's V-dependent extension lemmas.  So
the relocation is real but **not** a copy: it needs `DirectWF`'s
dependence on `Model.Extend` narrowed to the syntactic lemmas it
actually uses.  `Setlec/SetR/*` imports no `Setlec/Model/*` today and
that discipline is the reason this is not simply an added import.

**(B) The five install obligations: table, as requested.**

| obligation | Model sibling | proved? | transposes? |
|---|---|---|---|
| `StdAxiomKeyS` | `propext_key`, `choice_key` (`Model/StdAxioms.lean:476,799`) | yes | **no** |
| `OfReduceKeyS` | `ofReduce_key`, `trustCompiler_key` (`Model/TrustAxioms.lean:426,65`) | yes | **no** |
| `DivModPinS` | `divModCert_extract` (`Model/DivModCert.lean:163`) + `Consistency`'s block | yes | **no** |
| `MemberKeyS` | the member install's model key (`Model/IndInstall.lean`) | yes | **no** |
| `MemberEtaS` | the eta-law key | yes | **no** |

**Every one has a proved Model sibling, and not one of them
relocates.**  The reason is uniform: they are stated over `EnvModel`
and conclude with `HasType`/`has_type`, while the `SetR` versions must
conclude with `EnvS.mem_type` — membership *plus* the denoted type's
truthfulness (`AnnotOkV`).  That is P3's territory, and P3 says
truthfulness does not transport along an interpretation equality.

So the five are five re-proofs at the `EnvS` layer, each with a proved
template and none with a shortcut.  This is the first time in the
campaign that the inventory rule comes back **empty five times in a
row** — which is itself the finding: *the install tier's debt is
genuine work, not unlocated work.*

### DECISION REQUEST — `DivModCertR` was frozen without a consumer

`CtxOkR.pinnedCtx` lands (the rock's first piece, and the one with
reuse).  Before building the other two, the evidence says the rock may
not need to exist.

**Three facts.**

1. **`DivModCertR` has exactly one occurrence in the tree** — its own
   use inside `DivModPinR` (`SetR/Decl.lean:225`).  Nothing consumes
   it.  Its consumer would be `DivModPinS`, which is an *open* install
   obligation, so the detailed `Infer`-side content at depth `4` was
   frozen **before any consumer exercised it**.  That is precisely
   what D6's house rule forbids, and the rule is written in this file:
   *the house rule forbids freezing a statement no consumer has
   exercised.*
2. **The TT lane did not transpose the certificates at all.**
   `DivModPinTT` (`TTVerify/DeclDefn.lean:64`) takes
   `checkDivModPin … = .ok ()` **as a hypothesis** and does the
   certificate work *inside* `divModPinTT`.  The lane that has
   actually finished this branch chose the other factoring.
3. **The rock's size is the certificates.**  `checkDivModPin_inv` and
   `checkDivModCerts_inv` are already shared-tier and already deliver
   the guards, the storage, the pin annotate and `CertRuns`.  What is
   expensive is turning `CertRuns` into `Forall2 DivModCertR`: a
   depth-`4` frame package over a fragment richer than `natFragOk`'s,
   plus the `Infer`-side transport — `TTVerify/DivModPin.lean` spends
   ~1400 lines on the equivalent.

**The proposal.**  Replace `DivModPinR`'s
`Forall2 DivModCertR …` conjunct by the checker's own verdict,
`checkDivModCerts (fueledOps μ F) env c value' (divModCertStmts c)
(divModCertProofs c) = .ok true`, exactly as `DivModPinTT` keeps it.
Then `DivModPinBridgeR` is discharged by `checkDivModPin_inv` alone —
**T6's ledger closes today** — and the certificate work moves to
`DivModPinS`, the install obligation that must do it anyway and where
the TT lane put it.

**What this does and does not cost.**  It does *not* eliminate work:
`DivModPinS` gets less and must do more, and it is already on the
campaign's list of five.  It does *not* weaken any final theorem: the
verdict carries the same information the transposition would have, and
`DivModPinS`'s statement is unchanged.  What it changes is **where**
the depth-`4` machinery lives — beside the `EnvS` reasoning that
consumes it, rather than in a relation that nothing reads.

**Why I am asking rather than doing.**  Every earlier consumer-vote
had an actual consumer to read.  This one has none, so the argument is
from precedent and a house rule rather than from a use site — and it
edits a relation the fourteen rest on.  That is the stop bar's
"proof-design question the records do not answer", one level up: the
records answer it *by analogy*, which is not the same thing.

### T6's LEDGER IS CLOSED — the grant, executed

`DivModPinR`'s certificate conjunct is now the checker's own verdict
(`checkDivModCerts … = .ok true`), `DivModCertR` is deleted, and
`divModPinR_of` discharges the whole pack from `checkDivModPin_inv`
alone — twelve lines.  `declDefnR`'s `hdm` is deleted.

**`no_proof_of_Empty_R` now carries exactly five hypotheses, and all
five are the install tier's**: `MemberKeyS`, `MemberEtaS`,
`DivModPinS`, `StdAxiomKeyS`, `OfReduceKeyS`.  **Zero bridge
obligations remain.**  T6 owed three; three are closed.

**Guard (a) — the decision is reversible, and here is its reopen
condition.**  Recorded at the definition site as well as here.  The
certificate content enters as a verdict *because no consumer had
shaped it*.  If `DivModPinS`'s discharge shows the content wants
first-class relational form, **reintroduce it then, shaped by that
consumer** — not before.  `CtxOkR.pinnedCtx` stays landed precisely
for that eventuality: it is the reusable geometric piece
(`[H2, H1, natVR, natVR]` with per-slot annotations), it has no
dependence on the decision either way, and `DivModPinS` will want it.

**Guard (b) — confirmed, and worth stating exactly.**  The edit
touches `Setlec/SetR/Decl.lean` (the `DeclR` tier) and its three
consumers.  `Setlec/SetR/Rel.lean` contains **zero** occurrences of
`DivModPinR`, `DivModCertR` or `checkDivModCerts`, before or after.
The `[set]` relation family's premise-exactness claim is about
`Rel.lean`'s forty-two constructors and is untouched: **the core
relation family has not acquired a checker-verdict premise.**  What
acquired one is the per-declaration `Prop` that *describes a
`checkDecl` run* — a tier whose whole job is to mention the checker,
and which mentions `annotateCore`, `isDefEqCore` and `inferTypeCore`
throughout already.

*The general lesson, since the grant turned on it.*  The house rule
("do not freeze a statement no consumer has exercised") was written as
a caution about **detail**; this is the first time it caught a
statement whose detail was right and whose *existence* was wrong.  The
sharper form: **an unexercised statement's first error is usually not
its content but its right to exist.**

### The narrowing was a collapse, and the `_C` driver followed

The trace said "narrow `DirectWF`'s import to the syntactic lemmas it
uses".  Reading the use site, there was nothing to narrow — there was
a branch to delete.  `Model/BridgeWF.lean` touched `DirectWF` at
**exactly one place**, the `some p` arm of
`cases hdp : directParts? env block`, and `directParts?_none` makes
that arm unreachable.  Two lines replace nineteen, the
`Setlec.Model.DirectWF` import goes, and the file — already entirely
V-free — becomes shared-tier material.

So `Model/BridgeWF.lean` is now **`Setlec/Verify/BridgeWFDecl.lean`**
(`git mv`, one importer to repoint plus the root).  `directParts?_none`
moved with it into `Verify/BridgeDecl.lean`, where every consumer's
dependence on the compile-time switch is findable from one place.

*The general shape, worth a line beside the relocation thesis:*
**before narrowing a dependence, check whether the branch that
creates it can fire.**  A dead branch is not a dependence to be
minimised; it is a dependence to be deleted, and the two look
identical from the import list.

With `checkDecl_bridge` reachable, the cached-driver fold is the
transposition it was advertised as:

* `foldlM_RC` — per declaration, `checkDecl_bridge m.wf` supplies a
  fuel at which the pure checker reproduces the cached run; the rest
  is `foldlM_R`'s step verbatim.  Compiled first attempt;
* `checkDeclsC_sound_R`, `no_proof_of_Empty_C_R` — two of the
  fourteen, both at `[propext, Classical.choice, Quot.sound]`, both
  carrying exactly the install tier's five.

Five of the fourteen now stand.  The `_S` and `_SP` drivers are the
same shape with their own bridges (`checkDeclSharedF`, the
parsed-index step over the store); the `_input` corollaries follow the
Model lane's `foldlM_no_Empty_decl` pattern.

### All three drivers land; nine of the fourteen stand

The dead-branch rule paid twice more.  `Model/BridgeS.lean` (498
lines, V-free) touched `DirectWF` only through
`checkDirectStructS_run` and its projection helper — **179 lines whose
only caller was the unreachable arm**.  Deleted, not narrowed; the
file is now `Setlec/Verify/BridgeSDecl.lean`.  `checkDeclSPStep_run`
and `checkDeclSPStep_inRange` came out of `Model/ConsistencyP.lean`
into `Setlec/Verify/BridgePDecl.lean` the same way.

Three folds, all first attempt:

* `foldlM_RC` / `checkDeclsC_sound_R` / `no_proof_of_Empty_C_R`;
* `foldlM_RS` / `checkDeclsS_sound_R` / `no_proof_of_Empty_S_R`;
* `foldSP_R` / `checkDeclsSP_sound_R` / `no_proof_of_Empty_SP_R`.

**The store invariant's supplier, named** (the same discipline as the
environments'): `WFStore.wf` gives `st.raw.WF` **once, at the bundle**,
and the fold threads `ISOKF`/`Ext` out of `checkDeclSPStep_run` — the
residue is environment-free, so nothing about it depends on the model
at all.  `Ext.refl` seeds it and `Ext.trans` carries it; there is no
step at which the store invariant is re-derived, which is why the
parsed-index fold is the same length as the other two.

**Nine of the fourteen now stand**, every one at
`[propext, Classical.choice, Quot.sound]` and every one carrying
exactly the install tier's five.  The Model lane's `_C`, `_S` and
`_SP` theorems re-verified unchanged through all three relocations.

Remaining: the five `*_input` corollaries (the
`foldlM_no_Empty_decl` pattern), then the install tier's five.

### ALL FOURTEEN STAND — the breadth dimension is done

`checkDecl_stores` came out of `Model/Consistency.lean` into
`Setlec/Verify/DeclStores.lean` (purely syntactic; both routes' input
corollaries turn on it), and with it the last five landed:
`checkDecl_sound_R` and the four `*_input_*` corollaries, on the
Model lane's `foldlM_no_Empty_decl` pattern.

**The fourteen, all at `[propext, Classical.choice, Quot.sound]`:**

| | pure | cached | shared | parsed |
|---|---|---|---|---|
| acceptance | `checkDecls_sound_R` | `checkDeclsC_sound_R` | `checkDeclsS_sound_R` | `checkDeclsSP_sound_R` |
| no stored `Empty` | `no_proof_of_Empty_R` | `no_proof_of_Empty_C_R` | `no_proof_of_Empty_S_R` | `no_proof_of_Empty_SP_R` |
| no declared `Empty` | `no_proof_of_Empty_input_R` | `..._input_C_R` | `..._input_S_R` | `..._input_SP_R` |

plus `checkDecl_sound_R` (one declaration extends the invariant) and
`no_constant_of_Empty_R` (the model-level core).

*A relocation note worth keeping.*  Moving proof text between files
changes which `simp` arguments fire: `checkDecl_stores` arrived with
**nine** newly-unused `simp` arguments, and trimming them one at a
time turned up two places where a *different* argument then became
necessary (`checkThmVal` in the second branch, `fueledOps_ensureSort`
after it).  The rule: **after relocating a proof, the warning list is
not a tidy-up — it is a re-derivation of which lemmas the goal
actually needs, and the trims must be applied one at a time.**

All fourteen carry exactly the install tier's five, which is now the
whole remaining distance.

### CALIBRATION — measured, and the answer changed on measuring

The task was "land the genuinely smaller of `StdAxiomKeyS` /
`OfReduceKeyS`".  Measuring first (per the trace-before-write
discipline) turned up the cost driver, and it is not template size.

**Template sizes, measured.**

| obligation | Model template(s) | lines |
|---|---|---|
| `OfReduceKeyS` | `ofReduce_key` (`TrustAxioms.lean:426`) | ~120 |
| `StdAxiomKeyS` | `propext_key` (`StdAxioms.lean:476`) + `choice_key` (`:799`) | ~320 + ~42 |

So `OfReduceKeyS` is the smaller, by three-fold, and by measurement
rather than guess.

**But the templates are not the cost.**  Every Model key concludes
with a *value* — `SetTheory.pt ∈ˢ T`.  Every `SetR` key must produce
a **`VExpr` witness** `Vf` together with `AnnotOkV V ρ (Vf ψ)`, and
`AnnotOkV` is a **structural recursion on `VExpr`** (`SetR/AnnotOkV.lean:47`).
There is **no `pt`-valued `VExpr` in the tree**.  So the witness has
to be built and its truthfulness proved structurally — with no Model
analogue to transpose, because the Model lane never needed a syntactic
witness at all.

That is P3, located exactly: *truthfulness does not transport along an
interpretation equality*, and the place it bites is the **witness**,
not the membership.

**Where the template *does* transpose — and it is the pair.**  The
in-lane precedent is `trustCompilerKeyS` (`Install/Axiom.lean:191`,
already discharged, ~80 lines): its witness is
`m.cval trueIntroName ψ` — a **stored constant's valuation** — and
every conjunct then comes from `EnvS`'s own fields (`cval_closed`,
`val_params`, `annot_okV`, `cval_memType`).  No construction at all.

And `MemberKeyS`'s witness is
`m.cval (cvA.name.str "_model") ψ` — **also a stored constant's
valuation**, handed to it by the statement.  So the member key is the
`trustCompilerKeyS` shape, not the axiom-key shape: what it needs is
`cval_memType` at the model constant plus the type identification the
preprocessor's syntactic contract already supplies.

**The sized read, which is what the calibration was for:**

| obligation | shape | size |
|---|---|---|
| `MemberKeyS` | witness given (stored `_model` valuation) — `trustCompilerKeyS`'s shape | **smallest**; transcription-leaning |
| `OfReduceKeyS` | witness must be **constructed**, `AnnotOkV` proved structurally | medium; the construction is new work |
| `MemberEtaS` | concludes `EtaLawV`, a capability law, not a membership — different shape from all four others | unmeasured; sized by `EtaLawV`'s demands |
| `StdAxiomKeyS` | the `OfReduceKeyS` delta, twice, over a 3× template | large |
| `DivModPinS` | now also owns the depth-4 certificate machinery (the granted move); the TT lane spends ~1400 lines on the equivalent | **largest** |

**The recommendation, against the standing order:** start with
`MemberKeyS`, not an axiom key.  The order "smallest first to
calibrate" was chosen when the five looked uniform; measurement says
they are not, and the one whose witness is *given* is both the
smallest and the one whose success calibrates the pair — which is
precisely the read the calibration was commissioned to produce.
`MemberEtaS` remains unmeasured and is the one genuine unknown left.

### `MemberKeyS` CLOSED — the calibration's prediction held exactly

The witness was given and the conjuncts came from `EnvS`'s own fields,
as `trustCompilerKeyS` predicted.  `memberKeyS` is **thirty lines**:
`EnvS.cval_memType` at the stored `_model` constant supplies the
membership *and* the truthfulness outright, and all that remains is
that the two types denote the same — the block renaming carries
`cvA.type` to `cvm.type` up to `eqUpToNames`, and `denote` is blind to
exactly that difference (`denote_erasedEq`).

**One new shared lemma, and its reason is worth the line.**
`denote_renameConsts` needs the full `RenameOkT`, whose second clause
(*unstored maps to unstored*) fails at a **member** environment: the
block's later members are not stored yet, so a block name can be
unstored while its `_model` is stored.  But that clause exists only to
stop an unstored constant acquiring a denotation, and an expression
every constant of which *resolves* never reaches it.  Hence
`denote_renameConsts_resolve` (`Verify/Denote/Rename.lean`), premised
on the two clauses `BlockInstalledTT` actually supplies plus
`constsResolve`.

> **A premise that fails at your environment may be doing work your
> expression never needs.**  Before strengthening the environment,
> check whether the clause is reachable from the subject.

`no_proof_of_Empty_R` and its thirteen siblings now carry **four**:
`MemberEtaS`, `DivModPinS`, `StdAxiomKeyS`, `OfReduceKeyS`.

### `MemberEtaS` measured — not a rock, and not transcription

Its Model siblings are `modeled_caps_eta`
(`Model/ModeledCaps.lean:140`, ~160 lines) and `blockMember_headEta`
(`:446`, ~100) — call it **~260 lines of template**.

**P3 does *not* bite here.**  `EtaLawV` concludes an `interp`
*equality*; there is no membership-plus-truthfulness, no `AnnotOkV`,
and therefore no witness to construct.  That makes it structurally
unlike the two axiom keys.

**What differs is the quantification, not the semantics.**  The Model's
`EtaLaw` quantifies over **values** (`ps : List V`, `x : V`) and uses
`SpineFold`/`TeleFit`; `EtaLawV` quantifies over **`VExpr`s**
(`xs`, `B`) and uses `mkAppN`/`interp`/`TeleFitV`/`etaFabArgsV`.  So
the derivation transposes in shape and needs a value↔`VExpr`
adaptation layer — the `interp (mkAppN …) = SpineFold …` direction —
much of which the `SetR` `Sound` tier already carries
(`etaFabArgsV` is its own).

**Sized read: between `MemberKeyS` and `OfReduceKeyS`.**  Bigger than
transcription because of the adaptation layer; smaller than the axiom
keys because nothing has to be *built*.  **Not a rock** — reporting
that, since the instruction was to stop if it looked like one.

Revised order for the remaining four: `MemberEtaS` (medium,
templated), then `OfReduceKeyS` (first witness construction — it will
set the pattern for `StdAxiomKeyS`'s two), then `StdAxiomKeyS`, then
`DivModPinS` last with `pinnedCtx` waiting for it.

### `MemberEtaS` BREAKS PATTERN — it is plumbing, not proof

The sizing (~260 lines of template, value↔`VExpr` adaptation) was a
measurement of the wrong thing.  Two facts found on starting it:

**1. The heavy lifting is already done, in this lane.**
`etaLawKeyS` (`Install/EtaLawS.lean:108`) is **proved** — the whole
`EtaLawV` derivation, model artifacts through shape pins to the fired
law.  Nothing of `modeled_caps_eta` needs transposing; the SetR lane
did it during T5.  My estimate priced the Model template because I
checked the Model lane first, which was the wrong lane to check for an
obligation whose *own* lane had already built the machinery.

**2. `MemberEtaS` is not dischargeable at its current signature — and
this file already said so.**  §"`MemberEtaS`: not a member-fold
discharge" works the four cases and concludes:

> Both live rows need facts the fold does not have (the run's
> freshness facts; the block's identification of `T`).  So
> `MemberEtaS` stays a *forwarded* obligation, discharged at the
> `DeclIndS` assembly … It is re-signed then, with its consumer, per
> the house rule.

That is exactly where the campaign now stands.  `etaLawKeyS`'s premise
list wants the model artifacts, the shape pins, the valuation
identifications and a renaming — none of which `MemberEtaS`'s current
signature carries, and none of which the member fold has.  The
assembly does: `hprojFresh` is in scope at **both** assembly sites
(`Install/DeclIndS.lean:115`, `Bridge/DeclInd.lean:494`), which is the
fact the `etaFields > 0` row was refuted from.

**Why this is a stop.**  The other four remaining obligations are
*proofs at a fixed signature*.  This one is a **signature change with
a ripple**: `MemberEtaS`/`heta` occurs ~82 times across seven files —
`Main.lean` (48, the fourteen), `Bridge/DeclInd.lean` (13),
`Install/IndMembersS.lean` (8), `Install/DeclIndS.lean` (5),
`Bridge/Sound.lean` (5), `Install/IndRecsS.lean` (2),
`Bridge/EtaCerts.lean` (1).  Re-signing it means adding the assembly
premises, threading them from the two assemblies down through both
member folds, and discharging there — after which `heta` leaves the
fourteen entirely.

**The lesson, and it is the sizing rule's own blind spot:**

> **Size an obligation against the lane that will discharge it, not
> the lane that already discharged its sibling.**  A template in the
> other lane measures the *mathematics*; it says nothing about whether
> your own lane already has it, or whether your statement can even
> receive it.

Both errors this stretch were that: the mathematics was done and the
statement could not receive it.

### `OfReduceKeyS`: the sibling-lane file I did not know existed

Applying the new sizing rule ("check the lane that will discharge it")
sent me to `SetR` first, correctly — and finding nothing there, to the
*siblings*, where **`Setlec/TTVerify/OfReduceKey.lean`** turned out to
be a dedicated 355-line file for exactly this obligation.  My earlier
calibration priced `Model/TrustAxioms.lean`'s `ofReduce_key` (~120
lines) and never looked at the TT lane at all.

**Landed this stretch: the V-free half, relocated.**
`Setlec/Verify/OfReducePin.lean` now carries `ofReduce_elemTy`,
`ofReducePin_type`, `reduceOpCv_type`, `reduceElem_sort`,
`matchesPin_invT` and `eraseNames_sort_inv` — every shape fact about
the two pinned axioms, all V-free (both differ only in their element
type, so each is one `split`).  TT lane re-verified:
`no_proof_of_Empty_TT_closed` and `ofReduceKeyTT` at the standard
three, tt-model sweep identical.

**The remaining construction, mapped.**  `denote_ofReducePin`
(`TTVerify/OfReduceKey.lean:130`) computes the pinned type's
denotation to
`.pi E (.pi E (.pi (Eq E (op a) b) (Eq E a b)))` — the shape the
witness is checked against — and uses its `EnvTT` only through
`denote_const_nolevels`, so it restates over `EnvS` directly.  Then:

* the witness is `λ a b h. h`, i.e. `.lam A₁ (.lam A₂ (.lam A₃
  (.bvar 0)))` built from the *denoted type's own components*;
* `AnnotOkV` of it follows from `AnnotOkV` of the type — the same
  subterms — through `AnnotOkV_lam`/`AnnotOkV_pi`;
* the membership is `lamC_mem` three times, and the innermost step is
  the whole mathematical content: `interp A₃ = interp A₄`, because
  `EqLawV.app₃` reduces both to `eqv`, and `EnvS.reduce_ops` gives
  `app (cval op) x = x` for `x` in the element type.

So the SetR delta over `ofReduceKeyTT` is exactly `HasType` →
membership + `AnnotOkV`, and the `AnnotOkV` half is *free* once the
type's is proved — which the conclusion demands anyway.

**Sizing correction, third time on this obligation.**  ~120 lines
(Model) → ~180 (TT witness) → and now: the TT witness *minus* its
`HasType` bookkeeping *plus* `AnnotOkV`, over a relocated shape layer
that is already done.  The lesson stands and sharpens: **check every
lane before pricing, and price the delta, not the template.**

### `OfReduceKeyS`, half built — and the witness/type identity, exact

`denote_ofReducePinS` (`Install/Axiom.lean`) restates the TT lane's
type computation over `EnvS`, first attempt: the original used its
`EnvTT` only through `denote_const_nolevels`, and
`denote_const_nolevelsS` is the in-lane twin.  With `eqVS` beside it,
the pinned type is now known to denote to

```
.pi E (.pi E (.pi (Eq E (op a) b) (Eq E a b)))
```

**The structural finding, and it is sharper than "the `AnnotOkV` half
is free".**  `AnnotOkV`'s `.lam` and `.pi` clauses are *literally the
same shape* (`AnnotOkV_lam` / `AnnotOkV_pi`, `SetR/AnnotOkV.lean:80`).
So with the witness built as
`.lam E (.lam E (.lam H₁ (.bvar 0)))` from the type's own components,

> `AnnotOkV ρ (Vf ψ)` **is** `AnnotOkV ρ t`'s first three components,
> with `trivial` for the fourth (`AnnotOkV` of a `.bvar` is `True`).

Not "follows from" — *is*.  That is the pattern `StdAxiomKeyS` should
reuse: **build the witness out of the type's own subterms and its
truthfulness is the type's, component for component.**

**What remains, precisely.**  `AnnotOkV ρ t` itself is *not* available
from the invariant — `cvA` is fresh, so `cval_memType` does not apply
to it — and must be proved from the pinned type's shape.  Its only
non-trivial part is the `Eq`-spine's three `AnnotOkV_app` obligations
(`interp f ∈ˢ piC A B`, `interp a ∈ˢ A`), which peel from
`m.cval_memType` at `eqName` (stored, `hEq`) through `app_mem_piC`.
The membership `interp (Vf ψ) ∈ˢ interp ρ t` is then `lamC_mem` three
times, and the innermost step is the whole mathematical content:
`interp H₁ = interp H₂` because `EqLawV.app₃` reduces both to `eqv`
and `EnvS.reduce_ops` gives `app (cval op) a = a` for `a ∈ˢ E`.

Estimated remainder: the `Eq`-spine peeling (~80 lines) and the
three-fold `lamC_mem` (~40).

### The last gap in `OfReduceKeyS`: the spine helpers point the wrong way

`SetR/Sound/Iota.lean` already has `AnnotOkV_mkAppN_parts` /
`AnnotOkV_mkAppN_args` — but both are **destructors** (truthfulness of
a spine yields truthfulness of its parts).  Building `AnnotOkV` of the
`Eq` spine needs the **constructor** direction, which is where the
`piC` memberships enter and which nothing supplies yet.

So the one lemma still to write is

```
AnnotOkV_mkAppN_of :
  AnnotOkV ρ f → (∀ a ∈ as, AnnotOkV ρ a) →
  <the chain of piC memberships along the spine> →
  AnnotOkV ρ (VExpr.mkAppN f as)
```

— three `AnnotOkV_app` steps for the three-argument `Eq` spine, with
the memberships peeled from `m.cval_memType` at `eqName` through
`app_mem_piC`.  The level bookkeeping checks out:
`interp_sort ρ u = univ u`, `reduceElem_sort` puts the element type at
`.sort 1`, and `eqVS` instantiates `Eq` at `.succ .zero`, so
`EqLawV.app₃`'s `interp A ∈ˢ univ (ψ uN)` is `univ 1` on both sides.

*A note on the inventory rule's failure mode here.*  Finding
`AnnotOkV_mkAppN_parts` by name looked like a hit and was a miss: the
name says what it is *about*, not which way it runs.  **Search the
conclusion, not the subject** — a helper about the right object can
still face the wrong direction, and for `AnnotOkV` (destructors are
cheap, constructors carry the side conditions) that asymmetry is
systematic.

### `OfReduceKeyS`'s preamble, verified — and the two bridges it needed

`denote_eqA_typeS` is landed (`Install/Axiom.lean`): the pinned `Eq`
former's type denotes to
`.pi (.sort 1) (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))` at any
assignment sending `u` to `1`.

Two bridging facts were needed and neither was obvious:

* **`denote` will not fire through a projection.**
  `simp [denote_forallE, …]` made *no progress* on
  `eqA.toConstantVal.type` — the projection blocks the equation
  lemmas.  `have hty : eqA.toConstantVal.type = <literal> := rfl;
  rw [hty]` first, and the same `simp` closes it.  Worth naming
  because the failure looks like a missing lemma and is a blocked
  head.
* **`matchesPin` gives `eraseNames` equality, not type equality.**  So
  the pin does *not* hand over `cvA.type = pin.type`; it hands over
  `Expr.ErasedEq`, through `erasedEq_of_eraseNames`
  (`Verify/Denote/Inst.lean:335`, shared tier), and `denote_erasedEq`
  moves the denotation.  Same shape as the nested major's `hmaj`.

**The preamble compiles**, establishing: the element type's storage
and `Sort 1` pin, the operation's storage and empty level parameters,
`ofReduceOp cvA.name ∈ reduceOpNames`, `cvA.levelParams = []`, and

```
∀ ψ, denoteClosed m.cval env ψ cvA.type
  = some (.pi E (.pi E (.pi (mkAppN eqV [E, app op (.bvar 1), .bvar 0])
                           (mkAppN eqV [E, .bvar 2, .bvar 1]))))
```

**What remains are the four conclusion obligations**, all against that
one computed type:

1. `VExpr.Closed (Vf ψ)` — structural;
2. level-invariance — `m.val_params` at `E`, `op` (both level-free)
   and at `eqName` (whose one parameter the substituted assignment
   pins to `1` regardless of `ψ`);
3. `AnnotOkV ρ (Vf ψ)` — **the identity**: the first three components
   of `AnnotOkV ρ t`, `trivial` for the `.bvar` tail;
4. `AnnotOkV ρ t` and `interp (Vf ψ) ∈ˢ interp ρ t` — the `Eq`-spine
   peeling (`AnnotOkV_mkAppN_of`, constructor direction) and threefold
   `lamC_mem`, whose innermost step is `EqLawV.app₃` +
   `EnvS.reduce_ops`.

### `OfReduceKeyS` closed

All four obligations landed; the theorem stands at exactly
`[propext, Classical.choice, Quot.sound]`, ~230 lines in
`Install/Axiom.lean` (preamble + six shared `have`s + four
obligations).  Battery green (`lake build` warning-free, `lake test`,
arena 90/92, e2e 72/72, split 11/11, mode flags 10/10, both sweeps).

**The shape that carried it.** Six `have`s, stated *before* the
`refine`, do all the semantic work and are then consumed by both the
witness' truthfulness (obligation 3) and the type's (obligation 4):

* `hEc` — the element type is closed, so its interpretation is
  environment-independent (`interp_closed`); every de Bruijn shift in
  the proof is discharged by this one lemma;
* `hEmem` — `interp ρ E ∈ˢ univ 1`, off `cval_memType` at the `Sort 1`
  pin;
* `hQmem` — the pinned `Eq` former inhabits
  `piC (univ 1) (fun A => piC A fun _ => piC A fun _ => univ 0)`, off
  `cval_memType` + `denote_eqA_typeS`;
* `hOpi` — the trusted operation inhabits `E → E`, off `cval_memType`
  + `denote_erasedEq htyR` + `reduceOpCv_type`;
* `hOpApp` — one application is truthful *and* is the identity
  (`reduce_ops`), returned as a **pair**: the caller needs both, and
  splitting them duplicated the membership side condition;
* `hEqApp` — an `Eq`-spine over `E` is truthful, three `AnnotOkV_app`
  steps chained by `app_mem_piC` on `hQmem`.

**`hframe`/`hframe2`: state the frame at its own de Bruijn depth.**
The hypothesis' statement reads `ρ 1`/`ρ 0`; the conclusion's reads
`ρ 2`/`ρ 1`.  Stating each as *`∀ ρ`, given `ρ 1 ∈ˢ ⟦E⟧` and
`ρ 0 ∈ˢ ⟦E⟧`, the spine is truthful and interprets to `eqv (ρ 1)
(ρ 0)`* — rather than parameterising over the two members `x y` — is
what makes the `cons`-towers discharge by `show x ∈ˢ _` + a single
`hEc` rewrite instead of by transport.  **Rule: when a statement is
about a term with free de Bruijn indices, quantify the environment,
not the values it happens to hold.**

Then the whole of obligation 4's membership is: three `interp_lam,
interp_pi` rewrites, three `lamC_mem`s, and

```
rw [(hframe2 ψ _ hx3 hy3).2]; rw [(hframe ψ _ hx2 hy2).2] at hh
```

— the two frames interpret to the *same* truth set `eqv x y`, because
`reduce_ops` makes `op x` the identity, so `fun a b h => h` is a
member on the nose.

**Two mechanical traps, both new:**

* **A `def`'s dot notation resolves against the wrong explicit
  argument.**  `m.eq_lawV.app₃` elaborated `eq_lawV` into `EqLawV.app₃`'s
  *first explicit* argument, which is `V` (the section variable is
  `(V : Type w)`, not implicit).  Write `EqLawV.app₃ V m.eq_lawV …`.
  Generic: for a lemma in the namespace of a `Prop`-valued `def` whose
  section makes the carrier explicit, dot notation is unusable.
* **`rw [h]` inside a `by` block that fills a not-yet-unified
  argument.**  `(by rw [heqψ]; …)` for `app₃`'s `hA` failed with
  "did not find … in the target expression `VExpr`" — the `A` argument
  was still a metavariable, so the goal was not yet a membership.
  Supplying `A`, `a`, `b` and `ψ` explicitly fixed it.  The error text
  names the *metavariable's type*, which is the tell.
* Doc comments go **after** `set_option … in`, not before.

**`heqψ` must be spelled with `uN`**, not with
`Name.anonymous.str "u"`: `EqLawV`'s statement says `ψ uN`, and `rw`
needs the syntactic form even though the two are definitionally equal.
(`denote_eqA_typeS`'s hypothesis is in `exact` position, so it takes
either.)

### `StdAxiomKeyS`: calibration (measured, not landed)

**The identity pattern does not apply, and that is good news.**
`propext` and `Classical.choice` are not rearrangements of their own
types — but they do not need the TT lane's syntactic `Iff.rec`/
`Nonempty.rec` elimination either.  Both are **layer constants**:
`BConst.propext` and `BConst.choice` exist, with
`bval .propext = pt` and `bval .choice us = choiceV V (lv us 0)`
(`TT/Semantics/Value.lean:302`), and `TT/Semantics/ConstOk.lean`
already proves each inhabits *the layer's* type
(`bval_mem_propext`, `bval_mem_choice` — the latter in four lines).

So the set-lane witnesses are

```
propext : fun _ => VExpr.const .propext []
choice  : fun ψ => VExpr.const .choice [ψ uN]
```

and obligations 1–3 are **one-liners**: `Closed` is `trivial`,
`AnnotOkV ρ (.const _ _)` is `trivial`, and level-invariance is `rfl`
(propext) or one `uN` lookup off the pin (choice).  A probe
(scratch) confirms this compiles, with `denote_propext_typeS`
transposed to a bare `cval` unchanged.

**Why the TT lane needed an elimination and this lane does not.**
`HasType` cannot see `bval`: the layer's `propext` is typed
`∀ A B : Prop, (A→B) → (B→A) → A = B`, and no typing derivation turns
an inhabitant of the opaque `Iff a b` into the two implications — only
`Iff.rec` does.  Membership is *semantic*: the checker's hypothesis
domain `⟦Iff a b⟧` need only be shown to **force** `a = b`, which is a
`prop_ext` argument about truth values.  **This is the third time the
rule "size an obligation against the lane that will discharge it" has
paid: TTVerify was the wrong template; `Model/StdAxioms.lean` is the
right one.**

**What actually remains**, and it is the largest of the five:

| piece | source | ≈ lines |
|---|---|---|
| `iff_shapes`, `nonempty_shapes` (pure `stdAxiomOk` inversion, **no `m`**) | relocate `TTVerify/StdAxiomKey.lean` → `Verify/` | 110 |
| `denote_{propext,iffRec,iffIntro,choice,nonemptyIntro,nonemptyRec}_type` (bare `cval`; probe-verified for the first) | relocate + generalize | 190 |
| `iff_forces_eq` and its `iffVal`/`iffIntroVal`/`iffRecVal` supports | transpose `Model/StdAxioms.lean:129–443` | 315 |
| `nonemptyVal_forces` and supports | transpose `Model/StdAxioms.lean:523–768` | 245 |
| the two keys + `AnnotOkV t` (the `Eq`-spine, `hEqApp` pattern) | new | 120 |

≈ **980 lines**, of which ~300 are relocations that shrink
`TTVerify/StdAxiomKey.lean` and serve both lanes.

**One reconciliation is genuinely new** (neither lane has it):
`choiceV` (TT) abstracts over `¬¬A`, while the checker's pin abstracts
over `⟦Nonempty A⟧`, and `Model`'s `choiceVal` over `unitSet`/`empty`.
`lamC_mem` needs the domains to *match*, so the proof must first show
`⟦Nonempty A⟧ = ¬¬A` by `prop_ext` (both live in `univ 0`) — the
forward direction is `nonemptyVal_forces`, the backward one
`nonemptyIntroVal_app₂_mem` plus `exists_mem_of_dneg`.

### `MemberEtaS` retired — a threaded invariant, not a forwarded obligation

`MemberEtaS` is **gone from the campaign's hypothesis list**, replaced
by `memberEtaS`, an in-fold *theorem*.  What the fourteen carry in its
place is `EtaClosedS`, which is a different animal: **`V`-free**, about
`checkDecl` and `Env` only, with no `EnvS`, no `EtaLawV`, no valuation.
The semantic content of the eta obligation is discharged; what remains
is environment bookkeeping the Model lane already does.

**The measurement was wrong twice, in the same direction.**  T6 sized
this at "~260 lines of Model template", then corrected to "not
dischargeable at its signature; an ~82-occurrence re-signing ripple".
Both underestimated: the *signature* was not the blocker.  Reading the
four rows of the §"not a member-fold discharge" table against what a
fold can actually hold shows the live row is dischargeable in-fold —
`EtaPins` is **already threaded** and carries `etaLawKeyS`'s entire
premise list — and that the three dead rows die on facts that are
invariants, not premises.

**The three rows and their invariants:**

| row | dies on |
|---|---|
| `projFnName T j = c₀.name` | the member's own `isProjFnShape = false` guard |
| `T` stored *outside* the block, `caps.etaCtor = c₀.name` | `EtaFamiliesClosedO` — an outside former's constructor is already stored, and `c₀.name` is fresh |
| `T` a block former, `etaFields > 0` | `BlockEtaPinned`'s third conjunct — the first projection is not stored, because the projection fold has not run |

and the live row (`etaFields = 0`, the family completing at `T` or at
its constructor) is `etaLawKeyS` with its projection premises vacuous —
`memberUnitS`'s shape exactly.

**`BlockEtaPinned` (new, `Verify/Extend/Iota.lean`)** is the piece the
design was missing.  `EtaPins` speaks about the members *ahead* of the
fold; the head obligation is about a family that may already be
*behind* it.  So the fold needs a stored-side twin:

```
∀ n cvS capsS, blockNames.contains n → env.find? n = some (.indInfo cvS capsS) →
  capsS.eta = true →
  EtaPins mode env n cvS.levelParams capsS ∧
    blockNames.contains capsS.etaCtor = true ∧
    (0 < capsS.etaFields → env.find? (projFnName n 0) = none)
```

Three conjuncts, one per thing the discharge needs, all delivered
*under* `capsS.eta = true` — which is what makes the generic
(`caps = {}`) arm's supply vacuous instead of impossible.  **The
freshness had to live inside this conjunction**: as a separate
`BlockProjFresh` premise it was unconditional, and the generic arm
could not supply it; as the third conjunct it is only ever asked for
where the assembly's `hprojFresh` answers.  *Rule: an invariant's
conditions belong where its consumer's hypotheses are, not beside it.*

**What `EtaClosedS` costs and why it is not a regression.**  The
outside-families row is the one fact a block fold provably cannot
establish about itself: it is true one declaration earlier.  Threading
it turns the fold's carrier into

```
def EnvSOk (V) [SetTheory V] (env : Env) : Prop :=
  Nonempty (EnvS V env) ∧ EtaFamiliesClosed env
```

— a *bundle*, chosen over a second premise precisely because it keeps
every fold's binder count unchanged (six folds across `Bridge/Sound`
and `Main`, three of them state-carrying); only construction and
consumption sites move.  The fourteen's public statements are
untouched; `EtaClosedS` is a hypothesis exactly like the other four.

**Landed:** `Verify/Extend/Iota.lean` (`BlockEtaPinned`,
`projFnName_ne_of_shape`, `BlockEtaPinned.cons`),
`Verify/Extend/Ind.lean` (`EtaFamiliesClosedO.cons`),
`Install/IndRecsS.lean` (`indRecsFoldR_mono`, `indRecsR_mono` — the
V-free monos that pull the run's projection freshness back to the
block's base), `Install/IndMembersS.lean` (`memberEtaS`,
`etaMemberData_step`), the threading through both lanes' four folds,
and the two assemblies' base supplies.  `memberEtaS` stands at
`[propext, Classical.choice, Quot.sound]`.

**Open, and now purely syntactic:** `EtaClosedS`.  Its Model-lane twin
is the second conjunct of `Model/Consistency.lean`'s `checkDecl_sound`
— one `EtaFamiliesClosed.cons_nonind` per non-inductive branch, plus
the block install's own former, whose `indBlockCaps.etaCtor` is a
block member the member fold stores.  It is *interleaved* with the
model construction there, so it is a re-derivation rather than a
relocation; `Verify/DeclStores.lean` covers only `defn`/`thm`.

### `EtaClosedS` never had to exist — and `OfReduceKeyS` threaded

`EtaClosedS` is **deleted**.  It was the residue of `MemberEtaS`, and
it dissolved the moment the obligation was stated at the right place.

**The move.**  `EtaClosedS` was a standalone claim about `checkDecl`
(later `DeclR`), so its proof would have had to re-derive, from
scratch, every fact about what a block install stores — the member
fold's entries, the recursor swap's shadowing, the projection and
template folds' additions.  But `declIndS` *already holds all of
them*: `hnonrecUp`, `indMembersR_mono`, `hidR`, `hIfilt`.  So the
conclusion moved into `declIndS`:

```
DeclIndS V := … → EtaFamiliesClosed env → DeclIndR … →
  Nonempty (EnvS V env₂) ∧ EtaFamiliesClosed env₂
```

and `declStepS` returns the same pair — the five non-inductive kinds in
four lines each (`EtaFamiliesClosed.cons_nonind`, `hknd` vacuous
because the stored entry is a `defnInfo`/`thmInfo`/`axiomInfo`), and
the basis kind by `decide` on the pinned lists.  The fold carrier
`EnvSOk` was already the right shape, so **not one binder moved**.

*Rule: a side invariant that a step can establish about itself is not
an obligation; it is a second conclusion.  State it where the facts
are, not where the fold wants it.*

**What the ind case actually needed** — four small V-free lemmas, and
they are the honest inventory of "what a block install does to the
former table":

| lemma | says |
|---|---|
| `ExtEta` (+ `refl`/`trans`/`cons`, `Verify/EnvGuards.lean`) | non-recursor entries survive verbatim and no new former appears — closure transfers along it |
| `indMembersR_indNew` | a former stored after the member fold is the base's, verbatim, or a block former carrying the fold's `caps` |
| `indMembersR_ctorEntry` | the constructor member is stored with its arities |
| `indRecsR_noInd`, `projInstallR_ext`, `templatesR_ext` | the three post-member phases add no former |

`ExtEta`'s *keep* clause is restricted to non-recursor entries on
purpose: the recursor swap replaces its own provisional entries, so
verbatim preservation is false in general and true exactly where
`EtaFamiliesClosed` reads (a capability constructor is a `ctorInfo`).

**And `OfReduceKeyS` is now threaded**: the ripple that would have
churned its signature is over, so `ofReduceKeyS` goes in at
`declAxiomS` and `hofr` leaves the fourteen.

**The fourteen now carry exactly two hypotheses**: `DivModPinS V` and
`StdAxiomKeyS V`.  Every one of them still stands at
`[propext, Classical.choice, Quot.sound]`.

### The ledger, and the two that remain (measured)

Fourteen theorems, two hypotheses, all at
`[propext, Classical.choice, Quot.sound]`:

```
no_constant_of_Empty_R          checkDecls_sound_R
no_proof_of_Empty_R             checkDeclsC_sound_R
no_proof_of_Empty_C_R           checkDeclsS_sound_R
no_proof_of_Empty_S_R           checkDeclsSP_sound_R
no_proof_of_Empty_SP_R          checkDecl_sound_R
no_proof_of_Empty_input_R       no_proof_of_Empty_input_C_R
no_proof_of_Empty_input_S_R     no_proof_of_Empty_input_SP_R
```

**`DivModPinS` — sized against the right lane, and it is the larger.**
Applying "check every lane before pricing": the TT lane's
`TTVerify/DivModPin.lean` is 1526 lines, but the *set* lane's own
twin is `Model/DivModCert.lean` at **1622**, and that is the template
(`EnvModel`, `interp`, value equations — not `HasType`).  The SetR
delta is the same one `StdAxiomKeyS` has: `m.val n ψ` becomes
`interp V ρ (m.cval n ψ)` at every statement, plus `AnnotOkV`
packages the Model lane does not carry.

The inputs are already shared-tier: `checkDivModPin_inv` and
`checkDivModCerts_inv` (`Verify/DivModInv.lean`) deliver the guards,
the storage, the pin annotate and `CertRuns`.  What must be built is
`CertRuns → DivModClausesV`: `Model/DivModCert.lean`'s
`divModCert_extract` → `divmod_certs_sound` chain, over `EnvS`.
`CtxOkR.pinnedCtx` is landed and is the frame this consumes.

*Classification of the TT file, for whoever relocates:* ~350 of its
1526 lines are lane-independent (`natOpCod_shape`, `CtxOk.annotate`,
`denote_natOpCod`, `denote_natOpTy1`/`_2`, `denote4_of_denote2`,
`certGuard_proof`, the three `*_cons` guard lemmas, `psiEq1`,
`dmEqStmt`, the `dm*` value abbreviations and the `inst2_*` family) —
`cval`-only or pure.  The remaining ~900 (`clause1T`/`clause2T`,
`DMSpine.sound`, `dmClause1`/`2`, the nine per-operation lemmas,
`dmBase_of_guard`, `cert_extractT`, `Frames4.*`) are `HasType` work
with no set-side content.

**`StdAxiomKeyS` — ~980 lines**, plan unchanged (relocations first,
then `iff_forces_eq`, then the `¬¬`/`Nonempty` reconciliation).

**Both are leaves**: proving either changes no signature, so partial
work on them cannot break the tree — but it also cannot be sealed.

### `DivModPinS`, the extract layer — and the reopen condition, answered

`Setlec/SetR/DivModPin.lean` (354 lines) lands the layer between the
checker's certificate verdict and the value equations.  All of it at
`[propext, Classical.choice, Quot.sound]`.

**The reopen condition is answered "no".**  T6 retired `DivModCertR`
and recorded: *if `DivModPinS`'s discharge shows the certificate
content wants first-class relational form, reintroduce it then.*  It
does not.  The reason `ReducePinS` is 118 lines is that `ReducePinR`
hands it a `DefEq` **relation** — one `DefEq.sound` and it is done —
and the obvious inference was that div/mod needs the same.  But the
missing step is not a relation, it is an **`EnvR`**: `checkBridge`
turns the verdict's `annotateCore`/`inferTypeCore`/`isDefEqCore` runs
into `Infer`/`DefEq` at any `EnvR`, and the install already holds one
(`m.toEnvR`).  So `certValueS` does the bridging *in the discharge*,
where the TT lane also put it, and `DeclR` stays as it is.

*Rule: before reopening a statement for a consumer, check whether the
consumer can reach the machinery itself.  A missing premise and an
unimported lemma look identical from inside the proof.*

The one architectural consequence worth naming: the file sits **above
both tiers** (it imports `Bridge.Main` *and* `Install.Value`), because
an install obligation whose content is a checker run is not an install
lemma.  `Setlec/SetR.lean` is where it is wired in; nothing in either
tier imports it back, so the layering is unchanged.

**What is in it:**

| piece | content |
|---|---|
| `certValueS` | one certificate run ⟹ the statement's interpretation is inhabited, via `InferClaimsR`/`DefEqClaimsR` at depth 4 and `Infer.sound`/`DefEq.sound` |
| `fvarLeaves_substConst0`, `looseBVarsBounded_substConst0` | `substConst0` rewrites `const` nodes and **never enters an `fvar` annotation**, so a closed replacement moves no leaf — this is why the depth-4 frame survives the substitution unexamined |
| `dmVal`, `denote_dmDep`, `denote_dmSelf` | the frame's valuation: dependencies at their storage, the pinned operation at the annotated stored value (`cvalAt_self`) |
| `sat_four` | the `[H2, H1, natV, natV]` frame satisfied slot by slot |
| `natOpTyPinned_binaryE`/`_unaryE`, `natOpCod_stored` | the pinned-type inversions (`log2` is the unary one) |
| `dmBinMem`, `dmUnMem` | every operation the certificates mention is a function on the frame's `Nat` — the `Eq`-spine's side conditions |

**Remaining (the clauses layer):** per statement, the `Eq`-spine's
denotation and `EqLawV.app₃` + `eq_of_mem_eqv` to turn the inhabited
truth set into the equation; then the nine operations' clause
assembly.  `c ∈ natOpDeps c` for every div/mod op, so `divModEnvGuard`
pins the operation's *own* type as well as its dependencies' — that is
where `dmBinMem` gets its hypothesis for the self case.

### `DivModPinS`: one certificate, discharged

`dmCertEq1`/`dmCertEq2` land — the packaged forms a clause
instantiates.  Both at `[propext, Classical.choice, Quot.sound]`;
`Setlec/SetR/DivModPin.lean` is now 762 lines.

**The design that made these short: everything a certificate needs
from its statement is `decide`-able of the literal statement.**  The
three syntactic obligations `InferClaimsR`/`DefEqClaimsR` ask for —
`WScoped 4`, `looseBVarsBounded 0`, `LeavesBounded` — plus the
`pinnedCtx` slot condition all reduce to *where the leaves are*, and
the div/mod statements' leaves are exactly `x` and `y` at `Nat`.  That
is `dmLeavesOk`, a `Bool`, and every one of the three obligations
follows from it plus `wscopedB`/`looseBVarsBounded` on the literal.

The substitution of the pinned operation preserves all three
(`fvarLeaves_substConst0`, `wscopedB_substConst0`,
`looseBVarsBounded_substConst0`), so a clause's syntactic side
conditions are `by decide` **on the unsubstituted statement** — the
`annVal` blob never has to be examined.

*Rule: when a proof obligation is about a literal, find the decidable
predicate it factors through before writing any induction.  The
inductions are then about the one thing that is not literal.*

Two mechanical notes worth keeping:

* `Expr.WScoped` is well-founded, so `simp only [Expr.WScoped]`
  unfolds it **all the way** to a flat nest of `<` and `True`, and an
  anonymous constructor cannot be written against the result.  Build
  with per-former lemmas (`dmApp_wscoped`, `dmFvar_wscoped`) instead —
  their goals stop unfolding at a variable.
* Applying a substitution lemma to the *whole* statement and proving
  the unsubstituted side by `simp` is much shorter than pushing the
  substitution through the spine by hand.  The first version of `hwE`
  did the latter and needed four `show`s; the second is one line.

**Remaining:** the vocabulary's denotations (`op2`, `sub2`, `add2`,
`mul2`, `div2`, `mod2`, `ble2`, the literals) and the nine
operations' clause blocks.  Each clause supplies `dmCertEq*` with two
denotations and two memberships and reads off the equation;
`DivModClausesV`'s conjuncts are the same `app`-chains, so the match
is structural.

### `DivModPinS`: the fragment evaluator, and the frame

`Setlec/SetR/DivModPin.lean` is 1324 lines, all at
`[propext, Classical.choice, Quot.sound]`.  Two more layers landed.

**`dmEvalV` — denote *and* evaluate in one step, so no clause ever
names a `VExpr`.**  The first design had each clause compute its two
sides' denotations explicitly and then transport the equation onto
`DivModClausesV`'s `app`-chains.  That is nine blocks × two sides ×
a `VExpr` spelled out by hand.  Instead:

```
dmFragOk c ns : Expr → Bool          -- the statements' grammar
dmEvalV V val x y : Expr → V         -- its value
dmDenEval : dmFragOk … e → ∃ eV, denote … (subst e) = some eV ∧
              ∀ ρ₄, interp ρ₄ eV = dmEvalV V val (ρ₄ 3) (ρ₄ 2) e
```

and `dmEvalV` of `op2 x y` *is* `app (app (val c) x) y` — the very
chain `DivModClausesV` is written in.  So a clause denotes its sides
by `dmDenEval … (by decide)` and the match against the clause is
definitional.

*Rule: when two layers are written in the same shape by construction
(here: the certificate statements and the semantic clauses, both built
from one vocabulary), evaluate into that shape rather than transporting
between two spellings of it.*

**`dmFrameS` — the obligation's whole preamble, as one theorem.**  The
guards give it all: `natLitSupported` for `Nat`/`zero`/`succ`,
`natOpStoredOk` at each dependency for the function-space memberships,
and — because `c ∈ natOpDeps c` for every pin-certified operation —
the operation's *own* pinned type, which is where `dmSelfMem` gets its
hypothesis.  `Nat.ble` is a dependency of all nine, and it is the only
route by which `Bool` enters the frame at all (`natOpCod_ble`).

Two frictions worth recording:

* **`Nat.log2` is unary.**  Every other pin-certified operation is
  binary, and the frame's type conjunct had to become a disjunction
  because of it — the `decide` that would have ruled the unary case
  out is the one that fired and proved the *opposite*.  The checker's
  own `natOpTyPinned` has the same split; the model side had simply
  not needed to look.
* **`cases h : env.find? n` rewrites the goal** — fired again, in
  `natOpCod_stored`.  Sixth occurrence in the campaign; the witness is
  `rfl`, never the named hypothesis.

**What remains of `DivModPinS`** is the nine clause blocks.  Each is:
`dmDenEval` the two sides, `dmCertEq1`/`dmCertEq2` for the equation,
`dmFrameS`'s memberships for the side conditions, and `pt_mem_eqv_self`
for the guard slot.  One friction is known in advance: the blocks need
`cv.name` *concrete* (the statements and `divModCertStmts` only
compute then), so the proof should generalise `cv.name` to a variable
before `rcases`ing `natDivModNames` — otherwise `subst` has nothing to
act on.

### The trap family's sixth shape: **jointly unsatisfiable premises**

Instantiating `dmCertEq1` at `Nat.gcd`'s first certificate found a
defect in three statements this campaign had already landed and
audited.

**What was wrong.**  `certValueS` (and through it `dmCertEq1`/`2`) took
`CtxOkR.pinnedCtx`'s *closed-entry* form: `Δ.length = 4`, **every entry
closed**, and each leaf's annotation denoting to `Δ.getD (3 - l.1)`.
For the two `Nat` slots that is exactly right.  For a **hypothesis**
slot it cannot be met at all: the entry is the denotation of a
hypothesis type, and a hypothesis type mentions `x` and `y` — at depth
4 it is `.bvar 3`/`.bvar 2`, so it is *not closed*, and `pinnedCtx`'s
`hcl` has no proof.

So the two premises were jointly unsatisfiable.  Everything compiled;
the axiom audit was clean; the statements were **vacuous**.

**Why `CtxOkR` was fine all along.**  The relation is *slack* by
design: it asks for `Infer Δ (.bvar (d-1-l.1)) T'` together with
`DefEq T' T`, not for entry equality.  So the frame is satisfiable with
the hypothesis entries at depth **2**, `Infer.bvar`'s own `liftN 2`
supplying the depth-4 denotation — the TT lane's `denote4_of_denote2`
is exactly that step, and its presence there was the clue.
`pinnedCtx` is one *sufficient* route, correct only where the entries
are closed; T6 landed it "for `DivModPinS`" without an exercised
consumer, and the closedness hypothesis is what that cost.

**The fix.**  `certValueS`, `dmCertEq1` and `dmCertEq2` now take
`CtxOkR` **directly** — strictly more general, satisfiable, and it puts
the lift where the caller can see it.  The three closed-entry slot
builders (`dmSlots_stmt`, `dmSlots_applied1/2`) are deleted; the
reasoning is kept as a `/-! ### Why the slots are not built here -/`
note at the site.

**The rule, sharpened.**  The campaign's test was *"an obligation is
dischargeable only if every free variable of its conclusion is
determined by its hypotheses."*  That test passes here — and the
statement was still vacuous.  The missing check is the dual:

> **Before freezing a premise pair, ask what makes them true
> *together*.**  Each of `hclΔ` and `hslot` is satisfiable alone; only
> their conjunction is not.  A premise list is not a set of
> independent facts, and "each one has a supplier" does not mean the
> list does.

The house rule that would have caught it is already written in this
file — *the house rule forbids freezing a statement no consumer has
exercised* — and it was violated twice over: by `pinnedCtx` at T6, and
by `certValueS` here.  This is the second time an unexercised statement
in this campaign had its quantifiers or its premises wrong; the trap
family is now **six**-membered, and every member was found by the first
consumer, never by review.

### The frame, in its honest form — `pinnedCtxLift`

Built against the actual consumer this time, not ahead of one.

`CtxOkR.pinnedCtxLift` (`Setlec/SetR/CtxOkR.lean`) is `pinnedCtx`'s
general form: the slot condition reads

```
denote cval env φ d l.2.2 = some ((Δ.getD (d - 1 - l.1) default).liftN (d - l.1))
```

— exactly `Infer.bvar`'s own lift, since `Infer.bvar` at index
`i = d - 1 - l.1` produces `(Δ[i]).liftN (i + 1)`.  `pinnedCtx` is the
corollary where every entry is closed and the lift vanishes: right for
a context of *constant* types, wrong for a **telescope** whose later
entries mention its earlier variables.

The div/mod frame is `[H₂, H₁, natV, natV]` where **`H₁` is the first
hypothesis type's denotation at depth 2 and `H₂` the second's at depth
3** — the depths at which those types are *stated*.  Two `V`-free
lifting lemmas (`denote_lift1`, `denote_lift2`) carry them to depth 4;
they are the twins of the TT lane's `denote4_of_denote2`, whose
existence there was the clue I had classified and walked past.

*The searchlight rule, from the other side: a lemma the sibling lane
has and you do not is not noise in a classification table — it is the
shape of a step you have not taken yet.*

Landed with it: `dmCtxOk_stmt`, `dmCtxOk_applied1`, `dmCtxOk_applied2`
— the three `CtxOkR`s a clause needs, in the satisfiable form.  All at
`[propext, Classical.choice, Quot.sound]`.

### `dmClause1S` — one guarded div/mod clause, discharged

The crux of `DivModPinS` is proved.  `Setlec/SetR/DivModPin.lean` is
1797 lines, all at `[propext, Classical.choice, Quot.sound]`.

```
dmClause1S : … → CertRunFacts μ env F c value' ([eqB gl gr], eqN lhs rhs) proof →
  <13 syntactic facts, all `by decide` at the call site> →
  <4 memberships> →
  dmEvalV V VAL xx yy gl = dmEvalV V VAL xx yy gr →
  dmEvalV V VAL xx yy lhs = dmEvalV V VAL xx yy rhs
```

That conclusion is *literally* a `DivModClausesV` conjunct: `dmEvalV`
of `op2 x y` is `app (app (val c) x) y`.  So each of the seventeen
one-hypothesis clauses is one application of this theorem.

**What made it work, in order:** `dmFrameS` (the guards, unpacked
once), `dmDenEval` at the frame depth the fragment is *read* at,
`denote_lift1`/`denote_lift2` to carry the hypothesis entries from
where they are *stated* (2 and 3) to where `CtxOkR` reads them (4),
`dmCtxOk_applied1`/`dmCtxOk_stmt` through `pinnedCtxLift`, `sat_dm`
with each hypothesis slot read in its own shifted environment, and
`EqLawV.app₃` + `pt_mem_eqv_self` turning the clause's guard into that
slot's inhabitant.

Two frictions, both already in this file's own record and both fired
again:

* **multi-line `at`-lists do not parse** — the `rw [hc] at …` list had
  to go on one line;
* `(…).fvarsBelow` on a fresh line parses as an application; write
  `Expr.WScoped.fvarsBelow (…)`.

And one new sizing note: the frame's `htyOwn` had to be split *by
`Nat.log2`* rather than offered as a disjunction — a consumer needs to
*know* it has the binary shape, and `∨` makes it prove that again at
every call.  **A disjunction in a frame is a bill the consumer pays
once per use; a conditional is one it pays once.**

**Remaining:** the nine clause blocks — for each operation, unpack
`CertRuns`, supply `dmClause1S` with the two/three certificates'
memberships (`hselfMem`, `hdepBin`, `hbleMem`, `hzeroMem`,
`hsuccMem`, `hctorMem` are all in `dmFrameS`), and read off
`DivModClausesV`.  `Nat.div`/`Nat.mod`'s first certificate has two
hypotheses and wants the `dmCertEq2` twin of `dmClause1S`.

### `DivModPinS` CLOSED — one hypothesis left

`Setlec/SetR/DivModPin.lean` is 2879 lines; `divModPinS` stands at
`[propext, Classical.choice, Quot.sound]` and is threaded at
`declStepS`, so **`hdm` has left the fourteen**.  They now carry
exactly one hypothesis: `StdAxiomKeyS V`.

**The nine blocks cost almost nothing, because the shape was right.**
Once `dmClause1S` existed, seven of the nine operations were *generated
mechanically* — same skeleton, differing only in the certificate-proof
list, the dependency abbreviations, and four membership terms per
clause — and compiled with **zero errors on the first splice**.  That
is the payoff of the definitional-evaluation decision: `dmEvalV` of a
statement side *is* the `app`-chain `DivModClausesV` is written in, so
a clause never bridges two spellings.

*Rule: when a proof splits into `n` near-identical cases, the measure
of whether the shared lemma is right is whether the cases can be
written out mechanically. Seven-of-nine first-try is the shape being
right; a case that needs thought is a premise in the wrong place.*

**Three frictions worth keeping:**

* **`decide` cannot evaluate a well-founded definition.**
  `Expr.wscopedB`, `Expr.fvarLeaves` (hence `dmLeavesOk`) are
  `termination_by` definitions, so `by decide` fails on them however
  literal the argument is; `by simp [Expr.wscopedB]` /
  `by simp [dmLeavesOk, Expr.fvarLeaves]` go through the equation
  lemmas and succeed.  `dmFragOk` and `looseBVarsBounded` are
  structural and `decide` fine.  **The tactic that works is a fact
  about the definition's recursion, not about the goal's size.**
* **`reduceIte` will not fire on `natModName = natDivName`**: those
  are `def`s, so the `Decidable` instance does not reduce without
  unfolding them.  `if_neg (show ¬(natModName = natDivName) from by
  decide)` as a simp argument does — `decide` unfolds, `reduceIte`
  does not.  This is why `Nat.div`/`Nat.mod` needed a different
  dispatch line from the other seven.
* 124 unused-simp-argument warnings, from the thirty-four membership
  steps each wanting a slightly different lemma set: the file takes
  `set_option linter.unusedSimpArgs false`, exactly as
  `Setlec/TTVerify/DivModPin.lean` does and for the same reason.

### `StdAxiomKeyS` begun — the relocation, and the split

Two pieces landed.

**Relocated to the shared tier** (`Setlec/Verify/StdAxiomPin.lean`,
128 lines): `iff_shapes` and `nonempty_shapes`, `stdAxiomOk`'s two
branch inversions.  They are pure `Env`/`Bool` reasoning — no
valuation, no typing judgement — so task #123's criterion puts them in
`Verify`, and both lanes read them.  Verbatim; the TT lane now imports
them and is 989 lines instead of 1096.

The six `denote_*_type` computations were **not** relocated.  They use
their lane's `denote_const_nolevels`, which lives on each side, and the
set lane needs `interp`-level facts the TT ones do not produce — so
moving them would mean moving a third lemma and editing a closed lane
for a shape neither side would share.  *Relocate what is the same, not
what merely looks alike.*

**`Setlec/SetR/StdAxiomKey.lean`** carries the split (`PropextKeyS`,
`ChoiceKeyS`, `stdAxiomKeyS_of`) and `denote_propext_typeS`, which
transposes from the TT lane unchanged over a bare `cval`.

**What remains is exactly the two forcing arguments**, and they are
where the Model lane's weight is:

| piece | Model source | ≈ lines |
|---|---|---|
| `iff_forces_eq` + `iffVal_app₂_mem`, `iffIntroVal_app₄_mem`, `iffRecVal_mem` | `Model/StdAxioms.lean:129–443` | 315 |
| `nonemptyVal_forces` + its three supports | `:523–768` | 245 |
| the two keys and their `AnnotOkV` | new | 120 |

The transposition is `m.val n ψ ↦ interp V ρ (m.cval n ψ)` throughout,
plus the `AnnotOkV` packages the Model lane does not carry.  Neither
argument needs the recursor's *iota* rule — only its typing — which is
what keeps them independent of the inductive install.

### `StdAxiomKeyS` closes — and the fourteen are hypothesis-free

The last obligation is gone.  Both halves landed in
`Setlec/SetR/StdAxiomKey.lean` (724 lines), `stdAxiomKeyS` threads at
`declStepS` in `Bridge/Sound.lean` and `Main.lean`, and every one of
the fourteen now stands with **no named hypothesis** at exactly
`[propext, Classical.choice, Quot.sound]`.

**The transposition was three times smaller than the Model source,
and the reason is `piC`.**  `Model/StdAxioms.lean`'s two forcing
arguments spend most of their length on *universe scaffolding*: the
leveled `app_mem`/`lam_mem`/`pi0_mem_univ0` each carry a
codomain-membership side condition, so eliminating down a four-step
recursor telescope costs four nested `pi_mem_univ` obligations
(`hMS`, `hminorU`, `htail`, and the `r1`–`r5` chain that threads
them).  The `SetR` lane interprets every `VExpr.pi` to the
*level-free* `piC`, whose `app_mem_piC`, `lamC_mem` and `app_lamC`
have **no side conditions at all** — so `iff_forces_eqS` is
`app_mem_piC` five times in a row and `nonemptyVal_forcesS` is four,
with no scaffolding whatsoever.  315 + 245 Model lines became 67 + 34.

*Rule: when a lane's formers drop an index the source lane carried,
re-derive the proof rather than transposing it; the index is usually
paying for side conditions the new lane does not owe.*

**The witnesses are the layer's own constants, and that is what makes
the keys short.**  `Vf ψ = .const .propext []` and
`.const .choice [ψ uN]`: closedness, level-invariance and `AnnotOkV`
are then `trivial`/`rfl`/one `rw`, and only the *membership* obligation
does work.  The Model lane, having no `VExpr` layer to borrow from,
has to build `propextVal`/`choiceVal` by hand.

**The `¬¬`/`Nonempty` reconciliation did not resist — it was a
`prop_ext`.**  `bval .choice us = choiceV V u` abstracts over the
layer's double negation `piC (piC A fun _ => empty) fun _ => empty`,
while the checker's pin abstracts over the stored `app NE A`, and
`lamC_mem` needs the two domains *equal*, not merely equi-inhabited.
They are equal: both are propositions (`piC_prop_mem_univZero`,
`nonemptyVal_app_memS`), and both are `pt`-inhabited exactly when `A`
is — left to right by `exists_mem_of_dneg` + `nonemptyIntroVal_app₂_memS`
+ `mem_univ_zero`, right to left by `nonemptyVal_forcesS` and the
observation that over an inhabited `A` the domain `piC A fun _ => empty`
is empty, so the product is vacuously `pt`-inhabited.  `dneg_eq_nonemptyS`
is the whole reconciliation, eleven lines.

*Rule: when two lanes name the same proposition differently, check
whether the ambient theory can prove the two names denote the same
**set** before building a transport between them.  In a `Prop`-as-
subsingleton model, `prop_ext` turns a bi-implication into an equation,
and an equation is what the formers' congruence rules want.*

**One shared-tier statement grew.**  `nonempty_shapes` returned the
`Nonempty` former's `levelParams` but not its type; the set lane needs
the type to compute the former's denotation (the TT lane never did).
The conjunct was added in `Setlec/Verify/StdAxiomPin.lean` and the one
TT consumer destructures it away.  *A shared inversion lemma states
what its consumers need; a lane that needs more is a reason to widen
it, not to restate it locally.*

**Two frictions worth keeping:**

* **The `some` may already be gone.**  `denote_*` computations that
  reduce under a full `simp` (rather than `simp only`) arrive as
  `<literal> = t`, not `some <literal> = some t`; `obtain rfl := ht`
  works where `obtain rfl := Option.some.inj ht` fails with a
  `subst`-shaped error that reads like a malformed proof.
* **A `def`-named constant blocks `denote_const_nolevelsS`.**  The
  rewrite is stated at `iffName`/`nonemptyName`; the goal, after
  `simp` has unfolded the pinned declaration, holds
  `Name.anonymous.str "Iff"`.  The fix is to state the const
  denotation as a `have` and `simp only [iffName] at` *it*, then feed
  it to the main `simp` — the same recipe `denote_propext_typeS` uses.

**Signature note.**  The eight `False`-concluding theorems used to
bind `V` through the `(hstd : StdAxiomKeyS V)` hypothesis.  With the
hypothesis gone their statements no longer mention `V`, so it becomes
an explicit leading binder — exactly the Model lane's
`no_proof_of_Empty (V : Type u) [SetTheory V]` shape.

## T7 — the retirement

`Setlec/Model/*` is deleted: **83 files, 62,992 lines**, the direct
`Expr` set model and its consistency proof.  The root `Setlec.lean`
drops its sixteen `Setlec.Model.*` imports; `lake build` goes from 424
jobs to 341.

**The tier was a leaf.**  A reachability scan over the import graph
from all eight roots (`Setlec.lean`, `Setlec/TT.lean`,
`Setlec/TTVerify.lean`, `Setlec/SetR.lean`, `Setlec/PinGen/Certs.lean`,
`Main.lean`, `AnnotateBasis.lean`, `tests/SetlecTests.lean`) found
**nothing** outside `Setlec/Model/` importing it but the root umbrella,
and **no module made dead by the deletion** — every genuinely shared,
`V`-free piece had already been relocated to `Setlec/Verify/*` by tasks
#123 and #148 T1/T6, which is what made the cut a one-line edit rather
than a salvage operation.

*Rule: the cost of a retirement is paid before it, in the relocations.
A tier that can be deleted by removing its imports was already
retired; the commit only records it.*

**What the deletion costs, stated plainly.**  The direct
simple-structure install (`Setlec/Kernel/Direct.lean`,
`directStructsEnabled`) had its set model only in
`Setlec/Model/Direct*.lean`.  That switch has shipped `false` since
T0b by user ruling, and both surviving lanes reason about the shipped
configuration, so **no verdict changes and no theorem weakens** — but
the direct path's recognition layer and install arm are now *unmodeled
code behind a `false` switch*, pending their own deletion.  The
comments in `Setlec/Kernel/Direct.lean` and `Setlec/Kernel/Checker.lean`
say so.

**Doc pointers.**  Fourteen present-tense references to `Setlec/Model/*`
(the "Verification: …" headers in `Setlec/Kernel/*`, the "the
consistency chain covers" claims, `CLAUDE.md`'s layering rule) were
repointed to `Setlec.SetR.*`.  The ~120 *provenance* references
("relocated from `Setlec/Model/Extend/Ind.lean`, task #123") were left
alone: they are the campaign's record of where a lemma came from, and
rewriting them would erase the history that justifies the file
boundaries.  *A dangling pointer in a present-tense claim is a defect;
a dangling pointer in a past-tense provenance note is a citation.*

**The replacement surface** is the fourteen `*_R` theorems of
`Setlec/SetR/Main.lean`, all hypothesis-free at
`[propext, Classical.choice, Quot.sound]` (previous §).  Battery after
the deletion: build warning-free, `lake test`, arena 90/92, e2e 72/72,
split 11/11, mode flags 10/10, both sweeps as expected, zero sorries.

## T7b — the declarative lane and its mode

By user ruling ("TT tier and direct set model removed") the declarative
verification lane goes too.  **`Setlec/TTVerify/*.lean`: 50 files,
33,808 lines**, plus the `SetlecTTV` library target and the
`--tt-model` mode it was stated at.

**The cut was made at the dependency boundary, not the folder name.**
The measurement, in order:

| piece | verdict | why |
|---|---|---|
| `Setlec/TTVerify/*.lean` | **deleted** | nothing outside imported it; the fourteen `*_R` are the replacement |
| `Setlec/TT/Nat/*`, `TT/Nat.lean`, `TT/Examples.lean` | **deleted** | the layer's own demonstrations; reachable only from the `SetlecTT` umbrella |
| `Setlec/TT/Semantics/Consistency.lean` | **deleted** | the declarative lane's own consistency theorem — its consumer was the lane |
| `Setlec/TT/Deq.lean` | **deleted** | one code consumer left (`denote_beta_step`), itself TT-lane-only |
| `Setlec/Verify/Denote/Weaken.lean`, `Setlec/Verify/Extend/Decl.lean` | **deleted** | made unreachable by the `TTVerify` deletion |
| `Setlec/Verify/Denote/Tele.lean` | **split** | `TeleTyped`/`VTeleTyped` (typed walk, lane-only) out; `DenoteSpine` + `denote_mkAppN*` (34 + 28 SetR call sites) kept |
| `Setlec/Verify/Denote/HasTypeSubst.lean` | **split** | the `HasType.weakenN`/`weakenHead`/`instN`/`instantiate` battery out; `LiftCtx`/`InstCtx` kept — `Setlec/SetR/Weaken.lean` imports the file for them |
| **`Setlec/TT/Judgment.lean` (`HasType`)** | **STAYS** | see below |
| `TT/{Syntax,Subst,Const}`, `TT/Semantics/{Value,Interp,ConstOk,Soundness}` | **stay** | `VExpr`, `interp`, `bval`, `BConst`, `Sat`, `HasType.sound` |

**The declarative rule layer stays, and the reason is a measurement,
not a preference.**  The instruction was to cut `HasType`/`Deq` *if its
only remaining consumers were the TT lane and the tt-model config*.  Its
consumers are not: **`Setlec/SetR/Install/BasisS.lean` uses
`HasType.const` and `HasType.sound` at seventeen sites** — that pair is
how each basis constant's membership in its own denoted type is
obtained, and `HasType.sound` is proved by induction over *every*
constructor of `HasType`, so the inductive cannot be thinned either.
`Deq` had no such consumer and went.  The condition was conditional and
the condition was false; the boundary is where the consumers put it.

*Rule: a deletion order that names folders will cut in the wrong place.
Name the consumers, measure them, and let the boundary fall where the
measurement says — then write down which way each file went and why,
because "we kept `Setlec/TT/*`" is not a record and "SetR calls
`HasType.const` seventeen times" is.*

**The mode.**  `CheckMode` loses its `.ttModel` arm and is two-valued;
`--tt-model` joins `--yolo` and `--infer-only` as a hard error (exit 3),
with a message naming what happened to it.  `CheckMode.ttChecks` is now
constantly `false`.

**The seven gated checks are kept, statically unreachable.**  Deleting
them would touch `Setlec/Kernel/{Core,Modeled,CheckerS}.lean` and every
proof that mentions the gate, in a commit whose subject is retiring a
*verification* tier.  They stay as reviewed code behind one accessor,
which is also the single place a future lane would turn them back on.
Their removal is a kernel change and belongs in its own commit.

**`Setlec/TTVerify/DESIGN.md` is kept, code deleted.**  Its §0 and §25
are the project's house practices, declared binding by this file, and
twenty-two references across the tree cite its sections by number.  A
tombstone header says the code is gone and the paths in the prose are
citations.  *Deleting a lane's code does not delete what building it
taught.*

**Battery:** build warning-free (279 jobs, from 424 before T7),
`lake test`, arena 90/92, e2e 72/72, split 11/11, mode flags **9/9**
(the two `--tt-model` cases became one hard-error case), no-model sweep
as expected; the tt-model sweep left the battery with the mode.  Zero
sorries; the fourteen `*_R` unchanged at
`[propext, Classical.choice, Quot.sound]`.

# Task #151 tier C — the cert-tax lane (phase 2, first seal)

## The certificate-cost decomposition at `--set-model` (data in `_tmp/certprof-151/`)

The #141 stack (`instrumentation.patch`, rebased over the T7/T7b tree,
never landed) re-run on the lane the user pays — `--set-model`, not
the retired infer-only lane.  `perf stat` instructions:u; verdicts
identical in every masked configuration (all accept, same counts).
Families: 0 iota recursor telescope, 1 iota constructor telescope,
2 per-redex beta argument re-check, 8 `projCert`, 9 iota comparand
lists, 11 the per-argument application check (masking 11 skips it
*everywhere*, front door included — those runs are measurement
artifacts, never verdicts).

| config | init-prelude (3653 decls) | Std.Time cone (6390 decls) |
|---|---|---|
| baseline `--set-model` | 32.57 G | 1564.9 G |
| mask 0 (iota rec tele) | −1.2 % | −3.2 % |
| mask 1 (iota ctor tele) | −0.26 % | −0.65 % |
| mask 2 (beta) | −8.3 % | −16.1 % |
| mask 8 (projCert) | −0.08 % | — |
| mask 9 (comparands) | −0.16 % | — |
| mask {0,1,2,8,9} — all cert families | **19.00 G (−41.7 %)** | **260.9 G (−83.3 %)** |
| mask 11 too | 11.43 G | 51.4 G |
| `--no-model` | 16.04 G | (run aborted, exit 3 — unmeasured) |

Readings.  (a) The tax on init-prelude is 16.5 G = 50.8 % of the
verified run; the five certificate families jointly are 82 % of it,
wildly superadditive over the singles (2.7 G summed) — certified
reducts feed later certificates, the #141 amplification reproduced on
this lane and stronger.  (b) On the recursor-heavy Std.Time cone the
five families are **five-sixths of the entire verified run**.  (c) The
internal per-argument application share ≈ (mask-families) −
(`--no-model`) ≈ 3.0 G ≈ 9 % on init-prelude; the front-door share
(≈ `--no-model` − mask-all ≈ 4.6 G) is official-shared, not tax.
(d) Post-#100 every family runs *unconditionally* (the #49/#71
possibly-Prop gates are unsound-to-model under the domain-relative
collapse — `CoreI.lean:1613,1666`), which is exactly what the
collapse-free two-regime semantics re-justifies: under `piR`/`lamR`,
positive-regime members **are** graphs and `piR_dom_unique` carries no
side condition, so the #49 domain-determination argument returns,
strengthened, at every annotated slot.

## The I7 amendment, landed (steps 1–2 of the proof chain)

I7 carries the #152 chain-guarded codomain-sort premises,
premise-exact (see the rule's docstring): `μ.verified → ¬b.isLam →`
a `DefEq`-link to the checker's own computed body type `B'`, its
inference, and the sort fact — `B'`/`tB`/`v` unconstrained when the
guard does not fire.  The link premise is the A5 lesson applied:
`HasSort` is not `DefEq`-stable, so the fact is stated at the
checker's own comparand.  Discharged in `infer_lam_claimR` from the
#152 inversion conjunct + `inferSortR`; `checkStepR` stays proved with
no other bridge clause touched.  `Annotates.lam` caches the codomain
numeral through `HasSortC`; `Infer.annotates` is verified-mode with
the `(∃ ea, Annotates) ∧ (isLam → ∃ v, HasSortC)` motive and the
`hasSortC_pi_of` chain induction; `CvalAnnot` gains the λ-shaped-leaf
sort clause (an `EnvS`-shaped obligation, supplier later).  The
`AVExpr` swap is done: `Interp2/Syntax.lean` deleted, `interp2`
dispatches on `Annot/Syntax.lean`'s node, whose `lam` numeral is now
the codomain sort — F4 closed.

## What remains on this lane (the second soundness), stated before starting

The removals consume a soundness of the checker against `interp2`
over annotated derivations.  Its shape is constrained by the recorded
hazards: A2 (annotations do not cross `Red` — the statement follows
checker-computed facts, i.e. it lives at the bridge/claims level, not
as a transport over the bare relation), A4 (kinds thread through
shared inferred types, never read back from memberships), B5″ (a
fibre's universe is not recoverable from the product's — slot sorts
are data).  Rank 1 (iota telescopes, 7–15 %) is the pilot: the `Tele`
premises of R11 must be re-supplied from the stored recursor type's
install-time sort annotations plus the redex's own annotated slots,
after which the two `iotaCertsI` calls go mode-dead with zero new
checks.  Rank 2 (beta, 25–48 %) and rank 3 (internal per-argument,
~9 %) ride the same theorem.

## Tier C carried obligations — the visible ledger

Per the merge review: obligations this lane takes on hypotheses, so
they do not become eleventh-hour surprises.  Suppliers are all
`EnvS`-shaped (install-time facts a future `EnvS` component exposes):

| obligation | where taken | supplier class |
|---|---|---|
| `CvalAnnot` clause 1 — every stored valuation annotates | `Annot/Pass.lean`, since tier A | install-time: valuations are denoted checked terms |
| `CvalAnnot` clause 2 — λ-shaped stored valuations have sorted types | `Annot/Pass.lean`, this seal | front-door `ensureSort` (`Checker.lean:272,380`) |
| `Infer.annotates`/`Tele.annotates` are verified-mode | consumers must hold `μ.verified` | free at `--set-model` |
| `InferFuelDet` — cross-fuel determinism of `inferTypeCore` | `Annot/SimSubst.lean`, `betaCert_discharge`'s explicit hypothesis (v3 seal) | its own seal: fuel-monotonicity of `coreKnot` by oracle-extension induction — clean because `Kernel/Core.lean` has no tryCatch/orElse; NOTE the banked `*_det` lemmas are *same-fuel only*, do not double-count them |

## FINDING (filed, not chased): `--no-model` exits 3 on the Std.Time cone

`_tmp/certprof-151/std-nm-0.*`: `--no-model --pre pre2.ndjson` with
`SETLEC_FUEL=200000` dies at 491.9 G instructions, exit 3, empty
stdout/stderr.  The verified lane accepts the same stream in every
masked configuration.  Task-worthy (a silent internal error in the
parity lane); does not gate this lane.

## The second soundness — architecture, settled before mechanizing

The removals' soundness is **the #49 design resurrected over the
two-regime semantics** — domain determination at provably-positive
slots, a possibly-Prop residue — made sound by exactly what #100's
collapse broke:

* **`AnnotOk2`** (on `AVExpr`, hereditary, semantic — so it transports
  across reduction like `AnnotOkV`, sidestepping A2 for the invariant
  itself): the `AnnotOkV` clauses over `interp2`, with two upgrades —
  the app slot's package `∃ v A B, ⟦f⟧ ∈ piR v A B ∧ ⟦a⟧ ∈ A` carries
  the product **kind**, and the λ clause carries the **fibre package**
  (`∃ B̂, ∀ x ∈ ⟦A⟧, ⟦b⟧(x) ∈ B̂ x` graded by the node's own `v`).
* **The pinning chain**: at a *positive-kind* product a member is a
  graph and graphs determine domains (`mem_piR_pos`,
  `piR_dom_unique` — no side condition), so an app-slot membership
  *pins* the λ/telescope domain even when the **slot's own type is a
  proposition** — what matters is the kind of the *remaining
  telescope*, `imax`-folded, i.e. ultimately the codomain's kind.
* **The residue is codomain-`Prop`, exactly #49's**: at a `Prop`-kind
  product nothing pins the domain (the truth value forgets it), and
  `⟦reduct⟧ = pt` needs the argument membership.  Removals therefore
  land as **O(1) kind gates**, not unconditional deletions:
  – beta: skip the argument re-check when the λ's codomain kind is
    provably nonzero (the #152-computed sort, which must then reach
    the reduction site — mechanism to be priced: stored annotation vs
    recompute);
  – iota telescopes: skip both walks when the **instantiated motive
    sort** is provably nonzero (`Level.isNonZero`, one evaluation per
    fire — the telescope's slot kinds are static in the stored,
    install-sort-checked recursor type).  `Prop`-motive fires keep the
    walks.
* **Graded conclusions**: reduction/defeq interp2-equalities become
  conditional on the subject's `AnnotOk2` (the model's iota equality
  is genuinely membership-conditional — off-domain, the recursor
  value's junk and the rule tower's junk differ), threaded from the
  front door exactly as `AnnotOkV` is today.

Feasibility pilots to mechanize first (B5-style, before any motive is
re-signed): the graded beta step at both product kinds, and the
slot-pinning lemma at a positive-codomain telescope.

## Second soundness, seal 1 — `AnnotOk2` with its metatheory and the graded β step

`Annot/Ok2.lean`: the invariant as architected (kinded app slots, the
λ fibre package at the node's own annotation), its clause equations,
the substitution pair (`AnnotOk2_liftN`/`AnnotOk2_inst` — the
`AnnotOkV` proofs transposed verbatim onto `Interp2/Kit.lean`'s
rewrites; the two upgraded components ride the same congruences), the
β/ζ form `AnnotOk2_inst0`, and the capstone:

    AnnotOk2_beta_pos : v ≠ 0 → AnnotOk2 ρ (.app (.lam v A b) a) →
      ⟦.app (.lam v A b) a⟧ = ⟦b.inst a⟧ ∧ AnnotOk2 ρ (b.inst a)

— **both `RedS2` conjuncts of the β case from the subject's invariant
alone, no argument re-check**, at a provably-positive codomain kind.
The family-2 removal's core theorem, now in full (Pilot's
`graded_beta_pos` was its value-level kernel).  The kind-`0` residue
stands per #49/#73.

## Second soundness, seal 2 — the spine chain and the pinning fold

`Annot/Spine2.lean`, the family-0/1 core theorem set: `SlotChain` (the
subject side — read off the redex's own `AnnotOk2` by
`AnnotOk2_spine_slots`), `PosShape` (the stored-type side — the
telescope value peels in the graph regime; install-time data, the
O(1) motive-kind gate at runtime), `TeleFit2` (the value-level kinded
fit with `fold_mem`), and

    slotChain_fits : f ∈ T → SlotChain f as → PosShape T |as| →
      ∃ T', TeleFit2 T as T' ∧ foldl app f as ∈ T'

— every domain membership of the walk recovered by graph rigidity
(`piR_dom_unique`), `Prop`-typed slots included, since what matters is
the *product's* kind.  `AnnotOk2_redex_fits` packages the composite as
the exact interface seal 3's iota case consumes: subject invariant in,
telescope fit and residual membership out, no runtime walk anywhere.

## Second soundness, seal 3 — FINDING (blocking for rank 1's checker change), the assembly architecture, and the graded ζ step

### FINDING: the rank-1 checker change cannot ride the collapse lane

The plan had rank 1 (the `iotaCertsI` calls behind a
`Level.isNonZero` motive gate at `mode.verified`) executing after the
motive re-signing.  **It cannot land while the twelve consistency
theorems are proved over the collapse interpretation**, and the reason
is mechanizable, not scheduling:

* At a gated-off (positive-motive) fire, the bridge loses the `Tele`
  premises, so `sndRedIota` must recover the fits from the subject's
  invariant.  Over `interp2` that is seal 2's `AnnotOk2_redex_fits`.
* Over the **collapse** lane it is unrecoverable: `AnnotOkV`'s app
  slots are kind-less (`piC` carries no regime index), and
  `piC_dom_unique` needs `f ≠ pt` — which is not dischargeable, since
  `pt` inhabits positive-kind collapsed products whenever the fibres
  contain `pt` and the domain is nonempty (the all-`pt` graph
  collapses), and on empty domains every `lamC` is `pt` (`lamC_empty`,
  the #100 countermodel).  The domain-relative collapse destroys
  domain determination in exactly the cases the gate opens.

**Consequence**: the rank-1 (and rank-2) checker changes gate on
migrating the consistency surface — the twelve `Main.lean` theorems —
from `interp` to `interp2`.  The *measured payoff is already banked*
(`_tmp/certprof-151`: families 0+1 = −1.5 % init-prelude / −3.9 %
Std.Time single-mask, −41.7 % / −83.3 % for the family joint); the
landing is a proof milestone, not a measurement one.

### The assembly architecture: per-step graded lemmas + an annotated environment, no monolithic re-signing

The second soundness does **not** re-sign the 44-case mutual induction
wholesale.  Per A2's resolution (the statement follows
checker-computed facts):

* each reduction step gets a **graded step lemma on `AVExpr`** —
  β (`AnnotOk2_beta_pos`, seal 1), ζ (`AnnotOk2_zeta`, this seal),
  iota (consuming `AnnotOk2_redex_fits` + the stored rule's fired law
  over `interp2`), proj, and the rescues;
* the **environment invariant** (`EnvS2`, the migration's spine)
  stores, per constant, an annotation of its value and type with
  `AnnotOk2`/membership facts over `interp2` — every term the checker
  builds is then assembled from annotated pieces by
  annotation-preserving operations (`AVExpr.inst`/`mkAppN`; the
  metatheory of seal 1);
* the bridge-level claims maintain "the current term erases an
  annotated term carrying `AnnotOk2`" along runs and compose the step
  lemmas — annotations never cross a bare `Red`, they follow the run.

The fired-law premise (`RecRulesV2`) must be **stated by its
supplier** — the T5 install content re-derived over `interp2`
(`EnvS2`, the bottoms, `EqLawV2`, `bval2` towers — `Interp2/Value.lean`
already exists) — not guessed at the consumer; writing it
consumer-side first was the T5 near-miss this campaign should not
repeat.

### Migration roadmap (the remaining seals)

1. `EnvS2` core: the annotated-environment invariant, `CvalAnnot`'s
   two clauses become fields, `mem_type` over `interp2`.
2. The install tier over `interp2` (basis blocks on `bval2`,
   `EqLawV2`, the iota bottoms via seal 2's interfaces — the T5
   transposition recipe, third lane).
3. The soundness tier: the graded step lemmas assembled along the
   bridge claims; the twelve re-proved over `interp2`.
4. **Rank 1 executes** (checker change: `iotaCertsI` behind the
   motive-kind gate, riding `AnnotOk2_redex_fits` + the migrated
   bottoms), measured against `_tmp/certprof-151`.
5. Rank 2 (β behind the #152-sort delivery — the stored-annotation
   vs recompute pricing decision, taken then), rank 3 (internal
   per-argument), rank 4 sweep-up (proj, proof-irrel chains).

## Migration step 1 — `EnvS2` core (`Annot/EnvS2.lean`), and two motive-design walls settled

`EnvS2` lands by **containment** (holds the collapse-lane `EnvS`; its
V-free syntactic fields serve both stacks during the migration — the
scaffolding, not the end state), with the core interp2 fields:
`cval_annot` (the two `CvalAnnot` clauses become environment fields,
closing the carried-obligations ledger's supplier question),
`annot_ok2` (justified valuation annotations are interp2-truthful),
and `mem_type2` (conditional on the type-side annotation — vacuous
where none exists, exact where the consumer holds one).  `RecRulesV2`
deliberately absent until its supplier states it.  `CtxAnn`/`Sat2`
land beside it (the annotated context and its satisfaction, with
`Sat2_nil`/`Sat2_cons`/`CtxAnn.get`), plus `EnvS2.empty`.

**Two walls found shaping the graded motives, both routing to the
run-level formulation A2 already ruled:**

1. *Relation-level `RedS2` cannot produce reduct annotations*: β's
   reduct annotation `ba.inst aa` needs substitution admissibility
   for `Annotates` (each cached `HasSortC` under `inst`), which the
   family lacks by finding A1 — only weakening (M1) exists.
2. *Relation-level `DeqS2` cannot chain without coherence*: two
   justified annotations of one term may differ in their λ numerals
   (A4: no cross-tree coherence), so `interp2`-values of independently
   chosen annotations are not interchangeable without an
   `annot_coherence` theorem (provable only at satisfying `ρ` via
   `sortFact_unique`, and needing uniqueness-of-inference — new
   M-level metatheory).

Both dissolve at the **run level**: the bridge claims thread *one*
annotation per term along a checker run (each term's annotation
produced where the checker's own facts justify it, consumed by the
per-step graded lemmas), so no annotation ever crosses a bare `Red`
and no two annotations of one term ever meet.  The second soundness's
claims are therefore run-indexed (the `WhnfClaims`/`InferClaims`
pattern with interp2-semantic conclusions), not a re-signing of the
relation's mutual induction — the relation remains the bridge's
factoring device for the *checker-shape* content, as designed.

## WALL 3 (**open, escalated**) — defeq-leaf annotation coherence

Shaping `DefEqClaims2` surfaced the migration's crux.  The checker's
definitional equality concludes at a **syntactic** leaf: both sides
reduce to the same `VExpr`.  Under the collapse that closes the
soundness case trivially (`interp` is annotation-free).  Under
`interp2` it does not: the two annotation threads meeting at the leaf
may disagree in their binder numerals, and **numeral disagreement is
semantically real** — `lamR 0 A F = pt` while `lamR v A F` (`v ≠ 0`)
is a graph, so `.lam 0 Aa prf` and `.lam 5 Aa prf` are `AnnotOk2`
annotations of one term with different `interp2` values.  `AnnotOk2`
alone cannot pin numerals (the fibre package is satisfiable at both
regimes for proof-valued bodies), and A4 forbids reading numerals back
from memberships.  This is F4's flexibility biting at the leaf: the
term-directed two-regime interpretation makes syntactic equality
insufficient for semantic equality.

**Resolution space, priced but not chosen** (this is a fork like A5's,
not a call this lane makes silently):

* **R1 — canonical annotations**: define the numeral assignment as a
  *function* of (env, context types, term) — the sort the checker's
  own deterministic computation (#152's) would produce — and make the
  threading invariant "the annotation is the canonical one".  Two
  threads at one leaf then agree definitionally.  The cost is the
  stability metatheorem: canonicity must survive the checker's own
  substitutions and reductions (sort-level substitution stability — a
  sort-fragment of subject reduction, much weaker than the full
  metatheory the annotation design avoids, but new).
* **R2 — recompute at the leaf**: a runtime sort computation per
  defeq leaf re-synchronizes the numerals.  Anti-goal: it re-taxes
  the hot path the campaign is removing.
* **R3 — uniqueness-of-inference + justification threading**: pin
  numerals derivationally (`sortFact_unique_of_conv` at satisfying
  `ρ`); needs inference uniqueness up to `DefEq` (syntax-directed,
  but I8's conversion slack needs Π-injectivity-up-to-`DefEq`) *and*
  justification surviving reduction, which wall 1 blocks.  Likely
  subsumed by R1.

The groundwork landed this seal is resolution-independent: the
threading currency's congruences (`ZetaEq.liftN`/`ZetaEq.inst`, the
`SubstAlgebra` commutations at the ζ cases) and the β residue
companion (`AnnotOk2_beta_zero` — kind-0 β with the retained check's
membership fact).  The `Claims2` definitions are deliberately **not**
landed: their shape is exactly what the fork decides.

## R1 taken — canonical annotations; `denote2` lands (WALL 3's resolution, part 1)

The fork was decided R1 (coordinator's call from the standing rulings,
user override open): R2 re-taxes the hot path, R3 is blocked by wall 1
and needs the Π-injectivity route; R1 makes coherence the determinism
of a computation the checker already embodies, over **ground
numerals** (levels are ground `Nat`s throughout TT — the sort-level
stability fragment stays first-order where full SR is refuted).

`Annot/Canon.lean`: **`denote2`** — `denote` fused with the checker's
own sort computation (`sortOfE` = infer, whnf to a sort, evaluate;
`lamSortE` = the #152 fact per node), constant leaves from the
canonical annotated valuation `acval` (fixed at install, `EnvS2`-side),
literal spines annotated (`natLitT2`/`charListT2`).  A metatheory-level
function — the #100-stage-6 annotate pass resurrected proof-side, zero
runtime cost — so **coherence is definitional**: two threads at one
(env, depth, term) carry the same numerals because there is one
function value.

Next seal, alone (the load-bearing piece): the **erasure law**
(`denote2` erases to `denote` under the valuation link — mechanical;
note the functional-induction gotcha: match-style clause bodies split
`denote2.induct` into ~37 branch-conditioned cases, do-style keeps 15
with `Option.bind` unfolds; pick one and stick to it) and the
**stability metatheorem** — canonicity survives the checker's own
substitutions and reductions.  STOP condition stands: a genuine
instability counterexample is a design finding, not a proof gap.

## R1 part 2 — the erasure law

`denote2_erase` (`Annot/Canon.lean`): a successful canonical
annotation erases to the denotation, **exactly** — no ζ slack, since
`denote2`'s `letE` clause is structural — under the valuation link
(`∀ n ψ, (acval n ψ).erase = cval n ψ`, an `EnvS2`-shaped fact).
Proved by `denote2.induct` over the do-style clauses (15 cases; the
style decision recorded last seal held up — the two friction points
worth keeping: a do-bind that must be `rw`-穿 needs a defeq `replace`
cast, and the catch-all clause's equation only fires through
`denote2.eq_def`).  With coherence (definitional) and erasure (this
law), the canonical annotation is a genuine annotation-valued section
of `denote`; what remains of R1 is **stability alone**.

## The stability metatheorem — the semantic backbone, the decomposition, and a cost-structure FINDING (escalated)

**The backbone** (user exchange, folded in as instructed): every rule
the checker fires — iota, eta, β, proof-irrelevance, every defeq step
— is an equation at a **single common carrier** `T`: same carrier,
same sort.  For ground monomorphized levels `Sort u ≡ Sort v` iff
`u = v`, so **sorts are genuine invariants of defeq classes even
though type shapes are not**.  ("Modeled rules only relate data" is
false — large elimination makes the carrier itself `Type u` — but
"same-sorted on both sides, always" is a theorem of the rule format,
needs no install check, and survives large elimination.)  Mechanized
kernel: `sort_rigid` (`Annot/Kinding.lean`) — definitionally equal
sorts are equal at any satisfying valuation, one line over
`sortFact_unique`.  This is also the data-vs-`Prop` division of labor
of the regime split: rigidity at positive kinds replaces
Π-injectivity; `Prop` keeps its walks.

**The decomposition, worked to its base.**  Stability =
"`denote2` commutes with the checker's β-substitution at the
numerals": for each interior λ, the sort computed on the opened body
equals the sort computed on the substituted body.  Working the chain:

1. sorts of `DefEq` types are equal (`sort_rigid` — done);
2. the two computed types are `DefEq` — needs **M2**, substitution
   for the relation family, up-to-`DefEq`, mutual over
   `Red`/`Infer`/`DefEq`/`Tele`/`DefEqL` (M1/`Weaken.lean` is the
   template; `InstCtx` and its lookup lemmas already exist in
   `Verify/Denote/HasTypeSubst.lean`; the up-to-`DefEq` conclusion is
   what dodges finding A1 — no `HasSort` crosses anything);
3. linking the substituted run's own inference to M2's output needs
   **uniqueness of inference up to `DefEq`** — whose I8 case needs
   **Π-injectivity up to `DefEq`**, which the relation does not have
   and whose semantic form the B5 record refutes at `Prop`.

**The FINDING**: the relation-level route to stability costs
M2 + UoI + Π-injectivity — the third being exactly the ground the
campaign's records mark as hostile.  The **run-level route** avoids
all three: uniqueness of inference is *determinism of the checker's
own function* (free), and stability becomes a substitution
**simulation over the checker's functions** — `inferTypeCore`/`whnf`
outputs on substitution-related inputs are `DefEq`, with the sort leg
closed by `sort_rigid` and the carrier backbone.  This is
Bridge-scale mechanization (a mutual induction over the knot,
`checkStepR`-shaped), with no refutation expected: determinism plus
ground levels plus same-carrier leave nowhere for a sort to move.

The triangle that forces this (recorded so nobody re-walks it):
descended annotations lose coherence at defeq leaves (WALL 3);
canonical annotations need stability; stability at the relation level
needs Π-injectivity.  Canonical + run-level simulation is the unique
consistent corner.

**Escalation**: the stability seal therefore lands in two parts —
this analysis (with `sort_rigid`) now, and the simulation campaign as
the next arc, sized like a bridge tier, to be resourced knowingly
rather than discovered mid-proof.  No instability counterexample
exists or is expected; the STOP condition was tripped by *cost
structure*, not by refutation.

## The simulation arc, opened — the STATEMENT seal (constraint 1)

`Annot/SimSubst.lean`: the determinism lemmas (stated early per the
arc's third constraint — trivial, load-bearing: every UoI the
relation-level route needed is a rewrite here) and
**`SortSubstStable`**, the arc's target, consumer-exact and
trap-tested before any induction:

* *fuel* — defused by hypothesizing both computations' successes at
  one fuel (no monotonicity consumed);
* *branch divergence* — the conclusion is numeral equality through
  the relation's `DefEq` join, never an output-image equation;
* *unsatisfiable contexts* — **the quantifier decision**: the
  conclusion holds under `Sat V Δv ρ` only, because the consumer
  (`Claims2`) is semantic and the relation deliberately has no
  confluence theorem — `sort_rigid` closes the sort leg exactly
  there;
* *the named proof risk* — the case work must keep both sides
  run-backed; comparing a synthetic substituted derivation to the
  substituted run is uniqueness-of-inference ground, and reaching for
  it is the arc's STOP condition.

The statement quantifies the β site's own run facts (the argument's
infer + defeq — the cert every β site has), the bridge-standard
syntactic guards, and the context correspondence.  Sealed alone for
review before the induction (knot-natural boundaries per the
`checkStepR` decomposition follow).

### The β-premise refinement — theorems consume facts; removals change suppliers

Post-seal review caught a supplier problem in the statement above: the
β premise as sealed was the **run cert itself** — `inferTypeCore` on
the argument plus `isDefEqCore` against the domain — which is
precisely the pair of walks **rank 2 removes**.  The user's question:
is that circular?  Answer: no, because the campaign is two-phase
(migration proves the twelve for the *current* checker, whose runs
contain the certs; removal re-proves the gated cases with the
invariant as supplier) — but phase two would have needed a *variant*
of the theorem with a different premise, i.e. the statement was
supplier-committed.

**The refinement** (before any case work baked it in):
`SortSubstStable`'s β premise is now the run cert's *semantic
content* —

> the argument's interpretation is a member of the domain's
> interpretation at satisfying valuations of the context
> (`∀ ρ, Sat V Δv ρ → interp V ρ av ∈ˢ interp V ρ tyv`)

— and the run cert is demoted to **one discharge lemma**,
`betaCert_discharge`: run facts + claims (`InferClaimsR`,
`DefEqClaimsR`) bridge to derivations, `Infer.sound`/`DefEq.sound`
sound them, and the membership transports along the `DefEq`
interpretation-equality chain.  Today's consumer composes the lemma in
front of the theorem and is unaffected; the post-removal consumer
discharges the same premise from the invariant's slot package
(`AnnotOk2_redex_fits`'s per-slot membership at positive kind,
`AnnotOk2`'s app clause at kind 0).  One theorem serves both phases;
the supplier swaps under it.

This is the clean statement of the whole removal architecture, worth
recording once at full generality: **theorems consume facts, not the
walks that produced them; a removal never changes a theorem, it
changes the supplier of a premise.**  Every rank of the roadmap is an
instance — rank 1 swaps the iota telescope certs for `PosShape` +
`slotChain_fits`, rank 2 swaps the β cert for the slot package, rank 3
swaps the per-arg check for the spine chain.  Stating premises
semantically (Sat-conditioned membership/equality, never
`.ok`-equations of the walks slated for removal) is what makes the
swap a local re-proof of a discharge lemma instead of a re-statement
of the metatheorem.

### REFUTATION: the membership form of the β premise is too weak (whnfCore-branch pre-work STOP)

Sealed one grant later, before any induction case work, tracing the
paired induction's leaf against the refined premise refuted the
*specific semantic form* chosen above.  The principle stands; the
currency was wrong.

**Where the premise is consumed.**  `lamSortE` is *two* chained infer
runs: `infer(body) = bt`, then `sortOfE(bt)` = `infer(bt) = t`,
`whnf(t) = .sort ℓ`.  The paired induction walks the first infer on
inst-image subjects.  At the substituted `fvar d` leaf, side 1's
inferred type is the annotation `ty` itself (`inferBody`'s `.fvar`
clause returns it verbatim) and side 2's is `ta` — the checker's own
inferred type of the argument.  Every downstream fact — including the
*second* infer, which computes the sort **of** these types — flows
from that pair.  So the leaf needs the two *types* linked:

> `∀ ρ, Sat V Δv ρ → interp V ρ ⟦ta⟧ = interp V ρ ⟦ty⟧`

— interp-**equality of the argument's inferred type with the domain**.
That is the run cert's full semantic content (`DefEqClaimsR` +
`DefEq.sound` give exactly it).  The membership
`interp av ∈ˢ interp tyv` is what `betaCert_discharge` *derived from*
that equality and then discarded — strictly weaker.

**The countermodel (the gap is real, not proof-technical).**  Take
`body = bvar 0`, so the two `lamSortE` subjects are `fvar d n ty` and
`a` themselves.  Let `ty` be a unit-like inductive pinned at `Type 1`
and `a` an inhabitant of a unit-like at `Prop` (or `Nat` vs a
`Type 1` ℕ-clone).  If the model gives the two carriers the same set —
unit-likes at any sort plausibly all model as `{pt}`, and the
inductive carrier construction is sort-blind — then the membership
premise holds (`pt ∈ˢ {pt}` at every valuation, closed context, `Sat`
trivial), both runs succeed, and the conclusion fails:
side 1 computes `sortOfE(ty) = 2`, side 2 `sortOfE(ta) = 0`.
Cumulativity is the root cause: membership in a type pins the
element, never the type's sort — `HasSort.mem_univ`'s own recorded
caveat, now biting the premise itself.  (Not mechanized; realizes
against the `SetTheory` interface given any instance whose unit-like
installs share the carrier.  Mechanization would be parametric in `V`
via the unit-like install lemmas if the coordinator wants it banked.)

**Why the run-fact form was never circular-in-danger here**: with the
original premise the leaf is discharged by bridging the cert itself;
the induction never re-derives it.  The refinement's *goal* (supplier
neutrality) is right; the *currency* must be the type-level equality.

**Proposed corrected premise** (semantic, supplier-swappable,
leaf-exact):

    ∀ (fuel' : Nat) {ta : Expr}, inferTypeCore μ env fuel' d a = .ok ta →
      ∀ {tav}, denote mS.cval env φ d ta = some tav →
        ∀ ρ, Sat V Δv ρ → interp V ρ tav = interp V ρ tyv

quantified over **all** fuels so the induction's occurrence-walks (the
substituted `a` is re-inferred wherever the walk meets it, at varying
remaining fuel) consume it directly; the fuel-linking burden then
lives in the *discharge lemma* (one standard fuel-determinism lemma
for `inferTypeCore`, proved once), not in the metatheorem.  Phase-one
discharge: `DefEqClaimsR` + `DefEq.sound` + fuel-determinism —
*simpler* than the membership chain.  Occurrences at deeper depths
link by a depth-irrelevance lemma for `WScoped d` subjects (standard;
to be proved with the leaf case).

**The phase-two blade (design fork, flagged not solved).**  The
`AnnotOk2` app slot carries memberships only (`⟦f⟧ ∈ piR v A B ∧
⟦a⟧ ∈ A`).  By the countermodel, *no* membership package can supply
the corrected premise — post-removal the slot must carry the
domain-fit as a type-level equality fact (e.g. the primary typing
walk's `defeq(ta, dom)` verdict, threaded to the redex as an interp
equality), or rank 2's removal has no supplier for the β premise at
all.  This is a finding about the rank-2 design, discovered two seals
early — exactly what stating the premise before the case work was
for.

### The ruling, and the coordinator's record (verbatim, as directed)

> "My directive gave you the wrong currency and your trap discipline
> caught it before a single case consumed it — that sequence,
> directive included, belongs in the DESIGN record verbatim."

And the rule the episode produced, recorded at full generality: **when
a discharge lemma discards a stronger fact to satisfy a premise, the
premise is under-stated — check what the supplier naturally
produces.**  (`betaCert_discharge` derived the type-level equality
from `DefEq.sound` and threw it away to conclude the membership; the
supplier's natural product was the run verdict itself, and each
weakening below it loses something the induction needs.)

### SECOND REFUTATION: the corrected (interp-equality) premise falls to the SAME countermodel

Executing the adopted correction, the base-case trace (`body =
bvar 0`, where the conclusion demands `sortOfE(ty) = sortOfE(ta)`
outright) refuted it before it reached the statement: **the sealed
finding's own countermodel satisfies the sealed finding's own
proposed fix.**  Unit-likes at `Prop` and `Type 1` with the shared
carrier `{pt}`: `interp ⟦ta⟧ = interp ⟦ty⟧` holds at every valuation
— carriers equal is precisely the countermodel's construction — while
the checker computes sorts `0` vs `2`.  Interp-equality of types is
sort-blind; this is cumulativity one rung up the same ladder.

**The full ladder**, each rung refuted by the one countermodel family
or by architecture:

1. *membership* (`interp av ∈ˢ interp tyv`) — refuted: pins the
   element, not the type (first refutation).
2. *type-level interp equality* (`interp ⟦ta⟧ = interp ⟦tyv⟧`) —
   refuted: pins the carrier, not the sort (this refutation).
3. *relational conversion* (`DefEq Δv ⟦ta⟧ ⟦ty⟧`) — phase-one
   dischargeable (`DefEqClaimsR` bridges the cert), but the leaf
   cannot consume it: linking the sort facts of `DefEq`-related
   subjects is uniqueness-of-inference ground (semantic route dead by
   cumulativity, relational route deliberately absent), and an
   induction over the *derivation* dies at `DefEq.trans` — the middle
   term has no run, hence no sort computation to pair.
4. **the run itself** — the surviving currency.  The defeq *run's
   recursion tree* pairs the two syntaxes step by step, and every
   node of it is run-backed on both sides; it is the only object that
   crosses the cumulativity gap without UoI.

**Premise v3** (proposed; the statement rewrite waits for this
ruling):

    ∀ (fuel' : Nat) {ta : Expr},
      inferTypeCore μ env fuel' d a = .ok ta →
        ∃ fuelc, Setlec.isDefEqCore μ env fuelc d ta ty = .ok true

— *every inferred type of the argument is run-certified convertible
to the domain*.  Run-shaped, and still supplier-swappable, which
dissolves the apparent conflict with the removal architecture: the
FACT is "some certifying run exists", not "the β site performed it".
Phase one supplies the site's own cert (plus fuel-determinism to link
`ta` across fuels); phase two supplies the **primary typing walk's**
app-site defeq — the walk that is never removed, because it is the
typing judgment itself, not a certificate.  The phase-two blade
sharpens accordingly: the slot package must thread *run evidence*
(the primary verdict), not any semantic shadow of it.

**Consequences for the branch plan:**

* The **defeq-branch is load-bearing**, not a no-op: the leaf's
  workhorse is the paired induction over the certifying defeq run —
  "a true defeq run plus sort-computation runs on both arguments
  forces numeral agreement at `Sat`".  That is the arc's remaining
  provability risk, named before case work.
* **Fuel-determinism of the knot** is the phase-one discharge's
  enabler (site cert at one fuel, premise quantifies all fuels).
  Feasibility fact banked: `Setlec/Kernel/Core.lean` contains **no
  tryCatch/orElse anywhere** — the bodies never backtrack through
  errors, so success-monotonicity in fuel is clean and mechanical
  (oracle-extension induction over `coreKnot`).  Sized bridge-batch;
  its own seal.  Until it lands, the discharge lemma takes the
  determinism as an explicit hypothesis (the `CheckStepR` precedent:
  hypothesize the step, prove it in batches).
* Paired positions in the two runs always sit at **identical fuels**
  (the knot decrements per recursion level, never through results),
  so the induction itself never crosses fuels; only the discharge
  does.

### The v3 rewrite, sealed — and the coordinator's second record (verbatim, as directed)

> "Refutation 2 caught YOUR sealed correction, and my review approved
> that correction — the ladder's second rung got past both of us, and
> only the trace-before-statement discipline caught it."

Recorded next to the first, as ruled: neither author review nor
coordinator review caught rung 2; the *mechanical* discipline (trace
the base case before the premise reaches the statement) did.  The
discipline, not the reviewer, is the safeguard.

The rewrite itself (`Annot/SimSubst.lean`): `SortSubstStable` carries
the v3 premise — `∀ fuel' {ta}, inferTypeCore … a = .ok ta →
∃ fuelc, isDefEqCore … ta ty = .ok true`; `betaCert_discharge` became
*purely syntactic* (site cert + `InferFuelDet`, four lines — the
semantic machinery of the refuted discharge chains went with the
rungs it served); `InferFuelDet` is the ledger's new carried
obligation (entry above, with the same-fuel-only caveat on the banked
determinism lemmas and the no-catch feasibility fact).  Next per the
approved order: the mechanized countermodel seal (one family, both
rungs, guarding the final statement), then the induction with the
defeq-branch first as the named load-bearing risk — STOP condition
standing: a defeq rule that certifies across a sort boundary is the
finding of the whole arc.

### The countermodel, banked mechanized (`Annot/PremiseLadder.lean`)

The two dead rungs are now proofs of `False`, parametric in `V`:
`SortSubstStable_mem_refuted` and `SortSubstStable_interpEq_refuted`
(`∀ V [SetTheory V], ¬ rung`), each at exactly the three standard
axioms.  The countermodel got *simpler* than the design sketch — no
custom inductives needed: the pinned basis' own `PUnit` **is** the
sort-blind carrier family.  Its valuation is level-uniform
(`pinnedDirectT`: `cval PUnit ψ = punitT (ψ u)`,
`interp (punitT u) = unitSet` for every `u`), so
`ty := PUnit.{2}`, `a := PUnit.unit.{0}`, `body := .bvar 0` satisfies
both refuted premises at every valuation while the checker computes
`2` vs `0` — and the v3 premise correctly fails
(`defeq(PUnit.{0}, PUnit.{2})` is `false`; equal shadows, no
certifying run).

Mechanization facts worth reusing:

* the env is built by the *actual checker* (`checkDecls` on
  `[.basisDecl .punitK]`) and its model by the *actual acceptance
  theorem* (`checkDecls_sound_R`) — the refutation exercises the real
  pipeline end to end;
* one decided probe carries every env-dependent fact; checker runs
  evaluate in the kernel via **`decide +kernel`** — plain `decide`
  stalls because `whnfLoopFuel` is `@[irreducible]` and the
  elaborator respects reducibility while the kernel does not (a
  standing gotcha for any future in-proof evaluation of `whnf`-path
  functions);
* WF-recursive `Bool`/`List` helpers (`wscopedB`, `fvarLeaves`) do
  not reduce definitionally — evaluate them by `simp` with their
  equation lemmas, not `decide`;
* the rung statements are verbatim mirrors of the sealed
  `SortSubstStable` with only the premise swapped — if the
  statement's shape ever changes, re-sync them or the guard guards
  nothing.

## The defeq-branch, opened — the claim-family STATEMENT seal

`Annot/SortCoh.lean`: run-level sort coherence, the arc's load-bearing
branch, stated alone and trap-tested before any case work (the
discipline that has now caught three premise defects in this arc).
Four claims — **(A)** `EnsureSortAgreeR` (certified pair, both whnf to
literal sorts, numerals equal), **(B)** `SortOfAgreeR` (the target:
certified pair, both `sortOfE` runs succeed, numerals equal — the
exact shape `SortSubstStable`'s leaf consumes on the `ta`/`ty` pair),
**(C)** `SortOfWhnfCoreStableR` (one-sided: sort of the type survives
a whnfCore step), **(C-δ)** `SortOfDeltaStableR` (survives one
unfolding) — plus `KnotFuelDet` (the ledger obligation, knot-wide
form) and `PairedLeaves` (the ambient one-annotation-per-index
discipline, syntactic).

**The centerpiece: valuation-freedom.**  The claims never mention
`V`/`interp`/`Sat`.  The relation needed `Sat`-conditioning because it
has no confluence theorem; the runs have no such freedom — the checker
certifies `.sort u ≡ .sort v` only through the ground level
comparison.  Run-level sort coherence is syntax + arithmetic.  This
also dissolves the empty-domain binder problem that would have sunk a
`Sat`-conditioned induction at `pi`-congruence descents (no satisfying
valuation of an empty domain, yet inner numerals feed outer `imax`es):
with no valuation anywhere, binder descent is free.

**The case map of `defeqStep`** (trap-test evidence; every certifying
path classified):

| path | class | supplier |
|---|---|---|
| syntactic `a == b` | live | `KnotFuelDet` (same syntax, two fuels) |
| post-whnfCore `a' == b'` | live | (C) both sides + `KnotFuelDet` |
| `proofIrrel` | vacuous | subject's type is `Prop`-sorted, so it cannot whnf to a literal sort (`ℓ+1 = 0` impossible); vacuity crosses fuel scales → `KnotFuelDet` |
| `reduceNat` re-entry | vacuous-or-(C) | subjects are `Nat` elements (type `Nat` is not a sort); the re-entry itself rides (C) |
| lazy-delta one-sided/both | live | (C-δ) + loop IH |
| `defeqSpine` same-head | live | **the app/spine unknown** (below) |
| `.sort`/`.sort` level compare | live, the base | ground `isEquiv → eval` lemma |
| literal cases (nat/str/ctor) | vacuous | element-level subjects |
| `fvar i == fvar j`, `i = j` | live | `PairedLeaves` (annotations identical) → same computation, `KnotFuelDet`; inside descents, the Θ motive + (A) on the annotation pair |
| `forallE` congruence | live, the main case | (B) on the domain pair (sub-cert at `f-1`) + (B) on the opened-body pair (`infer`'s ∀ clause computes `.sort (.imax u v)` from exactly (B)-shaped sub-facts) |
| `lam` congruence | vacuous | subject's type is a Π, not a sort |
| app/app stuck congruence | live | **the app/spine unknown** |
| proj/proj stuck congruence | live | **the proj unknown** |
| eta (one-sided λ) | vacuous | function subjects |
| `stuckIrrel` fallbacks (K/unit/struct-eta) | vacuous | element/proof subjects |

**The Θ motive** (internal to the induction; the statement exposes
only `PairedLeaves`): congruence descent opens with *each side's own*
domain, so the paired zone's indices map to annotation *pairs*.  The
motive carries, per opened index: the pair, its certifying sub-run
(the domain premise, a call at knot fuel `f-1`), and the
induction-grade agreement fact — extended at every descent from the
domain IH.  Well-founded lexicographically on (knot fuel, lazy-delta
loop budget); the domain cert is one knot level down, so the
extension is IH-fed, never circular.

**The mutual knot is real, as granted**: (C)'s β case is
`SortSubstStable`-shaped (redex type vs substituted-body type — the
whnfCore branch is where the substitution simulation re-enters), and
`SortSubstStable`'s leaf is (B) — one mutual induction, three
branches, sealed at knot-natural boundaries.

**Named unknowns, graded** (to be attacked in this order, each its
own seal, STOP with the case if one genuinely fails):

1. *app/spine congruence* (defeqSpine + stuck app/app): `sortOfE` of
   a stuck application destructures `whnf(infer f)` into a Π and
   returns `B.inst a`-shaped types; pairing the two sides needs a
   run-level type-join for the certified heads.  Same-const heads
   with eval-equal levels (defeqSpine) share one declared type, which
   should pin the pairing; the general app/app case is the branch's
   hardest and may need a further claim (run-level "certified
   subjects' inferred types are certifiable") — if so, that claim
   gets its own statement seal before any case consumes it.
2. *delta install-threading* (C-δ): the unfolding's sort agreement
   rides the install-time cert (`checkDecl` ran `infer(value)` +
   `defeq(tv, ty)` when the definition entered the env); needs an
   env-level invariant field exposing that run fact (EnvWF-adjacent,
   V-free) — an install-tier addition, designed when (C-δ) is
   attacked.
3. *proj congruence*: projection types via `piResidual` peeling;
   expected to follow the app pattern.

**Anticipated `SortSubstStable` amendment** (recorded now, applied
when its leaf case lands): its guard set carries `CtxOkR` (denoted
discipline) but the leaf's (B) instance needs the *syntactic*
discipline (`PairedLeaves ta ty`), which the consumer has because a
walk opens each index once (`Expr.LeafCond` shape).  A
`PairedLeaves`-style hypothesis will be added to the statement at
that seal — flagged here so it does not arrive as a surprise.

**Retired**: the "identical fuels" lemma idea — every run is
quantified at its own fuel and all same-syntax links go through
`KnotFuelDet`, so no fuel alignment discipline is needed anywhere.

### Defeq-branch, seal 2: the ceiling induction + base ingredients (and two case-map corrections)

**Case-map corrections** (from reading the fallbacks' actual runs —
the map's `proofIrrel` row was wrong twice over):

* `proofIrrel` has **two** certifying branches.  The *unit-like*
  branch (both types whnf to a unit-like constant) is vacuous via
  `KnotFuelDet` alone: the sort run's `whnf(ta) = .sort ℓ` and the
  cert run's unit-like output are one output, and `.sort` is not
  const-headed (`unitBranch_absurd`, landed).  The *Prop-sorted*
  branch runs **no defeq sub-run between the two types** — it only
  checks each side's type-of-type is `Sort 0` — so there is nothing
  to hand an (A)-style IH.  It closes by vacuity through **(C\*)**:
  a subject whose type both whnfs to a literal sort and is
  `Prop`-sorted contradicts its own whnf chain (`sortOfE` of
  `.sort ℓ` is `eval ℓ + 1 ≥ 1`, but the cert run computes `0` for
  the same chain).  (C\*) — whole-`whnf`-chain sort stability — is
  therefore promoted to a first-class family member
  (`SortOfWhnfStableAt`); the same routing serves the K/unit/
  struct-eta rescue fallbacks, whose certifying runs also whnf the
  subjects' types to non-sort shapes.
* Consequence for supplier order: the "vacuous" rows are *not* below
  the base — they sit above (C)/(C-δ)/(C\*).  The truly standalone
  base is: the level lemma (`Level.isEquiv_sound`, banked), the
  syntactic cases (`sortOfE_fuelDet`), and the sort-sort arithmetic
  (`sortOfE_sort_out`).

**The ceiling induction** (the well-foundedness discovery, resolved
before any case consumed a broken measure): the claims reference each
other at **unrelated fuels** — a `(B)` instance about a cert at fuel 3
may consume `(C*)` facts about sort runs at fuel 10⁶, so no single
run's fuel can carry the mutual induction.  The measure is the
**ceiling** `N` bounding *every* quantified run fuel
(`SortCohAt μ env φ N`, a five-field Prop structure), under strong
induction on `N`: cross-claim consumptions are about sub-runs at
strictly smaller fuels (the knot decrements per level) and drop the
ceiling; lazy-delta/whnf **loop** re-entries keep every fuel and
decrease only the loop budget — the loop-internal motive
(`defeqLoop`/`whnfLoop`-level claims, lexicographically inside the
ceiling) is the next design piece, to be built with the first
congruence case.  The public claims are the `∀ N` closures
(`*_of_at`).  This subsumes and replaces the earlier "lexicographic
(knot fuel, loop budget)" sketch, which was measured against a single
run and would not have covered the cross-claim fuel independence.

**Landed ingredients** (`Annot/SortCoh.lean`): the ceilinged family +
bundle + closures; `sortOfE_fuelDet` (cross-fuel determinism of the
sort computation, `KnotFuelDet`-powered); `inferTypeCore_sort_out` /
`whnf_sort_out` / `sortOfE_sort_out` (the sort-sort base's run
equations and arithmetic); `unitBranch_absurd` (the unit-like vacuity
pattern, the template for the rescue fallbacks' cases).

### STOP: the ceiling measure fails the reference-graph check (defeq-branch wall)

Assembling the loop-internal motive, the first act was to re-derive
every cross-claim consumption against the ceiling measure before
writing a case.  Two holes, the second fatal to the measure as sealed:

1. **(B) → (C-family) keeps the ceiling.**  The post-whnfCore case of
   (B) consumes a (C)-instance at `(fc−1, f₁, f₂)`: the cert
   component drops but the *sort runs are passed through unchanged*,
   and when they dominate the max, the consumed instance's ceiling
   equals `N`.  The sealed justification ("cross-claim consumptions
   drop the ceiling") is wrong for every arrow that forwards the sort
   runs.  On its own this might be repairable by ordering the claims
   within a ceiling (the cycle `(B)→(C)→(B)` composes to a strict
   drop) — but:
2. **(C\*) must manufacture intermediate runs, at unbounded fuels.**
   Composing (C) along a whnf chain needs `sortOfE` runs on the
   *intermediate* reducts — and nothing ran them.  Exhibiting one is
   a success-construction whose fuel is built, not bounded: a
   constructed fuel can exceed **any** ceiling, so the consumed
   instance sits *above* `N`.  No max-based (nor sum-based — same
   hole) measure over hypothesized fuels survives manufactured runs.

**The regress that forced the issue** (why (C\*) cannot be dodged):
the `proofIrrel` Prop-branch vacuity needs "`SP` whnfs to a literal
sort" to contradict "`SP` is `Prop`-sorted" — but linking
`infer(SP)` across `SP`'s reduction is (C\*) again, one level up
(`ta` → `SP` → …).  The discharge never bottoms out at run facts
alone; it needs either reduction-transport of the sort computation or
the model.

**Repair space** (for the ruling; no case work until the measure is
re-sealed):

* **R1 — ∃-fuel runs + distinguished-run induction.**  Restate the
  family over fuel-free run predicates (`∃ f, run f = .ok x` —
  functional by `KnotFuelDet`), and induct per claim on its one
  *distinguished* run (the cert for (A)/(B); the reduction run for
  the C-family; the walk pair for the infer-branch), consuming other
  facts only as ∃-fuel side facts or via IHs on subtrees of the
  distinguished run.  Fuel arithmetic disappears into ∃.
* **R2 — semantic routing for the vacuities.**  Keep dual-success
  claims; discharge the proofIrrel/rescue vacuities through the
  existing twelve's claims + model (`univ`-regularity).  Cost: the
  claims become `EnvS`-conditioned — the V-freedom centerpiece is
  lost, and the statements change shape.
* **R3 (recommended) — the forward-transport claim species.**  Keep
  the V-free dual-success claims; add the missing species: **(F)**
  one-step *success transport* — a reduction step plus a successful
  sort computation on the redex yields an ∃-fuel successful sort
  computation on the reduct *with the same numeral* (β's instance is
  the constructive form of the substitution pairing; δ's threads the
  install cert).  (C\*) then iterates (F) forward and closes against
  the given endpoint run by `sortOfE_fuelDet` — no manufactured
  ceilings, no model.  The measure re-check under R3 (does every
  arrow now drop a distinguished-run measure?) is the re-seal's first
  obligation, per the escalation rule: the new claim species gets its
  own statement seal before any case consumes it.

The sealed `SortCohAt` definitions stay (they are the dual-success
claims R3 keeps); what is withdrawn is the ceiling induction's
*justification* and the plan to assemble the shell on it.

### The audit under R3 — the measure re-check PASSES, on a four-stratum design

R3 executed (`Annot/SortCoh.lean`: `SortOfEE`/`DefEqE` ∃-fuel facts,
`SortOfEE_det`, and the (F) species `SortTransportWhnfCoreF` /
`SortTransportDeltaF` / `SortTransportNatF`, with `SortTransportWhnfF`
as the (C\*-E) chain form).  The first obligation — every arrow drops
a distinguished-run measure — was re-derived from scratch, and it
**passes**, because of two facts found during the re-check:

**Keystone 1: (A) is standalone — stratum S0.**  (A)'s
whnf-to-literal-sort hypotheses never need (F): a whnf run
*self-decomposes* along its own loop (`whnfLoop l e = .ok s` with the
first step known gives `∃ l' < l`, a loop run on the intermediate — a
subtree, pure run-algebra), and cross-fuel `KnotFuelDet` aligns the
cert loop's own `whnfCore` outputs with the given runs' first steps.
Better: (A)'s *structural* stuck cases are vacuous by determinism —
a stuck pi/app/fvar whnfs to itself, and the given run says it whnfs
to a literal sort; the two outputs are one output.  So (A)'s live
endgame is only syntactic / sort-sort (the ground level lemma) / the
descent cases, and its induction is (cert fuel, cert-loop budget)
with no cross-claim arrow at all.

**Keystone 2: the constructive pairing needs no leaf-(B).**  In
(F-core)'s β case the substituted walk is *built* by structural
induction on the given opened walk, and the correspondence between
the two walks' output types travels as **cert runs** (`DefEqE`), not
as sort agreements: at the spliced-argument leaf the built walk's
piece is the site's own `infer(a) = ta` run and the correspondence
cert is the β cert itself — exactly the v3 premise's two components.
Only at the *top* of the construction is the numeral read off, via
(A) applied to the constructed correspondence cert — a downward
arrow into S0, where constructed instances cost nothing because S0
is already a ∀-quantified theorem.

**The strata** (each claim inducts on its own distinguished run;
cross-claim arrows go only downward to proven strata, so constructed
instances never meet a measure):

* **S0 — (A)** `EnsureSortAgreeR/At`: cert-loop induction; run
  algebra + `KnotFuelDet` + `Level.isEquiv_sound`; no cross-claim
  arrows.
* **S1 — the (F) species**: per-step structural inductions.  (F-core)
  β = the constructive pairing (consumes S0 + the site cert pieces);
  ι/proj/ζ analogous with their own cert threads; (F-δ) consumes the
  install cert (env-invariant field to be added) + env-extension run
  stability; (F-nat) vacuous.  Same-claim descent only on subtrees.
* **S2 — (C\*-E)** `SortTransportWhnfF`: `whnf`-loop induction
  consuming S1 as theorems; the old dual-success (C)/(C-δ)/(C\*)
  forms become corollaries (S1/S2 + `SortOfEE_det`).
* **S3 — (B)** `SortOfAgreeR`: cert-loop induction on (cert fuel,
  loop budget) *only* — the sort facts are ∃-fuel, so the measure
  crisis dissolves: loop re-entries after transport drop the budget
  regardless of constructed witness sizes (witnesses are consumed
  solely by `SortOfEE_det`-style lemmas and terminal cases, never by
  induction); sub-certs drop the cert fuel; every other arrow goes
  down to S0–S2.

The old holes, re-examined by name: hole 1 ((B)→(C-family) keeping
the ceiling) is gone because S0–S2 are theorems before S3 starts,
not mutual claims; hole 2 (manufactured intermediates above any
ceiling) is gone because ∃-fuel facts carry no fuel into any measure
and transports *produce* them rather than demand them.  The
`proofIrrel` regress discharges in S3 via S2 on the cert-side chain
(both endpoint facts exist — the cert run supplies `sortOfE`-shaped
pieces, the literal-sort endpoint is constructible at explicit fuel).

**Lineage** (as ruled): (F) is where the campaign's original
prognosis — "a narrow, level-data-only fragment of subject
reduction, far weaker than the metatheory the design avoids" — gets
its precise formal identity.  The arc circled it three times (the
currency ladder's run rung, the (C\*) promotion, the measure
refutation) before it landed as a statement; each circling narrowed
it, and what remains is exactly level data: one step, one numeral,
carried forward.

**Enabling obligations joining the ledger** (each its own seal, all
V-free): (E) env-extension run stability (a run over a prefix env
reproduces over the extended env — append-only, duplicate-checked
`find?`); the install-cert env-invariant field ((F-δ)'s supplier);
`KnotFuelDet` (already entered).

**Attack order from here**: S0 first (it is also where the fvar/Θ and
pi-congruence machinery gets its dry run at the cheapest claim), then
S1 in the order (F-nat) (vacuity template), (F-core) non-β cases,
(F-core).β (the pairing construction — the arc's summit), (F-δ)
(after (E) + the install field), then S2 (mechanical), then S3.

### STOP: Keystone 1 overclaimed — the hoisted probe re-entangles (A) with transport

Opening S0, the first case trace refuted part of the sealed audit.
The det-vacuity argument for (A)'s stuck cases is sound only for the
*structural endgame* fallbacks, which run on fully-whnf-stuck
subjects (there the subject's own whnf run must end at the stuck form
— determinism — so a non-sort stuck form contradicts the
whnf-to-sort hypothesis).  But **`defeqStep` hoists `proofIrrel`
before lazy delta** (mirroring the official kernel — a probe order,
not a Setlec quirk, and reduction-strategy changes are barred by the
standing ruling): the probe runs on *mid-chain* subjects that may
still delta/nat-step onward to a literal sort.  For those, nothing in
the probe's runs contradicts the whnf-to-sort hypothesis by
determinism alone — the contradiction ("a `Prop`-typed subject
cannot whnf-converge to a literal sort") requires transporting the
probe's own `sortOfE`-shaped facts along the subject's remaining
chain.  That is S2 machinery: **(A) is not standalone; the hoisted
probe is a genuine (A)↔(F) entanglement.**

The vacuity's true content, named: **Prop/Sort separation (PSS)** —
`proofIrrel`-style `Prop`-typing runs and a whnf-to-literal-sort run
on one subject are jointly absurd.  Its discharge is *one-shot* (no
regress): S2-transport the probe's `sortOfE(ta) = 0` along `ta`'s
chain to the literal end, where `sortOfE_sort_out` computes
`eval ℓ + 1` — `0 = eval ℓ + 1` is absurd.  But routed through the
sealed design it is formally circular: (F).β's *top* consumed (A) on
a **constructed** cert, whose own probe case is PSS again, at
unbounded (∃-fuel) components.

**Repair (δ), proposed** — three coupled changes that make the
circle a well-founded joint induction:

1. **Move the cert consumption from the top to the leaves.**  The
   pairing's correspondence invariant carries **constructed
   chain-links** (each corresponding type pair comes with built
   whnf-convergence to same-eval sorts) instead of cert runs; the
   site certs are consumed *immediately at the leaves* via (A)
   instances whose components — the cert's own fuel, the annotation
   chains — are **subtrees of the walk hypotheses**, never
   constructed.
2. **Mutualize J0 = {(A), the (F) species, the chain assembly} in
   one fueled joint induction** with measure = the sum of the
   *fueled hypothesis components*, under a strict **subtree
   discipline**: every fueled component of every consumed instance
   is a subtree of some hypothesis component.  (A)'s probe case
   consumes chain-transport instances at subtree fuels of its own
   `f₁`; (F).β consumes leaf-(A) at subtree components of the walk;
   re-entries drop loop budgets at fixed sums.
3. **∃-fuel is for outputs only.**  Transports still *produce*
   `SortOfEE`/chain-link facts fuel-free (hole 2 stays dissolved —
   produced facts are consumed solely by determinism-style lemmas
   and terminal cases, never inducted into); but every *hypothesis*
   of a J0-internal claim stays fueled so the sum measure is real.

S3 = (B) is unchanged (consumes J0 as theorems).  The strata
S0/S1/S2 collapse into J0 — the summit is bigger than the audit
hoped, but the measure is honest: the previous design's fatal arrows
((F).β's constructed-cert top-read; PSS's ∃-fuel erasure) are both
removed *by construction*, not by measure cleverness.

Sealed as a finding for the ruling before any case work consumes the
corrected design; the (F)/(A) statements as landed are untouched
(repair δ changes proof architecture and the internal claim forms,
not the public statements).

### J0 under repair δ: the internal forms, and the audit that the probe case tried first

For the record, as ruled: **the circle was purely architectural — the
mathematics (one-shot PSS discharge, no regress) was never in
doubt.**

**The forms** (`Annot/SortCoh.lean`): `SortLinkE` — the chain-link
the pairing correspondence carries: *conditional*, one-directional,
∃-fuel-output ("if the left type whnf-converges to a literal sort,
the right does too, same numeral").  Conditional because most
corresponding type pairs in a walk are not sort-convergent at all;
one-directional because the pairing builds side 2 from side 1 and the
top-read goes the same way.  **(A-T)** `SortLinkAcrossCertE` — the
family's true primitive: a certified conversion transports
whnf-to-sort success across itself.  Dual-success (A) is now a
corollary (`EnsureSortAgreeR_of_link`, proved: link the left run
across, collide with the right run by `KnotFuelDet`) — the
statement-level check that (A-T) is stated strong enough.

**The joint measure**: lexicographic on (Σ knot fuels, Σ loop
budgets) of the *fueled hypothesis* runs of an instance.  ∃-fuel
outputs and fuel-free env facts are exempt (never inducted into).

**The audit — probe case first**, as directed (the case that broke
audits one and two):

* **(A-T).probe** (hoisted `proofIrrel`, mid-chain): consumes one
  chain-assembly instance whose fueled hypotheses are (i) the given
  whnf run's *suffix* (same knot component, smaller loop budget) and
  (ii) the probe's own `sortOfE` pieces (subtrees of the cert, knot
  strictly smaller).  Knot-sum strictly drops.  **Passes.**
* (A-T) loop re-entries (post whnfCore/δ/nat): cert budget drops;
  the given run is untouched or decomposed to its own suffix.
  Knot-sum equal, budget-sum drops.  Passes.
* (A-T) structural cases: no congruence descent at all — a stuck
  non-sort form collides with the given run by determinism; the
  eta case collides the probe's whnf-to-∀ with a constructed
  whnf-to-sort on the same expression (the PSS pattern, subtree
  components).  Passes.
* (F-core).β: structural descent on the given walk's tree; the
  leaves consume (A-T) at the site cert + annotation chains — all
  subtrees of walk hypotheses (leaves-not-top, repair δ change 1).
  Knot-sum drops.  Passes.
* (F-core) non-β, (F-nat): cert threads are subtrees of the step
  run or of the `sortOfE` pieces.  Passes.
* **(F-δ)**: the install cert is *not* a subtree of anything — the
  resolution is that the env invariant field stores the fuel-free
  **consequence** (`DeltaSortLinked env`: per stored definition, the
  ∃-fuel sort-link between declared-type and value-type residuals),
  not the raw cert run.  J0 consumes the field without measure
  impact; the field is discharged in the install tier *after* J0 is
  a ∀-theorem, by (A-T) applied to each install cert.  No cycle:
  J0 consumes the field, never its discharge.  Passes.
* Chain assembly: `whnf`-loop induction, budget-sum drops per step,
  step species consumed as within-J0 arrows at subtree components.
  Passes.

**Every arrow drops the measure or goes to an exempt fact.  The
audit passes.**  S3 = (B) is outside J0 and unchanged: it consumes
J0 as theorems, and its own loop induction is (cert fuel, budget)
with ∃-fuel side facts.

`DeltaSortLinked`'s precise shape (the residual-application form) is
defined at the (F-δ) seal, where `unfoldDefinition`'s exact output
dictates it; it joins the ledger now as the install-tier obligation
replacing the raw install-cert field idea.

**Attack order, updated**: (A-T) first — it is the primitive, its
probe case is the audited one, and its cert-loop induction is the
smallest complete member; then the chain assembly (mechanical), then
(F-nat), (F-core) non-β, (F-core).β (the summit), (E), (F-δ), then
S3 = (B), then the `SortSubstStable` leaf wiring.

### (A-T) ingredient batch 1: run algebra landed; the ledger obligation is MONOTONICITY

`Annot/SortCoh.lean`: `whnfStep_decompose` (read a successful loop
step apart: whnfCore prefix, then the nat/δ/stuck trichotomy),
`whnfStep_assemble_nat/_delta/_stuck` (the goal-directed inverses),
`whnfLoop_succ`/`defeqLoop_succ` (definitional unfoldings),
`whnfLoop_budget_mono` (**provable with no obligation** — the
continuation is in tail position, so a shorter successful loop
replays inside a longer one), `whnf_to_loop`/`whnf_of_loop` (peel and
wrap between the public runs and the loop-internal forms).

**Ledger correction**: the carried obligation is `KnotFuelMono`
(cross-fuel *monotonicity*, five entry points + `reduceNat`), not
`KnotFuelDet` — determinism is its corollary
(`KnotFuelDet_of_mono`, proved: lift both runs to the max and read
them off each other).  Assembly is why monotonicity is unavoidable:
the probe/eta vacuities glue pieces from *different* runs (cert-side
whnfCore steps, given-run suffixes) into one constructed `whnf` run,
and a loop's sub-calls all go through one `r` — every piece must be
lifted to a common knot fuel first.  The planned discharge is
unchanged (oracle-extension induction over `coreKnot`, no catches in
the bodies); `reduceNat` joins the obligation because the assembly
lemmas glue its runs across knot levels too.  Existing
`KnotFuelDet`-consuming lemmas stay as stated — consumers hold
`KnotFuelMono` and project.

### (A-T) ingredient batch 2: the cert-loop decomposition, machine-checked

`Annot/SortCoh.lean`: `PostCoreCert` — the case map as a datatype, one
constructor per certifying path of `defeqStep` on the post-whnfCore
pair — and `defeqStep_decompose`, proved: a certifying step is the
syntactic fast path or one of the twenty-four constructors, with the
whnfCore facts stated once.  Design points that materialized in the
mechanization:

* the `rescue` constructor absorbs every `stuckIrrel` fallback site —
  the body always passes the case's own scrutinees, i.e. the
  post-whnfCore pair verbatim, so ten-odd branches collapse to one;
* hint/guard data no consumer reads (`unfoldableHead`, `headHint`,
  the string-support and `hasFvar` guards) is deliberately dropped:
  constructors are *weaker* than their branches, sound for a
  decomposition;
* the body agreed with the sealed case map everywhere — no doc-fix
  needed; the two liftFueled sites (sort-sort, const-const levels)
  carry their `Option`-level facts (`isEquiv`/`isEquivList
  = some true`), which is the shape `Level.isEquiv_sound` consumes.

The shell next: (A-T)'s cert-loop induction over
`defeqLoop_succ`/`defeqStep_decompose`, terminal cases first
(syntactic via `KnotFuelDet`, sorts via `isEquiv_sound` +
`whnf_sort_out`, det-vacuous structural endgame), the probe and
delta/nat re-entries routed per the J0 audit.

### The budget-edge finding: constructed runs live at the loop

Opening the shell, the assembly combinators surfaced a statement flaw
before any case consumed it: **`whnf`'s internal step budget is a
fixed constant** (`whnfLoopFuel`), so a constructed run one step
longer than a maximal given run cannot be wrapped back into `whnf` —
a whole-`whnf` ∃-run conclusion (`SortLinkE`, the (F) species'
`SortOfEE` outputs) is *false at the budget edge*: prepending a step
to a chain that used its entire budget overflows, and no knot fuel
buys more budget.  Given runs are unaffected (they are hypotheses);
only *constructed* runs hit the edge.

**The amendment, landed** (`Annot/SortCoh.lean`): internal ∃-run
forms go **loop-level**, carrying both existentials — knot fuel *and*
budget: `SortLinkE` now concludes a `whnfLoop` run; the new
`SortOfLE` (loop-level sort computation) replaces `SortOfEE` in all
four (F)-species hypotheses *and* conclusions (uniformity: a
transport's output must be consumable as the next transport's
input).  The public boundary is untouched — public claims' hypotheses
are given whole-`whnf`/`sortOfE` runs (peeled inward via `whnf_peel`
/ `SortOfLE_of_run`), and public conclusions are numeral equalities,
never constructed runs.  Colliding a constructed loop run with a
given run goes through the new `whnfLoop_det` (r-mono + budget-mono
+ same-fuel injection), with `whnfLoop_r_mono` proved from
`KnotFuelMono` by decompose-and-reassemble.
`EnsureSortAgreeR_of_link` re-proved against the amended link (it now
takes `KnotFuelMono`, not just determinism).

Also landed: the rfl-tier shape facts (`reduceNat_*` /
`unfoldDefinition_*` on the seven non-reducible shapes) — the
det-vacuity chases read the given run's own step against these.
Deferred to the shell seal: `unfoldDefinition_none_of_not_unfoldable`
and `natOpResult_shape` (the two non-rfl characterizations), and the
open question flagged for the appCong chase: the bool-constant
outputs of `natOpResult` are delta-inert only if the Bool ctors are
stored as ctors — whether `natOpGuard` pins that, or an env
hypothesis must join the (A-T) claims, is decided when the case is
written.

### (A-T) case tier: the vacuity workhorse and the replay, proved

`Annot/SortCoh.lean`: `loop_stuck_out` — if the subject's whnfCore
output is inert (the shape facts say no nat step, no unfolding), the
given loop run *ends there*; every det-vacuous structural case of the
(A-T) induction closes by colliding this with the given literal-sort
output (a `forallE`/`lam`/`fvar`/`proj`/`const`-shaped normal form is
not a sort).  `loop_align` — the syn-splice: two subjects with one
whnfCore output share every continuation, so the given run replays on
the other subject at a lifted knot fuel, same budget (decompose,
det-align the head, reassemble each trichotomy branch with the mono
obligation).  These two plus the shape facts and `isEquiv_sound` are
the complete supplier set for the shell's proved tier (syn, sorts,
and all det-vacuous structural constructors); what remains for the
shell seal is the induction plumbing (guard preservation through
re-entries), the re-entry cases themselves, and the PSS-routed
hypotheses (probe/rescue/etaR).

### Shell plumbing, first contact: two findings, one strengthening

Assembling the (A-T) shell surfaced three facts before any case was
written (reported per the no-silent-hypotheses rule):

1. **The guards are dead weight in (A-T)** — a pleasant finding: no
   case supplier consumes `WScoped`/`looseBVars`/`LeavesBounded`/
   `PairedLeaves` (syn is `loop_align`, sorts is
   `loop_stuck_out` + assembly, the vacuities are shape-collisions,
   and (A-T) never descends into sub-certs, so there is no
   `whnfPres_*` threading at all).  The internal loop claim drops
   them; the public statement keeps them for interface stability.
   Consequently the (A-T) induction is on the **loop budget alone**
   (no knot-fuel induction: no sub-cert descent).
2. **`natR` was under-informative** — the re-entry analysis needs the
   cert's own first-probe outcome.  Strengthened (constructor +
   decompose re-proof): `natR` now carries
   `reduceNat r env d a = .ok none`, derived in the decompose from
   the shared `hasFvar` guard — the second probe firing proves the
   guard true, so the first probe's `none` is the genuine function
   value.  (`deltaR` cannot be analogously strengthened: the
   `true.true` hint-ordered right-unfold has an unfoldable left
   subject; reverted after the mechanization said so.)
3. **`WhnfCoreIdem` joins the ledger** — the R-side re-entries
   (natR/deltaR/deltaB-with-divergence) pair an *unchanged post-core
   subject* with the given run, and building a run "on `a'`" needs
   `whnfCore` idempotence
   (`whnfCore f d e = .ok e' → whnfCore f' d e' = .ok e'` — true:
   outputs are head-normal; body-level induction over
   `whnfCoreBody`, sized like the decompose seal).  Carried as a
   named obligation with `KnotFuelMono`; its own discharge seal.
   Where the given run *nat-steps past* the cert's pair, the case is
   instead vacuous by the nat-shape chase (nat outputs are
   lits/bool-consts, which never converge to sorts) — the deferred
   `natOpResult_shape` supplies it, and the Bool-ctor inertness
   question lands there.

### Shell ingredients complete: head facts, the unfoldable-false lemma, the named hypotheses

Final ingredient pass before the shell (`Annot/SortCoh.lean`):

* **Five endgame constructors amended** with the branch's
  `unfoldableHead env a = false` fact (`natZeroR`, `natSuccR`,
  `strR`, `consts`, `appCong` — the const/app-headed left subjects,
  whose det-vacuities need the no-unfolding leg that shape-rfl cannot
  give); decompose re-proved.
* `unfoldDefinition_none_of_not_unfoldable` — the deferred direction
  of the `isSome` relation, proved.
* **The shell's five named hypotheses defined**: `WhnfCoreIdem` (the
  ledger obligation), `ProbeSortVacuity` / `RescueSortVacuity` /
  `EtaSortVacuity` (the PSS routings, each carrying the whnfCore
  alignment fact so the discharger has the full configuration), and
  `NatSortVacuity` (the nat-chase routing, cert run included,
  both sides in one disjunction — it also covers `natL` entirely:
  a cert whose left side nat-steps has a sort-free left subject, so
  the natL case needs no IH at all).

The shell (`sortLinkAcrossCertE_of`, next seal) consumes: `inl`/
`syn` via reuse/`loop_align`; sorts via `loop_stuck_out` + assembly +
`isEquiv_sound`; all det-vacuous structural constructors via
`loop_stuck_out` (+ the new head facts for const/app-headed lefts);
`natL` via `NatSortVacuity`; `natR`/`deltaL`/`deltaR`/`deltaB` via
trichotomy-of-the-given-run: nat-legs to `NatSortVacuity` or the
`natR` det-contradiction, aligned delta legs to the loop-IH with
`loop_align`+`WhnfCoreIdem` constructions and assemble-prepends
(loop-level outputs, uncapped budgets — the amendment paying off),
terminal legs to stuck-collisions; `irrel`/`rescue`/`etaR` to the
PSS routings; `etaL` det-vacuous (its left subject is the λ).

### STOP: the shell refuted (A-T)'s liveness half; the primitive reverts to dual-success (A)

Executing the shell, the `deltaR` b-side prepend refused: the
constructed run on `b` must pass through `reduceNat(b')`, for which
**no run fact exists** — and its error leg makes the conclusion a
*liveness* claim: `SortLinkE`'s "∃ a run on the other side" demands
that `b`'s chain terminate, which the runs cannot supply (fuel exists
precisely because termination is unproven; a `b` whose argument
chains exhaust every fuel refutes the ∃ outright, even though the
configuration is semantically fine).  **(A-T) — transport with a
blindly-constructed other side — over-claims.**  The dominance check
(`EnsureSortAgreeR_of_link`) proved (A-T) ⇒ (A) and seduced the
design into taking the stronger form as primitive; the shell's
execution is what exposed that the strength is *unprovable*, not
merely unconsumed.

**The audit of consumers says the liveness was never needed:**

* the leaf ((`SortSubstStable`'s (B)-instance) has BOTH sort runs
  given — dual-success suffices;
* the vacuity dischargers collide constructed runs with GIVEN runs —
  the constructions there mirror given runs step by step
  (fuel-bounded by them), never blind;
* (F).β's top-read under repair δ consumes leaf-(A) — dual — and its
  own constructions are simulations of the given walk, again
  run-mirrors.

**The revert**: the branch's primitive is dual-success **(A)**
(`EnsureSortAgreeAt`-shaped, both runs hypothesized, numeral
equality concluded).  Under the dual form every re-entry threads
from the two *given* runs: the b-side legs come from `b`'s own run's
decomposition (real facts, det-aligned with the cert's), the a'-runs
from `WhnfCoreIdem`-fed `loop_align` on the given a-run, and no case
constructs a run reality hasn't already exhibited.  `SortLinkE` and
`SortLinkAcrossCertE` stay as *definitions* (with
`EnsureSortAgreeR_of_link` documenting the dominance direction), but
nothing takes them as proof obligations; the shell to be built is
`EnsureSortAgree`'s.  The scaffold and the (liveness-shaped)
`SpineSortLink` were reverted unlanded; the spine routing will be
restated dual at the shell re-attempt.  The `whnf_peel` budget-bound
strengthening (needed regardless) is kept.

The vacuity-hypothesis Props are unaffected (they conclude `False`,
no liveness).  `NatSortVacuity` remains as stated; the b-side
`reduceNat` unknowns that motivated its cert-inclusive form now
resolve through the dual form's given-run facts instead, so its
discharger's scope may shrink at the re-attempt.

### THE DUAL SHELL LANDS: `ensureSortAgreeR_of` proved

The (A) primitive closes.  `Annot/SortCoh.lean`:
`ensureSortAgreeR_of` derives `EnsureSortAgreeR` — a certified pair
whose members both whnf to literal sorts has equal numerals — from
the two obligations and five routings:

    KnotFuelMono, WhnfCoreIdem,
    ProbeSortVacuity, RescueSortVacuity, EtaSortVacuity,
    NatSortVacuity, SpineSortAgree (dual form, defined this seal)

by one budget-only induction over the cert loop, dispatching all
twenty-five `PostCoreCert` constructors exactly per the supplier
map: `inl`/`syn` by determinism/replay; `sorts` by two
`loop_stuck_out` collisions + `isEquiv_sound`; eleven det-vacuous
structural cases by one-line stuck-collisions (the app/const-headed
five using their carried head facts + the unfoldable-false lemma and
`NatSortVacuity` for their nat legs); the four re-entry constructors
by reading both GIVEN runs' trichotomies — nat legs det-contradicted
or `NatSortVacuity`-routed, delta legs det-aligned into the loop IH,
terminal legs rebuilt as one-step stuck runs via `WhnfCoreIdem`; the
PSS cases routed.  No case constructs a run reality has not
exhibited; no wrapping (the IH consumes loop-level runs directly).

Recorded as ruled: **dominance checks certify direction, not
provability** — and the liveness finding sits beside the currency
ladder as its mirror (premises weaker than the leaf consumes are
vacuous; conclusions stronger than the runs can witness are liveness
claims).

**Remaining for the branch** (each its own seal): the discharge tier
— `KnotFuelMono` (oracle-extension induction), `WhnfCoreIdem`
(body-level induction), the three PSS vacuities (the chain-transport
machinery: (F)/S2 dual forms), `NatSortVacuity` (the
`natOpResult_shape` chase + the Bool-ctor inertness question),
`SpineSortAgree` (graded unknown #1) — then (B)'s shell on the same
pattern, the (F) species with run-mirror constructions, and the
`SortSubstStable` leaf wiring.

### WhnfCoreIdem corrected to same-fuel; discharge mapped

Scoping the discharge caught the landed obligation as **false**: a
fuel-`0` rerun always errors, and an iota-stuck rerun re-fires the
original's certificate sub-runs, which need the original's fuel — so
∀-fuel idempotence is unprovable in principle, and the dual shell was
consuming a false hypothesis (vacuously true, useless).  Corrected
immediately: `WhnfCoreIdem` is **same-fuel** (`whnfCore f d e = .ok
e' → whnfCore f d e' = .ok e'`) — at the same fuel the rerun
*mirrors* the original call for call — with larger fuels via
`KnotFuelMono`.  The shell's four assemble sites now lift the idem
fact and its co-pieces to `max fc ga` (mono + `whnfLoop_r_mono`);
`deltaL`'s ascription was already same-fuel.  Third instance of
execution-catches-overclaim, recorded with the other two.

**The discharge map** (next seal): one strong induction on `f`
proving core-idem and whnf-idem mutually —

* value shapes: rerun takes the value branch (`whnfCore_pos` on the
  original's sub-run supplies the fuel bound);
* β/ι/ζ-success: the output is a recursive run's output at `f-1` —
  IH + mono;
* β-certfail / ι-stuck: the rerun's cert/`iotaRec` calls are
  *literally the original's calls* — rewrite with the original run's
  own internal facts (no determinism needed);
* proj-stuck: the rerun's `whnf` is on a whnf-output — whnf-idem at
  `f-1`, which is `whnfLoop_final` (landed: terminal-step
  extraction) + core-idem at the loop's knot + a one-step terminal
  reassembly;
* the strLit-scrutinee corner: `projLitToCtor` reruns `whnf` on a
  `strLitToConstructor` spine; bounded chase (left spine is two
  nodes; `whnfCore` does no delta; `iotaRec` none via the
  `strLitSupported` storage facts; `reduceNat` none by name
  mismatch);
* `KnotFuelMono` is a sibling hypothesis of the discharge (its own
  oracle-extension discharge is independent — no cycle).

Landed this seal: the corrected statement, the shell patch,
`whnfCore_pos`, `whnfLoop_final`.

### STOP: the strLit corner refutes `WhnfCoreIdem` outright (fourth catch)

The discharge induction opened at the named watch-point, and the
corner did not resist the map — it refuted the obligation.  Same-fuel
included:

**The refutation.**  `projLitToCtor` on a string-literal scrutinee
runs `whnf (strLitToConstructor s)`, and that chain **delta-unfolds
the stored `String.ofList`** — whose body an accepted env may choose
adversarially: `strLitSupported` checks the support declarations'
presence and types, and `fun l => if … then "boom" else "zap"`
typechecks.  With a body that maps `"hi" ↦ "boom" ↦ "zap"`, the
original run on `.proj sn i pe` (where `whnf pe = "hi"`) outputs
`.proj sn i "boom"`; the rerun re-enters `projLitToCtor` on the
`"boom"` literal and outputs `.proj sn i "zap"`.  Re-normalizing is
*not* the identity: the proj-scrutinee's literal re-expansion is a
genuine second reduction step that `whnfCore` outputs can still
contain.  (The natVal analogue is harmless — `reduceNat` packs nat
literals canonically; the strVal path routes through a *stored
program*.)

**Why the map missed it**: the "bounded chase" assumed the ctor-form
chain was delta-inert; it is not — `String.ofList` is a definition,
and the `whnf` loop unfolds it.  The corner is not adversarial-only
in shape: any env where the expansion is not literal-idempotent
breaks it.

**Repair space** (for the ruling; no discharge work until the
obligation is re-stated):

* **R-a — restrict the obligation to the consumers' shapes.**  The
  shell consumes idem only to *rebuild one-step stuck runs* on
  `a'`/`b'` at the assemble/align sites.  What those sites truly
  need is weaker than idempotence: "`whnfCore f d a' = .ok x` for
  *some* `x` the surrounding facts identify" — in every shell use the
  surrounding case *also* holds `reduceNat`/`unfold` facts about
  `a'`, and for proj-strLit shapes the given run's own next step
  provides the continuation.  Candidate: replace `WhnfCoreIdem` by
  the site-shaped fact "a whnfCore output re-normalizes to *a value
  the same run's suffix processes*", i.e. thread the given run
  instead of an idem oracle — the run-mirror principle applied once
  more.
* **R-b — idem modulo proj-relit**: state idempotence with an
  explicit disjunct for the `.proj`-with-literal-scrutinee shape.
  Pollutes every consumer; the shell's four sites would need the
  disjunct discharged anyway — R-a subsumes it.
* **R-c — env-side pinning** of the `String.ofList` body
  (checker/install change): barred-adjacent (reference kernels do
  not pin it; the strategy ruling protects reduction behavior, and
  install-side strengthening would decline real streams).

Recommendation: **R-a** — re-derive the shell's four assemble/align
sites against run-threaded facts and delete the obligation, exactly
as the liveness revert deleted blind construction.  The count of
caught-undischargeable statements stands at four; all four were
caught by supplier-side scoping before any consumer relied on a
discharge.

### R-a executed: `WhnfCoreIdem` deleted; the shell rides run-threaded re-idem

`Annot/SortCoh.lean`: the obligation is gone from the ledger (a
tombstone comment holds the refutation sketch so no fuel form of
idempotence returns).  In its place, proved:

* `unfoldDefinition_some_head` / `reduceNat_some_head` — a step
  target of either is **const-headed** (read off their match
  patterns);
* `whnfCore_sort_run` — sorts re-core to themselves (value branch);
* **`whnfCore_reidem_const`** — a whnfCore output that is
  const-headed re-cores to itself at the same fuel, by induction on
  the *producing* run: value branches close by shape; β/ι/ζ-success
  outputs are recursive outputs (IH + mono); the β-certfail and
  ι-stuck reruns re-fire the original run's own `infer`/`defeq`/
  `iotaRec` facts verbatim; every proj branch is excluded by the
  const-head shape, so the strLit path — the refutation — is never
  entered.  `KnotFuelMono` is the only obligation consumed.

The shell (`ensureSortAgreeR_of`) lost its `hI` hypothesis: the four
assemble sites derive the const-head shape from their own leg's fact
(`unfold`-some at delta legs; the terminal legs are literal sorts via
`whnfCore_sort_run` + `whnfCore_pos`), and `deltaL` now derives its
`b'`-core fact per leg of the *given* b-run's trichotomy (nat-some /
unfold-some ⇒ const-headed ⇒ re-idem; terminal ⇒ sort).  Every fact
the shell consumes is now either an obligation (`KnotFuelMono`), a
routed vacuity, or something a given run exhibited.

Remaining discharge tier: `KnotFuelMono`, the three PSS vacuities,
`NatSortVacuity`, `SpineSortAgree`.

### KnotFuelMono discharge, batch 1: the oracle order and the helper tier

`Annot/SortCoh.lean`: `CoreSub` — success-extension between oracles,
all five fields (`annotate` included: the bodies reach it through
`isPropType`, even though the public obligation omits it) — and the
helper tier, proved: `ensureSort_mono`, `defEqList_mono`,
`reduceNat_mono` (sequential `by_cases` down its if-chains; the only
oracle use is `whnf` on the arguments), `whnfStep_mono` (decompose,
lift, reassemble — the run algebra reused verbatim), `whnfLoop_mono`
(budget induction over `whnfStep_mono`).

Remaining batches: the cert helpers (`iotaCerts`, `defeqSpine`,
`proofIrrel`, `projCert`/`projTeleCert`, the eta/unit certs,
`projLitToCtor`, `iotaRec`, `majorToCtor`, `isPropType`), the four
bodies + `annotateBody` and its loops, `defeqStep`/`defeqLoop` (via
the decompose or a direct chase), then the knot chain
(`Sub (coreKnot f) (coreKnot f')` by induction) and the public
`KnotFuelMono` projection.  The shell's contract taxonomy stands: an
obligation, a routed vacuity, or a given-run exhibit — nothing else.

### KnotFuelMono discharge, batch 2a: cert helpers, first half

Proved (`Annot/SortCoh.lean`): `iotaCerts_mono` (telescope/argument
recursion), `defeqSpine_mono`, `projTeleCert_mono`,
`projLitToCtor_mono`, `isPropType_mono` (the `annotate` field's one
consumer, confirming the five-field order).  All by the established
success-chase: case the oracle runs, lift by the order, transfer the
r-free guards verbatim.  Remaining for 2b: `projCert`, `proofIrrel`,
`etaCert`, the pair/struct eta and unit certs, `stuckIrrel`,
`majorToCtor`, `iotaRec` (largest, decomposes onto `defEqList`/
`iotaCerts`/levels).  Then the bodies, the step/loop layer for defeq,
the knot chain, the public projection.

### KnotFuelMono discharge, batch 2b-i: the inference-shaped certs

Proved: `projCert_mono`, `proofIrrel_mono`, `etaCert_mono` — the
three certs whose bodies are infer/whnf cascades with sort-matches.
Same success-chase; the only new wrinkle was tactical (branch-entry
iota via bare `simp only []` where the bind-lemmas have nothing left
to do).  Remaining 2b-ii: the pair/struct eta and unit certs,
`stuckIrrel`, `majorToCtor`, `iotaRec`; then the bodies, defeq
step/loop, knot chain, public projection.

### KnotFuelMono batch 2b-ii, part 1 — and a tactical finding

Proved: `projParamCert_mono` (the `iotaCerts` wrapper),
`structEtaProjCerts_mono` (index-list recursion).  **Tactical
finding**, reported before it costs more: the deep-compound-pattern
certs (`pairEtaCert`'s `some (.recInfo _ mI rP [rr])`-style matches)
resist the established recipe — after `cases`-substitution the
*goal*-side match over a nested pattern reduces neither by
`simp only []` nor `dsimp`, so `rw [if_pos …]` cannot reach the
guard.  Candidate recipes for the next seal: goal-side `split` with
equation branches (worked on concrete scrutinees in the re-idem
proof), or a `fun_cases`-driven case tree (the toolchain has
`fun_induction`; `Verify/Level.lean` uses it).  Remaining 2b-ii:
`pairEtaCert`, `structEtaCertWith`/`structEtaCert`,
`structUnitCert`, `stuckIrrel`, `litMajorToCtor`, `majorToCtor`,
`iotaRec`.

### KnotFuelMono batch 2b-ii, part 2: the recipe settled; the eta/unit tier proved

**The compound-pattern recipe is settled** (tried `split` first per
the ruling; it won): `split at h` substitutes variable-scrutinee
matches on *both* sides and resolves compound patterns natively
(non-variable scrutinees yield equations, extra binder at the
pattern); guards need goal-side `rw [if_pos/neg]`; oracle calls stay
the cases-lift pattern with `simp only []` for branch-entry iota;
`ite`-wrapped oracle calls go `by_cases` on the condition with
`rw … at h ⊢`.  Proved on it: `pairEtaCert_mono`,
`structUnitCert_mono`, `structEtaCertWith_mono` (the largest cert),
`structEtaCert_mono`, `stuckIrrel_mono` (the six-probe cascade),
`litMajorToCtor_mono`.  Remaining in the helper tier: `majorToCtor`,
`iotaRec`; then the bodies, defeq step/loop, knot chain, public
projection.

### KnotFuelMono: the helper tier is COMPLETE

`majorToCtor_mono` (both rescue branches: K and eta, each a guarded
infer/whnf/iotaCerts/cert cascade) and `iotaRec_mono` (the recursor
fire path end to end: major whnf, literal conversion, rescue, rule
lookup, the inert throw, comparand levels/params, both telescope
certificates, the index-residual check) close the tier.  Every
r-consuming helper of the knot now has a monotonicity lemma; the
recipe handled both without novelty (two `dsimp`/`simp` placement
adjustments only).  Remaining: the four bodies + `annotateBody` and
its loops, `defeqStep`/`defeqLoop`, the knot chain by fuel-gap
induction, and the public projection — at which point
**`KnotFuelMono` lands as a theorem**: the shell's last wide
obligation, from which half the ledger projects.

### KnotFuelMono: the annotate cluster and three bodies

Proved: `projFieldDom_mono` (telescope recursion with the Prop
checks), `annotateProjRec_mono` (the template-projection rewriter —
the deepest cascade of the cluster: isPropType, field domain, the
annotate/infer/ensureSort chain, the Prop restriction, the
recExtraLevel and scope-guard ites), `annotateProjElim_mono`,
`annotateBody_mono` (all nine clauses — the one body previously
unread on this arc; its structure held no surprises beyond routing
through the projection-elimination cluster, which was read and
proved first), `whnfCoreBody_mono`, and `inferBody_mono` (all
clauses, including the verified-mode λ codomain check and the proj
table dispatch).  Remaining: `defeqStep`/`defeqLoop` (the last
cascade), `whnfBody` (trivial via `whnfLoop_mono`), the knot chain,
and the public projection — the seal at which `KnotFuelMono` lands.

## KNOTFUELMONO LANDS AS A THEOREM

The shell's last wide obligation is discharged.  The final seal:
`defeqStep_mono` (the last cascade — syntactic paths, both guarded
probes, the full lazy-delta ladder, the fifteen-branch structural
endgame, every cert routed through its proved mono), `defeqLoop_mono`
(budget induction), `CoreSub.trans`, `coreSub_succ` (one knot level:
the five bodies at their proved monos; fuel-0 vacuous),
`coreSub_le` (the fuel-gap chain), and

    theorem knotFuelMono (μ : CheckMode) (env : Env) : KnotFuelMono μ env
    theorem knotFuelDet  (μ : CheckMode) (env : Env) : KnotFuelDet μ env

**The projection sweep — every lemma that hypothesized the
obligation now closes with the theorem in its slot**, verified by
the landed instantiation `ensureSortAgreeR_of_vacuities` (the dual
shell conditioned on the five routings alone) and by the slots
enumerated there: `whnfCore_reidem_const`, `whnfLoop_r_mono`,
`whnfLoop_det`, `loop_stuck_out`, `loop_align`, `whnf_sort_out`,
`sortOfE_sort_out`, `sortOfE_fuelDet`, `unitBranch_absurd`,
`SortOfLE_det`, `EnsureSortAgreeR_of_link`.  The ledger entry closes;
`InferFuelDet` (the v3 discharge's hypothesis in
`betaCert_discharge`) is `(knotFuelDet μ env).1`-projectable at its
consumer.

Remaining discharge tier for the branch: the three PSS vacuities,
`NatSortVacuity`, `SpineSortAgree` — then (B)'s shell, the (F)
species, the `SortSubstStable` leaf wiring.

### NatSortVacuity scoping: the Bool-ctor question decided (negatively) by `natOpGuard`'s own text

Read before the chase, as ruled.  `natOpGuard` checks, for the
comparison ops, only that `env.find? boolTrueName` /
`boolFalseName` exist with **empty level parameters** — `some ci =>
ci.toConstantVal.levelParams.isEmpty` accepts *any* constant kind.
An accepted env may store `Bool` as an axiom of type `Sort 1`
(passing `natOpCod`'s shape check) and `Bool.true` as a
level-monomorphic *definition* — which typechecks, passes the guard,
and makes `natOpResult`'s bool-constant outputs **delta-unfoldable**:
the "bool-consts are terminal" leg of the nat chase fails, the
unfolding routes through a stored program, and the strLit-corner
shape returns.

**Consequence**: `NatSortVacuity`'s discharge needs an env-side
fact.  Ledger entry: `BoolCtorsInert env` (the comparison-op outputs'
constants are stored as constructors, hence delta-inert), named
supplier: the install tier — for envs whose `Bool` arrived as an
inductive block the ctors are `ctorInfo` and duplicate-name installs
are rejected; the obligation is discharged per-env alongside
`DeltaSortLinked`.  The arithmetic-op leg (literal outputs) needs no
such fact.

**Also scoped**: the right disjunct of `NatSortVacuity` (the b-side
nat-step under an a-side sort convergence) is not a lemma chain but
a cert-loop induction of its own — "a sort-converging left is never
certified against a nat-stepping right" — structurally a sibling of
the (A) shell (same budget-only descent, terminal cases colliding
nat-shapes with sort-shapes).  The discharge seal should build it on
the shell's skeleton.

### The nat routing DISCHARGED — and the right disjunct dissolved first

Setting up the discharge found one more simplification before any
induction was built: **the right disjunct dissolves** — the dual
shell holds the *given run of each side*, so the routing restates
one-sided (`NatStepNoSort`: core-fact + nat-step + sort-run on one
subject → `False`, cert dropped entirely) and every `.inr` site
applies it with the b-side's own run.  The scoped cert-loop
induction was never needed; the run-mirror principle deleted it
before it was written — fourth deletion of this kind.

Landed and proved: `NatStepNoSort` (+ shell re-sited),
`BoolCtorsInert` (the ledgered env fact, exactly the two
delta-inertness equations the chase consumes),
`whnfCore_lit_run`/`whnfCore_const_run` (value-branch runs),
`natOpResult_shape` (a by_cases chain — `split_ifs` is Mathlib-only
and iterated `split` melts on the Name-eq instances; recorded as a
recipe note), `reduceNat_some_shape` (outputs are literals or the
two `Bool` constants), and the discharge

    theorem natStepNoSort_of : BoolCtorsInert env → NatStepNoSort μ env

— the given run's own trichotomy at the head-normal form:
delta/terminal legs collide with the nat-step by determinism; the
nat leg's target is a literal or `Bool` constant, all whnf-inert
(the `Bool` legs by the env fact), colliding with the literal-sort
convergence.  `ensureSortAgreeR_of_pss` re-states the shell on the
three PSS routings + spine + the env fact.

Remaining routings: the PSS trio, `SpineSortAgree`.

### The transport spine, mapped once (`_gen`-first)

The granted map: state the spine's lemmas at the generality the (F)
species' run-mirror constructions want — the second consumer is
already known, which is the `_gen`-first condition.  Reading the
trio's cert bodies before freezing anything settled the generality.

**Ruling — the transported fact is `w`-general**, not sort-numeral:

    TypeWhnfLE μ env d e w :=
      ∃ ft t, inferTypeCore … e = .ok t ∧
        ∃ g l, whnfLoop … t = .ok w

(loop-level per the budget-edge discipline; `φ`-free — `w` travels
syntactically).  Three forcing reads: `etaCert` matches
`whnf (infer b)` against `.forallE …`; `stuckIrrel`'s b-directed
branches match it against const-app heads (`pairEtaCert`'s
`.app (.app (.const c' _) A) B`, `structEtaCert`'s `wtb`,
`structUnitCert`'s `wta`); `proofIrrel`'s sort branch needs the
spine **twice**, the second time at a sort whose level is not the
subject's.  All collide by `TypeWhnfLE_det` against the constructible
chain-end fact `typeWhnfLE_sort : TypeWhnfLE d (.sort ℓ)
(.sort (.succ ℓ))` — shape collisions for rescue/eta, a level
collision for the probe.  A sort-numeral spine serves none of them;
`SortOfLE` is the spine's sort instance (`sortOfLE_iff_typeWhnfLE`).
The unconsumed `SortTransport*F` species were superseded in place by

* `TypeTransportCoreF` / `TypeTransportDeltaF` / `TypeTransportNatF`
  — the step species, `w`-uniform, premised on `SubjInv` (below);
  (F-core).β remains the summit (the constructive substitution
  pairing);
* `TypeTransportLoopF` — (C\*-L), the whole-chain transport at loop
  level, assembled later from the step species by one loop induction;
  its conclusion sits at the loop's *output*, where every trio
  collision reads it; the whole-`whnf` (C\*-E) spelling returns as a
  `whnf_peel` corollary when needed.

**Finding (premise necessity, refutation by reading)**: `infer`'s
`fvar` leaf returns its own annotation with no cross-leaf check, so
*no run ever certifies pairing* — the syntactic package cannot be
recovered from reality's exhibits and must travel as a premise.
`SubjInv d e` names it (guards + self-pairing); `SubjInv.of_pair`
restricts it from a pair's `PairedLeaves`.

**Finding (the supply chain is head-step-thin)**: the shell's `main`
induction is budget-only with a scoping-free motive, so it holds no
`SubjInv` at the routing sites today.  But its subjects evolve by
*head steps only* — congruence descent is routed wholesale to
`SpineSortAgree`, never recursed by `main` — so threading costs a
per-step preservation species set, not a descent apparatus:
`InvPreserveCoreF` / `InvPreserveDeltaF` (will thread an env
value-closedness fact — install tier, sibling of `BoolCtorsInert`,
named at its seal) / `InvPreserveNatF`, plus `InvPreserveInferF`
(invariant transfer to an inferred type — the probe's entry to the
type's own chain).  Next seal: amend the trio to carry `SubjInv` on
the subject, re-thread `main`'s motive with `SubjInv` both sides
(entry from `EnsureSortAgreeR`'s own guards via `SubjInv.of_pair`),
and let `ensureSortAgreeR_of_pss` take the `InvPreserve*` species as
hypotheses — obligations with named suppliers, per the ledger rule.

**The trio's discharge map against the spine** (the uniform recipe):
extract `TypeWhnfLE a' w` with the branch's shape from the cert;
decompose the given loop run one step and det-align its core output
with the given `a'`; stuck leg — the run ends at `a'`, so
`a' = .sort ℓ` and the collision is direct; nat/δ legs — the step
species carry the fact to the continuation subject, whose run is a
genuine `whnfLoop` run at smaller budget, so `TypeTransportLoopF`
lands `TypeWhnfLE (.sort ℓ) w`, and `typeWhnfLE_sort` +
`TypeWhnfLE_det` force `w = .sort (.succ ℓ)` — then the branch's
shape refutes it.  Per routing:

* `EtaSortVacuity`: `w = .forallE …` — `nomatch`.
* `RescueSortVacuity`, five-way read of `stuckIrrel`: the a-directed
  `pairEtaCert`/`structEtaCert` branches need **no spine** — the
  subject is ctor-app-headed, so a nat-stepping continuation is
  `NatStepNoSort` verbatim and an inert one is `loop_stuck_out`
  colliding an app head with `.sort`; the b-directed branches and
  `structUnitCert` are shape collisions at const-app-headed `w`; the
  fallback is `proofIrrel` = the probe reasoning.
* `ProbeSortVacuity`, unit branch: the unit check's own `whnf ta`
  run is the extraction; the collision needs an
  `isUnitLikeTy env (.sort _) = false` computation leaf
  (`unitBranch_absurd`'s det route does not apply — no second
  sort-run is given here).  Sort branch, the **double spine**:
  (1) subject chain forces `whnf ta = w₁ = .sort (.succ ℓ)`;
  (2) peel `ta`'s own whnf run, enter with `SubjInv` via
  `InvPreserveInferF`, and transport the cert's
  `TypeWhnfLE ta (.sort uT)` along it — `typeWhnfLE_sort` +
  det force `uT`'s syntactic successor shape, refuting the cert's
  `Level.isEquiv uT .zero = ok true` through a level-arithmetic
  leaf (isEquiv-succ-zero refutation, named at the discharge seal).
  The double application is why `w`-generality is load-bearing
  *inside* the trio, not only for (F).

Landed and proved this seal: `TypeWhnfLE`, `TypeWhnfLE_det`,
`typeWhnfLE_sort`, `sortOfLE_iff_typeWhnfLE`, `SubjInv`,
`SubjInv.of_pair`; the species restated (statements only, as
before).  Remaining routings unchanged: the PSS trio,
`SpineSortAgree`; new supplier tier: the `InvPreserve*` species.

### SubjInv threaded: the trio amended, the shell re-threaded

The supply chain landed exactly as sized — head-step-thin.  The trio
and `SpineSortAgree` now carry `SubjInv` on their subjects (premise
first, package style); `main`'s motive carries it both sides; the
entry restricts it from `EnsureSortAgreeR`'s own guards
(`SubjInv.of_pair` / `.of_pair_right` — the right-side restriction
landed with the thread); every re-entry site derives the successor
package from the three preservers (`hIC`/`hID`/`hIN` — nat re-entries
compose core-then-nat, δ re-entries core-then-δ; the natR stuck leg's
package specializes through the `a' = .sort` substitution untouched).
`ensureSortAgreeR_of`, `_of_vacuities`, `_of_pss` gained the three
`InvPreserve*F` hypotheses — ledgered obligations, suppliers = their
own discharge seals (`InvPreserveInferF` is not a shell hypothesis;
it enters at the probe's discharge only).  The whole re-thread
compiled first-pass: no case needed descent preservation, confirming
the head-step-only reading of `main`'s subject evolution.

Discharge-tier map (next): `typeTransportLoopF_of` (the loop
assembly from step species + preservers, `loop_stuck_out`'s
skeleton), then `etaSortVacuity_of` / `rescueSortVacuity_of` /
`probeSortVacuity_of` reducing the trio to the (F) species per the
recorded recipe.  Leaf inventory update: the isEquiv-succ-zero
refutation already exists as `Level.isEquiv_sound` (gives
`uT.eval φ = 0` against `eval (succ _) = _ + 1`); only the
`isUnitLikeTy env (.sort _) = false` computation leaf remains new.

### The PSS trio DISCHARGED — the branch's routings are now species-shaped

The recorded recipe held under mechanization, with one welcome
simplification and no statement-level surprises:

* `typeTransportLoopF_of` — the loop assembly, one budget induction
  over `whnfStep_decompose`; it needs **no determinism** (`hm`
  dropped from its statement: transport is forward-only along the
  given run).
* `typeWhnfLE_collide` — the collision engine: one-step decompose +
  det-align, then the step species carry the fact to the
  continuation subject (a genuine `whnfLoop` run at smaller budget)
  and `TypeTransportLoopF` lands it at `.sort ℓ`; the stuck leg
  needs no transport at all.  All three legs end at
  `typeWhnfLE_sort` + `TypeWhnfLE_det`.
* `ctorHead_no_sort` + `unfoldDefinition_ctor_none` — the no-spine
  route (nat continuation is `NatStepNoSort` verbatim, δ refuted by
  the ctor head, stuck collides shapes).
* `etaSortVacuity_of` — first-try landing of the extraction pattern
  (unfold + bind-simp + cases-with-rw + `split at`).
* `proofIrrel_no_sort` / `probeSortVacuity_of` — the double spine as
  mapped: the unit check's own run collides via `isUnitLikeTy_sort`
  (killing the unit branch before it forks), the sort branch pins
  `uT = .succ (.succ ℓ)` through the second transport (entered via
  `InvPreserveInferF`) and refutes `isEquiv uT 0` by
  `Level.isEquiv_sound` at the zero valuation.  The `okA = false`
  leg is a pure b-side walk to `.ok false ≠ .ok true`.  Recipe note:
  `liftFueled` results are cased as `CheckM` values first
  (`cases h : liftFueled … (m := CheckM)`), then `liftFueled.eq_def`
  + `split` recovers the `isEquiv = some _` equation — splitting
  `hpi` directly grabs the outer `Except.bind` match instead.
* `rescueSortVacuity_of` — the five-way read; the a-directed
  branches took the no-spine route, the b-directed and unit branches
  the collide route (where `split` had already reduced
  `(.sort _).getAppFn`, the arm equation is a bare constructor
  clash — `nomatch`, not a `getAppFn` simp), the fallback is the
  probe lemma.

**`ensureSortAgreeR_of_species`** restates the shell at the new
frontier: `EnsureSortAgreeR` from `BoolCtorsInert` + the three
`InvPreserve*F` + `InvPreserveInferF` + the three transport step
species + `SpineSortAgree`.  The trio is no longer a routing — every
remaining unknown of the defeq branch is either an (F) step species,
an invariant preserver, an env fact, or `SpineSortAgree`.

### SpineSortAgree reduced to its both-δ core — the graded unknown scoped

The `defeqSpine` case-structure map, before any induction (the
graded-unknown discipline): a `true` verdict pins both subjects
const-headed with the **same head `n`**, equal arg counts,
`isEquivList`-equivalent levels, and pointwise `defEqList`-certified
args.  On a sort-converging subject the loop's legs at the
head-normal form read off:

* stuck — the output is the literal sort, clashing with the const
  head (`defeqSpine`'s own match reduces to `pure false`);
* nat — `NatStepNoSort` **verbatim** (third reuse of that routing's
  one-sided form);
* δ — the only live leg: `unfoldDefinition` on the *same* `n` on
  both sides, so both continuations are instantiations of **one
  stored value** at equivalent levels with certified args.

`DeltaSpineSortAgree` names that residue (stated exactly as reality
exhibits it: the `defeqSpine` run + both unfold facts + both
continuation loop runs + `SubjInv` at the head-normal forms — no
decomposition baked in); `spineSortAgree_of` proves the reduction
(`hm`, `BoolCtorsInert`, `InvPreserveCoreF`, core ⇒
`SpineSortAgree`).  `ensureSortAgreeR_of_core` restates the branch
primitive at its irreducibles: env fact + three transport step
species + four preservers + the both-δ core.

**The core's identity (the graded part — supplier ruling needed).**
It is *not* level bookkeeping: term args never enter level data, but
the whnf **path** of the instantiated value can consume argument
values (types compute).  Hard instance: `def G (b : Bool) := cond b
Prop (Type 0)` — `G a ≡ G b` via the spine fires with certified
`a ≡ b`, and the two continuations reach `.sort 0` vs `.sort 1`
*unless* the certified pair converges to the same `Bool`
constructor.  So the core embeds **certified-pair convergence at
argument positions** — (A)-shaped strength, one template
instantiation down.  No decreasing syntactic measure identified: the
args' cert runs sit at fresh `defeqBody` budgets (no descent), and
the template's β-unfolding regrows subjects.  Non-vacuous even in
the benign direction (`def T := Prop`, `T ≡ T` by spine: both
continuations reach `.sort 0` — agreement there is by determinism,
but the general case is not).  Candidate supplier tiers, for the
ruling: (i) syntactic with a new measure — none found, this map is
the evidence; (ii) the model/certified tier — semantic defeq
soundness gives sort agreement of certified pairs, the lean4lean
route, supplied where `EnsureSortAgreeR`'s consumer already lives;
(iii) install-tier restriction — nothing natural.  The branch
primitive is otherwise fully discharged.

### The core's supplier RULED: grade (ii), the model tier

The ruling, with the reasoning recorded so the record shows why this
does not contradict the premise ladder: the ladder refuted
interp-equality → sort agreement for general TYPES (the sort-blind
carrier countermodel); `DeltaSpineSortAgree`'s conclusion is about
literal SORTS, where interp is injective (`univ_inj` — the same fact
that carried Tier A's unique kinding).  The route: certified pair →
`DefEqClaimsR` soundness → interp equality; both continuations
converge to literal sorts with interp preserved along the chain
(`WhnfClaimsR`, `denote_delta_step`) → `univ u = univ v` →
`univ_inj` → numerals equal.  The countermodel is consistent: it had
equal shadows and NO certifying run.  (ii) works precisely where the
ladder said semantics fails elsewhere.  (i) is evidenced empty (the
`G`-example: args' cert runs at fresh budgets, β regrowth — no
decreasing measure); (iii) would be a parity violation.  V-freedom
of the shell is unaffected: the core rides out as a hypothesis like
`BoolCtorsInert` and discharges at the consumer where `EnvS` lives.

### FINDING: the claims do not thread denote facts to internal spine subjects

The pre-build check the ruling required, run against the actual
suppliers by name (`Setlec/SetR/Bridge/Claims.lean`):

* `DefEqClaimsR` and `WhnfClaimsR`/`WhnfCoreClaimsR` are
  **conditional** on the subject denoting (`∀ {v}, denote … = some v
  → …`) and on `CtxOkR` at a context Δ;
* only `InferClaimsR` **establishes** denotedness — and it needs an
  `inferTypeCore` run plus `CtxOkR` plus the guards;
* `DeltaSpineSortAgree` carries none of these: no infer runs, no
  `CtxOkR`, no Δ, no denote facts — `SubjInv` is syntactic.

The internal spine-case subjects are multi-head-step descendants of
the consumer's framed pair, but the shell's motive does not record
that descent — so the core, as a closed `∀` over bare runs, is NOT
dischargeable at the model tier today.  The denotability premise-wish
the ruling warned about is real; reported, not patched.

**Repair direction (for ruling, not built):** an abstract invariant
slot.  The `SubjInv` thread is the template: make the shell
parametric in `P : Expr → Prop` (depth is FIXED along the shell —
subjects evolve by head steps only, so no depth-evolution in `P`),
with three P-preservation hypotheses (suppliers at the consumer:
`WhnfCoreClaimsR` for core steps, `denote_delta_step` for δ —
"the reduct denotes identically" — and the literal/`Bool` denotes
for nat), entry through a P-enriched (A)-variant
(`EnsureSortAgreeRP`), and the spine core receiving `P a'`/`P b'`.
The consumer instantiates `P := denote-and-CtxOkR-at-its-Δ`;
V-freedom is preserved by parametricity (the induction never
inspects `P`).  The P-free `EnsureSortAgreeR` returns as the
`P := True` instance.

### Two framings recorded (user exchange, via coordinator)

* **The trans-free framing, explicit**: a checker run IS a
  derivation in the trans-free algorithmic calculus (reduce
  left/right, congruence, leaves); the relation family keeps `trans`
  for soundness where interp-equality makes it free.  The back-phase
  minimization gets a pointer here: name the trans-free relation
  formally when that phase opens.
* **The typed-conversion framing**: this coherence family
  establishes exactly the "defeq preserves same-sortedness along its
  own recursion" invariant.  An up-front sort check in the checker
  is barred by parity/no-new-checks; assuming the invariant would
  not shorten the proof — its preservation IS the induction.

### (B)'s dual-pattern case map (scoped before any induction)

`sortOfE e = some u` unpacks to an infer run + a whnf-to-literal-sort
run on the inferred type + `eval` (`TypeWhnfLE e (.sort ℓ)` with
`u = ℓ.eval φ` — `sortOfLE_iff_typeWhnfLE`).  The 25-case read of
the (A) decomposition, at the type level:

* **Bases**: `syn` (`sortOfE_fuelDet`); `sorts`
  (`sortOfE_sort_out` + `Level.isEquiv_sound` — arithmetic); `lits`
  (identical subjects — det, no env fact needed).
* **Re-entries** (`natL/R`, `deltaL/R/B`): sortOfE stability across
  the head rewrite = the transport species' sort instances
  (`TypeTransport*F` via the bridge) + budget recursion — (A)'s
  skeleton verbatim.
* **PSS certs** (`irrel`/`rescue`/`etaR`): vacuities one level up —
  a PSS-certified subject has no successful `sortOfE`; the landed
  collision machinery discharges them (e.g. irrel: transport
  `TypeWhnfLE a (.sort ℓu)` one core step, `ta`'s chain pins
  `uT = .succ ℓu`, `isEquiv uT 0` refuted by eval arithmetic; eta:
  `forallE` vs sort clash; rescue: the five-way as before).
* **The congruence tier — (B)'s real content**, each a named routing
  at its own seal:
  - `fvars` (same index, own annotations): needs `ty₁ = ty₂` from
    **cross-pairing**.  DISCOVERY: the (A)-thread's `SubjInv` split
    (self-pairing per side) deliberately dropped the cross form —
    harmless in (A) where `fvars` is shape-vacuous, load-bearing in
    (B).  (B)'s thread must carry `PairedLeaves a b` in pair form,
    preserved along both sides' head steps jointly (leaf sets only
    shrink along whnfCore/δ/nat — same preservation species tier).
  - `consts` (same head, equiv levels, non-unfoldable): one stored
    type at two equiv level instantiations — level-subst congruence
    of whnf-to-sort runs; `DeltaSpineSortAgree`'s argless sibling.
  - `spine` / `appCong`: recursion through the application clause's
    pi-walk — the spine-core tier.
  - `piCong`/`lamCong`: subterm recursion with binder opening — the
    Θ-motive proper (each side opens with its OWN domain; the paired
    zone carries the domain sub-cert).
  - mixed nat/str terminals (`natZeroR` etc.): both types are the
    same basis const (`Nat`/`String`); vacuous or det modulo a
    basis-type delta-inertness env fact (`BoolCtorsInert`'s sibling;
    named if/when a case needs it).

**Statement-shape consequence, for the ruling**: (B)'s shell wants
(1) the pair-form `PairedLeaves` thread and (2) plausibly the same
abstract `P`-slot as the spine repair — both touch the motive.  Rule
on both before the (B) build so the motive is threaded once.

### The joint motive pass LANDED — one binary slot serves both rulings

Refinement over the ruled P-slot, recorded with its justification:
the shell is parametric in a **binary** invariant
`Q : Nat → Expr → Expr → Prop` on the compared pair, with three
*left*-step preservers (`QPreserveCoreF/DeltaF/NatF`) plus a
symmetry hypothesis — steps touch one side at a time, so right-side
steps ride symmetry (both ruled instances are symmetric: the denote
frame is `Q := P×P`, cross-pairing is `PairedLeaves`).  One slot
subsumes both ruled threads AND avoids a hypothesis regression: the
`Q := True` instance recovers the slot-free `EnsureSortAgreeR` with
*trivial* preservers (`fun _ h => h`), whereas threading
`PairedLeaves` concretely would have taxed the slot-free claim with
real pairing-preserver obligations it never uses.

Landed: `EnsureSortAgreeRQ` (the `Q`-enriched claim),
`ensureSortAgreeRQ_of` (the re-threaded shell — `Q` enters from the
claim's own premise and steps by preserver-plus-symmetry
compositions at every re-entry site; compiled with the motive edit
plus mechanical site compositions, the second first-pass re-thread),
`ensureSortAgreeR_of` (the `True` instance), the `Q`-parametric
chain (`_of_vacuities`/`_of_pss`/`_of_species`/`_of_core`,
`spineSortAgree_of`), `SpineSortAgree`/`DeltaSpineSortAgree` with
`Q` at pre-core/head-normal subjects respectively,
`PairedLeaves.symm`, and the pairing preserver species
(`PairedPreserveCoreF/DeltaF/NatF` — (B)'s `fvars` suppliers,
discharged alongside the `InvPreserve*F` suppliers whose
self-pairing legs prove the same leaf-shrinking).

Recipe note: implicit-`Q` wrapper calls mis-unify (higher-order
imitation picks a projection solution from the symmetry
hypothesis's swapped occurrence) — pin `(Q := Q)` explicitly at
every chained call.

The model-tier core discharge now has its channel: the consumer
instantiates `Q d a b := denotes-and-CtxOkR-in-frame for both`,
supplies the three preservers from `WhnfCoreClaimsR` /
`denote_delta_step` / the literal-`Bool` denotes, and
`DeltaSpineSortAgree` receives the frame at the head-normal forms.
Next: the (B) shell on the settled shape (its own motive copies the
`Q`-thread; PSS-one-level-up vacuities first, congruence tier
after).

### (B)'s dual shell LANDED — first-pass, on the settled motive

`sortOfAgreeRQ_of` proves `SortOfAgreeRQ` (the `Q`-enriched (B)
claim; `sortOfAgreeR_of` recovers the slot-free `SortOfAgreeR` at
`Q := True`) by the same budget-only cert-loop induction as (A), at
the type level — the motive threads `SubjInv` per side + concrete
cross-`PairedLeaves` (via the `PairedPreserve*F` species, now
consumed) + the abstract `Q`-slot.  The whole 25-case induction
compiled first-pass: with `sortOfLE_step_core/delta/nat` (the
transport species' sort instances) and `sortOfLE_sort_out`, every
base is determinism or arithmetic and every re-entry is a
composition.

Map corrections landed with the build:

* `etaL`/`etaR`/`lamCong` all die on ONE routing —
  `LamTySortVacuity` (a λ's inferred type is a `∀`, never a sort);
  the eta cert is not even consumed.  The predicted Θ-motive tier
  thus shrinks to `piCong` alone among the binder cases.
* `natL`/`natR` are plain re-entries through the nat transport
  species — not vacuities (the transported fact rides the step
  uniformly; the earlier vacuity reading was the (A) habit).
* `natZeroR` routes through the SAME `NatZeroTySortAgree` as
  `natZeroL`, flipped (`.symm`) — no orientation duplication needed
  where there is no run payload; `natSuccL/R` and `strL/R` keep
  split Props (their cert runs cannot be flipped).

(B)'s routing inventory (each at its own seal):
`ProbeTySortVacuity` / `RescueTySortVacuity` (the type-level PSS
duals — probe/eta reuse the landed collision skeleton with det in
place of the loop collide; rescue's a-directed legs need the
ctor-type telescope shape, an env-tier fact flagged at the map),
`LamTySortVacuity` (infer-lam extraction + forallE-stuck),
`NatZeroTySortAgree` / `NatSuccL/RTySortAgree` / `StrL/RTySortAgree`
(basis pins), `FvarTySortAgree` (cross-pairing + name-blind infer),
`ConstTySortAgree` (the spine core's argless sibling),
`SpineTySortAgree` / `PiCongTySortAgree` / `AppCongTySortAgree` /
`ProjCongTySortAgree` (the graded congruence tier, `Q`-carrying —
same supplier-tier question as `DeltaSpineSortAgree`, presumably the
same model-tier answer).

### Three (B) routings discharged; the congruence tier UNHELD (no cumulativity)

**Discharged this seal** (with the shape helpers
`whnfCore_forallE_run`, `inferTypeCore_lam_out`,
`inferTypeCore_fvar_out`):

* `lamTySortVacuity_of` — a λ infers to a `∀` (every success path of
  the clause), and `∀`s are whnf-inert (`loop_stuck_out`).
* `fvarTySortAgree_of` — cross-pairing pins the annotations equal
  (the leaf is the head of its own `fvarLeaves`), `infer` reads the
  annotation name-blind, `whnfLoop_det` finishes.  The `SubjInv`
  premises went unused — kept in the Prop for uniformity.
* `probeTySortVacuity_of` — the (A) double spine with `TypeWhnfLE_det`
  in place of the loop collide; `uT` pins to the SINGLE successor.

**The no-cumulativity finding (the coordinator's check, decisive —
the branch's load-bearing fact).**  Two lines of the checker:
`inferBody`'s sort clause is literally `.sort u ↦ .sort (.succ u)`
(Core.lean:1550), and the only sort-sort comparison anywhere is
`Level.isEquiv`, never `≤` (Core.lean:1816) — no cumulativity.
Consequently a family's codomain sort is one level expression,
computed at the fvar-opened body with no term arguments in sight;
every fibre inhabits it; a fibre reducing to `Sort ℓ` forces
`ℓ + 1 =` that expression.  **The result sort is pinned by the
head's declared codomain, uniformly in arguments.**

*Correction (retraction of the "hard instance")*: the `G`-example
(`cond b Prop (Type 0)`) is REJECTED at the app clause —
`isEquiv 1 2 = false` — so it never installs; the earlier ledger
entry's countermodel-flavored reading of the core is wrong.  What
the `G`-search DID establish survives as the measure verdict's
scope: no decreasing measure over run fuel and subject size — the
unhold adds the measure the search could not see, the
**environment's declaration index** (a stored head's declared type
mentions only earlier constants).

**The core's discharge chain, traced on landed machinery**
(`TypeTransportLoopF` + `typeWhnfLE_sort` + `TypeWhnfLE_det` +
`isEquivList` soundness), down to two ledger-shaped gaps:

* **Gap 1** — `DeltaSortLinked` strengthened to *two instantiations*:
  for stored `G` at arity `n`, `inferTypeCore`'s result whnf-sort is
  one level expression in `us`, not args; install-tier discharge
  route, with the declaration-index measure in view.  The (F-δ) seal
  moves EARLIER — its shape is now load-bearing for the core, not
  just the transport.
* **Gap 2 (landed this seal)** — `DeltaSpineSortAgree` restated
  dual-success: the sort runs are premises ON `a'`/`b'` (the (A-T)
  liveness pattern), and `spineSortAgree_of` assembles them in its
  both-δ leg (spine const heads → `whnfCore_reidem_const` →
  `whnfStep_assemble_delta`); the `xa`/`xb` unfold premises are gone
  — the discharge reads the δ steps off the runs.

Also per the unhold: A5 does not apply to this route
(`inferTypeCore` is a function; `KnotFuelDet` kills the type-slot
freedom that killed the relation-level version), and the graded
congruence tier (`Const`/`Spine`/`PiCong`/`AppCong` +
`ProjCong`) presumably follows the same fixed-codomain pattern —
each to be CHECKED against it at its seal, not assumed.  No
semantic supplier, no tagged model needed for the core.

### STOP: the w-general (F) species are REFUTABLE — currency finding

Preparing the resequenced (F-δ) seal, the species statements were
checked against construction before any discharge was built.  Both
step species fail, by the same seed: **certified-defeq sorts carry
`isEquiv`-related, syntactically DISTINCT levels** (the sort-sort
case is `Level.isEquiv u v`, Core.lean:1816 — the no-cumulativity
finding's own citation, read in the other direction).

*Falsifier, (F-δ)* — `def f : Sort (max u v) := PUnit.{max v u}`
(install cert: `isEquiv (max v u) (max u v) = true`, accepted).
`e := f`-const: `infer e` = the stored type `.sort (max u v)`,
whnf-inert, so `TypeWhnfLE e (.sort (max u v))`.
`e' := unfold e = PUnit.{max v u}`: `infer e' = .sort (max v u)`,
whnf-inert — by `TypeWhnfLE_det`, `e'` reaches ONLY
`.sort (max v u) ≠ .sort (max u v)`.  `TypeTransportDeltaF` is
false.

*Falsifier, (F-core).β* — `e := (fun x : Sort (max u v) => x)
PUnit.{max v u}`: the redex certifies (`isEquiv` at the domain),
`whnfCore e = PUnit.{max v u} = e'`; `infer e` = the codomain
instantiation `.sort (max u v)`; `infer e'` = `.sort (max v u)`.
Traced against the real clauses (lam clause's opened-body
annotation, app clause's residual).  `TypeTransportCoreF` is false.
Both falsifiers are arena-realizable (level params + a `PUnit`-like
stored constant).  A second, non-sort seed exists: proofIrrel-slack
stuck forms (`P x h₁` vs `P x h₂`) — so even a
level-equivalence-weakened conclusion (`∃ w', LevelEq w w' ∧ …`) is
false; the truthful conclusion relation degenerates to
certified-defeq-of-whnfs, the currency this arc rejected as
circular.

**What survives (master holds NO false theorems).**  The refuted
objects are `def`s (hypotheses); every consuming theorem is a valid
conditional: both shells (`ensureSortAgreeRQ_of`,
`sortOfAgreeRQ_of` — their inductions consume the species only
through routed hypotheses), the trio discharges,
`typeWhnfLE_collide`, `typeTransportLoopF_of`, the wrapper chains.
What is dead is the DISCHARGE ROUTE: the species can never be
supplied, so the tower cannot close as currently conditioned.
The three (B) discharges that avoid the species (`lam`, `fvar`)
stand on their own; `probeTySortVacuity_of` and the (A) trio
discharges are conditionals awaiting the repair.

**Repair space (for ruling — the currency must be re-chosen).**
The consumers' true needs split:

1. *Eval-level agreements* (the core, the sorts cases, the probe's
   second spine): the honest species shape is **dual-success eval
   currency pinned by install templates** — per-subject facts
   "IF sort-of succeeds on a `G`-headed subject, its value is
   `template_G[us].eval φ`" (`DeltaSortLinked`, exactly Gap 1),
   with neighboring templates eval-linked by the install cert under
   the **declaration-index measure**, and β linking through the
   arg-cert — the mutual knot at eval currency (the module
   docstring's original prognosis: one mutual induction with
   (B)-shaped leaves).  Intermediate subjects need no exhibited
   runs: pinning is per-head, not per-run.
2. *Shape collisions* (the trio's first spine application): the
   transported-shape route is dead; the surviving candidates are
   (a) per-head pinning again — a cert-exhibited `forallE`-shaped
   whnf-of-infer at `a'` vs the chain-end's sort-success, linked by
   definedness/shape agreement along the chain (needs a
   definedness-agreement component whose truth is unassessed), or
   (b) the semantic tier for the trio alone.

No code changed at this seal; the (F-δ) seal is HELD pending the
currency ruling.

### Currency ruling recorded; the semantic-trio statement pass landed

**Standing practice (coordinator's permanence ruling)**: *check the
species against construction before building the discharge* — run
the statement against the actual clauses and known slack seeds
(isEquiv level slack, proofIrrel stuck slack, fuel liveness) the way
the trap family is run against quantifier patterns.  It has now paid
three times (WhnfCoreIdem, the denote threading, the w-general
species).

**The ruling**: (1) eval currency for the agreement consumers —
dual-success, pinned per head by install templates
(`DeltaSortLinked`: "if sort-of succeeds on a `G`-headed subject,
its value evals to `template_G[us]` at `φ`"), neighbors linked by
install certs under the declaration-index measure, β through the
arg-cert; syntactic level identity was never the right invariant,
eval at `φ` is.  (2) The trio goes SEMANTIC through the landed
`Q`-slot: its content — a proposition cannot be a universe — is
`univ (ℓ+1) ∉`-the-`Prop`-fibre, no sort-blindness issue.

**Landed this seal (statements only)**: the five vacuity Props
(`Probe/Rescue/EtaSortVacuity`, `Probe/RescueTySortVacuity`) carry
the `Q`-frame at their cert pair (`Q d a' b'`; eta at
`Q d a' (.lam …)`); both shells supply it from the threaded slot
(one preserver composition per site); the landed syntactic
discharges absorb the premise (`∀ Q` — they never read it) so
master keeps compiling; the True instances update.  Inventory for
the semantic discharge seal: `univ_inj`, `mem_univ_zero`,
`univ_mem_univ` present (`SetTheory/Derive/Univ.lean`); the missing
one-lemma is `univ`-vs-`pt` separation — check `PtFresh.lean` first
(the #109 machinery is the natural supplier).

**Construction-check results on the eval-species candidates**
(the ruled pre-build check, run BEFORE stating them — three shapes
examined, none landed yet):

* *Step-agreement* (dual-success per step): TRUE-looking (both
  falsifiers pass at eval; installability forces branch sorts
  eval-equal — the no-cumulativity finding closes the type-level
  `cond` hole: distinct-sort branches don't fit one `Sort α`
  without cumulativity), but it does NOT COMPOSE along chains —
  intermediate successes are unexhibited.
* *Loop-form dual-success*: TRUE-looking as a primitive (discharged
  by a pinning induction that carries the pin, not the success),
  but INSUFFICIENT alone for the spine core — `sort-of a'` success
  is not among the core's premises.
* *Success-preserving forward transport*: BARRED — it is whnf
  termination on a defeq type, normalization strength.

**Consequence (finding, for the ruling on the next statement)**:
the (B) shell's re-entry legs consumed `sortOfLE_step_*` (derived
from the refuted species) — (B)'s discharge route is dead too, and
forward-success transport cannot be repaired at any currency.  All
remaining agreement consumers (the spine core, (B)'s re-entries,
`Const/Spine/PiCong/AppCong/ProjCong`) converge on ONE summit
statement: **the certified-pair eval-sort simulation** — a lockstep
relation on [same template, defEqList-certified args,
isEquivList-linked levels] pairs, stepping by δ (same stored value —
install cert links templates under the declaration-index measure),
β (the arg-cert), nat, and arg-head exposure (recursion into the
(A)/(B) claims at the certified arg pair — the mutual knot, with
the cert run GIVEN).  Proposal: state the simulation once, at its
own seal, with the pre-build check; the piecemeal step species are
not landed (two of three shapes fail their consumer analysis).

Recipe note: an `intro _`-anonymized hypothesis gets REVERTED by a
later `split at`, shifting the `next` binder assignment off by one —
name absorbed premises `_hQv`-style, never bare `_`.

### The summit STATED: `CertZip` + the two eval-sort simulation claims

Per the ruling, one statement seal, checks first.  Landed:
`CertZip μ env fc d` (lockstep relation: `refl`, `cert` leaves at
knot fuel `fc`, sort/const level slack, structural congruence over
exactly the nodes `instantiateLevelParams` crosses — "one template,
two instantiations, certified leaves" derivable, not primitive) and
the dual-success claims `ZipWhnfSortAgree` (subject form — the spine
core and (A)'s remaining routings collapse onto it) and
`ZipSortOfAgree` (type form — (B)'s re-entries and the congruence
routings collapse onto it).

**Lineage recorded**: the module docstring's one-mutual-induction
prognosis ("(C)'s β is SortSubstStable-shaped, SortSubstStable's
leaf is (B)-shaped") is the survivor of the refutation — the claims
above are its statement, arrived at by elimination.

**Pre-build check (run before writing, against the clauses)**:
* isEquiv slack — absorbed (conclusions are eval-equalities; both
  w-species falsifiers pass these statements);
* proofIrrel stuck slack — absorbed (no output-identity claims);
* liveness — none (dual-success throughout; the given runs also
  discipline asymmetric lockstep stages: a side whose redex cert
  fails goes stuck non-sort, contradicting its own given run);
* fuel scales — every run at its own fuel; `fc` indexes only the
  leaf certs (trap-family quantifier pattern);
* β-closure — shape-audited: whnf β-reduces at the head only; a zip
  head-λ is a template pair (contractum = body with the arg zip at
  substituAND positions — cert leaves are never substituted INTO)
  or a `cert` leaf (decomposed by the (A)-machinery at smaller
  `fc`).  The general zip substitution lemma is NOT claimed (cert
  leaves under substituted binders would break it); only the
  head-shape instances are needed.

**Measure audit (before any case work)**: lexicographic
**[env declaration index, cert knot fuel `fc`, run budgets]**.
* `fc` decreases at every leaf exposure: `isDefEqCore (fc+1)` opens
  to `defeqLoop` over `pureFns fc`, whose cert fields
  (`defEqList`, `piCong`'s sub-certs, …) run at `fc` — read off
  `isDefEqCore_succ`/`defeqLoop_succ`.  This is the mutual knot's
  universal decrease: (A)/(B) at `fc+1` consume zip claims whose
  leaves sit at `fc`, and vice versa.
* Run budgets decrease along lockstep decomposition of the given
  loop runs (the (A)-shell's own induction pattern).
* The δ-template link (same head unfolds one stored value; its
  install cert relates value-type to declared type) recurses through
  a cert that lives at the ENV PREFIX — the outer layer needs
  env-indexed claims plus prefix transport of runs and claims;
  named supplier: `Extend/Transport` (`extend_fresh` /
  `extend_rec_swap`).  This is the audit's one structural finding:
  the collapse seals must state the zip claims env-parametric (or
  thread an env-prefix hypothesis) before the δ case is built.
* The zip tier is `Q`-free: agreements went syntactic, so leaf
  recursion consumes (A)/(B) at `Q := True` — no `Q`-descent
  obligation anywhere; `Q`'s only surviving consumer is the
  semantic trio.
* Leaf recursion needs cross-`PairedLeaves` at the leaf pair; the
  claims carry `PairedLeaves s t`, and the (A)-shell's motive gains
  the concrete pairing thread at the collapse seal ((B)'s motive is
  the proved pattern; the preserver species already exist).

**The collapse map (next seals, in dependency order)**: (1) the
env-index layer decision (env-parametric restatement vs prefix
hypothesis — coordinator input wanted); (2) `defEqList` per-arg
extraction + the template-instantiation zip theorem
(`v[us] zip v[us']`); (3) `DeltaSpineSortAgree` from
`ZipWhnfSortAgree`; (4) (B)'s re-entries and congruence routings
from `ZipSortOfAgree`; (5) the zip claims' own mutual induction —
the summit's case work, LAST, on the audited measure.

### (E) STATED — env-extension run stability, the third install-tier fact

The env-layer ruling recorded: claims stay single-env (the
campaign's environment rule — state facts at the env the checker ran
them at; env-parametric restatement would churn the landed tier);
the δ-link's prefix install cert transports FORWARD via (E).

Landed (statements): `ConstsBound env₀ e` (every mentioned constant
bound in the prefix, hereditary through annotations — the `sizeF`
WF pattern), `FindPreserved env₀ env` (conservative extension),
`EnvExtendStable μ env₀ env` (knot-wide success-lifting on
prefix-bound subjects, the `CoreSub` field set including
`annotateCore` — `isPropType` reaches it).

**Pre-build check (run before writing)**: every env-consulting
clause classified —
* `find?` sites agree on prefix names by `FindPreserved`
  (supplier: duplicate-name installs rejected — no shadowing);
* presence guards (`natLitSupported`/`strLitSupported`/
  `natOpGuard`/`isUnitLikeTy`/`reservedBasisNames`) are
  `find?`-monotone or static; an env₀-SUCCESS pins them, so
  success-lifting never sees a guard flip (the flip direction only
  strands failures, which (E) does not lift);
* stuckness sites (`unfoldDefinition … = none` inside loop legs)
  agree because the run's reachable name set stays inside env₀:
  subject consts by the `ConstsBound` premise, stored-material
  consts by the env closure fact (its exact clause form — which
  `ConstantInfo` fields carry exprs — is fixed at the discharge
  seal, read off the induction's own sites);
* no clause consults the env wholesale.

**Premise suppliers named** (the ruling's explicit check):
`ConstsBound` for declared TYPES and for VALUES has ONE supplier —
the install traversal (install typechecks every declaration;
inference visits every const leaf; unknown constants throw), so
type-boundness is not a separate fact; recursor-rule RHSs ride the
RecRulesOk fold facts; fvar-closedness (the earlier ledgered
value-closedness) remains a SEPARATE fact for a different consumer
(δ leaf preservation).  Discharge route: the `CoreSub`-pattern
oracle-extension induction (the `KnotFuelMono` precedent, batched
the same way), internal motive strengthened with output-boundness.
(E) joins `DeltaSortLinked` and `BoolCtorsInert` as install-tier
obligations: discharged once, consumed wherever a prefix cert needs
lifting.

### Collapse tier opened: extraction + instantiation zip landed

**`CertZip` amended before its first theorem — the pre-build check
again**: the slack premises were `isEquiv`-form verdicts, but the
instantiation theorem cannot produce them (`isEquiv` is a partial
decision procedure with no completeness or subst-congruence); the
honest premise is **eval-form** (`∀ φ', u.eval φ' = v.eval φ'`,
pointwise map-form for `constSlack`), which `isEquiv_sound` supplies
wherever a verdict exists and which the discharges consume directly
(they only ever need eval facts).  Also added: the `fvar` congruence
constructor — `instantiateLevelParams` crosses annotations.

Landed and proved: `substFn_eval_congr` (pointwise eval-equal
substitutions induce one assignment), `certZip_instantiate` (one
template at two pointwise eval-equal instantiations lands in the
zip — the δ-case's bridge from the spine's `isEquivList` verdict),
`defEqList_extract` (per-argument `defeq` runs + the length
equation from a spine certificate).

Next: the flagged mechanical amendment — the (A)-motive gains the
concrete cross-pairing thread ((B)'s proved pattern, the
`PairedPreserve*F` species as hypotheses), `SpineSortAgree` /
`DeltaSpineSortAgree` gain `PairedLeaves` premises — then
`deltaSpineSortAgree_of` collapses the core onto
`ZipWhnfSortAgree` (mkAppN zip fold + `certZip_instantiate` at the
head + `.cert` leaves from `defEqList_extract`).

### The both-δ core COLLAPSED onto the summit

The flagged mechanical amendment landed first: the (A)-motive now
threads concrete cross-`PairedLeaves` ((B)'s proved pattern — the
`PairedPreserve*F` species as hypotheses of the whole (A) chain,
uniform with (B); `SpineSortAgree`/`DeltaSpineSortAgree` carry the
pairing at pre-core/head-normal subjects; `spineSortAgree_of` steps
it with `hLC` + symm).  Then the collapse:

* `evalEqList_map` — `isEquivList` soundness in the map form
  `constSlack` consumes;
* `certZip_mkAppN` — the spine fold (zipped head + pointwise `.cert`
  leaves stays zipped; the cons-getElem coercions are definitional,
  no simp);
* `deltaSpineSortAgree_of` — **the core discharged**: the spine
  facts zip the pair (`mkAppN_getApp` reconstruction, `constSlack`
  head, `defEqList_extract` leaves) and `ZipWhnfSortAgree`
  concludes.  Q is absorbed (`_hQv` — the zip tier is Q-free as
  audited).
* `ensureSortAgreeR_of_summit` — the frontier composite: the (A)
  primitive with the spine leg live modulo the summit claim.  (The
  trio legs still route through the refuted transport species
  pending the semantic discharge — tracked in the composite's
  docstring.)

Recipe note (three rounds): implicit-∀ Props eta-expand and
mis-instantiate at BOTH ends of an application — pin `(φ := φ)`
`(Q := Q)` at the producer AND the consumer, and ascribe
intermediate `have`s.

Remaining on the defeq branch: the semantic trio discharge (Q-frame
+ univ separation), the summit induction itself, the (B)-tier
collapse onto `ZipSortOfAgree`, and the install-tier facts
(`BoolCtorsInert`, `DeltaSortLinked`-shape inside the summit's δ
case via (E), the preserver suppliers).

### The public claims COLLAPSE onto the summit — the consumer set is final

The (B)-tier surgery turned out maximal: the `.cert` leaf absorbs
the entire top level.  A certified pair IS a zipped pair, so
`ensureSortAgreeRQ_of_zip` and `sortOfAgreeRQ_of_zip` derive both
public claims from the summit claims alone (one-liners; the (A)
entry peels its `whnf` runs to loop form; `Q` is absorbed — the zip
tier is Q-free as audited).

The landed 25-case shells are thereby SUPERSEDED as discharge routes
but deliberately kept: their case work is the summit induction's
`.cert`-case template.  The mutual knot's final shape: the summit
induction's `.cert` case decomposes the cert run exactly as the
shells do (defeqStep decomposition, re-entries by head steps,
vacuity routings, spine-to-zip), with every leaf cert at strictly
smaller knot fuel feeding the induction hypothesis — no separate
(A)/(B) claims in the mutual recursion at all.  The refuted
transport species and the dead `sortOfLE_step_*` instances now sit
ONLY inside superseded conditionals.

Summit consumer set, FINAL: `ZipWhnfSortAgree` + `ZipSortOfAgree`
serve everything downstream (`SortSubstStable`'s leaf via (B),
`EnsureSortAgreeR`'s consumers via (A), the trio's semantic
discharge stays on the (A)-shell's Q-channel as ruled).

### The semantic trio's frame STATED (`SortCohFrame.lean`)

`PtFresh` checked first, as directed: `univ_ne_pt` already exists
(PtFresh.lean:116) — the "one-lemma gap" was in the tree before the
seal opened.  The new `V`-carrying module (SortCoh stays `V`-free)
lands `FrameSide`/`FrameQ` — the consumer's `Q`-slot instantiation:
per side, the bridge-standard guards SELF-CARRIED (pre-build check:
the `QPreserve*F` species pass no `SubjInv`, so a frame that needs
guards for its own preservation must travel with them — no shell
re-touch), the context correspondence at the consumer's `Δv`, and
denotability; `frameQ_symm` proved (the slot's symmetry
requirement, by construction).

The discharge route recorded with every supplier named:
`checkBridge` (unconditional given `EnvR` — the claims are
AVAILABLE, not hypothetical; a decisive simplification found by the
reconnaissance), loop-to-whnf lifting via `whnfLoop_budget_mono` +
`whnf_of_loop`, `DefEq.sound`/`Infer.sound` at `(ρ, hSat)`
parameters (at `d = 0`, `Sat_nil`), `mem_univ_zero` + `univ_ne_pt`
for the collision, and the preservers riding `WhnfCoreClaimsR` /
`denote_delta_step` / literal-`Bool` denotes.  The three discharge
theorems and the preservers are the semantic-trio proof seals,
scheduled after the summit induction per the granted order (the
summit does not consume them).

### THE SUMMIT MAP (sealed alone — it surfaced findings)

The full case-structure scoping map for `ZipWhnfSortAgree`'s
induction, drawn before any case work, with the measure audit
instantiated against the actual motive and the reference-graph
stress test run.  Two findings landed as statement amendments with
this seal; the rest is the build map.

**Finding 1 (amendment, landed): `.cert` carries closedness.**  The
β case substitutes into zip derivations; a cert leaf's run does not
survive substitution — UNLESS the leaf pair is bvar-closed, in which
case `instantiate1` leaves it verbatim (closed subterms are
untouched, no shifting).  So `.cert` now demands
`looseBVarsBounded 0` both sides; every consumer had the fact in
hand (the public-claim guards; spine args via the new
`getAppArgs_bounded`).  With it, whnf's depth-stability closes the
original cliff completely: whnf never enters binders, so an
under-binder cert leaf surfaces only through β at the SAME depth,
verbatim.

**Finding 2 (map): the two substitution lemmas.**  The β case needs
(i) `certZip_instantiate1`: one template body, two closed zipped
args — `CertZip a₁ a₂ → CertZip (e.instantiate1 a₁)
(e.instantiate1 a₂)` (structural on `e`; the `refl` leaf of a body
zip does NOT survive substitution — this lemma is what replaces it);
(ii) the full form `CertZip body₁ body₂ → CertZip a₁ a₂ →
CertZip (body₁[a₁]) (body₂[a₂])` (induction on the body zip;
`refl` case = (i); `cert` case = verbatim by closedness).

**The case map** (`CertZip.rec` × the dual given runs):
* `refl` — `whnfLoop_det` (base).
* `sortSlack` — both runs stuck at the sorts (`loop_stuck_out`),
  `hev φ` (base).
* `cert a b _ _ hc` — THE SHELLS' TEMPLATE: `hc` at `fc+1` opens to
  the defeqLoop decomposition; re-entries by given-run surgery;
  vacuities routed (the trio Props stay hypotheses — semantic
  tier); nat via `natStepNoSort_of`; terminal shape cases vacuous
  by `loop_stuck_out`; **spine** = `deltaSpineSortAgree_of`'s zip
  construction feeding the ih at `fc` (< `fc+1` ✓).
* `constSlack` — both sides step identically: `whnfCore_const_run`,
  `reduceNat_const`; unfold: SAME head, so both unfold or both
  stick (the length guards agree via `hev`'s map-length); both-δ
  continuations are `certZip_instantiate` zips of ONE stored value
  (`hev` ✓) — recurse at same `fc`, smaller loop budgets.
  **(E)'s δ-link consumer DISSOLVED in the subject form**: same-head
  δ needs no install cert — the zip replaces the pinning route.
  ((E) stays on the ledger for the type form / other consumers,
  re-audited when `ZipSortOfAgree` is mapped.)  Needs the env fact
  `StoredWF` (stored values closed + leaf-free) for the
  continuations' `SubjInv`/pairing — the already-ledgered family,
  consumed directly here.
* `fvar` — both stuck (fvar is whnfCore-inert, `reduceNat_fvar`,
  `unfoldDefinition_fvar`) — never reaches a sort: vacuous.
* `lam`/`forallE`/`letE`(?)/`proj`(?) at TOP level — lam/forallE
  stuck-shape vacuous; letE reduces by zeta (lockstep — zipped
  bodies/values substitute by Finding 2); proj recurses through the
  proj clause (the simulation tier).
* `app` — THE SIMULATION TIER: whnfCore on zipped apps, lockstep
  through the body's clauses at knot fuel `ga-1` (the internal
  `r`-calls run one knot level down — `whnfCore_succ` — which is
  what pays for β-regrowth).  Sub-clauses to route as named
  obligations at their own seals: β (Finding 2 + each side's own
  arg-cert, asymmetry disciplined by the given runs), iotaRec
  lockstep (recursor-headed zipped spines CAN reach sorts —
  Type-valued recursor applications — so the iota lockstep is
  load-bearing; big sub-map: rule lookup same-recursor, majorToCtor,
  K/structure rescues), proj/projLitToCtor lockstep, and the
  stuck-output collision legs.

**The measure, stress-tested** (the ceiling lesson):
lexicographic **[cert fuel `fc`, knot fuels `ga+gb`, loop budgets
`la+lb`, zip structure]**.  Per case: cert/spine — `fc` ↓ (runs may
be reassembled at grown knot fuel: lex absorbs); constSlack both-δ —
`fc` =, knot =, loop ↓; simulation recursion — knot ↓ (internal
calls at `ga-1`; β-regrowth paid HERE — the fueled knot exists for
exactly this); congruence descent inside one whnfCore call — zip
structure ↓ at equal fuels.  No manufactured runs anywhere: every
consumed run is given, decomposed-from-given, or
assembled-from-decomposed (the landed spine pattern).  The
reference-graph test finds no cycle: the only cross-references are
cert→zip (fc ↓) and zip→zip (later components ↓).

**Build order at natural boundaries**: (1) the substitution lemmas
(Finding 2); (2) the outer skeleton (refl/sortSlack/fvar/lam/forallE
bases + the constSlack case, with the simulation and cert cases
routed as named Props); (3) the `.cert` case on the shells'
template; (4) the simulation tier clause by clause (β, then proj,
then iota — each its own seal); (5) `ZipSortOfAgree` mapped
separately after the subject form lands (its infer-level simulation
is a different walk).

### Summit build, tier 1: substitution pair + the sort-sort inversion

Build-order steps 1 and (part of) 2, landed and proved:

* `instantiate1_bounded` — substitution leaves bounded expressions
  verbatim (`j ≤ k` generalization for the binder crossings); the
  closed-cert-leaf engine.
* `certZip_instantiate1` — Finding 2(i): one template, two zipped
  closed args (structural; the `refl`-leaf replacement).
* `certZip_subst` — Finding 2(ii): zipped bodies at zipped args stay
  zipped, by induction on the body zip (`refl` by (i), `cert`
  verbatim by closedness — Finding 1 paying off exactly as mapped,
  congruence structurally; `fvar` is free because `instantiate1`
  leaves annotations untouched).  The β case's engine is done.
* `proofIrrel_sorts_absurd` / `stuckIrrel_sorts_absurd` — the
  probe/rescue walks at literal-sort subjects (the house extraction
  patterns; the five-way walk collapses fast because literal
  scrutinees pre-reduce every shape match).
* `isDefEqCore_sorts_eval` — **the sort-sort cert inversion**: a
  certified pair of literal sorts has eval-equal levels.  The
  decomposition needed only 10 arms — the other 15 `PostCoreCert`
  constructors are eliminated by index unification on the
  literal-sort pair (shape-mismatched indices never produce goals).
  This is the summit's stuck-stuck terminal AND the cert case's
  base.

Next per the build order: the outer skeleton — the loop-step
decomposition of both given runs against the zip, with the
zip-preservation step Props (`ZipWhnfCoreStep` etc.) and the cert
case routed; then the cert case on the shells' template; then the
simulation clauses (iota with the full pre-build treatment).

### Summit build, tier 2: THE SKELETON LANDED

`zipWhnfSortAgree_of` proves the summit claim from five routed case
Props, by the one lexicographic induction (outer `Nat.strongRecOn`
on the cert fuel, inner on the loop-budget sum), with `ZipBelow` as
the continuation contract (the house's continuation pattern — the
recursion travels as a premise, so the cases seal separately WITHOUT
sorries or claim-level circularity).

Inline and proved: `refl` (determinism), `sortSlack` (both runs
stuck at the literal sorts + the eval premise), and the stuck-shape
vacuities `fvar`/`lam`/`forallE` (one-sided `loop_stuck_out` with
the two new value-branch run lemmas `whnfCore_fvar_run`/
`whnfCore_lam_run`; `lit` rides `refl`).

Routed (each with `ZipBelow μ env φ fc (la+lb)` as premise):
* `ZipCertCase` — the shells' template (build step 3);
* `ZipConstCase` — the both-δ same-template case; its supply kit is
  the newly-STATED `StoredWF env` (stored defn/thm values fvar-free,
  bvar-closed, leaf-bounded — the ledgered value-closedness family
  in the form the summit reads) plus three instantiation-
  preservation lemmas (fvarLeaves/looseBVars/LeavesBounded under
  `instantiateLevelParams`);
* `ZipAppCase` / `ZipLetECase` / `ZipProjCase` — the sim roots (the
  knot-fuel tier; letE joined the sim because whnfCore zetas on
  demand — `r.whnfCore (b.instantiate1 v)` at one knot level down).

Pre-build check results folded into the routing shapes: a uniform
`ZipWhnfCoreSim` over all zips is UNPROVABLE (cert-headed pairs'
whnfCore outputs are not zip-able without constructing runs — the
run-mirror bar), so the sim is rooted per shape and the cert case
goes through the template; the cert case's own output-pair analysis
needs NO zip extension (syn→refl, sorts→sortSlack, spine→the landed
construction, consts→constSlack; fvars/lams/pis/packing pairs all
vacuous via their lit/stuck sides — the proposed packing-slack
constructors were killed by their own check); the app-with-cert-HEAD
sub-case is the mutual knot with binder opening (the Θ tier),
flagged for full treatment at its seal.

### Summit build, tier 3: the cert case DISCHARGED on the extracted template

The audit correction first (the pre-build check firing on my own
audit): **the "zip tier is Q-free" claim was WRONG** — the trio legs
INSIDE the cert case need the vacuity Props, whose only discharge
route is semantic (FrameQ), so the summit tower threads Q after all.
The saving grace, verified before amending: the landed preservers
cover every Q-evolution the summit performs (both-δ = two left-δs +
symm; β and zeta ride `QPreserveCoreF` because they happen inside
whnfCore; no new species).  The claims, `ZipBelow`, the five case
Props, the skeleton, and the collapse corollaries are all
Q-threaded; the corollaries got CLEANER (the public claims' Q now
lines up with the summit's instead of being absorbed).

Then the refactor that prevented ~200 lines of duplication: the
(A)-shell's `main` is extracted as **`certLoop_sortAgree`** — the
cert-loop template at a fixed knot fuel, with the spine handler as
the named-def hypothesis `SpineHandler μ env φ Q fc` (the def
wrapper defeats the implicit-∀ eager-opening disease; raw-∀
parameter types get opened at application sites — recipe confirmed
a third time, now with the fix of naming the seam).  The shell
consumes it with `hS`; **`zipCertCase_of`** consumes it with the
zip-and-recurse handler: post-core heads from the spine cert,
dual-success runs assembled via `whnfCore_reidem_const` +
`whnfStep_assemble_delta`, the pair zipped (`constSlack` head,
`.cert` leaves from `defEqList_extract`, closedness from
`getAppArgs_bounded`), and `ZipBelow` fed at `Or.inl
(Nat.lt_succ_self fc)` — the cert-fuel decrease, exactly the
measure's primary component.  Compiled first-pass.

**The summit's remaining obligations**: `ZipConstCase` (StoredWF
kit), the three sim roots (`ZipApp`/`ZipLetE`/`ZipProjCase` — iota
with full treatment), the vacuity Props (semantic tier), and the
env facts.

### Summit build, tier 4: the constSlack case DISCHARGED (StoredWF kit)

The supply kit, all proved: `instL_fvarLeaves_nil` /
`instL_looseBVarsBounded` (level instantiation creates no fvar
leaves and touches no bvars), `wScoped_of_fvarLeaves_nil` /
`subjInv_of_nil` / `pairedLeaves_of_nil` (the fvar-free `SubjInv`
package), and `unfoldDefinition_const_both` — both instantiations of
a same-head δ unfold TOGETHER (the guard reads only the length,
which the eval premise pins via map-length), yielding the one stored
value and both instantiation forms.

`zipConstCase_of` then discharges the case: decompose both given
runs one step (det-align against `whnfCore_const_run`); the nat legs
die on `reduceNat_const`, the stuck legs on the sort-vs-const clash;
in the both-δ leg the continuations are `certZip_instantiate` zips
of ONE stored value, with invariants from the kit (`StoredWF` the
consumed env fact), `Q` stepped by two left-δs + symmetry, and
`ZipBelow` fed at `Or.inr` — same cert fuel, strictly smaller
loop-budget sum, exactly the measure's second component.  The
cross-legs (one side unfolds, the other stuck) are killed by the
both-unfold lemma.

WF-def recipe consolidated (cost three rounds): `getAppFn`/
`getAppArgs`/`mkAppN`/`fvarLeaves`/`WScoped`/`instantiateLevelParams`
never reduce by `rfl`/`nomatch` — close leaf goals with their
equation-lemma simps, reduce literal-scrutinee matches with
`simp only []` after every `rw [hf] at`, and remember `cases hf :`
substitutes the goal (third confirmation), so find?-equation
components become `rfl`.

**Summit remaining**: the three sim roots (`ZipApp`/`ZipLetE`/
`ZipProjCase` — iota's full pre-build treatment when reached), the
semantic vacuities, `StoredWF`+`BoolCtorsInert` install discharges.

### Sim-tier map: the three roots FUNNEL into one workhorse (finding)

Opening `ZipLetECase` per the granted order, the pre-build check
found the map's root-by-root framing wrong: **the sim tier does not
decompose by root**.  The letE contractum `b[v]` (a `certZip_subst`
zip) is an ARBITRARY zip shape — including cert-headed apps — so the
letE case needs the same whnfCore lockstep as the app root; proj
likewise funnels through it (the scrutinee's whnf + the table
steps).  The three routed cases are thin wrappers over ONE
workhorse:

**The workhorse (to be stated with the full pre-build treatment —
next session's charter)**: the whnfCore lockstep on zipped pairs,
its own induction on the KNOT fuel of the given runs (the map's
"fueled knot pays for β-regrowth" insight), zip-in / zip-out on the
head-normal outputs, THEN the loop-level tri-analysis on zipped
head-normal pairs (nat/δ/stuck agreement by shape) feeding
`ZipBelow` at the smaller loop budget (`Or.inr` — the la-decrease
happens at the LOOP layer, not inside the workhorse).  Its terminal
collision is `certZip_sorts_eval` (LANDED this seal: only
`refl`/`sortSlack`/`cert` relate two literal sorts, the last through
`isDefEqCore_sorts_eval`; eight constructors eliminated by index
unification).

**The workhorse's audited hard cases** (the pre-build inventory for
its statement seal):
* cert-headed redexes (an app/letE position whose head zip is
  `.cert`) — whnfCore outputs of cert-related heads are not
  zip-able without decomposing the CERT (the mutual knot with
  binder opening; PostCoreCert's lamCong exposes opened-body certs
  — the Θ tier).  The workhorse's statement must route this as its
  own named case (disjunctive conclusion or a routed Prop), NOT
  claim totality over all zips (that shape was already killed once).
* the iota lockstep (recursor-headed zipped spines) — the full
  pre-build treatment as directed: iotaRec's clause surface
  (rule lookup at the same head, majorToCtor, K/structure rescues,
  projLitToCtor), the nat-op porosity in lockstep, and the
  struct-name slack flagged at the proj map.
* zeta inside the lockstep = `certZip_subst` + recursion at knot-1
  (measure ✓).

The letE/app/proj case Props stay as stated (they are the correct
seams); their discharges wait on the workhorse.  Next in order:
the workhorse statement seal (with the Θ/iota maps), then the three
wrapper discharges, then the semantic vacuities and install facts.

### Workhorse statement seal, part 1: the Θ zip-out REFUTED; measure extended

The full pre-build treatment opened on the workhorse and produced a
second refutation before any statement was frozen: **even a ROUTED
Θ-Prop promising zip-out is refutable.**  β under cert-related λs
(the lamCong decomposition of a `.cert` head) yields contracta
related only through the OPENED-body cert at `d+1` — no run exists
on the substituted forms, and constructing one is the run-mirror
bar.  So the lockstep cannot promise zipped outputs past a cert
head; the Θ seam must exit at the CLAIM level (eval-conclusion with
`ZipBelow`), and the workhorse family is CLAIM-SHAPED throughout —
the same architectural correction the uniform sim already took, now
forced one level deeper.  (Its eventual discharge is the mutual
knot with binder opening — the SimSubst/Θ-motive machinery, the
arc's final deep work, exactly as the module docstring's trap list
promised: the fvar-annotation-divergence apparatus.)

Landed this seal — **the measure extension** (prerequisite for any
sim-tier work): `ZipBelow` is now the THREE-component lex
`[cert fuel fc, knot-fuel sum ga+gb, loop-budget sum la+lb]`; the
skeleton gained the middle `Nat.strongRecOn` layer; the five case
Props carry the extended contract; the landed discharges adapt
(cert/spine at `Or.inl` unchanged; constSlack's continuation at
`Or.inr ⟨rfl, Or.inr ⟨rfl, ·⟩⟩` — same knot, smaller loop).  The
sim tier's internal recursions (whnf-of-major inside iota at
knot-1 with FRESH inner loop budgets) now fit: knot strictly
decreases, loop resets under it.  Compiled first-pass.

**Iota lockstep surface, read** (for the workhorse statements):
same recursor + zipped spines agree on the rule lookup (major's
ctor head), the arity/level/comparand guards run per side
(dual-success), and the OUTPUT is `mkAppN (rhs[us/us'])
(prefix-args ++ major-fields)` — `certZip_instantiate` + zipped
args + zipped major-fields, PROVIDED the major-whnf lockstep
(recursion at knot-1, Θ-routed when the major zip has a cert head).
`litMajorToCtor`/`projLitToCtor` expand identical literals to
identical programs (refl-zips through det).  `majorToCtor` (K and
structure-eta rescues) still unread — its lockstep map is the next
session's first read, before the workhorse statements are frozen.

### The majorToCtor lockstep read — the last unread surface, mapped

Read in full before freezing (the record's rule).  Findings for the
workhorse statements:

* **K-rescue and 0-field eta fires are major-INDEPENDENT**: both
  rescues fabricate 0-field constructors, so `margs.drop ctorParams
  = []` and the fired output is `mkAppN (rhs[us]) (args.take rP)` —
  the recursor's own zipped prefix only.  The hardest-looking
  rescue cases contribute NOTHING to the output zip beyond
  `certZip_instantiate` + the already-zipped spine.  (The rescue's
  internal certs — proofIrrel, the fabrication defeq, iotaCerts —
  run per side; dual-success needs no cross-side facts from them.)
* **Field-ful eta rescue**: the fired output's fields are
  projection-function applications TO THE MAJORS (`etaFabArgs`), so
  the output zip needs the major zip (congruence) AND the level
  instantiations `ust₁/ust₂` from the two `whnf (infer major)`
  runs — for congruence-zipped majors this rides the INFER lockstep;
  for cert-leaf majors it is the Θ seam (same family as cert heads).
* **Asymmetric divergence is vacuous by the stuck side's own run**:
  if one side rescues/fires and the other stays stuck, the stuck
  side's whnfStep ends at a recursor-headed app (iotaRec none,
  recursors never δ-unfold) — a non-sort loop output contradicting
  its given sort run.  The lockstep need only handle symmetric
  progress; every asymmetry exits vacuously.  (The audited
  "given runs discipline asymmetric stages" principle, now doing
  the rescues' work.)
* **The INFER lockstep joins the family**: `majorToCtor` and the
  eta fields consume `whnf (infer major)` on zipped majors, so the
  workhorse family mirrors the knot: lockstep Props for whnfCore,
  whnf/loop, infer (and iotaRec/majorToCtor as internal lemmas),
  all claim-shaped, all at the three-component measure, cert seams
  exiting to Θ.  This was always the summit's true form — the (B)
  map's "infer preserves zip" question and the sim tier's funnel
  are the same object.

**The workhorse statement freeze is next** (fresh runway): the
family's Props, the Θ-Prop (claim-shaped, cert-seam premises), the
vacuity-by-stuck-side inline pattern, and the audit against this
completed surface.  Everything below the freeze is enumerated:
three wrapper discharges, the semantic vacuities, `StoredWF` +
`BoolCtorsInert` install discharges, and the (B)-type-form map.

### The workhorse FROZEN: claim-shaped throughout, one Θ seam

The freeze, audited against the completed surface.  The architecture
that survived every check:

* **No separate lockstep-Prop family is needed.**  The B-vs-cert
  split (cert-free zips admit zip-out; cert leaves do not) is
  performed by `cases` on the zip DERIVATION inside the wrapper
  discharges — a stratified `CertZipB` inductive was drafted and
  discarded (it would only duplicate the constructors; the
  derivation analysis is free).  Zip-out exists LEG-LOCALLY (a
  lemma per symmetric leg), never as a standing claim — the two
  refutations (uniform sim; routed zip-out past cert heads) fixed
  this shape, and the guard-verdict question (`isNeverZero` on
  eval-equal instantiations — read, neither refuted nor needed)
  confirms it: asymmetric legs are vacuous by the stuck side's
  given run at the CLAIM level, so verdict-invariance never needs
  proving.
* **`ZipCertSpineCase` LANDED** — the one routed hard case: a
  cert-related head pair under pointwise-zipped spines, dual
  sort convergences, `ZipBelow` in hand.  `as = []` is
  `ZipCertCase` (discharged); the nonempty tier is the Θ-motive
  obligation (opened-body certs at `d+1` vs substituted forms —
  the binder-opening apparatus).
* **The infer-lockstep statements are deferred to need**: the
  wrapper discharges will state their per-shape infer lemmas
  leg-locally with their own pre-checks (the eta-rescue and
  app-clause consumers), rather than freezing a refutable general
  form.

**The branch's complete remaining ledger, in dependency order**:
(1) the three wrapper discharges (`ZipApp`/`ZipLetE`/`ZipProjCase`)
— derivation-cased, B-legs by leg-local zip-out + `ZipBelow`,
cert-legs to `ZipCertSpineCase`, iota/majorToCtor by the mapped
lockstep with per-side guards; (2) `ZipCertSpineCase`'s Θ-motive
discharge; (3) the semantic vacuities (`SortCohFrame`'s route, zero
unbuilt suppliers); (4) `StoredWF` + `BoolCtorsInert` install
discharges; (5) the (B) type-form map (`ZipSortOfAgree`'s own
skeleton on the same architecture).  Nothing else remains on the
defeq branch.

### ZipAppCase opened: the discharge's induction structure resolved

The pre-discharge analysis (run before any case work, as practiced)
settled the one open structural question — **where the β leg's
measure decrease lives**:

* The β contracta's loop runs assemble at the SAME [knot, loop]
  budgets as the app's (the tri pieces cannot be lowered), so the
  claim may NOT recurse at the contracta via `ZipBelow` — that leg
  would not decrease.
* The resolution: the wrapper's discharge is ONE claim-shaped
  induction over **[the head-zip derivation structure, the knot
  fuel of the given whnfCore runs]**, analyzing the whnfCore-app
  clause inline.  The internal core runs (head normalization,
  contracta) sit at knot `ga-1` (`whnfCore_succ`) — the knot pays
  for β exactly as the measure audit said — and `ZipBelow` is
  consumed only at the TRI legs (nat/δ continuations at `la-1`,
  the loop component) and the Θ/cert exits (the fc component).
  Zip-out for the contracta is `certZip_instantiate1 hx` at
  refl-heads (one body, two zipped args — the lemma built for
  exactly this), and leg-local elsewhere.
* The head-zip derivation-case map: `.cert` → `ZipCertSpineCase`
  at `as = [x₁]` (the mkAppN-singleton massage); `.refl` →
  det-synchronized analysis (same head normalization both sides;
  β by instantiate1-zip; iota by the mapped lockstep; stuck by the
  shape clash); `.app` (nested spines) → the induction recurses on
  the head zip (structurally smaller derivation); `.constSlack` →
  the iota/δ legs at same-name heads; other constructors are
  shape-vacuous heads (sortSlack/fvar/lam/forallE/letE/proj heads:
  the app's whnfCore leaves them stuck or reduces past them
  symmetrically — each a small leg).
* Leg-local extraction lemmas to build at the discharge seals (the
  sanctioned deferred tier): the whnfCore-app run's internal
  decomposition (head-run + cert-if + contractum-run extraction,
  the house cases-with-rw pattern at `whnfCoreBody`), and the
  per-shape infer lemmas where the eta rescue needs them.

The discharge campaign proceeds from this structure; nothing about
it is unmapped.

Addendum, same seal family: `whnfCore_app_decompose` LANDED — the
four-way internal decomposition (fired β with the argument cert /
stuck β / fired iota / stuck iota, head run at knot `g`).  The
house extraction pattern; the `cases hio :` goal-substitution recipe
made the equation components `rfl`.  The not-lam fact of the iota
legs is deliberately not carried (deferred to need — re-derivable
from the zip's shape analysis if a leg wants it).

### ZipAppCase brick 2: the fc-only contract + the zeta step

Preparing the inner induction, the cert-leg analysis found
`ZipCertCase`'s below-parameter stronger than its proof consumes:
`zipCertCase_of` feeds ONLY strictly-smaller cert fuel (the spine's
`Or.inl`), so demanding the full three-component contract blocked
consumers sitting at unrelated knot/loop positions (the inner
cert-leg assembles loop runs at budgets EXCEEDING its caller's).
Landed: `ZipBelowFc` (the fc-only contract), `ZipCertCase` weakened
to it (weaker premise = stronger Prop; the discharge unchanged
modulo the wrapper), the skeleton supplying it by restriction.  Any
consumer at any measure position can now invoke the cert machinery
on an assembled certified pair — the inner induction's cert leg is
unblocked.  Plus `whnfCore_letE_step` (zeta is one knot level down,
an `Iff.rfl` through `whnfCore_succ`).

### ZipAppCase brick 3: the spine view + the Θ contract aligned

`certZip_app_view` LANDED: every zip flattens to a head zip over
pointwise-zipped argument lists, the head either a certified pair
(possibly app-shaped — Θ's territory) or a NON-application zip node
(refl-of-getAppFn, slack, or congruence — the terminating heads for
the inner induction's case analysis).  With it, the inner
induction's app case dissolves: nested app-zips never need their own
case — the analysis always works on the flattened view, whose head
cases are exactly {refl, cert→Θ, constSlack→iota/δ,
lam-congruence→β via `certZip_subst`, shape-stuck}.  Supporting kit:
`getAppFn_not_app`, `mkAppN_append_one`, and the self-contained
append-indexing helpers (`getElem_append_left'`/`getElem_append_last`
— core lemma names shift across toolchains, so the two five-liners
are cheaper than name roulette).  `ZipCertSpineCase`'s below also
weakened to `ZipBelowFc`, aligned with the cert case.

Recipe: inside anonymous constructors, ALWAYS parenthesize lambda
components — an unparenthesized `fun … => body, next, …` swallows
the following components into a tuple body (cost one round).

The inner induction now has every brick: the four-way decomposition,
the spine view, `certZip_subst`/`_instantiate1`, the fc-only cert
exit, the zeta step, the sorts terminal.  Next seal: the induction
itself.

### The three wrappers DISCHARGED — the summit at TWO sim obligations

Designing the inner induction top-down produced the final collapse
before any induction was built: **every non-cert wrapper is
view-plus-dispatch.**  A letE or proj pair is a NON-application head
with an empty spine in the flattened view, and an app pair's view
exposes either a cert head (→ Θ) or a non-app head over a spine — so
one final routed Prop covers everything:

* `ZipSpineFlatCase` — the flat-spine leg: a non-app head zip over
  pointwise-zipped spines with both sort convergences.  Its
  discharge is the F-driven analysis (refl heads det-synchronized;
  lam-congruence β through `certZip_subst`; constSlack through the
  iota/δ lockstep — where the iota map lives; shape-stuck
  vacuities).
* `zipAppCase_of` = view + rw + dispatch (cert head → `hΘ` with the
  wrapper's own runs — no assembly needed at the root; else →
  `hSpine`).  `zipLetECase_of` / `zipProjCase_of` = one dispatch
  each at the empty spine.  The planned inner induction DISSOLVED
  into the flat-spine leg's future discharge — no nested motive was
  ever built.
* `zipWhnfSortAgree_of_two` — the frontier composite: the summit
  from {Θ, flat-spine} + the trio's Q-frame vacuities + the env
  facts + the preservers.  Every structural case of the summit
  skeleton is now discharged.

Elaboration recipes reconfirmed: pin `(F₁ := …)` when not-app
lambdas elaborate before unification pins the head; pin
`(φ := φ) (Q := Q)` at every chained composite.

**The defeq branch's remaining obligations, final form**:
`ZipSpineFlatCase` (the F-driven spine analysis — iota's full
treatment lives here), `ZipCertSpineCase` (the Θ motive), the
semantic trio (frame route, zero unbuilt suppliers), `StoredWF` +
`BoolCtorsInert` (install tier), the preserver/transport suppliers,
and the (B) type-form map.

### Flat-spine bases kit LANDED

The shape-stuck legs' entire supply, proved:

* `certZip_mkAppN_zips` — the pure congruence fold (zipped head
  under pointwise-zipped args; no cert leaves manufactured) — the
  δ-continuation zip for same-template spine unfolds.
* `iotaRec_none_of_fn_not_const` / `unfoldDefinition_none_of_fn_not_const`
  / `reduceNat_none_of_fn_not_const` — the three step functions all
  gate on a const head; non-const-headed subjects are inert at every
  step kind (each a split + shape refutation).
* `whnfCore_mkAppN_inert` — **spine inertness**: a stuck, non-λ,
  non-const-headed head keeps its whole spine whnfCore-stuck, with
  the honest fuel bookkeeping (one knot level per spine layer —
  the parametric bound `hd + as.length ≤ g` threads through the
  generalized-head induction).  Proof note: a variable-scrutinee
  match with a catch-all arm is definitionally stuck even under a
  not-lam hypothesis — the ten-way shape `cases` is the honest form
  (lam dies on the hypothesis, const on the head condition, the
  eight inert shapes reduce uniformly).

With this kit, the flat-spine discharge's sortSlack/fvar/forallE/
lam(stuck)/lit-headed legs are one `loop_stuck_out` each; the
remaining legs are: refl-const/constSlack δ (the both-unfold spine
extension + `certZip_mkAppN_zips` + `ZipBelow` at loop-decrease),
the β-chain (reassociation + spine-length induction), iota
(the standing full treatment), letE-under-spine zeta, proj, and the
nat-op fired-side vacuities.

### The flat-spine leg DISCHARGED to its four head cases

The mechanical stretch, batched per the grant.  Landed and proved:

* `mkAppN_cons_app` (nonempty spines are app-shaped),
  `mkAppN_bounded_head` (the head inherits the bvar bound), and
  `spine_inert_out` — the inert-spine loop terminal (one call
  packages `whnfCore_mkAppN_inert` + the three none-lemmas into
  `loop_stuck_out`).
* The four routed head Props: `ZipConstHeadCase` (δ/iota/nat-op —
  the iota lockstep's home), `ZipLamHeadCase` (the β-chain),
  `ZipLetEHeadCase` (zeta under application), `ZipProjHeadCase`
  (the proj walk).
* `zipSpineFlatCase_of` — the flat-spine leg discharged: cert heads
  to Θ; const/λ/letE/proj heads (both congruence-zipped and
  refl-headed, the latter dispatching with `CertZip.refl`
  components) to the four Props; sortSlack terminal at empty spines
  (eval), and ALL stuck-shape legs (sort/fvar/forallE/lit-headed,
  cong and refl alike) vacuous by `spine_inert_out` + the
  cons-shape clash; bvar heads refuted by the bounded-0 guard.
* `zipWhnfSortAgree_of_heads` — the frontier composite: the summit
  from {Θ, const-head, λ-head, letE-head, proj-head} + vacuities +
  env facts + preservers.

Elaboration notes: `refl`'s constructor argument is index-determined
(bind `_`, case on the subject variable); qualify constructor
literals on `show`-RHS positions (dot-notation loses the expected
type there).

**The sim tier's remaining surface**: exactly the four head-case
discharges — const (δ via the both-unfold spine extension +
`certZip_mkAppN_zips` + ZipBelow; iota with the standing full
treatment; nat-op fired-side vacuities), λ (reassociation +
spine-length induction), letE (knot-paid zeta + re-view), proj (the
clause walk) — plus Θ, the semantic trio, and the install facts.

### The const head DISCHARGED to iota

The δ and nat-op legs, landed on the kit:

* `iotaRec_none_of_not_rec` (non-recursor const heads never fire),
  `whnfCore_mkAppN_const_inert` (a non-recursor const head keeps its
  spine whnfCore-stuck — the inert induction generalized to carry
  the head's `getAppFn` fact), `unfoldDefinition_spine_both` (the
  both-unfold lemma at spine level: `getAppFn_mkAppN` +
  `getAppArgs_mkAppN` reduce the spine's view, then the const
  version's argument verbatim).
* `ZipIotaCase` — the routed iota Prop (recursor-headed spines at
  eval-linked levels, the `recInfo` fact as premise; the standing
  full treatment at its seal).
* `zipConstHeadCase_of`: recursor heads route to iota; non-recursor
  heads — nat legs die on `NatStepNoSort` (the spine IS the
  head-normal form), δ legs unfold together into
  `certZip_mkAppN_zips`-zipped instantiated spines with the
  preservers carrying the invariants and `ZipBelow` at the loop
  decrease, stuck legs clash with the sorts (nil by `mkAppN`
  reduction, cons by the app shape).  First-pass.

**Frontier: {Θ, iota, λ-head, letE-head, proj-head}** + the trio +
install facts.  The iota seal's pre-build treatment is next-largest;
λ/letE/proj are smaller.

### λ-head map: the β measure gap and its resolution (finding)

The λ head is NOT a quick brick — the pre-build analysis found a
real structural gap and its resolution:

**The gap.**  After the innermost β fires, the natural recursion at
the contractum-spine pair decreases NOTHING in `ZipBelow`'s
[fc, knot, loop]: the aligned loop runs keep the original loop
budget AND the original knot (the tri pieces on the fixed outputs
run at `pureFns ga` and cannot be lowered); spine length is not
viable either (re-viewing the contractum regrows the spine — β
regrowth in spine form).

**The resolution** — the originally-designed inner lemma returns,
now with its precise role: a FIXED-CONTEXT knot-only induction.
Fix the loop decomposition once (outputs `(e₁,e₂)`, the tri, the
`la-1` continuations); the inner lemma speaks of zipped pairs whose
whnfCore runs land at exactly `(e₁,e₂)`, and inducts on the SUM OF
THE CORE-RUN FUELS alone: β/zeta-contractions recurse at
`(g₁-1, g₂-1)` (the contractum core runs are constructible one knot
level down — the reassociation), cert-heads ASSEMBLE loop runs from
the fixed tri and exit to `hΘ` (hypothesis-level, no measure), δ
legs exit through `ZipBelow`'s loop component (the continuations at
`la-1`), stuck shapes exit through the fixed tri analysis.  The
loop-level and core-level measures never mix — that was the error
in both previous attempts.

**New obligations surfaced** (suppliers named):
* the substitution-transport kit — `SubjInv`/`PairedLeaves` under
  `instantiate1` and spine-folding (syntactic lemmas, provable);
* **`QPreserveBetaF`/`QPreserveZetaF`** — β/zeta-contraction
  preservers for the Q-slot (genuinely NEW species: the landed
  three cover only completed whnfCore outputs, and the contractum
  is not an output; at FrameQ they discharge through the claims'
  `Red` steps — denote is preserved along β/zeta reductions — so
  the suppliers exist at the consumer);
* `whnfCore_lam_spine_decompose` — the single-subject reassociation
  (fired-β leg reconstructs the contractum-spine's core run at
  `g-1`; stuck leg pins the spine).

Build order for the tier: the substitution kit → the new species
statements (+ shells/wrapper threading if the inner lemma's exits
need them — check at build) → the reassociation → the inner lemma →
the λ/letE-head discharges.  The letE head rides the same inner
lemma (zeta = the β case at its own clause).

### Substitution kit core + the two contraction species LANDED

The tier's first two build-order steps, proved:

* `looseBVarsBounded_mono`, `wScoped_instantiate1` (fvars and their
  annotations pass through untouched; the plugged argument brings
  its own scoping), `looseBVarsBounded_instantiate1` (closed
  argument, bound drops one binder), `fvarLeaves_instantiate1_mem`
  (no leaves beyond the body's and the argument's) — the syntactic
  transport for `SubjInv`/pairing at contracta.
* `QPreserveBetaF` (carrying the β-cert premises — exactly the
  claims' β-rule premises, the FrameQ supplier's shape) and
  `QPreserveZetaF` (`ZetaEq.interp_eq` the named supplier) —
  additive hypotheses of the coming inner lemma and λ/letE
  discharges only; no shell re-threading.

Next: the reassociation (`whnfCore_lam_spine_decompose`), then the
fixed-context knot-only inner lemma, then the λ/letE-head
discharges.

### CORRECTION: the fixed-context inner lemma fails at spine-β; the peeling design replaces it

Building the reassociation, the fuel count refuted the previous map
seal's resolution: the reassembled contractum-SPINE run lands at
**equal** fuel, not one less — the innermost contractum-core does
sit one level down, but every spine layer's legs ran at their
original fuels and fuel only transfers upward, so the reassembled
top pins at `G`.  The knot-only fixed-context induction therefore
does not decrease at spine-β (it was correct only for bare
redexes).  Third measure lesson on this branch: reassociation never
decreases fuel; only PEELING does.

**The corrected design — `coreLock`, the layer-peeling lockstep**:
strong induction on the PAIR'S core-run fuel sum; subjects peeled
one app-layer at a time (never reassociated):

* subject pair `(.app P₁ y₁, .app P₂ y₂)`: head-runs at `g-1`
  (the app-decompose) → recurse on the HEAD pair (strict decrease)
  → head-outputs ZIPPED (the lemma's own conclusion) → case on the
  zipped outputs' shapes;
* both heads λ (the zip gives them CONGRUENT — lam-zip or refl):
  β-certs per side; both fired → contracta are `certZip_subst`
  zips of the ZIPPED lam components at the (possibly different)
  args, with runs at one less fuel (the decompose's fired leg) →
  recurse (strict decrease).  Mixed/stuck: seam-lift;
* conclusion is DISJUNCTIVE: `ZipPack(u',v')` (outputs zipped +
  invariants) ∨ a LIFTABLE SEAM — cert-headed flatten (Θ-shape),
  recursor-headed flatten (iota-shape), or a stuck-side witness;
  every seam lifts through app-layers because VIEW-HEADS PROPAGATE
  (the outer pair's flattened head is the inner pair's), so the
  top-level caller — which holds the loop runs — converts seams to
  `hΘ`/`ZipIotaCase`/vacuity;
* whnfCore has NO δ (δ is the loop's step), so the only in-core
  actions are β/iota/zeta/proj — the seam set is closed.

The λ/letE-head discharges then decompose their loop runs once and
run `coreLock` on the first core step; the ZipPack outcome feeds
the fixed tri analysis (`ZipBelow` at the loop decrease), the seams
dispatch at the top.  `whnfCore_lam_spine_decompose` is NOT needed
(a reassociation artifact of the dead design); the landed
`whnfCore_app_decompose` is exactly the peeling tool.

Next seal: the seam datatype + `coreLock`'s statement with the
full pre-build check, then its induction.

### The seam datatype LANDED (coreLock's exit structure)

`CoreSeam μ env fc d` — five constructors, each pre-build-checked
for liftability and top-convertibility:
* `certHead`/`recHead`/`projHead` — the flatten seams (spines over a
  certified pair / a recursor at eval-linked levels / a zipped proj
  head), converting at the top via `hΘ`/`ZipIotaCase`/
  `ZipProjHeadCase` with the caller's loop runs;
* `deadL`/`deadR` — the self-sustaining stuck packages (a core run
  to an output whose head is non-const, non-λ, non-sort — the tri
  nones and the loop-stuck follow, contradicting the side's given
  sort run).

`dead_step` (an app over a dead-stuck head is itself dead-stuck —
the ten-shape pattern once more) and **`coreSeam_lift_app`** —
seams lift through app-layers: the flatten seams append the
argument zip (the landed index helpers), the dead seams take one
`dead_step`.  All first-pass.

Next: `coreLock`'s statement + induction — the disjunctive
conclusion is `ZipPack(u',v')` (invariants free from the landed
preservers, since outputs ARE whnfCore outputs) ∨ the seam
re-based via connecting core runs (`∃ w₁ w₂ …` for the zeta/β
chain steps, so the top can `loop_align`).

### The contraction trace LANDED (Contracts + full transport kit)

The pre-build check on `coreLock`'s final statement found the last
carrier problem: Q and the invariants cannot transport through
app-CONSTRUCTION at seam-return time (no species covers building an
app around a seam subject).  The honest carrier is the contraction
TRACE: every descent the peel performs is a β/zeta at a spine-head
position — exactly the two contraction species' shapes — so the
seam-pack carries `Contracts u w₁ ∧ Contracts v w₂` and the TOP
re-derives everything from its own facts:

* `Contracts` (refl/beta/zeta, spine-positioned, transitive by
  construction; the β constructor carries the cert runs);
* `Contracts.q_transport` (via `QPreserveBetaF`/`ZetaF`),
  `.leaves_sub` (the trace only shrinks leaves — via the one-step
  `beta_leaves_sub`/`zeta_leaves_sub`), `.subjInv` (the
  substitution kit at each step, self-pairing restricting through
  the subset), `.pairing` (cross-pairing through both subsets),
  `.app_lift` (the contraction site keeps its spine position under
  one more argument — `mkAppN_append_one` juggling);
* the spine-fold helpers (`mem_fvarLeaves_mkAppN_head/arg`,
  `fvarLeaves_mkAppN_cases`, `wScoped_mkAppN_build/parts`,
  `looseBVarsBounded_mkAppN_build/parts`).

`coreLock`'s final statement is now fully determined: the seam
disjunct is `∃ w₁ w₂ c₁ c₂, [core runs landing at (u',v')] ∧
Contracts u w₁ ∧ Contracts v w₂ ∧ CoreSeam w₁ w₂` — the top
loop-aligns via the connecting runs and re-derives the conversion
package from the traces.  Next seal: coreLock's induction.

### FINDING: the seam set was not closed — refl bottoms swallow head-whnf history; the carrier gains head re-basing

`coreLock`'s granted pre-build check (fourth round) refuted the
peeling design's closure claim ("view-heads propagate; the seam set
is closed").  The counter-configuration: the peel's head-recursion
bottoms at a **refl** node (`u`'s head equals `v`'s syntactically),
which returns ZipPack by determinism — but the head's whnfCore run
may contain iota steps, so the pack ERASES whnf history.  When the
outer layer's legs then iota-fire (real: shared recursor-headed
whnf-output `F` with zipped, differing final args; a cert-blob
major even makes the fire MIXED), the natural seam subjects
`(.app F y₁, .app F y₂)` are whnf-reachable but not
contraction-reachable: `Contracts` spans only spine β/ζ, so
NEITHER disjunct of the frozen conclusion applies.  Also refuted en
route: a bare-const refl bottom over a recursor cannot return an
eagerly-shaped seam instead (same reachability gap), and
whnfCore-output idempotence as a rescue pulls in mutual whnf/unfold
idempotence — rejected.

**The repair (landed this seal)** — the carrier is the honest fix:
`Contracts` gains a spine-positioned **head re-basing** constructor
(`head : whnfCore g d P = .ok F → Contracts (mkAppN F as) w →
Contracts (mkAppN P as) w`).  Every transport re-proved:
* `q_transport` threads NEW species **`QPreserveHeadF`** (Q survives
  completing the head's whnfCore under a spine; FrameQ supplier =
  the claims' core preservation, spine-composed);
* `leaves_sub`/`pairing` thread NEW species **`LeavesSubCoreF`**
  (whnfCore introduces no fvar leaves; supplier = a Verify-tier
  mutual induction over the core family, StoredWF-backed — its own
  seal, obligation ledgered);
* `subjInv` threads `InvPreserveCoreF` + `LeavesSubCoreF` (head
  invariants via the landed spine part/build kit + leaf-subset
  restriction of the pairing);
* `app_lift` unchanged in hypotheses (`head` keeps its spine
  position under one more argument);
* `head_leaves_sub` (a head's leaf subset spreads over the spine).

**Supporting bricks (landed)**: `whnfCore_app_decompose` amended —
the iota legs now carry the deferred not-λ fact (the split's
catch-all disequalities, free); **`whnfCore_app_assemble`** (the
decompose's inverse: head run + leg package → the layer's run at
`max`-joined fuel +1; `KnotFuelMono` lifts every leg run, iotaRec
via `iotaRec_mono`+`coreSub_le`; the ten-shape pattern for the
variable-head iota legs).  Re-based seam connecting runs are
assembled with this: the seam's own head run replaces the
original's, the original legs are reused verbatim.

**Effect on `coreLock`**: statement UNCHANGED in shape — the seam
disjunct's traces are now strong enough to reach every collision:
heads-ZipPack + iota legs exit as `recHead`/`certHead` seams at
head-re-based subjects (trace = one `head` step + `app_lift`;
connecting run = assemble of the pack's own head runs... the
ZipPack outcome must therefore ALSO return the head runs it
consumed — the induction takes them from the decompose directly,
no conclusion change).  Mixed iota fire exits via the same
`recHead` seam (shape-based, fire-agnostic — `ZipIotaCase` at the
top is where fire analysis lives).  β-cert-mixed exits `deadL/R`
(the stuck output is app-of-λ-headed: non-const, non-λ, non-sort;
self-sustaining by fuel monotonicity of the failing defeq).
Q-descent through app (`Q d (.app P y) (.app R z) → Q d P R`) is
still expected as one more routed species at the induction — named
next seal.  STOP-boundary seal: the induction itself waits for the
ratifying grant.

### coreLock LANDED (the layer-peeling lockstep, first full pass)

The Q-descent species checked and named first: **`QDescendAppF`**
(`Q d (.app P y) (.app R z) → Q d P R`; at `FrameQ` the frame is
per-side structural — a defined application has defined parts).
One more species surfaced at the same pre-build check:
**`CoreIdemF`** (whnfCore idempotent on its outputs) — the
cert/rec seam exits re-base to `(.app F₁ a₁, .app F₂ a₂)` with
completed heads, and the connecting-run assemble needs the head to
re-run to itself.  Supplier: a Verify-tier mutual induction over
the core family (inert shapes re-run by `pure`, stuck legs re-pin
by fuel monotonicity, contractum outputs recurse one level down);
its own seal, ledgered beside `LeavesSubCoreF`'s.

**`coreLock`** proved by `Nat.strongRecOn` on the fuel sum, eleven
zip-node cases:
* refl → determinism pack; cert/proj → flatten seam at the raw
  subjects (empty spines, refl traces, the original runs);
* sort/const/fvar/λ/∀-nodes → `whnfCore_inert` pack (new helper:
  ten-shape identity on non-redex subjects; the body's bvar arm
  THROWS — bvar is an error shape, not inert — recorded);
* letE → zeta at one knot level (`whnfCore_letE_step`), contracta
  invariants via the carrier transports on one-step prefix traces,
  recurse, re-base the returned traces by constructor composition;
* app → peel: decompose both, recurse on the heads.  Head-seam:
  lift (assemble with the seam's connecting run + `app_lift` +
  `coreSeam_lift_app`).  Head-pack: the legs matrix — β/β recurse
  on `certZip_subst` contracta (prefix = head-step + β-step, the
  cert data from the legs); any failed β-cert side → `deadL/R`
  (mono-stable original run; the stuck output is λ-headed-app:
  non-const, non-λ, non-sort); λ-vs-iota → cert node forced (refl
  and λ-nodes refute the iota side's not-λ fact) → certHead;
  iota/iota with any fire → **`zip_stuck_spine_exit`** (new: walks
  `certZip_app_view` to the first cert layer → `certHead`, or a
  shared-name const head → `recHead` under `recInfo` /
  `absurd_rec_fire` otherwise, every non-const head shape refuting
  the fire); both-inert → app-node pack.
* The four invariants at the outputs are derived ONCE from the
  landed preservers (outputs are whnfCore outputs) — every pack
  case returns the same free package; only the zip varies.  The
  head-pack's own invariants are consumed nowhere: only its zip.

Helper kit landed with it: `pairedLeaves_mono` (pairing restricts
along leaf subsets), `subjInv_app`, `mem_fvarLeaves_app_left/right`,
`zip_args_append` (the flatten seams' append step, extracted),
`getAppFn_of_not_app`, `absurd_rec_fire`.

Mechanization notes (recurring-lesson additions): `cases` on a zip
whose subjects are pre-existing fvars or literal components
SUBSUMES the corresponding constructor fields — bind them `_` and
reference the outer names (bit three times: `refl`/`cert`/λ-node
arms); a parenthesized multiline `by`-block inside an anonymous
constructor must keep its continuation indented past the `by` —
prefer `refine ⟨?_, …⟩` + trailing tactics.

Open obligations after this seal (suppliers named): the λ/letE-head
discharges riding coreLock (decompose the loop once, ZipPack feeds
the tri analysis at the loop decrease, seams convert at the top via
`hΘ`/`ZipIotaCase`/`ZipProjHeadCase`/dead-contradiction with the
carrier transports); the `CoreIdemF` + `LeavesSubCoreF` Verify-tier
suppliers; the `QPreserveHeadF`/`QDescendAppF`/β/ζ FrameQ suppliers;
iota's full map (`ZipIotaCase`); proj head; Θ; the semantic trio;
the install facts; the (B) type-form map.

### λ/letE-head cases DISCHARGED (zipHeadDispatch riding coreLock)

`coreLock` amended first (consumer-driven strengthening): the
seam-pack now carries **`c₁ ≤ g₁ ∧ c₂ ≤ g₂`** — every exit already
satisfied the bounds (raw exits at the given fuels, recursion
passes them up by `le_succ_of_le`, assembles by `max`-arithmetic) —
so the top can mono-lift the connecting runs to the premise knot
fuels and keep the ZipBelow measure slots EXACT.

**`zipHeadDispatch`** — the shared workhorse both head cases
collapse onto (the summit claim's body with the recursion bar as a
premise, non-circular: no `hLam`/`hLetE`/flat-spine hypotheses):
one loop step decomposed per side (`whnfStep_decompose`), coreLock
on the core runs, then
* **pack**: loop runs re-assembled for the outputs by `CoreIdemF`
  + the landed step assembles (same tri, same fuel); the returned
  zip classified by `certZip_app_view`: first cert layer → `hΘ`
  (fc-descent only, measure-free — Θ at empty spines subsumes the
  bare cert exit, `hCert` never needed); const heads (refl or
  `constSlack`) → `hConst` at the very same measure (legal: a
  hypothesis, not `below`); sort heads with empty spines → the
  forced stop arms (nat legs die by `NatStepNoSort`, δ by
  fn-not-const) and the eval link; every other head shape →
  **`loop_dead_exit`** (new: nat leg by `NatStepNoSort`, δ leg by
  the head shape, stop leg by the sort equation);
* **seam**: invariants transported by the carrier kit, connecting
  runs mono-lifted by the new bounds, loop runs re-based by the
  step assembles (same tri, premise fuels — so `below` passes
  UNCHANGED to the converters); `certHead → hΘ`,
  `recHead → ZipIotaCase`, `projHead → ZipProjHeadCase`,
  `deadL/deadR → loop_dead_exit` after determinism identifies the
  dead output with the step's own.

`zipLamHeadCase_of` / `zipLetEHeadCase_of` are one-liners: build
the spine zip from the congruent head components
(`certZip_mkAppN_zips` on the λ/letE node) and dispatch.  Three of
the four flat-spine head Props are now discharged; proj remains.

Helper kit: `not_const_getAppFn_of_shape`, `mkAppN_cons_ne_sort`,
`mkAppN_ne_sort`, `mkAppN_fn_ne_const`, `loop_dead_exit`.

Mechanization notes (the implicit-∀ trap at full strength, new
variants recorded): an implicit-∀ Prop hypothesis passed
POSITIONALLY gets eta-inserted and then applied to the next
argument (`hQs` consumed `hQA`); `@`-application at the consumer
fixes the head but arguments of def-named implicit-∀ types
(`below`) still eta-insert — eta-expand them with EXPLICIT implicit
binders; a shape-lambda under an un-unified implicit head
(`nomatch` under meta-`e`) fails with "Missing cases" — wrap in
`by` so the concrete expected type resolves first, and pin
`(H := shape)` where the helper's subject is otherwise meta;
`getAppFn` on literal ctors needs the equation simp, not `nomatch`;
and the φ/Q higher-order-unification corruption (a non-pattern
`?Q := fun d e c => Q d e (const)` guess) is prevented exactly by
the recorded `(φ := φ) (Q := Q)` consumer pins.

Remaining branch obligations: proj head (`ZipProjHeadCase`
discharge), Θ (`ZipCertSpineCase`), iota (`ZipIotaCase`), the
semantic trio, `CoreIdemF`/`LeavesSubCoreF` Verify-tier suppliers,
the FrameQ suppliers (`QPreserveHeadF`/`QDescendAppF`/β/ζ),
`StoredWF`/`BoolCtorsInert`/(E) install facts, the preserver
suppliers, the (B) type-form map.

### LeavesSubCoreF supplier LANDED (Verify/LeavesPres.lean)

The established pattern paid at full value: `whnfPres_leaves`
mirrors `whnfPres_WScoped` clause by clause (the mutual fuel
induction over whnfCore+whnf), and the existing inversions turned
out to be LEAVES-AWARE already — `majorToCtor_inv`'s fallback
carries `major'.fvarLeaves.all (contains major.fvarLeaves)` in its
statement, so the major chain transports without new inversion
work.  New leaves bricks: `natLitToConstructor_leaves_nil` /
`strLitToConstructor_leaves_nil` (the WScoped-at-depth-0 trick via
`fvarLeaves_lt_of_wscoped`), `litToCtorIfNat_leaves`,
`unfoldDefinition_leaves` (stored values closed, `EnvWF`).
Essentially first-pass (one simp-shape fix).  SortCoh consumes it
as `leavesSubCore_of (henv : EnvWF env) : LeavesSubCoreF μ env` —
the head re-basing carrier's leaf transport is now supplied.

CoreIdemF's pre-build map (recorded before its build): core side
rides `whnfCore_app_decompose`/`_assemble` at EXACT fuel (head-run
idem via the fuel-level IH, legs replayed verbatim — deterministic
reads); β/iota/zeta contractum outputs recurse one level down +
mono.  Surfaced corners: (i) the whnf side needs the loop TERMINAL
extraction (the landed SortCoh lemma family) + `whnfLoopFuel` as a
successor; (ii) the proj-stuck re-run needs projLitToCtor
idempotence, whose strVal-expansion arm needs "whnf of a
ctor-headed spine is not a string literal" (ctor-head inertness
through the loop); (iii) `whnf_proj_inv` collapses the stuck
reasons, so the proj-stuck case must re-drive the body manually
(deterministic reads reproduce the same failure; fire sub-branches
conclude by the core IH directly).

### FINDING: CoreIdemF re-ledgered a refuted obligation; deleted — consumers repaired onto the R-a family

Opening `CoreIdemF`'s supplier build, the pre-build check ran into
the strLit corner — and then into the RECORD: the identical
obligation (`WhnfCoreIdem`) was refuted OUTRIGHT on this branch
(fourth catch, R-a executed, tombstone at the deletion site): an
accepted env's `String.ofList` body makes the proj-scrutinee
literal re-expansion a genuine second reduction step
("hi" ↦ "boom" ↦ "zap"), so no fuel form of whnfCore idempotence
holds.  `CoreIdemF` had been introduced two seals ago as the head
re-basing's connecting-run supplier WITHOUT checking the tombstone
— the count of caught-undischargeable statements is now FIVE, and
this one was caught at the supplier seal before any discharge
relied on it, but AFTER two consumers landed on the hypothesis.
Lesson recorded: a new obligation's pre-build check must include a
TOMBSTONE SWEEP of the ledger (the refutation was recorded in this
very file and in a source comment).

**The repair (this seal)** — `CoreIdemF` deleted (tombstone left at
its site); every consumer re-derives its head self-run from
surrounding shape facts, exactly the landed R-a pattern:
* coreLock's certExit takes the two head self-runs as premises;
  β-side heads are λ-values (`whnfCore_lam_run` — already landed in
  the R-a era, rediscovered), iota-fire sides are const-headed (new
  `iotaRec_some_head`, the none-lemma's contrapositive) →
  `whnfCore_reidem_const`;
* iota-none sides split on the head: const → reidem; NON-const →
  the branch exits `deadR`/`deadL` at the raw subjects instead (the
  stuck output is non-const-headed, non-λ, non-sort — the top
  contradicts it with the sort premise), which is exactly where the
  strLit-corner shapes land — the refutation's reach is absorbed by
  the dead seams;
* zipHeadDispatch's pack-side loop re-assembles derive the output
  self-run from the TRI: nat leg dead (`NatStepNoSort`), δ leg
  const-headed (`unfoldDefinition_some_head` → reidem), stop leg a
  sort value (`whnfCore_sort_run`) — no idempotence anywhere.

Both suppliers are now closed: `LeavesSubCoreF` by
`whnfPres_leaves`, the idem SLOT by deletion + shape-guarded
re-derivation.  The carrier and dispatch hypothesis lists shrink by
one.

### Retroactive tombstone sweep (ratified rule, applied once) + the proj/iota shared map

**Sweep result: CLEAN.**  Every live routed Prop and species checked
against the recorded refutations: all level-linking premises are
eval-form (the currency ruling; no isEquiv-producible forms); no
routed Prop promises zip-out (all conclude eval-equality — the Θ
zip-out refutation); the shells' primitives are dual-success (the
liveness refutation); `PairedLeaves` is everywhere a premise, never
run-derived (the fvar-leaf reading); the (A)-premise ladder's
refuted forms (membership / interp-equality) appear in no live
statement — cert premises are `isDefEqCore` runs; and after the
CoreIdemF repair no idempotence obligation exists anywhere (the two
remaining `WhnfCoreIdem` mentions are the tombstones themselves).

**The proj-head pre-build map — a structural dependency finding.**
`ZipProjHeadCase`'s discharge needs the whnf-outputs of the ZIPPED
SCRUTINEES related — and `ZipIotaCase`'s needs the same for the
zipped MAJORS (`iotaRec` whnfs the major internally).  Neither is
`below`-reachable (scrutinees/majors land at ctor spines, not
sorts) and neither is coreLock-reachable (the chains are LOOP-level:
core+δ+nat).  The shared missing piece is **`loopLock`** — the
whnf-loop lockstep riding coreLock:

* subjects zipped + both whnf runs → outputs ZIPPED ∨ a re-based
  liftable seam ∨ a dead side;
* measure: knot-fuel sum, strong induction (the internal scrutinee/
  major whnfs run at knot fuel MINUS ONE — `whnf_proj_inv` pins
  this — so the recursion strictly decreases; loop steps within one
  knot level iterate on the loop budget);
* per loop step: coreLock on the core part; δ-steps sync by
  name-determinism (`unfoldDefinition_spine_both`) or exit Θ-seams
  at cert heads; nat steps are dead under sort premises
  (`NatStepNoSort`) and, at the loop-lockstep's own level,
  MIXED nat fire on zipped-but-unequal literal args is the one
  genuine wall — absorbed because the consumers are sort-premised
  downstream (below).

**Mixed-fire deadness closes the cascade** (the audit that makes
proj and iota dischargeable at all): a side whose proj/iota fire
FAILS lands proj-headed / recursor-headed stuck; the loop cannot
move it (recursors and proj heads neither unfold nor nat-fire), so
that side's loop never reaches a sort — the top's sort premise
refutes it.  So mixed fire is ALWAYS vacuous at the sort-premised
tops; the only real synchronization content is BOTH-fire, where
zipped ctor-spine majors force the SAME constructor name (ctor-head
zip nodes are refl/constSlack — same name — or cert, which exits a
Θ-seam), hence the same rule, shared RHS, zipped trailing args.
Audit obligations surfaced (suppliers to name at the discharge
seals): recursor consts never unfold (`recInfo` stores no value)
and never nat-fire (the nat-op guards pin the stored KIND);
proj-headed outputs likewise.

**Proposed order** (for the ruling): `loopLock` (statement seal
with the full pre-build treatment, then its induction) BEFORE the
proj and iota discharges, which then ride it the way λ/letE rode
coreLock; Θ can proceed independently (the defeq-run walk — the
certLoop template family) in either position.

### Θ route-check: the semantic shortcut re-barred by the centerpiece

Opening `ZipCertSpineCase`'s map, the pre-build check asked whether
the Θ-motive collapses semantically (zip → interp-equality by
congruence + cert-node `DefEq.sound`, loop preservation, then
`univ_inj` — all suppliers exist, `FrameQ` carries the premises).
The RECORD answers: the claim-family's centerpiece is
**valuation-freedom** — a `Sat`-conditioned route dies at
pi-congruence binder descents (the empty-domain problem: no
satisfying valuation extends into an empty domain, yet inner
numerals feed outer `imax`es), which is also the #100 countermodel
family (empty-domain `lamC = pt`).  The trio's semantic ruling
covers VACUITY exits only (contradictions need no under-binder
valuations); positive equalities stay syntactic.  Do not retry.

The Θ syntactic map's known shape (for its dedicated arc): the
heads' defeq-run walk (certLoop-style, run-mirror det-sync against
the spine's own core steps) interleaved with the spine's β through
the head lam-towers; the crux is the recorded substitution
simulation (opened-body defeq at `d+1` vs instantiated
continuations — the `SortSubstStable` family, whose leaf is (B)),
with `certLoop_sortAgree` for (A)-shaped leaves (its own congruence
rows were vacuous because (A)'s subjects whnf to sorts — Θ's HEADS
whnf to λ-towers, so the lam/lam row goes live for the first time).
Θ's map requires the certLoop internals, the (C) claims, and the
`SortSubstStable` surface read in full before the statement work —
a dedicated arc, not an inline continuation.

### loopLock pre-build treatment: the map (statement to follow the majorToCtor read)

The ruling's audits, folded in and extended; three
structure-determining findings:

**1. The nat tier is WHOLESALE Θ-family, not just mixed fire.**
Even dual `reduceNat` fires diverge syntactically: the fired
outputs' values agree only through the enclosing cert (a blob
grinding to a literal inside `reduceNat`'s own arg-whnfs, which run
at the SAME knot fuel — no measure descent into them exists).
Value divergence between zipped sides enters ONLY through cert
nodes (refl-rooted pairs are fuel-det-synchronized; slack nodes
carry no Nat content), so every nat-tier divergence traces to a
buried cert.  loopLock therefore does not resolve the nat tier: its
conclusion carries a **natSplit disjunct** — the zipped pre-fire
pair, both `reduceNat` outcomes, both continuation runs, no
relation claimed — and the consumers route it: proj-scrutinees dead
(Nat has no native projections), iota-majors through the Θ-funnel
their cert already owns.

**2. coreLock's recHead/projHead seams must be UNPACKED inside
loopLock, not carried out.**  At scrutinee/major level no sort
premise exists, so the fire-agnostic deferral that served the
sort-premised tops is not available: rec-spine pairs must actually
sync (recurse on the zipped majors — `iotaRec`'s internal major
whnf runs at knot fuel MINUS ONE, `iotaRec_inv` pins it, so the
knot-sum measure covers the recursion), fire by ctor-name
determinism on zipped ctor outputs, and diverge only into
Θ-funnels or dead data.  Same for proj (scrutinee-of-scrutinee at
knot−1 via `whnf_proj_inv`).

**3. The skeleton pattern applies a third time.**  loopLock =
`LoopBelow` (knot-sum, loop-budget-sum lex bar) + routed step Props
`LoopIotaStep` / `LoopProjStep` (each taking `LoopBelow`,
discharged at iota's / proj's own seals), with the δ tier internal
(same-name heads: `unfoldDefinition_spine_both`, name-determinism
makes mixed δ contradictory pending one guard-determinism audit;
cert-layer heads: certHead seams), the nat tier as natSplit, and
the carrier **`LoopReaches`** (refl / full-core-step / δ-step /
nat-step / embedded `Contracts`) whose transports compose the NINE
landed step preservers — no new species.

**Prerequisite before the statement freezes** (unread-surfaces rule,
full strength): `majorToCtor`'s K- and eta-rescue rows and the
`litMajorToCtor` surface, read in full — `LoopIotaStep`'s statement
quantifies over exactly that machinery ("Field-ful eta rescue"
consumes `whnf (infer major)` — the deferred infer-lockstep
question lives THERE and must be scoped into the Prop's premises,
not discovered inside its discharge).

Sequence within the arc: majorToCtor/K/eta read → `LoopReaches` +
transports + `LoopBelow` + the two routed Props + `loopLock`'s
statement (one seal) → the induction (next seal) → proj/iota
discharges ride it.

### loopLock statement kit LANDED (carrier, out-shapes, bar, routed Props)

Following the map (majorToCtor's K/eta rows read first: both
rescues run `whnf (infer major)` — the infer-lockstep question is
the DISCHARGE's business, leg-local per the deferred-to-need
ruling; the Props' premises stay run-shaped).  Landed, first-pass:

* **`LoopReaches`** — refl / full-core-step / δ / nat / embedded
  `Contracts`; `trans`, `q_transport` (six preservers),
  `subjInv` (three + `LeavesSubCoreF`), `pairing_left` (left-slot
  species; the contract case uses a refl other-trace).  No new
  species anywhere.
* **`LoopSeamOut`** — `CoreSeam` at loop-reachable subjects,
  connecting LOOP runs at bounded knot fuels (the coreLock
  fuel-bound lesson applied from the start; loop budgets need no
  bounds — `whnfLoop_budget_mono` exists).
* **`NatSplitOut`** — the Θ-family deferral with the PROGRESS
  MARKER (`o₁.isSome ∨ o₂.isSome`): the trap-family check ran —
  without the marker the disjunct absorbs the theorem vacuously.
  Carries the pre-core states (reachable), the synced zipped pair,
  both core runs, both `reduceNat` outcomes, and the suffix loop
  runs FROM THE PRE-CORE STATES (so sort-premised consumers get
  `NatStepNoSort`'s exact premises without any idempotence).
* **`LoopLockOut`** = pack (zip + the four invariants) ∨ seam ∨
  nat split; **`LoopBelow`** = knot-sum then loop-budget-sum, `fc`
  FIXED (the loop tier never descends cert fuel).
* **`LoopIotaStep` / `LoopProjStep`** — the routed step Props:
  shaped pair + component zips + invariants + reachability from
  the loop subjects + suffix loop runs + `LoopBelow` →
  `LoopLockOut`.  Both conclude at the FULL loop context (the
  walk hands everything over; the Props call `below` on their own
  continuations), which keeps loopLock's induction a pure walk.

**loopLock's theorem statement, frozen for the next seal**:
hypotheses = `hm hB hIC hID hIN hLC hLD hLN hQC hQD hQN hQB hQZ
hQH hLS hQs hQA` + `hIo : LoopIotaStep` + `hPr : LoopProjStep`;
then `∀ (N R : Nat) {f₁ f₂ l₁ l₂ fc d u v u' v'}, f₁+f₂ ≤ N →
l₁+l₂ ≤ R → CertZip → SubjInv both → PairedLeaves → Q → both
whnfLoop runs → LoopLockOut`.  Induction: strongRecOn N, inner
strongRecOn R; per loop step: decompose both sides
(`whnfStep_decompose`), coreLock on the core parts (pack → tri;
seam → unpack recHead/projHead through `hIo`/`hPr`, carry
certHead/dead out re-based, natSplit n/a at core level); tri:
both-stuck → pack out; δδ → spine_both sync (same-name) or
certHead seam (cert layer) or the one guard-determinism audit;
mixed δ vs stuck → name-determinism contradiction; any nat some →
NatSplitOut with the walk's own facts.  Consumers enter at knot
minus one (`whnf_proj_inv` / `iotaRec_inv` fuels).

### loopLock LANDED (the whnf-loop lockstep, on the frozen statement)

The guard-determinism audit resolved in place: `unfoldDefinition`'s
only guard is `us.length = cv.levelParams.length`, and eval-linked
level lists have equal lengths — mixed δ on same-name zipped heads
is contradictory (`unfoldDefinition_spine_both` supplies the other
side's fire directly).

The induction, as frozen: double `Nat.strongRecOn` (knot-fuel sum,
then loop-budget sum); `LoopBelow` assembled from the two IHs; per
step both sides decomposed, coreLock on the core parts.
* **Pack** → the tri matrix: any nat fire → the progress-marked
  `NatSplitOut` with the walk's own facts (one uniform builder);
  δδ → `certZip_app_view`: cert layer → certHead seam with runs
  re-assembled through `whnfCore_reidem_const` (δ-fires force const
  heads — the R-a family again), const heads → `spine_both` +
  δ-preserver transports + `below` at the loop decrease +
  `LoopLockOut.prepend`; other heads refute the fire (new
  subject-first `unfold_some_head_of_spine`, replacing 42
  meta-trapped contradiction arms with a two-liner each);
  δ×stuck → new **`whnfCore_self_or_dead`** (a whnfCore output
  re-cores to itself — const-headed via reidem, values via the
  landed value-run family — or is dead-shaped): self → certHead
  seam, dead → `deadL/deadR` at the raw subjects (the strLit-corner
  absorption, once more); mixed δ at same-name heads →
  contradiction; both stuck → pack out.
* **Seam** → carrier transports (`Contracts` embeds into
  `LoopReaches.contract`), runs re-assembled at the premise fuels
  via the coreLock bounds; certHead/deadL/deadR pass through
  re-based; **recHead → `hIo`**, **projHead → `hPr`** (the
  unpacking, exactly as mapped).

Deviations from the frozen hypothesis list, recorded: `hB` never
entered (no sort premise exists here, so `NatStepNoSort` has no
site) and the three nat preservers (`hIN`/`hLN`/`hQN`) dropped —
the nat tier exits as the split BEFORE any nat step is taken, so
nothing transports across one.  The nat preservers remain the
CONSUMERS' business (they hold sort premises and walk the split's
suffix runs).

Next: the proj/iota discharges ride loopLock (`LoopProjStep` /
`LoopIotaStep`, each at its own seal with its own pre-build map —
iota's includes the leg-local infer-lockstep lemmas for the K/eta
rescue rows); then Θ's dedicated read-phase arc.

### LoopProjStep pre-build map (the discharge follows at its own seal)

**The organizing fact — stuck-proj deadness at every level**: a
proj-headed state never moves (no δ — the head is not a const; no
nat; the spine above a stuck proj is iota-inert), so
* at any SORT-premised top, every stuck-proj configuration is
  vacuous by the side's own run (this also fixes
  `ZipProjHeadCase`'s eventual top discharge: its subjects' loops
  reach sorts, so the proj MUST fire or die — the top is
  LoopProjStep-shaped with the deadness simplifications); and
* inside LoopProjStep, MIXED proj-fire exits dead seams directly:
  the stuck side's output is proj-headed — non-const, non-λ,
  non-sort — `deadL`/`deadR` at the raw subjects with the
  mono-stable given runs.

**The discharge plan**:
1. **Bottom first** (the `.proj sn i e₁ / e₂` pair): both sides'
   proj-core steps invert (`whnf_proj_inv`); the scrutinee whnfs
   run at KNOT MINUS ONE — recurse through `LoopBelow` on the
   zipped scrutinees (premise zip; invariants descend
   structurally).  On the scrutinee pack: `projLit` sync (refl-lits
   agree; a cert-blob side is not syntactically a literal, so
   lit-vs-blob divergence lands in fire divergence below; the
   strLit expansion re-enters whnf at the same knot−1 — `below`
   covers it).  Fire conditions are DETERMINISTIC in
   `(env, sn, i, e₃')`: zipped ctor-headed scrutinee-whnfs with
   refl/constSlack heads share the ctor name and sync; cert-headed
   scrutinee-whnfs are never syntactically ctor-headed — no fire —
   stuck — dead.  Both-fire: the fields are `getD` of zipped
   spines (zipped), their continuations are CORE runs at knot−1 —
   **coreLock on the field pair** (standalone, fuel-parametric).
   Scrutinee seams/splits bubble out re-based (`LoopReaches.core`
   prefixes).
2. **Spines** (`as ≠ []`, the seam-lifted arguments): resolve the
   bottom as above, then REBASE to `(mkAppN h₁ as, mkAppN h₂ bs)`:
   stuck bottoms make the whole spine inert
   (`whnfCore_mkAppN_inert`-family) — pack directly on the rebuilt
   proj-zip + arg zips; fired bottoms hand the rebased pair to
   **coreLock** (per-layer run assembly from the original legs, the
   coreLock-consumer pattern).  Nested proj-seams from the rebased
   call RETURN as seams — no recursion: the top converts them by
   deadness.
3. Measure audit: all below-entries at knot−1 (scrutinees, strLit
   re-entries); field continuations via coreLock (no bar); no
   loop-budget descent needed anywhere in the discharge.

Surfaces to have in hand at the build (all previously read):
`whnf_proj_inv`'s full conjunct list (incl. `projCertP` and the
ttChecks-conditional lane — both per-side gates, dual-success),
`projLitToCtorP_inv`, the `whnfCore_mkAppN_inert` family, and the
decompose/assemble pair.

### FINDING at the LoopProjStep build: the cert-swallowed field forces a second Θ-deferral channel

The discharge's pre-build check, walking the both-fire path against
the actual fire conditions, found one corner the sealed
`LoopLockOut` cannot express:

**The corner.**  Both projections fire (both `getAppFn e₃ᵢ = const
entry.ctor` — the fire pins BOTH heads to the SAME constructor), but
the whnf'd-scrutinee pack's zip is cert-rooted with the cert layer
ABOVE the field position: the spine view's pairwise-zipped zone
does not reach `nP + i`, so the two extracted fields are related
only through the swallowing cert.  Every exit is barred:
* fields not zipped → no coreLock;
* returning the premise projHead seam → regress (the top's
  conversion is this very discharge, no measure moves);
* a REBASED seam or split (at `.proj sn i w'`-subjects) is doubly
  barred: the carrier has no under-proj step (transports cannot
  reach it), and runs from rebased proj-subjects require
  scrutinee-whnf idempotence — the REFUTED WhnfCoreIdem family, in
  its exact home territory (the tombstone rule, honored again).

**The sync path narrows but survives**: when the cert layer sits at
the HEAD (or the zip is refl/constSlack/structural), the fire pins
same-name ctor heads, the fields fall in the pairwise zone, and
both-fire hands zipped fields' core runs at knot−1 to coreLock —
as mapped.  Also banked: refl-equal literal scrutinees expand to
the SAME `strLitToConstructor` term, so the expansions' whnfs
DET-agree across fuels — no `below` call, no Q at the expansion
(the Q-gap that route would have opened never opens).

**The repair (ratification requested)**: `LoopLockOut` gains a
fourth disjunct — **`ProjSplitOut`**, the second Θ-deferral channel
beside the nat split, progress-marked by the DUAL FIRE data: the
original subjects (premise-reachable, premise runs — nothing
rebased), `sn`/`i`, the whnf'd-scrutinee pair with its pack
(zip + invariants), both `projLit` outcomes, and both fire
condition bundles.  The Θ-arc owns its conversion (the swallowing
cert IS the Θ-walk's subject), exactly as the record already
assigns cert-leaf majors/scrutinees to the Θ family.
`LoopIotaStep`'s cert-leaf-major corner will demand the same
channel; its precise shape lands at iota's own map seal so the two
splits stay parallel.

Consumer impact: loopLock passes splits through unchanged (its
walk never inspects them); the sort-premised tops treat ProjSplit
like the seams they already route to Θ.  The amendment is
conclusion-widening only — no landed proof weakens.

### The amended kit LANDED (ProjSplitOut + two companion amendments)

The ratified `ProjSplitOut` landed as specified (original subjects,
premise runs, dual-fire progress marker, arg zips and scrutinee
pack carried for the Θ-consumer, `g ≤ f` bounds included), with
`LoopLockOut` widened to four disjuncts and `LoopLockOut.prepend`
extended.  Two companion gaps surfaced by the discharge's continued
pre-build, sealed together (ratification-at-seal):

* **The step Props lacked `l₁ + l₂ ≤ R`** — their discharges' tail
  work (the tri analysis after field/residual composition) recurses
  through `below` at equal knot and DECREASED LOOP budget, which
  the frozen premises could not license.  Added to both;
  loopLock's call sites supply it from their own `hR`.
* **The carrier gains a `projFire` step** — the sync path's
  mid-state seams (from coreLock on the rebased field-spine pair)
  are reachable from the subjects only THROUGH the fire, and the
  head-constructor history repeats exactly: the carrier records
  what the walk actually did.  The step carries the full fire
  bundle (scrutinee whnf, `projLit`, table entry, bounds, field
  run); three new species thread the transports —
  **`QPreserveProjFireF`** (supplier: the model's projection law on
  the whnf'd constructor form + the claims' whnf preservation),
  **`InvPreserveProjFireF`** / **`PairedPreserveProjFireF`**
  (suppliers: the whnf/core preservation and leaf-subset families,
  `EnvWF`-backed, own seals beside `LeavesSubCoreF`'s).

All mechanical consumers rebuilt first-pass; loopLock's proof
unchanged except the two `hR`-threads and the split re-nesting.
Next seal: the `whnfCore_proj_spine_inv` inversion (reverse-spine
induction, nil-disjunct + dead-arm residual per the map) and the
LoopProjStep discharge on the now-complete kit.

### The proj-spine inversion LANDED (+ two small kit pieces)

`whnfCore_proj_spine_inv` — a core run on a projection-headed spine
factors through the scrutinee's whnf (at a bounded smaller knot)
and the projection decision: stuck (the rebuilt spine — the layer
legs are FORCED iota-none, β refuted by `mkAppN_ne_lam`, iota fires
refuted by the proj head), or fired with the field's run and a
TRI-DISJUNCTIVE residual — a run at bounded fuel, the empty spine
(`t = h'` directly), or a DEAD SHAPE (the layer over a dead field
output stays dead) — the nil/dead disjuncts dodging every
idempotence exactly as mapped.  Proof: strong induction on the
spine length with the concat split (`List.eq_nil_or_concat`;
`List.reverseRecOn` is not in this toolchain), the layer composed
by `whnfCore_app_decompose`/`_assemble` and
`whnfCore_self_or_dead`.  Mechanization notes: the β-legs carry
FIVE existentials (`ta` included — three pattern repairs); the
`(H := shape)` pin defeats the meta-lambda trap where by-wrapping
did not; assemble outputs are `max`-fueled — promise `max f' f' + 1`
with an omega bound, not `f' + 1`.

Also landed: `mkAppN_ne_lam` (the value-shape family's last gap)
and `QDescendProjF` (the descent family's second member, foreseen
at the build map — `FrameQ` is per-side structural).  Next: the
LoopProjStep discharge proper on the complete kit.

### FINDING at the discharge: ProjSplitOut's pack midsection is too strong — the split must nest the scrutinee-level out

Walking the discharge against the below-call's actual outcomes:

* **Banked first**: scrutinee-level DEAD seams are refuted by the
  fire itself (a dead-shaped scrutinee whnf output is non-const-
  headed, but the fire pins `e₃`'s head to the entry's constructor
  — in the identity `projLit` case they collide), and the
  refl-strLit path needs NO Q and NO coreLock (shared expansion ⇒
  det-equal `e₃`, det-equal fields — the Q-reflexivity gap never
  opens).  The id-id sync path needs one more descent species —
  **`QDescendArgF`** (the argument-side app descent; `FrameQ`
  per-side structural, same supplier family as `QDescendAppF`).
* **The finding**: when the scrutinee recursion returns a SEAM or a
  SPLIT (not a pack), both fires can still hold — and
  `ProjSplitOut`'s midsection demands the PACK's fields
  (`CertZip w₁ w₂ ∧ SubjInv ∧ … ∧ Q`), which those arms cannot
  supply.  The mid-state data they DO supply (scrutinee-level
  seams with their own connecting runs, or nested splits) is
  exactly what the Θ-consumer wants — richer than the pack — but
  the split as sealed cannot carry it.

**The repair (ratification requested)**: `LoopLockOut` becomes a
Prop-valued INDUCTIVE (strictly positive throughout), with the
proj-split constructor nesting the SCRUTINEE-LEVEL
`LoopLockOut e₁ e₂ w₁ w₂ g₁ g₂` in place of the pack midsection —
the self-similar shape: the split hands the Θ-consumer whatever
the scrutinee analysis produced (pack, seam, nat split, or a
nested proj split), and the discharge FORWARDS the below-out
instead of destructing it.  Pack/seam/nat-split constructors keep
their exact current payloads (mechanical re-nesting for the landed
loopLock and prepend); the iota split, when shaped at its map
seal, nests the MAJOR-level out the same way — the two channels
stay parallel by construction.

### The self-similar kit LANDED; LoopProjStep DISCHARGED

**The restructure (ratified)**: `LoopLockOut` is now a
strictly-positive inductive — `pack` / `seam` / `natSplit` wrap the
unchanged payloads, `projSplit` nests the scrutinee-level out in
place of the pack midsection.  `prepend` rewritten (the nested out
is scrutinee-level and untouched); loopLock's eleven construction
sites re-nested mechanically (one first attempt at a global textual
swap hit UNRELATED disjunction sites and was reverted — construction
-site swaps must be theorem-scoped, recorded as a mechanization
rule).

**`loopProjStep_of`** — the minimal discharge on the self-similar
shape, THREE hypotheses only (`hm`, `QDescendAppF`,
`QDescendProjF`):
* a stuck side or dead residual exits a dead seam at the raw
  subjects (shape facts by the `(e := shape)` pins);
* both-fire descends the invariants (new `qDescend_mkAppN` — the
  equal-length double-concat induction — plus `subjInv_spine_head`,
  `subjInv_proj`, `mem_fvarLeaves_proj`), converts the scrutinee
  whnfs to loop form, recurses through `below` at knot minus one,
  and FORWARDS the out inside `.projSplit` — the split is the
  interface; the sync work (view, field zips, coreLock) belongs to
  the split's sort-premised consumers, which hold strictly more
  facts.  No preserver species enter at all.

The λ/letE/proj trio of loop-tier obligations is now two-thirds
discharged at the loop level (`hPr` supplied); next: iota's map
with its parallel nested channel (`LoopIotaStep`), then Θ's read
phase — the Θ-arc's docket now holds the two splits' conversions
beside the cert-spine motive.

### Iota's map: the parallel-channel constraint dissolves; LoopIotaStep DISCHARGED

The map's pre-build walk resolved the frozen constraint by
DISSOLUTION: `LoopIotaStep`'s routed premises are exactly
`CoreSeam.recHead`'s payload (find? recInfo, eval-linked levels,
pairwise arg zips, the reaches, the premise runs), so the honest
loop-tier discharge is **the seam itself** — a one-liner, legal
and terminal, and non-circular because the seam's consumer is the
SORT-PREMISED top (`ZipIotaCase`'s own discharge, a different
Prop): there, mixed fire dies by deadness (stuck rec-spines never
reach sorts — recursors neither unfold nor nat-fire), synced fire
recurses on the zipped MAJORS through `ZipBelow` at the loop
decrease (majors are pairwise-zipped args — even easier than
proj's scrutinees), and cert-swallowed majors go to the Θ-arc.

**Why no iota split channel exists**: proj needed `ProjSplitOut`
because proj-STUCK pairs are dead-shaped-POOR (the seam family had
nothing to carry the fire data), while rec-spine pairs have the
RICH `recHead` seam that carries everything the top needs.  The
channels are not parallel because the seams are not — the frozen
constraint is discharged by this finding, not by construction.

**Milestone**: both step Props are supplied (`loopProjStep_of`,
`loopIotaStep_of`) — loopLock is closed END-TO-END at the loop
tier, modulo the ledgered species suppliers.  The remaining
defeq-branch docket: the two sort-premised top discharges
(`ZipProjHeadCase` riding loopLock + the proj split;
`ZipIotaCase` riding loopLock + the major recursion), Θ's
read-phase arc (docket: the cert-spine motive, the two split
conversions, cert-swallowed majors/scrutinees), the semantic trio,
the species suppliers (`LeavesSubCoreF` ✓ done; the projFire trio,
the FrameQ suppliers, the preserver families), the install facts,
and the (B) type-form map.

### The two sort-premised top discharges: the frozen map

**Audit fact underpinning both**: loopLock's TOP-LEVEL out never
contains a projHead seam — coreLock's projHead seams are routed
through `hPr` inside the walk, and `loopProjStep_of` returns only
dead seams and proj splits; the pack-branch recursion inherits the
property inductively.  So neither top discharge self-recurses on
its own seam shape.

**`ZipProjHeadCase`'s discharge** (riding loopLock + the split):
call loopLock on the subject pair (the full preserver battery +
both supplied step Props); convert per disjunct under the sort
premises: pack at the sort outputs → `certZip_sorts_eval`;
certHead seam → `hΘ` with `LoopReaches`-transported invariants
(the projFire transport species enter here — their suppliers'
seals precede this discharge) and the connecting runs, which land
at the sorts directly; recHead seam → `hIota` (ZipIotaCase as a
routed hypothesis — non-circular for this Prop); dead seams → the
`loop_dead_exit` pattern (det + tri + the seam's own shape facts);
natSplit → `NatStepNoSort` on the fired side (the split's fields
are its exact premises, by design); projSplit → a routed Θ-family
Prop (claim-shaped: split data + sort premises → eval-equality),
discharged at Θ's arc.

**`ZipIotaCase`'s discharge** (the major recursion — loopLock on
the pair returns the recHead seam back, per the dissolution, so
the work is local): decompose the first core steps; `iotaRec_inv`;
**loopLock on the zipped majors at knot−1** (majors are
pairwise-zipped args); dispatch its out:
* major-pack at ctor heads → same name (refl/constSlack view; cert
  heads are not syntactically ctor-headed → no fire → dead) →
  same rule → zipped reducts (shared instantiated RHS +
  pairwise trailing args, the `certZip_instantiate` +
  `certZip_mkAppN_zips` construction) → coreLock on the
  continuation runs at knot−1 → zip of the step outputs →
  **`ZipBelow` at the loop decrease** with the continuation loop
  runs (the loop budget drops by one per side across the step);
* mixed or failed fire → deadness (stuck rec-spines never reach
  sorts);
* major-level seams and splits (cert-swallowed majors) → the
  Θ-arc's routed Prop;
* deeper recHead seams mid-continuation → `ZipBelow` covers them
  (loop-decreased; sort-runs assembled from the seam's connecting
  runs by the step assembles; the subject zips from the recHead
  payload, the deltaSpine pattern);
* the K/eta rescue rows (`majorToCtor` fabrications) → the
  leg-local infer-lockstep lemmas, stated AT this discharge's seal
  with their own pre-checks (the deferred-to-need ruling).

**Θ's read-phase docket, final form (four items)**: the cert-spine
binder-opening motive (`SortSubstStable`/certLoop/(C) surfaces read
in full first); the projSplit conversion; the natSplit conversion
at the loop-consumers; cert-swallowed majors/scrutinees.  Supplier
seals that precede the top discharges: the projFire transport trio
and the remaining preserver/descent FrameQ suppliers.

### FINDING at zipProjHeadCase_of: the seam-budget bounds gap (the knot-bounds history, loop-budget edition)

The recHead-seam conversion hands `hIota` (ZipIotaCase) the seam's
connecting runs — whose knot fuels are ALWAYS maxed (`c := f`,
`le_refl` at every direct seam site) — so the `ZipBelow` the
consumer must be given sits at `(c₁+c₂, l₁ˢ+l₂ˢ)` with
`c₁+c₂ = ga+gb`, and the measure translation from the premise
`ZipBelow (ga+gb) (la+lb)` needs `l₁ˢ+l₂ˢ ≤ la+lb` — which HOLDS
at every construction site (refl at direct sites, strict descent
at recursion sites via the δδ `below`-calls) but is NOT RECORDED:
`LoopLockOut` carries no budget indices, so the invariant cannot
even be stated about the out.

**The repair (ratification requested)**: extend `LoopLockOut` with
two budget indices `(l₁ l₂)` — the call's loop budgets — and add
`l ≤ l`-bounds to the seam and both splits, mirroring the ratified
knot-bounds amendment exactly (whose sites all carried the
invariant unrecorded too, and whose payoff was the same: `below`
passes to consumers without measure drift).  `LoopBelow`, the step
Props, `prepend`, and loopLock's construction sites extend
mechanically (refl at direct sites; `Nat.le_succ_of_le`/`le_trans`
at pass-throughs; budget-mono never needed).  Third instance of
the same lesson: EVERY run a pack ships must ship with its fuel
bounds, knot AND budget, from the start.

### The budget-index surgery LANDED (the ratified third-bounds amendment)

`LoopLockOut` now carries the two budget indices; the seam and both
splits bound their shipped runs' budgets against them (`lc ≤ l`
beside `c ≤ f`); `LoopBelow`, both step Props, loopLock, and both
step discharges re-thread.  New **`LoopLockOut.mono_budget`**
(budget slots weaken upward; bounds compose, pack and nested out
untouched) serves the recursion-return sites — the δδ branch now
prepends THEN budget-weakens by one, exactly the `le_succ` shape
the finding predicted.  The projSplit constructor also gained the
nested out's own budget slots (`gl₁ gl₂` — the scrutinee analysis'
run budgets, unbounded against the outer loop: whnf-internal
budgets are unrelated to it).  All direct sites bound by `le_refl`,
recursion sites by the weakening — the invariant held everywhere,
now recorded everywhere.  Design axiom restated: every run a pack
ships, ships with BOTH fuel bounds from the start.

### zipProjHeadCase_of DISCHARGED; the audit fact moved INTO the type

Building the top discharge, `cases` demanded the projHead-seam arm
the walk never produces — the prose audit could not discharge a
syntactic obligation.  The honest fix: **`LoopSeam`**, the
loop-tier seam type with exactly four constructors
(certHead/recHead/deadL/deadR, payloads verbatim), replacing
`CoreSeam` in `LoopSeamOut` — the audit fact is now A TYPE, and
top consumers never face their own shape by construction.  All
loop-tier shipping sites re-tagged mechanically; coreLock keeps
`CoreSeam` (its projHead constructor is exactly what loopLock
unpacks).

`zipProjHeadCase_of` then landed on the frozen map: loopLock on
the subject pair; pack → `certZip_sorts_eval`; certHead → `hΘ`
with the carrier-transported invariants (`(Q := Q)` pins on the
transports — the HO-unification guard, again) and the connecting
sort-runs; recHead → `hIota` at **`ZipBelow.weaken`** (new: the
bar weakens to smaller measures by omega over the shipped bounds —
the budget surgery's direct payoff); dead seams → decompose + det
+ `loop_dead_exit`; natSplit → `NatStepNoSort` on the marked side
(`Option.isSome_iff_exists`); projSplit → the new routed
**`ProjSplitSortAgree`** (the Θ-family's second docket item,
payload-verbatim premises at sort-landing suffix runs).

**Milestone**: all four flat-spine head cases
(const/λ/letE/proj) now have their discharges.  The summit's
remaining routed obligations: `ZipCertSpineCase` (Θ),
`ZipIotaCase` (the major recursion), `ProjSplitSortAgree` (Θ's
docket) — plus the trio, the species suppliers, the install facts,
and (B).

### ZipIotaCase: the full-treatment pre-build map (build follows)

**Stuck sides die by their own tri** — no guard analysis needed:
nat-some → `NatStepNoSort` (the sort premise); δ-some →
`unfoldDefinition` is none on `recInfo` heads (a ten-line lemma off
the match); stop → sort = rec-spine, refuted by shape.  So only
both-fired carries content, exactly as at proj.

**The rec-spine inversion** (parallel to the proj one, reverse-
spine induction): stuck (the spine, iota-none at the arity layer or
under-applied) or fired — the `iotaRec_inv` payload at the arity
prefix plus the run/nil/dead residual.  The fire data pins BOTH
majors' whnf outputs to constructor spines (`hmfn`), which
organizes everything after.

**Both-fired**: majors are pairwise-zipped args; their whnfs run at
knot−1 (`iotaRec_inv`) — **loopLock on the zipped majors**.
* **Major-pack + identity rows + matching ctor names**
  (view: refl/constSlack heads) → same rule (`rules.find?` at the
  shared name) → zipped reducts (`certZip_instantiate` on the
  shared RHS at eval-linked levels + take/drop of zipped spines) →
  coreLock on the continuation runs at knot−1 → `ZipBelow` at the
  LOOP decrease (the budget drops by one across the step).
* **Everything else routes to ONE new Θ-family Prop,
  `IotaMajorSortAgree`** — the self-similar interface a third
  time: it takes the major-level `LoopLockOut` VERBATIM (pack with
  cert-headed/name-mismatched ctors, seams, splits — whatever the
  major analysis produced) plus the dual fire data and the sort
  runs, concluding the claim.  Cert-swallowed majors, mixed
  strLit rows, and nested seams all ride it; discharged at Θ's
  arc (its docket becomes: the cert-spine motive + THREE
  conversions — proj split, nat split, iota-major).
* **The K/eta rescue rows** (`majorToCtor`'s fabrication arms) →
  two leg-local routed Props stated AT the build with their own
  pre-checks (`KRescueSortAgree` / `EtaRescueSortAgree`-shaped:
  the rescue's `whnf (infer major)` data on both sides + the
  claim) — the deferred infer-lockstep enters exactly here and
  nowhere else; their discharges open the infer-lockstep seal that
  the record always predicted.

Refl-lit majors expand det-equal (no Q, no coreLock — the banked
strLit trick); `litMajorToCtor` identity rows transport through
the pack zip.

### The rec-spine inversion LANDED (+ the recInfo-unfold lemma)

`whnfCore_rec_spine_inv` — stuck (the spine) or fired at some
prefix split (`as = pre ++ post`) with the `iotaRec` fire run, the
continuation's run, and the run/nil/dead residual — the proj
inversion's structure verbatim (length induction, concat splits,
`whnfCore_self_or_dead` at nil residuals, dead propagation through
iota-none layers; the fire itself is caught at the stuck-head
layer where the legs' iota-some IS the fire).  Plus
`unfoldDefinition_none_of_recInfo` (recursor heads never unfold —
off the match).  Two fixes only (a drafting leftover and the
append-assoc direction).  Next: the three routed Props with their
pre-checks, then `zipIotaCase_of` on the map.

### The two routed Props LANDED — and the K row needs NO infer-lockstep

Statement-sealing the routed Props surfaced a finding that halves
the deferred obligation: **the K-rescue row discharges locally.**
`majorToCtor`'s K gate requires `cnF = 0` — the constructor has no
fields — so the fired reduct's field segment
(`major.getAppArgs.drop ctorParams`) is EMPTY on both sides
regardless of which side fabricated: K-reducts depend only on the
SPINE arguments (zipped by premise), and the single-rule gate
(`rules = [rl]`) pins the same rule on both sides (an
identity-side's ctor must be in the rules list, hence `rl.ctor`).
Multi-rule recursors never rescue (the `[rl]` match gate), so the
pack-sync path covers them.  **Only the eta row carries the
infer-lockstep** — its fabricated params come from
`whnf (infer major)`'s spine — and `EtaRescueSortAgree` is stated
with exactly that data (the infer runs as premises: the lockstep
enters here and NOWHERE else, sharper than the map predicted).

`IotaMajorSortAgree` landed with the self-similar payload (the
major-level `LoopLockOut` verbatim + both fires as runs, consumers
invert) and the full subject package.  Both Props first-pass.
Θ's docket final form: the cert-spine motive + proj-split +
nat-split + iota-major conversions + the eta-rescue lockstep.
Next: `zipIotaCase_of` on the map (stuck-kills by tri; both-fired
via the rec-spine inversion + majors' loopLock; identity/K rows
local; eta row and non-pack majors routed).

### zipIotaCase_of DISCHARGED — the last summit-routed discharge outside Θ

The minimal discharge on the proj pattern, landed:
* **stuck sides die by their own tri** exactly as mapped (nat →
  `NatStepNoSort`; δ → `unfoldDefinition_none_of_recInfo` off the
  spine head; stop → sort-vs-spine shape, nil and cons arms);
* **both-fired**: the rec-spine inversions identify the recursor
  (getAppFn + find? determinism, direction-controlled rewrites —
  `subst` on `c₁ = n` ate `n`, banked), extract the prefix lengths
  (`mI + 1`, so the major is the prefix's LAST element), build the
  pre/post/major zips from the subject zips (`getElem_append_left`
  / `getElem_append_right` with a simpa-normalization — index
  rewrites inside `getElem` are motive-dependent, use the equation
  form at the hypothesis then simp the indices), descend the
  invariants (`subjInv_spine_arg`) and Q (post-strip via
  `qDescend_mkAppN` + the new **`QDescendArgF`** at the last
  argument), run **loopLock on the zipped majors** at the fire's
  own knot fuels, and FORWARD everything to `IotaMajorSortAgree`.

New kit: `getD_eq_getElem'`, `mkAppN_append`, `QDescendArgF` (the
descent family's third member), `subjInv_spine_arg`.

**MILESTONE — the sim tier is closed outside Θ's arc.**  Every
summit-routed Prop now has a discharge except the five on Θ's
final docket: the cert-spine motive (`ZipCertSpineCase`), the
proj-split / nat-split? (nat is consumed inline by the tops) /
iota-major conversions (`ProjSplitSortAgree`,
`IotaMajorSortAgree`), and the eta-rescue lockstep
(`EtaRescueSortAgree`).  Beside Θ: the semantic trio, the species
suppliers (projFire trio + FrameQ family), the install facts
(`StoredWF`, `BoolCtorsInert`, (E)), and the (B) type-form map.
Θ's read phase opens next per the approved sequence.

### Θ's read phase COMPLETE — the map (the arc's most consequential)

**Read findings** (defeqStep in full; `PostCoreCert` +
`defeqStep_decompose` in full; certLoop's arm handling; the
(C)/`SortCohAt`/`SortSubstStable` status):

1. **`PostCoreCert` is the complete certifying-path taxonomy** —
   22 constructors; the binder arms (`piCong`/`lamCong`) carry the
   fvar-OPENED body runs at `d+1`, each side opened with ITS OWN
   annotation (`.fvar d n₁ ty₁` vs `.fvar d n₂ ty₂` — the
   `PairedLeaves` discipline's origin, read off the kernel code),
   and the opened certs run at the KNOT'S OWN fuel — one cert
   level down (`fc − 1`): the Θ-recursion's measure is the
   fc-descent, exactly `ZipBelowFc`'s shape.
2. **The (A)-template consumes NO binder apparatus**: certLoop's
   piCong/lamCong/appCong/eta/proj/fvar/const arms are all vacuous
   by `loop_stuck_out` (the subject's own sort-loop refutes stuck
   shapes).  The opened-body runs go unconsumed everywhere so far —
   Θ is their first and only consumer.
3. **TRAP RECORDED: the ceilinged `SortCohAt` family is UNCLOSED.**
   The structure bundling the five At-claims (including both (C)
   claims and `SortSubstStable`'s machinery) is consumed by four
   `_of_at` theorems but constructed NOWHERE — it is the OLD route
   that hit the defeq-branch wall (the ceiling-measure STOP), which
   the zip tier replaced.  Θ's discharge must not lean on the (C)
   claims or `SortSubstStable`; the substitution simulation must be
   built zip-side.  (`PremiseLadder` holds the refuted semantic
   forms — consistent.)

**The Θ design (the binder-opening motive, concretized)**: one walk
serves all four docket items.  Its induction is certLoop's
(defeq-loop budget, then the fc-descent at opened certs), its
subject GENERALIZED to a **substitution telescope**: a pair of
spines over cert-related cores under a stack of pending
substitutions — per opened index, the argument pair (zipped), the
domain cert (at `fc − 1`), and the annotation pair.  The walk
mirrors the subject loops' steps against the run's `PostCoreCert`
arms:
* `lamCong` + β-legs → PUSH onto the telescope (the opened-body
  cert at `fc − 1` is the next round's core; measure = fc), the
  loops' instantiated continuations tracked against the opened
  forms through the telescope;
* `spine`/`appCong`/`consts` arms → the same-head congruence
  data feeds the landed spine machinery (deltaSpine pattern);
* `deltaL/R/B` → name-determinism (`spine_both`) or re-entry at
  the loop budget; `natL/R` → `NatStepNoSort` under sort premises;
* `irrel`/eta/`stuckIrrel`-family arms → the landed vacuity trio;
* the fvar-leaf reads inside opened zones resolve through the
  telescope's annotation pairs ((A) on the annotation pair at the
  leaf — the record's motive, now with (A) DISCHARGED to feed it).
The three split conversions (`ProjSplitSortAgree` — walk the
scrutinee cert; `IotaMajorSortAgree` — walk the major cert +
the local K-row algebra; nat splits at the tops) and
`EtaRescueSortAgree` (the infer-lockstep row) consume the SAME
walk at telescope depth zero — the shared machinery is the walk
itself.

**Arc order**: the telescope datatype + the walk's statement (one
seal, full pre-build treatment with the trap-list above), the walk
(the induction, likely several seals at knot-natural boundaries),
then the four docket discharges as consumers.

### The Θ walk: full pre-build treatment (the summit statement design)

**The telescope.**  An entry per opened binder, innermost last:
`ThetaEntry := ⟨n₁ n₂ : Name, ty₁ ty₂ a₁ a₂ : Expr⟩` — the two
binder names, the ANNOTATION PAIR (each side's own domain — the
kernel opens with `.fvar d nᵢ tyᵢ`), and the ARGUMENT PAIR the
subject loops β-substituted where the run opened an fvar.  The
per-entry facts (carried as a `TelescopeOk fcK d` predicate over
the list, entry `j` at depth `d + j`):
* `CertZip fcK d a₁ a₂` (the argument zip — from the β-legs'
  positions in the original spines),
* `isDefEqCore (fcK+1) (d+j) ty₁ ty₂ = .ok true`-form domain fact
  (the run's own `hd` at the entry's depth; fuel bookkeeping: the
  opened runs sit at the walk's knot, one below the consumer's fc),
* `SubjInv` of both arguments, and the argument-side invariants.

**The subject form.**  The walk relates
`X₁ = mkAppN (subst₁ Γ C₁) sp₁` to `X₂ = mkAppN (subst₂ Γ C₂) sp₂`
where `substᵢ Γ` folds `instantiate1` of the `aᵢ`s over the
telescope (innermost first) and `C₁ C₂` are the OPENED cores the
pending defeq run relates: `defeqLoop μ (pureFns fcK) env (d + |Γ|)
L C₁ C₂ = .ok true`, with `sp₁ sp₂` pairwise-zipped.  At depth
zero this is exactly `ZipCertSpineCase`'s data with
`fcK := fc − 1`, `L := defeqLoopFuel` (from `isDefEqCore`'s
unfold).

**The measure**: lex `[fcK, L]` — pushes (lamCong under β) descend
`fcK` (the opened run sits at the knot one down, read off the
kernel's own fuel discipline); the lazy-delta/nat re-entries (`k`
at `L−1`) descend `L`; the subject loops' budgets descend WITH the
re-entries by the certLoop det-sync discipline and are carried as
premises, not measure slots.

**The walk's conclusion**: eval-equality of the sort numerals — no
disjuncts, no seams, no deferrals (the four docket items are its
CONSUMERS, not exits).

**Arm plan against `PostCoreCert`** (the 22 arms; det-sync of the
run's whnfCore pair with the loops' current core step first, per
certLoop):
* `syn` → the cores agree syntactically: the subject pair becomes
  same-core spines with zipped telescope images — the loops
  continue on det-equal material up to the substitutions and
  zipped spines; handled by the zip tier through loopLock on the
  REBASED pair (zips: refl-core + telescope-image zips — the
  images of a SHARED core under zipped substitutions zip by
  `certZip_subst` folded over Γ) and the landed conversion
  patterns.
* `irrel`, `etaL/R`, `stuckIrrel` family, `rescue` → the landed
  vacuity trio + `NatStepNoSort`, exactly certLoop's exits.
* `natL/R` → `NatStepNoSort` under the sort premises.
* `deltaL/R/B` → the loops δ-sync by name-determinism
  (`spine_both`) and the walk re-enters at `L−1`.
* `sorts` → cores are sorts: the spines must be empty (a sort
  under application is loop-dead) and the telescope images of
  sorts are sorts — conclude by `isEquiv` soundness.
* `consts`/`spine`/`appCong` → the same-head congruence data
  (`defEqList_extract`) feeds the zip construction; continue
  through loopLock on the rebased pair as at `syn`.
* `piCong` → cores are Π's: under application the loops are dead
  (Π is a value); with empty spines the loops END at the Π's — but
  the sort premise forces sorts — dead unless spines empty AND the
  cores ARE the outputs — then sort-vs-Π refutes.  VACUOUS both
  ways (the (A)-pattern).
* `lamCong` → THE PUSH: with non-empty spines the loops β-fire the
  first spine argument into the opened body; push
  `⟨n₁,n₂,ty₁,ty₂,a₁,a₂⟩`, recurse on the opened-body run at
  `fcK − 1` with the remaining spines; with empty spines the loops
  end at λ's — sort-vs-λ refutes (vacuous).
* `fvars` → cores are the SAME fvar index: if inside the telescope
  zone, the index resolves to an ANNOTATION PAIR and the loops
  read the annotations — the (A) claim on the annotation pair
  (DISCHARGED, `ensureSortAgreeRQ_of`) concludes; below the zone
  the annotations are literally paired by `PairedLeaves`.
* `lits`/`natZero*/natSucc*/str*` → literal cores never reach
  sorts under the loops — vacuous by shape.
* `projCong` → stuck-proj deadness (the recorded organizing fact).

**The trap-list, run**:
1. No vacuity absorption (single positive conclusion).
2. No zip-out promise (eval-conclusion only — the refuted shape
   avoided).
3. Premises producible at all five consumers (depth-0 checked
   against each routed Prop's data; the splits' cert nodes unfold
   to `defeqLoop` runs by `isDefEqCore`'s definition).
4. Measure instantiated: `[fcK, L]`, pushes descend slot 1 by the
   kernel's own knot discipline; no loop-budget slot needed (det
   carries the loops).
5. Joint satisfiability: depth-0 = any accepted cert-headed spine;
   pushed states = β-firing spines (arena-real).
6. Tombstone sweep: no idempotence anywhere (det against the
   loops' OWN runs, the certLoop discipline); no
   `SortCohAt`/`SortSubstStable`/(C) dependence (the read's trap);
   eval-currency throughout; pairing enters as premise
   (the telescope IS the paired discipline); no w-general species;
   no `WhnfCoreIdem` shape.
7. Exits are all landed suppliers (vacuity trio, `NatStepNoSort`,
   `defEqList_extract`, loopLock + conversions, (A)); no new seams.

**Freeze order**: `ThetaEntry`/`TelescopeOk`/`substᵢ` defs + the
walk's statement as a def (`ThetaWalkClaim`), then the induction in
seals at the arm-group boundaries (vacuous arms first, δ/nat
re-entries, the rebased-pair group, the push, the fvar leaf), then
the five consumer discharges.

### The Θ walk's statement FROZEN (first-pass)

`ThetaEntry` (names + annotation pair + argument pair),
`thetaSubst₁/₂` (innermost-first close-and-plug over the landed
`abstract1`/`instantiate1` algebra), `TelescopeOk` (per-entry: the
argument zip and the domain fact at `fcK + 1` — the knot's defeq
one fuel up, matching the run's own `hd` bookkeeping — plus the
arguments' subject packages), and `ThetaWalkClaim` (the summit:
spines over telescope-substituted run-related cores, both loops at
sorts, eval-equality; the bar at `fcK + 1` for the rebased-pair
conversions).  All compiled first-pass against the sealed
treatment.  Next: the walk's induction, in seals at the arm-group
boundaries (vacuous arms; δ/nat re-entries; the rebased-pair
group; the push; the fvar leaf), then the five consumer
discharges.

### STOP-FINDING at the walk's push case: the det-sync breaks one level in — the engine is the substitution simulation itself

The pre-build check on the induction's first round, run against the
push case as directed:

**At depth zero the certLoop det-sync works** — the run and the
loops whnfCore the SAME heads, and `KnotFuelDet` aligns them across
fuels.  **One push in, it breaks**: the run processes the OPENED
cores (fvar-form) while the loops process the SUBSTITUTED ones —
different terms, no determinism to invoke.  The walk's per-step
relation IS the substitution simulation, not a bookkeeping detail:
the treatment's phrase "det carries the loops" is correct only for
the δ/nat re-entries at matching terms; the push-descended rounds
need a genuinely new engine.

**The engine (zip-side, honoring the SortCohAt trap)**:
`whnfCore_subst_sim` — the substituted image of an opened core-run
is itself core-reachable:
  `whnfCore g (d+1) C = .ok C'` →
  the loops' runs on `(C.abstract1 d).instantiate1 a`-forms factor
  through `(C'.abstract1 d).instantiate1 a` (a core run exists from
  the substituted source to the substituted image, at bounded
  fuel).
One-directional (forward: the opened run's steps MAP under
substitution — β/ζ commute with fvar-substitution by the landed
`instantiate`/`abstract` algebra; ι fires map because
fvar-substitution preserves constructor heads; the substituted side
may reduce FURTHER — the unlocked `.app (fvar d) x → .app a x`
redexes — which is exactly why only the forward direction is
claimed and why the walk then re-decomposes the loops' actual
runs from the image point by determinism).  Scale: a
`LeavesPres`-class mutual induction (whnfCore/whnf/iotaRec under
substitution) with the per-step commutation lemmas as its kit —
the substitution simulation the record always said "re-enters the
knot", now in its zip-side form, with the loops' own runs (never
re-runs) closing each step.

**Amended arc order (ratification requested)**: (0) the
commutation kit (β/ζ/ι single-step under `abstract1`/
`instantiate1` — syntactic, per-step seals) → (1)
`whnfCore_subst_sim` (the mutual induction, its own map seal
first) → (2) the walk's induction per the sealed groups, with the
push case consuming the simulation → (3) the five depth-zero
consumers.  The vacuous-arm group can proceed in parallel with (0)
if sequencing favors it — it consumes nothing new.

### The commutation kit: inventory finding — the algebraic core is LANDED

The kit's map, taken by inventory of `Verify/Subst.lean` +
`Verify/Abstract.lean` before writing anything:

**Already landed** (the substitution simulation's algebraic core):
* `instantiate1_instantiate1` — the double-substitution
  commutation (closed substituends, index-side-conditioned): the β
  step's commutation with the telescope substitution IS this
  lemma, composed;
* `mkAppN_instantiate1` — spine distribution (the ι fire's
  reduct-shape under substitution);
* `abstract1_instantiate1` — the open/close roundtrip under
  `fvarConsistent` (the telescope's `substA d a := (·.abstract1 d)
  .instantiate1 a` collapses on opened material by exactly this);
* the bounds/scoping transports (`looseBVarsBounded_abstract1`,
  `WScoped.abstract1`, `fvarConsistent_abstract1/instantiate1`)
  and the `instSeq`/`liftLooseBVars` families.

**To write** (bounded, syntactic):
* the `substA`-distribution family over constructors (abstract1
  and instantiate1 are both structural — per-constructor
  one-liners);
* the three per-step commutations as COMPOSITES: β (contractum
  image via `instantiate1_instantiate1` under the closedness of
  telescope arguments — `TelescopeOk` carries `SubjInv`, whose
  `looseBVarsBounded 0` is the lemma's side condition, BY DESIGN);
  ζ (same shape); ι (fire image: ctor heads and spine shapes are
  `substA`-stable structurally, the rule RHS is closed so its
  image is itself, `mkAppN_instantiate1` distributes the reduct);
* the cert-leg stability for the β legs (the substituted infer/
  defeq runs are NOT claimed — the subst-sim's forward factoring
  only maps REDUCTION steps; the β-cert gates on the substituted
  side come from the loops' own decomposed runs, by determinism —
  the design's never-re-run discipline).

The subst-sim map seal follows with these composites as its kit.

### Commutation kit, part 1 LANDED; the β/ζ composite needs the direct induction

Landed (compiled, warning-free): `substAK` (the one-binder
close-and-plug), `abstract1_eq_self` (identity on `d`-fresh terms —
the freshness supplied at the walk by `fvarLeaves_lt_of_wscoped`),
`substAK_eq_self` (**the spine arguments are `substAK`-INVARIANT**
— the substitution acts only on the cores, a real simplification
for every walk case), and `abstract1_instantiate1_comm` (abstraction
commutes with instantiation by a `d`-fresh argument, cursor-shift
form).

**Finding at the β/ζ composite** (`substAK_instantiate1`): the
composition route through the landed pieces does NOT assemble — the
middle form plugs the VALUE'S IMAGE where the target has the value,
and `instantiate1_instantiate1`'s closedness side condition fails
on abstracted terms (`v.abstract1` carries the introduced bvar).
A draft with placeholder gaps was written and WITHDRAWN before
commit (the no-sorry rule enforced at the working tree).  The
composite needs its own DIRECT structural induction — one pass over
the body with the bvar/fvar index arithmetic handling the
general (non-fresh) value, the standard de Bruijn substitution
lemma in this codebase's fvar-annotated setting.  Its statement
(unchanged): `(substAK d (k+1) a b).instantiate1 (substAK d k a v)
k = substAK d k a (b.instantiate1 v k)` for closed `d`-fresh `a`
and closed `v`.  Next seal: that induction, then the ι composite
(structural, `mkAppN`-distribution based), then the subst-sim map.

### The β/ζ composite SEALED (the direct de Bruijn induction)

Landed (compiled, warning-free, zero sorries): `substAK_cursor`
(cursor-independence: `substAK d k a v = substAK d k' a v` for `v`
with loose bvars bounded by `j ≤ k, k'` — the retargeting lemma the
binder arms need to move the plugged value's cursor under a binder)
and `substAK_instantiate1` (the composite itself, exactly the frozen
statement).  Two findings from the induction:

* **The freshness hypothesis fell off.**  The composite needs only
  `a.looseBVarsBounded 0` (and closed `v`); `d`-freshness of the
  argument is NOT required — the `fvar d` arm closes because closed
  `a` is `instantiate1`-invariant at any cursor
  (`Setlec.Expr.instantiate1_eq_self` + `looseBVarsBounded_mono`),
  regardless of whether `a` mentions `d`.  The walk still supplies
  freshness (its arguments are `substAK`-invariant spine members),
  but the lemma is the standard one.
* **Mechanization**: the kernel's `if`-normal forms are UNSTABLE
  across elaboration passes (`x = x` conditions sometimes decide to
  `True`, sometimes stay literal; `rw` fires on one side only when
  the two sides' branches differ).  The robust pattern used
  throughout: `have`-ascribed equations with concrete `if`-goals
  discharged by `simp`/`omega`-backed `if_neg`/`if_pos`, plus
  `simp only [if_neg h]` (not `rw`) when both sides carry the same
  condition.  Structural arms are `show`-distributed (substAK is
  rfl-structural) + IHs, binder arms retarget via `substAK_cursor
  hvb (Nat.zero_le _) (Nat.zero_le _)`.

Next: the ι composite (fire-image under `substAK` — ctor-head
stability + closed rule RHS + `mkAppN` distribution; needs
`substAK_mkAppN`), then `whnfCore_subst_sim`'s map + induction.

### The ι composite SEALED — the commutation kit is COMPLETE

Landed: `mkAppN_abstract1` (spine distribution under abstraction)
and `substAK_mkAppN` (the telescope substitution distributes over
`mkAppN` — the ι fire result, `mkAppN` of the rule RHS over
`args.take rP ++ margs.drop ctorParams`, maps to the fire on the
mapped spine; the RHS's own invariance is `substAK_eq_self` on the
env-stored closed term, applied at the sim's site where EnvWF
supplies closedness).  List surgery on the spine parts is
`List.map_take`/`map_drop`/`map_append` at the consumer.  The kit
now holds: `abstract1_eq_self`, `substAK_eq_self`,
`abstract1_instantiate1_comm`, `substAK_cursor`,
`substAK_instantiate1`, `mkAppN_abstract1`, `substAK_mkAppN`.
Next: `whnfCore_subst_sim`'s map seal, then its induction.

### `whnfCore_subst_sim` MAP SEALED — `RawReach` + the two claims

Landed (compiled): `RawReach μ env d G` (the gate-free image trace,
16 constructors), `RawReach.trans`, `RawReach.mono_budget`,
`WhnfCoreSubstSimF` / `WhnfLoopSubstSimF` (cursor-0 `substAK` images
of depth-`(d+1)` runs are traced at depth `d`, ceilinged by the
run's knot fuel), `SubstSimClaims` (the `ShiftClaims`-pattern pair).

**The clause table** (opened kernel behavior → trace constructor):
leaf clauses → `refl` (incl. the `fvar d` head: both images are `a`,
the image may reduce FURTHER — the forward-only clause); `letE` →
`zeta`; app head-run → `appL` + IH; fired β → `beta` via
`substAK_instantiate1` (stuck β = congruence-only endpoint — no gate
in the trace); iota → the three fire rows with the major's own trace
NESTED (whnf sim + `litNat`/`litStr` conversions), the fire's image
via `substAK_mkAppN` + `substAK_eq_self` on the closed rule RHS
(`EnvWF`); proj → `projC` + `projFire`; loop tier adds `delta`
(image commutes — `substAK_unfoldDefinition`, a kit addition owed at
the induction) and the three nat rows (arg traces nested; op names,
guards, `natOpResult` all term-independent).

**Treatment decisions (frozen):**
* **No certificate gates in the trace** — the det-sync break's
  resolution.  The walk holds a sort-successful actual run; at every
  point where the trace claims a step the actual run's gate refused,
  the actual endpoint is head-stuck non-sort (`loop_dead_exit`,
  `unfoldDefinition_none_of_recInfo`) — contradiction.  Gate facts
  therefore never appear as constructor premises; env-syntactic,
  term-independent facts (lookups, counts, caps flags, op names,
  guards) DO, because the forcing side needs them to align the
  actual run's dispatch.
* **No free argument-position congruence** — a gratuitous argument
  step would break the endpoint's syntactic agreement with the
  actual run (whose stuck spines are returned verbatim).  Majors
  reach only inside the iota rows.  REBASE-CRITICAL.
* **Rescue rows carry fabrication data existentially** (`ust`,
  `targs` are infer-derived opened-side; the sim plugs their
  images).  K's field segment is emptied by `cnF = 0` at the
  consumers (StoredWF's `ctorParams = cnP`); eta's fields ride
  `etaFabArgs` verbatim — the residual infer-lockstep seam is
  `EtaRescueSortAgree`'s, exactly as routed.
* **Budget ceiling `G`**: the one carried run (`litStr`'s closed
  whnf of the string expansion) ships under `g ≤ G` with
  `mono_budget` — the both-fuel-bounds axiom honored in ceiling
  form; consumption is det-only (`KnotFuelDet`), never re-assembly.
  The sim produces the depth-`d` run from the opened depth-`(d+1)`
  one via the DISCHARGED `ShiftClaims` battery (Deep.lean 2837) +
  `shiftFrom`-identity on fvar-free terms + `whnfPres_leaves`.
* **Trap sweep**: SortCohAt phantom untouched; the WhnfCoreIdem
  tombstone not consumed; strategy-superset rule inapplicable
  (proof-side relation, not checker strategy); k = 0 specialization
  is sound — `whnfCore`/`whnf` never reduce under binders, so no
  cursor bump ever occurs on the subject path.

Next: the induction (`LeavesPres` skeleton, fuel-indexed; per-fuel
`SubstSimClaims`), with `substAK_unfoldDefinition` sealed en route.

### Sim map AMENDED (`whnf` tier) + the helper kit sealed

Pre-build on the induction found the knot-tier gap: the core body's
internal `r.whnf` runs are `whnf`-at-`fuel` (the predecessor
record), which neither the core nor the loop claim covers —
`WhnfSubstSimF` added, `SubstSimClaims` now three-tiered with the
discharge order `whnf` (from predecessor loop) → `core` (body) →
`loop` (from same-fuel `core`+`whnf`).  Helpers landed:
`not_hasFvar_of_fvarLeaves_nil`, `substAK_of_const_head` /
`substAK_getAppFn_const` / `substAK_getAppArgs_const` (image
spines), `substAK_unfoldDefinition` (delta commutes; closed stored
values via `EnvWF` + `instantiateLevelParams` transports),
`substAK_etaFabArgs`, and `whnf_closed_depth_down` (the DISCHARGED
`ShiftClaims` battery at `shiftFrom 0`-identity on fvar-free terms +
`whnf_leaves` — the transport the `litStr` trace rows ride).
Preservation suppliers located, all landed: `whnfCore_looseBVars` /
`whnf_looseBVars` (InferLeaves), `whnfPres_WScoped`,
`whnfCore_leaves`/`whnf_leaves`; inversion suppliers:
`whnf_app_inv`, `whnf_proj_inv`, `iotaRec_inv`, `majorToCtor_inv`
(carries the fabrication's scope-guard facts), `reduceNat_inv`,
`projLitToCtorP_inv`.  Nothing new to prove on the preservation
tier.  Next: the induction itself.

### `substSimClaims` DISCHARGED — the substitution simulation lands

The deepest theorem of the arc is sealed: `substSimClaims (henv :
EnvWF env) : ∀ fuel, SubstSimClaims μ env fuel` — every tier
(`core`/`whnf`/`loop`) at every knot fuel, by the `LeavesPres`-class
fuel induction with the ratified tier order (whnf from predecessor
loop; core from the body walk; loop by budget induction consuming
same-fuel core+whnf).  The clause walk landed exactly per the map's
table: trivial arms `refl`; ζ/β through `substAK_instantiate1`;
the app head through `appL`; iota through `iotaRec_inv` +
`substSim_major_trace` (the slot's whnf trace + `litNat`/`litStr`
conversion steps, the string expansion transported one depth down
through the discharged shift battery) + the three fire rows off
`majorToCtor_inv` (plain via image spines; K and eta via the
fabrication existentials — `hma` re-expressing the fab's spine, the
`rl'`-singleton `find?` collapse, `substAK_etaFabArgs` for the eta
fields); proj through `whnf_proj_inv` + `projC`/`projFire`; the nat
rows through the new `reduceNat_decompose`; delta through
`substAK_unfoldDefinition` + the new `unfoldDefinition_pres`.
Preservation rode entirely on landed suppliers
(`whnfCore_looseBVars`/`whnf_looseBVars`, `whnfCore_WScoped`/
`whnf_WScoped`, `whnf_leaves`) plus the new `litMajor_pres` /
`litToCtorIfNat_cases`.

**Mechanization notes banked**: constructor bullets against reduced
subjects need `show … from`-coerced rewrite equations (the goal
holds `.app (sA f') (sA x)`, the lemma speaks of `substAK … (.app
f' x)` — defeq, but `rw` is syntactic); deferred `?_` premises
leave relation endpoints (`M`) unconstrained — pin them with
explicit `(M := …)`; `rw [h] at h₁ h₂` fails on the first
hypothesis without an occurrence — list only carriers; a spliced
`python s.index` end-anchor MUST be searched from the start offset
(a first-occurrence match duplicated 10k lines mid-session —
excised by line surgery; scripts now assert anchors).

One editorial note: the K/eta rows needed NO ctorInfo unification
at all — the fire result depends only on the rule's own counts and
the fabrication spine, so the planned injection machinery was
deleted rather than repaired.  Next per the coordinator: the
mechanical SortCoh split seal, then the walk's induction.

### SortCoh SPLIT (mechanical seal, pure motion)

`SortCoh.lean` (14,425 lines) split into seven part-files under
`Setlec/SetR/Annot/SortCoh/` with a 17-line umbrella preserving the
historical module name (downstream imports untouched: `SortCohFrame`,
`SetR`).  Cut at the actual dependency seams (file order = import
order = the original top-down order): `Claims` (det obligation,
leaf discipline, claim + ceilinged families, run algebra, cert-loop
decomposition, transports, (A-T), R-a, dual shell, 2119 lines),
`Mono` (mono batches, knot chain, nat-chase, 2533), `Discharge`
(trio tier, (B), summit skeleton + StoredWF/flat-spine kits, 3883),
`CoreLock` (substitution-transport kit, seams, coreLock, loop
dispatch, 1951), `LoopLock` (lockstep tier + zip head cases, 2124),
`Theta` (walk statement + commutation kit, 456), `SubstSim` (map +
helpers + induction, 1475).  Each part re-opens the namespace, the
two `open`s, and (from `Discharge` on) `section Discharge` with its
`{μ} {env}` variables.  Zero statement changes; zero relocation
warnings (the V-freedom convention and linear structure meant no
re-derivations surfaced).  Battery green, axioms 12/12.

### The Θ engine tier E1–E3 SEALED (embeddings, trace image, telescope trace)

Three engines land between the simulation and the walk:

* **E1 — the identity embeddings** (`whnfCore_toRawReach`,
  `whnfLoop_toRawReach`, with `whnfLoop_pres` as their preservation
  supplier): a depth-`d` run embeds as a trace at its own depth with
  ZERO new inductions — shift the run one depth up (the `ShiftClaims`
  battery; `Setlec.whnfLoop_shift` de-privatized in `Deep.lean`, a
  one-word visibility change), apply the simulation at a dummy closed
  argument, collapse both `substAK`s by `substAK_eq_self` (the
  subject is `d`-fresh).  The shift battery pays a second time.
* **E2 — the trace tier**: `RawReach.pres` (the closedness package
  travels along gate-free traces) and `RawReach.image` (a trace at
  `d + 1` maps under one `substAK` to a trace at `d`) — the map
  AMENDED en route: the rescue rows (`iotaK`/`iotaEta`) now carry
  their fabrication spines' closedness (`htb`/`htw`), supplied in
  the sim's discharge from `majorToCtor`'s own scope guards (the
  fabrication's `wscopedB`/`looseBVarsBounded` checks — no infer
  preservation needed, hence no `LeavesBounded` threading).
  Suppliers: `whnf_closed_out_fvarfree`, `natOpResult_closed`
  (`delta` + scripted 16-way `by_cases`; `unfold` diverges on the
  if-chain — banked), `substAK_bounded`/`substAK_WScoped`.
* **E3 — the telescope trace** (`thetaSubst₁_trace`/`₂` +
  positional bounded/WScoped folds): a trace at the telescope's
  inner depth maps down the whole `Γ` (fold of E2 over the entries,
  packages from `TelescopeOk`).

With E1–E3 and `substSimClaims`, the walk's per-arm image
machinery is complete; the remaining engine is E4 — the rebase
(sort-successful loops transported along traces, the forcing sweep)
— whose map seal is next, with the iota-divergence seam treatment
at full strength.

Note: the session restart cleared the scratchpad's axiom-sweep
file; rebuilt covering the four `no_proof_of_Empty*_R` mains plus
eight branch summits (coreLock, loopLock, certLoop_sortAgree,
zipProjHeadCase_of, substSimClaims, RawReach.image,
thetaSubst₁_trace, whnfLoop_toRawReach) — 12/12 at exactly the
three standard axioms.

### STOP-FINDING at E4 (the rebase): two divergence seams beyond the routed coverage

The pre-build on the rebase engine (`RawSortRebase`: a sort-successful
loop transported along a gate-free trace), run at full strength
before any code, taxonomizes the trace-vs-actual divergences.  The
actual (gated, deterministic) run and the (gate-free) trace diverge
exactly where an IMAGE gate resolves differently from its opened
original.  Complete taxonomy of the divergence sites:

1. **Gate refusals → actual STUCK, dead-shaped** (β-cert, proj-cert,
   iota level/defeq certs, spine-length): the actual halts at a
   lam-headed app spine / full rec-spine (recInfo) / stuck proj.
   These forms are loop-dead (`unfoldDefinition_none_of_recInfo`,
   shape-none `reduceNat`, no β/ι) and non-sort — at any position
   whose context demands a sort they REFUTE, and as app/proj heads
   they kill the outer (length/shape mismatches force `iotaRec`
   none).  HANDLED by a `DeadCore` disjunct + the landed dead-exit
   family.
2. **Iota fire divergence** (rescue-vs-plain / rescue-vs-rescue):
   both sides fire the SAME rule (single-rule gate for rescues,
   `find?`-pinned otherwise) with the SAME `args.take rP` prefix —
   the results differ ONLY in the field segment.  K rows: `cnF = 0`
   empties both segments — ALWAYS agree (the record's "K is local"
   verbatim).  Eta rows: the segments are projection towers of the
   two sides' majors — the ETA-FIELD SEAM, the one place
   infer-lockstep enters, exactly as the record priced.
3. **Nat-arg divergence** (NEW, the finding's sharp edge): a nested
   major's trace passes a fired nat row (image of an opened
   `reduceNat` fire); if an image gate refused inside the ARG's own
   whnf, the actual arg is dead-stuck, the actual `reduceNat`
   returns none — and then the actual DELTA-UNFOLDS the op (the
   guard guarantees the stored definition exists!) and grinds the
   unfolded body on the stuck argument.  The actual is ALIVE and
   divergent, and relating the grind path to the claimed literal
   requires reasoning about an arbitrary stored definition body —
   NOT boundable by local analysis.  (The install-time NatOpsOk
   recurrences certify the semantic agreement, but that is a
   model-tier instrument, not a loop-syntactic one.)

**Two structural mitigations verified during the treatment**:
* `whnfCore` contains NO delta/nat steps — the CORE-tier trace
  fragment (what the push's head analysis needs) meets seams (2) and
  (3) only NESTED inside iota majors (whose whnf is loop-tier).
* The demand-driven reading of the frozen plan ("the loops β-fire",
  "re-decompose the ACTUAL runs") keeps the pushed continuations as
  SEGMENTS of the given `.ok` runs (their own gates already passed)
  — the engine is needed only to ALIGN the actual head-normal form
  with the run's opened image (λ for the push), where the taxonomy
  above applies at the head's core run + its nested majors.

**Proposed resolution (ratification requested)** — R1, the
core-dichotomy route: state E4 as the CORE-tier alignment
  `RawReach(core fragment) f f' → whnfCore g d f = .ok W →
     (∃ g₂, whnfCore g₂ d f' = .ok W) ∨ DeadCore W ∨ MajorSeam …`
with `DeadCore` refuted at sort-demanding contexts by the landed
dead-exit family, and the residual seam (eta fields / nat grind at
a nested major) packaged in ONE routed Prop whose discharge gets its
own dedicated analysis (candidate instruments: the eta-rescue's
`structEtaCert` runs carried by the actual, the guard's stored-shape
facts; possibly an arena-reality-guided restriction finding).  The
alternative (amending `ThetaWalkClaim` to carry image-side head
facts) merely relocates the same seam.  STOP — reporting before
building either.

### E4 map SEALED per R1 (`Align.lean`)

Landed (compiled): `DeadCore` (three shapes — lam-headed spine,
proj-headed, recursor spine at ≥ mI+1 args; shape-only, per the
treatment's two consumer routes), `LitResidue` (the actual parks at
a literal, the trace already converted — consumers re-run their own
conversion by determinism), `IotaFireSeam` (both sides fire with
different results; result-inequality is the progress marker; the
claimed provenance, remaining trace and actual continuation carried
whole — defensively general so any fire-alignment hole routes here
with evidence instead of blocking), `NatGrindSeam` (dead-parked
argument + declined `reduceNat` + the guard-guaranteed unfolding's
continuation, both arities in one pack), the two out-disjunctions
(`CoreAlignOut`/`LoopAlignOut`) and claims (`CoreAlignF`/
`LoopAlignF` — trace vs actual run, mutual at iota majors and proj
scrutinees vs whnfStep cores).

**Discharge plan** (the treatment's supplier list): structural
induction on the trace, runs universally quantified per arm; the
actual's decompositions via `whnfCore_app_decompose`/
`whnf_proj_inv`/`iotaRec_inv`/`whnfStep_decompose`/
`reduceNat_decompose`; assemblies via `whnfCore_app_assemble` (+ a
new proj assembly), `iotaRec_mono`, `whnfLoop_det`, `KnotFuelMono`;
dead exits via `loop_dead_exit` + `unfoldDefinition_none_of_recInfo`
+ NEW suppliers: `whnfCore_lam` identity, a letE run extractor,
`iotaRec` none-of-overlength, `reduceNat` none-of-dead-shapes (the
nat-guard/recInfo disjointness).  Chaining: aligned outputs re-enter
the next arm's decomposition; seams propagate outward unchanged.

### E4 DISCHARGED — the alignment engine lands (`alignAt`)

`alignAt (henv : EnvWF env) (hm : KnotFuelMono μ env)
(hPC : ProjCtorWF env) : ∀ g, CoreAlignAt μ env g ∧ LoopAlignAt μ
env g` — the rebase/forcing engine, discharged in full (1,359-line
part-file, zero sorries).  Architecture as ratified-and-refined:

* **The by_cases simplification** (the discharge's key find): at
  every fire node the engine DECIDES result-equality (`Expr` has
  `DecidableEq`) — equal fires chain, unequal fires route to the
  seam with full evidence.  No major-merging, no fire-alignment
  reasoning in the engine at all; the seams absorb exactly the
  divergences the STOP-finding taxonomized.
* **The knot measure**: strong induction on the input run's knot
  fuel (scrutinee whnfs and internal continuations sit one fuel
  down in the inversions — the kernel's own discipline); the loop
  tier at each fuel by budget induction consuming the same-fuel
  core tier.  The mutual (core ↔ loop at scrutinees vs whnfStep
  cores) is well-founded on (knot, budget) — no trace-structural
  mutual needed: `coreAlign_step` inducts on the trace with
  fuel-IHs; `loopAlign_step` never cases the trace (pendings carry
  the peeled data, so the budget IH consumes them wholesale).
* **The pending rows** (map amendment, the erased-residue trap's
  resolution): `PendingDelta`/`PendingNat`/`LitResidue` carry the
  loop-tier work a core run parks at (with `PendingNat` carrying
  the non-recursor fact its guard derived — needed for the fired
  refutations); the loop tier consumes them (its own delta is the
  same unfolding by purity; its nat outcome is decided against the
  claim).  `DeadCore` gained the lit-headed-spine row; `NatSeam`
  the fired-vs-claimed-delta and over-application rows; `ProjSeam`
  the nat-packing row.  Fuel bounds on the aligned outputs (the
  axiom's fourth instance) made the appL chain measure-clean:
  the head aligns at `g-1`, assembles at `≤ g`.
* **Suppliers landed en route**: `unfoldDefinition_inv`/`_app`,
  `whnfCore_nonrec_id` (const-headed non-recursor runs are the
  identity — the spine inversion's fired disjunct refuted through
  `iotaRec_fired_head`), `whnfCore_proj_congr` (the proj clause's
  tail is a function of the scrutinee's whnf — same-fuel congruence
  by double unfolding), `whnf_lit_id` (two knot levels),
  `iotaRec_none_of_arglen`/`_of_dead`, `DeadCore.app`/`.not_lam`,
  `natLitSupported_succ_not_rec`, `natOpGuard_not_rec` (the op is
  its own dependency; 16-way name analysis by `decide`),
  `LoopAlignOut.weaken_l`.
* `ProjCtorWF` (projection-table constructors are stored
  constructors) joins the install-facts docket beside `StoredWF`.

Next: the walk's arm groups — the push consuming `substSimClaims` +
`thetaSubst₁_trace` + `alignAt` — then the depth-zero consumers.

### The walk's pre-build, round two: the θ-image-of-cert wall (STOP)

With E1–E4 landed, the walk's arm-group pre-build (run at full
strength on the syn/congruence group before any code) finds the
frozen treatment's recipe incomplete:

**The wall.**  The syn arm's "certZip_subst folded over Γ" builds
the θ-image zip of a SHARED core — sound at one telescope level
(the abstracted cores coincide, `certZip_subst` with a refl body
does everything).  At two-plus levels the fold must map a zip whose
`.cert` arms (the deeper entries' certified argument pairs, which
may mention outer opened fvars — arena-real dependent arguments)
under `substAK` — and certificates do not transport under
substitution (the det-sync break, again).  `CertZip` has no arm for
the θ-image of a certified pair; the images are certified at NO
fuel.

**The measure edge.**  The natural resolution — recurse the WALK on
image-cert pairs (unfold the cert to its `defeqLoop` run) — lands
at the SAME `fcK` (TelescopeOk's certs sit at `fcK + 1`, whose
unfold is knot `fcK`) with a fresh `L`, outside the `[fcK, L]`
measure.  Re-indexing TelescopeOk's certs one tier down restores
the measure but breaks supply symmetry questions that need their
own audit.  ZipBelow-consumption instead requires SUM-STRICT budget
decrease, which the E4-rebased runs (bounded `≤`, not `<`) do not
provide on their own.

**Verified positives from the same pre-build**: the pushed entries'
argument pairs are the walk's OWN spine zips (no loop-gate certs
needed — supply confirmed); the post-core syn case reduces by
E3+E4 to same-`P` images with `P` core-normal, where the
sort/λ/Π/lit/below-zone-fvar cases all discharge or refute cleanly
— the wall is EXACTLY the in-zone-fvar and nested-cert-argument
corners.

**Options for ratification**:
(A) a `CertZip` θ-arm (the image-of-cert constructor) — zip-tier
ripple: every discharged zip consumer gains an arm, each routing to
a Θ-shaped hypothesis (mechanical but wide);
(B) walk-side mutual: state the image-pair walker as a SEPARATE
claim proven mutually with the walk, its cert-leaves recursing
through a REVISED measure ([fcK, L] ↦ [fcK, telescope-weight, L] or
TelescopeOk re-indexed at `fcK`);
(C) strengthen E4's aligned outputs to STRICT budget decrease where
a step was consumed (auditable: the aligned assembly reuses the
actual's continuation, one step shorter) — unlocking
ZipBelow-consumption for the image-pairs at equal fuel.
Leaning (C)+(B-measure-audit): (C) is a bounded E4 amendment in the
axiom's spirit; with strict decrease the image-cert pairs flow
through ZipBelow exactly like every other zip.  STOP — reporting.

### The consumer seal — two amendments, and the λ row's good news

Opening the interp2-consumer lane (arc steps 4–5, hypothesis-first,
in parallel with Θ) began with the brief's pre-build check: every
field of the Claims2 interface must have a named supplier in the
coherence tier's landed or frozen statements.  Two failed, both
repaired here; one row came back better than designed.

**AMENDMENT 1 — the currency seam (`Annot/EnvS2.lean`).**
`annot_ok2`/`mem_type2` landed at migration step 1, stated over the
`Annotates` *relation*, **before** R1 took canonical annotations.
They cannot serve `denote2`, and the obstruction is structural rather
than a missing lemma: `Annotates` has no structural `letE` clause —
only `zeta`, so it annotates the ζ-reduct — while `denote2`'s `letE`
clause *is* structural, and so is `denote`'s
(`Setlec/Verify/Denote.lean`).  **For any subject carrying a `let`, a
`denote2` output is not an `Annotates` annotation of the same term,
and no bridging theorem between the two can exist as they are
stated.**

The seam was invisible for a reason worth keeping: it is *vacuous on
the environment side* — stored terms carry no `letE` today, the
checker zeta-expands at annotation time — and bites only on **subject**
terms, which is exactly what `Claims2` quantifies over.  `denote2` also
had **zero consumers tree-wide**, so the two currencies had never met.

Repaired by option 1 (the ruling): `EnvS2` gains `acval`,
`acval_erase` (`denote2_erase`'s hypothesis), `acval_ok2` and a
`denote2`-shaped `mem_type2`.  Restated in place rather than
additively — the consumer sweep found `Annot/SimSubst.lean` *imports*
`EnvS2` without using it, and nothing else references the fields at
all.  `cval_annot` stays: it closes a named ledger obligation about
the relation and is not in the seam.  `EnvS2.empty` re-discharged
(`acval_erase` is `rfl`; the empty `acval` is the same `.const .empty
[0]` leaf one level up).

*Rule: when a resolution changes a tier's currency, the fields stated
in the old one are not merely stale — check whether the two currencies
can denote the same object at all before assuming a bridge exists.*

**AMENDMENT 2 — the app slot's kind-`0` asymmetry (`Annot/Ok2.lean`).**
`AnnotOk2`'s λ clause carried a kind-`0` fibre component; its app
clause did not.  That is a gap, not a saving: `app_mem_piR` needs
exactly `v = 0 → ∀ x ∈ˢ A, B x ∈ˢ univZero`, the slot's `B` is
∃-bound so no handle survives extraction, and the truth-value route
does not substitute — an inhabited `piR 0 A B` gives only that
`B ⟦a⟧` is *inhabited*, never that its inhabitant is `pt`.  That is
**finding B5's wall re-appearing in the membership formulation**, and
at kind `0` the app case could not close from the invariant at all.

Why it survived three consumers: `graded_beta_pos` and
`AnnotOk2_beta_pos` require positivity, and `AnnotOk2_beta_zero` takes
the missing fact as an explicit `hmem`.  *A clause whose only
consumers are guarded by the very hypothesis that hides its gap will
not be found by its consumers.*

Established, not assumed, in the same seal: `appSlot_of_pi` /
`AnnotOk2_app_of` build the slot — new component included — from the
**annotated `Π`'s own codomain sort fact**, supplier
`HasSort.mem_univ` (`Annot/Kinding.lean`) at the `Π`'s numeral: the
same route `Annotates.lam`'s cached `HasSortC` already takes for the λ
clause.  The two binder clauses are symmetric again.  `SlotChain`
(`Annot/Spine2.lean`) strengthened in step so `AnnotOk2_spine_slots`
reads the slot off unchanged; `slotChain_fits` carries and drops the
new component (it uses positivity only); the `liftN`/`inst`
congruences ride the existing rewrites, because the component mentions
only the ∃-bound `v`, `A`, `B` and so is invariant under the
environment change.

**THE λ ROW CLOSES, AND THE EMPTY-DOMAIN CASE IS FREE.**  The brief's
primary test was whether interp2's λ case closes from the interface
including the empty-domain row.  It does, and for a simpler reason
than the design anticipated: `lamR_mem` has no premise beyond the
fibre facts, and at `⟦A⟧ = ∅` *both* the fibre membership and the
kind-`0` fibre condition are vacuous.  So the empty-domain row needs
**no semantic fact about the annotation whatsoever — only the numeral,
which is in the term.**  No validity machinery is involved, which is
just as well: `ValidInfer` is refuted (`Annot/Validity.lean`,
`validity_refuted`), so the B5′ route the brief named is not available
and is not needed.  The actual supplier of the λ numeral is
`Annotates.lam`'s cached `HasSortC`, two-regime as `Infer.lam` is:
direct at the innermost binder of a chain (#152's guarded premises,
stated at the checker's own `B'` and `DefEq`-linked, per finding A5),
by `hasSortC_pi_of` induction at inner binders.

**Ledgered for the record, from the same sweep:**

* `SortSubstStable` (`Annot/SimSubst.lean`) takes `mS : EnvS V env` —
  the **collapse-lane** invariant, not `EnvS2`.  Re-signing it to the
  `EnvS2` world belongs to the leaf wiring.
* `Claims2` should name the **two frozen zip obligations**
  (`ZipWhnfSortAgree`, `ZipSortOfAgree`, via `ensureSortAgreeRQ_of_zip`
  / `sortOfAgreeRQ_of_zip`), not the fifteen-hypothesis shells — the
  discharge tier already reduced both public claims to one obligation
  each.

### Arc step 4 — the second soundness's per-former skeleton

`Setlec/SetR/Interp2/Skeleton.lean`: the `interp2` soundness's case
statements, one per `AVExpr` former, each stated over exactly the facts
the frozen interface carries.  **Nine of ten formers close; the tenth
is deferred to its supplier.**

| row | interface facts consumed | status |
|---|---|---|
| `sort` | none | ✓ `univ_mem_univ` |
| `prf` | type is a `Prop`, and inhabited | ✓ proof irrelevance is definitional |
| `bvar` | `Sat2` | ✓ |
| `pi` | domain at `u`, codomain at `v`, both hereditary halves | ✓ `piR_mem_univ`, the `imax` rule *exactly* |
| `lam` | body's membership, kind-`0` fibre condition, hereditary halves | ✓ **no empty-domain side condition** |
| `app` | function at an annotated `Π`, argument in the domain, the `Π`'s kind-`0` fibre condition | ✓ **at both kinds** |
| `letE` | body's two facts at the substituted value | ✓ ζ is an identity, not a step |
| `eqE` | the two sides' hereditary halves | ✓ `eqv_mem_univ` |
| `proj 0/1` | the subject's `Σ`-package — i.e. the invariant alone | ✓ (`sfst_mem_gen`/`ssnd_mem_gen`, the general-fibre forms) |
| `const` | — | **DEFERRED**, see below |

**The app row is the amendment's dividend.**  `sound_app` closes at
*both* kinds and `app_mem_of_slot` closes from the **invariant alone**.
Neither was possible before the app clause gained its kind-`0` fibre
component at the consumer seal: `app_mem_piR`'s `hB0` had no supplier,
and the truth-value route yields only that the fibre is *inhabited*.
The clause repair turned the app row from a `Prop`-codomain residue
into a theorem — which is the single most consequential thing this seal
records, because rank-2/3's removals all land on that row.

**The λ row's freedom, now mechanized.**  `sound_lam` has no
empty-domain hypothesis and needs no validity metatheorem: `lamR_mem`'s
premise is a `∀ x ∈ˢ ⟦A⟧`, vacuous at `⟦A⟧ = ∅`, and so is the kind-`0`
fibre condition.  The numeral still *matters* semantically
(`lamR 0 ∅ F = pt` versus `lamR 1 ∅ F = ∅`) but it comes from the
**term**, and no semantic fact about it is needed to close the case.
This is why `ValidInfer`'s refutation does not block the consumer lane
— the brief's "B5′-style validity" route is neither available nor
required.  The `Π`'s domain numeral is likewise free: `interp2`'s `pi`
clause discards it, so the row holds at every annotation of the domain.

**The `const` row is DEFERRED, and deliberately not stated.**  Two
suppliers are missing, and both are migration step 2's:

* no annotated built-in type former — no
  `BConst.type2 : BConst → List Nat → AVExpr`.  `BConst.type` yields a
  `VExpr` and `denote2` maps `Expr → AVExpr`, so it does not apply.
  **Without it the row's conclusion cannot be written at all**;
* no `bval2_mem_type` — `Interp2/Value.lean` has every per-constant
  application law and the towers' own memberships, but not
  `ConstOk.lean`'s capstone over `interp2`.

Writing either here would be the T5 near-miss the campaign has ruled
against — a premise guessed at the consumer rather than stated by its
supplier.  So the row waits, ledgered with those two names as step 2's
entry condition for this file.

*Rule, a corollary of the supplier rule worth its own line: a case you
cannot even **state** is not a gap in the design — it is a missing
former, and formers belong to the tier that owns the objects.  Check
which of the two you have before calling STOP.*

### The wall ruling executed: (C)-audit, (B)-audit, the audited architecture (map seal)

**(C)-audit result — condition (i) answered by the measure, not by
E4.**  Sweep of every E4 aligned-output construction site: the
loop-tier aligned assemblies reuse the input run's own budget shape
(`⟨g, l+1⟩` at the step, `l₂ ≤ l` through the pendings) — the
core-tier alignment consumes CORE steps, which the loop budget does
not count, so strictness is genuinely unavailable at those sites
(zero-loop-step by construction).  Under the audited measure below
the strict form is also UNNECESSARY: no image-pair consumer needs
budget decrease.  E4 stands unamended; the axiom's extension
("every consumed step recorded as a strict decrease") is satisfied
vacuously at the loop tier and structurally by the new measure
elsewhere.

**(A) rejected, with reason (per the ruling)**: a `CertZip` θ-arm
would carry the image of a certified pair as a zip arm — usable
only if certificates transported under substitution, which is the
wall itself relocated into the relation.

**(B)-audit — the full reference graph and the audited measure.**
The finding that dissolves the wall: **the in-zone-fvar recursion
shortens the telescope** — an entry's argument pair is substituted
by the PREFIX entries only, so its walk/zip instances run at
`|Γ'| < |Γ|`.  With that slot the graph closes:

* Claims: the WALK (run-form, `ThetaWalkClaim`, unchanged) and the
  new **θ-zip walker** (`ThetaZipWalkClaim`, map-sealed compiled):
  spines over telescope-images of a ZIPPED pair at zip-fuel
  `fcz ≤ fcK + 1`.  The syn-walker collapsed into the zip walker
  (refl is a zip).  At `Γ = []` the zip walker's cert-arm IS
  `ZipCertSpineCase`'s data — the depth-zero consumers are its
  instances.
* Measure (proof-internal, lexicographic):
  `[rank, |Γ|, phase, zip-structure∕L, loop-budgets]` with
  `rank(walk at fcK) := fcK + 1`, `rank(zip walker) := fcz`,
  `phase(zip walker) = 2 > phase(walk) = 1`.
* The audited transitions: walk's δ/nat re-entries → same prefix,
  `L−1` ✓; the push → `rank−1` (the opened-body run one knot down;
  `Γ` grows under the dominant drop) ✓; walk's syn → zip walker at
  refl, `fcz := 0` (refl-zips are rank-free) — rank drops ✓; walk's
  congruence arms (appCong/spine/consts) → zip walker at
  `fcz = fcK` (the run's OWN `defEqList`/head certs sit at the
  run's knot) — rank drops ✓; walk's in-zone fvar → zip walker at
  `fcz = fcK + 1` (TelescopeOk's tier), equal rank, `|Γ'| < |Γ|` ✓;
  zip walker's cert-arm → walk at `fcK := fcz − 1` (the unfold),
  equal rank, phase drops ✓; zip walker's structural/loop-step
  re-entries → its inner slots (the landed ZipApp-discharge's
  [zip-structure, knot] pattern) ✓.
* Supply re-verified: pushed entries' argument pairs are the walk's
  own spine zips; congruence-arm zips come from the run's own
  certificates one knot down; no loop-gate certs anywhere.

The verified positives from the wall report carry over unchanged
(post-core syn reduces by E3+E4 to same-`P` core-normal images;
sort/λ/Π/lit/below-zone-fvar discharge or refute cleanly).  Next:
ratification of the audited architecture, then the mutual discharge
in arm-group seals, then the depth-zero consumers as zip-walker
instances.

### The (B)-audit, round three: the sealed measure OVERTURNED — the audit's own full strength (STOP)

Extending the audit past the transition table to (a) the PUSHED
telescope's tier supply and (b) the re-entry loops' assembly knots
falsifies the `[rank, |Γ|, phase, …]` measure sealed one commit ago:

1. **Tier/knot decoupling is forced.**  `ThetaWalkClaim` couples the
   run's knot and `TelescopeOk`'s tier (both `fcK`).  The push drops
   the knot but CANNOT re-tier the old entries' certificates down
   (no fuel down-transport), and the pushed entry's certs arrive at
   the ORIGINAL tier (the spine zips).  So the telescope tier is a
   GLOBAL constant `T` of each summit entry and the knot descends
   independently — the frozen claim needs the two-fuel form.
2. **Pushes and in-zone entries trade `|Γ|` against the knot in
   opposite directions** — push: knot−1, `|Γ|`+1; in-zone: `|Γ|`
   strictly down, knot reset up to `T`.  No lexicographic order on
   (knot, `|Γ|`) covers both, and the growth is not potential-
   boundable (in-zone resets can re-grow past any prior state).
3. **The only globally descending currency is the GIVEN loops' own
   structure** — and the zip tier's landed ZipAppCase seal already
   recorded the exact discipline: "the claim must NOT recurse at
   the contracta — that leg would not decrease; the knot pays for β
   inline at `ga−1`".  The β-fires the push chases are CORE-internal
   to ONE `whnfStep` of the given loops: their processing must be
   INLINE down the loops' core runs (knot-descending), never a walk
   re-entry; the δ/nat re-entries descend the loop budgets; the
   cert exits descend `fc`.  The walk's real measure is ZipBelow's
   own `[fc, ga+gb, la+lb]` — the original bar — with the telescope
   as TRAVELING DATA (the defeq-run data consumed in sync with the
   inline core-walk), not a measure slot.

**Corrected architecture sketch (for ratification)**: the summit
discharge is an inline-processing induction in the ZipAppCase
style — primary on the loops' knots (`ga+gb`), the defeq-run data
(`PostCoreCert` at the current opened depth) traveling as a
hypothesis pack alongside the telescope; the E3/E4 engines align
the loops' actual core steps with the run's θ-images per layer;
zip-material exits through ZipBelow (fc-descent at cert exits,
budget-descent at δ/nat); the in-zone-fvar leaves exit through the
telescope pack's own zips at the SAME ZipBelow bar (their loops are
sub-runs at strictly smaller knots — the argument whnfs sit inside
iota/nat processing one knot down).  `ThetaZipWalkClaim` (beec972)
survives as the ENTRY-SHAPE (the consumers' interface) but its
discharge rides the corrected induction, not the overturned
measure.  The beec972 measure section is TOMBSTONED by this entry
(the tombstone-sweep rule applies: no future obligation may cite
`[rank, |Γ|, phase]`).  STOP — reporting before any arm code.

### Migration step 2, entry item 1 — `BConst.type2` (the annotated basis types)

`Setlec/SetR/Interp2/BasisType.lean`: the first of the two suppliers
the skeleton's `const` row waits on.  `BConst.type` yields a `VExpr`
and `denote2` maps `Expr → AVExpr`, so neither can produce a built-in's
*annotated* type — the former has to exist on its own, and now does,
for all eighteen constants.

**The annotation convention was inherited, not invented**, which is the
point: `Interp2/Value.lean` had already fixed it for the value side —
every binder's codomain slot carries the tower's **result sort** `r`
(sound because `piR`/`lamR` read the numeral only through `v = 0`, and
`imax x y = 0 ↔ y = 0`), every domain slot carries the domain's
**exact** sort (because `AnnotOk2`'s binder clauses and
`Skeleton.sound_pi` read it).  The two sides must agree numeral for
numeral or the capstone cannot typecheck, so the former was written by
reading the towers off `Value.lean` rather than by re-deriving them:
`natSucc` at `r = 1`, `natRec` at `u`, `punitRec`/`emptyRec` at `v`,
`psigma` at `max u v + 1`, `psigmaMk` at `max u v`, `quot` at `u + 1`,
`quotMk` at `u`, `quotLift` at `v`, `choice` at `u`, and
`quotInd`/`quotSound`/`propext` at `0` (their values are `pt`; their
types are propositions).

**One trap, named because it is easy to get backwards.**  A codomain
slot holds the sort of `B` *as a type*, so a codomain `.sort k` gets
`k + 1`, never `k`.  That is why `A → Prop` annotates as
`.pi u 1 A (.sort 0)` and is a **type** of sort `max u 1`, not a
proposition — exactly what `relSpace2` says.  Getting this wrong would
have made every quotient row silently Prop-valued.

**Faithfulness is checked, not asserted**: `type2_erase` proves
`(type2 c us).erase = BConst.type c us` on the nose, all eighteen cases
by one `simp`.  So the former adds annotations and nothing else, and a
*numeral* error is the only thing this file can get wrong — which is
precisely what entry item 2 will test.

**Entry item 2 is confirmed mechanical in shape.**  Probed before
sealing, on three constants across the difficulty range: the pattern
`simp only [BConst.type2, <smart constructors>, interp2_*]` reduces
`interp2 ρ (type2 c us)` to the tower's own space, after which the
existing membership lemma closes it (`natSuccV2_mem`,
`omega_mem_univ_succ`, `unitSet_mem_univ`).  What remains for
`bval2_mem_type` is that most **tower** memberships do not yet exist —
`Value.lean` has the application laws and the applied-form memberships,
but the bare-tower facts are `ConstOk.lean`'s (v1) and have no interp2
analogue.  So entry item 2 is "port `ConstOk.lean` (267 lines) onto
`piR`", not "invent an argument": sized, and with every case's target
already written down here.

### The corrected architecture's map tier SEALED (`ThetaRel.lean`)

Landed (compiled): `certZip_mono` (fuel lift — congruence-arm
argument zips at the run's knot lift to the tier, keeping spines
un-nested), `ThetaRel` (zip / packed / same — the traveling
currency; knot decoupled from the tier per round three),
`ThetaCoreSeam` (the landed `CoreSeam` shape with `ThetaRel`
material at head rows, dead rows verbatim, plus the `alignSeam` row
carrying the E4 seams outward), `ThetaCoreOut`, and the
`ThetaCoreLockF` claim (inline induction over the runs' knot sum;
zip rows delegate to the landed `coreLock`).  Next: the θ-coreLock
discharge, then the loop tier, then the tie and the consumers.

### The θ computation kit + THE PUSH ALGEBRA sealed

Landed in `ThetaRel.lean` (all compiled, zero sorries):
* the θ-image computation family (`thetaSubst₁/₂` on sorts, consts,
  lits, apps, Π-shapes, projs, spines — the leaf-invariances and
  distributions the same/packed analyses read);
* `instantiate1_abstract1_fresh` — the REVERSE roundtrip
  (abstracting a fresh opening recovers a bounded body; the missing
  half of the open/close algebra);
* `thetaSubst₁/₂_append` + `TelescopeOk.append` (the push's
  telescope extension folds);
* `thetaSubst₁/₂_scoped_id` (outer-scoped closed terms are
  θ-invariant — spine args in particular);
* `thetaSubst₁/₂_lam_beta` (the λ-image's shape with its β
  composite through the whole telescope); and
* **`thetaSubst₁_push`** — the arc's deepest single equality: the
  θ-append image of the OPENED body equals the actual β-contractum
  (`append` fold + reverse roundtrip + `lam_beta` + `scoped_id`).
  The inline push case now reduces to bookkeeping.
Also: `ThetaCoreSeam` gained the `certHead` row with `ThetaRel`
arguments (the congruence exits' shape), and `alignSeam` carries
its trace ceiling.  Next: the `same`-row core analysis
(`thetaSame_core`), then the packed tier and `thetaCoreLock`.

### The Θ relation MUTUALIZED (the same-λ push's forcing)

The `same`-row pre-build found the last structural constraint: a
shared-λ head fired against REL-related spine arguments pushes an
entry whose argument pair is Θ-related, not certificate-zipped — so
the telescope's argument relation must itself be `ThetaRel`.
Landed: the mutual pair `ThetaRel`/`TelescopeRel` (spines and
telescope arguments Θ-related; zips embed via `.zip`, and
`TelescopeRel.of_ok` embeds the claims' `TelescopeOk`), the kit
ported (`thetaRel_bounded₁/₂`, `thetaRel_WScoped₁/₂`,
`thetaRel_lam_beta₁/₂`, `TelescopeRel.append`), and
`thetaSubst₁_push` trimmed to its true inputs (the β composite +
the roundtrip facts).  All warning-free; battery green, axioms
12/12.  The `same`/`packed` analyses now have every structural
ingredient; next: `thetaSame_core` (one layer per invocation,
recursion through the claim at strictly smaller knot sums).

### Migration step 2, entry item 2 — the capstone port, thirteen of eighteen

`Setlec/SetR/Interp2/BasisOk.lean`: `ConstOk.lean`'s per-constant
memberships ported onto `piR`/`lamR` and `BConst.type2`.  **Thirteen
cases land; five resist, each for a different and nameable reason.**

Landed: `nat`, `natZero`, `natSucc`, `natRec`, `punit`, `punitUnit`,
`punitRec`, `empty`, `emptyRec`, `psigma`, `quot`, `quotMk`, `choice`.

**The port pattern held exactly as probed** — `show` the value at its
tower, `simp only` with `type2` + the smart constructors + the
`interp2` clause equations (which reduces the type to the tower's own
space, the payoff of having read the numeral convention off
`Value.lean` rather than choosing one), then `lamR_mem` down the
binders.  Three cases were *cheaper* than v1: `lamR_mem` carries no
universe side condition where `lamC_mem` needed `app_mem`'s codomain
premise, and `Empty.rec` is a **graph** here rather than `pt`
(`emptyRecV2 = lamR v … (lamR v ∅ …)`), so its case is two `lamR_mem`s
over a vacuous domain instead of v1's `pt_mem_piC_iff` argument.

**Two frictions worth reusing.**  `Nat.succ`'s wrinkle transposes
verbatim — `type2`'s step premise mentions the *value* `natSuccV2`
while `natStepSpace2` is written with the operator `natsucc`, and they
agree on `ω`, which is v1's `natStepSpace_eq` restated
(`natStepSpace2_eq`); it is needed under two binders, so the natRec
case goes through an explicit `interp2_type_natRec` equation built
with `piR_congr`, exactly as v1 built its `interp_type_natRec` with
`congr 1`/`funext`.  And a singleton level list needs normalising:
`quotT2 u` emits `.const .quot [u]`, whose `bval2` is
`quotV2 (lv [u] 0)`, so `lv` and `List.getD_cons_zero` join the simp
set or the rewrite misses.

**FINDING — `psigmaMk` resists, and the reason is a value-level
decision made two seals ago.**  v1's proof is four `lamC_mem`s then a
split on `max u v = 0`, and it works because `psigmaMkV`'s *body*
carries an explicit `if max u v = 0 then pt else spair a b` tag.
`psigmaMkV2` deliberately dropped that tag — "the annotation already
squashes the whole tower at `0`" — so the innermost `lamR_mem`
obligation becomes `spair a b ∈ˢ sigmaSet 0 A B'`, which is **false**
(`spair a b ≠ pt`, and a kind-`0` `sigmaSet` is a truth value).

The statement is still true: at `max u v = 0` the whole tower *is*
`pt`, and the truth-value chain is inhabited — over an empty `A` the
`piR 0 A …` layer is vacuous, and over an inhabited one `pt_mem_sigma`
supplies the witness.  But the argument has to be a **top-level case
split with a direct `piR_zero`/`truthVal` chain**, not `lamR_mem`.

*Rule: dropping a value-level regime tag does not remove the kind-`0`
argument, it MOVES it — from the leaf, where a pointwise lemma
discharges it, to the root, where the whole tower's inhabitation has
to be exhibited.  The saving is real (the definition is smaller) and
the cost is real (the proof is no longer pointwise); price both when
the tag goes.*

**The remaining four, with what each needs:**

* `quotLift` — six binders; mechanical but long, wants `quotLiftR_mem`
  plus the invariance premise unpacked by `quotInv_of_mem2`;
* `quotInd`, `quotSound`, `propext` — the `pt`-valued propositions (the
  flagged hard tail): each needs its proposition shown **inhabited**,
  not merely typed, so the `piR 0` truth-value form replaces v1's
  `pt_mem_piC_iff` chains.

No STOP: every one of the five has a supplier in hand, and the two
shapes needed (`psigmaMk`'s root-level split, the tail's inhabitation
chains) are both writable against `piR_zero` as it stands.  The
capstone `bval2_mem_type` itself waits on all eighteen, so the `const`
row stays deferred until they land.

### Step 2 entry item 2 COMPLETE — and the skeleton stands at ten of ten

The five that resisted are in, `bval2_mem_type` closes over all
eighteen, and `Skeleton.sound_const` — deferred at its own seal for
want of a supplier, not a proof — is now two facts wide.  **Deliverable
(2) covers ten `AVExpr` formers of ten.**

**`psigmaMk`, by the root split the finding predicted.**  Exactly as
mapped: `by_cases` on `Nat.max u v = 0`; the positive branch is v1's
four pointwise `lamR_mem`s with `spair_mem`; the zero branch rewrites
the tower to `pt` and exhibits *inhabitation* down four levels.  That
needed one general lemma the collapse lane had and this one did not —
`pt_mem_piR_zero` (`Interp2/Ops.lean`): at `v = 0` the product is a
truth value, so membership of the canonical proof needs only that each
fibre is **inhabited**, strictly weaker than `lamR_mem`'s pointwise
`F x ∈ˢ B x`.  Its pointwise wrapper `pt_mem_piR_zero_of` is the
line-for-line stand-in for the collapse lane's `pt_mem_piC_iff.mpr`.

*The finding's rule, now paid for: dropping a value-level regime tag
moves the kind-`0` argument from leaf to root.  The missing lemma was
the shape of the move — `lamR_mem` is a **witness** law, and what the
root needs is an **inhabitation** law.  When a tag goes, check that the
weaker law exists before assuming the proof transposes.*

**The other four went as sized.**  `quotLift`: five `lamR_mem`s and
`quotLiftR_mem`, whose kind-`0` fibre premise comes from the third
binder (`B ∈ˢ univ v`, and `univ 0 = univZero`) — nothing new.  The
`pt`-valued propositions (`quotInd`, `quotSound`, `propext`) ported
line for line off v1 once `pt_mem_piR_zero_of` existed, which is the
whole content of "the inhabitation tail": the arguments were never the
difficulty, the missing introduction law was.

**Two frictions banked for the next porter.**  A `have` with an
explicit type ascription written in `lv us 0` will not `rw` against a
goal carrying `us.getD 0 0` — drop the ascription and let it infer.
And `quotInd`'s minor-premise fibre condition must be rewritten through
`quotMkV2_app` *before* `app_mem_piR_pos` fires, because the invariant
states the fibre at the constructor's **value** while the motive
membership is about its `quotClass` **reduct**.

**The `const` row consumes nothing from the interface** — a built-in is
a closed leaf, so no context, no valuation, no hereditary premise.
That is why it could be written last and still cost one line, and it is
a small confirmation that the interface's shape was right: the row that
needed the most *machinery* needed the least *interface*.

## Migration step 3 — the map, before any statement

Opening step 3 with the map the brief asked for: what the consistency
surface's re-proof over `interp2` actually consumes, sized against what
exists.  **The map's headline is a correction**, and it is the reason
the map was worth doing first.

### The correction: step 3 is not a re-proof of the forty-four

The roadmap line reads "the soundness tier: the graded step lemmas
assembled along the bridge claims; the twelve re-proved over
`interp2`", and it is easy to read the second clause as "restate
`Sound/*` with `interp → interp2`".  **That is not possible, and not
because it is hard.**

`Sound/Motives.lean`'s five motives quantify `VExpr`:

    RedS (Δ : List VExpr) (v w : VExpr) : Prop :=
      ∀ ρ, Sat V Δ ρ → interp V ρ v = interp V ρ w ∧ (AnnotOkV … v → …)

while `interp2 : (Nat → V) → AVExpr → V` is over the *annotated*
syntax, and the relations (`Rel.lean`) are over `VExpr` too — so the
mutual recursor's motives must be.  Bridging would need a
`VExpr → AVExpr` map, and **there is none, by design**: `Annotates` is
a *relation* (`List VExpr → VExpr → AVExpr → Prop`) whose whole
difficulty was that a term has many annotations (WALL 3), and `denote2`
is a *function* but from `Expr`, not `VExpr`.  A bare `VExpr` has no
canonical annotation, and manufacturing one is exactly the problem R1
solved by refusing to.

The architecture record already says this in its own words — "the
second soundness does **not** re-sign the 44-case mutual induction
wholesale… the bridge-level claims maintain 'the current term erases an
annotated term carrying `AnnotOk2`' along runs and compose the step
lemmas — annotations never cross a bare `Red`, they follow the run."
The map's contribution is to show that this is *forced*, not preferred,
and to price what follows from it.

### What follows: `Sound/*` is not migrated at all

**The 4,295 lines of `Sound/*` stay where they are, serving the
collapse lane, until that lane retires.**  Step 3 builds a *parallel*
run-level structure rather than a translation of this one.  The
sizing this produces is the good news of the map:

| tier | lines | step 3's demand |
|---|---|---|
| `Bridge/*` | 9,525 | **none** — `EnvR`-only, "no `SetTheory`, no membership, no interpretation"; `CheckStepR` is discharged (`checkStepR`, `Bridge/Main.lean:35`) and stays discharged |
| `Sound/*` | 4,295 | **none** — not translated; see above |
| `Install/*` | 18,749 | **the work**: the five keys `declStepS` takes, re-proved over `interp2` |
| `Interp2/*` + `Annot/*` | ~5,900 | the substrate, largely built (steps 1–2 landed `EnvS2`, `denote2`, `AnnotOk2`, the skeleton, `BConst.type2`, `bval2_mem_type`) |

### The spine, traced

`checkDecls_sound_R` → `foldlM_R` → two things per declaration:
`checkDeclR_sound` (the bridge half) and `declStepS` (the install
half).  **The model enters at exactly two points**, and neither is in
the bridge:

* `declIndRS`'s `MemberKeyS` — the first statement in the spine that
  mentions `interp` at all;
* `declStepS`'s five keys — `DivModPinS`, `ReducePinS`,
  `StdAxiomKeyS`, `DeclBasisS`, `DeclIndS` — every one `EnvS`-attached
  and all but two mentioning `interp` directly.

So "the twelve re-proved over `interp2`" reduces to: **re-prove the
five keys and `MemberKeyS` over `interp2`, and restate the fourteen's
conclusion from `Nonempty (EnvS V env')` to `Nonempty (EnvS2 V env')`.**
Everything else in the spine is either V-free or already migrated.

`Sound/*` is the *install tier's* supplier, not the fourteen's — the
keys consume `Infer.sound`/`DefEq.sound`, the fourteen do not.  That is
why replacing what the keys consume (with `Claims2`) is the whole job,
and why the 44 minors never appear in it.

### What `Claims2` must be

The run-level analogue of `Bridge/Claims.lean`'s four claims, over
`denote2` outputs rather than `denote` outputs, composed from the
**per-former skeleton rows** (`Interp2/Skeleton.lean`, ten of ten as of
arc step 4) plus the graded step lemmas (`AnnotOk2_beta_pos`,
`AnnotOk2_zeta`, `AnnotOk2_redex_fits`).  Its inputs, named:

| input | source | status |
|---|---|---|
| the ten former rows | `Interp2/Skeleton.lean` | landed |
| β / ζ / redex-fits step lemmas | `Annot/Ok2.lean`, `Annot/Spine2.lean` | landed |
| the basis capstone | `Interp2/BasisOk.lean` | landed |
| `denote2` + erasure law | `Annot/Canon.lean` | landed |
| `EnvS2` fields | `Annot/EnvS2.lean` | landed (containment scaffolding) |
| **`denote2` fuel-invariance** | `knotFuelMono`/`KnotFuelDet_of_mono` | supplier landed, **lemma not stated** |
| **`SortSubstStable`** (v3) | `Annot/SimSubst.lean` | frozen; `Claims2` is its consumer |
| **`ZipWhnfSortAgree` / `ZipSortOfAgree`** | `SortCoh/Discharge.lean` | frozen — the two obligations the Θ lane discharges |
| **`RecRulesV2`** | — | **no definition anywhere**; deliberately absent under the T5 rule |

### The one gap that feeds back into Θ, stated now

`RecRulesV2` is the only input with **no supplier and no statement**.
It is deliberate — "stated by its supplier when the bottoms migrate" —
but it is also unavoidable: `declStepS` installs inductives, so the
spine passes through iota, so `Claims2`'s iota row needs the fired law.
`Claims2` must therefore carry it as an **opaque named slot**, exactly
as `Skeleton.sound_const` carried its absence before `BConst.type2` and
`bval2_mem_type` existed.

*What this means for Θ, while its consumers are still adjustable:*
nothing Θ produces can discharge `RecRulesV2` — it is install-tier
content, not coherence content — but Θ's two frozen zip obligations
**are** `Claims2` inputs, and `Claims2` should name those two rather
than the fifteen-hypothesis shells (`ensureSortAgreeRQ_of_zip` /
`sortOfAgreeRQ_of_zip` already reduce both public claims to one
obligation each).  That is the ledger entry from the consumer side.

### A terminology correction for the record

The migration sections say "the twelve"; the T6/T7 sections and
`Main.lean`'s own docstring say "the fourteen".  `Main.lean` has
fourteen non-fold theorems; "twelve" undercounts by excluding
`checkDecl_sound_R` and `no_constant_of_Empty_R` — the two that are not
in the 4×3 driver grid.  **Fourteen is right**; the roadmap's "twelve"
should be read as "the twelve driver-grid ones".

### Row invariants, the Raw currency, and the resolution kit sealed

Amendments from the `runCore` pre-build, all compiled warning-free:
the rows carry their cores' `SubjInv` (E1's inputs at the inner
depth); `TelescopeRel.cons`'s domain fact is Θ-typed (the zipped-λ
push's tys are zips, not certs; the loop-tier annotation-reads will
consume the rel form); `ThetaCoreOut`'s rebase disjunct carries
`RawReach` (the E-currency — the aligned points live on the raw
image traces, not the gated `Contracts` paths); `ofZip` takes the
`SubjInv` pair; `of_ok` deleted (the consumers' telescopes are
empty — `.nil` suffices at every entry point).  New kit:
`thetaSubst₁/₂_fvar_below` (θ-invariance below the zone),
`thetaSubst₁/₂_fvar_inzone` (in-zone resolution to the entry's
argument under the PREFIX telescope), `thetaSubst₁/₂_concat` +
`TelescopeRel.concat` (telescope composition — the in-zone
re-expression's spine), and `RawReach.mkAppN_left` (head-congruence
spine lift).  Battery green, axioms 12/12.

### The discharge's mechanization strategy: the composition-generalized motive

The last hard nut, cracked at pre-build: the in-zone `fvar` chase
(head resolves to an entry's argument pair, whose own rel may again
be in-zone-headed) is well-founded on the REL-DERIVATION structure
— entries reference strictly OUTER entries — but naive re-entry
rebuilds the rel (concat-composed), losing structural descent, and
Prop-inductives carry no size.  The resolution needs NO new indices:

**Induct structurally on the mutual `ThetaRel`/`TelescopeRel`
derivation with a composition-generalized motive** —
`M(d, u, v) := ∀ (d₀, Γout) with d₀ + |Γout| = d, ∀ extra spines
and runs on the further-imaged pair (θ-imaging composes by
`thetaSubst_concat`), the core out holds` — so the in-zone case
applies the ENTRY's hz-IH at the composed outer telescope (a
structural sub-derivation through the mutual induction's per-field
IHs), while all spine/β/continuation recursion routes through the
outer strong induction on the runs' knot sum (the spine-peel's
descent).  Measure: [N strong, rel-derivation structural] — no
weights, no fuel, no Type-valued reification.

Remaining discharge inventory (fully de-risked, mechanization
volume only): the three row-analyses under the motive (head-shape
cases × the PostCoreCert arms at `runCore`, with the landed
suppliers: the θ computation kit, the push algebra, E1–E4, the
in-zone resolution, `whnfCore_nonrec_id`/dead machinery), then the
loop tier (pre-build owed for the seam-to-sort conversions), the
sort-agreement tie, and the four depth-zero consumers (junction
note: the two frozen zip obligations flag prominently for the other
lane's Claims2 when those land).

### Step 3, seal 1 — `Claims2` stated (`Interp2/Claims2.lean`)

The four run-level claims in the annotated currency, the mutual fuel
induction `checkSound2` with its `zero` case closed, and the discharge's
named inputs as a bundle.  Hypothesis-first, `CheckStepR`'s precedent
throughout: `CheckStep2` is a bare `Prop` and `checkSound2` takes it.

**Two simplifications the annotated currency buys**, both worth having
on the record because they make the claims *smaller* than v1's:

* **the `∃ T'` slack disappears.**  `InferClaimsR` must conclude "some
  `T'` with `Infer … T'` and `DefEq … T' tv`", because an on-the-nose
  inference claim cannot serve a binder congruence (design §0
  decision 1).  `InferClaims2`'s conclusion is *semantic* — a
  membership — and `DefEq` slack is absorbed by `DefEqClaims2`'s own
  equality, so it concludes directly at the inferred type's
  annotation.  The slack was a *relational* artefact and does not
  survive the move to interpretations;
* **the context correspondence is reused, not re-invented.**  The
  hypothesis side stays `CtxOkR` at the **erasures**
  (`Δa.map AVExpr.erase`) — a *function* of the annotated context, so
  no new relation and no appeal to `Annotates`, whose
  many-annotations problem is exactly what R1 removed.  Inventing a
  `CtxOkR2` was the obvious move and would have been the wrong one.

**The ledgered `EnvS` seam is closed, and by scaffolding that was
already there.**  `SortSubstStable` takes `mS : EnvS V env` — the
collapse-lane invariant — which the consumer seal flagged as needing
re-signing to the `EnvS2` world.  It does not: `EnvS2` holds an `EnvS`
in its `base` field by containment, so `m.base` supplies it verbatim.
*A seam noticed early was retired by a decision taken earlier still.*

**`Step2Inputs` makes the supplier ledger mechanical.**  Rather than
prose, the inputs a `CheckStep2` discharge will consume are a
structure, and the three *kinds* are the point:

* `subst_stable` — frozen, and `Claims2` is its named consumer;
* `zip_whnf` / `zip_sortOf` — **the two zip obligations themselves**,
  not the fifteen-hypothesis shells: `ensureSortAgreeRQ_of_zip` and
  `sortOfAgreeRQ_of_zip` already reduce both public claims to one
  obligation each, so naming the shells would over-state what the
  consumer needs.  This is the Θ-junction entry from the consumer
  side;
* `infer_fuel_det` — scheduled, supplier landed (`knotFuelMono`);
* `rec_rules2` — **an opaque `Prop` parameter**.  `declStepS` installs
  inductives, so the spine passes through iota, so the discharge needs
  the fired modeled-iota law over `interp2`; by the T5 rule that
  premise belongs to the iota bottoms when they migrate, and writing it
  consumer-side is the near-miss this campaign has ruled against.  The
  `Skeleton.sound_const` precedent exactly — carry the absence, name
  it, and let the supplier state it.

*Rule worth keeping from the shape of this bundle: **a named slot and a
frozen hypothesis are different things and should not be spelled the
same way.**  A frozen hypothesis has a statement someone else will
prove; a named slot has no statement yet, and writing one would bind
the supplier to the consumer's guess.  Making the first a field of a
known `Prop` and the second an opaque parameter keeps the difference
visible at the use site.*

Next: `CheckStep2`'s discharge, clause by clause, and the five install
keys over `interp2` in dependency order.

### Step 3, seal 2 — `CheckStep2`'s clause map, and the lemma that unblocks 2,227 lines

Mapping `CheckStep2`'s discharge clause by clause against the landed
skeleton rows, before writing any case.  **Nine of the eleven inference
clauses have their supplier; two did not, and the reason turned out to
be a single missing lemma.**

| checker clause | supplier | status |
|---|---|---|
| `.sort u` | `sound_sort` | landed |
| `.fvar` | `sound_bvar` (+ the `CtxOkR` leaf → `Sat2` bridge) | landed |
| `.const n us` (stored) | `EnvS2.acval_ok2`, `mem_type2` | landed |
| `.forallE` | `sound_pi` | landed |
| `.lam` | `sound_lam` | landed |
| `.app` | `sound_app` | landed |
| `.proj` | `sound_proj_fst`/`_snd` | landed |
| `.letE` | `sound_letE` | landed |
| `.lit natVal` | the `Nat`-literal block over `interp2` | **was blocked** |
| `.lit strVal` | the `String`-literal block over `interp2` | **was blocked** |
| (`whnfCore`/`defeq` rows) β, ζ | `AnnotOk2_beta_pos`/`_zero`, `AnnotOk2_zeta` | landed |
| iota | — | **the named slot** (`Step2Inputs.rec_rules2`) |

**The literal clauses were blocked on one lemma, and it is now
supplied.**  The step-3 map recorded that `Sound/{Lit,NatOps,
NatOpsWf}.lean` — **2,227 lines, 47% of the Sound tier** — touch the
interpretation through only five lemmas: `interp_app`, `interp_bvar`,
`interp_sort`, `interp_pi` and `interp_closed`.  Four had `interp2`
analogues.  The fifth did not, and neither did its engine
`interp_congr_below`.

`Interp2/Kit.lean` now carries both.  One decision worth recording:
they are stated through the **erasure's** bound
(`VExpr.bvarsBelow k e.erase`) rather than a fresh
`AVExpr.bvarsBelow`.  `AVExpr` has no closedness predicate at all, and
adding one would have meant touching `Annot/Syntax.lean`, a shared
landed file — but `erase` maps `bvar i` to `bvar i` and preserves every
former's shape, so the erasure's bound *is* the annotated term's bound.
**No new predicate, no shared-file edit, and the lemma is exactly as
strong.**

*Rule, and it is P4's converse in miniature: before adding a predicate
to a shared syntax, check whether an existing one already says the same
thing through a structure-preserving map.  `erase` was right there.*

So the sizing changes: the literal block goes from "blocked" to
"near-mechanically portable", which is the difference between 2,227
lines of new argument and 2,227 lines of transposition.  **One
sixty-line lemma was the whole obstruction.**

**What remains genuinely open on `CheckStep2`.**  The clause map's own
verdict: the inference and reduction rows are supplier-complete except
iota, which is the named slot by the T5 rule and stays that way until
the bottoms migrate.  The discharge itself is a fresh induction over
the *runs* — it cannot ride the v1 bridge, because that bridge produces
relation derivations about **erasures** while `Claims2` needs `interp2`
facts about **annotations**, and no map carries one to the other (the
step-3 map's headline, in its local form).  So the discharge is
`Bridge/*`-shaped work, and the honest estimate is that it is the
largest single remaining item on the lane — larger than everything
steps 1–2 contained.  Sized, not started; every clause now knows what
it consumes.

### Species suppliers, batch 1 (`Species.lean`)

Discharged from the landed Verify batteries (`EnvWF`-parametric,
warning-free): `leavesSubCoreF_of`, `invPreserve{Core,Delta,Nat}F_of`,
`pairedPreserve{Core,Delta,Nat}F_of`, `invPreserveProjFireF_of`,
`pairedPreserveProjFireF_of`, `storedWF_of` — riding
`SubjInv.step`/`PairedLeaves.sub_left`/`LeavesBounded.sub`
(leaf-subset monotonicity) plus the scoped/bounded preservation
family; the projection fire's facts-free leaf chain
(`projFire_field_leaves`) threads the conversion rows without
scrutinee facts.  `knotFuelMono` and `natStepNoSort_of` were already
landed.  Remaining named leaves on the two-obligation path: the
`Q`-family (discharges at the consumer's concrete `Q`),
`BoolCtorsInert` (install fact), `TypeTransport{Core,Delta,Nat}F`
(the checker's infer-subject-reduction — its own tier), the Θ docket.

### Refinement three: the Θ relation as DATA (`ThetaRelD` triple)

The composition-generalized motive hit positivity: the analysis
motive needs the outer telescope's per-entry analyses as a premise,
which self-references the motive (negative occurrence — no
inductive pack can carry it), and every Nat-measure attempt
re-inflates at the in-zone reset (round three's lesson, now at the
mechanization tier).  The one certain resolution: the relation
becomes Type-valued data — the mutual triple
`ThetaRelD`/`ThetaRelsD`/`TelescopeRelD` (spines as the list
inductive so `sizeOf` counts them), with the Prop wrappers
`ThetaRel`/`TelescopeRel` (`Nonempty`) keeping every statement
unchanged.  The discharge recurses well-foundedly on
`(N, sizeOf rel-bundle, L, row-weight)`: the in-zone chase descends
to the looked-up entry's SUB-TERM; pushes and peels descend the
knot sum; the run's δ/nat arms descend `L`; the syn hop descends
the manual row-weight (run > same).  Kit ported to the data forms
(`TelescopeRelD.append/concat`, the bounded/WScoped/lam-beta
family); `ThetaRelsD.length_eq/get` bridge to the Prop shapes.
Battery green, axioms 12/12.

## #151 junction feedback holding pen (fold into consumer-tier pre-builds)

From the consumer lane's Claims2 refutation work (2026-08-30), two
statement-level findings that MUST enter the pre-build checks of the
affected seals before their statements freeze:

1. **SortSubstStable needs a sortOfE twin.**  SortSubstStable is
   stated for `lamSortE`, but denote2's pi clause needs the same
   substitution-stability for `sortOfE`, which has no statement
   anywhere in the tree.  When the leaf-wiring/consumer work reaches
   SortSubstStable, state the sortOfE twin alongside — same proof
   skeleton at the other entry point is the expectation, but verify,
   don't assume.
2. **.lam granularity/mode mismatch.**  denote2 calls `lamSortE` per
   λ NODE; `inferBody` runs it once per CHAIN and only at
   `mode.verified` (never at noModel).  The consumer lane repairs its
   side with a mode quantifier.  GATE: check the depth-zero
   sort-agreement consumers' statements (ZipCertSpineCase tie,
   ProjSplitSortAgree, IotaMajorSortAgree, EtaRescueSortAgree, and
   the ZipWhnfSortAgree/ZipSortOfAgree assembly) for per-node facts
   sourced from per-chain checker runs; if any, the same granularity
   gap applies.

## #151 refinement four: liftCore + Based (the push-entry depth repair)

FINDING (2026-08-30, layer pre-build): the banked push recipe ("entry
hz := sp-rel[0]") glossed a depth mismatch — `TelescopeRelD.append`'s
entry slot at position |Γc| demands a relation at depth d+|Γc|, but
push arguments (outer-spine elements) carry relations at the BASE
depth d.  Depth-weakening of ThetaRelD is NOT subject-preserving
(θ-substitution levels move with the index), so no weakenD exists.

REPAIR (additive, measure re-verified):
* New row `ThetaRelD.liftCore {d₀ d} (hle : d₀ ≤ d) (rel at d₀)
  (scope + bvar facts on the endpoints) (hsp : spine at d)` with
  subject `mkAppN u sp` — a base-scoped core presented at a deeper
  slot.  Push entries (hz and the ty-slot hd) wrap base relations.
* `wt (liftCore) = 1 + wt rel + wt hsp`; the analyzer's wrapper arm
  re-enters at prefix `Γo.take (d₀ − d)` (empty in the standard
  d₀ = base case), strict wt drop via the wrapper node.
* The wrapper arm needs d₀ ≥ the frame base; sub-base wrappers are
  unreachable in the real pipeline but not excluded by the type —
  hence the `Based β` invariant trio (mutual Prop over the data:
  rows recurse, wrapper clause adds β ≤ d₀), threaded as premises
  through ThetaIH/analyzers and carried by ThetaCoreOut's rel
  branch (`BasedRel`) and the seam rows' relation slots.
  Preservation battery: castD/castE, takeD/lookup, concat, appendR,
  underTele/imageRels, extendSp, append, ofZip.
* `underTele` stays Based-free: its wrapper arm splits on d₀ ≤ d
  (direct re-wrap) vs d < d₀ (recurse under the take-(d₀−d) prefix);
  needs thetaSubstᵢ_take_of_scoped (suffix-idle images, via _concat
  + _scoped_id).
* rowW/rowL deleted (CPS architecture made the delegation-hop
  measure obsolete; W/L live as per-theorem constants now).

Also banked this stretch: mutual-WF theorems over the data trio are
NON-VIABLE for the discharge (decreasing goals replay tactic-cases
contexts with non-defeq inaccessible copies of case fields; probe5
evidence) — the CPS-IH architecture (single WF thetaAnalyze,
match-style; plain content analyzers taking ThetaIH; ThetaIH.shrink
makes any sub-budget re-entry an N-drop) is the ratified replacement
and compiles end-to-end.  Data-valued `have` is defeq-opaque: inline
data terms at omega/defeq-sensitive sites (three incidents).
## The `CheckStep2` discharge — the induction's map (campaign seal 0)

### The measure, taken from the checker rather than invented

Two nested layers, and the discipline is one sentence:
**depth-increasing recursion goes through the IH at `fuel`;
depth-preserving iteration goes through the continuation at `budget`.**

* Every body takes `(r : CoreFns m)` and **never calls itself**.  A sub-
  result through `r` runs at `fuel - 1`, so a clause at `fuel + 1`
  reaches it by *applying an IH* — no sub-induction.
* `whnf` and `isDefEqCore` are loops on a **separate private budget**
  (`whnfLoopFuel = defeqLoopFuel = 100000`, `@[irreducible]`), taken
  through an abstracted continuation `k`.  Delta chains and literal
  acceleration are *iteration*, not knot recursion (task #106).  Each
  loop gets one `induction budget`, with `k`'s contract named as a
  `Prop` — the checker's own continuation-passing factoring, mirrored.

### Case structure, against the actual decompositions

| body | cases | notes |
|---|---|---|
| `inferBody` | **11** — sort, fvar, const, lit nat, lit str, forallE, lam, app, proj, letE, bvar | `.bvar` throws; dispatch is on `ExprView` |
| `whnfCoreBody` | **9** — 6 leaves, `.app` (β / ι / stuck), `.proj` (1 reducing, **5 stuck exits**), `.letE` (ζ), `.bvar` | no delta at this level |
| `whnfStep` | **3 exits** — literal, delta, fixpoint | order: whnfCore → reduceNat → delta |
| `defeqStep` | **7 blocks**; block 7 (structural congruence) has **17 cases**, and its fallthrough `stuckIrrel` has **6 arms** | `defeqSpine` is the same-head short-circuit inside the lazy-delta block; a `false` there is never final |

**Mode gating is nearly free.**  Exactly five gated sites in
`Core.lean`.  Four are `ttChecks`, which is **constantly `false`** since
T7b — so those `.proj`/eta sites discharge by the ungated path.  Only
`inferBody`'s λ-codomain check (`Core.lean:1615`, `mode.verified &&
!body.isLam`) is genuinely two-valued and needs a case split; it fires
**once per λ chain, at the innermost binder**.

### Per-clause consumption, and the priority order

**Tier A — consumes only LANDED suppliers (no Θ dependency).**  Start
here, per the economy directive.

| clause | consumes |
|---|---|
| infer `.sort` / `.fvar` / `.letE` | `sound_sort` / `sound_bvar` / `sound_letE` |
| infer `.const` | `EnvS2.acval_ok2`, `mem_type2` |
| infer `.forallE` / `.lam` / `.app` / `.proj` | `sound_pi` / `sound_lam` / `sound_app` / `sound_proj_*` |
| whnfCore leaves, `.letE` (ζ) | `denote2` clause equations, `AnnotOk2_zeta` |
| whnfCore `.app` β | `AnnotOk2_beta_pos` / `_beta_zero` |
| whnfCore `.proj` | `sound_proj_*`, the five stuck exits are identity |
| whnf loop, delta step | the reduct denotes **identically** — no new fact |
| defeq structural congruences | `interp2` clause equations + the IHs |

**Tier B — the literal block.**  infer `.lit natVal` / `.lit strVal`,
`reduceNat`'s two arms, and the `.lit` congruence cases.  Unblocked by
`interp2_closed` (seal 2); a **transposition batch** of
`Sound/{Lit,NatOps,NatOpsWf}`'s 2,227 lines, not new argument.

**Tier C — conditional by design.**
* **iota** (`whnfCore`'s `.app` ι sub-case, and the rescues) — enters
  through `Step2Inputs.rec_rules2`, the **named slot**.  This is the
  one seam where the T5 rule binds: the fired law is stated by the
  migrating bottoms, never here.
* **β's sort premise** — `SortSubstStable`, whose own suppliers are
  Θ's two zip obligations.  Carried as `Step2Inputs.subst_stable`;
  the clause is written conditional and closes when Θ lands.

### The shape to follow (v1's, which works)

1. four claims + step `Prop` + fuel induction — **landed**
   (`Claims2.lean`);
2. frame packages once, `whnfCore_packageR`-style (IH output + frame in
   one `obtain`);
3. per quarter, **one dispatch lemma matching the checker's own case
   split**, with every non-local clause a named `…Step2 : Prop` stated
   **at a checker function boundary**, never mid-body;
4. loops get `induction budget` with the continuation's contract named;
5. discharge bottom-up along a **linear import chain**, one obligation
   per file, so the assembler is a dozen-line `exact`.

### Sizing, honestly

v1's `CheckStepR` tier is **5,964 lines**: ~77% per-clause case work,
~8% frame plumbing, ~15% assembly — and very unevenly spread (`Stuck`
520, `Iota` 550, `ReduceNat` 483 are 26% between them).  The interp2
analogue should come in **somewhat under** that: it produces semantic
facts rather than relation derivations (no `Red`/`Infer` construction
plumbing), and the ten per-former rows are already landed.  Estimate
**3,500–5,000 lines across 8–12 seals**.  Tier A is the majority of it
and depends on nothing outstanding.

### Discharge campaign, seal 1 — the four quarters' Tier A clauses

`Interp2/Step2/{Infer,WhnfCore,DefEq,Loop}.lean`: the per-clause lemmas
each dispatch will consume, for every Tier A branch.  All compile; the
battery is unchanged; 305 jobs warning-free.

**Infer** — the leaves (`.sort`, `.fvar`) discharge from `denote2`'s
own clause equations plus the matching skeleton row, with no IH at all;
the structural clauses (`.forallE`, `.lam`, `.app`, `.letE`, `.proj`)
are stated over the rows' *inputs* rather than over `inferBody`'s
spelling, so the dispatch owns the run and the clauses stay independent
of it.

**WhnfCore** — two shapes cover eight of nine cases.  `whnfStep2_id`
is the identity shape and serves **eleven** branches (six leaves, five
stuck `.proj` exits); ζ and both β kinds are the graded step lemmas,
which conclude the claim's two conjuncts exactly.  ι is Tier C.

**DefEq** — the equivalence and the congruences, all pure
interpretation algebra, plus proof irrelevance and η.  `symm`/`trans`
are one-liners precisely because `DefEqClaims2` is unconditional in
truthfulness, the grading inherited from `DeqS`.

**The delta exit turned out to need an environment field, and it is
added.**  `EnvS2` gains `acval_defn` and `acval_thm` — the `denote2`
successors of `EnvS.defn_eq`/`thm_ok`.  v1 records the same fact as
"the reduct denotes *identically*"; here it must be a field rather than
a lemma, because `denote2` reads `acval` where `denote` read `cval`.
With it the loop's delta exit is free: the unfolded body's canonical
annotation **is** the constant's own leaf, so the step moves neither
the interpretation nor the invariant.  `EnvS2.empty` re-discharged
(vacuous over `env.consts = []`).

**FINDING — a named contract that proves by `rfl` is not a contract.**
The map instructed naming the loop's continuation contract at the
function boundary, following v1.  Written out it was
`interp2 ρ ea = interp2 ρ ea ∧ (AnnotOk2 ρ ea → AnnotOk2 ρ ea)` —
`⟨rfl, id⟩`, i.e. nothing.  **Deleted before landing.**

The instruction was right for v1 and wrong here, and the difference is
instructive: v1's loop must *construct a `Red` derivation*, so its
continuation genuinely owes something at each budget step.
`WhnfClaims2` concludes an **equality and a transport**, and the loop
moves the subject without moving either — every budget step is the
identity on the claim.  The content is entirely in the three exits'
step facts; the budget recursion is bookkeeping and belongs inside the
dispatch.

*Rule: when transposing a proof architecture, check whether the thing
the original carried still has content in the new currency before
giving it a name.  A vacuous `Prop` with a good name is worse than no
`Prop`, because it looks discharged.*

**Ledgered from the map, as directed**: four of the five mode-gated
sites in `Core.lean` are `ttChecks`, **constantly `false` since T7b**,
so the `.proj`/eta gates discharge by the ungated path and cost the
campaign nothing.  Only `inferBody`'s λ-codomain check
(`Core.lean:1615`, `mode.verified && !body.isLam`) is genuinely
two-valued, and it fires once per λ chain at the innermost binder.

### Discharge campaign, seal 2 — the dispatch keystone validated, Tier B piloted

Two claims from the campaign map tested against reality; both hold.

**The dispatch transfers verbatim.**  `infer_sort_claim2`
(`Interp2/Step2/Dispatch.lean`) is v1's `infer_sort_claimR` with the
conclusion swapped to the annotated currency, and **the unfolding
recipe is unchanged** — `rw [inferTypeCore_succ]` then
`simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
Except.bind, Except.ok.injEq]`.  It compiled first try.

That is the campaign's keystone risk retired: the *checker* is the same
function on both lanes, so the case-splitting machinery — which is
where a bridge's bulk and its fiddliness live — is shared.  Only what a
clause produces afterwards differs, and that is exactly the part the
skeleton rows already supply.  **The remaining ten `inferBody` clauses,
and the other three quarters' dispatches, are grind against a validated
template rather than an open problem.**

**Tier B is transposition, as priced.**  `natLit_facts2`
(`Interp2/Step2/Lit.lean`) is `Sound/Lit.lean`'s `natLit_facts` onto
`piR`/`AnnotOk2`/`interp2` and `denote2`'s own numeral spine
(`natLitT2` — the same former the `.lit natVal` clause emits).  It
compiled first try and came out **shorter than v1**: `Nat → Nat` sits
at result sort `1`, so the successor's product is in the graph regime,
`app_mem_piR_pos` applies with no fibre premise, and the app slot's
kind-`0` component is vacuous.  v1 needed `app_mem_piC` and the
collapse's side conditions at the same spot.

One structuring choice worth copying through the batch: the numeral
induction takes the two head facts as **explicit arguments** rather
than re-deriving them, because they are one `mem_type2` chain shared by
every numeral.  v1 factors the same way (`natHeads_facts` out of
`natLit_facts`), and the factoring is what keeps the induction free of
the literal guards' inversion plumbing.

**State of the campaign.**  Landed: the map, the four quarters' Tier A
clause lemmas, `EnvS2`'s two delta fields, the Tier B pilot, the
dispatch keystone.  Remaining and now fully templated: the other ten
infer clauses, the three other dispatches, the rest of Tier B
(`strLit_facts` is its bulk at ~394 v1 lines), then the five install
keys and the fourteen's conclusion swap.  Tier C (iota via the named
slot, β's sort premise via `SortSubstStable`) stays conditional by
design.

### Discharge campaign, seal 3 — STOP: the `.fvar` clause refutes `Claims2`'s hypothesis side

Running the infer clauses against the validated template, the second
one stopped the batch.

**What broke.**  `Claims2` was sealed with the context correspondence
*reused rather than re-invented*: `CtxOkR` at the **erasures**
(`Δa.map AVExpr.erase`), on the reasoning that it is a function of the
annotated context and so needs no new relation.  That reasoning was
checked against the *conclusion* side, which never wants more.  The
`.fvar` clause reads the context, and wants two things `CtxOkR` states
only relationally:

1. **definedness** — that the leaf's annotation has a `denote2` at all.
   `CtxOkR`'s leaf package gives `denote cval env φ d ty = some T`; the
   annotated denotation is a *different function* and its definedness
   does not follow;
2. **the leaf-to-entry link** — the claim needs
   `ρ k ∈ˢ interp2 ρ tya`, while `Sat2` offers
   `ρ k ∈ˢ interp2 (fun j => ρ (j+k+1)) Aa`.  `CtxOkR` bridges the
   corresponding v1 gap with `∃ T', Infer … ∧ DefEq … T' T` — a
   **relational** package — and turning that `DefEq` into an `interp2`
   equality is exactly the move the step-3 map proved does not exist.

So the erasure route is sound for the conclusion and insufficient for
the hypothesis, and the difference surfaces at **one clause out of
eleven** — the only one that reads the context rather than passing it
along.

*Rule: a hypothesis reused from another currency is only as good as the
weakest clause that reads it.  Check the clause that reads the context,
not the ones that merely thread it.*

**Landed anyway, so the stop costs nothing.**  `infer_fvar_claim2`
takes both facts explicitly and compiles, so it is usable the moment a
supplier exists; `infer_bvar_claim2` (the throw) is closed outright.

**The repair, stated and checked but deliberately NOT wired.**
`CtxOk2` is `CtxOkR`'s leaf package transposed — per leaf, the
annotation denotes under `denote2`, and its interpretation agrees with
the context entry read in the entry's own tail context, the second
conjunct being the semantic fact directly where `CtxOkR` had the
relational one.  `CtxOk2.fvar_leaf` proves it supplies exactly what the
clause takes, so the repair is *checked rather than asserted*.

It is not wired in because substituting it for
`CtxOkR (Δa.map erase)` changes **`Claims2`'s sealed statement** in all
four claims — a junction decision, not a consumer's.  The change is one
edit and touches no other clause: the other ten pass the context along
without reading it.  Awaiting the ruling.

### Tier B, the `String` half — and where its head facts must come from

`charList_facts2`/`strLit_facts2`
(`Interp2/Step2/StrLit.lean`) transpose `Sound/Lit.lean`'s
`strLit_facts` — v1's ~394-line bulk — onto `piR`/`AnnotOk2`/`interp2`
and `denote2`'s own character-list spine (`charListT2`).  They
compiled first try, at **~55 proof lines**, and the pricing held
exactly as `natLit_facts2` predicted: `Char`, `List Char`, `String`
and `Nat` are all `Type`-level, so every product in the spine is in
the graph regime, `app_mem_piR_pos` applies with no fibre premise at
each of the four application sites, and all four `AnnotOk2` app slots'
kind-`0` components are vacuous.  v1 needed `TeleFitV.appN` /
`appN_annot` telescope walks with per-argument
`VExpr.inst_eq_self_of_closed` bookkeeping for the same four steps.

**The "five lemmas" claim, confirmed and sharpened.**  The block was
priced as touching the interpretation through `interp_app`,
`interp_bvar`, `interp_sort`, `interp_pi`, `interp_closed` only.  With
the heads as arguments the transposed core needs **just
`interp2_app`** — `bvar`/`sort`/`pi`/`closed` occur in v1 *only*
inside the head-fact derivations (`hnilOk`, `hconsOk`, `hAppDomOk`,
`hCharU`, `hListMem`), which are now the hypothesis boundary.  Nothing
else in the block was interpretation-sensitive.

**The finding: the head facts are not a `denote2` computation.**  In
v1 the heads come from `EnvS.mem_type` aimed at a `denote`-computed
type, and that computation is *determined* by `strLitSupported`'s
syntactic inversion because `denote`'s `forallE` clause is
numeral-free.  `denote2`'s `forallE` clause is not: it calls
`sortOfE` (= `inferTypeCore` then `whnf` then `Level.eval`) on the
stored domain and body.  `strLitSupported` pins the stored *type
shapes* and says nothing about what the checker's own inference
returns on them, so no annotated type `ta` can be exhibited from the
guard alone and `EnvS2.mem_type2` cannot be aimed.

So for the annotated lane the supplier of a stored constant's head
fact is **the annotation pass, not a `denote2` evaluation**:
`Annotates`/`HasSort` for the stored type, plus the numeral-agreement
laws (`piR_zero_agree`) to reconcile whatever numerals `sortOfE`
produced with the `1`s the membership statements use.  This is a
structural difference between the lanes, not a gap in this seal, and
it applies to *every* basis-constant head the tier-B block wants —
`natLit_facts2`'s two heads included, which is why both files take
them as arguments.  Whoever wires the literal clauses into the
dispatch pays it once, at the `acval`-side supplier, for all eight
heads at once.
### Discharge campaign, seal 5 — TWO STOPs, both quarters past them

`WhnfCoreStep2` and `WhnfStep2`, run against `Bridge/WhnfCore.lean`.
The case split transferred verbatim — it is the same checker — and the
sealed *statements* did not.

**STOP 1 (mechanically refuted): the annotation's fuel is tied to the
checker's.**  All four claims of `Claims2` read the subject's
annotation at `denote2 … fuel …`, the same numeral that indexes the
checker call.  The knot decrements that numeral and every reduction
clause recurses, so the step from `fuel` to `fuel + 1` must move a
`denote2` fact *down* to `fuel` before the induction hypothesis will
take it.  That move is `Denote2FuelDown` and it is **false**:
`denote2` is `denote` fused with the checker's own sort computation,
so no binder has an annotation until the fuel suffices to run
`inferTypeCore` and `whnf`.  `denote2_fuelDown_false` exhibits it at
the smallest witness — at fuel `1` the reduction loop cannot take its
first `whnfCore` step (`whnf_one_error`), so `sortOfE` is `none`
everywhere and no `∀`/`λ` annotates at all (`denote2_one_forallE`,
`denote2_one_lam`), while at fuel `2` the smallest closed `∀` does
(`denote2_two_forallE`).  Unconditional in mode, environment, level
assignment and annotated valuation.

The defect is in **all four claims**, not this quarter's two.  Seals
1–4 did not meet it because the clauses they landed
(`infer_sort_claim2`, `infer_fvar_claim2`, `infer_bvar_claim2`) are
exactly the three that do not recurse.

*The repair is a strengthening and one binder wide*: quantify the
annotation fuel **inside** the claim, independent of the checker's
(`WhnfCoreClaims2F` / `WhnfClaims2F`).  Every recursive use then
instantiates the induction hypothesis at the goal's own `F` and no
fuel moves.  `WhnfCoreClaims2F.toClaims2` checks the repaired claim
still implies the sealed one, so nothing downstream loses;
`whnfCore_letE_claim2F` is the checked evidence that repair 1 is the
whole of STOP 1 at a recursing clause.

**STOP 2: the `interp2` equality is stated ungraded.**  `Claims2`
concludes `interp2 ρ ea = interp2 ρ ea' ∧ (AnnotOk2 ρ ea → AnnotOk2 ρ
ea')` — the equality *outside* the premise.  The quarter's own Tier-A
suppliers do not have that shape: `AnnotOk2_zeta`,
`AnnotOk2_beta_pos` and `AnnotOk2_beta_zero` conclude
`eq ∧ AnnotOk2 ρ ea'` **from** `AnnotOk2 ρ ea`.  For ζ the difference
is harmless (`whnfStep2_zeta_eq` proves the ζ equality premise-free).
For β it is not: `interp2_beta_pos` needs `⟦a⟧ ∈ˢ ⟦A⟧` (off the domain
`app` is the canonical junk `∅`), which the clause's own certificate
supplies; but `interp2_beta_zero` needs the λ's whole fibre package,
i.e. `AnnotOk2` of the redex's head, and `whnfCoreBody` never infers
the head — it whnf's it.  So the kind-`0` β branch has no supplier for
the ungraded equality.  *The repair is a weakening, and it is the
shape the suppliers already have*: move the equality inside the
premise (`WhnfCoreClaims2R` / `WhnfClaims2R`).

**Both quarters are discharged past both STOPs.**  In the repaired
currency, `whnfCore_claims2R` closes all nine `whnfCoreBody` cases and
`whnf_claims2R` closes the loop by induction on `whnfLoopFuel` (never
on the knot's `fuel` — the map's discipline, and it held).  The
residues are named at the checker's own function boundaries and none
is this seal's to state: `IotaStep2` (the migrating iota bottoms',
per the T5 rule), `ProjStep2` and `ReduceNatStep2` (v1's `ProjStepR`
/ `ReduceNatStepR` transposed), `Denote2Inst1` (the `SortSubstStable`
lane's; v1's `denote_beta`), `Delta2` (an annotated `mkAppN`
inversion) and `BetaCert2` (the inference and defeq quarters, once
they are repaired too).  The six leaves and `.bvar` are closed at the
**sealed** shape, needing neither repair.

*Rule: when a claim fuses a checker-computed object into its
statement, the object's own fuel must be quantified separately from
the checker's — the knot decrements one and not the other.  And a
claim's conclusion should be read off the suppliers it names, not
written first and matched later.*

Awaiting the ruling on both repairs; neither is wired into
`Claims2.lean`, for the seal-3 reason.

### Discharge campaign, fold-in — `Claims2` is refuted twice, by two independent discharges

Three of four parallel quarters delivered.  Two of them, working from
different checker functions and never seeing each other's work,
**independently stated the same obligation, under the same name, and
one of them refuted it**.  That is the strongest evidence available
that the defect is in `Claims2` and not in a proof strategy.

**DEFECT 1 — the annotation's fuel is tied to the checker's.**  All
four claims read the subject through `denote2 … fuel …`, the same
numeral that indexes the checker call.  The knot decrements it, so a
recursing clause must move a `denote2` fact from `fuel + 1` down to
`fuel`.  `denote2_fuelDown_false` proves that move impossible —
unconditionally in mode, environment, level assignment and annotated
valuation.  The witness chain is of independent interest: at fuel `1`
the reduction loop cannot take its first `whnfCore` step, so `sortOfE`
is `none` everywhere and **no binder annotates at all**, while at fuel
`2` the smallest closed `∀` does.

Seals 1–4 never met it because the only clauses landed by then —
`.sort`, `.fvar`, `.bvar` — are exactly the three that do not recurse.
*A statement can survive every clause that does not exercise it; the
first recursing clause is the test.*

Repair: quantify the annotation fuel **independently** of the
checker's (`∀ {F}, denote2 … F d e = some ea → …`).  A strengthening,
one binder wide; `WhnfCoreClaims2F.toClaims2` checks nothing downstream
loses.

**DEFECT 2 — the equality is stated ungraded, against this file's own
architecture.**  `Claims2` concludes `interp2 ρ ea = interp2 ρ ea' ∧
(AnnotOk2 ρ ea → AnnotOk2 ρ ea')`, with the equality *outside* the
premise.  The architecture record above (§"the second soundness —
architecture", **Graded conclusions**) says the opposite, and says why:
*"reduction/defeq interp2-equalities become conditional on the
subject's `AnnotOk2` … the model's iota equality is genuinely
membership-conditional — off-domain, the recursor value's junk and the
rule tower's junk differ."*

The suppliers were built to the record, not to the seal:
`AnnotOk2_zeta`, `AnnotOk2_beta_pos`, `AnnotOk2_beta_zero` all conclude
`eq ∧ AnnotOk2 ρ ea'` **from** `AnnotOk2 ρ ea`.  β at kind `0` is where
it bites for real — off-domain `app` is the canonical junk `∅`, so the
ungraded equality is false there.

*Rule: when a seal and an earlier architecture note disagree, the note
is not stale until someone has re-argued it.  Check the record before
stating, not after the first refutation.*

**What is discharged past both defects.**  `whnfCore_claims2R` (all
nine `whnfCoreBody` cases), `whnf_claims2R` (the loop, by induction on
`whnfLoopFuel` — the map's measure discipline held exactly),
`defeqStep_claim2` (all seven blocks, transferred *verbatim* from
`Bridge/DefEq.lean` and compiled first try), `defeqStuck_claim2` (10 of
17 stuck cases), `defeq_claims2`, and Tier B's `String` half
(`strLit_facts2`, 160 lines against v1's ~394, no residues).

**Two findings for the junction, from the defeq quarter:**

* **Relational facts flow into the annotated lane for free.**
  `checkBridge` is a theorem at every `EnvR`, `EnvS2` contains an
  `EnvS`, and `EnvS.toEnvR` converts — so a `DefEq` *premise* is one
  line away.  The seal-3 STOP is therefore **one-directional**: only
  `DefEq → interp2` is blocked, not `→ DefEq`.  Worth knowing before
  anyone over-reads that note.
* **The Θ lane does not reach the binder congruences.**
  `SortOfAgreeR` carries `PairedLeaves a b`, but `defeqStep` opens
  `∀`/`λ` congruences with *each side's own* annotation, so the opened
  bodies carry `(d, n₁, ty₁)` and `(d, n₂, ty₂)` and `PairedLeaves`
  fails at index `d` — precisely where the congruence needs it.  The
  shared-numeral agreement `deqStep2_piCong`/`lamCong` demand is **not**
  a `SortOfAgreeR` instance and cannot be routed to `zip_sortOf`.  No
  other consumer has hit this.

**Also surfaced**: `AcvalParams2`, the `acval` twin of
`EnvS.val_params` — a missing `EnvS2` **field**, not a missing proof;
and `Delta2`, which corrects seal 1's "the delta exit is free":
`acval_defn` gives the *body*'s annotation, but the loop unfolds a
*spine*, and the body-to-spine step needs an annotated `mkAppN`
inversion this lane does not have.

### CAMPAIGN STOP — `CheckStep2` is FALSE as sealed, not merely hard

The fourth quarter closed the case on `Claims2`.  `InferClaims2` is not
under-supplied; it is **refuted**, and `CheckStep2` with it.

`inferClaims2_one_refuted` (`Step2/InferQ.lean`): given a stored
constant whose type is a `∀` — i.e. **every realistic environment** —
`¬ InferClaims2 μ m φ 1`.  The chain is mechanical:
`whnf_one_not_ok` (at fuel 1 the loop runs `whnfCore` at fuel 0, which
throws, so **no** `whnf` at fuel 1 ever succeeds) ⇒ `sortOfE_one = none`
⇒ `denote2_one_forallE = none`; while `inferTypeCore μ env 1 0
(.const n us)` succeeds outright.  So the claim demands a `denote2` the
fuel cannot produce.

And that propagates all the way up.  Checked, not argued:

    inferClaims2_one_refuted m hf hlen hpi
      (checkSound2 hstep m φ 1).2.2.2  :  False

compiles from `hstep : CheckStep2 μ V`.  `CheckStep2`'s hypotheses at
`fuel = 0` are the vacuous fuel-zero claims `checkSound2` already
proves, and its conclusion contains the refuted `InferClaims2 μ m φ 1`.
**The statement I sealed cannot be proved by anyone.**

Why `.const` and `.fvar` are the witnesses, and why nothing earlier
caught it: a clause that *recurses* pays for its returned type's
annotation with its own run; `.sort` and the literals return shapes
`denote2` handles with no run at all.  `.const` and `.fvar` are in
neither position — they recurse into nothing yet return a type
`inferBody` merely **reads** (the stored declaration; the leaf's
annotation), whose `denote2` is a knot computation at the claim's own
fuel.  Seals 1–4 landed exactly `.sort`, `.fvar`, `.bvar`, and `.fvar`
was already stopped for an unrelated reason, so the one witness in the
landed set was masked by a different defect.

*Rule: a claim that quantifies a fuel must be checked at the smallest
fuel, not the generic one.  Every defect this campaign found lives at
`fuel ≤ 1`, and none of them is visible in the `∀ fuel` reading.*

**Four independent defects in one sealed statement**, found by four
discharges that did not see each other:

| # | defect | found by |
|---|---|---|
| 1 | the annotation's fuel tied to the checker's (`denote2_fuelDown_false`) | whnf **and** defeq, convergently |
| 2 | the `interp2` equality stated ungraded, against this file's own architecture note | whnf |
| 3 | `InferClaims2` false at fuel 1 ⇒ `CheckStep2` false | infer |
| 4 | `CtxOkR`-on-erasures cannot serve the `.fvar` clause (`CtxOk2`) | seal 3 |

Defect 3 subsumes the *shape* of 1: both are the fuel index, and the
repair is the same — quantify the annotation's fuel independently of
the checker's, made harmless downstream by **`denote2_fuelMono`, which
is a theorem** (`knotFuelMono` landed unconditionally after `Claims2`
was sealed), not an input.  `Step2Inputs.infer_fuel_det` can be retired
for this purpose.

**Nothing is lost.**  Every quarter is discharged *past* its defects in
a repaired currency, stated and checked: `whnfCore_claims2R`,
`whnf_claims2R`, `defeqStep_claim2` (all seven blocks, transferred
verbatim from `Bridge/DefEq.lean`), `defeq_claims2`, `inferStep2_of`
(which localises the falsity in one visible field, `ConstType2`), the
`.forallE` clause outright, and Tier B whole.  313 jobs, battery
identical to baseline, axioms exactly the three throughout.

**Four corrections to my own briefs and seals**, worth more than the
proofs they came with:

* `Bridge/Infer.lean`'s prose is **stale** — it calls the five
  structural clauses "named `Prop`s pending a finding".
  `Bridge/InferStruct.lean` (472 lines) discharges I6/I7/I8/I10 and is
  the working reference.  I pointed the discharge at the wrong file.
* the unfolding recipe was needed far less than the map claimed:
  `Verify/InferLemmas.lean` already carries
  `inferTypeCore_{forall,lam,app,letE,proj,const}_inv`.
* **`SortSubstStable` is one lemma short of the β crossing** — it is
  stated for `lamSortE` only, and `denote2`'s `pi` clause under a
  substituted body needs the same stability for `sortOfE`, which has no
  statement anywhere.  A gap in the Θ lane's own deliverable.
* **the `.lam` chain-granularity mismatch**: `denote2` calls
  `lamSortE` per λ *node*; `inferBody` runs it once per λ *chain* and
  only at `mode.verified` — at `.noModel`, at no node at all.
  `InferStep2` is stated for all `μ`, so this is a real quantifier
  mismatch, not a proof difficulty.

### Seal 6 — the amended `Claims2` (`Interp2/Claims2A.lean`)

The four defects the parallel discharges found are folded into one
amended statement.  The sealed `Claims2`/`Routed` shapes stay in the
tree as the tombstone until the last quarter has migrated off them;
they are **refuted**, and nothing new may be pointed at them.

| # | repair | found by | why it was invisible |
|---|--------|----------|----------------------|
| R1 | the annotation's fuel `F` is its own binder | whnf **and** defeq, independently | only a *recursing* clause has to move a `denote2` fact down a decrement; the landed seals were `.sort`/`.fvar`/`.bvar` |
| R2 | the reduction equalities are graded by `AnnotOk2 ea` | whnf | β at kind `0` is the only counterexample and no landed seal reached β |
| R3 | the inferred type's annotation lives at some `F' ≥ F` | infer (mechanized) | `.const`/`.fvar` neither recurse nor return run-free shapes — the single masked witness |
| R4 | claims stated at `μ.verified = true` | infer | `denote2` asks `lamSortE` per λ *node*, `inferBody` per λ *chain* |

`DefEqClaims2A` is deliberately left **ungraded** — that is the shape
the defeq quarter actually proved across all seven blocks, and it is
`DeqS`'s grading, which `symm`/`trans` depend on.  Symmetry between the
four claims would have been invention; the asymmetry is the evidence.
Likewise only `InferClaims2A` takes `CtxOk2`: its `.fvar` clause is the
only one that *reads* the context rather than threading it.

`Step2Inputs.infer_fuel_det` is retired for its stated purpose:
`denote2_fuelMono` (`Step2/Fuel.lean`) is a theorem.

**Acceptance test, run and recorded** in `Claims2A.lean`'s header: the
refutation transplanted verbatim onto `InferClaims2A` no longer
elaborates, failing precisely at the repaired slot, with the two
hypothetical inputs supplied so no other step can be the cause.
`denote2_two_forallE` supplies the positive half — the annotation R3
defers really does exist one fuel up.

**Rules earned, joining the trap family.**
* *A claim that quantifies a fuel must be checked at the smallest fuel
  it admits.*  All four defects live at `fuel ≤ 1`.
* *When a seal and an earlier architecture note disagree, the note is
  not stale until someone has re-argued it.*  R2 was written down
  before the seal and simply lost.
* *A hypothesis borrowed from another currency is only as good as the
  weakest clause that reads it.*  R4 and the `CtxOk2` split are both
  this rule.
* *Four independent discharges are a statement's real proofreaders.*
  Two of the four found R1 without seeing each other's work; the
  convergence is what made the amendment safe to write at once.

### STOP 2 — `EnvS2` is unsatisfiable, and R1 was applied to three claims out of four

Found while surveying the *next* campaign item (the fourteen's
conclusion swap), before any of its work was done.  Mechanized in
`Interp2/EnvS2Refute.lean`; four compiling witnesses.

**`EnvS2.acval_defn` and `EnvS2.acval_thm` are false at every
environment that stores a λ-bodied definition or a λ-shaped proof** —
that is, every environment past `Env.empty`.  Both fields are
*equations demanding success*, universally quantified over the
annotation fuel, and `denote2` at fuel `1` returns `none` on every
binder (`denote2_one_lam`, `denote2_one_forallE`).  No hypothesis, no
run, no choice of `V` is involved:

```
acvalDefnUniform_lam_refuted : AcvalDefnUniform acval →
  .defnInfo cv (.lam n ty body mb) hint ∈ env.consts → False
```

`EnvS2.empty` is not evidence against this — `env.consts = []` makes
both fields vacuous.  **The one witness in the landed set had no
constants in it**, exactly the masking that hid the `InferClaims2`
defect one seal ago.

Consequence: the migration item *"swap the fourteen's conclusion to
`Nonempty (EnvS2 V env')`"* is not merely unproved but **unprovable**
as the structure stands.  The install layer cannot be at fault, and
work spent there would have been wasted.

**And the same argument refutes `WhnfClaims2A`**
(`whnfClaims2A_delta_refuted`).  R1 freed the annotation fuel `F` but
still demanded the *reduct's* annotation at that same `F` — and
reduction can produce a term needing more fuel than the subject did:
the delta exit turns a `.const` leaf (annotates at fuel `1`) into a
`λ` body (does not).  R1 and R3 are **one repair**, and applying it to
the inference claim while leaving the reduction claims at a fixed `F`
was the error.  Seal 6's acceptance test could not catch this: it
tested the witness it was built from, and this is a different witness.

**The corrected shapes.**  Reduction claims take R3's form —

```
∀ {F ea}, denote2 … F d e = some ea →
  ∃ F' ea', F ≤ F' ∧ denote2 … F' d e' = some ea' ∧
    ∀ ρ, Sat2 → AnnotOk2 ρ ea →
      interp2 ρ ea = interp2 ρ ea' ∧ AnnotOk2 ρ ea'
```

— composing left-to-right (the next link consumes `ea'` at `F'`), with
`denote2_fuelMono` carrying any subject annotation *up* to a common
fuel.  `DefEqClaims2A` needs no change: it produces no reduct.  The
`EnvS2` fields become R3-shaped too, which supplies the delta exit both
halves of what it now owes:

```
acval_defn : … ∈ env.consts → ∀ F, ∃ F', F ≤ F' ∧
  denote2 μ acval env φ F' 0 value = some (acval cv.name φ)
```

**Rules earned.**
* *A structure field that is an equation demanding success must be
  checked at the smallest fuel it admits, exactly like a claim.*  The
  smallest-fuel rule was recorded one seal ago for claims and not
  carried across to environment invariants.
* *When a repair is applied to some of a family and not the rest,
  the exemption needs an argument.*  `DefEqClaims2A`'s exemption had
  one (it produces no reduct, and `DeqS`'s grading is load-bearing);
  the reduction claims' did not — they simply were not re-examined.
* *An acceptance test proves the witness it was built from is dead,
  and nothing more.*  Seal 6's test passed and the statement was still
  false.  Next time, hunt a second witness before sealing.


**Repaired in the same seal.**  `EnvS2`'s two fields now read

```
acval_defn : … ∈ env.consts → ∀ F, ∃ F', F ≤ F' ∧
  denote2 μ acval env φ F' 0 value = some (acval cv.name φ)
```

and `Interp2/Claims2B.lean` carries `WhnfCoreClaims2B`/`WhnfClaims2B`
in the matching shape, with `CheckStep2B`, `checkSound2B` and the four
routed quarters.  `DefEqClaims2A` and `InferClaims2A` are reused
verbatim — neither was refuted.  `Loop.lean`'s two delta lemmas are
re-pointed.  The refutations are kept by restating the old field
shapes as `AcvalDefnUniform`/`AcvalThmUniform`, so the evidence
survives its own repair.

**The generative rule, now stated once and applied everywhere.**

> A shape that asserts `denote2 … F … e = some _` as a **conclusion**,
> for an `F` its consumer may choose, is false unless `e` is a leaf.

Applied across the family: the reduction claims asserted success for
the *reduct*, `acval_defn` for a definition's *body* — neither a leaf,
both false.  Shapes asserting `denote2` success as a **hypothesis**
are safe, going vacuous at low fuel rather than false; `CtxOk2` and
`mem_type2` are of that kind and survive.  `CtxOk2` is additionally
**monotone** in its fuel via `denote2_fuelMono`, which is what lets a
recursing clause carry the context up to the `F'` the corrected claims
hand back.

### The next campaign's gate, checked before opening it

STOP 2 killed the fourteen's conclusion swap as it stood.  Before
re-opening it, the question worth answering is whether the *repaired*
`acval_defn` is establishable at install — because if it is not, the
campaign is dead again and no amount of install-layer work helps.

It is, and the install layer already has the hook.  `EnvS.defn_eq` is
established (`Install/Value.lean`) by **defining** the valuation at the
new name to be the body's denotation — `cvalAt m.cval env name value` —
with the install key's `hkey ψ` supplying `∃ v t, denote … value =
some v ∧ …`, i.e. an *existence* hypothesis that the body denotes at
all.  The `interp2` analogue is the same move one level up: define
`acval` at the new name to be the body's annotated denotation, with an
`hkey2` supplying `∃ F' v, denote2 μ acval env φ F' 0 value = some v`.

So the repaired field's existential slots into the slot the
architecture already has.  The new content is one extra existential
quantifier in the install key, not a new theory.  Two details that
make this work and are worth having written down:

* **`denote2`'s fuel is not a recursion budget.**  It is passed
  *unchanged* to every recursive call and exists only to run
  `sortOfE`/`lamSortE`, which need `inferTypeCore`/`whnf` runs
  (`Annot/Canon.lean`).  So "some fuel" means "large enough for the
  deepest sort computation in this term", and a checked declaration's
  own successful runs are the natural source.
* **No global fuel is needed.**  `acval_defn` is `∀ F, ∃ F' ≥ F, …`
  per definition and per query, so different declarations may need
  different fuels.  `acval` itself is fuel-free — it is the value, not
  the computation — which is what keeps the structure's fields
  independent of any one budget.

This is also the first time in the arc that a campaign's central
obligation was tested against its supplier *before* the campaign
opened rather than at its end.  That is the cheap version of the
lesson STOP 2 taught expensively.

### The fuel-slack law, sharpened by the head-normalisation quarter

The rule STOP 2 recorded — *"…false unless `e` is a leaf"* — is
correct but coarse.  The whnf quarter supplied the exact version, and
it is checkable directly against `Annot/Canon.lean`:

> **`denote2` consumes fuel at `.forallE` and `.lam` nodes and nowhere
> else.**  Those two clauses call `sortOfE`/`lamSortE`; every other
> clause is either a leaf or a structural recursion at the same fuel.

Hence the precise law:

> A reduct needs `F' > F` **iff it contains a binder node the
> subject's annotation did not already pay for.**

That is strictly more informative than the leaf formulation — it says
*where* the cost is, so a clause can be classified by inspection
instead of by attempting the proof.  The quarter's classification:

| exit | slack | note |
|---|---|---|
| the six leaves, `.bvar`, stuck exits | none | no binder node in the reduct |
| **literal acceleration** | **none** | `reduceNat`'s reducts are closed on leaves by construction — fuel-free verbatim |
| delta | `∃ F' ≥ F` | **`Delta2` as stated is refuted** — λ-bodied stored definition, same witness family as `acvalDefnUniform_lam_refuted` |
| `.proj` | `∃ F' ≥ F` | refuted by any structure with a function field — every bundled class |
| iota | `∃ F' ≥ F` | premise reachable, no witness built |
| β / ζ (`Denote2Inst1`) | `∃ F' ≥ F` | structurally must need it; no refutation built, and said so rather than implying one |

**The statement needed no further change.**  `∃ F', F ≤ F' ∧ …`
already admits `F' = F`, so the fuel-preserving exits discharge it
without slack and the others use it.  Recording this explicitly
because the temptation was to add a second, tighter claim shape for
the fuel-preserving clauses; that would have bought nothing and split
the family.

Three composition facts, confirmed against the corrected claims:

* chaining reductions is `le_trans` and nothing else;
* `denote2_fuelMono` returns **the same `AVExpr`**, so the grading (R2)
  and the slack (R1/R3) do not interact — raising a fuel cannot
  invalidate an `AnnotOk2` already in hand;
* `DefEqClaims2A` staying ungraded *and* same-fuel is right **from the
  consumer's side too**, not only because it is what was proved.

And the answer to the question the amendment most needed: **no clause
requires any fixed relation between the run's fuel and the annotation
fuel.**  The two are independent throughout, `F ≤ F'` is exact, and
the slack never points downward.  That is what makes `Claims2B` a
statement rather than a guess.

### The positive half, checked rather than assumed

STOP 2 proved the old `EnvS2` fields false.  That is only half a
result: a repair that is merely *not refuted* may still be
unsatisfiable, and this arc has now been burned twice by exactly that
— `EnvS2.empty` had no constants, and seal 6's acceptance test killed
only the witness it was built from.  So the repaired field was tested
in the positive direction, in the very case that killed the old one:

* `denote2_two_lam` — the counterpart of `denote2_one_lam`.  The λ
  that fuel `1` cannot annotate, fuel `2` can.  Exact analogue of
  `denote2_two_forallE`, which played this role for R3.
* `acval_defn_repaired_sat` — the repaired field's *own shape*, at an
  arbitrary demanded fuel `F`, satisfied by a λ-bodied definition via
  `F' = max F 2` and `denote2_fuelMono`.  Stated over the field's form
  rather than a convenient special case, so it is the repair under
  test and not a weaker cousin.

*Rule: a refutation and a satisfiability witness are two different
results, and a repair needs both.*  "Not refuted" is not "usable" —
`Claims2` was not refuted for five seals.

### R4 is not free for the fourteen — the swap is not a swap [RETRACTED, seal 10]

Repair R4 (`μ.verified = true` on the claims) was ledgered as costless
"at `--set-model`".  Checked against the fourteen, it is not, and the
next campaign's framing has to change accordingly.

**All fourteen `*_R` theorems in `SetR/Main.lean` are mode-generic** —
every one binds `{μ : CheckMode}` with no constraint.  `CheckStep2B`
and its claims hold only at `μ.verified = true`, and
`CheckMode.verified` is `false` at exactly `.noModel`
(`Kernel/Env.lean`).  So a conclusion swapped from
`Nonempty (EnvS V env')` to `Nonempty (EnvS2 V env')` would be
**strictly narrower than the theorem it replaces**, silently dropping
the `.noModel` lane — which is a live, tested mode (the arena's
no-model sweep, 138 arena + 72 e2e).

**And the restriction is forced, not a proof weakness.**  `.noModel`
is the official-parity lane, and task #152's λ codomain-sort check is
deliberately *not* run there because the reference kernel's
`infer_lambda` does not run it.  `denote2` still *computes* at
`.noModel` — `lamSortE` is a function, not a check — but nothing in
the run establishes the sort it reads, so the claims are not provable
there and no amount of work makes them so.  This is a kernel design
decision (parity) surfacing as a model-lane boundary.

Consequences for the queued campaign, which should open with this
rather than discover it:

* the item is **not** "swap the fourteen's conclusion".  It is *add* an
  `EnvS2` conclusion at verified modes, keeping the `EnvS` one, or
  state the interp2 fourteen with `μ.verified = true` as a hypothesis;
* **the v1 lane is not retired by this migration.**  `.noModel`
  keeps it permanently, for the same reason the TT bridge is
  permanent — a lane that exists to match the reference kernel cannot
  be replaced by one that checks more than the reference kernel does;
* the `interp`/`interp2` containment (`EnvS2.base : EnvS V env`) is
  therefore load-bearing in the long run, not migration scaffolding.

*Rule: when a repair adds a hypothesis, check it against the
statements the campaign is ultimately for, not only against the
clauses that motivated it.*  R4 was adopted to fix a λ-clause
granularity mismatch and its cost only appears fourteen theorems
downstream.

### Fold-in checklist for the four quarters, and one null result

**The sweep came back clean where it matters.**  Applying STOP 2's
rule to the whole `Annot` layer — the tier I own — turns up nothing
else: `EnvS2`'s two repaired fields are existential, `mem_type2` and
`Canon.lean`'s success facts are hypothesis-position, and `CvalAnnot`
is stated over `Annotates`, which is relational and fuel-free and so
cannot have the defect at all.  Recording the null result because it
bounds where a STOP 3 could come from: not here, and not in the
claims — only in the quarters' own residues, which is where the four
per-owner lists were sent.

**Cleanup owed once all four quarters land** (not done now, because
three are in flight):

* `Step2/Routed.lean:55` — `checkStep2_of` concludes the **refuted**
  `CheckStep2`.  It is not unsound (its hypotheses are themselves
  unprovable), but it is exactly the hazard this campaign keeps
  writing down: *a vacuous thing with a good name looks discharged.*
  Delete `Routed.lean` and the `*Step2`/`*Step2A` quarter defs once
  `checkStep2B_of` has real inputs.
* Keep `Claims2.lean` and `Claims2A.lean` **only** for their
  refutations and lineage prose; delete their `CheckStep2`/`CheckStep2A`
  and `checkSound2`/`checkSound2A`, which nothing should ever point at
  again.
* The `# CheckStep2, …` docstring headers across the nine `Step2`
  files should say `CheckStep2B`.  Cosmetic, but the file headers are
  how the next reader decides which generation is live, and two dead
  generations are already one too many.

### STOP 3 — `DefEqClaims2A`'s exemption from R2, and my reasoning error

Found by the defeq quarter. **`DefEqClaims2A` left ungraded is not
provable.** The exemption I wrote at seal 7 — *"it produces no reduct,
so it needs no slack and no grading"* — is right about **production**
and wrong about **consumption**: `defeqStep`'s first move is to
`whnfCore` both sides, which consumes the now-graded reduction claims,
and at those two sites the quarter holds no `AnnotOk2` for either
subject and cannot manufacture one (`denote2` performs no membership
check at an `app` node; `WScoped`/`looseBVarsBounded`/`LeavesBounded`/
`CtxOkR` are all syntactic).

I had given the reduction claims' exemption from R3 a second look one
seal earlier and explicitly *declined* to give defeq's the same, on
the grounds that its asymmetry "was what the quarter actually proved".
That was evidence about the sealed statement, not about the corrected
one — and the correction is exactly what invalidated it.

`DefEqClaims2B` (in `Claims2B.lean`, the quarter's `DefEqClaims2AP`
verbatim) is now canonical, and `CheckStep2B` and all four routed
quarters are stated with it: the induction cannot close with an
ungraded hypothesis and a graded conclusion, so the family had to
become uniform rather than the defeq slot staying special. The two
`AnnotOk2` are **premises, never conclusions**, so none crosses an
equality and `deqStep2_symm`/`deqStep2_trans` stay one-liners — which
is what the original exemption was protecting, and it turns out not to
have needed the exemption to get it.

*Rule: an asymmetry justified by "this is what was proved" expires the
moment the thing it was proved against is corrected.*

**Confirmed by the fold:** the whnf quarter's two deliverables still
compile with the *weaker* graded IH, so they never needed defeq's
ungraded strength. The asymmetry bought nothing at any consumer.

### Seal 8 — the four quarters folded in

All four re-points landed, reviewed, merged; build green (316 jobs,
zero warnings), no `sorry`, axioms exactly the three standard, battery
90/92 with e2e 72/72 and the no-model sweep unchanged.

| quarter | deliverable | own refutations found |
|---|---|---|
| whnf | `whnfCoreStep2B_of`, `whnfStep2B_of` | `delta2_refuted`, `projStep2_refuted` |
| defeq | `defEqStep2BP_of` → `defEqStep2B_of` | STOP 3 (above) |
| dispatch | `infer_{sort,fvar,bvar}_claim2A`, literals, the `CtxOk2` kit | `ctxOk2_one_forallE_leaf_false` |
| infer | in flight | — |

**Three results worth keeping from the quarters' reports.**

* **The rule's two-sidedness, stated properly by the dispatch
  quarter:** *the smallest-fuel test is about which side of the arrow
  the success-demanding equation is on.* They mechanized both halves
  for `CtxOk2` — `ctxOk2_one_forallE_leaf_false` (empty at `F = 1`
  for a ∀-typed leaf) **and** `ctxOk2_zero_inhabited` (holds at every
  fuel at depth 0) — rather than reporting the negative alone. That is
  the practice this campaign has been converging on, arrived at
  independently.
* **R3's slack is unspent in the whole dispatch and literal layer.**
  `.fvar` — the clause that *forced* `CtxOk2` — takes `F' = F`,
  because it reads the context at the claim's own fuel. `.const`
  spends the slack because its type comes from the environment, not
  from a hypothesis about the context. R4's `μ.verified` is unused
  there too. Both premises were kept and the non-use documented as
  evidence.
* **`denote2`'s depth-shift law exists and was nearly free.** There was
  reason to fear it could not: `denote` depends on depth only through
  its `fvar` clause, while `denote2` also calls the *checker* at that
  depth. `Setlec.shiftClaims` (`Verify/Deep.lean`), landed for the
  memo cache's depth-free keys, is exactly the bisimulation needed.

**T5 applied, and one field added.** The dispatch quarter carried
`hacl : ∀ n ψ k, (acval n ψ).liftN 1 k = acval n ψ` as an explicit
premise for want of a supplier. It now has one: `EnvS2.acval_closed`,
the transpose of `EnvS.cval_closed`. Syntactic — no `denote2` in it —
so unlike the two fields STOP 2 refuted it cannot go false at a small
fuel, and it is `rfl` at `EnvS2.empty`. Deliberately *not* a new
`AVExpr.Closed` predicate: the lifting equation is what consumers
rewrite with.

**Two integration findings from writing four files in parallel.**
`DefEqRun.lean` and `Step2/Whnf.lean` both declared `denote2_bvar`
with identical statements (resolved by deletion); `denote2_sort` is
the same pair between `Whnf.lean` and `InferQ.lean`, latent only
because `InferQ` is not yet in the import closure. *Parallel quarters
converge on the same helper names, and the collision surfaces at
integration rather than at authoring.*

**Open at the junction, for the infer quarter:** a consumer of the
defeq claim must now supply `AnnotOk2` for the two **types** it
compares. `InferClaims2A` delivers it for the *subject* and says
nothing about the returned type. Whether `InferClaims2A`'s conclusion
needs extending is asked of the infer quarter against a site it can
point at — not adopted by symmetry.

### Seal 9 — the capstone: `CheckStep2B` follows from eight residues

`Interp2/Capstone.lean`: `checkStep2B_of_quarters` and
`checkSound2B_of_quarters`. Every hypothesis is a **named routed
residue** owned by one quarter; none is a claim about the checker's
runs, and none is discharged there. What this establishes is that the
*decomposition closes* — the remaining work is a finite list of named
obligations rather than an open question about the shape of the
induction.

Residues: `Denote2Inst1B`, `BetaCert2`, `IotaStep2B`, `ProjStep2B`
(whnfCore); `ReduceNatStep2`, `Delta2B` (the loop); `DefEqStep2BP`
(defeq's ten); `InferInputs2A` (infer's).

**Three generations were needed** — `Claims2` → `Claims2A` →
`Claims2B` — and each was refuted by a **consumer**, never by
inspection. The consumers were the four quarters running in parallel
against the statement. That is the transferable result of this arc:
*a statement seal is validated by discharging it in parallel from
several directions, not by reviewing it.* Every one of the three
defects was invisible to the seal's own author and obvious to the
quarter that had to pay for it.

### The integration cost of parallel authoring, measured

Four quarters written simultaneously against a moving statement cost
**three name collisions and one stale-signature break**, all surfacing
at the fold and none at authoring:

* `denote2_bvar` — declared identically in `DefEqRun` and `Whnf`;
* `denote2_sort`, `sortOfE_one`, `denote2_one_forallE` — `InferQ` vs
  `Whnf`, latent until `Claims2B` entered the closure; renamed
  `…Q`/`…_at_one` by the infer quarter on request;
* `infer_natLit_claim2A` — written twice, by the dispatch and infer
  quarters, same conclusion. The dispatch copy took four explicit
  membership premises; the infer copy bundles one routed `NatHeads2`
  and derives the returned type's annotation from the support guard.
  **Kept the infer copy** (strictly stronger, and the one the assembly
  calls); deleted the dispatch copy.
* `infer_app_claim2A` took `ihd : DefEqClaims2A` because it was
  written before STOP 3 was adopted mid-flight. Repaired at the fold
  by paying the two `AnnotOk2` premises — `TypeOk2` for the argument
  type, `AnnotOk2_pi` on R2's own output for the domain. **Cost:
  nothing new**, exactly as the infer quarter predicted.

*Rule: a mid-flight statement change costs one integration break per
consumer, and the break is silent until the fold — so change the
statement early or not at all.* Adopting STOP 3 mid-flight was right
(the alternative was four quarters closing against a false claim), but
it was not free.

### R4 may be removable, and that would recover `.noModel` [SETTLED, seal 10: it is]

The infer quarter reports **`μ.verified = true` is not what fixed the
`.lam` clause** — `lamSortE_runs` reads the #152 codomain run out of
the hypothesis annotation, so the chain-granularity mismatch dissolves
under R1/R3 and `LamCodSort2` is retired outright. R4 is now consumed
*only to pass to the induction hypothesis*, which needs it only
because the claims carry it.

That is a fixed point that may be removable: if no clause uses R4 for
anything but threading, dropping it from all four claims should
succeed. Worth doing, because R4 is what costs the fourteen the
`.noModel` lane (recorded above) — removing it would recover the
mode-generic conclusion the migration was assumed to preserve.

**Not attempted here**, and deliberately: the claim family has been
refuted three times, twice by a repair applied to part of it. A fourth
statement change goes through the same parallel discharge as the other
three, not through a plausibility argument at the junction.

### Still open at the junction: `CtxOk2R` is believed false

The infer quarter's `.app` clause consumes `CtxOk2` (from
`InferClaims2A`) **and** `CtxOkR`-on-erasures (from `WhnfClaims2B` and
`DefEqClaims2B`), so it needs a bridge, and `CtxOk2R` — stated, not
proved, and believed false — is that bridge. It would need an
`∃ T', Infer … ∧ DefEq …` derivation out of an `interp2` equation:
the "no `VExpr → AVExpr`" wall, in the direction seal 3 did not test.

The repair is statement-level and belongs here, not to a quarter: the
dispatch quarter's original proposal was to substitute `CtxOk2` for
`CtxOkR` in **all four** claims, and only `InferClaims2A` was changed.
That is the *third* time in this arc a repair was applied to part of
the family and not the rest — the same error as R2/R3 and as STOP 3.
The pattern is now explicit enough to state as a rule:

*Rule: when a repair changes one claim of a mutually-recursive family,
the default is to change all of them; an exemption needs an argument
that survives the other repairs in the same seal.*


### Seal 10 — R4 withdrawn, and a retraction of my own reasoning

**R4 is removed from all four claims. The `.noModel` lane comes back.**
Verified: `CheckStep2B`, `checkSound2B`, `checkStep2B_of_quarters` and
`checkSound2B_of_quarters` are mode-generic again, and I checked the
payoff directly rather than taking it on report — `noModel_step`
instantiates the capstone at `CheckMode.noModel` and elaborates, with
`CheckMode.noModel.verified = false` by `rfl` beside it.

**The strongest form the evidence could take:** the removal was green
on the *first* compile, and the diff contains **no line where a proof
step was rewritten** — only deleted binders and deleted arguments.
Eleven Prop-level premise lines, eleven theorem binders, ~48 intro and
application sites, and not one tactic changed. R4 was a fixed point of
the induction and nothing else: the claims carried it only so that
they could pass it to themselves.

**I have to retract the reason, not only the conclusion.** Seal 8 said
the `.noModel` restriction was *forced* — "a kernel design decision
(parity) surfacing as a model-lane boundary", and "nothing in the run
establishes the sort it reads, so the claims are not provable there
and no amount of work makes them so". The second half is **false**,
and checkable in five lines of `Annot/Canon.lean`:

```
def lamSortE mode env φ fuel d body :=
  match (inferTypeCore mode env fuel d body).toOption with
  | none => none
  | some bt => sortOfE mode env φ fuel d bt
```

`lamSortE` is not a readback of the checker's run. It performs
`denote2`'s **own** `inferTypeCore` and `sortOfE` runs, at the
annotation fuel, entirely independently of whether `inferBody`
executed the task-#152 codomain check during the run under test. So
once R1/R3 moved the subject's annotation to the hypothesis side, the
λ node's sort numeral arrives as a hypothesis *carrying its own two
runs with it*, and no clause anywhere asks that the checker have
checked it. The granularity mismatch R4 was invented for stopped
existing at seal 7 and nobody noticed for three seals.

**Not vacuous, which is the check that makes the answer worth having.**
`.noModel` runs strictly *fewer* checks, so `inferTypeCore` succeeds at
least as often and `denote2` at `.noModel` is if anything *more*
defined than at the verified modes — confirmed by instantiating
`denote2_two_lam` there. And the soundness burden did not migrate: what
still has to hold is that `lamSortE`'s numeral is semantically right,
which is `SortSem2`, a routed residue stated over `sortOfE`, already
mode-generic and untouched by any of this. R4 was never buying a part
of it.

**What `.noModel` actually costs** is a *harder residue discharge* —
its inference runs check less, so `SortSem2` and its neighbours have
less to lean on there — not an unstatable claim. That is a real cost
and it lands on the residues, where it can be measured.

**Rules earned.**
* *A premise that only ever feeds itself is a fixed point, and fixed
  points are removable until proven otherwise.* R4 survived three
  seals because every clause could point at another clause that
  "needed" it.
* *When you record that something is impossible, record the mechanism,
  because the mechanism is what gets falsified.* Seal 8's conclusion
  was wrong only because its mechanism was wrong, and the mechanism
  was checkable in one function definition. Had I written "R4 is
  needed because X" and checked X, this would have been a one-seal
  detour instead of three.
* *A spike is a discharge when its diff shows no tactic changed.*

### Seal 11 — `CtxOk2R` is false, and the family-wide `CtxOk2` question is resolved

`Interp2/Step2/CtxOk2RRefute.lean`. The headline is **premise-free**:

```
not_ctxOk2R : ∀ (m : EnvS2 V env) (μ : CheckMode) (φ : Name → Nat),
  ¬ CtxOk2R m μ φ
```

No environment shape, no fuel, no mode, no level assignment, no side
condition. Restated as `CtxOk2RShape` so it survives any repair of the
original, per the `AcvalDefnUniform` pattern.

**The reason is not the one anyone expected.** The suspicion was the
relational wall — deriving `∃ T', Infer … ∧ DefEq …` from an `interp2`
equation. The actual reason is structural and cheaper: `CtxOk2` states
its leaf agreement under `Sat2` (annotated currency); `CtxOkR`'s only
semantic reading is via `Sat` (collapse currency); and **the two
currencies disagree about which contexts are inhabited**, exactly at an
empty-domain λ. That is the **#100 countermodel**, named in
`lamR_pos_empty`'s own docstring:

* `interp2 ⟪fun (_ : Empty) => Prop⟫ = ∅` — at `v ≠ 0` the annotation
  decides, not the vacuous value test;
* `interp ⟪fun (_ : Empty) => Prop⟫.erase = pt`.

At `d = 1`, `Δa = [emptyLamA]`, subject `.fvar 0 n Prop`: `Sat2` is
unsatisfiable so `CtxOk2` holds for free, while `CtxOkR` still owes an
`Infer`/`DefEq` pair that `Infer.sound`/`DefEq.sound` turn into
`ptTag ∈ˢ univ 0` at `ρ ≡ ptTag`, where `Sat` *is* satisfiable.

The discipline that forced honesty here: an *honest* `⟪Empty⟫` entry
does **not** refute — empty in both currencies, so `Sat` dies too and
soundness says nothing. **Only a currency disagreement is decisive.**
And `ctxOk2R_refuted_nonvacuous` shows it is not a vacuity artifact:
the same contradiction with the `interp2` agreement holding for every
`ρ` unconditionally.

**The smallest-fuel test did not fire, and that is worth recording.**
`CtxOkR` asserts `denote` (fuel-free), and `CtxOk2`'s `denote2`
obligation sits in a hypothesis. The refutation is uniform in `F`. The
trap that caught three statements did not catch this one; the argument
had to be semantic. *A trap-check that comes back clean is not a
clean bill of health.*

#### The resolution, under the family-wide rule

Measured, not guessed — kit *uses*, not occurrences (the hypothesis is
threaded on ~120 lines and almost none look at it):

| use | Whnf | DefEqRun | `CtxOk2` supplies it? |
|---|---|---|---|
| `of_subset` | 10 | 24 | yes |
| leaf re-assembly | 7 | 0 | yes (`of_cover`/`length`) |
| `of_fvarLeaves_nil` | 0 | 8 | needs a one-line twin |
| `openCong` | 0 | 5 | **no — the one real reader** |

**41 of 54 are pure `fvarLeaves` re-plumbing; 8 need a one-liner; 5
are a genuine read.** All five are `CtxOkR.openCong` at the `∀`/`λ`
congruences, where the checker opens each side's body with its own
annotation, so the second body sits in a context whose head is the
*left* domain while the opened variable's annotation denotes the
*right* one. `CtxOkR` absorbs that with a bare `DefEq A₁ A₂`.

Under the rule adopted at seal 9 — *an exemption needs an argument
that survives the other repairs in the same seal* — **the exemption
does not survive.** The annotated `openCong` is available:
`DefEqClaims2B`'s conclusion *is* the domains' `interp2` equality. It
is available only **graded**, under `AnnotOk2` of both domains — but
those are the same two facts `DefEqClaims2B` already takes at top
level. So the repair converts one bare `DefEq` premise into a graded
semantic one at five sites, and is plausibly payable at all five.

**Decision: all four claims move to `CtxOk2`.**

**The alternative I considered and rejected.** The refutation is
admitted *purely* because `CtxOk2` puts no well-formedness condition
on `Δa` — no `CtxAnn`, no `AnnotOk2` — and the refuting `Δa` is not
one `CtxOk2.open` could build from a checker-accepted subject (a λ is
not a `Sort`, so it is not a binder domain). So a second repair
exists: strengthen `CtxOk2`'s `Δa` and the bridge might become true.
Rejected, for two reasons. It is speculative — "might", and it would
need its own refutation hunt. And it keeps two currencies mixed at the
seam, whereas the currency mismatch itself
(`interp2 ⟪λ(_:Empty).Prop⟫ = ∅` vs `interp …⟫.erase = pt`) remains a
live fact about *any* statement spanning both lanes. Moving to
`CtxOk2` removes the seam; strengthening `CtxOk2` only removes this
counterexample to it.

*Distinction to keep: `CtxOk2R` is false **as stated**. Whether a
strengthened `CtxOk2` could support some bridge is untested, and
choosing the family-wide move means we never have to find out.*

#### Open, and named so it is not lost

**`CtxOk2Open` has not had its trap-check.** Its conclusion asserts
`denote2 … F (d+1) …` for annotations only hypothesised at
`denote2 … F d …`, and `denote2`'s binder clauses call
`sortOfE … F d`, which runs the checker *at that depth*. The
hypotheses demand the same successes at the same fuel, so the
smallest-fuel test likely goes vacuous rather than false — but the
**depth** shift is the untested part, and `denote2_shiftFrom` carries
side conditions. Owner: whoever discharges `CtxOk2Open`. Flagged by
the refutation's author, who correctly declined to test a residue
outside their brief.

### Seal 12 — the residue batch: one discharged, three blocked on missing `interp2` laws

`Delta2B` is **discharged modulo one obligation** (`delta2B_of`). The
residue's own docstring said "the annotation does not move, only the
fuel does" — right, and not the whole bill. `unfoldDefinition` hands
the loop `value.instantiateLevelParams cv.levelParams us`, under a
spine, at the subject's depth, while `EnvS2.acval_defn` speaks about
`value`, at depth `0`, under a *substituted* assignment. **Three
crossings**, of which two are now theorems in a new reusable module
`Interp2/Step2/Levels.lean`: `denote2_mkAppN_swap` (head swap under a
spine, fuel free to move up) and `denote2_depth_of_closed`.

**The third crossing is not a clean induction, and that is the finding.**
On v1 it is `denote_instLevels`, one induction, because `denote` reads
the level assignment only at `.sort` and `.const`. **`denote2` reads it
there *and* through `sortOfE`/`lamSortE`, which are checker runs** — so
at every binder node the crossing relates two *runs* on two different
terms. It is a metatheorem about the checker, the level-side twin of
`shiftClaims`, and it has no counterpart in the tree. Named
`Denote2InstLevels`.

**Three of eight residues are blocked on missing environment laws, not
on proofs.** This is the batch's most valuable output:

* **`ReduceNatStep2` is not the cheap one.** Its fuel half was settled
  (`natOpResult_leaf`); its *semantic* conjunct has **no supplier**.
  `EnvS.nat_ops : NatOpsV` is stated over `denote`/`interp`/`cval`, and
  `EnvS2` has no `interp2` counterpart — the erasure link cannot carry
  it, because `interp2` is the two-regime annotation-driven
  interpretation, not `interp ∘ erase`. v1 escapes by concluding a
  `Red` whose soundness consumes `nat_ops` elsewhere; the interp2
  claims conclude the equality directly, so the law must be present.
* **`ProjStep2B` and `IotaStep2B` are the same class** — the fired
  modeled-iota law and the native-pair projection law, neither of
  which exists over `interp2`.

By T5 these belong to their suppliers, exactly as `RecRulesV2` is
deliberately absent from `EnvS2` today. *The interp2 migration's real
remaining cost is a set of environment laws, not a set of proofs.*

**`BetaCert2` produced a result worth more than its discharge.**
`betaCert2P_of_claims` composes `InferClaims2A` and `DefEqClaims2B`
into the β certificate, and needs exactly one thing the quarter cannot
build: `CtxOk2` on the argument, from `CtxOkR`-on-erasures. So:

* **`CtxOk2R` has a second, independent consumer.** The seam is not
  the inference `.app` clause's alone, and both sites want the same
  repair — the context currency made uniform, which seal 11 already
  decided. Two independent confirmations of one statement change.
* **Seal 8's open question is answered from a second site**: yes,
  `InferClaims2A`'s conclusion needs extending to carry the returned
  type's `AnnotOk2`, because `DefEqClaims2B` is graded on both sides.

Deliberately **not** wired in: `BetaCert2P` adds a premise its
consumer cannot supply, and weakening `BetaCert2` to fit would have
been the failure mode this campaign keeps naming.

#### The `AcvalDefnInst` request: accepted in principle, with the cost stated

The batch recommends restating `EnvS2.acval_defn`/`acval_thm` at the
*instantiated* value (`AcvalDefnInst`), which discharges `Delta2B`
outright. It is a verified **strengthening** — the current fields are
its identity-substitution instance
(`acval_defn_of_acvalDefnInst`, `substFn_param_self`) — so nothing
downstream is lost.

**Checked at the junction before accepting, per the standing rule that
a strengthening must also be shown inhabited:**
`acvalDefnInst_noParams` derives the proposed shape from the *existing*
fields at any declaration with no level parameters. So it is satisfiable
well beyond `EnvS2.empty`'s vacuity, and only genuinely
level-parametric declarations need new content.

**But it relocates rather than removes the obligation, and that must be
on the record.** Defining `acval c ψ` as the body's denotation under
`ψ` makes the field ask precisely `Denote2InstLevels` at the install
site. The batch preferred relocation because it doubts the metatheorem
is true at all — `piResultIsProp`/`piResultNeverZero` (`Kernel/Core.lean`)
make the structure-eta rescue and the irrelevance branch
**level-sensitive**, so a run genuinely can change behaviour under
instantiation. No witness either way; flagged as a risk, not a
refutation, and correctly so.

Relocation is still the right move — the install layer knows the
declaration was *checked* and chooses `acval` itself, neither of which
the delta exit has. **Adoption deferred until the `openCong` worker
lands**, because a fifth `EnvS2` change while an agent is mid-flight is
exactly the silent integration break seal 9 made a rule about.

**Named as the install campaign's gate:** whether `AcvalDefnInst` is
establishable at install, and whether `Denote2InstLevels` is true at
all. The second question now has a concrete attack — find a
declaration whose `piResultIsProp` branch flips under level
instantiation, or prove it cannot.

### Seal 13 — the `openCong` gate proves; and the ρ-quantifier finding

Seal 11's family-wide move was gated on one lemma. **It proves.**
`CtxOk2.openCong` (`Step2/Dispatch.lean`), plus the trivial
`CtxOk2.of_fvarLeaves_nil` twin. All axioms exactly the three standard.

**`CtxOk2Open` is not a residue at all — it is a premise-free
theorem.** `ctxOk2Open_of` (`Step2/CtxOk2OpenD.lean`). The trap-check
DESIGN flagged as owed came back on both dimensions: the *fuel*
dimension goes **clean, not vacuous** (the residue asserts no `denote2`
success its consumer does not hand it — `denote2_weaken_top` is an
equation uniform in `F`, and its two obligations are the `sortOfE`
shift equations, also uniform), and the *depth* dimension — the part
nobody had tested — is discharged because `denote2_shiftFrom`'s three
side conditions are all already available.

**And the reason the third one is available is worth its own line.**
`CtxOk2.wScoped`: **`CtxOk2` already carries its own scoping.** Its
leaf package gives `l.1 < d ∧ fvarsBelow l.1 l.2.2` *hereditarily*
(`Expr.fvarLeaves` descends into annotations), which unrolls to
`Expr.WScoped d e`. The `fvar` case is the content: the leaf's own
`fvarsBelow idx ty` is what lets the recursion drop from `d` to `idx`,
which a plain `fvarsBelow d` cannot. So `openCong` and `openS` need no
scoping premises, and `CtxOk2Open` is satisfiable *as stated*, with
neither `WScoped` it omits. *A predicate written for one purpose was
already strong enough for another; nobody had unrolled it.*

#### The ρ-quantifier: the grading is in the wrong scope

`hdom` is free at all five congruence sites — literally
`DefEqClaims2B`'s conclusion partially applied before its `ρ`. The two
`AnnotOk2` are **not**. `DefEqClaims2B` takes them *under* `∀ ρ`, so a
site that has already done `intro ρ hρ hokA hokB` holds them at **one**
valuation; `CtxOk2` is a `∀ ρ` statement about the *extended* context
and needs them at every satisfying one.

**This is not an artifact of the proof.** `not_openCongLocal` is a
**premise-free refutation** of the ρ-local lemma — `d = 1`,
`Δa = [⟪Sort 1⟫]`, `ta₂ = .bvar 0`, `ta₁ = ⟪Sort 0⟫`: they agree at
`ρ ≡ univ 0`, and the extended context's leaf link at `ρ ≡ ∅` demands
`∅ = univ 0`, hence `∅ ∈ˢ ∅`. Even with the left domain fully
certified. *The problem is the quantifier, not the grading.*

`AnnotOk2.hoist_pi`/`hoist_lam` show the repair self-propagates: the
hoisted node fact splits into the domain's hoisted form and the
codomain's hoisted form in the extended context — exactly the pair the
recursive call needs.

#### The blast radius, audited at the junction

The request was to hoist `DefEqClaims2B`'s two `AnnotOk2` above its
`∀ ρ`. The worker verified the congruence consumer and correctly
flagged the rest as unaudited. **Audited here, and it propagates —
which is the seal-9 rule firing for the fourth time:**

* `betaCert2P_of_claims` (`Whnf.lean`) takes its `AnnotOk2 ρ tya` from
  **`BetaCert2P`'s own ρ-local premise**, so `BetaCert2P` must hoist
  too. Its other one comes from `TypeOk2`, which is already all-ρ and
  costs nothing.
* `infer_app_claim2A`'s `hdom` takes `AnnotOk2 ρ Aa` from the
  **reduction claim's graded output at one ρ** (`hredf ρ hρ …`). So
  `WhnfCoreClaims2B`/`WhnfClaims2B` must hoist as well — their
  conclusion `∀ ρ, Sat2 → AnnotOk2 ρ ea → (… ∧ AnnotOk2 ρ ea')` is
  ρ-local on both sides.

So the change is **all four claims plus `BetaCert2P`**, not
`DefEqClaims2B` alone. Consistent with the rule and with the three
previous times a repair was scoped to one claim and had to be widened.

**Not made now, deliberately.** It is a four-claim statement change and
this campaign's own evidence is that such a change must be
re-discharged in parallel by the quarters, not applied at the junction
and hoped through — every one of the three refuted generations was
refuted by a consumer. It is the next campaign step, and it is now
fully specified: the shape, the mechanized proof that the weaker form
is false, the propagation set, and the fact that the repair
self-propagates at the congruences.

**Standing after this seal.** Seal 11's move is unblocked at four of
its five reading sites and specified at the fifth. `CtxOk2Open` is off
the residue list. The eight capstone residues stand at: one discharged
(`Delta2B`, modulo `AcvalDefnInst`), three blocked on missing `interp2`
environment laws, one on the `SortSubstStable` lane, and three open.

### Seal 14 — statement generation four: the grading hoisted above `ρ`

`Interp2/Claims2C.lean`. Every `AnnotOk2` a claim **takes** or
**gives** moves above the `∀ ρ`; the `interp2` equalities and the
membership stay per-valuation, being genuinely per-valuation facts.

**The first generation change in this arc that fixes an insufficiency
rather than a falsehood.** `Claims2` and `Claims2A` were refuted;
`Claims2B` is not. It is merely too weak to supply
`CtxOk2.openCong` — and `not_openCongLocal` proves premise-free that
no ρ-local congruence lemma exists to supply instead, even with the
left domain fully certified. *The problem is the quantifier, not the
grading.* Recording the distinction because "superseded" and "refuted"
have been the same word too often in this campaign.

**`InferClaims2C` is also extended**, not merely hoisted: it now
delivers the returned type's `AnnotOk2` beside the subject's. That is
seal 8's open question answered from two independent sites
(`infer_app_claim2A`, `betaCert2P_of_claims`), and it retires the
inference quarter's `TypeOk2` residue.

**Direction, so the quarters know what they are being handed.** Each
claim's `AnnotOk2` premises became ρ-uniform, so each claim is
*weaker*: producers prove less, consumers get less. The two claims
that also deliver an `AnnotOk2` deliver it ρ-uniformly, which is
stronger on the output side. Net: the reduction and inference quarters
owe more at their conclusions and are owed more at their hypotheses;
the defeq quarter is purely relieved. **That asymmetry is the point** —
it is what lets a congruence site hand `openCong` the ρ-uniform pair
it provably cannot obtain otherwise.

**One change per generation.** Seal 11's context-currency move
(`CtxOkR` → `CtxOk2` in all four claims) is decided and specified but
is *not* in this generation. Bundling two independent statement
changes is how an integration break stops being localizable, and this
campaign already paid for one mid-flight change. The context move is
generation five.

**Re-discharged in parallel, not sequentially.** Four workers, one per
quarter, concurrently — because every one of the three refuted
generations was refuted by a *consumer*, never by inspection, and
sequential discharge would find the same defects one at a time after
the statement had already been built on.

### Seal 15 — the three missing `interp2` environment laws, stated and queued

`Interp2/EnvLaws2.lean`. Seal 12's finding turned into statements:
`NatOpsV2`, `RecRulesV2`, `ProjPairV2` — the suppliers for
`ReduceNatStep2`, `IotaStep2B` and `ProjStep2B`, which are blocked on
**laws that do not exist**, not on proofs.

**Stated as first drafts, and labelled as such in the file.** They are
deliberately *not* wired into `EnvS2`. This campaign's evidence is
that a statement is validated by the consumer that discharges it —
three `Claims2` generations were refuted, every one by a consumer,
never by inspection — so each law is derived from what its residue
visibly needs, with the v1 sentence as the guide, and each is expected
to move before adoption. The path is the one `AcvalParams2` took:
`Prop` here, diagnosed by its consumer, promoted to an `EnvS2` field
when the install tier can establish it. **T5: every one names its
install-tier supplier in its docstring**, and in each case it is an
existing `EnvS.cons` obligation (`hheadNat`, `hheadRec`,
`hheadProj`/`hheadProjPair`).

**The trap-check applied in advance.** Each law asserts a `denote2`
success as a conclusion, and a recursor RHS or a `Nat` equation may
carry a binder — so all three are stated with the existential fuel
slack seals 7 and 12 established, never at a caller-chosen fuel. Seal
11's caveat stands: passing this check is not a clean bill of health.

**One of the three is honestly weaker than the others**, and the file
says so. `ProjPairV2` has **no v1 sentence to transpose** — v1's
`ProjOkT` is purely syntactic and says nothing semantic — so it is
derived from the consumer alone. Its scope is the *native* pair only,
per the standing `proj-unification-limits` finding that modeled types
can never get first-class `.proj`.

**Ordering the evidence suggests**, recorded in the file:

1. **`Denote2InstLevels` first.** `RecRulesV2` takes its RHS at
   `instantiateLevelParams`, so it meets seal 12's open metatheorem
   head-on — the *same* crossing that blocks the delta exit. Settling
   it once serves both, and seal 12 recorded a live doubt that it is
   true at all (`piResultIsProp`/`piResultNeverZero` make a run
   level-sensitive). **If it is false, `RecRulesV2` as drafted is the
   wrong statement**, which is precisely why it goes first.
2. `NatOpsV2` — most complete v1 counterpart, supplier obligation
   already exists.
3. `ProjPairV2` — least settled.

These three join the five install keys and `MemberKeyS` as the
install-tier campaign.

### Seal 16 — generation four, the head-normalisation quarter (and a correction)

`whnfCoreStep2C_of` and `whnfStep2C_of`, both proved, both on exactly
the three standard axioms. **No statement change and no `EnvS2` field
requested** — generation four is sufficient for this quarter, and it
built first try.

**Correction to the junction's own briefing.** I told the four workers
that the reduction and inference quarters are "on the paying side" of
the ρ-hoist and the defeq quarter is relieved. For the reduction
quarter that is **wrong, and structurally so**: `whnfCore` **never
opens a binder** — `.forallE` and `.lam` are two of its six *leaf*
cases — so `Δa` is constant through every clause and every loop
iteration, and the extended-context pair is never asked for.

Consequently `AnnotOk2.hoist_pi`/`hoist_lam` were **not used and not
needed** here. What each clause needs is a *component* of the node
fact at the **same** `Δa` (`AnnotOk2_app.1`, `AnnotOk2_zeta.2`,
`AnnotOk2_beta_pos/zero.2`), and every one is already a pointwise
implication, so pushing it under `∀ ρ` is literally
`fun ρ hρ => …`.

*The hoist is free exactly where the recursion does not change the
context; `hoist_*` is the price of the sites that do — the
congruences.* So generation four's cost is not "reduction and
inference pay, defeq is relieved"; it is **"whoever changes the
context pays"**, which is a different and smaller set. Recorded
because the junction's cost model was wrong in a way that would have
mis-scoped the next generation too.

**`TypeOk2` is gone, not relocated.** `betaCert2PC_of_claims` takes no
`htok` at all: the `…B` composition needed an explicit stand-in for
the inference quarter's residue because `InferClaims2A` concluded
`AnnotOk2` of the subject and never of the returned type.
`InferClaims2C` delivers both, ρ-uniformly, which is exactly the shape
`DefEqClaims2C` takes. **Seal 8's open question is now paid back from
the second site DESIGN named for it.**

**A methodological point worth keeping.** The three hoisted residues
(`IotaStep2C`, `ProjStep2C`, `ReduceNatStep2C`) each land with a
`toC` bridge proving the *existing* `…B` residue implies it. So the
hoist **weakens** what suppliers owe and strengthens nothing — and *a
weakening of an already-audited statement cannot become false*, so the
three need no fresh refutation hunt. That is the cheapest form of
trap-check available and it should be the default whenever a
generation change is a weakening: **prove the bridge from the old
shape, and inherit its audit.**

`BetaCert2PC` is deliberately still **not** wired into
`whnfCore_app_claim2C`: it needs `CtxOk2` where the `.app` clause has
only `CtxOkR`-on-erasures, which is seal 11's context-currency move,
i.e. generation five. `BetaCert2` remains the residue the quarter
routes through.

*Hygiene note:* the four generation-four worktrees were created from
inside the `discharge` worktree, so they nested under it rather than
sitting beside it. Harmless to git, but the briefs' paths were wrong
and each worker had to find its own tree. Create worktrees from the
repository root.

### Seal 17 — generation four's defeq and inference quarters

Both landed green, both on exactly the three standard axioms, neither
requesting a statement change. Three of four quarters are in.

**Generation four's central purpose is validated.**
`binder_ctxOk2_openCong` discharges `CtxOk2.openCong` **from
`DefEqClaims2C` and nothing else**: `hok₁`/`hok₂` *are* the claim's two
hoisted premises verbatim, and `hdom` *is* its conclusion with `ρ` and
`Sat2` still abstracted. The quantifier obstacle `not_openCongLocal`
identified is gone.

The quarter also checked the thing nobody asked it to:
`binder_ctxOk2_openCong_sat` verifies the remaining premises are
**jointly meetable** at a concrete one-binder instance, so the lemma is
not an implication out of contradictory hypotheses. *That check is now
being run unprompted by workers, which is the practice propagating on
its own.*

**One new idea, and it is the self-propagation made explicit.**
`Sat2_cons_congr`: `hoist_pi`/`hoist_lam` deliver the *right*
codomain's hoisted fact over `ta₂ :: Δa`, while the congruence recurses
over `ta₁ :: Δa`. The domain equality moves it — and is available
ρ-uniformly *precisely because it is the claim's own conclusion before
its `ρ`*. The `…A` lane made the same move at one valuation; hoisting
changed its shape, not its content.

**`TypeOk2` is retired outright**, confirmed from the second quarter:
`InferInputs2C` sheds the field. Its three uses were all in `.app`, and
all three are now the induction hypothesis's own new conjunct, at the
same annotation and fuel — arriving ρ-uniform, which is what the
hoisted claims demand and what `TypeOk2` had been supplying only
*coincidentally*. The extension is what makes it non-coincidental.

**The honest qualification, from both quarters independently.**
`binder_ctxOk2_openCong` takes *both* context currencies, because
generation four moved the quantifier and not the currency. That seam is
now the **only** thing between the congruence proofs and firing
`CtxOk2.openCong` in place of `CtxOkR.openCong`. Generation five.

#### The `.fvar` finding — a supplier request, not a residue

The inference quarter's `.fvar` clause **cannot** deliver the returned
type's `AnnotOk2`. `CtxOk2`'s leaf package carries definedness, the
context index and an `interp2` equation — **and no truthfulness**, and
nothing recovers it: `Sat2` gives *inhabitation* of context entries,
never `AnnotOk2`; the leaf link is an equation between interpretations
and `AnnotOk2` is not an `interp2` invariant (#100); and the clause
performs no run on `ty`, so no IH applies.

Routed as `CtxAnn2` at the exact granularity a **fourth component of
`CtxOk2`'s leaf package** would have, so it can move verbatim — the
`CtxOk2Open` → `CtxOk2.openS` precedent. Claimed to self-propagate:
the new head leaf's annotation is `ta.liftN 1 0`, whose `AnnotOk2` is
`AnnotOk2_liftN` of the domain's ρ-uniform `AnnotOk2`, which generation
four now supplies at every binder site.

**A methodological result worth more than the residue.** The quarter
attempted to refute `CtxAnn2` and reports it **does not go through
parametrically** — and says *why*, which is the useful part. A witness
needs a leaf annotation whose `AnnotOk2` fails while its interpretation
is *inhabited* (else `Sat2` dies and the instance is vacuous — seal
11's `⟪Empty⟫` discipline, applied unprompted). The `AnnotOk2` failures
`denote2` can actually produce sit at `app`/`proj` nodes, and there the
interpretation is `SetTheory.app`/`sfst` of junk, which the `SetTheory`
interface constrains in **neither** direction. So it is parametrically
neither provable nor refutable: *a genuine statement about the
supplier, not a theorem waiting to be found.* Recorded as prose
analysis and explicitly not mechanized — which is the right label for
it.

#### Corrections to the junction's briefs, both from workers

* The three payments the inference quarter owed are **not** "all in
  residues you already own", as I wrote. Two are (`ConstType2C`,
  `BetaCross2C`); the third is the *supplier's* `CtxOk2`. The quarter's
  own seal-7 assessment had this right and my summary of it did not.
* `BetaCross2C` turns the truthfulness transport into a
  **biconditional** — `.letE` uses it forwards, `.app` backwards, now
  that the substituted annotation is the *returned type*. The sealed
  `BetaCross2` had both directions and `BetaCross2A` dropped one; this
  buys it back rather than inventing anything.

#### The fourth collision, and the starkest

`whnfCore_package2C` was written **byte-identically** by the whnf and
defeq quarters, independently. Not merely the same name — the same
lemma, the same statement, two proofs. `DefEqRun` could not see
`Whnf`'s copy because the quarters are *siblings, not stacked*; the fix
was the import edge plus one deletion.

*Four instances now. The cost is one deletion each time; the benefit is
two independent checks of the same statement — on this occasion, two
independent proofs of it.*

### Seal 18 — generation four complete; three rulings

All four quarters landed and merged; `Interp2/Capstone2C.lean` proves
`checkStep2C_of_quarters : CheckStep2C μ V` from the routed residues
alone. **The decomposition closes at generation four**, and the
generation's own purpose is separately established: the `∀`/`λ`
congruences can discharge `CtxOk2.openCong`, which
`not_openCongLocal` proves no ρ-local claim could supply.

#### Ruling 1 — the dedupe, adjudicated

Seven collisions this campaign, three of them in this generation.
Direction settled by one criterion: **the copy that is wired into a
capstone deliverable wins; the supplier's kit wins over a local copy.**

| pair | kept | reason |
|---|---|---|
| `whnfCore_package2C` | `Whnf.lean` | byte-identical; import edge added so `DefEqRun` can see it |
| `infer_{sort,bvar,fvar}_claim2C` | `InferQ.lean` | wired into `inferStep2C_of`; `Dispatch`'s were unwired |
| `AnnotOk2.hoist_app`/`hoist_proj` | `Dispatch.lean` | supplier's kit is where the others look |
| `Sat2_cons_congr` / `Sat2.head_congr` | `Dispatch.lean` | same |

**The fifth collision was the junction's fault, not the workers'** —
both the dispatch and inference briefs listed the same three clauses,
so both quarters owned them. Worth recording: six of the seven were
convergent discovery, which is cheap and even useful; the one that was
a scoping error is the one to avoid.

**Mitigation adopted:** `Step2/Dispatch.lean`'s kit is now the
published inventory, and its module docstring carries the list. Future
briefs must point at it and say *check here before writing a helper*.

#### Ruling 2 — generation five is new-definition-plus-bridge

Accepted as the dispatch quarter states it. Sites constructing
`CtxOk2` from scratch would owe the fourth conjunct, and all are cheap
(`by simp` on `.sort` leaves) **except the tombstone witnesses**
(`CtxOk2RRefute`, `not_openCongLocal`), which construct `CtxOk2`
concretely and are **untouchable** under the refutation-preservation
practice. So generation five must introduce a new definition and
bridge, never edit `CtxOk2` in place. `CtxOk2Ann`'s stated-beside
shape is already correct, and its kit battery
(`weakenTop`/`openCong`/`openS`/`of_subset`/`fuelMono`) is mechanized.

*This is the first time the refutation-preservation practice has
constrained a future design rather than merely recorded a past one.
The cost is real and worth paying: a tombstone that can be edited to
suit a later definition is not a tombstone.*

#### Ruling 3 — proceed on the structural argument; the countermodel is queued as a **bounded** check

The question is whether `CtxOk2 → CtxOk2Ann` is derivable, i.e.
whether the fourth conjunct is genuinely independent. Two quarters
argue structurally that it is not derivable; neither has a
countermodel. Seal 11's rule says a derivation gap is not a
refutation.

**Ruled: generation five proceeds without banking the countermodel**,
for two reasons that distinguish this from seal 11.

1. **The risk profile is inverted.** At seal 11, proceeding risked
   building on a *false* statement. Here, if the conjunct turns out
   derivable, the cost is a *redundant premise* — construction sites
   owe something they could have proved. Wasteful, never unsound.
2. **The inference quarter's analysis says the countermodel is
   parametrically unbuildable**: a witness needs an annotation whose
   `AnnotOk2` fails while its interpretation is inhabited, and those
   failures sit at `app`/`proj` nodes where the interpretation is
   `SetTheory.app`/`sfst` of junk — which the `SetTheory` interface
   constrains in **neither** direction. Demanding a countermodel that
   provably cannot exist parametrically would block indefinitely.

**But the gap is not simply waved through.** The open-ended hunt is
replaced by a *decidable* question about the interface, which the
dispatch quarter's attack sketch already isolates: **is
`¬ (univ 0 ∈ˢ piR v A B)` derivable from `SetTheory`?** If it is not,
that underivability *is* the confirmation that the gap is genuine and
parametric rather than a missing proof — and it is a bounded check on
a fixed interface, not a search. Queued as such.

*Rule: when a refutation is argued to be parametrically impossible,
replace the demand for a countermodel with a bounded question about
the interface that would have to supply it.*

### Seal 19 — `Denote2InstLevels`: not settled, but seal 12's attack is closed

Reported honestly as **not settled**, with no proof or refutation
manufactured. What changed is the *shape* of the open question, and
that is worth more than a verdict would have been if forced.

**Seal 12's concrete attack is closed and should stop being treated as
a live refutation lead.**

* **`piResultIsProp` is not in the seam.** Its two call sites
  (`Kernel/Modeled.lean:723`, `Kernel/CheckerS.lean:305`) both compute
  `IndCaps` **at install, on a stored inductive's own type**. A
  subject's level instantiation never touches a stored type, so the
  `ruleK` capability a run reads is *identical* on both sides of the
  crossing. As a function it is level-sensitive
  (`piResultIsProp_flips`, mechanized) — which is presumably how it
  reached seal 12's list. **The call sites are what make it inert, and
  seal 12 looked at the function.**
* **`piResultNeverZero` is in the seam, does flip, and flips
  one-directionally.** `piResultNeverZero_flips` is a genuine
  `false → true` witness; `piResultNeverZero_map_subst` shows `true`
  can **never** become `false`. So instantiation can make the
  structure-eta/K rescue fire where it did not, and can never lose
  one — the *safe* direction for the statement as written.

**The crossing is now algebra plus two checker statements.**
`denote2_instLevels_of : SortOfEInstLevels → LamSortEInstLevels →
Denote2InstLevels`, with the `denote2` side **fully discharged** —
including `.const` and both literal clauses, via `EnvS2.acval_params`.
What remains, `InferInstLevels` and `WhnfSortInstLevels`, mention no
`denote2`, no `V`, no `EnvS2` and no valuation.

**That last point is the methodological gain.** `Denote2InstLevels`
quantifies over an `EnvS2 V env`, and the only one the tree exhibits is
`EnvS2.empty` — so **no counterexample could be built against it at
all** before the install tier lands. The primitives quantify over a
bare `Env`, so they are refutable *today*. *Factoring an unfalsifiable
statement into falsifiable ones is progress even when nothing is
proved.*

**A statement-design finding, tied to the guard result.** The obvious
primitive — "`whnf` commutes with instantiation, as an equality on
reducts" — **should not be assumed**: the rescue flip is precisely a
reason for the instantiated run to reduce *further*. No witness was
built, so it is recorded as *expect false*, not refuted.
`WhnfSortInstLevels` restricts to runs landing on a `.sort`, which the
flip cannot reach because a sort is terminal for `whnf` — the monotone
direction of the flip is what makes the narrow form immune to the
objection that condemns the general one.

The other obvious refutation is closed by design: a binder carrying a
stale sort annotation is impossible, because task #100 left
`BinderMeta` holding a `BinderInfo` and nothing else. **There is no
level inside an `Expr` that instantiation fails to reach.**

**Status of `RecRulesV2`: not cleared.** It still rests on an open
metatheorem — but one a worker can now attack or kill, which was the
whole point of putting it first. Seal 15's ordering holds.

**Trap-check, reported against interest:** all four new `Prop`s go
**vacuous** at `F = 1`, not clean, and the file says so. Per seal 11
that is worth nothing as a bill of health.

### Dispatch policy amendment — no parallel fan-out within a batch

**User ruling, effective now.** Parallel workers stay *between*
independent workstreams; **within** a proof batch, one Opus worker
proves the list **serially**. Same token cost, and the worker
accumulates recipes from proof to proof — this campaign's largest rate
lever — while eliminating what the fan-out demonstrably cost:

* **seven convergent-duplicate pairs**, two byte-identical, each
  needing a dedupe adjudication at the fold;
* one collision caused by the *junction's* own scoping error, two
  briefs listing the same three clauses;
* messages routed to workers about facts a serial worker would simply
  have had.

Against that, the fan-out's benefit was real but narrower than it
looked: the three refuted generations were each caught by *a*
consumer, and a serial worker is still a consumer. **Concurrency was
not what made the refutations happen; discharging was.**

**The pattern from generation five onward.** The junction freezes: the
statements, a **worked example** (one member of the list, proved), and
the **recipe book** — including the kit inventory, now published in
`Step2/Dispatch.lean`'s module docstring with a *check here before
writing a helper* banner and the two shapes that are false by design.
One worker proves down the list. One review, one grant.

### Seal 20 — generation five frozen; the recipe book for the serial batch

`Interp2/CtxOk2D.lean` and `Interp2/Claims2D.lean`, both compiling.
This is the **freeze**: statements, worked examples, and the book
below. One serial worker proves down the list from here.

**The statements.** `CtxOk2D := CtxOk2 ∧ CtxOk2Ann` — a new definition
with a bridge, never an edit, because the tombstone witnesses
construct `CtxOk2` concretely (ruling 2). Then `Claims2D` carries
`CtxOk2D` in **all four** claims, retiring the `CtxOkR`/`CtxOk2` seam
that `not_ctxOk2R` proved uncrossable. The ρ-hoist and the fuel slack
are untouched: **one change per generation.**

**The forced shape change:** `CtxOk2D` is indexed by `F` and `CtxOkR`
was not, so in the three claims that took the context *before*
`∀ {F}`, it moves *inside* — the shape `InferClaims2C` already had.
Mechanical, but every consumer sees it.

#### The recipe book

*The transport recipe*, worked twice in `CtxOk2D.lean`: split the
conjunction, apply both halves, reassemble. **Two traps, both of which
caught the junction writing the examples:**

1. **The `CtxOk2Ann` half often needs the `CtxOk2` half as well** —
   `CtxOk2Ann.fuelMono` takes *three* arguments, reading definedness
   out of the `CtxOk2` package to know which `tya` the leaf denotes
   to. About half the list is like this.
2. **The two halves' argument orders differ, unpredictably.** Read
   each signature; do not pattern-match on the first arrangement that
   type-checks in the other half.

*The kit inventory* is published in `Step2/Dispatch.lean`'s module
docstring — 44 entries, grouped, under a **check here before writing a
helper** banner. Seven collisions this campaign say the check is
worth it.

*The false-by-design shapes*, in the same banner and worth more than
the 44 real entries: **no `letE` binder splitter** (`AnnotOk2`'s `letE`
clause reads the body at the *value's* point, while `Sat2 (T :: Δa)`
only constrains the head to *inhabit* `T`; `hoist_zeta` is the usable
form and the one the checker needs) and **no unconditional `of_lam`**
(the λ's fibre is a genuinely per-valuation fact with no hereditary
source). *A worker warned off a wrong shape saves a refutation round.*

*The `toC`-bridge technique* (seal 16): when a generation change is a
**weakening**, land each new residue with a proof that the old shape
implies it. A weakening of an already-audited statement cannot become
false, so it **inherits the old audit** and needs no fresh refutation
hunt. Generation five is a *strengthening* of the context hypothesis,
so this does **not** apply here — and saying so is the point of having
the rule.

*The trap-checks*, in the order they earn their keep:
* **smallest fuel** — a shape asserting `denote2 … F … e = some _` as
  a **conclusion**, at a consumer-chosen `F`, is false unless `e`
  carries no `.forallE`/`.lam` node. Caught three statements.
* **and its caveat (seal 11)** — it came back *clean* for `CtxOk2R`,
  which was false anyway for a semantic reason. **A clean trap-check
  is not a clean bill of health.**
* **satisfiability** — a refutation and a satisfiability witness are
  different results and a repair needs both. Check the positive
  direction in the very case that killed the old shape
  (`denote2_two_lam`, `acvalDefnInst_noParams`).
* **vacuity** — an instance where `Sat2` is unsatisfiable proves
  nothing. Only a *currency disagreement* is decisive (seal 11's
  `⟪Empty⟫` discipline).

*The standing rules*: family-wide is the **starting assumption** for
any repair to a mutually-recursive family, and an exemption needs an
argument that survives the other repairs in the same seal (four
instances). A fired-law premise belongs to its **supplier**, never
guessed consumer-side (T5) — three `EnvS2` fields have been added this
way. A vacuous `Prop` with a good name is worse than none. Refutations
are **preserved across their own repair** by restating the refuted
shape as a standalone `def`.

### Seal 21 — generation five discharged; the serial pattern's first trial

All four sections landed in **one serial batch**: the `CtxOk2D` kit
lift (24 entries), the four quarters, `Capstone2D.lean`, and the
retirements. **2489 insertions, 0 deletions** — the `…C` lane and
every tombstone byte-identical. Build green (326 jobs), `lake test`
green, battery 90/92 with e2e 72/72 and the no-model sweep unchanged,
axioms exactly the three standard, no `sorry`.

**What generation five bought, measured rather than asserted:**

| | gen 4 | gen 5 |
|---|---|---|
| capstone residues | 17 | **15** |
| `InferInputs` fields | 9 | **6** |
| whnfCore routed residues | 4 | **3** |

* **`BetaCert2` is discharged, not re-routed** (`betaCert2D_of_claims`).
  Seal 14 predicted exactly this — *"that is seal 11's move and it is
  generation five"* — and it came out true.
* **`CtxOk2R` is gone from `InferInputs2D`**: the field whose docstring
  said `not_ctxOk2R` refutes it. Its four uses are now `fuelMono` +
  `of_subset` of a hypothesis the clause already holds.
* `binder_congr2D` builds both opened contexts with
  `openS`/`openCongC`; the `…C` version needed `denote2_erase` twice,
  `defeqR_at`, `frame_openR` and `CtxOkR.openCong`. Seven lines to two.
* `infer_forallE_claim2D` **sheds its `WScoped` premise** — the `…C`
  lane carried it only to feed `CtxOk2Open`'s `fvarsBelow`.

#### The serial pattern: the prediction held

**Proofs got monotonically easier, and every chunk compiled on the
first `lake build`.** Section 1's `of_subset` reflex made every
structural projection in sections 2–4 a one-liner, and
`fuelMono + of_subset` became the single idiom for ~25 fuel joins. The
three largest proofs were the *easiest relative to size*, because by
then the plumbing was mechanical. That is the recipe-accumulation
effect the amendment was adopted for, visible in a single batch.

Against the fan-out's ledger for the same amount of work: **zero
duplicate pairs, zero dedupe adjudications, zero misrouted messages.**

The one proof that did *not* get easier is worth naming:
`infer_app_claim2D`, the only place frame conditions had to be
re-derived by hand, because `frame_inferR` bundles them with a
`CtxOkR` the new lane does not want. **A `frame_infer2D` in the
supplier would have saved it** — that is the kit gap this batch found,
alongside `frame_appArg2D` which the worker did write.

#### Two findings recorded against interest

1. **Generation five *weakens* three claims at small fuel.** `CtxOkR`
   is fuel-free; `CtxOk2D` inherits `CtxOk2`'s emptiness at `F = 1` for
   binder-carrying subjects. So `WhnfCoreClaims2D`/`WhnfClaims2D`/
   `DefEqClaims2D` are weaker than their `…C` counterparts there.
   `InferClaims2C` has had this since seal 6 and it is harmless at the
   consumption point (depth `0`, where `CtxOk2D.nil` is free at every
   fuel) — but this is the one respect in which the generation
   weakens rather than strengthens, and it is written into
   `CtxOk2D.lean` because a consumer instantiating at a small `F` must
   know.

2. **One recipe-book check could not be performed, and was not
   faked.** The book says: check satisfiability *in the very case that
   killed the old shape*. `CtxOk2R` died of a **disagreement between
   two currencies** at the #100 empty-domain λ. With one currency
   there is no second party to disagree, so **no corresponding
   positive instance exists** — the structural answer is that the seam
   is absent, not that it is now crossable. `CtxOk2D.nonvacuous` is
   supplied instead, at depth 1 over a *satisfiable* context, and it
   had to be built fresh: the two halves' existing witnesses sit at
   different instances (`Sort 0` vs `Sort 1`) and so were not a
   witness for the conjunction.

   *Rule: a recipe-book check that cannot be performed must be
   reported as not performed. The book is a checklist, not a
   certificate.*

### The dispatch rule's evidence base — measured, both patterns

Recorded side by side, because the rule now rests on numbers rather
than argument. Comparable amounts of work: generation four (fan-out,
four concurrent workers) and generation five (serial, one worker).

| | gen 4, fan-out | gen 5, serial |
|---|---|---|
| workers | 4 concurrent | 1 |
| convergent-duplicate pairs | **7** (2 byte-identical) | **0** |
| dedupe adjudications at the fold | 7 | 0 |
| collisions caused by junction scoping error | 1 | 0 |
| mid-flight messages to workers about shared facts | 6 | 0 |
| integration breaks at the fold | 3 | 0 |
| chunks compiling on first build | not tracked | **all** |
| proof difficulty over the batch | flat | **monotonically decreasing** |
| statement changes requested | 0 | 0 |
| refuted statements caught | 0 | 0 |

**The safety property is unchanged, which is the load-bearing point.**
Across this campaign every refuted statement was caught by *a consumer
discharging it* — never by inspection, never by concurrency. A serial
worker is still a consumer. Generations four and five each caught
zero, because by then the statements were right; the three that were
wrong (`Claims2`, `Claims2A`, and `EnvS2`'s two fields) were caught by
discharge attempts under **both** dispatch patterns.

*So: concurrency bought nothing on safety and cost seven duplicates and
three integration breaks. Serial buys the recipe curve for free.*
Parallelism stays only **between** independent workstreams — this lane
and the Θ lane — where there is no shared statement to converge on.

**And the kit gap is closed.** `CtxOk2D.frame_infer2D` — `frame_inferR`
minus the erasure — is landed. The one proof in generation five that
did not get easier named its own missing supplier, which is the most
useful thing a hard proof can do.

### Seal 22 — the `RecRulesV2` map: the draft is insufficient, and mapping caught it

Mapped before freezing, on the instruction that this was the
least-mapped item on the campaign. **It was, and the draft would have
wasted a serial batch.**

**The headline: `RecRulesV2` as drafted at seal 15 omits the fired
equality entirely.** It transposes about six lines of `RecRuleLawV`'s
fifty-five — `rP ≤ mI`, the level-instantiated RHS denotation, and a
truthfulness conjunct — and carries **no** constructor lookup, no
spine arities, no level comparand, no plain/nested parameter premises,
no index pin, no telescope fits, and **no `interp2` equality between
the recursor spine and the reduct spine**. Its consumer
`IotaStep2C`/`IotaStep2D` concludes exactly that equality, and nothing
else in the tier can supply it. *A law drafted from its consumer's
signature, without reading its supplier, missed the one conjunct the
consumer exists to consume.*

**Second correction: the third conjunct is misattributed.**
`RecRuleLawV`'s truthfulness conjunct is *conditional* and lands on
the **applied reduct** `mkAppN R (xs.take rP ++ ys.drop cnP)`. The
draft's is unconditional and about the bare `R` — which is the
transpose of the install bottoms' own **input** `_hrhsKey`
(`Install/IndBottomS.lean:73/200/359`), not of the law's output.
Plausibly establishable; simply a different statement.

**Third: the draft's own docstring was wrong about the cost.** It said
"only the interpretation moves". Two conjuncts contradict that —
`TeleFitV` → `TeleFit2` is a **currency change** (`V`-valued and
kinded, not `VExpr`-indexed), and `IotaIndexPinV` has **no `interp2`
counterpart at all**, because it decomposes the constructor residual
*syntactically* (`restC = mkAppN H cargs`) while `TeleFit2`'s residual
is a bare `V` with no spine to destructure.

The draft is marked **INSUFFICIENT** in its own docstring and left
unfrozen and unconsumed, as the record of what a consumer-derived
draft misses.

#### What the map settled that is not a problem

* **The fuel slack costs nothing on identification.** `denote2_fuelMono`
  lets a consumer holding `denote2 … F₀ … = some ea'` and the law's
  `denote2 … F' … = some R` join at `max` and conclude `ea' = R` —
  precisely v1's move at `Sound/Iota.lean:174`.
* **Granularity is per rule**, not per `(φ, us)`; `rP ≤ mI` sits ahead
  of both quantifiers.
* **The indexed nested-aux machinery is establishment-only.**
  `eqUpToNames`, the const-head certificate and the `checkAnnotList`
  fixed point appear as premises of `IndBottomNestedS` and in the
  checker — **never in the law**. Only one conjunct is
  nested-specific, and its `rP`-context spelling is task #105's
  lowering already visible in v1's statement.
* **`TeleFit2` is an improvement, not just a port.**
  `AnnotOk2_redex_fits` derives the fit from the subject's `AnnotOk2`
  plus a `PosShape`, with **no runtime walk** — better than v1's
  `TeleS` route.

#### The decision, and the bounded question it hangs on

Two coherent statements exist and the draft is neither:

* **(i) the full transpose** — carry all twelve conjuncts. Cost:
  invent `IotaIndexPin2`, move the fits to `TeleFit2`, and supply an
  `AnnotOk2` spine-assembly lemma (the `TeleFitV.appN_annot`
  analogue), **which the map could not find in the tree**;
* **(ii) the minimal law plus a separate equality obligation** stated
  at the *reduct* rather than at the rule. This has a precedent in
  this codebase: v1's `EnvR` deliberately narrowed its two
  rule-derived fields to their consumption for exactly this reason
  (`Bridge/Decl.lean:36-51`).

**Not ruled now.** T5 points at (i) — a fired-law premise belongs to
its supplier — but (i) requires `IotaIndexPin2`, and the map's finding
is that the structure it decomposes *does not exist* on the `interp2`
side. So the choice reduces to one bounded question, in the shape seal
18 established for exactly this situation:

> **Can `IotaIndexPin2` be stated at all, given that `TeleFit2`'s
> residual is a bare `V` with no spine structure?**

If yes, (i). If no, (ii) is forced and the equality moves to the
reduct. Queued as the next install-tier item, ahead of the statement
freeze — and **`Denote2InstLevels` is unaffected either way**, since
the RHS-denotation conjunct survives in both options.

#### Three named gaps the map flagged, unverified

`AVExpr.bvarsBelow` and `AVExpr.instRevChain` (needed only if the
nested parameter premise is carried), and the `AnnotOk2` spine-assembly
lemma (needed by option (i)'s truthfulness conjunct). All three
grep-negative, all three flagged as such rather than asserted absent.

### Seal 23 — the bounded question answered: the pin is statable on annotated syntax

Decided against the recorded evidence first, as directed, and the
answer **corrects seal 22 rather than confirming it**.

**The squashing countermodel does apply — to any `V`-side
formulation.** Task #107's witness (`T._model := fun _ => PUnit'`,
field `{v // v = p}`, `proj_0 := fun p _ => ⟨p, rfl⟩`: iota *and* eta
provable, every install check passing, contradictory forced values)
says a bare `V` does not determine a destructor. Distinct constructor
spines interpret to equal values, so **no `V`-side fact can recover a
spine.** A pin stated about `TeleFit2`'s bare-`V` residual is not
merely hard — it is not statable. Seal 22 was right that far.

**But it does not force the minimal law, because the pin was never a
`V`-side fact in v1.** `IotaIndexPinV` decomposes `restC`
**syntactically** — `restC : VExpr`, because `TeleFitV` is
`VExpr`-indexed — and only then compares `interp` of the pieces. So
the faithful transpose is an **`AVExpr` fact**: not a workaround for
the squash, but the same construction one currency over.
`IotaIndexPin2` is now stated in `Interp2/EnvLaws2.lean`, and it
compiles. `AVExpr.mkAppN`, `interp2_mkAppN` and `denote2_mkAppN_swap`
all exist.

**Correcting seal 22:** *"`IotaIndexPinV` has no `interp2` counterpart
at all"* was wrong as written. It has none **as a fact about
`TeleFit2`'s residual**, which is what the map examined — and that
narrower claim is true and is the useful one. The general claim came
from reading the map's verdict as being about the pin rather than
about the place the map looked for it.

*Rule: when a map reports "no counterpart", ask what it searched. A
counterpart absent from one currency may be present in another that
the consumer already holds.*

#### The design tension, recorded because it will recur

`TeleFit2`'s value-level design is a genuine improvement over v1 —
`AnnotOk2_redex_fits` derives fits from the subject's `AnnotOk2` with
**no runtime walk** — and it is *precisely* that choice which removes
the syntactic residual the pin needs. Both are right; they serve
different jobs. **Fits guard memberships, where value-level is
correct; the pin guards index agreement, where syntax-level is
correct. They must not share a residual.**

#### Consequences for the ruling

The two-way choice reopens as a three-way one, and **the full
transpose is back on the table** — the obstacle seal 22 recorded as
fatal is not. Not yet ruled, because two things must land first, and
both were already owed:

1. **The residual's source.** Either an `AVExpr`-indexed fit beside
   `TeleFit2` (v1's `TeleFitV`, transposed) or the consumer's own
   decomposition through `denote2_mkAppN_swap`. The second is
   cheaper and is where the consumer's facts already live —
   `iotaRec` itself checks index agreement syntactically
   (`defEqList (residual.getAppArgs.drop ctorParams) …`).
2. **The three grep-negative gaps**, supplier-named or built before
   the freeze: `AVExpr.bvarsBelow`, `AVExpr.instRevChain` (needed
   only if the nested parameter premise is carried), and the
   `AnnotOk2` spine-assembly lemma (the `TeleFitV.appN_annot`
   analogue) that the truthfulness conjunct needs.

`Denote2InstLevels` proceeds unaffected: the RHS-denotation conjunct
survives in every option.

## The statement-currency separation (stated once, at full generality)

> **Fits guard memberships, and value-level is correct for them.
> Pins guard index agreement, and syntax-level is correct for them.
> They must not share a residual.**

This is the same separation that resolved the coherence arc, now
appearing at the install tier. It is not a workaround for either
currency's limits; it is a statement about what each kind of guard is
*for*.

* A **membership** guard says "this value inhabits that set". It
  quantifies over interpretations and never needs to know how a value
  was built — so stating it at value level is not merely adequate but
  *better*: `TeleFit2` with `AnnotOk2_redex_fits` derives fits from
  the subject's own invariant with **no runtime walk**, which v1's
  `TeleFitV`/`TeleS` route cannot.
* An **index-agreement** guard says "this spine's `i`-th argument is
  that one". It is irreducibly about *structure*, and by the #107
  squashing countermodel a bare `V` **has none** — distinct
  constructor spines interpret to equal values, so no value-side fact
  recovers a spine. v1 knew this: `IotaIndexPinV` decomposes a
  `VExpr`, not a `V`.

The failure mode the rule prevents is trying to read one guard's
residual out of the other's — which is exactly what made
`IotaIndexPin2` look unstatable at seal 22.

### Seal 24 — route 2 confirmed by supplier check; the three gaps named

**Ruling: route 2, the consumer's own decomposition. Confirmed before
committing, not assumed.** `iotaRec_inv`
(`Verify/InferLemmas.lean:823`) exposes **both** pieces the pin needs,
as conjuncts of its existing output:

* `piResidual (cvj.type.instantiateLevelParams cvj.levelParams usj)
  major.getAppArgs = some residual` — the residual, **as an `Expr`**;
* `defEqListP mode env fuel d (residual.getAppArgs.drop ctorParams)
  ((e.getAppArgs.take mI).drop rP) = .ok true` — the index guard the
  checker itself runs (`Kernel/Core.lean:1335`).

So the thread is: `residual` decomposes syntactically at `Expr` level
for free; `denote2_mkAppN_swap` pushes that to the `AVExpr`
decomposition `IotaIndexPin2` asks for; and the `defEqListP` guard
plus `DefEqClaims2D` gives the `interp2` equalities between the
annotations. **No second fit structure, no fallback needed** — and
note this is also how v1 reaches its own `restC`, which is the
denotation of the very same checker `residual`. Route 2 is not the
cheaper option so much as the *faithful* one.

**The three gaps, supplier-named:**

1. **`AVExpr.bvarsBelow` — do not build it.** Precedent:
   `EnvS2.acval_closed` deliberately avoided adding an `AVExpr.Closed`
   predicate, because *the lifting equation is what consumers actually
   rewrite with*. The nested premise's `bvarsBelow rP` should be
   spelled the same way, off `AVExpr.liftN` (`Annot/Syntax.lean:131`).
   Needed only if conjunct G is carried.
2. **`AVExpr.instRevChain` — build it**, in `Annot/Syntax.lean` beside
   `liftN`/`inst`, as the mechanical transpose of `VExpr.instRevChain`.
   Pure syntax, no `V`. Needed only if conjunct G is carried.
3. **The `AnnotOk2` spine-assembly lemma — supplier is
   `Annot/Spine2.lean`, and it is the one real piece of work.**
   `Spine2.lean` has only the *elimination* direction
   (`AnnotOk2 (mkAppN f as) → …`, lines 108 and 139); the map found no
   factory for the converse, and the converse is *harder* over
   `interp2` than over `interp`, because `AnnotOk2`'s `.app` clause
   demands a `piR` package with the codomain-kind side condition where
   `AnnotOkV`'s demands a plain `piC`. So `TeleFitV.appN_annot`
   (`AnnotOkV.lean:333`) does **not** transpose directly. Needed by
   conjunct L in the full transpose.

Gaps 1 and 2 are conditional on a conjunct that may not be carried;
gap 3 is conditional on the full transpose. **None blocks
`Denote2InstLevels`**, which proceeds next.

### Seal 25 — both `InstLevels` primitives are false; the factoring dropped a hypothesis

Settled, mechanized, in `Interp2/Step2/LevelsInst.lean`. **Both are
false as stated — and for a hygiene reason, not the deep one.**

They quantify over a **bare `Env`** with no well-formedness side
condition, and that alone kills them: a stored constant with
`levelParams = []` whose stored expression mentions a level parameter
anyway is legal input to both and **impossible for a checked
environment** (`ConstWF.allLevelParamsDefined`). `not_whnfSortInstLevels`
stores a definition whose *value* is `Sort escP`; `not_inferInstLevels`
an axiom whose *type* is — one clause earlier, same shape. The subject
carries no level, so instantiation has nothing to act on, while every
run answers the escaped sort. Joined across fuels with `knotFuelMono`,
so they hold at every `F'`.

`not_sortOfEInstLevels` shows the escape is **not an artefact of the
factoring**: it reaches the statement the delta exit consumes directly.

**The repair is free, and the finding is where the hypothesis went.**
`Denote2InstLevels` is stated over an `EnvS2 V env`, whose
`base : EnvS V env` carries `wf : EnvWF env`. **The factoring, not the
metatheorem, dropped it.** The `…W` forms re-derive the entire chain
with `m.base.wf` threaded and `denote2_instLevels_of` stands unchanged
— nothing downstream moves.

*Rule: when a statement is factored into primitives, check that every
hypothesis the original carried is still reachable in each piece. A
primitive that quantifies more widely than its parent is not a
weaker lemma, it is a different and possibly false one.*

**The satisfiability discipline was applied without being asked**, and
correctly: `escEnvT_not_wf`/`escEnvV_not_wf` show the witnesses do not
refute the *repair*, and `envWF_empty` shows the repaired hypothesis is
reachable, so the `…W` forms are not vacuous.

**Sort-terminality held, and is now a theorem.**
`whnfSortInstLevels_of_upTo`: at a `.sort` reduct the *simulation*
form (`WhnfInstLevelsUpTo` — instantiated subject and substituted
reduct share a common head normal form) collapses to the narrow one,
because a sort is its own whnf. `Levels.lean`'s informal argument,
mechanized. **`WhnfInstLevelsUpTo` is the shape a discharge should aim
at.**

#### Correcting seal 19: the suspect list was not exhaustive

Seal 19 recorded that seal 12's attack was closed — `piResultIsProp`
out of the seam, `piResultNeverZero` in it but flipping only the safe
way. **A third level-sensitive guard exists and neither seal named
it**: `whnfCore`'s **beta certificate**. It is in the seam, and unlike
the other two it needs **no environment and no inductives** —
`(fun _ : Sort p => Prop) (x : Prop)` is stuck at the parameter and
beta-reduces at `p := 0`, because `Level.isEquiv 0 p = false` while
`Level.isEquiv 0 0 = true`. Mechanized as `betaCertLevel_flips`.

*Seal 19 said "the concrete attack is closed", which was true, and I
let it read as "the seam is mapped", which was not. Closing an attack
is not enumerating a seam.*

#### The suggested order inverts for the discharge

`WhnfSortInstLevels`-first was right for **refutation** — the witness
shape transferred and the second statement fell to a one-line `rfl`
plus a copy of the same fuel join. It is **wrong for discharge**:
`InferInstLevels`' `.app` clause needs `whnf` to commute at a
`.forallE`, and its `.proj` clause at a const-headed application —
arbitrary reducts, i.e. the *general* form. **Primitive 1 cannot be
discharged from primitive 2**; it needs `WhnfInstLevelsUpTo`.

#### Reported as not done

Lifting the beta-cert flip to two `whnf` runs — which would refute the
**general** form in the *empty* environment and so survive `EnvWF` — was
not carried out. Evaluation shows the stuck redex on one side and
`Prop` on the other; **an evaluation is not a proof and was not offered
as one.** The obstacle is named: `Level.isEquiv` does not reduce
definitionally under the literal `Level.defaultFuel`, so a run-level
proof must thread three hand-proved `isEquiv` values through
`proofIrrel`'s nested runs and three `@[irreducible]` fuel peels. The
general form under `EnvWF` stays **expect false**, with a named
candidate witness and a mechanized guard.

**`Denote2InstLevels` does not close.** Seal 12's metatheorem stays
open — but its residue is now two `EnvWF`-carrying statements instead
of two bare-`Env` ones that were false.

#### A refinement to the recipe book, from its second failure

The book's *"check satisfiability in the very case that killed the old
shape"* could not be performed here either — the killing case is an
environment `ConstWF` forbids, so **no repaired instance exists at
it**. That is now twice (seal 21 was the first), and the pattern is
clear enough to state:

*When a repair works by adding a well-formedness hypothesis, the
killing case is excluded by construction and the check is structurally
unavailable. Supply instead: (a) that the witnesses do not refute the
repair, and (b) that the repaired hypothesis is reachable. Both were
supplied here.*

### Seal 26 — the seam, enumerated structurally: the beta certificate is not the last guard

Done from the **clause list, not from attacks**, which is the whole
point. Method, so it can be re-run rather than re-invented:

1. Enumerate the checker's **level-examining primitives** — the
   functions whose result can branch control flow on a `Level`.
   `Setlec/Kernel/Level.lean` closes at seven: `isEquiv`,
   `isEquivList`, `isZero`, `isNonZero`, `isNeverZero`, `leq`,
   `allParamsDefined`. Plus the two derived guards `piResultIsProp`
   and `piResultNeverZero` (`Kernel/Core.lean:127`, `:138`).
2. Find **every call site** of those in the kernel.
3. **Attribute each to its enclosing function**, and keep only those
   on the reduction/inference knot.

**Result: thirteen seam sites across nine run-path functions.** Not
one, not three.

| function | sites | primitive |
|---|---|---|
| `proofIrrel` | 786, 790 | `isEquiv _ .zero` ×2 |
| `pairEtaCert` | 856 | `isEquivList` |
| `structEtaCertWith` | 940 | `isEquivList` |
| `majorToCtor` | 1153 | **`piResultNeverZero`** |
| `iotaRec` | 1311 | `isEquivList usj` |
| `projCert` | 1371, 1376 | `isEquiv` ×2 |
| `defeqSpine` | 1694 | `isEquivList` |
| `defeqStep` | 1816, 1858 | `isEquiv` on sorts; `isEquivList` |
| `isPropType` | 1944 | `isEquiv _ .zero` |

All in `Kernel/Core.lean`; all reachable from
`whnfCore`/`whnf`/`inferTypeCore`/`isDefEqCore`.

**The enumeration cross-checks seal 19 and seal 25, and corrects the
scale of both.** Seal 19 named two guards and closed one. Seal 25
added a third and warned that closing is not enumerating. **The
structural count is nine functions** — so the honest state before this
seal was that roughly a quarter of the seam had been looked at. The
beta certificate is *one family among several*, reached through
`proofIrrel`/`isPropType`'s zero-tests.

**Two cross-checks that came out right**, which is the reason to trust
the method rather than the count:

* `piResultIsProp` appears in `Core.lean` at line 1148 **only inside a
  comment**; its live call sites are `Modeled.lean:723` and
  `CheckerS.lean:305`, both install-time. That is exactly seal 19's
  finding, re-derived from the other direction.
* `piResultNeverZero` at `Core.lean:1153` in `majorToCtor` *is* a live
  seam call — also as seal 19 had it.

**Deliberately excluded, with reasons:**

* `CheckerS.lean:771/904/918/1490/1712` and `:507`,
  `Modeled.lean:179/723` — **declaration-check and install time**, not
  the knot. A subject's level instantiation never reaches them.
* `annotateProjRec` (`Core.lean:2002`) — the **preprocessing pass**.
  Out of seam for `InferInstLevels`/`WhnfSortInstLevels`, whose
  subjects are already annotated when the run starts. Worth recording
  that it *is* level-sensitive and *would* be in seam for any statement
  about the preprocessing contract.

**Consequence for the discharge.** `WhnfInstLevelsUpTo` — the
simulation form, per seal 25's sort-terminality theorem — must survive
all nine, not just the three named so far. Six have never been
examined: the two eta certificates, `projCert`, `defeqSpine`,
`defeqStep`, and `isPropType`. Each is a `Level` equality or
zero-test whose *monotonicity direction under substitution* is the
question, exactly as `piResultNeverZero_map_subst` settled that one.

*That is the shape of the next piece of work, and it is now a finite
checklist rather than a hunt.* `Denote2InstLevels` stays open with
better residue, per the standing ledger state; the keys may consume
the `…W` forms directly without it.

*Rule: enumerate a seam from the function's own clause list and the
primitive's own call sites. An enumeration driven by attacks
terminates when imagination does.*

### Seal 28 — the seam is not uniformly one-directional, and the congruence is false

The checklist came back and **three of the freeze's predictions were
wrong**. Recording them first, because they are the finding.

**1. The congruence is FALSE, by fuel — and "check the fuel first" was
the right instruction.** `Level.isEquiv`'s `simplify` fast path does
**not** cover every `some true`: `max u v` against `max v u` is kept
apart (`combining` is not syntactically commutative) and decided by two
three-step `leq` runs. Substituting `u ↦ succ^10000 zero` leaves the
fast path closed and makes the first `leqCore` recursion peel more
`succ`s than `Level.defaultFuel` has units. `not_isEquivSubstMono`,
`not_isEquivListSubstMono`. The verdict goes to **`none`**, never to
`some false` — the third outcome the binary framing hides, exactly as
seal 27 flagged.

**2. The checklist did not collapse.** Seal 27 predicted ten sites
falling to one congruence. Actual: **4 settled, 8 settled only up to
the `none` channel, 1 not settled.** `IsEquivZeroSubstMono` is **true**
— and *not* a corollary of the congruence, for an independent reason
worth keeping: `isEquiv l .zero = some true` can only come from the
fast path, because a `leq` round trip answering `true` forces
`eval φ l = 0` at every assignment, and such a level is one `simplify`
collapses syntactically. So the hypothesis is equivalent to
`Level.isZero`. `Level.subst ks vs .zero = .zero` was never needed.

**3. The frozen table had two errors of its own.**

* **Three sites are in a *mapped* shape the freeze did not state.**
  `projCert` and `iotaRec` compare against a **stored** level read at
  the subject's level args, so instantiation maps the substitution
  over `us` — `subst ps (ws.map (subst ks vs)) r`, which is the shape
  `piResultNeverZero_map_subst` already had. Stated, refuted
  (`not_isEquivSubstMonoMapped`), replaced.
* **`defeqSpine` reads its guard without `liftFueled`** —
  `| some true => … | _ => pure false`. There `none` is
  indistinguishable from `some false`, so the guard genuinely goes
  **`true → false`** under substitution (`spineGuard_flips_to_false`),
  while the rest of the family goes `false → true`.

  **So the seam is not uniformly one-directional**, which seal 27
  asserted it would be. Twelve sites route `none` through
  `liftFueled`'s internal error; one swallows it.

#### What replaces the refuted lemmas

`isEquiv_subst_eval`, `isEquivList_subst_evalEq`,
`isEquiv_subst_eval_mapped` — the substituted pairs still **evaluate**
equal at every assignment, unconditionally, with no fuel in the
statement. *That is the monotonicity, in the only currency `isEquiv`'s
soundness speaks.* Plus `isEquiv_subst_ne_false` — the verdict never
becomes `false` — conditional on one new named residue,
`LeqFalseComplete` (`leqCore`'s `false` verdicts are correct; about
the level procedure alone). `Verify/Level.lean` proves only the `true`
direction, by design; this seam needs the other.

#### The correction that matters most for the plan

**`LeqFalseComplete` does not repair the crossing.** The crossing is
*uninstantiated success ⟹ instantiated success*, so what must be
excluded is the instantiated run doing **less** — which is precisely
what the fuel gap does. The residue only buys the verdict reading, and
what that rules out is the "diverges irreconcilably" STOP.

**An unconditional `WhnfInstLevelsUpTo` therefore needs a *budget
hypothesis* on the instantiating levels, which nothing in the tree
carries** — and `defeqSpine` needs more than a budget, because its
fallback is a *different reduction path* rather than an abort. Seal
26 set `WhnfInstLevelsUpTo` as the discharge target; that target is
**not unconditionally reachable**, and the next statement must carry a
budget or restrict the substitutions.

#### Not a soundness hole, and the exposure is bounded

**Every failure mode makes the checker do *less*, never accept more.**
A `none` becomes an internal error at twelve sites and a skipped
short-circuit at the thirteenth; neither admits a term. And the
refutation's witness needs a level of `succ`-depth ≈ 10⁴ — carriable
by an input stream, produced by no realistic one.

*Rule earned: when a guard's decision procedure is fuelled, "which way
does it flip" is the wrong question. Ask which way it flips **and**
whether it can fail to decide — and then ask, per call site, whether
the caller can tell those apart.* Twelve of thirteen here cannot tell
`none` from an error; one cannot tell it from `false`.

### Seal 29 — the consumer check: they do *not* hold the instantiated run

The redirect asked whether the actual consumers already hold the
instantiated run, so the `none` channel is excluded by a witness
rather than by a budget threaded from nowhere. **Checked, and the
answer is no for both named consumers** — which the redirect named as
the finding to report if it came out this way.

* **The delta exit.** `Delta2B`'s conclusion is
  `∃ F', F ≤ F' ∧ denote2 … F' d e' = some ea` — it **owes** the
  reduct's annotation. `delta2B_of` takes `AcvalDefnInst` and
  *produces* it; nothing hands it in.
* **The iota law's consumer.** `IotaStep2D` concludes
  `∃ F' ea', F ≤ F' ∧ denote2 … F' d e'' = some ea' ∧ …` — same shape,
  same direction.

And this is not local to those two: **`WhnfCoreClaims2D`,
`WhnfClaims2D` and `InferClaims2D` all conclude an existential
annotation for the reduct or the inferred type.** The entire
reduction-claim family is forward-producing on the annotation side.
So the dual-success discipline cannot simply be *applied* here — the
premise it would condition on is exactly what the family currently
promises to deliver.

**Why this is not the refuted (F)-species even though it rhymes.**
The (F) refutation was about predicting a *checker* run on a side
nothing ran. Here the produced object is `denote2`, which is **our**
function — but `denote2`'s binder clauses call `sortOfE`/`lamSortE`,
which *are* checker runs. So the family predicts checker runs after
all, one level down, and that is precisely why the level-substitution
crossing bites. **The rhyme is real and the redirect's instinct was
right; what is wrong is only the premise that the consumers already
hold the other side.**

#### The option this opens, and it is better than budget bookkeeping

Flip the claims to dual-success at the **claim** level rather than the
primitive level:

```
whnfCore … = .ok e' →
denote2 … F d e = some ea →
denote2 … F' d e' = some ea' →        -- premise, not conclusion
∀ ρ, Sat2 → AnnotOk2 ρ ea → interp2 ρ ea = interp2 ρ ea' ∧ …
```

Then **existence is localized and agreement is distributed**:

* *Existence* of an annotation is discharged **once, at the
  declaration level**, where a checked declaration genuinely supplies
  the runs — `EnvS2.mem_type2` is already hypothesis-position, and
  STOP 2 repaired `acval_defn` to the *uniqueness* form for exactly
  this reason. **The dual-success discipline and STOP 2's repair are
  the same move**, which is the strongest evidence that this is the
  grain of the problem rather than a workaround.
* *Agreement* — which is all the reduction claims ever needed for
  soundness — is transported per step, and needs no fuel budget,
  because both runs are given.

The cost is real and must be priced before any freeze: every consumer
that currently *reads* a produced annotation would have to obtain it
otherwise, and the inference claim's `.app` clause is the one to check
first, since it consumes the head's reduct annotation to reach the
`∀`'s domain.

**Not attempted here.** It is a sixth statement generation, it touches
all four claims, and this campaign's rule is that such a change is
re-discharged by a consumer rather than reasoned through at the
junction. It is now specified enough to be that batch's brief.

*Rule: when a discipline says "condition on the given run", check
which side the statement currently promises to deliver. A family that
produces the very premise you meant to condition on cannot adopt the
discipline without first moving the production somewhere it is given.*

### Seal 30 — pricing `.app` first changed generation six's specification

Step (1) of the authorized order was to price the `.app` clause before
freezing anything. **It did not pass as specified, and the pricing paid
for itself immediately.**

`infer_app_claim2D` consumes **two** annotations to reach the `∀`'s
domain — the head's inferred type `tfa` and the `whnf`'d `∀`'s `pa` —
and under generation six *both become premises* rather than the
claims' existential conclusions. Read at `InferQ.lean:2599–2604`:
both currently arrive from `ihi` and `ihw`.

**Neither is a declaration.** Both are intermediate terms computed
during checking. So the specification's phrase — *existence localized
to the declaration level, where checked declarations genuinely supply
the runs* — **cannot supply `.app`**, and a freeze on that wording
would have STOPped at the first clause discharged.

#### The repair keeps the discipline instead of abandoning it

Make the existence supply **run-conditioned** rather than
declaration-scoped: an annotation exists for any term the checker
**successfully ran on**. Stated as `Denote2Total`
(`Interp2/EnvLaws2.lean`):

```
∀ F d e t, inferTypeCore μ env F d e = .ok t →
  ∃ F' ea, denote2 μ m.acval env φ F' d e = some ea
```

This is **itself a dual-success statement** — it conditions on a given
run and predicts nothing — so it is legitimate in exactly the place a
budget hypothesis was not. And `.app` *does* hold what it needs: it
has `htf : inferTypeCore … = .ok tf` for the head's type, and the
`whnf` run for the `∀`.

Why it should be provable, as a shape and not a claim: a successful
`inferTypeCore` on `e` visits every binder node of `e`, so each
`sortOfE`/`lamSortE` the annotation needs is a run that already
succeeded at *some* fuel, and `knotFuelMono` lifts each to a common
maximum over the finitely many nodes.

The fuel is existential, so the smallest-fuel rule is satisfied **by
construction rather than by luck** — `denote2` on a binder cannot
answer at fuel `1`, and nothing here asks it to.

#### Status of the authorized order

* **(1) price `.app` — done, and it amended the specification.**
  Generation six proceeds, with existence supplied by `Denote2Total`
  rather than by declaration scope.
* (2) the freeze — **not yet**, and it must now be written against the
  amended supply. The three sweeps the order requires (vacuity probe,
  smallest-fuel check, tombstone sweep) apply to the frozen text when
  it exists.
* (3) the serial re-discharge — behind (2).

*Rule: price the named risk before freezing, and price it against the
specification's actual words. "Existence at the declaration level" and
"existence for anything the checker ran on" differ by exactly the two
annotations the hardest clause needs, and only writing the clause out
shows it.*

### Seal 31 — generation six frozen: dual success, and the three checks

`Interp2/Claims2E.lean`, compiling first try. **Every annotation a
claim used to *produce* is now a premise.** The claims no longer
promise that a reduct or an inferred type annotates; they say that
*when both sides annotate, the annotations agree.*

Existence moved to `Denote2Total` (seal 30), which is itself
dual-success — conditioned on a given run, predicting nothing.

**One thing was already right, and it is evidence.** `DefEqClaims2D`
needed no change: it has taken both annotations as premises since
generation four's hoist. Defeq is the one claim that never produced a
reduct, and seal 14 recorded it as *"purely relieved"* by that hoist.
**The claim that needs no change in generation six is the one that was
already dual-success** — which is the same convergence as `acval_defn`'s
uniqueness repair, arriving a third time from a third direction.

**Fuel ordering dropped.** Generations three to five carried
`F ≤ F'` because the reduct's annotation was *produced* and had to be
produced somewhere reachable. With both given, the fuels are
independent — `denote2_fuelMono` makes `denote2` functional wherever
defined, so an annotation is the same object at every fuel that
computes it. Dropping the ordering is **not** a weakening; it is
removing noise the production discipline had required.

#### The three checks, run on the frozen text

1. **Smallest fuel — satisfied by construction.** No clause asserts a
   `denote2` success as a *conclusion*; every `denote2` sits in a
   premise. The rule that refuted three statements in this campaign
   **has nothing to bite on**, and that is a structural consequence of
   dual success rather than an accident. Per seal 11 this is still not
   a clean bill of health — it is the absence of one specific hazard,
   and seal 28's fuel refutation is the standing reminder that hazards
   arrive from elsewhere.
2. **Vacuity — probed, and this is the check the generation most
   needs**, because dual success *adds* premises and a claim whose
   premises cannot all hold says nothing.
   `claims2E_premises_inhabited` exhibits an instance where every
   premise of the reduction claims holds at once. Deliberately at
   `.sort`, the one shape whose `whnfCore` and `denote2` both answer
   with no run — so the probe tests the **premise set**, not the
   checker's cooperation.
3. **Tombstones — swept.** The generation adds a file and edits none;
   `not_ctxOk2R`, `not_isEquivSubstMono` and the rest verify unchanged
   on the standard axioms, tree green at 330 jobs.

*Rule: a discipline that adds premises inverts which check matters.
Under production discipline the danger was asserting too much and the
smallest-fuel rule caught it; under dual success the danger is
asserting nothing, and the vacuity probe is the one that earns its
keep.*

### Seal 32 — generation six is a factorisation, not a localization; `Denote2Total` named the wrong side

The re-discharge came back with the generation's **intended payoff
refuted**, and the error was the junction's twice over.

#### `Denote2Total` cannot discharge `.app`, and the reason is structural

```
Denote2Total := ∀ F d e t, inferTypeCore μ env F d e = .ok t →
                  ∃ F' ea, denote2 … F' d e = some ea
```

**The conclusion is about `e`, the run's *subject*. `t` is bound and
does not occur in it.** All three annotations `.app` consumes are on
the other side: `tf` (the *result* of `infer f`), the `whnf` reduct's
`.pi`, and `tya` (the *result* of `infer a`). Seal 30 said `.app`
"holds `inferTypeCore … = .ok tf` and the `whnf` run" — true, and
irrelevant: **holding a run yields the subject's annotation, and every
term `.app` needs is a run's output.** At `.app` the subject's
annotation is already a premise of `InferClaims2E`, so the supplier
adds nothing at all there.

**And the count was wrong too.** `.app` needs **three** annotations,
not the two seal 30 named — the argument's inferred type is a third,
consumed by the defeq claim. `Denote2Total` supplies **zero** of them.

* **Two of the three are a one-word repair**, `e ↦ t`: landed as
  `Denote2TotalR`, with `inferExists2E_of_totalR` proving it discharges
  the inference existence factor outright.
* **The third is not repairable by any run-conditioned law.** The `.pi`
  annotation needs `sortOfE` at the ∀'s domain *and* its opened body;
  `inferBody`'s `.app` branch (`Kernel/Core.lean:1621-1633`) runs
  `infer f`, `whnf tf`, `infer a`, `defeq` and **no sort computation on
  either**, and the ∀ is the subject of no later run. *There is nothing
  to condition on.* It can come only from a reduction-preservation
  fact — which today exists only inside generation five's own
  induction.

#### What generation six actually is

Mechanized both directions, at all four claims (`Interp2/Dual2E.lean`):

```
Claims2D  ⟺  Claims2E  ∧  Exists2E
```

**A factorisation, not a localization.** Agreement goes to the `…2E`
claims; existence goes to three named factors (`WhnfCoreExists2E`,
`WhnfExists2E`, `InferExists2E`) — **which are still discharged only by
generation five's induction, carrying the same predictions
internally.** So seal 29's stated goal, *existence localized to where
runs are given*, did **not** happen. Any consumer needing to know a
reduct annotates is exactly where it started.

**What did survive is real and worth keeping:** the `…2E` claims are
genuinely free of the fuel-sensitive `sortOfE` prediction seal 28
refuted, and that is what makes them transportable across level
substitution. The capstone lands on **exactly generation five's fifteen
residues — none added, none retired.**

#### Three findings from the discharge

* **The free claim is not the free quarter.** `DefEqClaims2E` was free
  as predicted (a fuel split at `F' := F`, six lines). The *quarter*
  was not: `defeqStep_claim2D` consumes `ihwc : WhnfCoreClaims2D`, so
  `defEqStep2E_of` still needs `WhnfCoreExists2E`.
* **`checkStep2E_of_quarters` does not use `CheckStep2E`'s own four
  hypotheses at all** — it routes through `checkSound2D`. That is a
  smell the routed variant exists to answer, and it is recorded rather
  than hidden.
* **No clause closed vacuously**, checked: every `…2E` claim is proved
  *from* its `…2D` counterpart, so it inherits that content wherever it
  holds. The vacuity risk this generation introduced did not
  materialize.

#### `Denote2Total`'s own status, and a collision with seal 10

Not proved and not refuted; the attempt stopped when `.app` priced
negative. But its provability is doubtful for an independent reason:
it needs `lamSortE` defined at every λ node, and the checker computes
that **only under `mode.verified`, and only at the innermost binder of
a λ chain** (task #152). **Seal 10 withdrew `μ.verified` from the
claims to recover the `.noModel` lane** — so a supplier that needs it
would reintroduce exactly what that seal removed. Flagged, not
resolved.

*Rule: when a supplier is priced against a consumer, check which side
of the run each needed object sits on. "The consumer holds the run" is
not the same as "the consumer holds the annotation", and the
difference is invisible until the clause is written out.*

### Seal 33 — the statement tier is CLOSED

**Generation six is the factorisation, and that is enough.** Recorded
as what it was: *entered for localization, refuted there, but the
transportable forms were the actual need.* Seal 28's crossing demanded
claims free of the fuel-sensitive `sortOfE` prediction; the `…2E`
claims are exactly that, mechanized in both directions
(`claims2D_of_2E`, `exists2E_of_claims2D`), with no vacuous clause and
the capstone on generation five's fifteen residues unchanged.

The localization ambition failed for a reason the discharge made
**structural, not circumstantial**: the `∀`'s annotation at `.app` has
nothing to condition on, because no later run has that `∀` as its
subject. That is a fact about `inferBody`'s `.app` branch, not a gap
in anyone's effort.

**`Denote2Total` is parked, not pursued.** Its docstring carries the
tombstone: it names the run's *subject* where its consumer needs
*outputs*, and proving it would need `mode.verified` — the premise
**seal 10 deliberately withdrew** to recover the `.noModel` lane.
Doubtful provability plus a collision with a landed seal is a
do-not-chase. `Denote2TotalR`, the `e ↦ t` repair that actually
discharges the inference factor, is kept.

#### The statement tier: six generations, closed

| gen | change | fate |
|---|---|---|
| `Claims2` | the original seal | **refuted** (`inferClaims2_one_refuted`) |
| `2A` | fuel binder, grading, `F' ≥ F`, `μ.verified` | **refuted** (`whnfClaims2A_delta_refuted`) |
| `2B` | R1/R3 unified across the family | superseded |
| `2C` | the `AnnotOk2` grading hoisted above `ρ` | superseded |
| `2D` | one context currency (`CtxOk2D`) | superseded |
| `2E` | dual success | **current** |

Plus two withdrawals that were not generations: R4 (`μ.verified`,
seal 10) and the `CtxOkR` seam (seal 11).

**No generation seven without a consumer-refutation forcing it.** The
evidence base for that rule is this table: every one of the two
refutations, and every one of the four supersessions, was driven by a
*consumer attempting a discharge* — never by inspection, never by a
junction's analysis. A seventh generation reasoned out at the junction
would be the first, and this campaign has no evidence that works.

**Everything now defers to the keys**, which are the goal's critical
path.

### Seal 34 — the keys survey: the keys are not the bottleneck

The batch was briefed survey-first with my expectation stated as a
hypothesis to test. **It came back "the right instinct pointed at the
wrong object"** — which is the most useful form a wrong expectation can
take.

**Every premise of all six keys is V-free**, without exception. But
that is not the measurement that sizes the work: each key's V content
is entirely in its *conclusion*, and the conclusion is the point of a
key. The measurement that decides the batch is one level up — **the
`EnvS2`-over-`EnvS` delta is nine fields, and only two mention `V`**
(`acval_ok2`, `mem_type2`).

**The surprise worth flagging: `acval_defn`/`acval_thm` are V-free but
not free.** `denote2 : Expr → Option AVExpr` has no `V` in it, so those
two fields are **syntactic obligations about the checker's own runs**,
not semantic ones. That is where the difficulty is, and it is not
semantic difficulty. *A survey that had only asked "which conjuncts
mention `V`" would have called this tier cheap.*

#### The two blockers, both upstream of every key

* **R1 — checker-run stability under environment extension.** `denote2`
  runs `inferTypeCore`/`whnf` **in `env`**, so carrying an old
  constant's `acval_defn`/`acval_thm`/`mem_type2` into `env₂` needs a
  run-stability lemma. **It does not exist**, and v1 needs no analogue
  because `denote` touches `env` only through `find?`. Believed true, of
  a size comparable to a Step2 quarter. *The gap is invisible from the
  v1 side, which is why no earlier seal saw it.*
* **R2 — annotation existence for a checked declaration's body.**
  Needed to *choose* `acval` at defn/thm installs. This is
  `Denote2Total`'s wall again — and an `EnvS2` **field is a conclusion,
  so it cannot escape by dual success the way the claims did.**

Both bite **before the semantics, not in it**, and both bite the two
cheapest keys (`ReducePinS`, one `DefEq.sound`; `MemberKeyS`, pure
transport) identically — so there is no easy one to pick off first.

#### Ruling on R2: adopt the uniqueness form

Three exits were offered. **(a) prove it** — parked at seal 33, for
`Denote2Total`'s wall and the `mode.verified` collision with seal 10's
withdrawal. **(b) a named input-level hypothesis** — this makes the
fourteen conditional on an unverified assumption, and the campaign
takes that route only when nothing else exists. **(c) restate
`acval_defn`/`acval_thm` dual-success** — *if* the value annotates,
the annotation is the constant's leaf.

**Ruled: (c).** Three reasons, and the first is the strongest:

1. **It completes generation six into the environment tier.**
   Generation six moved the *claims* to dual success; the *fields*
   should follow. Existence is then owed in exactly one place —
   `Exists2E` — instead of two.
2. **STOP 2 already identified this and then chose otherwise.** That
   seal's own text reads: *"what the delta exit actually needs is
   uniqueness, not existence at every fuel"* — and the repair adopted
   was the existential anyway. The uniqueness form is not a new idea;
   it is the one that was already correct.
3. **The consumer check passes in the current currency.**
   `Delta2B`/`AcvalDefnInst` consume the existential, but their `…2E`
   counterparts take annotations as *premises*, which is where
   generation six put them.

**This does not reopen the statement tier.** Seal 33 closed
`Claims2*`; `EnvS2`'s fields are the environment tier, and the ruling
moves that tier into alignment with the closed one.

#### Three further requests, recorded

* **R3 — `NatOpsV2` is incomplete for its own named consumer**, and it
  is seal 22's failure mode exactly: it quantifies the seven
  `natOpNames`, while `reduceNat` accelerates all nine
  `natDivModNames` too, and the two sets are **disjoint**. A `DivModV2`
  is owed beside it. **Caught by mapping, not by discharge — twice now
  for drafted laws.**
* **R5 — `EnvS2` has no counterpart for six `EnvS` fields**
  (`rec_rules`, `caps_ok`, `nat_ops`, `div_mod`, `reduce_ops`,
  `proj_ok`). Until it is ruled whether those join `EnvS2` or stay on
  the v1 side via `base`, **`DeclBasisS`/`DeclIndS` cannot even be
  stated** in interp2 form.
* **R6 — `Nonempty` hides the produced `cval`**, which
  `EnvS2.acval_erase` must name. A Σ-valued restatement is needed, in a
  5900-line proof, and should be a deliberate decision.

#### What landed, and one piece of discipline worth copying

`Interp2/Install2.lean`: `acvalWith` and its congruences, four of the
nine delta fields' extension steps, and **`denote2_acval_congr` — the
lemma v1 never needed.** `denote` reads `cval` at any name; `denote2`
reads `acval` only where the environment stores something. Stated as an
*equation*, so the two runs are `none` together — **an install must not
silently assume an annotation exists.**

And: the batch **committed no statement drafts of the six keys**, on
the grounds that with no install-tier consumer able to attempt a
discharge, a named `Prop` would be precisely seal 20's *"vacuous `Prop`
with a good name, worse than none"*. That is the rule applied against
the batch's own apparent productivity, which is the hardest direction
to apply it in.

### Seal 35 — the (E)-fit check: three of four, and the fourth is a statement-level request

Run before building anything, as directed. **The cross-lane inventory
paid off: R1 is mostly already stated, and what is missing is small
and precise.**

`EnvExtendStable` (Θ lane, `Annot/SortCoh/Discharge.lean:1291`) covers
**the whole knot** — `whnfCore`, `whnf`, `inferTypeCore`,
`isDefEqCore`, `annotateCore` — each as *successful runs on
prefix-bound subjects are reproduced verbatim at the extended env*,
premised on `ConstsBound env₀`. And `denote2`'s internal calls are
exactly `inferTypeCore` and `whnf` (through `sortOfE`/`lamSortE`,
`Annot/Canon.lean:43-58`). **No import cycle**: `SortCoh/*` does not
reach `Interp2/*`.

**Three of `denote2`'s four needs fit directly:**

* the `.const` clause's `find?` — `FindPreserved` (same file);
* the literal spines' `natLitSupported`/`strLitSupported` guards —
  `find?`-monotone, so a `true` at `env₀` stays `true`;
* the `inferTypeCore` call inside `sortOfE`/`lamSortE` — (E)'s third
  conjunct verbatim.

**The fourth does not, and the gap is exact.** `sortOfE` *chains*:
`inferTypeCore` on `e` yields `t`, then `whnf` runs **on `t`**. (E)'s
`whnf` conjunct requires `ConstsBound env₀ t` — and its
`inferTypeCore` conjunct concludes only `inferTypeCore … = .ok x`,
**not** `ConstsBound env₀ x`. So the chain cannot be composed from the
statement as written.

**It is not missing content, only missing exposure.** (E)'s own
docstring records that its discharge runs *"with the internal motive
strengthened by output-boundness"* — the fact exists inside the proof.
**Cross-lane request, statement-level: expose it**, by strengthening
(E)'s `inferTypeCore` conjunct to also conclude `ConstsBound env₀ x`.

*That is the difference between a Step2-quarter-sized build and a
one-conjunct amendment, and it was found by reading the other lane's
statement instead of writing my own.*

#### R3 landed: `DivModV2`

Stated beside `NatOpsV2` (`Interp2/EnvLaws2.lean`) with the
disjointness recorded: `NatOpsV2` covers the **seven** `natOpNames`,
`reduceNat` accelerates the **nine** `natDivModNames`, and the sets
share nothing — so the interp2 lane had no div/mod law at all while
`DivModPinS`'s transpose has a real consumer needing one.

**Both catches of this failure mode came from mapping a consumer's
actual call, not from reading the law.** Seal 22 was the first.

One observation the statement forced: **`DivModV2` takes no `μ`.**
`NatOpsV2` needs one because its equations run through `denote2`;
`DivModClausesV` is value-level throughout, so this law is
**mode-independent** — and a mode-independent law cannot reintroduce
the `μ.verified` premise seal 10 withdrew. The unused binder was
dropped rather than silenced, which is how the observation surfaced.

#### Sequence from here

R5 and R6 join the environment-tier freeze; the freeze carries the
nine-field delta in the **uniqueness form** (seal 34), R5's six
missing fields, and R6's `cval` naming. Then the three sweeps on the
frozen text, then the keys become statable and the serial batch runs.

### Seal 36 — the environment tier frozen: `EnvS2U`, and R6 was a non-problem

`Interp2/EnvS2U.lean`. The nine-field delta in the **uniqueness form**
seal 34 ruled, as a **new structure with a bridge** rather than an edit
— seal 18's precedent, and here it also keeps the older claim lanes
green, since they consume the existential fields. `EnvS2.toU` shows
`EnvS2U` is strictly weaker: the existential field identifies any other
annotation by `denote2_fuelMono` plus functionality.

#### R6 was a non-problem, and checking cost ten minutes

The keys survey reported that `Nonempty (EnvS V env₂)` hides the
produced `cval`, so `DeclBasisS`/`DeclIndS` would need a **Σ-valued
restatement inside a 5900-line proof**. **They do not.** `Nonempty`
eliminates into `Prop`, and `Nonempty (EnvS2U V env₂)` *is* a `Prop`,
so `obtain ⟨m⟩` yields the witness and the extra fields are built
against it. Verified by elaboration before the freeze was written.

*A reported obstacle whose remedy costs a 5900-line edit is worth ten
minutes of checking before it is believed.* R6 is withdrawn.

#### R5, ruled on the survey's own discipline

**A field is added when a consumer can attempt its discharge, and not
before.**

* `proj_ok` — `ProjOkT` is syntactic and V-free; `base` carries it.
  **No counterpart is ever owed.**
* `rec_rules`, `nat_ops`, `div_mod` — interp2 consumers exist and the
  laws are drafted (`RecRulesV2`, still **INSUFFICIENT**; `NatOpsV2`;
  `DivModV2`). These three join once their laws settle.
* `caps_ok`, `reduce_ops` — **no interp2 consumer exists**;
  `reduce_ops` has one consumer in the entire tree and it is
  install-tier-internal. Adding either now is seal 20's *"vacuous
  `Prop` with a good name"*.

#### The three sweeps

1. **Smallest fuel — satisfied by construction.** No field asserts a
   `denote2` success as a *conclusion*; every `denote2` sits in a
   premise. That is the whole content of the uniqueness ruling.
2. **Vacuity — and this is the first time the check could be run as
   the recipe book writes it.** Seals 21 and 25 could not perform
   *"check satisfiability in the very case that killed the old
   shape"*, because their repairs excluded the killing case by
   construction. Here the killing case — a λ-bodied definition, which
   `acvalDefnUniform_lam_refuted` used — **is still admissible**; only
   the obligation at it changed. `acval_defn_uniq_lam_ok` shows the
   uniqueness form survives there, and for the right reason: the
   premise fails, so the obligation is *discharged* rather than
   contradicted.
3. **Tombstones — swept.** A file added, none edited; tree green at
   334 jobs, no `sorry`, `acvalDefnUniform_lam_refuted` and the rest
   verifying unchanged on the standard axioms.

*Rule: a repair that weakens an assertion to an implication can be
tested at the exact witness that refuted the original — and should be,
because that is the one case where the old and new shapes are known to
differ.*

### Seal 37 — the keys' statements, and a cross-lane hypothesis with a landing date

`Interp2/Keys2.lean`. The last statement work before the fourteen's
swap, written against `EnvS2U` and stated **enabler first**, because
the survey established the keys are not the bottleneck.

**`Denote2EnvExtend` is the enabler**: `denote2` is stable under
environment extension. It is an **equation between two runs**, not an
implication, for the same reason `denote2_acval_congr` is one — an
install must not be able to assume silently that an annotation exists
on one side and not the other.

**`InferOutputBound` is the cross-lane hypothesis, and it now has a
landing date rather than a believer.** Seal 35 asked the Θ lane to
expose a fact its own discharge already held; **that lane has landed
the amendment** — `EnvExtendStable`'s `inferTypeCore` conjunct now
also concludes `ConstsBound env₀` of the output type, a pure
strengthening with no consumers affected. So the definition here is
**scheduled for deletion, not for proof**: when the amendment reaches
master, every use is replaced by the conjunct and the `def` goes.

*Naming a cross-lane dependency instead of assuming it is what turned
a Step2-quarter-sized build into a one-conjunct amendment on someone
else's branch.*

#### The keys, stated cheapest-first

`ReducePin2`, `MemberBlock2` (the block `MemberKeyS` and
`StdAxiomKeyS` share — the survey found them to be the same
three-part per-`ψ` obligation), and `DeclStep2`. Every *premise* of
every key is already V-free, checked at each definition site, so the
hypothesis sides are reused verbatim and not restated.

**`ReducePin2` takes no `μ`** — value-level throughout, like
`DivModV2`, so it cannot reintroduce the `μ.verified` premise seal 10
withdrew. Second time an unused binder dropped rather than
underscored has surfaced that.

#### The three sweeps, and the one honest gap

1. **Smallest fuel.** Only `MemberBlock2` asserts a `denote2` success,
   and it carries the existential slack for a checked reason: **every
   standard axiom's type and every block member's type is a `∀`**, and
   `denote2_one_forallE` is `none` at fuel `1`, so a caller-chosen `F`
   would make it **false** — exactly as it made `EnvS2.acval_defn`'s
   original form false at STOP 2. Same repair, reused.
2. **Vacuity — and here is the gap, recorded rather than discovered
   later.** `ReducePin2` and `MemberBlock2` inherit premises from v1
   keys discharged today, so those are inhabited. **`DeclStep2` is
   `Nonempty (EnvS2U V env₂)`, and the only exhibited inhabitant of
   `EnvS2U` is `EnvS2U.empty`.** That is precisely the shape of every
   earlier vacuity failure in this arc — `EnvS2.empty` masked a false
   field for four seals. **Closing it by building an `EnvS2U` at a
   non-empty environment is the batch's first job.**
3. **Tombstones.** A file added, none edited; tree green at 335 jobs.

### Seal 38 — a non-empty `EnvS2U` exists; and the keys hit a missing tier

**Section 1 succeeded, and it was the right thing to do first.**
`probeEnvS2U` (`Interp2/EnvS2UNe.lean`) is an `EnvS2U` at a
**non-empty** environment — one axiom of type `.sort .zero`, named
with a `.num` so every disequality against the tree's `.str`-shaped
reserved names is one constructor comparison.

**No field failed.** `acval_defn`/`acval_thm` are vacuous *for the
right reason* — nothing of that kind stored, rather than nothing
stored at all — and `mem_type2` is **genuinely exercised**:
`probe_denote2_type` proves its premise is met at every mode, fuel and
valuation, so the field is not skipped. The four-seal masking shape is
closed.

Honest limit, recorded in the file: the stored type is sort-shaped, so
no binder numeral is computed and **`sortOfE` never runs**. The basis
block is the next probe up. *A first inhabitant that exercises one
field is not an inhabitant that exercises the structure.*

Route note: `EnvS.cons` directly, **not** `extendAxiomS` — the latter
returns `Nonempty`, and `acval_erase` must *name* `base.cval`. R6 said
`Nonempty` is fine for *consuming*; constructing is where it bites.

#### `Denote2EnvExtend` is proved — and my seal-35 fit check was wrong about the direction

`denote2_envExtend` closes over all fifteen `denote2.induct` cases.
Two findings came with it, and the first is a correction to this
junction.

**Finding 1 — the direction had already inverted, one seal before I
checked it.** `EnvExtendStable` lifts **forward**: prefix success
reproduced at the extension. But seal 34's uniqueness ruling put
`denote2` into the **premises** of `mem_type2`/`acval_defn`/
`acval_thm`, so transporting an old constant's field to `env₂` needs
**env₂-run ⇒ env₀-run** — *backward*. An equation needs both
directions, so no composition of a one-directional (E) can prove it.

**Seal 35 matched `denote2`'s calls to (E)'s conjuncts and never
checked the direction** — which the ruling I had made one seal earlier
had already inverted. `EnvExtendReflect` names the missing half.
*Rule: when a ruling changes which side of an implication a fact sits
on, every downstream fit check is invalidated, including ones already
performed.*

**Finding 2 — mechanized refutation.**
`denote2EnvExtend_lit_refuted`: the statement is **false** at
`Env.empty → natLitEnv`, at a pair where `FindPreserved` — the
supplier I named for exactly that clause — *does* hold.
`ConstsBound` grades a literal by its `| _ => True` catch-all, while
`denote2`'s literal clauses are gated on
`natLitSupported`/`strLitSupported`, and `find?`-monotonicity runs the
wrong way. `LitGuardsAgree` names the repair, and
`litGuardsAgree_probe` shows it holds at section 1's non-degenerate
extension, so it is not a diagonal-only hypothesis.

Both are **exposure** requests on the Θ lane in the `InferOutputBound`
pattern — named `def`s, not assumptions. The kernel's own
`whnf`/`infer`/`annotate` consult the same guards, so an extension
flipping one very likely breaks (E) too: the facts almost certainly
exist inside its discharge already.

#### Section 3: the keys hit a tier that does not exist

**None of the three discharged, and the reason is one thing.**
`interp2_ne_interp_erase` is now a *theorem*: `interp2 V ρ ea ≠
interp V ρ ea.erase`, at the #100 countermodel's own witness.

**So seal 34's prices were v1 prices.** "`ReducePinS` — one
`DefEq.sound`"; "`MemberKeyS` — pure transport". There *is* no
transport. **A v1 key's proof is a shape, never a plan** — and this
junction wrote both of those prices down as if it were.

* **`ReducePin2`** — blocked on a **missing whole soundness**.
  `ReducePinR`'s certificate is a *derivation*, and its only soundness
  is `DefEq.sound` over `interp`. **Over `interp2` there is no
  relation-level soundness at all**: that lane is a checker-run
  development. Landed instead: `reducePin2_witness`, the conclusion
  satisfied non-vacuously, with `reducePin2_domain_ne` guarding the
  empty-domain trap that would have made the witness worthless.
* **`MemberBlock2`** — the existence conjunct is `Denote2Total`'s wall
  (parked, seal 33). Seal 37's `∃ F' ≥ F` slack is over the *fuel*;
  the obstruction is `sortOfE` succeeding **at all**. Landed:
  `memberBlock2_probe`, the key's first genuine instance, at section
  1's `Prop`-typed axiom — which puts the wall exactly one binder
  away.
* **`DeclStep2`** — vacuity closed by section 1, transport supplied by
  section 2; the new constant's `mem_type2` *is* `MemberBlock2`, so it
  is blocked there and nowhere else.

#### The finding that outranks the batch

**The interp2 migration replaced the bridge but not the relation
tier, and the install keys live on the relation tier.** v1 has both a
relational development (`Rel.lean` + `Sound/*`) and a checker-run
bridge; interp2 has only the second. Every key's V content is proved
on v1 through relational soundness, and there is no interp2
counterpart to route through.

**This is a decision above the batch**, and it is stated here rather
than taken: build a relation-level soundness over `interp2` — which
duplicates the whole `Sound/*` tier — or **re-route the keys through
the checker-run claims**, making them conditional on the same residue
set the rest of the lane already carries.

The second is coherent with the lane as built: `checkSound2*` is
already conditional on `CheckStep2*`, so keys conditional on the same
residues add no new kind of assumption. But it is a scope ruling, not
a lemma.

### Seal 39 — scope ruling (ii) adopted; and the seam it exposes

**Ruled: the keys re-route through the checker-run claims, conditional
on the residue set.** Not merely because relational soundness over
`interp2` would be expensive — **that door is closed, not costly.**
The step-3 map already found it: relational soundness over `interp2`
needs motives over `AVExpr` that the `VExpr`-quantified relation
cannot state, and R1 refused the map that would bridge them. **Building
a second relational tier over annotated syntax would be a new
campaign, not a duplication** — which is a materially different reason
from the one I offered, and the stronger one.

(ii) is the architecture's own grain: the annotated lane is
**run-level by design**, `checkSound2*` is already conditional on
exactly these residues, and the keys inherit **no new *kind* of
assumption**.

#### The sequencing, recorded explicitly

* **Now** — the keys are conditional on the residue set, exactly as
  `checkSound2*` is.
* **At junction closure** — when the two zips, `SortSubstStable`,
  `RecRulesV2` and the remaining residues discharge, the conditionals
  discharge with them and **the fourteen over `EnvS2U` stand
  hypothesis-free.**
* **Throughout** — **v1's fourteen are untouched.** They are
  hypothesis-free today and remain so; nothing in this lane weakens
  the standing result.

#### The seam the ruling exposes, found before restating anything

Route (ii) makes the keys conditional on the claims. **The claims are
stated over `EnvS2 V env` — the *existential* fields — while the
environment tier is now `EnvS2U`, the uniqueness form.** `Loop.lean`'s
delta exits consume `m.acval_defn`/`m.acval_thm` in the existential
form at lines 53 and 61.

So route (ii) cannot be taken as the claims stand: it would make the
keys conditional on an `EnvS2`, whose existential fields are
`Denote2Total`'s wall — **the very obstruction the uniqueness ruling
escaped.** That is circular, and I created the circle at seal 36 by
freezing the environment tier without re-pointing the claims'
parameter.

**The resolution is the completion of seal 34's own ruling, not a new
one.** That seal said the uniqueness form *"completes generation six
into the environment tier"*; the claims' structure parameter is the
seam between the two tiers, and re-pointing it from `EnvS2` to
`EnvS2U` is what completing it means. It is coherent precisely because
generation six made the delta exit take the reduct's annotation as a
**premise** — so it needs only uniqueness.

**This is not a generation seven.** Seal 33 closed the statement tier
against *shape* changes forced by consumer refutation. The claims'
content is unchanged here; only the structure parameter weakens, and
it weakens to the tier that was already ruled. Recording the
distinction because "no generation seven" must not become a reason to
leave two tiers misaligned.

*Rule: a freeze that changes one tier's structure must be checked
against every statement that quantifies over it, in the same seal. I
froze `EnvS2U` at seal 36 and did not, and the circularity surfaced
two seals later when a consumer tried to use both.*

### Cross-lane: both (E) exposure requests landed

The Θ lane has landed both amendments (`f1ab6dc` on `agent/cert-tax`;
reaching master with that lane's next grant). Pure statement exposure
— no discharge triggered on their side, and nothing in this lane
changes shape.

1. **The full backward block.** On `ConstsBound`-`env₀` subjects the
   extension's runs reproduce **at `env₀`**, for all five families —
   the `env₂ → env₀` direction seal 38's Finding 1 showed the
   uniqueness-form premises need, and which no composition of the
   original forward-only (E) could supply.
2. **Literal-guard agreement**, as three conjuncts: both
   literal-support equalities plus pointwise `natOpGuard`. Demanded
   **outright** — *an extension may not flip a guard* — on the strength
   of `denote2EnvExtend_lit_refuted`.

**Three local hypotheses now have landing dates rather than
believers**, all in the `InferOutputBound` pattern:

| local `def` | file | becomes |
|---|---|---|
| `InferOutputBound` | `Keys2.lean` | (E)'s `inferTypeCore` output conjunct |
| `EnvExtendReflect` | `Denote2Extend.lean` | (E)'s backward block |
| `LitGuardsAgree` | `Denote2Extend.lean` | (E)'s guard-agreement conjuncts |

All three are **scheduled for deletion, not for proof**. They exist
only so this lane compiles in the interval.

*Three for three: every cross-lane gap this arc named as an exposure
request — a fact the other lane's discharge already held — came back
as a statement amendment rather than a build. The pattern is worth
stating as a rule: **when a needed fact is one another lane already
proves internally, ask for exposure before costing a proof.** Seal 35
turned a Step2-quarter-sized build into a one-conjunct amendment that
way; seal 38's two did the same.*

**Discipline note:** the running batch was told to keep using the
local stand-ins even where the amended (E) would be easier, and to
record where it would have helped. Swapping mid-batch would leave the
tree uncompilable until the Θ merge lands — *a dependency with a
landing date is still not a dependency you build against today.*

### Seal 40 — the re-point holds; route (ii)'s reach is not uniform

Three sections, all landed (`Claims2U.lean`, `EnvS2UPi.lean`,
`Keys2Cond.lean`), tree green at 341 jobs.

**Section 1 — the re-point went through, and the STOP measurement was
taken rather than assumed.** `m.acval_defn`/`m.acval_thm` are consumed
by **exactly four lemmas** in the whole Step2 development, and **none
is a claim discharge** — all four are lemmas *about* the residue
`AcvalDefnInst`. So no quarter needs the existential field and seal
34's ruling does complete into the claims. The four bridges are
`Iff.rfl`: at an `EnvS2` the re-pointed claim **is** the generation-six
claim as a proposition, not merely a consequence.

Casualty, recorded at its site: `acvalDefnInst_of_instLevels` does not
survive — it read *existence* out of `EnvS2.acval_defn`, and
uniqueness has none to give.

**Section 2 — the probe walks into the wall and survives.**
`piProbeEnvS2U`: a single pi-typed axiom (the basis block was not
needed). `sortOfE` genuinely runs, and the check that distinguishes it
from the first probe is that **`mem_type2`'s premise is not met at
every fuel** — `none` at 0 and at 1 (the fact that made
`EnvS2.acval_defn`'s original shape false at STOP 2), first succeeding
at 2. *The field is exercised through a checker run rather than past
one.* Still unexercised and named rather than assumed: the domain is a
sort, so a stored type whose domain is a stored *constant* needs a
second constant.

#### The finding that outranks the section: route (ii)'s reach is not uniform

The install's own runs are the bridge for `ReducePin2` —
`checkReducePin` genuinely runs `isDefEq`, and `DefEqClaims2U` cashes
it. **They are not for `MemberKeyS`/`StdAxiomKeyS`.** `MemberValR`'s
model-counterpart pin is `Expr.eqUpToNames`, a **syntactic rename
check rather than a checker verdict**, and a standard axiom has **no
value to infer at all**. Neither key has a defeq run for the claims to
cash.

So (ii) closes `ReducePin2` and the **truthfulness half** of the
member keys, and leaves their **membership half** exactly where seal
38 left it — their content is model-side, and the claims reach only
the `AnnotOk2` conjunct. *Both the recommendation and the ruling
assumed uniform reach; it is not uniform, and the non-uniformity is a
property of what the install actually runs.*

#### `CheckStep2U` — and `cval_annot` was an omission of mine

`CheckStep2U` is strictly stronger than `CheckStep2E` and has no
derivation from the current quarters. Two causes, and **one is my
error**: `EnvS2U` (seal 36) **drops `cval_annot`**, and that was an
omission in writing the freeze, not a ruling. It is half the gap.

**Restoration attempted and not landed.** Adding the field back is one
line; supplying it at `probeEnvS2U` is not — the empty environment's
recipe does not transfer, because the λ-shape obligation there is
discharged by *having no stored constants*, while the probe has one
whose valuation is `emptyT 0`. Three attempts, then reverted rather
than pursued: the finding is worth more than the fix, and the fix
belongs in a batch that can take the probes with it.

**Owed, in order:** restore `cval_annot` to `EnvS2U`, re-supply it at
both probes, then re-measure whether `CheckStep2U` becomes derivable —
since the *other* half of the gap (the two `denote2` fields) is
already measured as unneeded by any quarter.

Until then: everything conditional on `…2U` at an **arbitrary**
`EnvS2U` is conditional on more than the lane owes. At an `EnvS2` —
and so at both probes — it is free.

*Rule: when a freeze drops a field, say whether it was ruled or
merely omitted. Seal 36 listed nine fields and did not say which of
`EnvS2`'s ten it was declining; four seals later a consumer paid for
the ambiguity.*

### Seal 41 — `cval_annot` was never the gap; the real one is the structure parameter

The owed sequence came back and **refuted seal 40's diagnosis of my own
omission.** I called `cval_annot` *"half the gap"*. It is **none of
it.**

**Item 3, checked rather than reasoned: `EnvS2.cval_annot` is
projected nowhere in the tree.** Its only supplier is `EnvS2.empty`;
`Annot/Pass.lean`'s two existence theorems take `CvalAnnot` as an
*explicit hypothesis*, not off an `EnvS2`. So restoring it removes an
asymmetry between the structures and **no obstruction at all**.

**The real gap is not about fields.** The four `…Step2E_of` and all
**fifteen** residues `Capstone2E` assembles are stated
`∀ (env) (m : EnvS2 V env)` — so the quarters **cannot be applied at
an `EnvS2U` at any field set**. What is needed is an `EnvS2` at the
`EnvS2U` in hand with the **same `acval`** (the claims are stated at
`m.acval`; a different valuation is useless). `EnvS2UInImage` names
exactly that and `checkStep2U_of_2E` cashes it.

**And the bridge must not be closed.** The residue inside
`EnvS2UInImage` is the two `denote2` fields *in the direction
uniqueness cannot supply* — `Denote2Total`'s wall at stored bodies,
which is the obstruction seal 34 introduced uniqueness to escape.
`acval_defn_uniq_lam_ok` is the standing witness that uniqueness holds
precisely where existence fails. **Closing the bridge would undo the
ruling.**

**The route that does work**, and it is a statement change rather than
a proof: **re-point the four quarters to `EnvS2U`**, as `Claims2U`
re-pointed the claims — licensed by seal 40's four-lemma measurement
(no quarter reads the existential fields), touching `Claims2E.lean`
and `Capstone2E.lean`. `whnfStep2_delta_U`/`whnfStep2_delta_thm_U`
already exist, and `whnfStep2_delta` itself currently has **no
consumer**.

#### Item 1 — it does not land, and the probes were not why

The two one-liners are right; the tree fails at **one** place —
`declStep2_of_axiom`, a **third `EnvS2U` construction site** that
neither seal 40 nor the brief had in view. Two statement-level
reasons, both real:

* the fresh name's collapse-lane valuation is **unconstrained** by the
  premises (`MemberBlock2` is a membership fact; `EnvS` has no
  annotation field), and a valuation genuinely can fail `CvalAnnot` —
  `Infer` has **no `.prf` clause**, so a leaf like `.lam .prf .prf`
  has no `Annotates` derivation at all;
* the old names' `CvalAnnot` sits at the pre-install environment, and
  transporting it needs **environment weakening for
  `Annotates`/`Infer`/`DefEq`**, which exists nowhere.
  `denote2_envExtend` has no relational counterpart.

Said-and-stopped rather than edited a forbidden file. *My brief named
two construction sites; there were three. A count of construction
sites is a thing to measure, not to remember.*

#### Item 2 — both probes discharged, and the λ-shape conjunct is met

My self-diagnosis was right that it *is* the empty recipe — and wrong
about why it failed. No `simp` set reaches it because `probeEnvS` is
**the assembler applied to twenty arguments**; `probeEnvS_cval … :=
rfl` is what gets there, and the conjunct then closes.

**`piProbeEnvS_cvalAnnot` is the batch's real content, and the
λ-shape conjunct is met rather than dodged** — non-vacuity recorded as
`piProbeCval_isLam`, not asserted. Meeting it is an **inversion** of
`Infer` at a fixed λ subject, not a computation, because `Infer`'s
type slot is pinned only up to `DefEq`. The finding inside it: **I7
and I3 infer the same type** for the stored leaf, one reading the
codomain off I2 and the other off the stored type's denotation. *That
agreement is the probe's install contract surfacing on the relational
side; had they disagreed the conjunct would have been unmeetable.*

#### The probes' honest limit, restated one level up

Both lift to `EnvS2` on the nose — but the two `denote2` fields agree
there **only because neither environment stores a `defnInfo` or
`thmInfo`**. So **no axiom-only probe can exercise the residue.** The
next probe up needs a stored *definition*, and that is where
`EnvS2UInImage` stops being free.

*Rule: when a diagnosis names a cause, check the cause is consumed
anywhere before calling it the gap. `cval_annot` was absent, and
absent things look causal.*

### Seal 42 — rulings: `cval_annot` withdrawn, the quarters' re-point authorized

**(a) Item 1 is WITHDRAWN, not retried.** The absent-things-look-causal
rule cuts sharper than my report asked. `cval_annot` is **projected
nowhere**, supplied only by `EnvS2.empty`, and the consumers that want
its content take `CvalAnnot` as an **explicit hypothesis**
(`Annot/Pass.lean`) — the textbook *vacuous field with a good name*,
which this campaign's own no-unconsumed-fields discipline says not to
carry.

So: **do not restore it at `EnvS2U`**, and **`EnvS2`'s own copy is
flagged for deletion** at the next cleanup seal, with `Pass.lean`'s
hypothesis-style consumers noted as the correct pattern.

*This dissolves the third construction site's obstructions entirely —
they were the cost of supplying a field nothing reads.* The seal-40
"restoration owed" line is void.

**Both third-site findings are ledgered as knowledge**, since they are
true regardless and were paid for:

* **A fresh name's collapse-lane valuation genuinely can escape
  `CvalAnnot`.** `Infer` has **no `.prf` clause**
  (`Annot/Validity.lean`'s `not_infer_prf`), so a leaf like
  `.lam .prf .prf` has no `Annotates` derivation at all. Any future
  field asserting annotation of an *arbitrary* stored valuation is
  false for this reason.
* **The relational environment-weakening family is absent** —
  `Annotates`/`Infer`/`DefEq` under cons-extension. `denote2_envExtend`
  has no relational counterpart. **Known-absent with a named route**: a
  bounded structural induction with `find?`-monotone premises, the
  shape (E) already has on the run side. **Built on demand only.**

**(b) The four quarters' re-point to `EnvS2U` is authorized** — the
same license as `Claims2U`'s: seal 40's four-lemma measurement showed
no quarter reads the existential fields. Statement changes in
`Claims2E.lean` and `Capstone2E.lean`, not proofs.

**The `EnvS2UInImage` bridge stays OPEN**, and its docstring now says
why: closing it would undo seal 34, because its residue is
`Denote2Total`'s wall in the direction uniqueness cannot supply. The
docstring also records the limit — both probes lift *only* because
neither stores a `defnInfo`, so **no axiom-only probe exercises the
residue.**

**(c) Ledger line: I7 and I3 infer the same type** for the pi-probe's
stored leaf — one reading the codomain off I2, the other off the
stored type's denotation. *The install contract surfacing on the
relational side; had they disagreed, the λ-shape conjunct would have
been unmeetable.*

**(d) Next probe: the stored-definition probe** — the one that
actually exercises `EnvS2UInImage`'s residue, per the limit above.
Then the conditional keys land on the re-pointed quarters.

*Rule: a field nobody projects is not a gap to fill but a field to
delete — and the obstructions to supplying it are not findings about
the design, only invoices for the mistake.*

### Seal 43 — both definition probes lift; the residue is characterised exactly

**Item 2 is the batch, and its headline is a biconditional**
(`Interp2/EnvS2UDef.lean`):

```
EnvS2UInImage V m ↔ ∀ μ φ, CvalAnnot μ env m.base.cval φ ∧
                            Denote2Bodies V m μ φ
```

Both directions proved. `Denote2Bodies` says only that **some** fuel
annotates each stored body. So **uniqueness supplies the
identification half of the existential field for free**, and the
entire residue is `Denote2Total` at the stored bodies — *and nothing
else*.

That is the mechanized form of "uniqueness holds precisely where
existence fails", which seal 34 predicted and nothing had exhibited.
**And it relocates the parting**: it is **not** at `defnInfo`, and
**not** at λ-bodied definitions.

* `defProbe` (`def _ : Sort 1 := Sort 0`) — binder-free value, so
  `acval_defn`'s premise is met at **every** fuel and the leaf is
  *forced*, not chosen. **Lifts.**
* `lamDef` (`def _ : ∀ _ : Sort 0, Sort 1 := fun _ => Sort 0`) — the
  λ-bodied case, where `denote2_one_lam` (the fact that refuted the
  original field) makes the premise unmeetable below fuel `2`, and the
  annotation exists only through a `lamSortE` run. `CvalAnnot`'s
  λ-shape conjunct is non-vacuous here, and seal 42's I7/I3 agreement
  repeats. **Lifts too.**

**Honest limit, recorded in the file rather than smoothed over.**
`denote2` differs from `denote` only at the two binder clauses, and
`EnvS.defn_eq` already forces every stored body to `denote`. So a
separating witness needs a stored body whose binder sorts **no** fuel
computes — and every well-typed body computes them. Not exhibited, and
the file says so instead of claiming the residue closed.

*That is a strong hint about the endgame: if every well-typed stored
body computes its binder sorts, `Denote2Bodies` may follow from
`EnvS`'s own fields rather than needing `Denote2Total`.* Named as the
place to look; not claimed.

**A nuance worth keeping straight.** `CvalAnnot` appears in the
biconditional — yet seal 42 withdrew `cval_annot` as a field nothing
projects. Both are right: **the field was vacuous, the predicate is
load-bearing.** Withdrawing a field is not withdrawing its proposition.

#### Item 1 — stopped, and my authorization was wrong twice

I authorized the quarters' re-point as *"statement changes in two
files, not proofs."* **Both halves were wrong**, and the worker
measured rather than argued:

* **An import cycle.** `EnvS2U.lean` imports `Step2/Whnf.lean` →
  `Dual2E.lean` → `Claims2E.lean`. So **`EnvS2U` sits strictly
  downstream of the four quarters it would be re-pointed into**, and
  the import is rejected outright.
* **It does not stop at two files.** 528 occurrences of `EnvS2 V`
  across 30 files under `Interp2/`; the four `…Step2E_of` proofs and
  all fifteen residues are `∀ (m : EnvS2 V env)`, so at every
  application site it is a **proof** change.

Seal 41 was right that the gap is the structure parameter; what is new
is that **the fix cannot be localized.** The unblocking move is a file
split: `EnvS2U`'s *structure* needs only `Annot/EnvS2`'s cone, and its
`Step2/Whnf` import is used solely by `EnvS2.toU` and the
`acval_defn_uniq_lam_ok` probe — both of which can live downstream in
a second file. That is an edit to a forbidden file, so the worker
said-and-stopped.

*Rule: before authorizing a re-point as "a statement change", count
the occurrences and check the import direction. I did neither, and the
authorization named the wrong two files.*

#### Item 3 — the keys already consumed `…2U`

There was no bridge to remove: `reducePin2_of_claims`,
`memberBlock2_of_stored` and `declStep2_of_axiom` have taken the `…2U`
claims since seal 40. What was missing was the **supplier**, and the
simplification found is that **the keys never needed
`checkStep2U_of_2E`'s `∀ env, ∀ m` hypothesis** — each key is stated
at a single `m`, so the *pointwise* `EnvS2UInImage` suffices
(`claims2U_of_2E`, `claims2U_of_bodies`).

And `claims2U_lamDef` inhabits the keys' claim premises at an
environment that **stores a definition** — before item 2, those
premises were only ever inhabited where `acval_defn` says nothing.

### Seal 44 — the endgame lead: STOP with the gap; and the file split lands

**Directive (2) first, and it does not close.** The lead was: if
`denote2` differs from `denote` only at the binder clauses, and
`EnvS.defn_eq` already forces every stored body to `denote`, then
`Denote2Bodies` might follow from `EnvS`'s own fields — dissolving the
entire residue.

**Pre-build supplier check, against the front door's actual facts:**

`EnvS`'s only well-formedness field is `wf : EnvWF env`, and
`ConstWF` (`Verify/EnvWF.lean:35`) is **purely syntactic** —
`hasFvar`, `allLevelParamsDefined`, `constsResolve`,
`looseBVarsBounded`, and the same four for a definition's value and a
recursor's rule right-hand sides. **No `inferTypeCore`, no
`ensureSort`, no `whnf`. No `EnvS` field records that any run
succeeded.**

So the front door *had* the fact — it ran the checker — and **`EnvS`
does not carry it.** `Denote2Bodies` does **not** follow from `EnvS`'s
fields, and the residue does not dissolve. STOP with the gap, as
directed.

**But the relocation is favourable, and that is the useful half.**
`Denote2Bodies` quantifies over **stored** bodies only — each one the
front door actually checked — where `Denote2Total` (parked, seal 33)
quantified over arbitrary terms and hit a wall at `.app`'s `∀`, which
**no later run has as its subject**. Stored bodies have runs; that `∀`
had none. So the residue is *establishable at install*, and is a
strictly smaller obligation than the one it replaced.

*Rule: "the front door established it" is not the same as "the
invariant records it". Check which fields exist, not which facts were
once true.*

#### The file split, landed

`Annot/EnvS2U.lean` now holds the **structure**; `Interp2/EnvS2U.lean`
keeps `EnvS2.toU` and the `acval_defn_uniq_lam_ok` probe, the only two
things that wanted `Step2/Whnf`'s cone.

This dissolves seal 43's blocker: `EnvS2U` was **strictly downstream
of the four quarters** it must be re-pointed into (`EnvS2U` →
`Step2/Whnf` → `Dual2E` → `Claims2E`, rejected outright). Confirmed
unblocked by elaborating `Claims2E` and `Annot/EnvS2U` together and
naming `EnvS2U` — it resolves.

Gates: build green at **343 jobs**, warning-free; battery **90/92**
with e2e 72/72, split driver 11/11, mode flags 9/9 and the no-model
sweep unchanged — **the other lane's cone is intact.**

The 528-occurrence re-point is now *enabled* but not *done*: it
remains a proof change at every application site, and that is the next
batch, with the pointwise-bridge simplification riding on it either
way.

### Seal 45 — the re-point scoped, and `Denote2Bodies`' supplier stated

**(a) The 528 figure is not the batch.** Measured by file:

| live lane | sites | | tombstoned | sites |
|---|---|---|---|---|
| `Step2/DefEqRun` | 141 | | `Capstone2C/2D`, `Capstone` | 42 |
| `Step2/Whnf` | 97 | | `Claims2A/2C/2D` | 30 |
| `Step2/InferQ` | 83 | | | |
| `Capstone2E` | 29 | | | |
| `Dual2E`, `Claims2E` | 27 | | | |
| `Dispatch`, `Levels` | 19 | | | |

**The superseded generations need nothing** — they are tombstones and
must stay as they are. The live scope is ≈396, and **321 of it is the
three quarter files**.

**Judged uniform enough for a serial worker.** The per-site edit is a
binder type change, and seal 40's measurement is the licence: no
quarter reads `acval_defn`/`acval_thm`, whose only four consumers are
lemmas *about* the residue. The four exceptions are known by name and
go in the brief.

**(b) `Denote2Bodies`' supplier, stated** (`EnvS2UDef.lean`):

* `Denote2BodyOfRun` — *a body the checker successfully inferred a
  type for has an annotation at some fuel*. **Run-conditioned, so it
  predicts nothing** — the discipline seal 33 parked `Denote2Total`
  for failing.
* `Denote2BodiesStep` — the fold's step: `Denote2Bodies` at the
  extension from the prefix's, the extension's transport
  (`Denote2EnvExtend`), and the front-door fact at the one new body.

**Why this is not seal 30's error repeated.** `Denote2Total` named the
run's **subject** where its consumer needed **outputs**.
`Denote2BodyOfRun` names the body — which *is* the run's subject — and
its consumer is `Denote2Bodies`, which asks about stored bodies. The
`.const`-side twin of `Denote2TotalR`, not a re-run of the mistake.

*And the relocation is what makes it plausible at all: the residue
moved from an object **no later run has as its subject** to objects
**every one of which the front door demonstrably ran on.***

Stated, not proved: if the front-door run's existence is not visible
where `DeclStep2` can see it, **that is an exposure request** on
whatever holds it — the pattern that has gone three for three this arc
— and not a rebuild.

### Seal 46 — the live lane is re-pointed; the scope deviation is ACCEPTED

516 sites, **515 mechanical**. Build green at 343 jobs, `lake test`
clean, battery **90/92** with e2e 72/72 and the no-model sweep
unchanged.

**Seal 40's measurement was confirmed exactly: the four predicted
exceptions were the only ones. There is no fifth.** A four-lemma count
taken six seals earlier predicted a 516-site mechanical change to the
lemma. *That is what a measurement is worth compared to an
impression.*

| exception | disposition |
|---|---|
| `whnfStep2_delta`, `whnfStep2_delta_thm` | kept at `EnvS2` (read existence) |
| `acvalDefnInst_noParams` | kept at `EnvS2` — conclusion spelled out, so it still typechecks |
| `acvalDefnInst_of_instLevels` | **deleted** — both hypothesis and conclusion moved to `EnvS2U`, so it cannot be *stated*, exactly as seal 40 predicted |

All four are consumerless; nothing downstream noticed.

#### The finding: my brief was wrong, and the tombstones could not stay behind

I wrote that the superseded generations *"need nothing"*. **False**,
for two independent reasons, either alone fatal:

1. `Claims2A/2C/2D` **apply `CtxOk2`/`CtxOk2D` to their own `EnvS2`
   binder**, and those predicates live in the *live* files that moved.
   The `Coe (EnvS2 …) (EnvS2U …)` escape was **tested, not assumed**:
   it does not fire, because Lean will not insert a coercion against a
   metavariable-headed expected type.
2. All four `…Step2E_of` **factor through generation five at the same
   `m`**, and `Capstone2E` derives everything from `checkSound2D`.
   Given an arbitrary `EnvS2U` there is no `EnvS2` to hand them — that
   map is exactly `EnvS2UInImage`, which stays open by ruling.

My scope table also **under-counted by 15 live sites** across five
files I did not list.

**Ruled: the deviation is accepted.** The tombstone-preservation
practice exists to stop a refutation being *weakened*; widening its
quantifier does the **opposite**. Verified at the junction rather than
taken on report: `not_ctxOk2R` now reads
`∀ (m : EnvS2U V env) μ φ, ¬ CtxOk2R m μ φ` — and since `EnvS2U` is
the weaker structure there are *more* of them, so the statement is
**strictly stronger**, with the old form recovered through `toU`. Same
for `whnfClaims2A_delta_refuted`. Both verify on the standard axioms.

*Rule: a tombstone may be strengthened, never weakened. Widening the
class it quantifies over is strengthening — check the direction before
invoking the practice.*

#### The bridge residue drops out; the bridge does not

`checkStep2U_of_2E` no longer takes `EnvS2UInImage`, and the keys
carry no pointwise residue. **`EnvS2UInImage`, `envS2UInImage_iff` and
both probes stand untouched — seal 34 is intact.**

**Two riders, both recorded in-tree and both against interest:**

* **The obligation moved; it did not vanish.** The fifteen residues
  are now demanded at *every* `EnvS2U` — a strictly larger class than
  the `toU`-image — so they became harder to discharge by exactly the
  amount the claims seam became easier. **Seal 32's finding again: a
  factorisation, not a localization.** None of the fifteen is
  discharged in this tree today.
* **`Claims2U`'s copies are now degenerate** — `…Claims2U` and
  `…Claims2E` are the same definitions twice, so the `Iff.rfl` bridges
  are `rfl` between identical texts and the two `checkStep2*_of_*`
  are the identity. Flagged by the worker under my own rule about
  `rfl`-provable Props. **Ruled: keep as drift checks now, retire at
  the cleanup seal** alongside `EnvS2.cval_annot`.

### Seal 47 — the keys' stopping points; the supplier is NOT VISIBLE; my step lemma amended

Both items landed, gates unchanged: build 343 jobs warning-free,
`lake test` clean, battery **90/92** with e2e 72/72 and the no-model
sweep unchanged.

#### Item 1 — four premises retired, each key's stop named

`constsBound_of_constsResolve` is the find: **`ConstsBound` is
`Expr.constsResolve` read as a proposition**, and *weaker* at the
literal and projection clauses — so `ConstWF`'s existing conjunct
implies it, and `declStep2_of_axiom` drops its boundedness premise
entirely. `memberBlock2_of_stored` drops three more, all read off
`m.base.wf`.

| key | stops at |
|---|---|
| `reducePin2_of_checkStep` | two `Denote2Total` premises, plus two env facts `EnvWF` does not carry and two needing `ReducePinR`'s inversion |
| `memberBlock2_of_checkStep` | `Denote2Total` at the stored type, **and `hrun` — item 2's gap already biting in this tree** |
| `declStep2_of_axiom` | `Denote2EnvExtend`, `MemberBlock2` at the new axiom, and the collapse-lane install |

#### Item 2 — verdict: **NOT VISIBLE**, and the diagnosis is exact

* **The fact is true.** `checkDefnVal` (`Kernel/Checker.lean:372`) runs
  `inferType` on the **annotated** value — the term that gets stored —
  at the **pre-install** environment. Seals 44/45 hold as stated.
* **It is held in a named binder**: `valueFrontR_of`
  (`Bridge/Decl.lean:134`) takes `hvt : inferTypeCore … = .ok vtype`
  explicitly.
* **It is dropped at exactly one place.** `ValueFrontR`
  (`SetR/Decl.lean:152`) records five syntactic conjuncts and one
  relational front door; its only checker call is `annotateCore`.
  Grep for `inferTypeCore` across `Decl.lean` and all of `Install/`
  returns **nothing**.
* **`annotateCore` is not a substitute** — checked, not assumed: since
  #100 stage 6 its binder clauses are purely structural, computing no
  sort and running no `infer`. *Restating the supplier over the one
  exposed run would trade a true premise for a useless one.*

**Exposure request** (the pattern, now four for four): on
`ValueFrontR`, `(∃ vtype, inferTypeCore μ env F 0 value' = .ok vtype)`,
supplied at `valueFrontR_of` by `⟨vtype, hvt⟩` — **a pair, not a
proof**. Twin on `ConstantValR` for the type side. Cost is positional
destructuring at six sites, all in files this lane may not edit.

**Two things the exposure would still not close**, both reported
against interest:

1. **My `Denote2BodiesStep` was unprovable as stated** — exposure or
   not. Its premise spoke at the **prefix** and its conclusion at the
   **extension**, and nothing bridged them. **Amended here** to carry
   `Denote2EnvExtend` as an explicit premise. Naming the transport
   also names its cost: it is undischarged, and its literal clause is
   outright **refuted**.

   *Rule: a step lemma whose premise and conclusion live at different
   environments must carry the transport, or it is a wish with a
   signature.*
2. **`memberBlock2_of_stored`'s `hrun` is stronger than the front
   door.** It demands `inferTypeCore … = .ok (.sort u)` — literally a
   sort — while `checkConstantVal` only `ensureSort`s, i.e. *whnfs*,
   the output. **The exposed conjunct would not apply on the nose**,
   and the key would need the claim at a non-sort inferred type, where
   its second dual-success premise stops being free.

*That second point is the more useful one: an exposure request that
would land and still not close its consumer is worth knowing about
before it is filed.*

### Seal 48 — the pre-landing verification comes back NEGATIVE

Directive (1) was to reshape the exposure to the front door's actual
output chain and **re-verify the consumer applies on the nose before
landing anything.** Done, and **it does not apply.** Nothing was
landed.

**The front door's actual chain** (`Kernel/CheckerBase.lean:88-89`):

```
let stype ← ops.inferType env 0 type
let _u   ← ops.ensureSort env 0 stype
```

So what `checkConstantVal` genuinely produces is **two facts**:

* `inferTypeCore μ env F 0 type = .ok stype`, and
* `ensureSortCore μ env F 0 stype = .ok u`

— **not** `inferTypeCore … = .ok (.sort u)`. `ensureSort` *whnfs* its
input; the inferred type need not **be** a sort, only reduce to one.

**`memberBlock2_of_stored`'s `hrun` demands the fused literal**
(`Keys2Cond.lean:380`). Against the honest chain it would be handed
`stype` and a separate reduction, and **the consumer does not apply.**
So the exposure alone was never going to close it — which is precisely
what seal 47 flagged and what this check was ordered to confirm before
anything was filed.

**Both sides must be reshaped, not just the supplier.** And the
consumer's reshape has a cost worth naming in advance: with the chain
in place, `memberBlock2_of_stored` needs **`WhnfClaims2U` alongside
`InferClaims2U`** — because reaching the sort now goes through a
`whnf` step the fused form had hidden inside its own hypothesis. *A
premise that fuses two runs hides the second claim its discharge will
need.*

**Design, to be built and verified together:**

* **Exposure**, on `ConstantValR` (`SetR/Decl.lean:132`):
  `(∃ stype u, inferTypeCore μ env F 0 type' = .ok stype ∧
  ensureSortCore μ env F 0 stype = .ok u)`, supplied at
  `constantValR_of` from the facts `checkConstantVal_inv` already
  yields — **a pair of pairs, not a proof.** The value-side twin on
  `ValueFrontR` for `Denote2BodyOfRun`.
* **Consumer**, `memberBlock2_of_stored`: take the chain, and take
  both claims.

**Directive (2) noted and adopted**: `Bridge/Decl.lean` and
`SetR/Decl.lean` are this lane's surface, not the Θ worker's (whose
active tree is `SortCoh/ThetaRel`). This is an ordinary edit under the
battery-confirms-the-other-cone protocol, **not** a cross-lane
request — so the pattern's fourth instance is filed by the lane that
needs it.

**Directive (3) noted**: `Denote2EnvExtend` stays frozen-on-Θ until
their sorry-free prefix lands.

*Rule: verify the consumer against the reshaped supplier before
filing, not after. The check cost one reading of `CheckerBase.lean`
and would have cost a landed-and-useless conjunct.*

### Seal 49 — the exposure lands; the gate is negative again; seal 48's predicted cost was wrong

Build green at 343 jobs, `lake test` clean, battery **90/92** with e2e
72/72 and the no-model sweep unchanged — so the other lane's cone
through `SetR/Decl.lean` and `Bridge/Decl.lean` is intact.

**Item 1 — landed, mechanical at every site.** `ConstantValR` gains the
chain, `ValueFrontR` the single-run twin, supplied at `Bridge/Decl.lean`
as `⟨stype, u, hst, hsort⟩` and `⟨vtype, hvt⟩` — **pairs, not proofs**,
exactly as seal 47 measured. *My site list was short again*: six
`DivModPin` sites, not four, plus three in `Bridge/Decl.lean` I did not
name.

**Item 2 — seal 48's predicted cost was wrong, and the worker probed
rather than believing me.** I predicted the reshaped consumer would
need **`WhnfClaims2U` alongside `InferClaims2U`**. It needs neither:
`MemberBlock2` asks only for the *subject's* `AnnotOk2`, and **nothing
in the route turns on what the inferred type is or reduces to.** The
`ensureSort` half of the chain I designed is **consumed nowhere.**

What the fused literal sort was *actually* doing was supplying the
claim's **other dual-success premise** for free, via `denote2_sort`. At
an arbitrary `stype` that annotation must come from somewhere — and
that somewhere is `InferExists2E`, not a whnf claim.

*Rule: when a fused premise is split, ask what each half was buying.
I assumed the sort was buying its own reduction; it was buying an
**annotation**.*

**Item 3 — the gate is negative, with two leftovers rather than one.**
`memberBlock2_of_constantValR` compiles and exhibits the composition,
so the reading is precise:

* **`hrun` applies on the nose** — a real closure. The old fused
  premise was un-dischargeable **in principle**, because
  `checkConstantVal` never produces `.ok (.sort u)`.
* **Leftover 1 — `EnvExtendStable`, which I did not anticipate.**
  `ConstantValR` says the name is **fresh at `env₀`**; the key needs
  `c ∈ env.consts` at `env`. **The composition crosses an
  environment.** It is the *forward* direction, so Θ's
  `EnvExtendStable` is the right shape, and its `ConstsBound` side
  condition is free from `ConstantValR`'s own `constsResolve` via
  `constsBound_of_constsResolve`.

  **This is seal 47's own prefix/extension rule biting a second time**
  — *"a step lemma whose premise and conclusion live at different
  environments must carry the transport"* — and I wrote that rule two
  seals ago and still designed a composition that ignored it.
* **Leftover 2 — `InferExists2E`**, beyond the reach of *any*
  checker-side exposure: **no run the front door makes says the
  inferred type annotates.**

**Recorded stall, honest under D6:** `ValueFrontR`'s new twin has **no
consumer in this tree** — it was filed for `Denote2BodyOfRun`, which
lives in another lane. It is supplied from a real binder and is not
`rfl`-provable, but **no discharge has exercised its quantifiers.**

*The exposure pattern's fourth instance therefore lands with a
qualification the first three did not have: it closed the premise it
was filed for, and the consumer still does not close.* That is not a
failure of the pattern — it is the difference between "the supplier
was missing" and "the supplier was one of several missing things",
which only writing the composition reveals.

### Seal 50 — perspective: the two leftovers ARE the priced residue set

A reframing that changes what seal 49's negative gate means, recorded
because the raw reading is misleading.

**Neither leftover is a new obstruction.** Both are the residue set
that scope ruling (ii) — seal 39 — already priced:

* **`InferExists2E`** is a **generation-six factorization residue**
  (seal 32), dischargeable through the claims exactly as the
  conditional-keys design intends. The key composition consuming it
  **conditionally is the adopted sequencing, not a shortfall.**
* **`EnvExtendStable`** is the **known frozen-on-Θ transport**,
  unblocking when that lane's sorry-free prefix lands.

So seal 49's gate is negative *against an unconditional reading* and
**exactly on target against the conditional one**, which is the one
ruling (ii) adopted. The milestone was never "the keys close
outright"; it is **"the keys close on precisely these named
residues"**, with the unconditional forms following at junction
closure — the sequencing recorded at seal 39 and unchanged since:

> conditional now; unconditional at junction closure when the zips,
> `SortSubstStable`, `RecRulesV2` and the remaining residues discharge;
> **v1's fourteen untouched and hypothesis-free throughout.**

*Rule: a gate's verdict is only meaningful against the reading its
ruling adopted. "Does not close" and "does not close unconditionally"
are different results, and the second is what a conditional design
predicts.*

**And `ValueFrontR`'s twin is a frozen supply, not a vacuous `Prop`.**
The distinction is the one this campaign's own slot-versus-hypothesis
rule draws: it has a **named future consumer** (`Denote2BodyOfRun`),
is supplied from a real binder at `valueFrontR_of`, and is not
`rfl`-provable. The D6 flag stands as an honest note that no discharge
has exercised its quantifiers yet — *which is a smaller claim than
"unconsumed field", and the two must not be conflated.*

### Seal 51 — the milestone: the keys bundled, and all fourteen swaps stated

Build green at **345 jobs**, `lake test` 133/133, battery **90/92**
with e2e 72/72 and the no-model sweep unchanged.

**v1's fourteen are byte-identical** — `git diff` on `Main.lean` is
**empty**, verified at the junction, and every one of them still
verifies on exactly the three standard axioms. The swaps read
`EnvS2U.base`; they never re-prove.

**Item 1 — `Interp2/Keys2Bundle.lean`.** `installKeys2_of_residues`
concludes `ReducePin2 ∧ MemberBlock2 ∧ DeclStep2` from **one**
structure whose every field carries provenance and a discharge date:
`CheckStep2E` shared, then 7 + 5 + 9 per-key residues.
**Mode-generic** — no `μ.verified` anywhere.

**Item 2 — `Main2.lean`. All fourteen go**, including the four
`_input_` forms via new `foldlM_no_Empty_R2/RC2/RS2` and a re-run SP
induction. Five carry a **stronger carrier** than their v1 twins.

#### The honest reading, which the theorem count would otherwise obscure

The worker flagged this rather than letting fourteen green theorems
speak for themselves, and it is the part that matters:

**`CheckStep2E`, `EnvExtendStable`, `Denote2EnvExtend` and
`DeclStep2All` are all uninhabited, so no item-2 statement is usable
today.** `EnvExtendStable` in particular has **no supplier anywhere in
the tree** — grep-confirmed. That is exactly what seal 39's
*"conditional now, unconditional at junction closure"* looks like
written down.

What **is** inhabited, from real runs: `ConstantValR`
(`constantValR_of`, a conjunct of four of `DeclR`'s six kinds),
`ReduceOpFits2`, `EnvS2UOk V Env.empty`, and the syntactic fields.
**The fold's base case is inhabited for real**, so it does not start
vacuous.

**Three stalls recorded rather than smoothed:**

1. **Item 2's condition is not literally item 1's hypothesis set, and
   could not be.** Item 1's `MemberBlock2` lands at a constant already
   in the *prefix*; `declStep2_of_axiom` needs it at the **new** name
   in the extension — which needs the `EnvS2U` the step is building.
   So `DeclStep2All` is a **separate named residue**, with its
   docstring recording that item 1 closes three of the five inputs
   v1's dispatch consumes (`DeclBasisS`/`DeclIndS` have no interp2
   counterpart at all; `DivModPinS` only a draft). *Calling item 2
   "conditional on item 1" would have been the loose statement.*
2. **`no_constant_of_Empty_R2` has no interp2-side proof** — there is
   no `empty_pinned` counterpart at the annotated tier, so the Empty
   content is the collapse lane's, read off `base`. Stated as such.
3. **The eight `no_proof_of_Empty*_R2` conclude `False`, which v1
   proves *unconditionally*.** Their content is **the route, not the
   fact**, and the file says so.

*Rule: when a milestone is a statement rather than a proof, the
inhabitation table is the deliverable and the theorem count is
decoration. Fourteen conditional theorems over four uninhabited
residues is a map of the remaining work, and saying so is what keeps
it one.*
