# Setlec/SetR — the mode-indexed algorithmic relation family (task #148)

This is the campaign's §-file for the `Setlec/SetR/*` tier.  The
campaign design document (architecture, the full rule tables, the task
sequence, the risk register) is the #148 design deliverable; this file
records what T2 **built**, where it **deviates** from the design's §1
as written, and what T3 (bridge) and T4 (soundness) need to know that
the design document does not say.  House practices are
`Setlec/TTVerify/DESIGN.md` §0/§25 (binding).

## Promoted practices (binding here; candidates for §0/§25)

Four rules earned promotion during T5 by recurring across unrelated
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
