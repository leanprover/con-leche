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
