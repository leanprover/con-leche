# Setlec/SetR — the mode-indexed algorithmic relation family (task #148)

This is the campaign's §-file for the `Setlec/SetR/*` tier.  The
campaign design document (architecture, the full rule tables, the task
sequence, the risk register) is the #148 design deliverable; this file
records what T2 **built**, where it **deviates** from the design's §1
as written, and what T3 (bridge) and T4 (soundness) need to know that
the design document does not say.  House practices are
`Setlec/TTVerify/DESIGN.md` §0/§25 (binding).

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

**D3 — `rP ≤ mI` is an R11 side condition.**  Not checked per-fire by
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
