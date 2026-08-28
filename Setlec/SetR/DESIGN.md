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
