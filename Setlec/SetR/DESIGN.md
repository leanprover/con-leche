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

### FINDING 5 (raised at `declIndS` stage 2; **a reading to fix, not a wall**): the block folds' fixed `cval`

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
