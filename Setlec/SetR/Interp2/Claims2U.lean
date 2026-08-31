import Setlec.SetR.Interp2.EnvS2U

/-!
# The uniqueness-form delta exit — what is left of the `EnvS2U`
re-point

## History, and what this file is now

Seal 39 exposed the tier seam: route (ii) makes the install keys
conditional on the claims, the claims were stated over `EnvS2` — the
**existential** `acval_defn`/`acval_thm` — and the environment tier is
`EnvS2U`, the uniqueness form.  This file was seal 39's answer: a
second copy of the four claims, the `CheckStep2*` step, the induction
and the context predicate, all with the structure parameter weakened
to `EnvS2U`, plus `Iff.rfl` bridges checking that "copied" was exact.

Seal 46 recorded what the generation-six re-point then did to those
copies: **the live `…2E` family was re-pointed at the source**, so
`…Claims2U` and `…Claims2E` became the same definitions twice, the
bridges became `rfl` between identical texts, and
`checkStep2E_of_2U`/`checkStep2U_of_2E` became the identity function.
They were kept for one seal as drift checks and ruled retire-at-
cleanup.

**Retired at the cleanup seal.**  Gone: `CtxOk2U`, `CtxOk2AnnU`,
`CtxOk2DU` and its two kit entries, `ctxOk2DU_iff`, the four
`…Claims2U`, `CheckStep2U`, `checkSound2U`, the four `…_iff` bridges
and the two `checkStep2*_of_*` identities.  `Keys2Cond.lean` — their
only consumer — now names the `…2E` family and `CtxOk2D` directly,
with no proof changed: the substitution is definitional, which is
precisely what the retired bridges asserted.

*Rule: a `rfl` bridge between two texts is a drift check only while
the texts can drift.  Once one is generated from the other by a
rename, the check has no content and the copy is a second place to
keep in step.*

## What survives, and why it is not a copy

The **uniqueness-form delta exit**.  These four have no counterpart in
the live lane: `whnfStep2_delta`/`whnfStep2_delta_thm`
(`Step2/Loop.lean`) and `AcvalDefnInst`/`acvalDefnInst_noParams`
(`Step2/Whnf.lean`) are stated at an `EnvS2` and *produce* a body's
annotation; the transposes below are stated at an `EnvS2U` and
*identify* a given one.  That is seal 34's ruling at the exit it was
made for, and the two forms are not interderivable — see the honest
note at `acvalDefnInstU_noParams`, which says which half of the old
satisfiability argument survives and which does not.

They live here rather than in `Step2/Loop.lean` for an import reason:
`Interp2/EnvS2U.lean` imports `Step2/Whnf.lean`, which imports
`Step2/Loop.lean`, so `EnvS2U` is strictly downstream of the loop
quarter and the uniqueness-form lemmas cannot be stated there.

## The measurement that licensed the re-point, kept

`m.acval_defn`/`m.acval_thm` — the two fields whose form changed — are
consumed by **exactly four lemmas in the whole Step2 development**:
the four named above.  **None of them is a claim discharge.**  Every
one is a lemma *about the residue `AcvalDefnInst`* — that it is
satisfiable at a parameter-free declaration, and that
`Denote2InstLevels` supplies it.

The live lane's re-point confirmed the measurement exactly: those four
were the **only** sites that were not a binder type change, and
`acvalDefnInst_of_instLevels` is the one of them that does not
survive.
-/
namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The delta exit, in the uniqueness form

`Step2/Loop.lean` is where the batch expected the work, and it is —
but not *in* that file: `Interp2/EnvS2U.lean` imports
`Step2/Whnf.lean`, which imports `Step2/Loop.lean`, so `EnvS2U` is
strictly downstream of the loop quarter and the uniqueness-form
lemmas cannot be stated there.  They are stated here instead, beside
the claims that consume them. -/

variable {env : Env} {φ : Name → Nat}

/-- **The delta exit, uniqueness form.**  Where `whnfStep2_delta`
*produces* the body's annotation, this one *identifies* a given one.
That is the whole of seal 34's ruling at the exit it was made for. -/
theorem whnfStep2_delta_U (m : EnvS2UM V μ env) {F : Nat}
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv value hint ∈ env.consts)
    {ra : AVExpr}
    (h : denote2 μ m.acval env φ F 0 value = some ra) :
    ra = m.acval cv.name φ :=
  m.acval_defn φ F cv value hint hc h

/-- Ditto for a theorem's proof value. -/
theorem whnfStep2_delta_thm_U (m : EnvS2UM V μ env) {F : Nat}
    {cv : ConstantVal} {value : Expr}
    (hc : ConstantInfo.thmInfo cv value ∈ env.consts)
    {ra : AVExpr}
    (h : denote2 μ m.acval env φ F 0 value = some ra) :
    ra = m.acval cv.name φ :=
  m.acval_thm φ F cv value hc h

/-- **The residue the delta exit actually consumes, uniqueness
form.**  `AcvalDefnInst` (`Step2/Whnf.lean`) restated the fields at
the *instantiated* value, because `unfoldDefinition` hands the loop
`value.instantiateLevelParams cv.levelParams us`, not `value`.  The
uniqueness transpose keeps that crossing and drops the existence. -/
def AcvalDefnInstU (μ : CheckMode) {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) : Prop :=
  ∀ {F : Nat} {cv : ConstantVal} {value : Expr} {us : List Level},
    ((∃ hint : ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env.consts) ∨
      ConstantInfo.thmInfo cv value ∈ env.consts) →
    us.length = cv.levelParams.length →
    ∀ {ra : AVExpr},
      denote2 μ m.acval env φ F 0
          (value.instantiateLevelParams cv.levelParams us) = some ra →
      ra = m.acval cv.name (Level.substFn φ cv.levelParams us)

/-- **The satisfiability half survives the re-point, and at the same
declarations.**  `acvalDefnInst_noParams` showed the existential
residue holds at a parameter-free declaration from the two `EnvS2`
fields; this is the same argument from the two `EnvS2U` fields.

The honest half: what does *not* survive is
`acvalDefnInst_of_instLevels`, which derived the existential residue
from `Denote2InstLevels` — that derivation reads existence out of
`EnvS2.acval_defn`, and the uniqueness field has none to give.  The
uniqueness residue is derivable from `Denote2InstLevels` only in the
direction that carries an annotation *in*, which is what the form
above states. -/
theorem acvalDefnInstU_noParams {env : Env} (m : EnvS2UM V μ env)
    {F : Nat} {cv : ConstantVal} {value : Expr} {us : List Level}
    (hnp : cv.levelParams = [])
    (hmem : (∃ hint : ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env.consts) ∨
      ConstantInfo.thmInfo cv value ∈ env.consts)
    (hlen : us.length = cv.levelParams.length) {ra : AVExpr}
    (hden : denote2 μ m.acval env φ F 0
        (value.instantiateLevelParams cv.levelParams us) = some ra) :
    ra = m.acval cv.name (Level.substFn φ cv.levelParams us) := by
  obtain rfl : us = [] := by
    rw [hnp] at hlen; exact List.eq_nil_of_length_eq_zero hlen
  have hself : Setlec.Expr.instantiateLevelParams cv.levelParams
      ([] : List Level) value = value := by
    rw [hnp]
    simpa using Setlec.Expr.instantiateLevelParams_self (ks := []) value
  have hfn : Level.substFn φ cv.levelParams ([] : List Level) = φ := by
    rw [hnp]; simpa using substFn_param_self φ []
  rw [hself] at hden
  rw [hfn]
  rcases hmem with ⟨hint, hc⟩ | hc
  · exact m.acval_defn φ F cv value hint hc hden
  · exact m.acval_thm φ F cv value hc hden

/-! ## The three sweeps, re-run after the retirement

**1. Smallest fuel.** Nothing left in this file asserts a `denote2`
success as a conclusion — every `denote2` sits in a premise, and the
two uniqueness-form environment fields put theirs in a premise by
construction (seal 36's first sweep).  Per seal 11, the absence of one
hazard, not a clean bill of health.

**2. Vacuity.** `AcvalDefnInstU` is not `rfl`-provable: its conclusion
is an equation between two annotations the premise does not identify,
and `acvalDefnInstU_noParams` meets it at a real declaration.  The
claims' own inhabitation moved with the claims —
`claims2E_premises_inhabited` (`Claims2E.lean`) is where it now is.

**3. Tombstones.** None edited and none orphaned: the deletions here
were the degenerate `…2U` copies, and no `*_refuted`, `*Uniform`,
`not_*` or `*_flips` declaration mentions one.
`whnfClaims2A_delta_refuted` (`EnvS2Refute.lean`) refutes the
*generation-two* claim, which is stated in its own file and
untouched. -/

end Setlec.SetR.Interp2
