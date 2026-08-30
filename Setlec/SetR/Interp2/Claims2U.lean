import Setlec.SetR.Interp2.EnvS2U

/-!
# The claims, re-pointed to `EnvS2U` — the tier seam closed

Seal 39 exposed the seam: route (ii) makes the install keys
conditional on the claims, the claims are stated over `EnvS2` — the
**existential** `acval_defn`/`acval_thm` — and the environment tier is
`EnvS2U`, the uniqueness form.  Making the keys conditional on an
`EnvS2` would make them conditional on `Denote2Total`'s wall, which is
the obstruction the uniqueness ruling exists to escape.

This file completes seal 34's ruling into the claims: the same
statements, with the structure parameter weakened to `EnvS2U`.

## Not a generation seven

Seal 33 closed the statement tier against *shape* changes forced by
consumer refutation.  Nothing here changes a claim's content: clause
for clause, premise for premise, the `…2U` claims are the `…2E`
claims with `EnvS2` replaced by `EnvS2U`.  `claims2E_of_2U` below is
the mechanical check of that — every bridge is `Iff.rfl`, so the two
families are *definitionally* the same proposition wherever both are
stated.

## Add, never delete

The `…2E` family stays as the older lane, exactly as `EnvS2` stayed
when `EnvS2U` was added (seal 18's precedent, seal 36's application).
`Capstone2E` and the four `…Step2E_of` quarters consume it verbatim
and are untouched.

## The context predicate had to come with them

`CtxOk2`/`CtxOk2Ann`/`CtxOk2D` (`Step2/Dispatch.lean`,
`Interp2/CtxOk2D.lean`) all take an `EnvS2` and all read it **only**
through `m.acval`.  So they are re-pointed here in the same way and
for the same reason, and `ctxOk2DU_iff` records that the re-pointed
predicate is definitionally the old one.

## What the re-point costs, measured rather than asserted

`m.acval_defn`/`m.acval_thm` — the two fields whose form changed — are
consumed by **exactly four lemmas in the whole Step2 development**:
`Step2/Loop.lean`'s `whnfStep2_delta` and `whnfStep2_delta_thm`, and
`Step2/Whnf.lean`'s `acvalDefnInst_noParams` and
`acvalDefnInst_of_instLevels`.  **None of
them is a claim discharge.**  Every one is a lemma *about the residue
`AcvalDefnInst`* — that it is satisfiable at a parameter-free
declaration, and that `Denote2InstLevels` supplies it.

So no quarter needs the existential field to prove a claim, and the
re-point goes through at the statement tier untouched.  What the
uniqueness form does change is the *residue's own* shape, and that is
recorded here rather than routed around: `AcvalDefnInstU` and
`acvalDefnInstU_noParams` below are the uniqueness transposes, and
the honest note at their site says which half of the old satisfiability
argument survives and which does not.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The context predicate, re-pointed

Three definitions, copied clause for clause from `CtxOk2`,
`CtxOk2Ann` and `CtxOk2D` with `EnvS2` weakened to `EnvS2U`.  The
`Iff.rfl` bridges below are the proof that "copied" is exact. -/

/-- `CtxOk2`, over the uniqueness-form environment tier. -/
def CtxOk2U {env : Env} (m : EnvS2U V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel d : Nat) (Δa : List AVExpr) (e : Expr) :
    Prop :=
  Δa.length = d ∧
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2.2 ∧
    ∃ tya Aa,
      denote2 μ m.acval env φ fuel d l.2.2 = some tya ∧
      Δa[d - 1 - l.1]? = some Aa ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ tya
          = interp2 V (fun j => ρ (j + (d - 1 - l.1) + 1)) Aa

/-- `CtxOk2Ann`, ditto. -/
def CtxOk2AnnU {env : Env} (m : EnvS2U V env) (μ : CheckMode)
    (φ : Name → Nat) (F d : Nat) (Δa : List AVExpr) (e : Expr) :
    Prop :=
  ∀ l ∈ e.fvarLeaves, ∀ tya : AVExpr,
    denote2 μ m.acval env φ F d l.2.2 = some tya →
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ tya

/-- `CtxOk2D`, ditto — the generation-five supplier the claims use. -/
def CtxOk2DU {env : Env} (m : EnvS2U V env) (μ : CheckMode)
    (φ : Name → Nat) (F d : Nat) (Δa : List AVExpr) (e : Expr) :
    Prop :=
  CtxOk2U m μ φ F d Δa e ∧ CtxOk2AnnU m μ φ F d Δa e

/-- **The re-pointed predicate is definitionally the old one.**  At an
`EnvS2` the two agree by `rfl`, which is the whole content of the
claim that this is a re-point and not a restatement. -/
theorem ctxOk2DU_iff {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) (F d : Nat) (Δa : List AVExpr) (e : Expr) :
    CtxOk2DU (EnvS2.toU V m) μ φ F d Δa e ↔ CtxOk2D m μ φ F d Δa e :=
  Iff.rfl

/-! ### The two constructors the closed case needs

Not a re-proof of the kit (`Step2/Dispatch.lean`'s inventory): only
the entries a *closed* subject at depth `0` uses, which is where every
install key lives. -/

/-- A subject with no free-variable leaves satisfies the predicate in
the empty context, at every fuel. -/
theorem CtxOk2DU.of_closed {env : Env} {m : EnvS2U V env}
    {μ : CheckMode} {φ : Name → Nat} {F : Nat} {e : Expr}
    (h : e.fvarLeaves = []) : CtxOk2DU m μ φ F 0 [] e := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro l hl; rw [h] at hl; exact absurd hl (by simp)
  · intro l hl; rw [h] at hl; exact absurd hl (by simp)

/-- Fuel monotonicity, on the pair — the one kit entry the keys use
that is not about the empty context.  `denote2_fuelMono` returns the
*same* annotation at the larger fuel, so both halves transport. -/
theorem CtxOk2DU.fuelMono {env : Env} {m : EnvS2U V env}
    {μ : CheckMode} {φ : Name → Nat} {F F' d : Nat}
    {Δa : List AVExpr} {e : Expr} (hle : F ≤ F')
    (h : CtxOk2DU m μ φ F d Δa e) : CtxOk2DU m μ φ F' d Δa e := by
  obtain ⟨⟨hlen, hleaf⟩, hann⟩ := h
  refine ⟨⟨hlen, ?_⟩, ?_⟩
  · intro l hl
    obtain ⟨h1, h2, tya, Aa, h3, h4, h5⟩ := hleaf l hl
    exact ⟨h1, h2, tya, Aa, denote2_fuelMono hle d l.2.2 h3, h4, h5⟩
  · intro l hl tya htya
    obtain ⟨-, -, tya₀, -, h3, -, -⟩ := hleaf l hl
    obtain rfl : tya₀ = tya :=
      Option.some.inj
        ((denote2_fuelMono hle d l.2.2 h3).symm.trans htya)
    exact hann l hl tya₀ h3

/-! ## The four claims, re-pointed

Copied from `Claims2E.lean` with two substitutions and no third:
`EnvS2 → EnvS2U`, `CtxOk2D → CtxOk2DU`. -/

/-- Head normalisation, dual success, over `EnvS2U`. -/
def WhnfCoreClaims2U (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F F' : Nat} {ea ea' : AVExpr},
      CtxOk2DU m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      denote2 μ m.acval env φ F' d e' = some ea' →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- The reduction loop, dual success, over `EnvS2U`. -/
def WhnfClaims2U (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F F' : Nat} {ea ea' : AVExpr},
      CtxOk2DU m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      denote2 μ m.acval env φ F' d e' = some ea' →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- Definitional equality, over `EnvS2U`. -/
def DefEqClaims2U (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.isDefEqCore μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {F F' : Nat} {aa ba : AVExpr},
      CtxOk2DU m μ φ F d Δa a →
      CtxOk2DU m μ φ F' d Δa b →
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F' d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa = interp2 V ρ ba

/-- Inference, dual success, over `EnvS2U`. -/
def InferClaims2U (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AVExpr},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F F' : Nat} {ea ta : AVExpr},
      CtxOk2DU m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      denote2 μ m.acval env φ F' d t = some ta →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-- The step, over `EnvS2U`. -/
def CheckStep2U (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2U μ m φ fuel → WhnfClaims2U μ m φ fuel →
    DefEqClaims2U μ m φ fuel → InferClaims2U μ m φ fuel →
    WhnfCoreClaims2U μ m φ (fuel + 1) ∧ WhnfClaims2U μ m φ (fuel + 1) ∧
      DefEqClaims2U μ m φ (fuel + 1) ∧ InferClaims2U μ m φ (fuel + 1)

/-- The induction, over `EnvS2U` — `checkSound2E`'s proof verbatim,
which is one more check that nothing in the claims' content moved. -/
theorem checkSound2U {μ : CheckMode} {env : Env}
    (hstep : CheckStep2U μ V) (m : EnvS2U V env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2U μ m φ fuel ∧ WhnfClaims2U μ m φ fuel ∧
        DefEqClaims2U μ m φ fuel ∧ InferClaims2U μ m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d e e' Δa h
      rw [Setlec.whnfCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e e' Δa h
      rw [Setlec.whnf_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d a b Δa h
      rw [Setlec.isDefEqCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e t Δa h
      rw [Setlec.inferTypeCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi⟩ := ih
    exact hstep env m φ fuel ihwc ihw ihd ihi

/-! ## The bridges — the re-point checked, not asserted

Each is `Iff.rfl`: at an `EnvS2` the re-pointed claim *is* the
generation-six claim, as a proposition and not merely as a
consequence.  That is the precise sense in which the content did not
change.

The converse direction — every `EnvS2U` comes from an `EnvS2` — is
**not** available and is not claimed: `EnvS2U` drops `cval_annot` as
well as weakening the two `denote2` fields, so `CheckStep2U` is a
*strictly stronger* residue than `CheckStep2E`.  Recorded rather than
elided: a key conditional on `…2U` at an arbitrary `EnvS2U` is
conditional on more than the lane owes today, and the fourteen's swap
must either exhibit its environments as `EnvS2`s (as the probes do) or
carry the difference. -/

theorem whnfCoreClaims2U_iff {μ : CheckMode} {env : Env}
    (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat) :
    WhnfCoreClaims2U μ (EnvS2.toU V m) φ fuel ↔
      WhnfCoreClaims2E μ m φ fuel := Iff.rfl

theorem whnfClaims2U_iff {μ : CheckMode} {env : Env}
    (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat) :
    WhnfClaims2U μ (EnvS2.toU V m) φ fuel ↔
      WhnfClaims2E μ m φ fuel := Iff.rfl

theorem defEqClaims2U_iff {μ : CheckMode} {env : Env}
    (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat) :
    DefEqClaims2U μ (EnvS2.toU V m) φ fuel ↔
      DefEqClaims2E μ m φ fuel := Iff.rfl

theorem inferClaims2U_iff {μ : CheckMode} {env : Env}
    (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat) :
    InferClaims2U μ (EnvS2.toU V m) φ fuel ↔
      InferClaims2E μ m φ fuel := Iff.rfl

/-- **The re-pointed step implies the old one.**  Nothing the older
lane proves from `CheckStep2E` is lost. -/
theorem checkStep2E_of_2U {μ : CheckMode}
    (h : CheckStep2U μ V) : CheckStep2E μ V := by
  intro env m φ fuel h1 h2 h3 h4
  exact h env (EnvS2.toU V m) φ fuel h1 h2 h3 h4

/-! ## The delta exit, in the uniqueness form

`Step2/Loop.lean` is where the batch expected the work, and it is —
but not *in* that file: `Interp2/EnvS2U.lean` imports
`Step2/Whnf.lean`, which imports `Step2/Loop.lean`, so `EnvS2U` is
strictly downstream of the loop quarter and the uniqueness-form
lemmas cannot be stated there.  They are stated here instead, beside
the claims that consume them. -/

variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- **The delta exit, uniqueness form.**  Where `whnfStep2_delta`
*produces* the body's annotation, this one *identifies* a given one.
That is the whole of seal 34's ruling at the exit it was made for. -/
theorem whnfStep2_delta_U (m : EnvS2U V env) {F : Nat}
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv value hint ∈ env.consts)
    {ra : AVExpr}
    (h : denote2 μ m.acval env φ F 0 value = some ra) :
    ra = m.acval cv.name φ :=
  m.acval_defn μ φ F cv value hint hc h

/-- Ditto for a theorem's proof value. -/
theorem whnfStep2_delta_thm_U (m : EnvS2U V env) {F : Nat}
    {cv : ConstantVal} {value : Expr}
    (hc : ConstantInfo.thmInfo cv value ∈ env.consts)
    {ra : AVExpr}
    (h : denote2 μ m.acval env φ F 0 value = some ra) :
    ra = m.acval cv.name φ :=
  m.acval_thm μ φ F cv value hc h

/-- **The residue the delta exit actually consumes, uniqueness
form.**  `AcvalDefnInst` (`Step2/Whnf.lean`) restated the fields at
the *instantiated* value, because `unfoldDefinition` hands the loop
`value.instantiateLevelParams cv.levelParams us`, not `value`.  The
uniqueness transpose keeps that crossing and drops the existence. -/
def AcvalDefnInstU (μ : CheckMode) {env : Env} (m : EnvS2U V env)
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
theorem acvalDefnInstU_noParams {env : Env} (m : EnvS2U V env)
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
  · exact m.acval_defn μ φ F cv value hint hc hden
  · exact m.acval_thm μ φ F cv value hc hden

/-! ## The three sweeps

**1. Smallest fuel.** No claim above asserts a `denote2` success as a
conclusion — every `denote2` sits in a premise, inherited from
generation six, and the two re-pointed environment fields put their
`denote2` in a premise by construction (seal 36's first sweep).  Per
seal 11, the absence of one hazard, not a clean bill of health.

**2. Vacuity.** The claims are `Iff.rfl`-equal to the `…2E` claims at
every `EnvS2`, so `claims2E_premises_inhabited` transports verbatim
and the premise sets are inhabited.  `CtxOk2DU.of_closed` is not
`rfl`-provable — it needs the leaf list to be empty — and
`AcvalDefnInstU` is not `rfl`-provable either, since its conclusion
is an equation between two annotations the premise does not identify.

**3. Tombstones.** A file added, none edited. -/

end Setlec.SetR.Interp2
