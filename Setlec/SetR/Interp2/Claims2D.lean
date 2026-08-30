import Setlec.SetR.Interp2.CtxOk2D

/-!
# `Claims2`, generation five — one context currency

Lineage: `Claims2` → `Claims2A` → `Claims2B` → `Claims2C` → this file.
The first two were **refuted**; `Claims2B` and `Claims2C` are not.

## The change

All four claims carry **`CtxOk2D`**, in place of `CtxOkR`-on-erasures
for the three reduction/defeq claims and `CtxOk2` for the inference
claim. Two independent motives, both already decided:

* **Seal 11.** `CtxOk2R` — the bridge from `CtxOk2` to `CtxOkR` — is
  **false, premise-free** (`not_ctxOk2R`), because the two currencies
  disagree about which contexts are inhabited at an empty-domain λ
  (the #100 countermodel). Two independent consumers need that bridge
  and neither can have it, so the seam must go rather than be crossed.
* **Seal 17.** `CtxOk2`'s leaf package carries no *truthfulness*, so
  the `.fvar` clause cannot deliver the returned type's `AnnotOk2`.
  `CtxOk2D` adds it as the fourth conjunct.

## The shape change this forces

`CtxOk2D` is indexed by the annotation fuel `F`, and `CtxOkR` was not.
So in the three claims that took `CtxOkR` **before** `∀ {F}`, the
context hypothesis moves **inside** that binder — the shape
`InferClaims2C` has had since generation two. Mechanical, but it is a
real reordering and every consumer sees it.

## What does *not* change

The ρ-hoist (generation four) is untouched: every `AnnotOk2` a claim
takes or gives stays above the `∀ ρ`. The fuel slack `∃ F' ≥ F`
(generation three) is untouched. **One change per generation** — the
rule this campaign adopted at seal 14 and has not since had cause to
regret.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]

/-- Head normalisation, one currency. -/
def WhnfCoreClaims2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F : Nat} {ea : AVExpr},
      CtxOk2D m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
      ∃ F' ea', F ≤ F' ∧
        denote2 μ m.acval env φ F' d e' = some ea' ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- The reduction loop, one currency. -/
def WhnfClaims2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F : Nat} {ea : AVExpr},
      CtxOk2D m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
      ∃ F' ea', F ≤ F' ∧
        denote2 μ m.acval env φ F' d e' = some ea' ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- Definitional equality, one currency. -/
def DefEqClaims2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.isDefEqCore μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {F : Nat} {aa ba : AVExpr},
      CtxOk2D m μ φ F d Δa a →
      CtxOk2D m μ φ F d Δa b →
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa = interp2 V ρ ba

/-- Inference, one currency. -/
def InferClaims2D (μ : CheckMode) {env : Env} (m : EnvS2U V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AVExpr},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F : Nat} {ea : AVExpr},
      CtxOk2D m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      ∃ F' ta, F ≤ F' ∧
        denote2 μ m.acval env φ F' d t = some ta ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-- The generation-five step. -/
def CheckStep2D (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2D μ m φ fuel → WhnfClaims2D μ m φ fuel →
    DefEqClaims2D μ m φ fuel → InferClaims2D μ m φ fuel →
    WhnfCoreClaims2D μ m φ (fuel + 1) ∧ WhnfClaims2D μ m φ (fuel + 1) ∧
      DefEqClaims2D μ m φ (fuel + 1) ∧ InferClaims2D μ m φ (fuel + 1)

/-- The generation-five induction. -/
theorem checkSound2D {μ : CheckMode} {env : Env}
    (hstep : CheckStep2D μ V) (m : EnvS2U V env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2D μ m φ fuel ∧ WhnfClaims2D μ m φ fuel ∧
        DefEqClaims2D μ m φ fuel ∧ InferClaims2D μ m φ fuel := by
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

/-! ## The routed quarters -/

/-- The inference quarter. -/
def InferStep2D (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2D μ m φ fuel → WhnfClaims2D μ m φ fuel →
    DefEqClaims2D μ m φ fuel → InferClaims2D μ m φ fuel →
    InferClaims2D μ m φ (fuel + 1)

/-- The head-normalisation quarter. -/
def WhnfCoreStep2D (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2D μ m φ fuel → WhnfClaims2D μ m φ fuel →
    DefEqClaims2D μ m φ fuel → InferClaims2D μ m φ fuel →
    WhnfCoreClaims2D μ m φ (fuel + 1)

/-- The reduction loop. -/
def WhnfStep2D (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2D μ m φ fuel → WhnfClaims2D μ m φ fuel →
    DefEqClaims2D μ m φ fuel → InferClaims2D μ m φ fuel →
    WhnfClaims2D μ m φ (fuel + 1)

/-- The definitional-equality quarter. -/
def DefEqStep2D (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2D μ m φ fuel → WhnfClaims2D μ m φ fuel →
    DefEqClaims2D μ m φ fuel → InferClaims2D μ m φ fuel →
    DefEqClaims2D μ m φ (fuel + 1)

/-- **The generation-five assembly.** -/
theorem checkStep2D_of {μ : CheckMode} {V : Type w} [SetTheory V]
    (hwc : WhnfCoreStep2D μ V) (hw : WhnfStep2D μ V)
    (hd : DefEqStep2D μ V) (hi : InferStep2D μ V) :
    CheckStep2D μ V := by
  intro env m φ fuel h1 h2 h3 h4
  exact ⟨hwc env m φ fuel h1 h2 h3 h4, hw env m φ fuel h1 h2 h3 h4,
    hd env m φ fuel h1 h2 h3 h4, hi env m φ fuel h1 h2 h3 h4⟩

end Setlec.SetR.Interp2
