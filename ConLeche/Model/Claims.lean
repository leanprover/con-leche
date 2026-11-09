module

public import ConLeche.Verify.InferLeaves
public import ConLeche.Semantics.Skeleton
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Denote
import ConLeche.Model.Env.EnvModel
public import ConLeche.Model.Currency

public section

/-!
# The P-generation claims: the ladder over `denote` (task #161, P3.3)

The soundness ladder over **`denote`**, the reading of stored terms
(no fuel: there is no run to pay for):

* the truthfulness currency is the semantic invariant `WellDenoted`;
* the context discipline is `CtxOk`, with leaf truthfulness
  `WellDenoted`.

The **dual-success** shape: every `denote` sits in a premise, never
a conclusion, so the smallest-fuel refutation rule has nothing to bite
on.  Level instantiation is `denotePInstLevels`; the environment
crossing is `denote_envExtend` (`FindPreserved`/`LitGuardsAgree`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]

/-- Two types are equal when they are equal away from the point:
neither is the point.  The consumers of a `DefEqClaim` between two
types route through it (task #342 L8): the claim is conditional on the
point (L9); between two members of one type, `IsTy.eq_of_ne_pt` plays
the same part. -/
theorem eq_of_IsTy_of_ne_pt {x y : V} (hx : IsTy x) (hy : IsTy y)
    (h : x ≠ pt → y ≠ pt → x = y) : x = y :=
  h hx.ne_pt hy.ne_pt

/-- Head normalisation, dual success, P currency, conditional on the
point (task #342, L9): the reduct is graded and equal where the subject
is not the point. -/
@[expose] def WhnfCoreClaim {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List Term},
    whnfCore .verified false env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ea' : Term},
      CtxOk m φ d Δa e →
      denote m.acval env φ d e = some ea →
      denote m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ ea) →
      (∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ≠ pt →
          WellDenoted V ρ ea') ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ≠ pt →
          interp V ρ ea = interp V ρ ea'

/-- The reduction loop, dual success, P currency, conditional on the
point (task #342, L9). -/
@[expose] def WhnfClaim {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List Term},
    whnf .verified false env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ea' : Term},
      CtxOk m φ d Δa e →
      denote m.acval env φ d e = some ea →
      denote m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ ea) →
      (∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ≠ pt →
          WellDenoted V ρ ea') ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ≠ pt →
          interp V ρ ea = interp V ρ ea'

/-- Definitional equality, P currency, conditional on the point (task
#342, L9): two sides that are not the point are equal.  A consumer
comparing two types or two members of one type closes with
`eq_of_IsTy_of_ne_pt` / `IsTy.eq_of_ne_pt`. -/
@[expose] def DefEqClaim {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List Term},
    ConLeche.isDefEqCore .verified false env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : Term},
      CtxOk m φ d Δa a →
      CtxOk m φ d Δa b →
      denote m.acval env φ d a = some aa →
      denote m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ aa ≠ pt → interp V ρ ba ≠ pt →
        interp V ρ aa = interp V ρ ba

/-- Inference, dual success, P currency: the subject's and the
type's truthfulness are *conclusions*, and
the type denotes a type. -/
@[expose] def InferClaim {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List Term},
    inferTypeCore .verified false env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ta : Term},
      CtxOk m φ d Δa e →
      denote m.acval env φ d e = some ea →
      denote m.acval env φ d t = some ta →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ ea) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedTy V ρ ta) ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea ∈ˢ interp V ρ ta

end ConLeche.Model
