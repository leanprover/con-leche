import Setlec.SetR.Interp2.Claims2D

/-!
# `Claims2`, generation six — dual success

Lineage: `Claims2` → `2A` → `2B` → `2C` → `2D` → this file. The first
two were **refuted**; `2B`–`2D` were superseded, not falsified.

## The change

**Every annotation a claim used to *produce* is now a premise.** The
claims no longer promise that a reduct or an inferred type annotates;
they say that *when both sides annotate*, the annotations agree.

Forced by seal 28: the reduction claims' existential annotations
predicted `sortOfE`/`lamSortE` runs on terms nobody had run, and
`Level.isEquiv`'s fuel makes that prediction **false** under level
substitution (`not_isEquivSubstMono`) — the verdict goes to `none`, so
the instantiated run does *less*. Conditioning on a given run excludes
the `none` channel by witness rather than by a budget nothing carries.

## Where existence went

To `Denote2Total` (`Interp2/EnvLaws2.lean`): *an annotation exists for
any term the checker successfully ran on.* Itself dual-success — it
conditions on a given run and predicts nothing. Seal 30 priced the
`.app` clause against it and it carries: that clause holds
`inferTypeCore … = .ok tf` for the head's type and the `whnf` run for
the `∀`, which is exactly what the supplier consumes.

## What did *not* change, and one thing that was already right

The fuel slack, the ρ-hoist and the single context currency all stand.
And **`DefEqClaims2D` was already in this shape** — it has taken both
annotations as premises since generation four's hoist. That is not a
coincidence: defeq is the one claim that never produced a reduct, and
seal 14 recorded it as "purely relieved" by the hoist. *The claim that
needed no change is the one that was already dual-success.*

## Fuel ordering, dropped

Generations three through five carried `F ≤ F'` because the reduct's
annotation was *produced* and had to be produced somewhere reachable.
With both annotations given, the two fuels are independent:
`denote2_fuelMono` makes `denote2` functional wherever defined, so an
annotation is the same object at every fuel that computes it. The
ordering is therefore **noise**, and dropping it is not a weakening.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]

/-- Head normalisation, dual success. -/
def WhnfCoreClaims2E (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F F' : Nat} {ea ea' : AVExpr},
      CtxOk2D m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      denote2 μ m.acval env φ F' d e' = some ea' →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- The reduction loop, dual success. -/
def WhnfClaims2E (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F F' : Nat} {ea ea' : AVExpr},
      CtxOk2D m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      denote2 μ m.acval env φ F' d e' = some ea' →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- Definitional equality — **unchanged from generation five** except
for the fuel split, because it was already dual-success. -/
def DefEqClaims2E (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.isDefEqCore μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {F F' : Nat} {aa ba : AVExpr},
      CtxOk2D m μ φ F d Δa a →
      CtxOk2D m μ φ F' d Δa b →
      denote2 μ m.acval env φ F d a = some aa →
      denote2 μ m.acval env φ F' d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa = interp2 V ρ ba

/-- Inference, dual success. -/
def InferClaims2E (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AVExpr},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F F' : Nat} {ea ta : AVExpr},
      CtxOk2D m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      denote2 μ m.acval env φ F' d t = some ta →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea ∈ˢ interp2 V ρ ta

/-- The generation-six step. -/
def CheckStep2E (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2E μ m φ fuel → WhnfClaims2E μ m φ fuel →
    DefEqClaims2E μ m φ fuel → InferClaims2E μ m φ fuel →
    WhnfCoreClaims2E μ m φ (fuel + 1) ∧ WhnfClaims2E μ m φ (fuel + 1) ∧
      DefEqClaims2E μ m φ (fuel + 1) ∧ InferClaims2E μ m φ (fuel + 1)

/-- The generation-six induction. -/
theorem checkSound2E {μ : CheckMode} {env : Env}
    (hstep : CheckStep2E μ V) (m : EnvS2 V env) (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2E μ m φ fuel ∧ WhnfClaims2E μ m φ fuel ∧
        DefEqClaims2E μ m φ fuel ∧ InferClaims2E μ m φ fuel := by
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

/-! ## The three checks on the frozen text

**1. Smallest fuel — satisfied by construction, not by luck.** No
clause above asserts a `denote2` success as a *conclusion*: every
`denote2` sits in a premise. The rule that refuted three statements in
this campaign has nothing to bite on here, and that is the structural
consequence of dual success rather than a happy accident. Per seal 11
this is still **not** a clean bill of health — it is the absence of one
specific hazard.

**2. Vacuity — probed, below.** A claim whose premises cannot all hold
says nothing. Dual success *adds* premises, so this is the check the
generation most needs. `claims2E_premises_inhabited` exhibits an
instance where every premise of the reduction claims holds at once.

**3. Tombstones — swept.** This generation adds a file and edits none,
so every `*_refuted`, `*Uniform`, `not_*` and `*_flips` declaration is
untouched; the tree builds green with all of them in place. -/

/-- **The vacuity probe.**  At a sort, at depth `0`, in the empty
context, every premise the reduction claims impose holds
simultaneously — so the claims are not vacuously true.

Deliberately at `.sort`: it is the one shape whose `whnfCore` and
`denote2` both answer without a run, so the probe tests the *premise
set*, not the checker's cooperation. -/
theorem claims2E_premises_inhabited {μ : CheckMode} {env : Env}
    (m : EnvS2 V env) (φ : Name → Nat) (fuel F F' : Nat) :
    whnfCore μ env (fuel + 1) 0 (.sort .zero) = .ok (.sort .zero) ∧
      CtxOk2D m μ φ F 0 [] (.sort .zero) ∧
      denote2 μ m.acval env φ F 0 (.sort .zero) = some (.sort 0) ∧
      denote2 μ m.acval env φ F' 0 (.sort .zero) = some (.sort 0) ∧
      (∀ ρ : Nat → V, Sat2 V [] ρ → AnnotOk2 V ρ (.sort 0)) := by
  refine ⟨rfl, ⟨CtxOk2.nil ?_, CtxOk2Ann.of_fvarLeaves_nil ?_⟩,
    ?_, ?_, fun ρ _ => ?_⟩
  · simp [Setlec.Expr.fvarLeaves]
  · simp [Setlec.Expr.fvarLeaves]
  · rw [denote2]; simp [Setlec.Level.eval]
  · rw [denote2]; simp [Setlec.Level.eval]
  · simp [AnnotOk2]

/-! ## The routed quarters -/

def InferStep2E (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2E μ m φ fuel → WhnfClaims2E μ m φ fuel →
    DefEqClaims2E μ m φ fuel → InferClaims2E μ m φ fuel →
    InferClaims2E μ m φ (fuel + 1)

def WhnfCoreStep2E (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2E μ m φ fuel → WhnfClaims2E μ m φ fuel →
    DefEqClaims2E μ m φ fuel → InferClaims2E μ m φ fuel →
    WhnfCoreClaims2E μ m φ (fuel + 1)

def WhnfStep2E (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2E μ m φ fuel → WhnfClaims2E μ m φ fuel →
    DefEqClaims2E μ m φ fuel → InferClaims2E μ m φ fuel →
    WhnfClaims2E μ m φ (fuel + 1)

def DefEqStep2E (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2E μ m φ fuel → WhnfClaims2E μ m φ fuel →
    DefEqClaims2E μ m φ fuel → InferClaims2E μ m φ fuel →
    DefEqClaims2E μ m φ (fuel + 1)

/-- **The generation-six assembly.** -/
theorem checkStep2E_of {μ : CheckMode} {V : Type w} [SetTheory V]
    (hwc : WhnfCoreStep2E μ V) (hw : WhnfStep2E μ V)
    (hd : DefEqStep2E μ V) (hi : InferStep2E μ V) :
    CheckStep2E μ V := by
  intro env m φ fuel h1 h2 h3 h4
  exact ⟨hwc env m φ fuel h1 h2 h3 h4, hw env m φ fuel h1 h2 h3 h4,
    hd env m φ fuel h1 h2 h3 h4, hi env m φ fuel h1 h2 h3 h4⟩

end Setlec.SetR.Interp2
