import Setlec.SetR.Interp2.Step2.Dispatch

/-!
# `CheckStep2`, routed by quarter — the statement layer

`CheckStep2` decomposed into its four independent halves, one per
checker function, in the house's routed-`Prop` pattern: each is a named
`Prop` a discharge can be aimed at without touching the others, and
`checkStep2_of` assembles them.

This is the campaign's work surface.  Each quarter takes **all four**
claims at `fuel` — the checker's bodies call each other through the
knot, so an inference clause may need a defeq fact and vice versa — and
produces **one** claim at `fuel + 1`.
-/

namespace Setlec.SetR.Interp2

open Setlec (CheckMode Env)

universe w

/-- The inference quarter: `inferBody`'s eleven clauses. -/
def InferStep2 (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Setlec.Name → Nat) (fuel : Nat),
    WhnfCoreClaims2 μ m φ fuel → WhnfClaims2 μ m φ fuel →
    DefEqClaims2 μ m φ fuel → InferClaims2 μ m φ fuel →
    InferClaims2 μ m φ (fuel + 1)

/-- The head-normalisation quarter: `whnfCoreBody`'s nine cases. -/
def WhnfCoreStep2 (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Setlec.Name → Nat) (fuel : Nat),
    WhnfCoreClaims2 μ m φ fuel → WhnfClaims2 μ m φ fuel →
    DefEqClaims2 μ m φ fuel → InferClaims2 μ m φ fuel →
    WhnfCoreClaims2 μ m φ (fuel + 1)

/-- The reduction loop: `whnfStep`'s three exits under the budget. -/
def WhnfStep2 (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Setlec.Name → Nat) (fuel : Nat),
    WhnfCoreClaims2 μ m φ fuel → WhnfClaims2 μ m φ fuel →
    DefEqClaims2 μ m φ fuel → InferClaims2 μ m φ fuel →
    WhnfClaims2 μ m φ (fuel + 1)

/-- The definitional-equality quarter: `defeqStep`'s seven blocks. -/
def DefEqStep2 (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2 V env) (φ : Setlec.Name → Nat) (fuel : Nat),
    WhnfCoreClaims2 μ m φ fuel → WhnfClaims2 μ m φ fuel →
    DefEqClaims2 μ m φ fuel → InferClaims2 μ m φ fuel →
    DefEqClaims2 μ m φ (fuel + 1)

/-- **The assembly.**  The four quarters are `CheckStep2`. -/
theorem checkStep2_of {μ : CheckMode} {V : Type w} [SetTheory V]
    (hwc : WhnfCoreStep2 μ V) (hw : WhnfStep2 μ V)
    (hd : DefEqStep2 μ V) (hi : InferStep2 μ V) :
    CheckStep2 μ V := by
  intro env m φ fuel h1 h2 h3 h4
  exact ⟨hwc env m φ fuel h1 h2 h3 h4, hw env m φ fuel h1 h2 h3 h4,
    hd env m φ fuel h1 h2 h3 h4, hi env m φ fuel h1 h2 h3 h4⟩

end Setlec.SetR.Interp2
