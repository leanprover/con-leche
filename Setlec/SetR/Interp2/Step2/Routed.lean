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
  ∀ (env : Env) (m : EnvS2U V env) (φ : Setlec.Name → Nat) (fuel : Nat),
    WhnfCoreClaims2 μ m φ fuel → WhnfClaims2 μ m φ fuel →
    DefEqClaims2 μ m φ fuel → InferClaims2 μ m φ fuel →
    InferClaims2 μ m φ (fuel + 1)

/-- The head-normalisation quarter: `whnfCoreBody`'s nine cases. -/
def WhnfCoreStep2 (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Setlec.Name → Nat) (fuel : Nat),
    WhnfCoreClaims2 μ m φ fuel → WhnfClaims2 μ m φ fuel →
    DefEqClaims2 μ m φ fuel → InferClaims2 μ m φ fuel →
    WhnfCoreClaims2 μ m φ (fuel + 1)

/-- The reduction loop: `whnfStep`'s three exits under the budget. -/
def WhnfStep2 (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Setlec.Name → Nat) (fuel : Nat),
    WhnfCoreClaims2 μ m φ fuel → WhnfClaims2 μ m φ fuel →
    DefEqClaims2 μ m φ fuel → InferClaims2 μ m φ fuel →
    WhnfClaims2 μ m φ (fuel + 1)

/-- The definitional-equality quarter: `defeqStep`'s seven blocks. -/
def DefEqStep2 (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2U V env) (φ : Setlec.Name → Nat) (fuel : Nat),
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

/-! ## Pointer: the four Props above are the SEALED shapes

They are kept as the tombstone and nothing new may be aimed at them.
`CheckStep2` is refuted (`inferClaims2_one_refuted`,
`Step2/InferQ.lean`), and so is every quarter that concludes one of its
claims.

The live routing lives **upstream of the discharges and downstream of
this file**, so it cannot be re-exported here — this module is imported
by the amendments, not the other way round:

* `Interp2/Claims2A.lean` — `InferStep2A`, `WhnfCoreStep2A`,
  `WhnfStep2A`, `DefEqStep2A`, `checkStep2A_of` (seal 6: R1–R4);
* `Interp2/Claims2B.lean` — the reduction quarters again, corrected
  (seal 7: the reduct's annotation lives at its own `F' ≥ F`, because
  the delta exit turns a `.const` leaf into a `λ` body).

The dispatch layer this file routes has been re-pointed in place:
`Step2/Dispatch.lean`'s `Amended` section, `Step2/Lit.lean`'s and
`Step2/StrLit.lean`'s tails.  The sealed clause lemmas stay beside
them, likewise as tombstones. -/

end Setlec.SetR.Interp2
