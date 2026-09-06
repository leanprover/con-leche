import Lech.Semantics.Interp

/-!
# `SetBase/Sat2` — the annotated context's satisfaction, and its
transitivity kit

`Sat2` (with its two introduction lemmas) and `interp2C_trans`, re-based
at THE SEPARATION's S2 (task #161).

`interp2C_trans` is the **two-edit sever**'s second edit: the graded
lane's `Step2/WhnfP` imported the whole 2U module `Step2/Whnf` for this
one eight-line composition.  The lemma is model-free — it is `Eq.trans`
under a valuation quantifier — but its *statement* names `Sat2`, which
lived in `Annot/EnvS2.lean` beside the `EnvS`-containing invariant.  A
base module may not import a lane, so `Sat2` comes down with it; it is
model-free in exactly the same sense (a `List AVExpr`, a valuation, and
`interp2`), and both lanes state their context currency with it.

Statements verbatim, namespace (`Lech.SetR.Interp2`) unchanged.
-/

namespace Lech.Semantics
open Lech.SetModel

open SetTheory

universe w

section
variable (V : Type w) [SetTheory V]

/-- `ρ` satisfies an annotated context over `interp2` — the `Sat`
transpose. -/
def Sat2 (Δa : List AVExpr) (ρ : Nat → V) : Prop :=
  ∀ i Aa, Δa[i]? = some Aa →
    ρ i ∈ˢ interp2 V (fun j => ρ (j + i + 1)) Aa

theorem Sat2_nil (ρ : Nat → V) : Sat2 V [] ρ := by
  intro i Aa hi
  cases hi

theorem Sat2_cons {Δa : List AVExpr} {Aa : AVExpr} {ρ : Nat → V} {x : V}
    (hρ : Sat2 V Δa ρ) (hx : x ∈ˢ interp2 V ρ Aa) :
    Sat2 V (Aa :: Δa) (cons x ρ) := by
  intro i Aa' hi
  cases i with
  | zero =>
    obtain rfl : Aa = Aa' := by simpa using hi
    exact hx
  | succ i =>
    have h := hρ i Aa' (by simpa using hi)
    exact h

end

section
variable {V : Type w} [SetTheory V]

/-- The tail of a satisfying valuation satisfies the tail context —
`Sat2_cons`'s inverse, and what every weakening step consumes. -/
theorem Sat2_tail {Δa : List AVExpr} {Ba : AVExpr} {ρ : Nat → V}
    (hρ : Sat2 V (Ba :: Δa) ρ) : Sat2 V Δa (fun j => ρ (j + 1)) := by
  intro i Aa hi
  exact hρ (i + 1) Aa (by simpa using hi)

/-- Equalities compose per valuation; the invariant does not travel
with them, because in the hoisted currency it is carried separately
and uniformly. -/
theorem interp2C_trans {Δa : List AVExpr} {a b c : AVExpr}
    (h1 : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ a = interp2 V ρ b)
    (h2 : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ b = interp2 V ρ c) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ a = interp2 V ρ c :=
  fun ρ hρ => (h1 ρ hρ).trans (h2 ρ hρ)

end

end Lech.Semantics
