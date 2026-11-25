module

public import ConLeche.Semantics.Kit

@[expose] public section

/-!
# The definitional-equality clauses — pure `interp` algebra

Every theorem here is pure `interp` algebra — no environment
invariant, no claim carrier.

Per-clause lemmas for the definitional-equality claim.  The claim is
**unconditional in truthfulness** — an `interp` equality and nothing
else: `symm`, `trans` and the binder congruences are one-liners only if
no `WellDenoted` has to cross a `DefEq`.

The structural arms of the definitional-equality body (`quickDefEq`,
`defeqStuck`) are many cases;
the fifteen here are pure interpretation algebra.  The two that are
not — the capability rescues (`structEta`, `structUnit`) and the
literal acceleration — are proved in `Model/Rules/DefEqSound.lean`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## The congruences

The binder cases descend under `Sat_cons`, which is the only
structural fact about `Sat` the quarter consumes. -/

theorem deqStep_appCong {ρ : Nat → V} {fa fb aa ab : Term}
    (hf : interp V ρ fa = interp V ρ fb)
    (ha : interp V ρ aa = interp V ρ ab) :
    interp V ρ (.app fa aa) = interp V ρ (.app fb ab) := by
  simp only [interp_app, hf, ha]

/-- **∀-congruence.**  The codomain descends at the *domain's* own
value set, which is where `Sat_cons` enters. -/
theorem deqStep_piCong {ρ : Nat → V}
    {Aa Ab Ba Bb : Term}
    (hA : interp V ρ Aa = interp V ρ Ab)
    (hB : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba = interp V (cons x ρ) Bb) :
    interp V ρ (.pi Aa Ba) = interp V ρ (.pi Ab Bb) := by
  rw [interp_pi, interp_pi]
  exact piV_ext hA _ _ hB

end ConLeche.Semantics
