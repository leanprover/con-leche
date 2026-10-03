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
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The congruences

The binder cases descend under `Sat_cons`, which is the only
structural fact about `Sat` the quarter consumes. -/

theorem deqStep_appCong {ρ : Nat → V} {fa fb aa ab : AnnotTerm}
    (hf : interp V ρ fa = interp V ρ fb)
    (ha : interp V ρ aa = interp V ρ ab) :
    interp V ρ (.app fa aa) = interp V ρ (.app fb ab) := by
  simp only [interp_app, hf, ha]

theorem deqStep_fstCong {ρ : Nat → V} {ea eb : AnnotTerm}
    (h : interp V ρ ea = interp V ρ eb) :
    interp V ρ (.fst ea) = interp V ρ (.fst eb) := by
  simp only [interp_fst, h]

theorem deqStep_sndCong {ρ : Nat → V} {ea eb : AnnotTerm}
    (h : interp V ρ ea = interp V ρ eb) :
    interp V ρ (.snd ea) = interp V ρ (.snd eb) := by
  simp only [interp_snd, h]

/-- **∀-congruence.**  The codomain descends at the *domain's* own
value set, which is where `Sat_cons` enters. -/
theorem deqStep_piCong {ρ : Nat → V} {u u' v : Nat}
    {Aa Ab Ba Bb : AnnotTerm}
    (hA : interp V ρ Aa = interp V ρ Ab)
    (hB : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba = interp V (cons x ρ) Bb) :
    interp V ρ (.pi u v Aa Ba) = interp V ρ (.pi u' v Ab Bb) := by
  simp only [interp_pi, ← hA]
  exact piR_congr hB

/-- **λ-congruence**, at a shared codomain numeral — which is what the
run supplies, since both sides' annotations come from one annotation
walk. -/
theorem deqStep_lamCong {ρ : Nat → V} {v : Nat} {Aa Ab ba bb : AnnotTerm}
    (hA : interp V ρ Aa = interp V ρ Ab)
    (hb : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) ba = interp V (cons x ρ) bb) :
    interp V ρ (.lam v Aa ba) = interp V ρ (.lam v Ab bb) := by
  simp only [interp_lam, ← hA]
  exact lamR_congr hb

/-! ## Proof irrelevance

The `Prop`-kind collapse, in the annotated currency: two terms whose
types are propositions are both the canonical proof, whatever the
propositions are.  The checker certifies each side's type separately
and never that the two agree — so this takes two independent
memberships, as the rule does. -/

/-! ## η for functions

`lamR_eta` at the stuck side's product — premise-free above kind `0`,
and at kind `0` both sides are the canonical proof anyway. -/

end ConLeche.Semantics
