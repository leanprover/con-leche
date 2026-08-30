import Setlec.SetR.Interp2.Claims2

/-!
# `CheckStep2`, the definitional-equality quarter — Tier A clauses

Per-clause lemmas for `DefEqClaims2`.  The claim is **unconditional in
truthfulness** — an `interp2` equality and nothing else — which is the
grading `DeqS` uses and for the same reason: `symm`, `trans` and the
binder congruences are one-liners only if no `AnnotOk2` has to cross a
`DefEq`.  Breaking that grading would immediately re-break them.

`defeqStep`'s seventh block (structural congruence) is seventeen cases;
Tier A is the fifteen that are pure interpretation algebra.  The two
that are not — the capability rescues (`structEta`, `structUnit`,
`pairEta`) and the literal acceleration — are Tier C and Tier B
respectively, and appear here only as names.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The equivalence -/

theorem deqStep2_refl {ρ : Nat → V} (ea : AVExpr) :
    interp2 V ρ ea = interp2 V ρ ea := rfl

theorem deqStep2_symm {ρ : Nat → V} {aa ba : AVExpr}
    (h : interp2 V ρ aa = interp2 V ρ ba) :
    interp2 V ρ ba = interp2 V ρ aa := h.symm

theorem deqStep2_trans {ρ : Nat → V} {aa ba ca : AVExpr}
    (h₁ : interp2 V ρ aa = interp2 V ρ ba)
    (h₂ : interp2 V ρ ba = interp2 V ρ ca) :
    interp2 V ρ aa = interp2 V ρ ca := h₁.trans h₂

/-! ## The congruences

The binder cases descend under `Sat2_cons`, which is the only
structural fact about `Sat2` the quarter consumes. -/

theorem deqStep2_appCong {ρ : Nat → V} {fa fb aa ab : AVExpr}
    (hf : interp2 V ρ fa = interp2 V ρ fb)
    (ha : interp2 V ρ aa = interp2 V ρ ab) :
    interp2 V ρ (.app fa aa) = interp2 V ρ (.app fb ab) := by
  simp only [interp2_app, hf, ha]

theorem deqStep2_projCong {ρ : Nat → V} {i : Nat} {ea eb : AVExpr}
    (h : interp2 V ρ ea = interp2 V ρ eb) :
    interp2 V ρ (.proj i ea) = interp2 V ρ (.proj i eb) := by
  simp only [interp2_proj, h]

theorem deqStep2_eqECong {ρ : Nat → V} {Ta Tb aa ab ba bb : AVExpr}
    (ha : interp2 V ρ aa = interp2 V ρ ab)
    (hb : interp2 V ρ ba = interp2 V ρ bb) :
    interp2 V ρ (.eqE Ta aa ba) = interp2 V ρ (.eqE Tb ab bb) := by
  simp only [interp2_eqE, ha, hb]

/-- **∀-congruence.**  The codomain descends at the *domain's* own
value set, which is where `Sat2_cons` enters. -/
theorem deqStep2_piCong {ρ : Nat → V} {u u' v : Nat}
    {Aa Ab Ba Bb : AVExpr}
    (hA : interp2 V ρ Aa = interp2 V ρ Ab)
    (hB : ∀ x, x ∈ˢ interp2 V ρ Aa →
      interp2 V (cons x ρ) Ba = interp2 V (cons x ρ) Bb) :
    interp2 V ρ (.pi u v Aa Ba) = interp2 V ρ (.pi u' v Ab Bb) := by
  simp only [interp2_pi, ← hA]
  exact piR_congr hB

/-- **λ-congruence**, at a shared codomain numeral — which is what the
run supplies, since both sides' annotations come from one `denote2`
walk (R1's coherence, in the form the consumer needs it). -/
theorem deqStep2_lamCong {ρ : Nat → V} {v : Nat} {Aa Ab ba bb : AVExpr}
    (hA : interp2 V ρ Aa = interp2 V ρ Ab)
    (hb : ∀ x, x ∈ˢ interp2 V ρ Aa →
      interp2 V (cons x ρ) ba = interp2 V (cons x ρ) bb) :
    interp2 V ρ (.lam v Aa ba) = interp2 V ρ (.lam v Ab bb) := by
  simp only [interp2_lam, ← hA]
  exact lamR_congr hb

/-! ## Proof irrelevance

The `Prop`-kind collapse, in the annotated currency: two terms whose
types are propositions are both the canonical proof, whatever the
propositions are.  The checker certifies each side's type separately
and never that the two agree — so this takes two independent
memberships, as the rule does. -/

theorem deqStep2_proofIrrel {ρ : Nat → V} {aa ba Ta Tb : AVExpr}
    (hTa : interp2 V ρ Ta ∈ˢ (univZero : V))
    (hTb : interp2 V ρ Tb ∈ˢ (univZero : V))
    (ha : interp2 V ρ aa ∈ˢ interp2 V ρ Ta)
    (hb : interp2 V ρ ba ∈ˢ interp2 V ρ Tb) :
    interp2 V ρ aa = interp2 V ρ ba :=
  (eq_pt_of_mem_univZero hTa ha).trans
    (eq_pt_of_mem_univZero hTb hb).symm

/-! ## η for functions

`lamR_eta` at the stuck side's product — premise-free above kind `0`,
and at kind `0` both sides are the canonical proof anyway. -/

theorem deqStep2_eta {v : Nat} {A f : V} {B : V → V}
    (hf : f ∈ˢ piR v A B) :
    lamR v A (fun x => SetTheory.app f x) = f := lamR_eta hf

end Setlec.SetR.Interp2
