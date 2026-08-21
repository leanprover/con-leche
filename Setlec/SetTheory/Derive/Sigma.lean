import Setlec.SetTheory.Derive.Univ

/-!
# Dependent pairs, with the level-0 truncation

`sigmaSet w A B` is, for `w ≠ 0`, the raw pair set `sigmaPairs A B`
(Kuratowski pairs `⟨a, b⟩` with `a ∈ A`, `b ∈ B a`); for `w = 0` the
truth value `[∃ a ∈ A, B a inhabited]` (the `Prop` collapse).

`spair` is the Kuratowski pair; `sfst`/`ssnd` extract the components
classically (well-defined by `kpair_inj`) and default to `pt` on
non-pairs — in particular on `pt` itself, which is never a pair, so
`sfst pt = ssnd pt = pt` holds by the tag.
-/

namespace Setlec.TG

universe u

variable {V : Type u} [TG V]

open Classical in
/-- Dependent pair set at level `w` (see module docs). -/
noncomputable def sigmaSet (w : Nat) (A : V) (B : V → V) : V :=
  if w = 0 then truthVal (∃ x, x ∈ᵗ A ∧ ∃ y, y ∈ᵗ B x) else sigmaPairs A B

/-- Pairing: the Kuratowski pair. -/
noncomputable def spair (a b : V) : V := kpair a b

open Classical in
/-- First projection, `pt` on non-pairs. -/
noncomputable def sfst (p : V) : V :=
  if h : ∃ a b, p = kpair a b then Classical.choose h else pt

open Classical in
/-- Second projection, `pt` on non-pairs. -/
noncomputable def ssnd (p : V) : V :=
  if h : ∃ a b, p = kpair a b then Classical.choose (Classical.choose_spec h)
  else pt

theorem sigmaSet_zero {A : V} {B : V → V} :
    sigmaSet 0 A B = truthVal (∃ x, x ∈ᵗ A ∧ ∃ y, y ∈ᵗ B x) := by
  unfold sigmaSet; exact if_pos rfl

theorem sigmaSet_pos {w : Nat} (hw : w ≠ 0) {A : V} {B : V → V} :
    sigmaSet w A B = sigmaPairs A B := by
  unfold sigmaSet; exact if_neg hw

theorem sigma_congr {w : Nat} {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ᵗ A → B x = B' x) : sigmaSet w A B = sigmaSet w A B' := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [sigmaSet_zero, sigmaSet_zero]
    refine truthVal_congr ⟨?_, ?_⟩
    · rintro ⟨x, hx, y, hy⟩; exact ⟨x, hx, y, h x hx ▸ hy⟩
    · rintro ⟨x, hx, y, hy⟩; exact ⟨x, hx, y, (h x hx).symm ▸ hy⟩
  · rw [sigmaSet_pos (Nat.pos_iff_ne_zero.mp hw), sigmaSet_pos (Nat.pos_iff_ne_zero.mp hw)]
    exact sigmaPairs_congr h

theorem spair_mem {w : Nat} {A : V} {B : V → V} {a b : V} (hw : w ≠ 0)
    (ha : a ∈ᵗ A) (hb : b ∈ᵗ B a) : spair a b ∈ᵗ sigmaSet w A B := by
  rw [sigmaSet_pos hw]
  exact mem_sigmaPairs.mpr ⟨a, ha, b, hb, rfl⟩

theorem pt_mem_sigma {A : V} {B : V → V} {a b : V}
    (ha : a ∈ᵗ A) (hb : b ∈ᵗ B a) : (pt : V) ∈ᵗ sigmaSet 0 A B := by
  rw [sigmaSet_zero]
  exact pt_mem_truthVal ⟨a, ha, b, hb⟩

theorem mem_sigma_elim {w : Nat} {A : V} {B : V → V} {t : V}
    (ht : t ∈ᵗ sigmaSet w A B) :
    ∃ a b, a ∈ᵗ A ∧ b ∈ᵗ B a ∧ (w = 0 → t = pt) ∧ (w ≠ 0 → t = spair a b) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [sigmaSet_zero] at ht
    obtain ⟨a, ha, b, hb⟩ := of_mem_truthVal ht
    exact ⟨a, b, ha, hb, fun _ => eq_pt_of_mem_truthVal ht, fun h0 => absurd rfl h0⟩
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    rw [sigmaSet_pos hw'] at ht
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sigmaPairs.mp ht
    exact ⟨a, b, ha, hb, fun h0 => absurd h0 hw', fun _ => rfl⟩

theorem sfst_spair (a b : V) : sfst (spair a b) = a := by
  unfold sfst spair
  rw [dif_pos ⟨a, b, rfl⟩]
  have hs := Classical.choose_spec
    (⟨a, b, rfl⟩ : ∃ a' b', (kpair a b : V) = kpair a' b')
  have hs2 := Classical.choose_spec hs
  exact (kpair_inj hs2).1.symm

theorem ssnd_spair (a b : V) : ssnd (spair a b) = b := by
  unfold ssnd spair
  rw [dif_pos ⟨a, b, rfl⟩]
  have hs := Classical.choose_spec
    (⟨a, b, rfl⟩ : ∃ a' b', (kpair a b : V) = kpair a' b')
  have hs2 := Classical.choose_spec hs
  exact (kpair_inj hs2).2.symm

theorem sfst_pt : sfst (pt : V) = pt := by
  unfold sfst
  rw [dif_neg]
  rintro ⟨a, b, h⟩
  exact pt_ne_kpair a b h

theorem ssnd_pt : ssnd (pt : V) = pt := by
  unfold ssnd
  rw [dif_neg]
  rintro ⟨a, b, h⟩
  exact pt_ne_kpair a b h

/-- Formation along the tower, at the joint level `max u v`. -/
theorem sigma_mem_univ {u v : Nat} {A : V} {B : V → V}
    (hA : A ∈ᵗ (univ u : V)) (hB : ∀ x, x ∈ᵗ A → B x ∈ᵗ (univ v : V)) :
    sigmaSet (Nat.max u v) A B ∈ᵗ (univ (Nat.max u v) : V) := by
  rcases Nat.eq_zero_or_pos (Nat.max u v) with hw | hw
  · rw [hw, sigmaSet_zero, univ_zero]
    exact truthVal_mem_univZero _
  · have hw' : Nat.max u v ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    rw [sigmaSet_pos hw']
    exact (univ_isTGUniverse hw').sigmaPairs_mem
      (univ_mono (Nat.le_max_left u v) A hA)
      (fun x hx => univ_mono (Nat.le_max_right u v) _ (hB x hx))

end Setlec.TG
