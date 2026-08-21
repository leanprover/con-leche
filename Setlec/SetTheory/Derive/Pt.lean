import Setlec.SetTheory.Derive.Universe

/-!
# The proof point, truth values, `univ 0`, and `eqv`

* `pt := {∅}` — the tagged proof point: the canonical inhabitant of
  every true proposition.  Its element `∅` is empty, while every
  element of a Kuratowski pair is nonempty, so `pt` is never an
  ordered pair and (since graphs are sets of pairs, and nonempty ones
  at that) never a function graph — the tag `Derive/Graphs.lean`
  exploits.  cf. nanodatg `derived/src/anchor.rs`.
* `unitSet := {pt}` — the true truth value, and the model of `PUnit`.
* `univZero := power unitSet = {∅, {pt}}` — the set of truth values,
  Carneiro's `U₀ = {∅, {•}}`; stating it as a power set makes
  "members of `univ 0` are subsets of `{pt}`" definitional, and
  propositional extensionality one application of `ext`.
* `truthVal p` — the truth value of a meta-level proposition, `{pt}`
  if `p` holds and `∅` otherwise (classical); `eqv x y` is
  `truthVal (x = y)`.
-/

namespace Setlec.TG

universe u

variable {V : Type u} [TG V]

/-- The proof point `pt = {∅}`. -/
noncomputable def pt : V := sing empty

theorem mem_pt {z : V} : z ∈ᵗ (pt : V) ↔ z = empty := mem_sing

theorem pt_ne_empty : (pt : V) ≠ empty :=
  ne_empty_of_mem (mem_pt.mpr rfl)

/-- `pt` is not a Kuratowski pair: its element is empty, a pair's
elements are not. -/
theorem pt_ne_kpair (a b : V) : (pt : V) ≠ kpair a b := by
  intro h
  obtain ⟨w, hw⟩ := mem_kpair_nonempty (h ▸ mem_pt.mpr rfl)
  exact not_mem_empty w hw

/-- The canonical singleton `{pt}`: the true truth value. -/
noncomputable def unitSet : V := sing pt

theorem mem_unitSet {z : V} : z ∈ᵗ (unitSet : V) ↔ z = pt := mem_sing

theorem pt_mem_unitSet : (pt : V) ∈ᵗ unitSet := mem_unitSet.mpr rfl

theorem unitSet_ne_empty : (unitSet : V) ≠ empty :=
  ne_empty_of_mem pt_mem_unitSet

/-- The interpretation of `Sort 0`: the set `{∅, {pt}}` of truth
values, stated as the power set of `{pt}`. -/
noncomputable def univZero : V := power unitSet

theorem mem_univZero {T : V} : T ∈ᵗ (univZero : V) ↔ T ⊆ᵗ unitSet :=
  mem_power_iff_subset

/-- Members of `univ 0` have at most the proof point as element. -/
theorem eq_pt_of_mem_univZero {T x : V} (hT : T ∈ᵗ (univZero : V))
    (hx : x ∈ᵗ T) : x = pt :=
  mem_unitSet.mp (mem_univZero.mp hT x hx)

/-- Propositional extensionality: truth values with the same
`pt`-membership are equal. -/
theorem univZero_ext {A B : V} (hA : A ∈ᵗ (univZero : V))
    (hB : B ∈ᵗ (univZero : V)) (hab : pt ∈ᵗ A → pt ∈ᵗ B)
    (hba : pt ∈ᵗ B → pt ∈ᵗ A) : A = B :=
  ext fun z =>
    ⟨fun hz => by
       have h := eq_pt_of_mem_univZero hA hz; subst h; exact hab hz,
     fun hz => by
       have h := eq_pt_of_mem_univZero hB hz; subst h; exact hba hz⟩

open Classical in
/-- The truth value of a meta-level proposition: `{pt}` if it holds,
`∅` otherwise. -/
noncomputable def truthVal (p : Prop) : V := if p then unitSet else empty

theorem mem_truthVal {p : Prop} {z : V} :
    z ∈ᵗ (truthVal p : V) ↔ p ∧ z = pt := by
  unfold truthVal
  split
  · next hp => exact ⟨fun hz => ⟨hp, mem_unitSet.mp hz⟩, fun ⟨_, hz⟩ => hz ▸ pt_mem_unitSet⟩
  · next hp =>
    exact ⟨fun hz => absurd hz (not_mem_empty z), fun ⟨h, _⟩ => absurd h hp⟩

theorem pt_mem_truthVal {p : Prop} (hp : p) : (pt : V) ∈ᵗ truthVal p :=
  mem_truthVal.mpr ⟨hp, rfl⟩

theorem of_mem_truthVal {p : Prop} {z : V} (hz : z ∈ᵗ (truthVal p : V)) : p :=
  (mem_truthVal.mp hz).1

theorem eq_pt_of_mem_truthVal {p : Prop} {z : V} (hz : z ∈ᵗ (truthVal p : V)) :
    z = pt :=
  (mem_truthVal.mp hz).2

theorem truthVal_eq_unitSet {p : Prop} (hp : p) : (truthVal p : V) = unitSet := by
  unfold truthVal; exact if_pos hp

theorem truthVal_eq_empty {p : Prop} (hp : ¬ p) : (truthVal p : V) = empty := by
  unfold truthVal; exact if_neg hp

theorem truthVal_congr {p q : Prop} (h : p ↔ q) :
    (truthVal p : V) = truthVal q := by
  rcases Classical.em p with hp | hp
  · rw [truthVal_eq_unitSet hp, truthVal_eq_unitSet (h.mp hp)]
  · rw [truthVal_eq_empty hp, truthVal_eq_empty (fun hq => hp (h.mpr hq))]

theorem truthVal_mem_univZero (p : Prop) :
    (truthVal p : V) ∈ᵗ univZero := by
  rcases Classical.em p with hp | hp
  · rw [truthVal_eq_unitSet hp]
    exact mem_univZero.mpr (Subset.refl _)
  · rw [truthVal_eq_empty hp]
    exact mem_univZero.mpr (empty_subset _)

/-- Every member of `univ 0` is the truth value of its own
inhabitedness. -/
theorem mem_univZero_eq_truthVal {T : V} (hT : T ∈ᵗ (univZero : V)) :
    T = truthVal (pt ∈ᵗ T) := by
  rcases Classical.em ((pt : V) ∈ᵗ T) with hp | hp
  · rw [truthVal_eq_unitSet hp]
    exact ext fun z => ⟨fun hz => eq_pt_of_mem_univZero hT hz ▸ pt_mem_unitSet,
      fun hz => mem_unitSet.mp hz ▸ hp⟩
  · rw [truthVal_eq_empty hp]
    exact eq_empty fun z hz => hp (eq_pt_of_mem_univZero hT hz ▸ hz)

/-- The truth value of an equality. -/
noncomputable def eqv (x y : V) : V := truthVal (x = y)

theorem eqv_mem_univZero (x y : V) : eqv x y ∈ᵗ (univZero : V) :=
  truthVal_mem_univZero _

theorem eq_of_mem_eqv {a x y : V} (h : a ∈ᵗ eqv x y) : x = y :=
  of_mem_truthVal h

theorem pt_mem_eqv_self (x : V) : (pt : V) ∈ᵗ eqv x x :=
  pt_mem_truthVal rfl

/-- `pt`, `unitSet`, `univZero` and truth values live in every
(inhabited) Grothendieck universe. -/
theorem _root_.Setlec.IsTGUniverse.pt_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ᵗ U) : (pt : V) ∈ᵗ U :=
  hU.sing_mem hy (hU.empty_mem hy)

theorem _root_.Setlec.IsTGUniverse.unitSet_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ᵗ U) : (unitSet : V) ∈ᵗ U :=
  hU.sing_mem hy (hU.pt_mem hy)

theorem _root_.Setlec.IsTGUniverse.univZero_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ᵗ U) : (univZero : V) ∈ᵗ U :=
  hU.power_mem (hU.unitSet_mem hy)

theorem _root_.Setlec.IsTGUniverse.truthVal_mem {U y : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (hy : y ∈ᵗ U) (p : Prop) :
    (truthVal p : V) ∈ᵗ U :=
  hU.transitive (hU.univZero_mem hy) (truthVal_mem_univZero p)

end Setlec.TG
