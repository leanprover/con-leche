import Setlec.SetTheory.Derive.Graphs

/-!
# The dependent product and abstraction, with the level-0 truncation

Carneiro §6.2 conventions, as fixed by the `SetTheory` interface:

* `pi 0 A B` is the truth value `[∀ x ∈ A, B x inhabited]` — `Prop` is
  impredicative and proof irrelevance immediate;
* `pi (v+1) A B` is the set of dependent function graphs (`piSet`);
* `lam 0 A F = pt`, `lam (v+1) A F = graph F A`.

The universe-membership laws are stated against `univZero` (level 0)
and against an arbitrary Grothendieck universe (level ≠ 0); the tower
arithmetic (`Nat.max`, cumulativity) happens in `Derive/Univ.lean` and
`Basic.lean`.  Laws whose target mentions `univ v` only in the
`v = 0` case take that case's premise as `v = 0 → … ∈ˢ univZero`
(`app_mem'`/`app_lam'`; the interface-shaped `app_mem`/`app_lam` with
the unconditional `univ v` premise live in `Basic.lean`).
-/

namespace Setlec.SetTheory

universe u

variable {V : Type u} [SetTheory V]

open Classical in
/-- The dependent product at codomain sort `v` (see module docs). -/
noncomputable def pi (v : Nat) (A : V) (B : V → V) : V :=
  if v = 0 then truthVal (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) else piSet A B

/-- Abstraction at codomain sort `v` (see module docs). -/
noncomputable def lam (v : Nat) (A : V) (F : V → V) : V :=
  if v = 0 then pt else graph F A

theorem pi_zero {A : V} {B : V → V} :
    pi 0 A B = truthVal (∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) := by
  unfold pi; exact if_pos rfl

theorem pi_pos {v : Nat} (hv : v ≠ 0) {A : V} {B : V → V} :
    pi v A B = piSet A B := by
  unfold pi; exact if_neg hv

theorem lam_zero {A : V} {F : V → V} : lam 0 A F = (pt : V) := by
  unfold lam; exact if_pos rfl

theorem lam_pos {v : Nat} (hv : v ≠ 0) {A : V} {F : V → V} :
    lam v A F = graph F A := by
  unfold lam; exact if_neg hv

theorem pi_congr {v : Nat} {A : V} {B B' : V → V}
    (h : ∀ x, x ∈ˢ A → B x = B' x) : pi v A B = pi v A B' := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [pi_zero, pi_zero]
    exact truthVal_congr
      ⟨fun hi x hx => h x hx ▸ hi x hx, fun hi x hx => (h x hx).symm ▸ hi x hx⟩
  · rw [pi_pos (Nat.pos_iff_ne_zero.mp hv), pi_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact piSet_congr h

theorem lam_congr {v : Nat} {A : V} {F F' : V → V}
    (h : ∀ x, x ∈ˢ A → F x = F' x) : lam v A F = lam v A F' := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lam_zero, lam_zero]
  · rw [lam_pos (Nat.pos_iff_ne_zero.mp hv), lam_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact graph_congr h

/-- Introduction: fibre-wise members abstract into the product.  (For
`v = 0` the premise itself witnesses every fibre inhabited.) -/
theorem lam_mem {v : Nat} {A : V} {F B : V → V}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : lam v A F ∈ˢ pi v A B := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lam_zero, pi_zero]
    exact pt_mem_truthVal fun x hx => ⟨F x, hF x hx⟩
  · rw [lam_pos (Nat.pos_iff_ne_zero.mp hv), pi_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact graph_mem_piSet hF

/-- Inhabitants of Prop-valued products are the proof point. -/
theorem mem_pi_zero {A f : V} {B : V → V} (hf : f ∈ˢ pi 0 A B) : f = pt := by
  rw [pi_zero] at hf
  exact eq_pt_of_mem_truthVal hf

/-- Elimination: application stays in the fibre.  The fibre premise is
needed only at `v = 0`, where fibres must be truth values. -/
theorem app_mem' {v : Nat} {A f a : V} {B : V → V}
    (hf : f ∈ˢ pi v A B) (ha : a ∈ˢ A)
    (hB0 : v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) : app f a ∈ˢ B a := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · have hfp : f = pt := mem_pi_zero hf
    rw [pi_zero] at hf
    obtain ⟨y, hy⟩ := of_mem_truthVal hf a ha
    rw [hfp, app_pt]
    rwa [eq_pt_of_mem_univZero (hB0 rfl a ha) hy] at hy
  · rw [pi_pos (Nat.pos_iff_ne_zero.mp hv)] at hf
    exact app_mem_of_mem_piSet hf ha

/-- Beta, conditional on membership. -/
theorem app_lam' {v : Nat} {A a : V} {F B : V → V}
    (ha : a ∈ˢ A) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x)
    (hB0 : v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) :
    app (lam v A F) a = F a := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lam_zero, app_pt]
    exact (eq_pt_of_mem_univZero (hB0 rfl a ha) (hF a ha)).symm
  · rw [lam_pos (Nat.pos_iff_ne_zero.mp hv)]
    exact app_graph ha

/-- Type-valued abstractions are graphs, never the proof point. -/
theorem lam_ne_pt {v : Nat} {A : V} {F : V → V} (hv : v ≠ 0) :
    lam v A F ≠ pt := by
  rw [lam_pos hv]
  exact graph_ne_pt

/-- Graphs determine their domains. -/
theorem lam_dom {v' v : Nat} {A A' : V} {F : V → V} {B : V → V}
    (hf : lam v' A F ∈ˢ pi v A' B) (hv : v ≠ 0) (hv' : v' ≠ 0) :
    ∀ x, x ∈ˢ A' → x ∈ˢ A := by
  rw [lam_pos hv', pi_pos hv] at hf
  exact graph_dom_of_mem_piSet hf

/-- Eta: a member of a product is the abstraction of its applications. -/
theorem lam_eta {v : Nat} {A f : V} {B : V → V} (hf : f ∈ˢ pi v A B) :
    lam v A (fun x => app f x) = f := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [lam_zero, mem_pi_zero hf]
  · rw [lam_pos (Nat.pos_iff_ne_zero.mp hv)]
    rw [pi_pos (Nat.pos_iff_ne_zero.mp hv)] at hf
    exact eq_graph_app_of_mem_piSet hf

/-- Formation, level 0: a `Prop`-valued product is a truth value. -/
theorem pi_zero_mem_univZero {A : V} {B : V → V} :
    pi 0 A B ∈ˢ (univZero : V) := by
  rw [pi_zero]
  exact truthVal_mem_univZero _

/-- Formation, level ≠ 0: Grothendieck universe closure. -/
theorem _root_.Setlec.IsTGUniverse.pi_mem {U A : V} {B : V → V} {v : Nat}
    (hU : IsTGUniverse (Mem (V := V)) U) (hv : v ≠ 0) (hA : A ∈ˢ U)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ U) : pi v A B ∈ˢ U := by
  rw [pi_pos hv]
  exact hU.piSet_mem hA hB

/- Compiler stubs (see `Derive/Empty.lean`): never executed, no logical
content. -/
private unsafe def piImpl {V : Type u} [SetTheory V] (_v : Nat) (_A : V) (_B : V → V) : V := unsafeCast ()
private unsafe def lamImpl {V : Type u} [SetTheory V] (_v : Nat) (_A : V) (_F : V → V) : V := unsafeCast ()

attribute [implemented_by piImpl] pi
attribute [implemented_by lamImpl] lam

/- Opaque interface operators (see `Derive/Empty.lean`). -/
attribute [irreducible] pi lam

end Setlec.SetTheory
