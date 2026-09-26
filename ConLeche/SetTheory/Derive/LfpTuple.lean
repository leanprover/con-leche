module

public import ConLeche.SetTheory.Derive.LfpFam
@[expose] public section

/-!
# Least pre-fixed points of TUPLE functors, and Bekić's section law (task #315)

The carrier of a block of `k` inductive families `T₀ … T_{k-1}` is the
simultaneous least pre-fixed point of its constructor-tower functor
acting on **tuples of families** — a meta-level tuple `X : Nat → V`
whose `m`-th component (`m < k`) is a family over member `m`'s own
index-tuple set `Is m` (`famSpace w (Is m)`), ordered componentwise
(`TupleLe`).  No member tag enters any index set: the tuple is a
meta-level object, its components are the members' own families.
This is `LfpFam.lean` componentwise:

    lfpTuple w k Is Φ m = graph (i ↦ {x ∈ app (L₀ m) i | ∀ closed X, x ∈ app (X m) i}) (Is m)

over a classically chosen closed tuple `L₀` (the empty tuple when
there is none — TOTAL, as `lfpFamSet` is).  Under a closed tuple and
monotonicity the least pre-fixed tuple is a fixed point
(`lfpTuple_eq`) and supports simultaneous structural induction
(`lfpTuple_induction`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The tuple space and its order -/

/-- The tuple lies in the product of the members' family spaces
(positions `≥ k` are unconstrained junk). -/
def InTupleSpace (w k : Nat) (Is : Nat → V) (X : Nat → V) : Prop :=
  ∀ m, m < k → X m ∈ˢ famSpace w (Is m)

/-- The componentwise order on tuples of families. -/
def TupleLe (k : Nat) (Is : Nat → V) (X Y : Nat → V) : Prop :=
  ∀ m, m < k → FamLe (Is m) (X m) (Y m)

theorem TupleLe.refl (k : Nat) (Is X : Nat → V) : TupleLe k Is X X :=
  fun m _ => FamLe.refl (Is m) (X m)


/-- A `Φ`-closed tuple: a pre-fixed point of `Φ` in the tuple space. -/
def IsClosedTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) (X : Nat → V) : Prop :=
  InTupleSpace w k Is X ∧ TupleLe k Is (Φ X) X

/-- Monotonicity of a tuple functor on the tuple space. -/
def MonoTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Prop :=
  ∀ X Y, InTupleSpace w k Is X → InTupleSpace w k Is Y → TupleLe k Is X Y →
    TupleLe k Is (Φ X) (Φ Y)

/-- The functor maps the tuple space into itself. -/
def MapsTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Prop :=
  ∀ X, InTupleSpace w k Is X → InTupleSpace w k Is (Φ X)


/-! ## The least pre-fixed tuple -/

open Classical in
/-- **The least pre-fixed tuple of `Φ`** — componentwise, fibrewise the
intersection of the closed tuples when there is one (separated from a
chosen closed tuple), the empty tuple otherwise. -/
noncomputable def lfpTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Nat → V :=
  fun m =>
    if h : ∃ L, IsClosedTuple w k Is Φ L then
      graph (fun i => sep (app (Classical.choose h m) i)
        (fun x => ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i)) (Is m)
    else graph (fun _ => empty) (Is m)

section Laws

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}

theorem lfpTuple_of_not (h : ¬ ∃ L, IsClosedTuple w k Is Φ L) (m : Nat) :
    lfpTuple w k Is Φ m = graph (fun _ => empty) (Is m) := by
  unfold lfpTuple; exact dif_neg h

theorem mem_app_lfpTuple (h : ∃ L, IsClosedTuple w k Is Φ L) {m : Nat} {i x : V}
    (hi : i ∈ˢ Is m) :
    x ∈ˢ app (lfpTuple w k Is Φ m) i ↔ ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i := by
  unfold lfpTuple
  rw [dif_pos h, app_graph hi, mem_sep]
  exact ⟨fun hx => hx.2, fun hx => ⟨hx _ (Classical.choose_spec h), hx⟩⟩

/-- **Leastness**: the least pre-fixed tuple lies below every closed
tuple. -/
theorem lfpTuple_le {X : Nat → V} (hX : IsClosedTuple w k Is Φ X) :
    TupleLe k Is (lfpTuple w k Is Φ) X :=
  fun _ _ _ hi _x hx => (mem_app_lfpTuple ⟨X, hX⟩ hi).mp hx X hX

/-- **Formation, unconditional**: the least pre-fixed tuple is in the
tuple space. -/
theorem lfpTuple_mem (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) :
    InTupleSpace w k Is (lfpTuple w k Is Φ) := by
  intro m hm
  by_cases h : ∃ L, IsClosedTuple w k Is Φ L
  · unfold lfpTuple
    rw [dif_pos h]
    exact graph_mem_famSpace fun _ hi =>
      univ_sep_mem (famSpace_app ((Classical.choose_spec h).1 m hm) hi)
  · rw [lfpTuple_of_not h]
    exact graph_mem_famSpace fun _ _ => empty_mem_univ w

/-- **Closure**: the least pre-fixed tuple is a pre-fixed point. -/
theorem lfpTuple_closed (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ) :
    TupleLe k Is (Φ (lfpTuple w k Is Φ)) (lfpTuple w k Is Φ) := by
  intro m hm i hi x hx
  rw [mem_app_lfpTuple h hi]
  intro X hX
  exact hX.2 m hm i hi x
    (hmono _ _ (lfpTuple_mem w k Is Φ) hX.1 (lfpTuple_le hX) m hm i hi x hx)


/-- The least pre-fixed tuple is a post-fixed point. -/
theorem lfpTuple_fixed (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) :
    TupleLe k Is (lfpTuple w k Is Φ) (Φ (lfpTuple w k Is Φ)) := by
  refine lfpTuple_le ⟨hmaps _ (lfpTuple_mem w k Is Φ), ?_⟩
  exact hmono _ _ (hmaps _ (lfpTuple_mem w k Is Φ)) (lfpTuple_mem w k Is Φ)
    (lfpTuple_closed h hmono)

/-- The fixed-point equation, componentwise and fibrewise. -/
theorem app_lfpTuple_eq (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) {m : Nat} (hm : m < k) {i : V} (hi : i ∈ˢ Is m) :
    app (Φ (lfpTuple w k Is Φ) m) i = app (lfpTuple w k Is Φ m) i :=
  Subset.antisymm (lfpTuple_closed h hmono m hm i hi) (lfpTuple_fixed h hmono hmaps m hm i hi)

/-- The fixed-point equation, componentwise. -/
theorem lfpTuple_eq (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) {m : Nat} (hm : m < k) :
    Φ (lfpTuple w k Is Φ) m = lfpTuple w k Is Φ m :=
  famSpace_ext (hmaps _ (lfpTuple_mem w k Is Φ) m hm) (lfpTuple_mem w k Is Φ m hm)
    fun _ hi => app_lfpTuple_eq h hmono hmaps hm hi

/-- The tuple of separations of the carrier by a per-member property. -/
noncomputable def sepTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (P : Nat → V → V → Prop) : Nat → V :=
  fun m => graph (fun i => sep (app (lfpTuple w k Is Φ m) i) (P m i)) (Is m)

/-- The separated tuple is in the tuple space. -/
theorem sepTuple_mem (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (P : Nat → V → V → Prop) : InTupleSpace w k Is (sepTuple w k Is Φ P) := fun m hm =>
  graph_mem_famSpace fun _ hi => univ_sep_mem (famSpace_app (lfpTuple_mem w k Is Φ m hm) hi)

/-- The separated tuple lies below the carrier. -/
theorem sepTuple_le (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (P : Nat → V → V → Prop) : TupleLe k Is (sepTuple w k Is Φ P) (lfpTuple w k Is Φ) := by
  intro m hm i hi y hy
  unfold sepTuple at hy
  rw [app_graph hi] at hy
  exact (mem_sep.mp hy).1

/-- **Simultaneous structural induction**: a family of properties, one
per member, closed under the functor on the carrier holds on the whole
carrier. -/
theorem lfpTuple_induction (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (P : Nat → V → V → Prop)
    (hP : ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x,
      x ∈ˢ app (Φ (sepTuple w k Is Φ P) m) i → P m i x) :
    ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ m) i → P m i x := by
  intro m hm i hi x hx
  have hSmem := sepTuple_mem w k Is Φ P
  have hSle := sepTuple_le w k Is Φ P
  have hS : IsClosedTuple w k Is Φ (sepTuple w k Is Φ P) := by
    refine ⟨hSmem, fun m hm i hi y hy => ?_⟩
    show y ∈ˢ app (graph (fun i => sep (app (lfpTuple w k Is Φ m) i) (P m i)) (Is m)) i
    rw [app_graph hi, mem_sep]
    refine ⟨?_, hP m hm i hi y hy⟩
    exact lfpTuple_closed h hmono m hm i hi y
      (hmono _ _ hSmem (lfpTuple_mem w k Is Φ) hSle m hm i hi y hy)
  have := lfpTuple_le hS m hm i hi x hx
  unfold sepTuple at this
  rw [app_graph hi] at this
  exact (mem_sep.mp this).2

end Laws

/-! ## Congruence: the least tuple reads its operator and index sets below `k` only

A block's operator and index sets are DATA, read off whatever
presentation the consumer has; two presentations that agree on the `k`
components the tuple has agree on its carrier.  This is what lets a
reading be replaced by an equal one under the lfp without re-running
the fixed point — the one part of the retired composition module
(`Derive/LfpCompose.lean`, DESIGN 2026-09-21 §6.1) that has consumers.
-/

section Congr

variable {w k : Nat} {Is Is' : Nat → V} {Φ Φ' : (Nat → V) → Nat → V}

/-- Two presentations agreeing below `k` have the same closed tuples. -/
theorem isClosedTuple_congr (hIs : ∀ m, m < k → Is m = Is' m)
    (hΦ : ∀ X, InTupleSpace w k Is X → ∀ m, m < k → Φ X m = Φ' X m) {X : Nat → V} :
    IsClosedTuple w k Is Φ X ↔ IsClosedTuple w k Is' Φ' X := by
  have hsp : InTupleSpace w k Is X ↔ InTupleSpace w k Is' X := by
    constructor
    · intro h m hm; rw [← hIs m hm]; exact h m hm
    · intro h m hm; rw [hIs m hm]; exact h m hm
  constructor
  · rintro ⟨hX, hle⟩
    refine ⟨hsp.mp hX, fun m hm => ?_⟩
    rw [← hIs m hm, ← hΦ X hX m hm]; exact hle m hm
  · rintro ⟨hX, hle⟩
    have hX' := hsp.mpr hX
    refine ⟨hX', fun m hm => ?_⟩
    rw [hIs m hm, hΦ X hX' m hm]; exact hle m hm


/-- **The least tuple is a congruence** in the operator (on the tuple
space) and the index sets, below `k`. -/
theorem lfpTuple_congr (hIs : ∀ m, m < k → Is m = Is' m)
    (hΦ : ∀ X, InTupleSpace w k Is X → ∀ m, m < k → Φ X m = Φ' X m) {m : Nat} (hm : m < k) :
    lfpTuple w k Is Φ m = lfpTuple w k Is' Φ' m := by
  have hcl : (∃ L, IsClosedTuple w k Is Φ L) ↔ ∃ L, IsClosedTuple w k Is' Φ' L :=
    ⟨fun ⟨L, hL⟩ => ⟨L, (isClosedTuple_congr hIs hΦ).mp hL⟩,
      fun ⟨L, hL⟩ => ⟨L, (isClosedTuple_congr hIs hΦ).mpr hL⟩⟩
  by_cases h : ∃ L, IsClosedTuple w k Is Φ L
  · have h' := hcl.mp h
    refine famSpace_ext (lfpTuple_mem w k Is Φ m hm) (by rw [hIs m hm]; exact lfpTuple_mem w k Is' Φ' m hm)
      fun i hi => ?_
    apply SetTheory.ext
    intro x
    rw [mem_app_lfpTuple h hi, mem_app_lfpTuple h' (by rw [← hIs m hm]; exact hi)]
    constructor
    · intro hx X hX; exact hx X ((isClosedTuple_congr hIs hΦ).mpr hX)
    · intro hx X hX; exact hx X ((isClosedTuple_congr hIs hΦ).mp hX)
  · rw [lfpTuple_of_not h, lfpTuple_of_not (fun h' => h (hcl.mpr h')), hIs m hm]

end Congr

end ConLeche.SetTheory

/-! ## A single family is the one-member block -/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]


end ConLeche.SetTheory
