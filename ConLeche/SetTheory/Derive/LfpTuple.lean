module

public import ConLeche.SetTheory.Derive.LfpFam
import ConLeche.SetTheory.Derive.Graphs
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

**Bekić's section law** (`lfpTuple_eq_section`): member `m`'s
component is the least pre-fixed FAMILY of its own SECTION — the
set-level functor `secF w Is Φ L m` on `famSpace w (Is m)` obtained
by holding the other components at their carriers `L` — so a member of
a block has exactly the single-family datum shape (`lfpFamSet` of a
set-level functor over its own index set), the other members entering
its operator the way parameters do.  The converse is false
(DESIGN §M.58: `(⊤, ⊤, ⊤)` satisfies "each an lfp of its section at the
others" for the cyclic identity operator), which is why the block's
datum records the TUPLE and the section form is a derived law.

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

theorem TupleLe.trans {k : Nat} {Is X Y Z : Nat → V} (h₁ : TupleLe k Is X Y)
    (h₂ : TupleLe k Is Y Z) : TupleLe k Is X Z :=
  fun m hm => (h₁ m hm).trans (h₂ m hm)

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

/-- Componentwise-equal tuples (on the block's positions) are
componentwise equal as sets. -/
theorem tuple_ext {w k : Nat} {Is X Y : Nat → V} (hX : InTupleSpace w k Is X)
    (hY : InTupleSpace w k Is Y) (h : ∀ m, m < k → ∀ i, i ∈ˢ Is m → app (X m) i = app (Y m) i) :
    ∀ m, m < k → X m = Y m :=
  fun m hm => famSpace_ext (hX m hm) (hY m hm) (h m hm)

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

/-- The least pre-fixed tuple is closed, as a tuple. -/
theorem lfpTuple_isClosed (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ) :
    IsClosedTuple w k Is Φ (lfpTuple w k Is Φ) :=
  ⟨lfpTuple_mem w k Is Φ, lfpTuple_closed h hmono⟩

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

/-- **Simultaneous structural induction**: a family of properties, one
per member, closed under the functor on the carrier holds on the whole
carrier. -/
theorem lfpTuple_induction (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (P : Nat → V → V → Prop)
    (hP : ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x,
      x ∈ˢ app (Φ (sepTuple w k Is Φ P) m) i → P m i x) :
    ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ m) i → P m i x := by
  intro m hm i hi x hx
  have hSmem : InTupleSpace w k Is (sepTuple w k Is Φ P) := fun m hm =>
    graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpTuple_mem w k Is Φ m hm) hi)
  have hSle : TupleLe k Is (sepTuple w k Is Φ P) (lfpTuple w k Is Φ) := by
    intro m hm i hi y hy
    unfold sepTuple at hy
    rw [app_graph hi] at hy
    exact (mem_sep.mp hy).1
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

/-! ## Bekić: a member's component is the least pre-fixed family of its section -/

/-- The tuple `L` with component `m` replaced by `X`. -/
def updTuple (L : Nat → V) (m : Nat) (X : V) : Nat → V :=
  fun j => if j = m then X else L j

omit [SetTheory V] in
@[simp] theorem updTuple_same (L : Nat → V) (m : Nat) (X : V) : updTuple L m X m = X := by
  simp [updTuple]

omit [SetTheory V] in
theorem updTuple_other (L : Nat → V) {m j : Nat} (X : V) (h : j ≠ m) :
    updTuple L m X j = L j := by
  simp [updTuple, h]

omit [SetTheory V] in
theorem updTuple_self (L : Nat → V) (m : Nat) : updTuple L m (L m) = L := by
  funext j
  by_cases h : j = m
  · subst h; simp [updTuple]
  · simp [updTuple, h]

/-- **The section of `Φ` at component `m`**, holding the other
components at `L`: a set-level functor on `famSpace w (Is m)`. -/
noncomputable def secF (w : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) (L : Nat → V)
    (m : Nat) : V :=
  graph (fun X => Φ (updTuple L m X) m) (famSpace w (Is m))

section Bekic

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}

theorem app_secF {L : Nat → V} {m : Nat} {X : V} (hX : X ∈ˢ famSpace w (Is m)) :
    app (secF w Is Φ L m) X = Φ (updTuple L m X) m :=
  app_graph hX

theorem inTupleSpace_updTuple {L : Nat → V} (hL : InTupleSpace w k Is L) {m : Nat} {X : V}
    (hX : X ∈ˢ famSpace w (Is m)) : InTupleSpace w k Is (updTuple L m X) := by
  intro j hj
  by_cases hjm : j = m
  · subst hjm; simpa [updTuple] using hX
  · rw [updTuple_other L X hjm]; exact hL j hj

/-- The section of a monotone tuple functor is a monotone family
functor. -/
theorem secF_mono (hmono : MonoTuple w k Is Φ) {L : Nat → V} (hL : InTupleSpace w k Is L)
    {m : Nat} (hm : m < k) : MonoFam w (Is m) (secF w Is Φ L m) := by
  intro X Y hX hY hle
  rw [app_secF hX, app_secF hY]
  refine hmono _ _ (inTupleSpace_updTuple hL hX) (inTupleSpace_updTuple hL hY) ?_ m hm
  intro j hj
  by_cases hjm : j = m
  · subst hjm; simpa [updTuple] using hle
  · rw [updTuple_other L X hjm, updTuple_other L Y hjm]; exact FamLe.refl _ _

/-- The section of a space-preserving tuple functor preserves the
family space. -/
theorem secF_maps (hmaps : MapsTuple w k Is Φ) {L : Nat → V} (hL : InTupleSpace w k Is L)
    {m : Nat} (hm : m < k) : MapsFam w (Is m) (secF w Is Φ L m) := by
  intro X hX
  rw [app_secF hX]
  exact hmaps _ (inTupleSpace_updTuple hL hX) m hm

/-- The carrier's `m`-th component is a closed family for its
section. -/
theorem lfpTuple_closedFam_secF (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    {m : Nat} (hm : m < k) :
    IsClosedFam w (Is m) (secF w Is Φ (lfpTuple w k Is Φ) m) (lfpTuple w k Is Φ m) := by
  refine ⟨lfpTuple_mem w k Is Φ m hm, ?_⟩
  rw [app_secF (lfpTuple_mem w k Is Φ m hm), updTuple_self]
  exact lfpTuple_closed h hmono m hm

/-- **Bekić's section law.**  Member `m`'s component of the least
pre-fixed tuple is the least pre-fixed family of `m`'s section at the
tuple's own carriers. -/
theorem lfpTuple_eq_section (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    {m : Nat} (hm : m < k) :
    lfpTuple w k Is Φ m = lfpFamSet w (Is m) (secF w Is Φ (lfpTuple w k Is Φ) m) := by
  have hLmem := lfpTuple_mem w k Is Φ
  have hcl : ∃ L', IsClosedFam w (Is m) (secF w Is Φ (lfpTuple w k Is Φ) m) L' :=
    ⟨_, lfpTuple_closedFam_secF h hmono hm⟩
  have hSmem := lfpFamSet_mem w (Is m) (secF w Is Φ (lfpTuple w k Is Φ) m)
  refine famSpace_ext (hLmem m hm) hSmem fun i hi => Subset.antisymm ?_ ?_
  · -- the carrier lies in the section's lfp: the updated tuple is closed
    have hupd : IsClosedTuple w k Is Φ
        (updTuple (lfpTuple w k Is Φ) m
          (lfpFamSet w (Is m) (secF w Is Φ (lfpTuple w k Is Φ) m))) := by
      refine ⟨inTupleSpace_updTuple hLmem hSmem, fun j hj => ?_⟩
      by_cases hjm : j = m
      · subst hjm
        rw [updTuple_same]
        have := lfpFamSet_closed hcl (secF_mono hmono hLmem hj)
        rwa [app_secF hSmem] at this
      · rw [updTuple_other _ _ hjm]
        refine FamLe.trans ?_ (lfpTuple_closed h hmono j hj)
        refine hmono _ _ (inTupleSpace_updTuple hLmem hSmem) hLmem ?_ j hj
        intro j' hj'
        by_cases hj'm : j' = m
        · subst hj'm
          rw [updTuple_same]
          exact lfpFamSet_le (lfpTuple_closedFam_secF h hmono hj')
        · rw [updTuple_other _ _ hj'm]; exact FamLe.refl _ _
    have := lfpTuple_le hupd m hm i hi
    rwa [updTuple_same] at this
  · exact lfpFamSet_le (lfpTuple_closedFam_secF h hmono hm) i hi

end Bekic

end ConLeche.SetTheory

/-! ## A single family is the one-member block -/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The one-member tuple functor of a set-level family functor `F`:
component `0` is `app F` at the tuple's component `0`. -/
noncomputable def oneTuple (F : V) : (Nat → V) → Nat → V := fun X _ => app F (X 0)

theorem isClosedTuple_one_iff {w : Nat} {I F : V} {X : Nat → V} :
    IsClosedTuple w 1 (fun _ => I) (oneTuple F) X ↔ IsClosedFam w I F (X 0) := by
  constructor
  · rintro ⟨hX, hle⟩
    exact ⟨hX 0 Nat.zero_lt_one, hle 0 Nat.zero_lt_one⟩
  · rintro ⟨hX, hle⟩
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
      exact hX
    · obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
      exact hle

/-- **A single family IS the one-member block**: `lfpFamSet` is the
`k = 1` case of `lfpTuple`, with no hypothesis at all. -/
theorem lfpTuple_one (w : Nat) (I F : V) :
    lfpTuple w 1 (fun _ => I) (oneTuple F) 0 = lfpFamSet w I F := by
  by_cases h : ∃ L, IsClosedFam w I F L
  · have h' : ∃ L, IsClosedTuple w 1 (fun _ => I) (oneTuple F) L :=
      ⟨fun _ => Classical.choose h, isClosedTuple_one_iff.mpr (Classical.choose_spec h)⟩
    refine famSpace_ext (lfpTuple_mem w 1 (fun _ => I) (oneTuple F) 0 Nat.zero_lt_one)
      (lfpFamSet_mem w I F) fun i hi => ?_
    apply SetTheory.ext
    intro x
    rw [mem_app_lfpTuple h' hi, mem_app_lfpFamSet h hi]
    constructor
    · intro hx L hL
      exact hx (fun _ => L) (isClosedTuple_one_iff.mpr hL)
    · intro hx X hX
      exact hx (X 0) (isClosedTuple_one_iff.mp hX)
  · have h' : ¬ ∃ L, IsClosedTuple w 1 (fun _ => I) (oneTuple F) L := fun ⟨L, hL⟩ =>
      h ⟨L 0, isClosedTuple_one_iff.mp hL⟩
    rw [lfpTuple_of_not h', lfpFamSet_of_not h]

end ConLeche.SetTheory
