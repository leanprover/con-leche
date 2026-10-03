module

public import Fragment.Univ

@[expose] public section

/-!
# The least fixed point inside the set theory

The family of an inductive block is the least fixed point of its
operator — but a *set-sized* one.  A family here is a function
`W : ι → V` from a Lean-level index type (parameters and indices,
say) to sets, its fibres; the operator `Φ : (ι → V) → ι → V` produces
sets from families.  "In the universe" is fibrewise (`InUniv`), the
order is fibrewise inclusion (`FamLe`), and a family is **closed**
when it is in the universe and a pre-fixed point of `Φ`
(`IsClosedFam`).

**The least fixed point** `lfpFamSet n Φ` is the intersection of all
closed families, taken *inside the set theory*: a closed family `L₀`
is chosen (classically), and the fibre at `i` is the separation of
`L₀ i` by "a member of every closed family's fibre at `i`" — a member
of the universe because `L₀ i` is (`sep_mem_univ`).  When there is no
closed family it is the empty family, so the definition is total.
Under a closed family and monotonicity it is the least closed family
(`lfpFamSet_least`), a fixed point (`lfpFamSet_eq`), and supports
induction (`lfpFamSet_induction`): a property closed under `Φ` on the
family's separation by it holds on the family.  The closed family
comes from accessibility (`closed_of_acc`, `Access.lean`).

Con-leche: `lfpFamSet` (`ConLeche/SetTheory/Derive/LfpFam.lean`) for
one family and `lfpTuple` (`LfpTuple.lean`) for a tuple of them, where
a family is a *graph* over an index set and the theorems read through
`app`; the fragment's Lean-level index type drops the graphs.  The
names and the order of the theorems follow `LfpTuple.lean`:
`InTupleSpace`/`InUniv`, `TupleLe`/`FamLe`, `IsClosedTuple`/
`IsClosedFam`, `MonoTuple`/`MonoFam`, `MapsTuple`/`MapsFam`,
`lfpTuple_le`/`lfpFamSet_least`, `lfpTuple_mem`/`lfpFamSet_mem`,
`lfpTuple_closed`, `lfpTuple_fixed`, `lfpTuple_eq`, `sepTuple`/
`sepFam`, `lfpTuple_induction`/`lfpFamSet_induction`.
-/

namespace Fragment
open SetLib UnivLib

universe u v

variable {V : Type u} [UnivLib V] {ι : Type v}

/-! ## Families and operators -/

/-- A family of members of `univ n`.  Con-leche: `InTupleSpace`,
`ConLeche/SetTheory/Derive/LfpTuple.lean`. -/
def InUniv (n : Nat) (W : ι → V) : Prop := ∀ i, W i ∈ˢ (univ n : V)

/-- Fibrewise inclusion of families.  Con-leche: `TupleLe`. -/
def FamLe (W W' : ι → V) : Prop := ∀ i, W i ⊆ˢ W' i

theorem FamLe.refl (W : ι → V) : FamLe W W := fun i => Sub.refl (W i)

theorem FamLe.trans {W W' W'' : ι → V} (h₁ : FamLe W W') (h₂ : FamLe W' W'') : FamLe W W'' :=
  fun i => (h₁ i).trans (h₂ i)

/-- A **closed family** of `Φ`: in the universe, and a pre-fixed point.
Con-leche: `IsClosedTuple`. -/
def IsClosedFam (n : Nat) (Φ : (ι → V) → ι → V) (W : ι → V) : Prop :=
  InUniv n W ∧ FamLe (Φ W) W

/-- Monotonicity of an operator on families in the universe.
Con-leche: `MonoTuple`. -/
def MonoFam (n : Nat) (Φ : (ι → V) → ι → V) : Prop :=
  ∀ W W', InUniv n W → InUniv n W' → FamLe W W' → FamLe (Φ W) (Φ W')

/-- The operator maps families in the universe to families in the
universe.  Con-leche: `MapsTuple`. -/
def MapsFam (n : Nat) (Φ : (ι → V) → ι → V) : Prop :=
  ∀ W, InUniv n W → InUniv n (Φ W)

/-! ## The least fixed point -/

open Classical in
/-- **The least fixed point of `Φ` inside the set theory**: fibrewise
the intersection of the closed families when there is one, separated
from a chosen closed family `L₀`; the empty family otherwise.
Con-leche: `lfpTuple`, `ConLeche/SetTheory/Derive/LfpTuple.lean`. -/
noncomputable def lfpFamSet (n : Nat) (Φ : (ι → V) → ι → V) : ι → V :=
  if h : ∃ L, IsClosedFam n Φ L then
    fun i => sep (Classical.choose h i) fun x => ∀ X, IsClosedFam n Φ X → x ∈ˢ X i
  else fun _ => empty

section Laws

variable {n : Nat} {Φ : (ι → V) → ι → V}

theorem lfpFamSet_of_not (h : ¬ ∃ L, IsClosedFam n Φ L) :
    lfpFamSet n Φ = fun _ => (empty : V) := by
  unfold lfpFamSet; exact dif_neg h

/-- The members of the least fixed point: the members of every closed
family.  Con-leche: `mem_app_lfpTuple`. -/
theorem mem_lfpFamSet (h : ∃ L, IsClosedFam n Φ L) {i : ι} {x : V} :
    x ∈ˢ lfpFamSet n Φ i ↔ ∀ X, IsClosedFam n Φ X → x ∈ˢ X i := by
  simp only [lfpFamSet, dif_pos h, mem_sep]
  exact ⟨fun hx => hx.2, fun hx => ⟨hx _ (Classical.choose_spec h), hx⟩⟩

/-- **Leastness**: the least fixed point lies below every closed
family.  Con-leche: `lfpTuple_le`. -/
theorem lfpFamSet_least {X : ι → V} (hX : IsClosedFam n Φ X) : FamLe (lfpFamSet n Φ) X :=
  fun _ _ hx => (mem_lfpFamSet ⟨X, hX⟩).mp hx X hX

/-- **Formation, unconditional**: the fibres of the least fixed point
are members of the universe.  Con-leche: `lfpTuple_mem`. -/
theorem lfpFamSet_mem (n : Nat) (Φ : (ι → V) → ι → V) : InUniv n (lfpFamSet n Φ) := by
  intro i
  by_cases h : ∃ L, IsClosedFam n Φ L
  · simp only [lfpFamSet, dif_pos h]
    exact sep_mem_univ ((Classical.choose_spec h).1 i)
  · rw [lfpFamSet_of_not h]
    exact empty_mem_univ n

/-- **Closure**: the least fixed point is a pre-fixed point.
Con-leche: `lfpTuple_closed`. -/
theorem lfpFamSet_closed (h : ∃ L, IsClosedFam n Φ L) (hmono : MonoFam n Φ) :
    FamLe (Φ (lfpFamSet n Φ)) (lfpFamSet n Φ) := by
  intro i x hx
  rw [mem_lfpFamSet h]
  intro X hX
  exact hX.2 i x (hmono _ _ (lfpFamSet_mem n Φ) hX.1 (lfpFamSet_least hX) i x hx)

/-- The least fixed point is a post-fixed point.  Con-leche:
`lfpTuple_fixed`. -/
theorem lfpFamSet_fixed (h : ∃ L, IsClosedFam n Φ L) (hmono : MonoFam n Φ) (hmaps : MapsFam n Φ) :
    FamLe (lfpFamSet n Φ) (Φ (lfpFamSet n Φ)) := by
  refine lfpFamSet_least ⟨hmaps _ (lfpFamSet_mem n Φ), ?_⟩
  exact hmono _ _ (hmaps _ (lfpFamSet_mem n Φ)) (lfpFamSet_mem n Φ) (lfpFamSet_closed h hmono)

/-- **The fixed-point equation**, fibrewise.  Con-leche:
`lfpTuple_eq`. -/
theorem lfpFamSet_eq (h : ∃ L, IsClosedFam n Φ L) (hmono : MonoFam n Φ) (hmaps : MapsFam n Φ)
    (i : ι) : Φ (lfpFamSet n Φ) i = lfpFamSet n Φ i :=
  Sub.antisymm (lfpFamSet_closed h hmono i) (lfpFamSet_fixed h hmono hmaps i)

/-- The least fixed point separated by a property, fibrewise.
Con-leche: `sepTuple`. -/
noncomputable def sepFam (n : Nat) (Φ : (ι → V) → ι → V) (P : ι → V → Prop) : ι → V :=
  fun i => sep (lfpFamSet n Φ i) (P i)

theorem sepFam_mem (n : Nat) (Φ : (ι → V) → ι → V) (P : ι → V → Prop) : InUniv n (sepFam n Φ P) :=
  fun i => sep_mem_univ (lfpFamSet_mem n Φ i)

theorem sepFam_le (n : Nat) (Φ : (ι → V) → ι → V) (P : ι → V → Prop) :
    FamLe (sepFam n Φ P) (lfpFamSet n Φ) := fun _ _ hx => (mem_sep.mp hx).1

/-- **Induction**: a property closed under `Φ` on the family's
separation by it holds on the whole family — the separation is a
closed family, so the least fixed point lies below it.  Con-leche:
`lfpTuple_induction`. -/
theorem lfpFamSet_induction (h : ∃ L, IsClosedFam n Φ L) (hmono : MonoFam n Φ) (P : ι → V → Prop)
    (hP : ∀ i x, x ∈ˢ Φ (sepFam n Φ P) i → P i x) :
    ∀ i x, x ∈ˢ lfpFamSet n Φ i → P i x := by
  intro i x hx
  have hS : IsClosedFam n Φ (sepFam n Φ P) := by
    refine ⟨sepFam_mem n Φ P, fun j y hy => mem_sep.mpr ⟨?_, hP j y hy⟩⟩
    exact lfpFamSet_closed h hmono j y
      (hmono _ _ (sepFam_mem n Φ P) (lfpFamSet_mem n Φ) (sepFam_le n Φ P) j y hy)
  exact (mem_sep.mp (lfpFamSet_least hS i x hx)).2

end Laws

/-- **At a proposition no bound is needed**: every member of `univ 0`
is a subset of `{pt}`, so the constant family `{pt}` is closed under
any operator into `univ 0`.  Con-leche: `closedTuple_zero`,
`ConLeche/SetModel/Access.lean`. -/
theorem closedFam_zero {Φ : (ι → V) → ι → V} (hmaps : MapsFam 0 Φ) : ∃ L, IsClosedFam 0 Φ L := by
  have htop : InUniv 0 (fun _ : ι => (one : V)) := fun _ => one_mem_univ_zero
  refine ⟨_, htop, fun i x hx => ?_⟩
  exact mem_one.mpr (eq_pt_of_mem_univ_zero (hmaps _ htop i) hx)

end Fragment
