module

public import ConLeche.SetModel.NestWide
public import ConLeche.SetModel.WideFlat
@[expose] public section

/-!
# The wide presentation of a nested block, as one record (lane NESTW, L7 step 2)

`WideAt w k Is Φ` packages what `closed_of_wide_groups` (NestWide) and
the flat kit at per-component injections (`UBlock.closedI_of_flat`,
WideFlat) need of a nested block's operator `Φ` on its `k` members at
the level `w`:

* `n` wide keys, the FRAME OCCURRENCES of the positivity walk (NESTW
  F-W3), and the wide block `ub` on `k + n` components whose first `k`
  index sets are the block's (`isLo`);
* the per-component injection `ι` (members: the block's own; keys: the
  container clause's, F-W2), a set of the level at every fitting spine
  (`hι`);
* the flat presentation of every wide constructor (`flat`, U4 at every
  non-ordinary field included: `HoleUnread`);
* the keys grouped by container group, with the containers' clause
  facts (`P`, `hP`);
* the substitution law at the members (`mem`).

`WideAt.closed` is (W) at `w ≠ 0`.  The wide operator is `ub`'s hole
operator at `ι`, at the frame `ρ` and a parameter `α` (a model's wide
fields never read it: a nested occurrence is a plain key hole; the
set-level instances do).
-/

namespace ConLeche.SetTheory

open Tower
open ConLeche.SetModel

universe u

variable {V : Type u} [SetTheory V]

/-- **The wide presentation of the operator `Φ`** (see the module
docstring). -/
structure WideAt (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Type u where
  /-- the number of wide keys -/
  n : Nat
  /-- the wide block: members, then keys -/
  ub : UBlock V w (k + n)
  /-- the members' index sets are the block's -/
  isLo : ∀ m, m < k → ub.Is m = Is m
  /-- the per-component injection -/
  ι : Nat → Nat → List V → V
  /-- the parameter frame the wide fields read -/
  ρ : Nat → V
  /-- the wide block's parameter (unread by a model's wide fields: a
  nested occurrence is a plain key hole; any set of the level) -/
  α : V
  hα : α ∈ˢ (univ w : V)
  /-- the injection is a set of the level at every fitting spine -/
  hι : ∀ X, InTupleSpace w (k + n) ub.Is X → ∀ c, c < k + n → ∀ j ct fs,
    (ub.ctors c)[j]? = some ct → FitsS (teleOf ct.fields ρ X α) fs → ι c j fs ∈ˢ (univ w : V)
  /-- every wide constructor is presented flat -/
  flat : ub.FlatAt ρ α
  /-- the keys, grouped by container group -/
  P : KeyGroups V
  /-- the containers' clause facts at the instantiation -/
  hP : P.Ok w k n ub.Is (uPhiI ub ι ρ α)
  /-- **the substitution law at the members**, `≤` form -/
  mem : ∀ X Y, InTupleSpace w k Is X → InTupleSpace w n (dropTup k ub.Is) Y →
    Dominated k n ub.Is (P.ev w) (catTup k X Y) → TupleLe k Is (Φ X) (uPhiI ub ι ρ α (catTup k X Y))

namespace WideAt

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}

theorem inTupleSpace_lo (W : WideAt w k Is Φ) {X : Nat → V} :
    InTupleSpace w k W.ub.Is X ↔ InTupleSpace w k Is X :=
  ⟨fun h m hm => W.isLo m hm ▸ h m hm, fun h m hm => (W.isLo m hm).symm ▸ h m hm⟩

theorem tupleLe_lo (W : WideAt w k Is Φ) {X Y : Nat → V} :
    TupleLe k W.ub.Is X Y ↔ TupleLe k Is X Y :=
  ⟨fun h m hm => W.isLo m hm ▸ h m hm, fun h m hm => (W.isLo m hm).symm ▸ h m hm⟩

/-- **(W) from the wide presentation**, at `w ≠ 0`. -/
theorem closed (hw : w ≠ 0) (W : WideAt w k Is Φ) : ∃ L, IsClosedTuple w k Is Φ L := by
  obtain ⟨L, hL1, hL2⟩ := closed_of_wide_groups (Φ := Φ)
    (uPhiI_mono W.ub W.ι W.ρ W.hα)
    (UBlock.closedI_of_flat hw W.ub W.ι W.ρ W.α W.hι W.flat) W.P W.hP
    (fun X Y hX hY hd => W.tupleLe_lo.mpr (W.mem X Y (W.inTupleSpace_lo.mp hX) hY hd))
  exact ⟨L, W.inTupleSpace_lo.mp hL1, W.tupleLe_lo.mp hL2⟩

end WideAt

end ConLeche.SetTheory
