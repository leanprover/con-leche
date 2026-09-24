module

public import ConLeche.Semantics.Tower.BlockLeafI
public import ConLeche.Semantics.Tower.FixFamI
@[expose] public section

/-!
# The block functor's laws (task #315, the uniform route at `k` members)

`BlockLeafI.lean` spells the block's operator and reads it; this module
proves what the least pre-fixed TUPLE needs of it — monotonicity, that
it preserves the tuple space, a closed tuple, and the fixed-point
equation.  It is `FixFamI.lean` at `k`, and the
generic halves of that file (the X-frame kit, the Π-tower and telescope
lemmas, the terminator, `SlotFit`/`slotSet`) are REUSED rather than
restated: they never mention the family slot's shape, only its value.

What is new at `k`:

* a recursive slot reads the TARGET's component of the family tuple
  (`slotXBI_interp`: `slotSet … (projS c Y)`), so monotonicity is
  componentwise (`MonoTuple`) and the slots' fit
  (`SlotsFitXB`) carries the target;
* the premise bundle `BlockChainsOk` is the k = 1 `XChainsOk` with the
  members quantified and the closed FAMILY replaced by a closed TUPLE;
* the fixed-point equation is per member (`blockFamG_app_eq`), with
  monotonicity and a closed tuple as premises; the member's fibre as the
  tagged union of its STORED constructors is read at the hole chains by
  the override law (`Model/Inductives/BlockHoleFold.lean`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The recursive slot at a family tuple -/

section Slot

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}

/-- **The target's component of a tuple of the family space** is a
family over the target's index tuples. -/
theorem projS_mem_famsSpaceB {c : Nat} (hc : c < k) {Y : V}
    (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) :
    projS c Y ∈ˢ lfpFamSpace V w (idxSet (uf c) ρp (Idss c)) := by
  have := projS_mem_ndTowerSet V (blockR_ne_zero k w uf) k 0 hY c hc
  rwa [Nat.zero_add] at this

end Slot

/-! ## The slots' fit and the functor's premise bundle -/

/-! ## Monotonicity -/

/-! ## The functor's laws -/

section Functor

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- A tuple of the tuple space, tupled up, is in the family space. -/
theorem ndMkTowerSet_mem_famsSpaceB {Xs : Nat → V}
    (hXs : InTupleSpace w k (blockIdx uf ρp Idss) Xs) :
    ndMkTowerSet Xs 0 k ∈ˢ famsSpaceB k w ρp uf Idss :=
  ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0 fun c hc => by
    rw [lfpFamSpace_eq']
    exact hXs c (by omega)

theorem projS_ndMkTowerSet_zero {Xs : Nat → V} {c : Nat} (hc : c < k) :
    projS c (ndMkTowerSet Xs 0 k) = Xs c := by
  rw [projS_ndMkTowerSet k 0 c hc, Nat.zero_add]

theorem app_blockPhi {Chs : Nat → List (List AnnotTerm)} {Xs : Nat → V} {m : Nat} {t : V}
    (ht : t ∈ˢ idxSet (uf m) ρp (Idss m)) :
    SetTheory.app (blockPhiG k w ρp uf Idss Chs Xs m) t
      = blockStepG w ρp Chs m (ndMkTowerSet Xs 0 k) t :=
  app_lamR_pos (Nat.succ_ne_zero w) ht

/-- **The block's operator preserves the tuple space.** -/
theorem blockPhi_maps_of {Chs : Nat → List (List AnnotTerm)}
    (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    MapsTuple w k (blockIdx uf ρp Idss) (blockPhiG k w ρp uf Idss Chs) := by
  intro X hX m hm
  show lamR (w + 1) (idxSet (uf m) ρp (Idss m)) _ ∈ˢ famSpace w (blockIdx uf ρp Idss m)
  rw [← lfpFamSpace_eq']
  exact lamR_mem fun t ht =>
    blockStepG_univ hok (ndMkTowerSet_mem_famsSpaceB hX) hm ht

end Functor

/-! ## Elimination at a stage, and (W) at `w ≠ 0` -/

end ConLeche.Semantics
