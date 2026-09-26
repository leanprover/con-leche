module

public import ConLeche.Term.Subst

@[expose] public section

/-!
# Types of the built-in constants

The smart constructors for the built-in constants' `Term` types are
what the denotation function emits (`ConLeche/Verify/Denote.lean`) and what
`ConLeche/Semantics/BasisType.lean`, `ConLeche/SetModel/Value.lean` and
`ConLeche/Model/Capstone.lean` read.
-/

namespace ConLeche.Term

open Term

/-- Level lookup with a `0` default. -/
def lv (us : List Nat) (i : Nat) : Nat := us.getD i 0

/-! ## Smart constructors -/

/-- `PUnit.{u}` -/
def punitT (u : Nat) : Term := .const .punit [u]

/-- `Empty.{u}` (level-polymorphic: `Empty.{0}` is `False`) -/
def emptyT (u : Nat) : Term := .const .empty [u]

/-! ## The block carrier's tuple spelling (task #315, the uniform route)

`lfpTuple k` binds ONE tuple of index sets and ONE operator on the
tuple of families, so its type mentions two right-nested pair towers —
`⟨Sort u_0, …, Sort u_{k-1}⟩` and `⟨I_0 → Sort w, …, I_{k-1} → Sort w⟩`
— and the members' index sets are read off the first by the uniform
projection family.  Both towers are NON-dependent: component `m` may
mention the ambient tuple variable but never an earlier component, so
the former takes the components **already lifted to their own depth**
(component `m` sits under `m` of the tower's fibre binders). -/

/-- An upper bound for every level a list mentions (`0` past its
end, so the bound is global in the index — which is what a tower's
formation premise wants). -/
def levMax (us : List Nat) : Nat := us.foldr Nat.max 0

theorem lv_le_levMax : ∀ (us : List Nat) (m : Nat), lv us m ≤ levMax us
  | [], m => by simp [lv, levMax]
  | u :: us, 0 => by
    show u ≤ Nat.max u (levMax us)
    exact Nat.le_max_left _ _
  | u :: us, m + 1 => by
    show lv us m ≤ Nat.max u (levMax us)
    exact Nat.le_trans (lv_le_levMax us m) (Nat.le_max_right _ _)

/-- The sort of `lfpTuple k`'s index-set tuple `⟨Sort u_0, …⟩`. -/
def tupleIdxSort (us : List Nat) : Nat := levMax us + 1

/-- The sort of `lfpTuple k`'s family tuple `⟨I_0 → Sort w, …⟩`. -/
def tupleFamSort (k : Nat) (us : List Nat) : Nat :=
  Nat.max (levMax us) (lv us k + 1)

end ConLeche.Term
