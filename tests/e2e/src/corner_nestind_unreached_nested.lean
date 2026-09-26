--#export VT.rec VT.rec_1 VT.rec_2 VT.rec_3

/- Corner case (classes UNREACHED from the block): the block `VT` nests through `VF`, a member of a mutual group
   whose other member `VC1` is itself NESTED (`VC1.mk : VC2 (VC1 α)`).
   Official copies `VF`'s whole group, then the nested occurrence inside
   the copy of `VC1`, and generates recursors on `VC1 VT` and
   `VC2 (VC1 VT)` — both unreached from `VT`'s members, and calling EACH
   OTHER across two DIFFERENT recorded blocks (`VC1`'s group and `VC2`):
   `VC2 (VC1 VT)`'s elements are visited at `VC2`'s frame read at a
   SEPARATED `VC1` tuple.  Official 0. -/
inductive VC2 (β : Type) where
  | nil : VC2 β
  | mk : β → VC2 β
mutual
inductive VC1 (α : Type) where
  | mk : VC2 (VC1 α) → VC1 α
inductive VF (α : Type) where
  | mk : α → VF α
end
inductive VT where
  | leaf : VT
  | mk : VF VT → VT
