--#export IdxVT.rec

/- Corner case, the GOOD half (lane NESTPOS, positivity through
   containers): the block `IdxVT` with its would-be nested occurrence
   pointed at the unrelated type `VPin` — an ordinary, non-nested
   block every checker accepts.  The forged twin
   `corner_nestpos_idxval_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `VPin` to `IdxVT` inside `IdxVT`'s block, giving
   a nested instance whose INDEX VALUE mentions the block: `IdxV IdxVT (List.length [h])` with `h : IdxVT` an earlier field (`is_valid_ind_app` on the auxiliary application: an index with a block occurrence).
   Official (Lean v4.29.1 and v4.34.0, the block written in Lean)
   REJECTS it: "(kernel) arg #2 of 'IdxVT.mk' contains a non valid occurrence of the datatypes being declared". -/

inductive IdxV (α : Type) : Nat → Type where
  | z : IdxV α 0
  | s : IdxV α 1
inductive VPin where
  | pin : VPin
inductive IdxVT where
  | leaf : IdxVT
  | mk : (h : VPin) → IdxV VPin (List.length [h]) → IdxVT
