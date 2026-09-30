--#export PEqL.rec

/- Corner case, the GOOD half (positivity through a
   BASIS container): the block `PEqL` with its would-be nested occurrence
   pointed at the unrelated type `LPinE`.  The forged twin
   `corner_nestpos_eqlocal_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `LPinE` to `PEqL` inside `PEqL`'s block, giving
   `PEqL | mk : (h : PEqL) → @Eq PEqL h h → PEqL` — the pinned `Eq` at a parameter `a := h`, a constructor field.
   Official (Lean v4.29.1, the block written in Lean) REJECTS it:
   "(kernel) invalid nested inductive datatype 'Eq', nested inductive datatypes parameters cannot contain local variables.".  The positivity function reads `Eq` from the
   environment like any stored inductive (no basis exclusion) and
   reaches the same verdict. -/

inductive LPinE : Prop where
  | pin : LPinE
inductive PEqL : Prop where
  | base : PEqL
  | mk : (h : LPinE) → @Eq LPinE h h → PEqL
