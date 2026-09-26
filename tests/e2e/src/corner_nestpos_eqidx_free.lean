--#export PEqI.rec

/- Corner case, the GOOD half (positivity through a
   BASIS container): the block `PEqI` with its would-be nested occurrence
   pointed at the unrelated type `IPinE`.  The forged twin
   `corner_nestpos_eqidx_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `IPinE` to `PEqI` inside `PEqI`'s block, giving
   `PEqI | mk : @Eq Prop PEqI PEqI → PEqI` — the pinned `Eq` with the member in the INDEX argument.
   Official (Lean v4.29.1, the block written in Lean) REJECTS it:
   "(kernel) arg #1 of 'PEqI.mk' contains a non valid occurrence of the datatypes being declared".  The positivity function reads `Eq` from the
   environment like any stored inductive (no basis exclusion) and
   reaches the same verdict. -/

inductive IPinE : Prop where
  | pin : IPinE
inductive PEqI : Prop where
  | base : PEqI
  | mk : @Eq Prop IPinE IPinE → PEqI
