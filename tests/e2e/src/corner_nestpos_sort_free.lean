--#export SortT.rec

/- Corner case, the GOOD half (lane NESTPOS, positivity through
   containers): the block `SortT` with its would-be nested occurrence
   pointed at the unrelated type `SPin` — an ordinary, non-nested
   block every checker accepts.  The forged twin
   `corner_nestpos_sort_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `SPin` to `SortT` inside `SortT`'s block, giving
   a MIXED-SORT nested block: the `Type` block `SortT` through the `Prop` container `Nonempty`.
   Official (Lean v4.29.1 and v4.34.0, the block written in Lean)
   REJECTS it: "(kernel) mutually inductive types must live in the same universe". -/

inductive SPin where
  | pin : SPin
inductive SortT where
  | leaf : SortT
  | mk : Nonempty SPin → SortT
