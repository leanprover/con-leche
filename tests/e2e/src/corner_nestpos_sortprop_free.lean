--#export SortP.rec

/- Corner case, the GOOD half (lane NESTPOS, positivity through
   containers): the block `SortP` with its would-be nested occurrence
   pointed at the unrelated type `PPin` — an ordinary, non-nested
   block every checker accepts.  The forged twin
   `corner_nestpos_sortprop_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `PPin` to `SortP` inside `SortP`'s block, giving
   a MIXED-SORT nested block the other way: the `Prop` block `SortP` through the `Type` container `PLift`.
   Official (Lean v4.29.1 and v4.34.0, the block written in Lean)
   REJECTS it: "(kernel) mutually inductive types must live in the same universe". -/

inductive PPin : Prop where
  | pin : PPin
inductive SortP : Prop where
  | leaf : SortP
  | mk : PLift PPin → SortP
