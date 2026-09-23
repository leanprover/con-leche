--#export RedT.rec

/- Corner case, the GOOD half (lane NESTPOS, positivity through
   containers): the block `RedT` with its would-be nested occurrence
   pointed at the unrelated type `RPin` — an ordinary, non-nested
   block every checker accepts.  The forged twin
   `corner_nestpos_redex_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `RPin` to `RedT` inside `RedT`'s block, giving
   a container reached only by REDUCTION: `FL RedT` with `FL α := List α` — official locates nested instances syntactically, before any `whnf`, so `FL` is no container and the reduct `List RedT` is a non-member head.
   Official (Lean v4.29.1 and v4.34.0, the block written in Lean)
   REJECTS it (the ONE positivity function ACCEPTS it: an accepted
   superset, charter item 8, D1): "(kernel) arg #1 of 'RedT.mk' contains a non valid occurrence of the datatypes being declared". -/

def FL (α : Type) : Type := List α
inductive RPin where
  | pin : RPin
inductive RedT where
  | leaf : RedT
  | mk : FL RPin → RedT
