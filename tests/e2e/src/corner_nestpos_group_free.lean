--#export GT.rec

/- Corner case, the GOOD half (positivity through
   containers): the block `GT` with its would-be nested occurrence
   pointed at the unrelated type `GPin` — an ordinary, non-nested
   block every checker accepts.  The forged twin
   `corner_nestpos_group_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `GPin` to `GT` inside `GT`'s block, giving
   a container whose MUTUAL GROUP has an UNREACHED member negative in the parameter: `GT` nests through `GC1` only, but official copies every member of `GC1`'s group (`I_val->get_all()`, inductive.cpp:1009), and `GC2`'s copy `(GT → Nat) → …` is negative.
   Official (Lean v4.29.1 and v4.34.0, the block written in Lean)
   REJECTS it, and so does the positivity function (it walks every
   member of the recorded group): "(kernel) arg #1 of '_nested.GC2_2.mk' has a non positive occurrence of the datatypes being declared". -/

mutual
inductive GC1 (α : Type) where
  | mk : α → GC1 α
inductive GC2 (α : Type) where
  | mk : (α → Nat) → GC2 α
end
inductive GPin where
  | pin : GPin
inductive GT where
  | leaf : GT
  | mk : GC1 GPin → GT
