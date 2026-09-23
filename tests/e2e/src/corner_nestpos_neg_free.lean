--#export NegT.rec

/- Corner case, the GOOD half (lane NESTPOS, positivity through
   containers): the block `NegT` with its would-be nested occurrence
   pointed at the unrelated type `NPin` — an ordinary, non-nested
   block every checker accepts.  The forged twin
   `corner_nestpos_neg_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `NPin` to `NegT` inside `NegT`'s block, giving
   a NEGATIVE occurrence through a container: `NegC α | mk : (α → Nat) → NegC α`, nested at `NegC NegT`.
   Official (Lean v4.29.1 and v4.34.0, the block written in Lean)
   REJECTS it: "(kernel) arg #1 of '_nested.NegC_1.mk' has a non positive occurrence of the datatypes being declared". -/

inductive NegC (α : Type) where
  | mk : (α → Nat) → NegC α
inductive NPin where
  | pin : NPin
inductive NegT where
  | leaf : NegT
  | mk : NegC NPin → NegT
