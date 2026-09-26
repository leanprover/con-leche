--#export NegDT.rec

/- Corner case, the GOOD half (positivity through
   containers): the block `NegDT` with its would-be nested occurrence
   pointed at the unrelated type `DPin` — an ordinary, non-nested
   block every checker accepts.  The forged twin
   `corner_nestpos_negdeep_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `DPin` to `NegDT` inside `NegDT`'s block, giving
   a negative occurrence one container DEEPER: `NegD α | mk : List (α → Nat) → NegD α`, nested at `NegD NegDT` (the instance `List (NegDT → Nat)` is the negative one).
   Official (Lean v4.29.1 and v4.34.0, the block written in Lean)
   REJECTS it: "(kernel) arg #1 of '_nested.List_2.cons' has a non positive occurrence of the datatypes being declared". -/

inductive NegD (α : Type) where
  | mk : List (α → Nat) → NegD α
inductive DPin where
  | pin : DPin
inductive NegDT where
  | leaf : NegDT
  | mk : NegD DPin → NegDT
