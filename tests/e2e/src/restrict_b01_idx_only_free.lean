--#export T.rec

/- RESTRICT b01, the GOOD half: the block `T` with its would-be
   occurrence in a container's INDEX pointed at the unrelated type
   `BPin` — an ordinary, non-nested block every checker accepts.  The
   forged twin `restrict_b01_idx_only_bad` (`scripts/mk_restrict_bad.py`)
   repoints `BPin` to `T` inside `T`'s block, giving `mk : Vi Nat T → T`:
   the member ONLY in a container's index, not a nested occurrence.
   Official (Lean v4.29.1, the block written in Lean) REJECTS it:
   "(kernel) arg #1 of 'T.mk' contains a non valid occurrence of the
   datatypes being declared". -/

inductive Vi (α : Type) : Type → Type where
  | mk : Vi α α
inductive BPin where
  | pin : BPin
inductive T where
  | mk : Vi Nat BPin → T
