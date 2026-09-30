--#export T.rec
/- Corner case (lane RP-ANNOT, F-RPW-1's control): the δ/β-erased read of
   an earlier NON-recursive field (`K2 Nat n`, `n : Nat`) before a
   recursive one.  Official 0, ours 0 (unchanged: the read names no
   member, so the abstraction leaves it alone). -/
set_option genSizeOf false
set_option genInjectivity false
def K2 (β : Type) (_ : β) : Type := β
inductive T : Type where
  | leaf : T
  | mk : (n : Nat) → K2 Nat n → T → T
