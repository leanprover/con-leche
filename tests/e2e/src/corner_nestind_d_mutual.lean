--#export TM.rec TM.rec_1 TM.rec_2

/- Corner case: a MUTUAL container group `AM`/`BM` with a reflexive
   field.  Official 0.  Target 0. -/

mutual
inductive AM (α : Type) : Type where
  | a0 : AM α
  | a (x : α) (b : BM α) : AM α
inductive BM (α : Type) : Type where
  | b (a : AM α) (f : Nat → AM α) : BM α
end
inductive TM : Type where
  | node (c : AM TM) : TM
