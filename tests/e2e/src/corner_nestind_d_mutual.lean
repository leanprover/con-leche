--#export TM.rec TM.rec_1 TM.rec_2

/- Corner case (lane NESTIND, ruling (D), item-9 adversarial pass): a
   MUTUAL container group `AM`/`BM` with a reflexive field; at each class the
   whole group at the instantiation is abstracted.  Official 0.  Target 0.
   Today 2 (the modeller declines). -/

mutual
inductive AM (α : Type) : Type where
  | a0 : AM α
  | a (x : α) (b : BM α) : AM α
inductive BM (α : Type) : Type where
  | b (a : AM α) (f : Nat → AM α) : BM α
end
inductive TM : Type where
  | node (c : AM TM) : TM
