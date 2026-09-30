--#export TC.rec TC.rec_1

/- Corner case: called fields reaching the container's own class through
   δ (`Id`), ζ (`let`) and a projection ι (`((CC α, Nat) : Type × Type).1`),
   the class literal inside the redex.  Official 0.  Target 0. -/

set_option genSizeOf false
inductive CC (α : Type) : Type where
  | nil : CC α
  | mk (a : α) (z : Id (CC α)) (w : let X := CC α; X) (p : ((CC α, Nat) : Type × Type).1) : CC α
inductive TC : Type where
  | node (c : CC TC) : TC
