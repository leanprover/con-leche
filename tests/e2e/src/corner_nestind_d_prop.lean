--#export TP.rec TP.rec_1

/- Corner case: a `Prop` block nested in a `Prop` container (the `w = 0`
   regime).  Official 0.  Target 0. -/

inductive PL (α : Prop) : Prop where
  | cons (h : α) (t : PL α) : PL α
  | nil : PL α
inductive TP : Prop where
  | node (c : PL TP) : TP
