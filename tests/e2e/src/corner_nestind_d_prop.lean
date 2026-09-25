--#export TP.rec TP.rec_1

/- Corner case (lane NESTIND, ruling (D), item-9 adversarial pass): a
   `Prop` block nested in a `Prop` container (the `w = 0` regime of
   finding F12).  Official 0.  Target 0. -/

inductive PL (α : Prop) : Prop where
  | cons (h : α) (t : PL α) : PL α
  | nil : PL α
inductive TP : Prop where
  | node (c : PL TP) : TP
