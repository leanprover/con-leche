--#export TI.rec TI.rec_1

/- Corner case (lane NESTIND, ruling (D), item-9 adversarial pass): the
   nested occurrence's index is a redex (`IX TI (not false)`) and the
   container's own recursive field sits at another index.  Official 0.
   Target 0. -/

inductive IX (α : Type) : Bool → Type where
  | t (a : α) (k : IX α false) : IX α true
  | f : IX α false
inductive TI : Type where
  | node (c : IX TI (not false)) : TI
