--#export TV.rec TV.rec_1

/- Corner case (lane NESTIND, ruling (D), item-9 adversarial pass): an
   INDEXED container `VV α : Nat → Type` nested at `VV TV (n + 2)`; the class
   hole is the instantiation `VV TV`, applied to the index.  Official 0.
   Target 0. -/

inductive VV (α : Type) : Nat → Type where
  | nil : VV α 0
  | cons (n : Nat) (a : α) (v : VV α n) : VV α (n + 1)
inductive TV : Type where
  | node (n : Nat) (v : VV TV (n + 2)) : TV
