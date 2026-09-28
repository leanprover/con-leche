--#export R.rec R.rec_1
/- Corner case (lane RP-ANNOT, F-RPW-1): `corner_rpwhnf_erasedread_member`'s
   shape as a plain container `C`, nested in `R`.  Official 0.  The false
   reject (1) was at `C` itself, a flat block; ours 0 now. -/
set_option genSizeOf false
set_option genInjectivity false
def K2 (β : Type) (_ : β) : Type := β
inductive C (α : Type) : Type where
  | nil : α → C α
  | cons : (x : C α) → K2 (C α) x → C α
inductive R : Type where
  | mk : C R → R
