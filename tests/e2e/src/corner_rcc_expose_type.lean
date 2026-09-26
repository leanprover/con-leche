--#export T T.rec T.rec_1 T.rec_2
/- RCC (lane PRIMREC/RCC): `corner_rcc_expose_prop` at `Type`, the good
   twin of `corner_rcc_create_type` (forged by
   `scripts/mk_rcc_fixtures.py`).  Official 0, today 0. -/
set_option genSizeOf false
inductive Ap (f : Type → Type) (A : Type) : Type where
  | mk : f A → Ap f A
inductive L (α : Type) : Type where
  | nil : L α
  | cons : α → L α → L α
inductive T : Type where
  | mk : Ap L T → T
