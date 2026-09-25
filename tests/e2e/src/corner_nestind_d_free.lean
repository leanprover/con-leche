--#export TD.rec TD.rec_1

/- Corner case (lane NESTIND, ruling (D), the charter item-9 adversarial pass):
   the plain nested block the forged twin `corner_nestind_d_redex_bad`
   (`scripts/mk_nestind_d_bad.py`) is made from.  At an outside class the
   target check types every call a second time with the family's CLASSES
   abstracted to holes (`targetClassCallsOk`); here `CD.mk`'s field is the
   literal instantiation `CD TD`.  Official 0; target 0. -/

inductive CD (α : Type) : Type where
  | nil : CD α
  | mk (z : CD α) : CD α
inductive TD : Type where
  | node (c : CD TD) : TD
