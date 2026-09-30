--#export TD.rec TD.rec_1

/- Corner case: the plain nested block the forged twin
   `corner_nestind_d_redex_bad` (`scripts/mk_nestind_d_bad.py`) is made
   from; `CD.mk`'s field is the literal instantiation `CD TD`.
   Official 0; target 0. -/

inductive CD (α : Type) : Type where
  | nil : CD α
  | mk (z : CD α) : CD α
inductive TD : Type where
  | node (c : CD TD) : TD
