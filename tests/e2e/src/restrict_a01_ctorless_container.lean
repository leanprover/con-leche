--#export T.rec T.rec_1
/- RESTRICT a01: nesting through a container with NO constructors.
   Official (kernel) accepts: `E T` is a nested occurrence, the auxiliary
   `_nested.E_1` has no constructors, `T.rec_1` has zero rules.
   Ours accepts too: the install records official's `nparams`, which
   `nestContainer` reads. -/
inductive E (α : Type) : Type
inductive T where
  | mk : E T → T
