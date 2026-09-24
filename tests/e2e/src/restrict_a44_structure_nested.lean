--#export S.rec S.rec_1 S.children S.label
/- RESTRICT a44: a nested STRUCTURE (projections as `.proj` definitions;
   the frontend's projection→rec rewrite at a nested block, NESTPLAN R1). -/
structure S where
  label : Nat
  children : List S
