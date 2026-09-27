--#export W
/- Corner case (lane FUSELOOP, the fused positivity and recursor checks):
   the good twin `scripts/mk_fuseloop_fixtures.py` forges
   `corner_fuseloop_order_decline` from (the forger's expression indices
   are this export's, taken with `prelude`).  Official 0. -/
prelude
universe u
inductive W (α : Type u) : Type u where
  | mk : (α → W α) → W α
