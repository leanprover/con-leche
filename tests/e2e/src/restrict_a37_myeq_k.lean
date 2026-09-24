--#export MyEq.rec
/- RESTRICT a37: a user copy of `Eq` (K-target, large eliminator, index). -/
universe u
inductive MyEq (α : Sort u) (a : α) : α → Prop where
  | refl : MyEq α a a
