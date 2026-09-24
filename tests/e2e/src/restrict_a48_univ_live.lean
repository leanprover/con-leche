--#export T.rec
/- RESTRICT a48: a universe-polymorphic NON-nested block (live route): the
   recursor's fresh elimination parameter `u_1` in front of `u`. -/
universe u
inductive T (α : Type u) : Type u where
  | leaf : T α
  | node : T α → T α → T α
