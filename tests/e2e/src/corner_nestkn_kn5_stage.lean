--#export T.rec T.rec_1 T.rec_2 T.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key-named positivity, adversarial (lane PRIMREC/NESTKN-K2): KN5-merged spellings of
   one key AT STAGE.  Node `G T`'s child `Prod (List (G T)) (List ((fun x => x) (G T)))`:
   the two spellings merge (defeq parameters) into one family; the site spells both
   with its own hole, and the match checks the second position up to defeq. -/

inductive G (α : Type) : Type where
  | leaf : G α
  | node (c : Prod (List (G α)) (List ((fun x => x) (G α)))) : G α
inductive T : Type where
  | leaf : T
  | mk (g : G T) : T
