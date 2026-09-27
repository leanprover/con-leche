--#export T.rec T.rec_1 T.rec_2 T.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key-named recursor route, KN5 with a SWALLOWED representative (lane PRIMREC/NESTKN-RP):
   the child `Prod (Ph (List T)) (List ((fun x => x) T))` contains `List T` (inner-first,
   the merge class's REPRESENTATIVE, inside the flexible `Ph (List T)`, whose family
   swallows it) and its alias `List ((fun x => x) T)` (defeq, merged).  The match binds
   the family to the ALIAS's spelling; the positivity check walks `List ((fun x => x) T)`
   and never `List T` (`Ph` never uses its parameter). -/

inductive Ph (α : Type) : Type where
  | mk : Nat → Ph α
inductive T : Type where
  | leaf : T
  | mk (c : Prod (Ph (List T)) (List ((fun x => x) T))) : T
