--#export Tr.rec Tr.rec_1

/- PRIMREC/NESTHOME: the rose tree, `Tr : Type` nested in `List` — the
   member's recursor and the auxiliary one for `List Tr` calling each
   other (the hot layer).  Official 0.  Target 0. -/

inductive Tr : Type where
  | node (n : Nat) (cs : List Tr) : Tr
