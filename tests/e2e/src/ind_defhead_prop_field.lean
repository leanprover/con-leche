--#export P.one

/- Task #480: a def-headed `Prop` family with a field that is no proposition stays
   accepted: nothing asks about the sort at the block's install, and no use projects.

   official: 0 (Lean elaborated and its kernel checked this).  con-leche: 0. -/

def MyProp := Prop

inductive P : MyProp
  | mk (n : Nat)

theorem P.one : P := P.mk 1
