--#export DT.rec DT.rec_1
/- Corner case (lane POSDERIV, the item-9 adversarial pass for the
   MEMBER-MENTION check on outside recursor majors): the auxiliary major
   `List (K DT)` mentions the member `DT` only under a definition `K`
   that δ-reduces it away (`K _ := Nat`).  Official's `is_nested`
   (`is_nested_inductive_app`, inductive.cpp v4.34.0 :1033–1051) reads
   the parameter `K DT` SYNTACTICALLY, finds `DT`, and generates
   `DT.rec_1` on `List (K DT)`; a check that read the parameter after
   whnf (`Nat`) would refuse it.  Official 0. -/
def K (_ : Type) : Type := Nat
inductive DT where
  | leaf : DT
  | mk : List (K DT) → DT
