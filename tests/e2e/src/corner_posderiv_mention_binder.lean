--#export BT.rec BT.rec_1
/- Corner case (lane POSDERIV, the item-9 adversarial pass for the
   MEMBER-MENTION check on outside recursor majors): the auxiliary
   major `PC (BT → False)` mentions the member `BT` only in a Π binder's
   DOMAIN inside its parameter.  Official's `is_nested` (`find` over
   the parameter, inductive.cpp v4.34.0 :1037–1049) descends into binder
   domains, so it generates `BT.rec_1` on `PC (BT → False)` (the
   container has no field, so the negative occurrence is replaced whole
   by the auxiliary type and never reaches `check_positivity`).
   Official 0. -/
inductive PC (p : Prop) : Type where
  | mk : PC p
inductive BT where
  | leaf : BT
  | mk : PC (BT → False) → BT
