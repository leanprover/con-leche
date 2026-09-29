--#export E.rec
/- Control for `nested_idx_param`: the container's index is CLOSED
(mentions no parameter), which the modeller always handled.  Official
ACCEPTS. -/
inductive C (α : Type) (P : Prop) : Nat → Prop
  | mk : P → C α P 0
inductive E (V : Type) : Prop where
  | node (h : C V (E V) 0) : E V
