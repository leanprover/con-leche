--#export E.rec
/- `nested_idx_param` in `Type` (large eliminator: the pack/unpack and
recursor records carry the index too).  Official ACCEPTS. -/
inductive C (α : Type) (β : Type) : Option α → Type
  | mk : β → C α β none
inductive E (V : Type) : Type where
  | leaf : E V
  | node (h : C V (E V) none) : E V
