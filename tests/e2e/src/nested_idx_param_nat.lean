--#export E.rec
/- `nested_idx_param` with a `Nat` index whose container-side spelling
mentions the parameter (`@List.length α []`).  Official ACCEPTS. -/
inductive C (α : Type) (P : Prop) : Nat → Prop
  | mk : P → C α P (@List.length α [])
inductive E (V : Type) : Prop where
  | node (h : C V (E V) 0) : E V
