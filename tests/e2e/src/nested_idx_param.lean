--#export E.rec
/- A nested occurrence whose container carries an INDEX mentioning the
container's parameter, instantiated at the block's parameter: the
container constructor's result index `@none α` and the field's index
`@none V` both mention a parameter (the cslib reject's minimal shape).
Official ACCEPTS. -/
inductive C (α : Type) (P : Prop) : Option α → Prop
  | mk : P → C α P none
inductive E (V : Type) : Prop where
  | node (h : C V (E V) none) : E V
