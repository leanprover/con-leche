-- Task #607: a hole at the placeholder axiom `sorryAx`, in a module without Init.
prelude
universe u
inductive Bool : Type where
  | false : Bool
  | true : Bool
axiom sorryAx (α : Sort u) (synthetic : Bool) : α
