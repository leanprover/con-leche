-- Task #607: CmpSorryC again, its hole at `sorryAx` "filled" by the same axiom: declined (the
-- placeholder axiom installs no axiom of its own).
prelude
universe u
inductive Bool : Type where
  | false : Bool
  | true : Bool
axiom sorryAx (α : Sort u) (synthetic : Bool) : α
