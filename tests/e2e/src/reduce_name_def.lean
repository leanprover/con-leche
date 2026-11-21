prelude
-- A definition at a compiler-trust name (`Lean.reduceBool`), of a propositional type.  A file
-- without Lean's `Init` may declare it, and Lean accepts it; con-leche reserves the name to the
-- opaque constant of the pin's shape, as it reserves `Nat.add` to the pinned definition, and
-- rejects the declaration (exit 1), a reject Lean does not make.  Target verdict: 1.
inductive T : Prop
  | intro
def Lean.reduceBool : T := T.intro
