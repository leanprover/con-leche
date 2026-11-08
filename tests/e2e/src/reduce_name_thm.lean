prelude
-- A theorem at a compiler-trust name (`Lean.reduceNat`).  Lean accepts it in a file without its
-- `Init`; con-leche reserves the name to the opaque constant of the pin's shape and rejects the
-- declaration (exit 1), a reject Lean does not make.  Target verdict: 1.
inductive T : Prop
  | intro
theorem Lean.reduceNat : T := T.intro
