--#export Bool

/- Task #480: a family that literal arithmetic or the basis reads by name, stored at
   a definition: declined, since those readers compare the former's stored type.
   TODO official: 0 (Lean elaborated and its kernel checked this); target 0.
   con-leche: 2. -/

prelude

def T := Type

inductive Bool : T
  | false
  | true
