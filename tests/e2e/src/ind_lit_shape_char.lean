--#export Char.rec
/- A declaration at a literal's name with another shape: `Char` a family in `Type 1`.  The shape a
   literal's meaning reads is checked at the declaration, so this declines there, whether or not the
   stream goes on to use a string literal.  Official accepts it: it reads the names unchecked.  A
   deliberate refusal, in a prelude-only corner.
   official: 0 (run).  con-leche: 2. -/
prelude

inductive Char : Type 1
  | mk
