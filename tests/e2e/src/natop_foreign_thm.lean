--#export uses

/- Task #480: the literal fast path fires on a certified operation's name, so only a
   definition may take such a name.  A theorem `Nat.add`, used by a later theorem.
   Official: 0 (run); it fires by name on anything.  con-leche: 1, refused at the
   declaration, by the maintainer's ruling that a foreign declaration at a certified name
   is a reject. -/

prelude

inductive P : Prop
  | i

theorem Nat.add : P := P.i

theorem uses : P := Nat.add
