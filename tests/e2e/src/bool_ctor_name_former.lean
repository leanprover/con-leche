--#export Bool.true.mk

/- Task #480: a family at a `Bool` constructor's name, which the comparisons' fast path
   produces by name.  Official: 0 (run).  con-leche: 1.  A prelude-only corner, stricter than
   official on purpose: nothing else stops a member from being what `Nat.beq 0 0` reduces to. -/

prelude

inductive Bool.true : Type
  | mk : Bool.true
