--#export Nat.add.mk

/- Task #480: a family at a certified operation's name.  Official: 0 (run).  con-leche: 1,
   refused at its former, by the maintainer's ruling that a foreign declaration at a
   certified name is a reject. -/

prelude

inductive Nat.add : Type
  | mk : Nat.add
