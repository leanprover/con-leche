--#export Id' T.rec T.rec_1 T.rec_2 T.rec_3

/- CLASSCHECK / P2D, the coarser tier at a class fact's kept hole
   (good twin).  `P (RL T) (RL T)`: official's auxiliary types are
   `P (RL T) (RL T)`, `RL T`, `List (RL T)`.  The forged twin
   `corner_classcheck_alias_cyc_bad` (scripts/mk_classcheck_p2d_fixtures.py)
   spells the class `P (RL T) (RL (Id' T))` and keeps the three classes:
   `RL (Id' T)` in `P`'s constructor is then `RL T` only by defeq, and
   `RL T` is a CYCLIC inner class of `P (RL T) (RL (Id' T))` (`RL` is
   younger than `P`) — a hole the class fact keeps free, which the
   syntactic key `P z_ρ (RL (Id' X))` reads TRUE at that position.  The
   class check therefore never identifies an occurrence with a class
   another container's fact keeps free (its group or a cyclic inner
   class).  Official 0 here, 1 on the twin. -/

def Id' (α : Type) : Type := α
inductive P (α β : Type) : Type where
  | mk (a : α) (b : β) : P α β
inductive RL (α : Type) : Type where
  | node (a : α) (cs : List (RL α)) : RL α
inductive T : Type where
  | leaf : T
  | mk (p : P (RL T) (RL T)) : T
