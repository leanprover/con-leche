--#export Id' K1 T.rec T.rec_1 T.rec_2

/- CLASSCHECK / P2D, a container's block mates are classes (good twin).
   `A`/`B` one mutual block, `A`'s field `K1 (B α)` a mate occurrence
   whnf ERASES (`K1 β := Nat`).  Official copies the whole block:
   auxiliary types `A T` and `B T`.  The forged twin
   `corner_classcheck_mates_bad` (scripts/mk_classcheck_p2d_fixtures.py)
   spells the mate's class `B (Id' T)`: `A T`'s crest then has the mate
   occurrence `B X` at `A T`'s own instantiation with no class of that
   spelling — the lfp node of `A T` is the whole block at `[T]`, whose
   `B` component no class walks.  The class check requires every block
   mate of a container class at its instantiation to be a class.
   Official 0 here, 1 on the twin. -/

def Id' (α : Type) : Type := α
def K1 (β : Type) : Type := Nat
mutual
inductive A (α : Type) : Type where
  | a (x : K1 (B α)) (y : α) : A α
inductive B (α : Type) : Type where
  | b (y : α) : B α
end
inductive T : Type where
  | leaf : T
  | mk (x : A T) (y : B T) : T
