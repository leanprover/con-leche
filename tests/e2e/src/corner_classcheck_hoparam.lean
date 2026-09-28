--#export T.rec T.rec_1 T.rec_2 T.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- CLASSCHECK / P2D: a HIGHER-ORDER container parameter.  `Ap f α` reads
   `f α`; at the class `Ap RL T` its constructor's field is `RL T` — a
   class occurrence formed by instantiating TWO parameters, a subterm of
   neither: the key in hole form (`Ap RL X`) does not contain it, and its
   inductive `RL` is YOUNGER than `Ap`.  (PROOFPLAN's occurrence lemma A1
   — every class occurrence in a crest is the group, a member, an inner
   class of the key, or of an older inductive — does not hold here.)
   Official 0, the default route 0, the class checker 0. -/
inductive Ap (f : Type → Type) (α : Type) : Type where
  | mk (x : f α) : Ap f α
inductive RL (α : Type) : Type where
  | node (a : α) (cs : List (RL α)) : RL α
inductive T : Type where
  | leaf : T
  | mk (p : Ap RL T) : T
