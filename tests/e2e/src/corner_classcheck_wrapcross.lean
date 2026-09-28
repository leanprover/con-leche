--#export T.rec T.rec_1 T.rec_2 T.rec_3 T.rec_4
set_option genSizeOfSpec false
set_option genInjectivity false

/- CLASSCHECK / P2D3: an inner class of a key that is CROSS-FORMED in a
   class the key's own constructor reads.  Class `r := Wrap RL T (RL T)`
   has the inner class `ρ := RL T` (its third parameter, commuting with
   the instantiation) and reads `d := Ap2 RL T (RL T)`, in whose
   constructor `ρ` is ALSO formed by instantiating two parameters
   (`f α`).  `RL` is the youngest container, so `ρ` is an "inner younger
   commuting" class of `r` — a free hole of `r`'s fact under the naive
   free sets — while `d` must read `ρ` coherently: `r`'s identification
   at a stage value of `ρ` fails (`d`'s carrier reads `RL X` whatever
   `ρ`'s hole holds).  No reader supplies `r` a stage value of `ρ`
   (nothing `ρ` reaches mentions `r`): the free sets are the classes a
   reader DOES supply at a stage, i.e. inner classes on a mention cycle
   with the key.  Official 0. -/
inductive Ap2 (f : Type → Type) (α : Type) (β : Type) : Type where
  | mk (x : f α) (y : β) : Ap2 f α β
inductive Wrap (f : Type → Type) (α : Type) (β : Type) : Type where
  | mk (x : Ap2 f α β) : Wrap f α β
inductive RL (α : Type) : Type where
  | node (a : α) (cs : List (RL α)) : RL α
inductive T : Type where
  | leaf : T
  | mk (p : Wrap RL T (RL T)) : T
