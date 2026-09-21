--#export TVN.rec TVN.rec_1

/- Corner case: nesting through an INDEXED container from a
   NON-parametric member, with the index an explicit field of the
   constructor bound before the container occurrence
   (`(n : Nat) → VecC TVN n`).  `indexed_nested_aux` is the parametric
   twin (`TV α | node : α → {n} → Vec (TV α) n`, an implicit
   ctor-local index); this one drops the parameter and makes the index
   an ordinary preceding field, so `TVN.rec_1`'s major is
   `VecC TVN a` at `numIndices = 1` with nothing else in the
   telescope.  Official ACCEPTS. -/

inductive VecC (α : Type) : Nat → Type where
  | nil : VecC α 0
  | cons {n : Nat} : α → VecC α n → VecC α (n + 1)

inductive TVN where
  | node : (n : Nat) → VecC TVN n → TVN
