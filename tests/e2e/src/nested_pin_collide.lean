--#export Collide.self

/- THE CONTAINER-INSTANCE MAP — the COLLAPSING arm.  Its twin with the
   pins apart is `nested_pin_nocollide.lean` and its control is
   `nested_pin_collide2.lean`; all three share the container `J` below.

   `J`'s own elimination mints TWO pins, differing only in which of
   `J`'s parameters sits in `Pair`'s first slot:

     pin 0 = Pair α (J α β)      pin 1 = Pair β (J α β)

   Here the block instantiates BOTH parameters at `Collide`, so both
   pins become `Pair Collide (J Collide Collide)`, and official mints
   one auxiliary type per distinct pin EXPRESSION: the block has ONE
   `Pair` copy for `J`'s TWO own-pin classes — the map from the
   container's classes to the block's components COLLAPSES, and is not
   an injection.

   official (Lean v4.29.1): accepts.  con-leche: accepts.

   The stream is committed beside this source and regenerates from it
   with `scripts/export-fixture.sh nested_pin_collide` (Lean v4.29.1,
   lean4export at `caccfbe`). -/

inductive Pair (α : Type) (β : Type) where
  | mk (a : α) (b : β)

inductive J (α : Type) (β : Type) where
  | node (x : Pair α (J α β)) (y : Pair β (J α β))

inductive Collide where
  | mk (j : J Collide Collide)

theorem Collide.self (x : Collide) : x = x := rfl
