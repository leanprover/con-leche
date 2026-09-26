--#export Collide2.self

/- THE CONTAINER-INSTANCE MAP — the CONTROL.  Its two partners are
   `nested_pin_collide.lean` (collapsing) and
   `nested_pin_nocollide.lean` (apart); all three share the container
   `J` below.

   WHAT IT CONTROLS FOR.  The apart twin differs from the collapsing
   one in two ways at once — it keeps the container's two own pins
   apart AND it introduces `Wrap`.  This source has `Wrap` and
   collapses anyway (both of `J`'s parameters are instantiated at
   `Wrap Collide2`, so `Pair α (J α β)` and `Pair β (J α β)` again
   become one expression).

   official (Lean v4.29.1): accepts.  con-leche: accepts.

   The stream is committed beside this source and regenerates with
   `scripts/export-fixture.sh nested_pin_collide2` (Lean v4.29.1,
   lean4export at `caccfbe`). -/

inductive Wrap (α : Type) where
  | w (a : α)

inductive Pair (α : Type) (β : Type) where
  | mk (a : α) (b : β)

inductive J (α : Type) (β : Type) where
  | node (x : Pair α (J α β)) (y : Pair β (J α β))

inductive Collide2 where
  | mk (j : J (Wrap Collide2) (Wrap Collide2))

theorem Collide2.self (x : Collide2) : x = x := rfl
