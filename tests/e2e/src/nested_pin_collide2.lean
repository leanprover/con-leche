--#export Collide2.self

/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's CONTROL for the collapsing-pins witness; on master it is a plain `tests/e2e-expected.txt` fixture, and `--nested-shadow` and `tests/nested-shadow-expected.txt` exist on that branch only.

   THE CONTAINER-INSTANCE MAP, AS A WITNESS — the CONTROL (task #315,
   lane WIDE (f1)).  Its two partners are `nested_pin_collide.lean`
   (collapsing, rejected) and `nested_pin_nocollide.lean` (apart,
   accepted); all three share the container `J` below.

   WHAT IT CONTROLS FOR.  The accepting twin differs from the
   collapsing one in two ways at once — it keeps the container's two
   own pins apart AND it introduces `Wrap`.  This source has `Wrap`
   and collapses anyway (both of `J`'s parameters are instantiated at
   `Wrap Collide2`, so `Pair α (J α β)` and `Pair β (J α β)` again
   become one expression).  So the variable that moves the verdict is
   the collapse and not the extra type.

   official (Lean v4.29.1): accepts.  con-leche's modelled dispatch
   exits 1 on it today, as on `nested_pin_collide`.

   Shadow row `J=accept,` in `tests/nested-shadow-expected.txt`, a
   tripwire like its partner's; no `tests/e2e-expected.txt` row until
   the flip.  The stream is committed beside this source and
   regenerates with `scripts/export-fixture.sh nested_pin_collide2`
   (Lean v4.29.1, lean4export at `caccfbe`). -/

inductive Wrap (α : Type) where
  | w (a : α)

inductive Pair (α : Type) (β : Type) where
  | mk (a : α) (b : β)

inductive J (α : Type) (β : Type) where
  | node (x : Pair α (J α β)) (y : Pair β (J α β))

inductive Collide2 where
  | mk (j : J (Wrap Collide2) (Wrap Collide2))

theorem Collide2.self (x : Collide2) : x = x := rfl
