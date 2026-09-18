--#export Collide2.self

/- THE CONTAINER-INSTANCE MAP, AS A WITNESS — the CONTROL (task #315,
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

   official (Lean v4.29.1): accepts.  con-leche today: REJECTS, exit 1,
   `duplicate declaration Collide2._model._impl.pack_1` — the same
   in-process-modeller helper-naming defect
   (`ConLeche/Frontend/InModel/Nested.lean:653`) that
   `nested_pin_collide.lean`'s header records.

   NO ROW IN `tests/e2e-expected.txt` AND NO COMMITTED STREAM; the
   stream regenerates with `scripts/export-fixture.sh nested_pin_collide2`
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
