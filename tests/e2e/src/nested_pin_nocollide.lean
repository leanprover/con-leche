--#export NoCollide.self

/- THE CONTAINER-INSTANCE MAP, AS A WITNESS — the ACCEPTING arm (task
   #315, lane WIDE (f1)).  One of three sources that together show what
   the nested expansion's instance map is and is not; the other two are
   `nested_pin_collide.lean` and `nested_pin_collide2.lean`, and all
   three share the container `J` below.

   `J`'s own elimination mints TWO pins, differing only in which of
   `J`'s parameters sits in `Pair`'s first slot:

     pin 0 = Pair α (J α β)      pin 1 = Pair β (J α β)

   Here the block instantiates them APART (`α := NoCollide`,
   `β := Wrap NoCollide`), so the two stay two, and the map from `J`'s
   three classes (its member and its two own pins) to the block's
   components is injective — the block's pin table, read with
   `scripts/nested-pin-probe.lean`, is

     pin 0 = _nested.J_1     (J NoCollide) (Wrap NoCollide)
     pin 1 = _nested.Pair_2  (Pair NoCollide) ((J NoCollide) (Wrap NoCollide))
     pin 2 = _nested.Pair_3  (Pair (Wrap NoCollide)) ((J NoCollide) (Wrap NoCollide))
     pin 3 = _nested.Wrap_4  (Wrap NoCollide)

   so `J`'s classes sit at the block's components 1, 2, 3.

   official (Lean v4.29.1): accepts.  con-leche: accepts (exit 0).

   NO ROW IN `tests/e2e-expected.txt` AND NO COMMITTED STREAM.  The
   three sources are witnesses to a shape, not verdict fixtures: two of
   them are rejected today by a defect (see `nested_pin_collide.lean`),
   and a row would either enshrine that reject or fail the gate.  The
   streams regenerate from these sources with the pinned toolchain,
   `scripts/export-fixture.sh nested_pin_nocollide` (Lean v4.29.1,
   lean4export at `caccfbe`). -/

inductive Wrap (α : Type) where
  | w (a : α)

inductive Pair (α : Type) (β : Type) where
  | mk (a : α) (b : β)

inductive J (α : Type) (β : Type) where
  | node (x : Pair α (J α β)) (y : Pair β (J α β))

inductive NoCollide where
  | mk (j : J NoCollide (Wrap NoCollide))

theorem NoCollide.self (x : NoCollide) : x = x := rfl
