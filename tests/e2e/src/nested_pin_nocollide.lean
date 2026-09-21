--#export NoCollide.self

/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's ACCEPTING arm of the container-instance-map triple; on master it is a plain `tests/e2e-expected.txt` fixture, and `--nested-shadow`, `tests/nested-shadow-expected.txt` and `scripts/nested-pin-probe.lean` exist on that branch only.

   THE CONTAINER-INSTANCE MAP, AS A WITNESS — the ACCEPTING arm (task
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

   official (Lean v4.29.1): accepts.  con-leche: accepts (exit 0), and
   the UNIFORM route accepts both nested blocks in shadow —
   `J=accept,NoCollide=accept,` in `tests/nested-shadow-expected.txt`,
   which is this witness's point.

   No `tests/e2e-expected.txt` row: the three witnesses are held
   together in the shadow gate, and its two partners have no e2e row
   until the flip.  The stream is committed beside this source and
   regenerates with `scripts/export-fixture.sh nested_pin_nocollide`
   (Lean v4.29.1, lean4export at `caccfbe`). -/

inductive Wrap (α : Type) where
  | w (a : α)

inductive Pair (α : Type) (β : Type) where
  | mk (a : α) (b : β)

inductive J (α : Type) (β : Type) where
  | node (x : Pair α (J α β)) (y : Pair β (J α β))

inductive NoCollide where
  | mk (j : J NoCollide (Wrap NoCollide))

theorem NoCollide.self (x : NoCollide) : x = x := rfl
