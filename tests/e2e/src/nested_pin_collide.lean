--#export Collide.self

/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's COLLAPSING-pins witness; on master it is a plain `tests/e2e-expected.txt` fixture, and `--nested-shadow`, `tests/nested-shadow-expected.txt`, `docs/NESTED.md` and the `_nomodel` twin named on `agent/uniform-collide` exist on those branches only.

   THE CONTAINER-INSTANCE MAP, AS A WITNESS — the COLLAPSING arm (task
   #315, lane WIDE (f1)).  Its accepting twin is
   `nested_pin_nocollide.lean` and its control is
   `nested_pin_collide2.lean`; all three share the container `J` below.

   `J`'s own elimination mints TWO pins, differing only in which of
   `J`'s parameters sits in `Pair`'s first slot:

     pin 0 = Pair α (J α β)      pin 1 = Pair β (J α β)

   Here the block instantiates BOTH parameters at `Collide`, so both
   pins become `Pair Collide (J Collide Collide)`.  The expansion mints
   one copy per distinct pin EXPRESSION
   (`st.pins.find? (fun q => q.pin == pin)`,
   `ConLeche/Kernel/Inductives/NestedElim.lean`), so the block has ONE
   `Pair` mimic for `J`'s TWO own-pin classes: the map from the
   container's classes to the block's components COLLAPSES, and is not
   an injection.  That is the fact this source exists to exhibit —
   `docs/NESTED.md` §5 records what it costs the identification.

   official (Lean v4.29.1): accepts.  con-leche's modelled dispatch
   exits 1 on it today (`duplicate declaration
   Collide._model._impl.pack_1`, a generated model record).

   THE ROW IS IN `tests/nested-shadow-expected.txt`, NOT IN
   `tests/e2e-expected.txt`.  The shadow gate is where the uniform
   route is measured, and this stream is in it: `J=accept,`.  The outer
   block's own shadow does not run yet — the fold stops at the
   generated model record before that install — so the row is a
   TRIPWIRE that gains `,Collide=accept` the day the stream gets that
   far.  The e2e row, which records the dispatch's exit code, is added
   at the flip.

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
