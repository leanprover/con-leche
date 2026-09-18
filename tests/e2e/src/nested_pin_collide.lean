--#export Collide.self

/- THE CONTAINER-INSTANCE MAP, AS A WITNESS — the COLLAPSING arm (task
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

   official (Lean v4.29.1): accepts.  con-leche today: REJECTS, exit 1,

     invalid: duplicate declaration Collide._model._impl.pack_1
     [… a generated model record of inductive Collide, fold position 47]

   THE REJECT IS A DEFECT, AND IT IS NOT IN THE KERNEL.  The in-process
   modeller names its pack/unpack helpers by the MIMIC ORDINAL
   (`Mem.j`, `ConLeche/Frontend/InModel/Nested.lean:653`), so a
   container group contributing two own-pin classes to ONE mimic emits
   `pack_j` twice and the fold then rejects the duplicate.  Official
   accepts the stream, so this is a FALSE REJECT (exit 1, not exit 2).
   Recorded, deliberately not fixed here: the modeller is the
   dispatched route on `master`.

   NO ROW IN `tests/e2e-expected.txt` AND NO COMMITTED STREAM.  A row
   would enshrine the false reject.  The stream regenerates from this
   source with the pinned toolchain,
   `scripts/export-fixture.sh nested_pin_collide` (Lean v4.29.1,
   lean4export at `caccfbe`). -/

inductive Pair (α : Type) (β : Type) where
  | mk (a : α) (b : β)

inductive J (α : Type) (β : Type) where
  | node (x : Pair α (J α β)) (y : Pair β (J α β))

inductive Collide where
  | mk (j : J Collide Collide)

theorem Collide.self (x : Collide) : x = x := rfl
