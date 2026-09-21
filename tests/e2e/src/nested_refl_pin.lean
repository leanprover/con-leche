--#export ReflPin.self

/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's reflexive-nested-field witness (K.63); on master it is a plain `tests/e2e-expected.txt` fixture, and `--nested-shadow`, `tests/nested-shadow-expected.txt` and the K-records named below exist on that branch only.

   A REFLEXIVE NESTED FIELD IN A CONTAINER (task #315, K.63's fixture).

   The container `J` has a constructor field that is a Π whose BODY is
   an application of a further stored container carrying one of `J`'s
   own members:

     J.node : (Nat → Box (J α)) → J α

   so `J`'s own elimination pins `Box (J α)` and the field of `J`'s copy
   in the outer block is classified `.reflexive` into that pin.  K.60
   claims nothing there by construction — its guard reads the stored
   domain's head, and a Π's `getAppFn` is not a `.const` — which is why
   K.63 exists; and no other accepted fixture exercises the shape, which
   is why this source does.

   official (Lean v4.29.1): accepts.  con-leche: accepts (exit 0), and
   the uniform route accepts both nested blocks in shadow —
   `J=accept,ReflPin=accept,` in `tests/nested-shadow-expected.txt`,
   which is this witness's point.

   No `tests/e2e-expected.txt` row: the stream is here for the shadow
   gate, where the uniform route is measured.  It is committed beside
   this source and regenerates with
   `scripts/export-fixture.sh nested_refl_pin` (Lean v4.29.1,
   lean4export at `caccfbe`). -/

inductive Box (α : Type) where
  | mk (a : α)

inductive J (α : Type) where
  | node (f : Nat → Box (J α))

inductive ReflPin where
  | mk (j : J ReflPin)

theorem ReflPin.self (x : ReflPin) : x = x := rfl
