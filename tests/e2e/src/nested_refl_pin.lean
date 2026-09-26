--#export ReflPin.self

/- A REFLEXIVE NESTED FIELD IN A CONTAINER.

   The container `J` has a constructor field that is a Π whose BODY is
   an application of a further stored container carrying one of `J`'s
   own members:

     J.node : (Nat → Box (J α)) → J α

   so `J`'s own elimination pins `Box (J α)` and the field of `J`'s copy
   in the outer block is classified `.reflexive` into that pin.  No
   other accepted fixture exercises the shape.

   official (Lean v4.29.1): accepts.  con-leche: accepts.

   The stream is committed beside this source and regenerates with
   `scripts/export-fixture.sh nested_refl_pin` (Lean v4.29.1,
   lean4export at `caccfbe`). -/

inductive Box (α : Type) where
  | mk (a : α)

inductive J (α : Type) where
  | node (f : Nat → Box (J α))

inductive ReflPin where
  | mk (j : J ReflPin)

theorem ReflPin.self (x : ReflPin) : x = x := rfl
