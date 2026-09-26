--#export PiField.self

/- A CONTAINER FIELD WHOSE STORED DOMAIN IS A `Π` — the second shape
   the stored domain takes at the arm `nested_bvar_field` names.

     K α  | mk   (f : Nat → α)      -- the field is a `Π`
     J β  | node (k : K (J β))      -- J's own pin is `K (J β)`
     PiField | mk (j : J PiField)

   `K` calls the field ORDINARY and `J`'s own elimination rewrote it to
   REFLEXIVE: the copies' field telescopes are not empty.

   official (Lean v4.29.1): accepts.  con-leche: accepts.

   Committed beside this source; regenerates with
   `scripts/export-fixture.sh nested_pi_field` (Lean v4.29.1,
   lean4export at `caccfbe`). -/

inductive K (α : Type) where
  | mk (f : Nat → α)

inductive J (β : Type) where
  | node (k : K (J β))

inductive PiField where
  | mk (j : J PiField)

theorem PiField.self (x : PiField) : x = x := rfl
