--#export BvarField.self

/- A CONTAINER FIELD WHOSE STORED DOMAIN IS A BARE PARAMETER — the
   MINIMAL witness that the shared container's stored field domain need
   not be constant-headed where the OWNER's copy rewrote it.

     K α  | mk   (a : α)            -- the field is the bvar `α`
     J β  | node (k : K (J β))      -- J's own pin is `K (J β)`
     BvarField | mk (j : J BvarField)

   `K` calls its only field ORDINARY (the domain mentions no member of
   `K`), and `J`'s own elimination REWROTE it: `α := J β` is an
   occurrence of `J`'s member, so the copy of `K.mk` in `J`'s block has
   a RECURSIVE field.  The outer block copies both groups, so the copy
   of `K` there has `J`'s own pin as its OWNER.  The stored domain at
   that arm is `Expr.bvar 0`, whose `getAppFn` is no `.const`; read at
   the owner's component `J β` it IS constant-headed.

   `nested_pin_nocollide` (`Pair α β | mk (a : α) (b : β)`) and
   `nested_p04` exhibit the same shape inside larger fixtures; this
   source is the smallest one that does.

   official (Lean v4.29.1): accepts.  con-leche: accepts.

   The stream is committed beside this source and regenerates with
   `scripts/export-fixture.sh nested_bvar_field` (Lean v4.29.1,
   lean4export at `caccfbe`). -/

inductive K (α : Type) where
  | mk (a : α)

inductive J (β : Type) where
  | node (k : K (J β))

inductive BvarField where
  | mk (j : J BvarField)

theorem BvarField.self (x : BvarField) : x = x := rfl
