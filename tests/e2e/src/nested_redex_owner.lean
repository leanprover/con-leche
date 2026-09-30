/- A CONTAINER MINT THAT IS A REDEX, WITH AN OWNER ABOVE IT.

     Wrap (f : True → Type) | mk : f True.intro → Wrap f
     J β                    | node : Wrap (fun _ : True => J β) → J β
     Outer                  | mk   : J Outer → Outer

   `nested_lam_pin_prop` has the same λ-REDEX mint at the BLOCK's own
   nesting; here it sits one level down, at `J`'s, so the outer block's
   copy of `Wrap` has `J`'s own pin as its OWNER.

   `Wrap` calls its only field ORDINARY and `J`'s elimination REWROTE
   it: the recomputation `(fun _ : True => J β) True.intro` reduces to
   `J β`, an occurrence of `J`'s member.  Read UNNORMALISED the field's
   head is a λ, no `.const`, so the owner's rewrite is visible only at
   the positivity normal form; a check that read the unreduced mint
   would misclassify the field.

   official (Lean v4.29.1): ACCEPTS.  con-leche: accepts.

   Committed beside this source; regenerates with
   `scripts/export-fixture.sh nested_redex_owner` (Lean v4.29.1,
   lean4export at `caccfbe`). -/
prelude
inductive True : Prop where
  | intro : True

inductive Wrap (f : True → Type) : Type where
  | mk : f True.intro → Wrap f

inductive J (β : Type) : Type where
  | node : Wrap (fun _ : True => J β) → J β

inductive Outer : Type where
  | mk : J Outer → Outer
