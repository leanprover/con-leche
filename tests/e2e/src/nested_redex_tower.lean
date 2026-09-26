/- A CONTAINER MINT THAT IS A REDEX **WHOSE REDUCTION IS A `Π`**.

     Wrap (f : True → Type) | mk : f True.intro → Wrap f
     J β                    | node : Wrap (fun _ : True => True → J β) → J β
     Outer                  | mk   : J Outer → Outer

   It is `nested_redex_owner`'s mint with `nested_comp_tower`'s
   component: the pin `Wrap (fun _ : True => True → J β)` mints the
   copy's only field as `(fun _ : True => True → J β) True.intro`, a
   λ-REDEX whose head normal form is the `Π` `True → J β`.  The
   positivity walk reduces it, so the copy's field is `True → J β`,
   REFLEXIVE with a one-binder telescope — while the CONTAINER's stored
   field domain `f True.intro` is an APPLICATION whose reading, at the
   pin's components, is not a `Π` at all: the two agree only
   SEMANTICALLY, not as readings.

   `nested_comp_tower` is the same corner without the redex (there the
   mint IS a `Π` already, and the container's tower is what disagrees);
   `nested_redex_owner` is the redex without the tower (its reduction
   is an application, so the copy's field is finitary).  This source is
   the one where the two meet.

   official (Lean v4.29.1): accepts.  con-leche: accepts.

   The stream is committed beside this source and regenerates with
   `scripts/export-fixture.sh nested_redex_tower` (Lean v4.29.1,
   lean4export at `caccfbe`). -/
prelude
inductive True : Prop where
  | intro : True

inductive Wrap (f : True → Type) : Type where
  | mk : f True.intro → Wrap f

inductive J (β : Type) : Type where
  | node : Wrap (fun _ : True => True → J β) → J β

inductive Outer : Type where
  | mk : J Outer → Outer
