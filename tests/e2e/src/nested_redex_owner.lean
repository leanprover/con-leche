/- A CONTAINER MINT THAT IS A REDEX, WITH AN OWNER ABOVE IT (task
   #315, lane LE) — the shape that puts a copy in K.70's arm (C)
   without the arm's claim being true, and the SECOND finding of the
   `hscope` reading.

     Wrap (f : True → Type) | mk : f True.intro → Wrap f
     J β                    | node : Wrap (fun _ : True => J β) → J β
     Outer                  | mk   : J Outer → Outer

   `nested_lam_pin_prop` has the same λ-REDEX mint at the BLOCK's own
   nesting; here it sits one level down, at `J`'s, so the outer block's
   copy of `Wrap` has `J`'s own pin as its OWNER and K.67's walk speaks
   at it.

   `Wrap` calls its only field ORDINARY and `J`'s elimination REWROTE
   it: the recomputation `(fun _ : True => J β) True.intro` reduces to
   `J β`, an occurrence of `J`'s member.  But `ordRootFired` is the
   UNNORMALISED head test and a λ is no `.const`, so the owner reads as
   NOT FIRING and the field falls into K.70's arm (C), whose claim is
   that the block's target leaves the owner's instance.  It does not:
   the target is the copy of `J`'s own member, squarely inside the map.

   official (Lean v4.29.1): ACCEPTS.  con-leche's dispatch accepts the
   stream (exit 0, 8 declarations) — the native route is not on it —
   and the uniform route ERRORS on `Outer` with "a rewritten ordinary
   field's target is not the owning container's own class".  THE ROW
   BELOW IS PINNED AT THAT VERDICT as the finding, `inmodel_groups`'
   precedent; it becomes `Outer=accept` when K.67's walk reads its fire
   test at the positivity normal form the way K.69 already does
   (`ordRootNorm`), which was measured to fix it with the gate
   unchanged at 44/44.

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
