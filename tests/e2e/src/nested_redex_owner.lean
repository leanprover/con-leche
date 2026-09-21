/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's regression test for reading the fire test at the positivity normal form; on master it is a plain `tests/e2e-expected.txt` fixture, and `--nested-shadow`, `tests/nested-shadow-expected.txt` and the K-records named below exist on that branch only.

   A CONTAINER MINT THAT IS A REDEX, WITH AN OWNER ABOVE IT (task
   #315, lane LE) — the shape that REFUTED K.70's complementarity
   argument, and the witness K.67's normalisation exists for.

     Wrap (f : True → Type) | mk : f True.intro → Wrap f
     J β                    | node : Wrap (fun _ : True => J β) → J β
     Outer                  | mk   : J Outer → Outer

   `nested_lam_pin_prop` has the same λ-REDEX mint at the BLOCK's own
   nesting; here it sits one level down, at `J`'s, so the outer block's
   copy of `Wrap` has `J`'s own pin as its OWNER and K.67's walk speaks
   at it.

   `Wrap` calls its only field ORDINARY and `J`'s elimination REWROTE
   it: the recomputation `(fun _ : True => J β) True.intro` reduces to
   `J β`, an occurrence of `J`'s member.  Asked UNNORMALISED,
   `ordRootFired` answers `false` — a λ is no `.const` — so the owner
   reads as NOT FIRING and the field falls into K.70's arm (C), whose
   claim is that the block's target leaves the owner's instance.  It
   does not: the target is the copy of `J`'s own member, squarely
   inside the map.  Asked at `ordRootNorm` the owner FIRES and the
   POSITIVE row speaks, which is what the route does.

   official (Lean v4.29.1): ACCEPTS.  con-leche's dispatch accepts the
   stream (exit 0, 8 declarations) — the native route is not on it —
   and the uniform route ACCEPTS both blocks since K.67's walk reads
   its fire test at the positivity normal form the way K.69 already
   does (`ordRootNorm`).  Before that spelling the route ERRORED on
   `Outer` with "a rewritten ordinary field's target is not the owning
   container's own class", which is what this fixture was built to
   exhibit: the arm is complementary as a BOOL at whatever term the
   test is asked of, but the negative arm's CLAIM is about the owner's
   instance, so asking it of the un-reduced mint makes the claim
   false.  The row below is this fixture's REGRESSION: it goes back to
   `Outer=error` the moment the normalisation is dropped.

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
