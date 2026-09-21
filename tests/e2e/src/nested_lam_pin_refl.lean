/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's witness that the positivity normalisation CREATES a Pi-telescope out of a lambda-redex pin component; on master it is a plain `tests/e2e-expected.txt` fixture, and `--nested-shadow` and `tests/nested-shadow-expected.txt` exist on that branch only.

   End-to-end fixture (task #315, lane L-B): the REFLEXIVE twin of
   `nested_lam_pin_prop`.  The container's field is a λ-REDEX at the
   pin's components, and the positivity normalisation's `whnf`
   CREATES a Π-telescope out of it:

     Wrap (f : True → Type) | mk : f True.intro → Wrap f

   nested at `f := fun _ : True => True → T`.  The copy's field domain
   is `(fun _ : True => True → T) True.intro`, whose normalisation is
   `True → T` — a REFLEXIVE field at the member `T`, telescope
   `[True]` — while the CONTAINER's own field `f True.intro` is
   ordinary and is not a Π at all.

   The block is accepted (`tests/nested-shadow-expected.txt`), and it
   is what refutes `EntryRead`'s Π-tower clauses at a container
   -ordinary field: DESIGN "L-B session 17".

   The in-process modeller declines the block ("1 inductive hypotheses
   for 0 recursive fields"), so the shadow row runs with the modeller
   off. -/
prelude
inductive True : Prop where
  | intro : True

inductive Wrap (f : True → Type) : Type where
  | mk : f True.intro → Wrap f

inductive T : Type where
  | node : Wrap (fun _ : True => True → T) → T
