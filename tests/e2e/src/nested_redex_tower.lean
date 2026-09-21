/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's witness refuting the syntactic spelling of `CopyOrdTele`; on master it is a plain `tests/e2e-expected.txt` fixture, and `--nested-shadow`, `tests/nested-shadow-expected.txt` and the `CON_LECHE_INMODEL` runs named below exist on that branch only.

   A CONTAINER MINT THAT IS A REDEX **WHOSE REDUCTION IS A `Π`** (task
   #315, lane LE) — the witness that refutes the SYNTACTIC spelling of
   step 5's object `CopyOrdTele` (DESIGN, "WIDE (f3) STEP 5 — THE
   ASSEMBLY EXISTS, RE-RUN AT `σ`").

     Wrap (f : True → Type) | mk : f True.intro → Wrap f
     J β                    | node : Wrap (fun _ : True => True → J β) → J β
     Outer                  | mk   : J Outer → Outer

   It is `nested_redex_owner`'s mint with `nested_comp_tower`'s
   component: the pin `Wrap (fun _ : True => True → J β)` mints the
   copy's only field as `(fun _ : True => True → J β) True.intro`, a
   λ-REDEX whose head normal form is the `Π` `True → J β`.  The
   positivity normalisation (`normPosDomM`, which the install runs
   before it stores the copy's constructor) reduces it, so the STORED
   copy field is `True → J β` and the block classifies it REFLEXIVE
   with a ONE-binder recorded telescope — while the CONTAINER's stored
   field domain `f True.intro` is an APPLICATION whose reading, at the
   pin's components, is an application too and not a `Π` at all.

   So "the copy's recorded telescope is the `Π`-prefix of the
   container's field domain with the components substituted" is FALSE
   here as an equation between READINGS, and only its `interp` form
   survives: the walk's reading law (`normPosDomM_read_of`) relates the
   minted domain's reading to the normalised one's SEMANTICALLY and in
   no stronger way.

   `nested_comp_tower` is the same corner without the redex (there the
   mint IS a `Π` already, and the container's tower is what disagrees);
   `nested_redex_owner` is the redex without the tower (its reduction
   is an application, so the copy's field is finitary and no telescope
   is recorded).  This source is the one where the two meet.

   official (Lean v4.29.1): accepts.  con-leche's dispatch DECLINES the
   stream (the in-process modeller cannot model `J`) and the native
   route ACCEPTS `J` — which is the row below, measured at
   `CON_LECHE_INMODEL=0` the way `nested_pi_field` is.

   No `tests/e2e-expected.txt` row: the stream is here for the shadow
   gate, where the uniform route is measured.  It is committed beside
   this source and regenerates with
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
