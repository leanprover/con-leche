--#export PiField.self

/- COLLECTED FROM `agent/uniform-le`, where it was the uniform (native nested) route's witness for a container field whose stored domain is a `Pi`; on master it is a plain `tests/e2e-expected.txt` fixture, and `--nested-shadow`, `tests/nested-shadow-expected.txt` and the modeller-off runs named below exist on that branch only.

   A CONTAINER FIELD WHOSE STORED DOMAIN IS A `Π` (task #315, lane LE)
   — the second shape the stored domain takes at the arm
   `nested_bvar_field` names, and the one the REFLEXIVE `Π`-prefix
   object is owed at.

     K α  | mk   (f : Nat → α)      -- the field is a `Π`
     J β  | node (k : K (J β))      -- J's own pin is `K (J β)`
     PiField | mk (j : J PiField)

   `K` calls the field ORDINARY and `J`'s own elimination rewrote it to
   REFLEXIVE.  `stripDomPis` cuts the tower and the recomputation is
   constant-headed as in `nested_bvar_field`, but the cut
   (`domPiDepth`) is no longer `0`, so the two copies' field telescopes
   are not empty and `slotSet_nil` does not collapse them — which is
   what "the reflexive `Π`-prefix is a separate object" means at this
   arm.

   official (Lean v4.29.1): accepts.  con-leche DECLINES the stream
   (exit 2, "in-process model of J: reflexive member J"), so the fold
   never reaches `PiField` and the row below covers `J` ONLY, with the
   modeller off.  It is a TRIPWIRE, `nested_refl_pin`'s kind: it gains
   `,PiField=accept` the day a route installs a container with a
   reflexive member, which is the day this arm is first reachable
   end to end.

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
