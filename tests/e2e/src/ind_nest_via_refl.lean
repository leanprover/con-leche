--#export ViaRefl.self

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean", raw-decline arm): nesting through a REFLEXIVE container
   (`W1`).  The export flags the block `isReflexive`, so it goes to the
   preprocessor, which models it; raw, the in-process modeller declines a
   reflexive member.

   official: 0.  con-leche at master 700a06ca: 0 piped, 2 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/NestViaRefl.lean. -/
inductive W1 (α : Type)
  | sup (a : α) (f : Nat → W1 α)

inductive ViaRefl
  | leaf
  | node (w : W1 ViaRefl)

theorem ViaRefl.self (x : ViaRefl) : x = x := rfl
