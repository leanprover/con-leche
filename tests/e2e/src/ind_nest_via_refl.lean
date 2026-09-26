--#export ViaRefl.self

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean"): nesting through a REFLEXIVE container (`W1`).  The export
   flags the block `isReflexive`.

   official: 0.  con-leche: 0.
   Probe of record: _tmp/indaudit/probes/P/NestViaRefl.lean. -/
inductive W1 (α : Type)
  | sup (a : α) (f : Nat → W1 α)

inductive ViaRefl
  | leaf
  | node (w : W1 ViaRefl)

theorem ViaRefl.self (x : ViaRefl) : x = x := rfl
