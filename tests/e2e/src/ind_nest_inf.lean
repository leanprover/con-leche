--#export InfNest.self

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean"): INFINITARY nesting — a nested occurrence under a binder
   inside the container's parameter, `List (Nat → T)`.  The export flags
   the block `isReflexive` (the flag is computed on the kernel's
   auxiliary mutual declaration).

   official: 0.  con-leche: 0.
   Probe of record: _tmp/indaudit/probes/P/NestInf.lean. -/
inductive InfNest
  | leaf
  | node (cs : List (Nat → InfNest))

theorem InfNest.self (x : InfNest) : x = x := rfl
