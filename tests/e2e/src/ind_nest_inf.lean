--#export InfNest.self

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean", raw-decline arm): INFINITARY nesting — a nested occurrence
   under a binder inside the container's parameter, `List (Nat → T)`.
   The export flags the block `isReflexive` (the flag is computed on the
   kernel's auxiliary mutual declaration), so the in-process modeller's
   predicate leaves it to the preprocessor, which models it and the
   stream accepts.  Raw it is a documented decline ("reflexive member").

   official: 0.  lech at master 700a06ca: 0 piped, 2 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/NestInf.lean. -/
inductive InfNest
  | leaf
  | node (cs : List (Nat → InfNest))

theorem InfNest.self (x : InfNest) : x = x := rfl
