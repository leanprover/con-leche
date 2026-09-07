--#export PNonempty.self PAnd.self

/- End-to-end fixture (task #208; inductive audit #206, §2 "probed and
   clean"): `Prop` blocks nested through `Prop` containers (`Nonempty`,
   `And`).  Both official and the in-process modeller accept, piped and
   raw.

   official: 0.  lech at master 700a06ca: 0 piped, 0 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/NestProp.lean. -/
inductive PNonempty : Prop
  | mk (h : Nonempty PNonempty)

inductive PAnd : Prop
  | mk (h : PAnd ∧ True)

theorem PNonempty.self (x : PNonempty) : x = x := rfl
theorem PAnd.self (x : PAnd) : x = x := rfl
