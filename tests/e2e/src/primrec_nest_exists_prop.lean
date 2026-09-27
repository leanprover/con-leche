--#export ET.rec ET.rec_1

/- PRIMREC/NESTHOME: a `Prop` block nested in `Exists` — the container's
   parameter a λ over the member (`Exists fun n : Nat => ET`), official's
   auxiliary recursor for it beside `ET.rec`.  Official 0.  Target 0. -/

inductive ET : Prop where
  | base : ET
  | mk (h : Exists fun (_ : Nat) => ET) : ET
