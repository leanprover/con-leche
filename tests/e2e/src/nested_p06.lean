--#export P6.rec P6.rec_1

/- Task #279 probe p06: a `Prop` block through `And`, at two constructors (small eliminator).  Official (Lean v4.33.0) ACCEPTS. -/
inductive P6 : Prop where
  | mk : And P6 P6 → P6
  | base : P6
