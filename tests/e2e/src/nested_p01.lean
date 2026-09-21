--#export P1.rec P1.rec_1

/- Task #279 probe p01: a nested occurrence UNDER A BINDER in the field (`(Nat → List T) → T`).  Official (Lean v4.33.0) ACCEPTS. -/
inductive P1 where
  | mk : (Nat → List P1) → P1
