--#export P31.rec P31.rec_1

/- Task #279 probe p31: a REFLEXIVE nested field (`(Nat → Array T) → T`).  Official (Lean v4.33.0) ACCEPTS. -/
inductive P31 where
  | mk : (Nat → Array P31) → P31
