--#export P20.rec P20.rec_1 P20.rec_2

/- Task #279 probe p20: `Subtype` at a CONSTANT predicate.  Official (Lean v4.33.0) ACCEPTS. -/
inductive P20 where
  | mk : { _l : List P20 // True } → P20
