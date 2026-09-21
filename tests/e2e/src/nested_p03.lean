--#export P3.rec P3.rec_1 P3.rec_2

/- Task #279 probe P3: a nested CHAIN, `Array (List T)` — two mimics,
   creation depth 2.  Official (Lean v4.33.0) ACCEPTS. -/
inductive P3 where
  | mk : Array (List P3) → P3
