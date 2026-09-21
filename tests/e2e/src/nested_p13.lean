--#export P13.rec P13.rec_1

/- Task #279 probe p13: a ONE-constructor `Prop` block through `And` — still the small eliminator.  Official (Lean v4.33.0) ACCEPTS. -/
inductive P13 : Prop where
  | mk : And P13 P13 → P13
