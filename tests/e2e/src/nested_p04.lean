--#export P4.rec P4.rec_1 P4.rec_2

/- Task #279 probe p04: nesting through a container that is ITSELF nested.  Official (Lean v4.33.0) ACCEPTS. -/
inductive P4C (α : Type) where
  | text (s : α)
  | append (parts : Array (P4C α))
inductive P4 where
  | mk : P4C P4 → P4
