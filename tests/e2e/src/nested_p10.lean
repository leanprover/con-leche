--#export P10.rec P10.rec_1

/- Task #279 probe p10: nesting through a REFLEXIVE container.  Official (Lean v4.33.0) ACCEPTS. -/
inductive P10S (α : Type) where
  | sup : (Nat → P10S α) → α → P10S α
inductive P10 where
  | mk : P10S P10 → P10
