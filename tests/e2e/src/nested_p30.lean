--#export P30.rec P30.rec_1

/- Task #279 probe p30: a universe-polymorphic block through `List`.  Official (Lean v4.33.0) ACCEPTS. -/
inductive P30 (α : Type u) : Type u where
  | mk : α → List (P30 α) → P30 α
