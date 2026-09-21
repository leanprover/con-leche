--#export P5.rec P5.rec_1 P5.rec_2

/- Task #279 probe p05: nesting through a MUTUAL container — both members are copied.  Official (Lean v4.33.0) ACCEPTS. -/
mutual
inductive P5Ev (α : Type) where
  | nil
  | cons : α → P5Od α → P5Ev α
inductive P5Od (α : Type) where
  | cons : α → P5Ev α → P5Od α
end
inductive P5 where
  | mk : P5Ev P5 → P5
