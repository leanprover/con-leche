--#export P25.rec P25.rec_1

/- Task #279 probe p25: nesting through an INDEXED container at a closed index.  Official (Lean v4.33.0) ACCEPTS. -/
inductive P25V (α : Type) : Nat → Type where
  | nil : P25V α 0
  | cons {n : Nat} : α → P25V α n → P25V α (n + 1)
inductive P25 where
  | mk : P25V P25 3 → P25
