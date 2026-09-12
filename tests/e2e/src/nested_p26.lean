--#export P26.rec P26.rec_1 P26.rec_2

/- Task #279 probe p26: a λ-pin with a USED variable.  Official (Lean v4.33.0) ACCEPTS. -/
inductive P26V (α : Type) : Nat → Type where
  | nil : P26V α 0
  | cons {n : Nat} : α → P26V α n → P26V α (n + 1)
inductive P26D (α : Type) (β : α → Type) where
  | leaf
  | node (k : α) (v : β k) (rest : P26D α β)
inductive P26 where
  | mk : P26D Nat (fun k => P26V P26 k) → P26
