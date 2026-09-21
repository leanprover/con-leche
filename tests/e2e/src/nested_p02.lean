--#export P2.rec P2.rec_1

/- Task #279 probe p02: a λ-pin at a constant function (`DMap Nat (fun _ => T)`).  Official (Lean v4.33.0) ACCEPTS. -/
inductive P2D (α : Type) (β : α → Type) where
  | leaf
  | node (k : α) (v : β k) (rest : P2D α β)
inductive P2 where
  | mk : P2D Nat (fun _ => P2) → P2
