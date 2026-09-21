--#export P24A.rec P24B.rec P24A.rec_1 P24A.rec_2

/- Task #279 probe p24: mutual AND nested, with an indexed member.  Official (Lean v4.33.0) ACCEPTS. -/
inductive P24V (α : Type) : Nat → Type where
  | nil : P24V α 0
  | cons {n : Nat} : α → P24V α n → P24V α (n + 1)
mutual
inductive P24A : Type where
  | mk : List (P24B 0) → P24A
inductive P24B : Nat → Type where
  | mk : (n : Nat) → P24V P24A n → P24B n
end
