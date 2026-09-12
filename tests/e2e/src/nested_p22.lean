--#export P22.rec P22.rec_1 P22.rec_2

/- Task #279 probe p22: a λ-pin whose body is a container application.  Official (Lean v4.33.0) ACCEPTS. -/
inductive P22T (f : Nat → Type) where
  | mk (n : Nat) (v : f n)
inductive P22 where
  | mk : P22T (fun _ => List P22) → P22
