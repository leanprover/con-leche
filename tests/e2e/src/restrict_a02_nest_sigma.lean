--#export T.rec T.rec_1 T.rec_2
/- RESTRICT a02: a container parameter that is a λ hiding a second nested
   instance (`Sigma (fun n => Vec T n)`); official replaces `Vec T n` under the
   binder; the aux `Sigma` ctor's field `(fun n => Vec T n) fst` needs whnf. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n+1)
inductive T where
  | mk : (Σ n : Nat, Vec T n) → T
