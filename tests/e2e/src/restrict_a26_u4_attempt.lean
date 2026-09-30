--#export T.rec
/- RESTRICT a26: an attempt at U4 (a later field depending on a recursive
   field): `(fun (_ : T) => Nat) t` mentions `t`, but every well-typed use of
   `t` must mention `T`, so the domain is replaced by its whnf `Nat`. -/
inductive T where
  | mk : (t : T) → (f : (fun (_ : T) => Nat) t) → T
  | leaf : T
