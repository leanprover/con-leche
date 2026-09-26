--#export AT.rec AT.rec_1
/- Corner case (the recursor MAJOR check): a nested occurrence `List AT` that official finds SYNTACTICALLY
   (`replace_all_nested`, before any whnf) inside the argument of a
   definition `K` which δ-reduces it away.  Official generates `AT.rec_1`
   on `List AT`; the positivity walk reads the field at its whnf, `Nat`,
   and never visits `List AT`.  Official 0. -/
def K (_ : Type) : Type := Nat
inductive AT where
  | leaf : AT
  | mk : K (List AT) → AT
