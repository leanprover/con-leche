--#export MA.rec MB.rec MA.rec_1
/- Corner case (lane SEEDDEFEQ, the seeded positivity check): the MUTUAL
   twin of `corner_posderiv_major_delta`.  A nested occurrence `List MA`
   that official finds SYNTACTICALLY inside the argument of `K`, which
   δ-reduces it away: official generates `MA.rec_1` on `List MA`; the
   positivity check reads the field at its whnf, `Nat`, and walks `List MA`
   only because the stream's `MA.rec_1` SEEDS it.  Official 0. -/
def K (_ : Type) : Type := Nat
mutual
inductive MA where
  | leaf : MA
  | mk : K (List MA) → MB → MA
inductive MB where
  | mk : MA → MB
end
