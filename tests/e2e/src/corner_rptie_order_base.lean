--#export T.rec T.rec_1
/- Corner case (lane RPTIE, the order of the recursor check's stage (b) and
   the seeds it walks): a nested occurrence `P (T α)` whnf ERASES (`K`
   δ-reduces it away), so the positivity walk meets the class only as the
   SEED of `T.rec_1`.  The good twin `scripts/mk_rptie_fixtures.py` forges
   `corner_rptie_order_decline` from (the forger's expression indices are
   this export's).  Official 0. -/
prelude
universe u
inductive E : Type where
  | e : E
def K (_ : Type u) : Type := E
inductive P (α : Type u) : Type u where
  | mk : α → P α
inductive T (α : Type u) : Type u where
  | leaf : T α
  | mk : K (P (T α)) → T α
