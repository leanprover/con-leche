--#export T T.rec T.rec_1 T.rec_2
/- RCC (lane PRIMREC/RCC): the good twin of `corner_rcc_create_prop`,
   which `scripts/mk_rcc_fixtures.py` forges from this stream.  A `Prop`
   block nested through `Ap L T`: the auxiliary class `Ap L T` calls the
   class `L T` on its field `f A`, stuck on the parameters at `Ap`'s own
   reading and `L T` once instantiated (no reduction: the key OCCURS in
   the instantiated field).  Official 0, today 0. -/
set_option genSizeOf false
inductive Ap (f : Prop → Prop) (A : Prop) : Prop where
  | mk : f A → Ap f A
inductive L (α : Prop) : Prop where
  | nil : L α
  | cons : α → L α → L α
inductive T : Prop where
  | mk : Ap L T → T
