--#export TF.rec TF.rec_1

/- Corner case: the container's reflexive field is reached only through δ
   (`Fn α := KF → α`), so the field's whnf-telescope comes from
   unfolding.  Official 0; target 0. -/

inductive KF : Type where
  | k : KF
def Fn (β : Type) : Type := KF → β
inductive CF (α : Type) : Type where
  | nil : CF α
  | mk (f : Fn α) (z : CF α) : CF α
inductive TF : Type where
  | node (c : CF TF) : TF
