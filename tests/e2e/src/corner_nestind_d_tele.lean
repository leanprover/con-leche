--#export TF.rec TF.rec_1

/- Corner case (lane NESTIND, session 15, the (D) re-layout's probe): at an
   OUTSIDE class the target check types every call a second time with the
   family's classes abstracted (`targetClassCallsOk`), under the field's
   MEMBER-level whnf-telescope (the rule frame's `teles`), no longer the
   class-abstracted type's own.  Here the container's reflexive field is
   reached only through δ (`Fn α := KF → α`), so both telescopes come from
   whnf of differently abstracted terms (`Fn TF` vs `Fn #CF…`).
   Official 0; target 0. -/

inductive KF : Type where
  | k : KF
def Fn (β : Type) : Type := KF → β
inductive CF (α : Type) : Type where
  | nil : CF α
  | mk (f : Fn α) (z : CF α) : CF α
inductive TF : Type where
  | node (c : CF TF) : TF
