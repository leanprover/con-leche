module

import ConLeche.Verify.InstLevels
public import ConLeche.Verify.Denote.Shift
public import ConLeche.Verify.Subst

public section

/-!
# Constant renaming and level instantiation, on the denotation side

`RenEqT`: two expressions related by constant renaming, modulo the
positions the denotation never reads.  It is `V`-free, which is why it
lives here and not in the model tier: **do not** import
`ConLeche/Model/*` from this hierarchy — the model tier imports it from
here instead.
-/

namespace ConLeche.Verify

open ConLeche.Term

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- Related by constant renaming, modulo the positions the denotation
never reads. -/
@[expose] def RenEqT (f : Name → Name) (e₁ e₂ : Expr) : Prop :=
  Expr.ErasedEq (e₁.renameConsts f) e₂

/-- Renamed-equality survives instantiating both sides with related
arguments. -/
theorem RenEqT.instantiate1 {f : Name → Name} {e₁ e₂ a₁ a₂ : Expr} {k : Nat}
    (he : RenEqT f e₁ e₂) (ha : RenEqT f a₁ a₂) :
    RenEqT f (e₁.instantiate1 a₁ k) (e₂.instantiate1 a₂ k) := by
  unfold RenEqT
  rw [Expr.renameConsts_instantiate1_gen]
  exact Expr.ErasedEq.instantiate1 he ha

/-- **Two telescopes' opening variables are renamed-equal**, whatever
their binders were called and whatever they were annotated with:
`renameConsts` reaches only the annotation, and erasure compares only
the index.  This is what lets one alignment step open *both* sides. -/
theorem RenEqT.fvar {f : Name → Name} {i : Nat}
    {ty ty' : Expr} : RenEqT f (.fvar i ty) (.fvar i ty') := by
  show Expr.ErasedEq (.fvar i (ty.renameConsts f)) (.fvar i ty')
  rfl

end ConLeche.Verify
