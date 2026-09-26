module

import ConLeche.Verify.InstLevels
public import ConLeche.Verify.Denote.Shift
public import ConLeche.Verify.Subst

public section

/-!
# Constant renaming and level instantiation, on the denotation side

`denote_renameConsts` — the transpose of `interp_renameConsts` — plus
the prefix relation the telescope folds state their domain agreement
with.

**Why the bridge needs it and `DeclBasisTT` did not.**  A pinned basis
constant has no `_model` counterpart, so nothing has to be renamed.  A
modeled block's install does: the capability pins describe the
`T._model` artifact, while the laws (`EtaLawTT`, `UnitLawTT`) are
stated at the **public** former, and `checkMemberVal`'s comparison
relates the two only *through* `renameConsts`.

`RenEqT`/`PiDomsRenEqT` are `V`-free, which is why they live here and
not in the model tier: **do not** import `ConLeche/Model/*` from this
hierarchy — the model tier (`ConLeche/Model/IndRename.lean` and the
frame files around it) imports them from here instead.
-/

namespace ConLeche.Verify

open ConLeche.Term

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-! ## Renaming constants -/

  -- (task #175 wiring W3 added a fourth, tower-freeness conjunct here
  -- because the branched `.proj` reading consulted the table at both
  -- the source and the image name; W5 fixed the struct name under
  -- `renameConsts` instead, and the conjunct is gone.)

/-! ## The domain-agreement prefix relation

Only the *first `k`* domains are constrained, and the residuals are
left free: at a fold's use site the two telescopes agree on the
parameter prefix and then diverge — the type former ends in a sort, the
checked theorem in an equation. -/

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
