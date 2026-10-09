module

public import ConLeche.Cached.ParsedC
import ConLeche.Verify.Cached.BlockOverlay
import ConLeche.Verify.Cached.KnotCongr

public section

/-!
# The pinned arms push onto an unshared index (task #331)

The cached driver runs `checkDeclC` (`ConLeche/Cached/ParsedC.lean`),
whose pinned `Nat`-operation and `reduce*` arms certify against an
overlay sharing the index (`FEnv.overlay`) and push only afterwards.
This file proves it equal to the reference `checkDeclCRef`, which every
other proof reads (`checkDeclC_eq_ref`): the certificates read the
pushed environment only through `find?`, and on an environment without
an overlay the overlay answers `find?` as the push does
(`find?_overlay_pushAll`, `ConLeche/Verify/Cached/BlockOverlay.lean`).
-/

namespace ConLeche.Cached

open ConLeche

/-! ## The pinned guards read the pushed environment through `find?` -/

section Congr

variable {fe₁ fe₂ : FEnv}

theorem natOpCodF_congr (hfe : fe₁.find? = fe₂.find?) (c : Name) (e : Expr) :
    natOpCodF fe₁ c e = natOpCodF fe₂ c e := by
  unfold natOpCodF; simp only [hfe]

theorem natOpTyPinnedF_congr (hfe : fe₁.find? = fe₂.find?) (c : Name) (ty : Expr) :
    natOpTyPinnedF fe₁ c ty = natOpTyPinnedF fe₂ c ty := by
  unfold natOpTyPinnedF; simp only [natOpCodF_congr hfe]

theorem natOpStoredOkF_congr (hfe : fe₁.find? = fe₂.find?) :
    natOpStoredOkF fe₁ = natOpStoredOkF fe₂ := by
  funext n; unfold natOpStoredOkF; simp only [hfe, natOpTyPinnedF_congr hfe]

theorem natOpGuardF_congr (hfe : fe₁.find? = fe₂.find?) :
    natOpGuardF fe₁ = natOpGuardF fe₂ := by
  funext c; unfold natOpGuardF; simp only [hfe, natLitSupportedF_congr hfe]

theorem divModEnvGuardF_congr (hfe : fe₁.find? = fe₂.find?) :
    divModEnvGuardF fe₁ = divModEnvGuardF fe₂ := by
  funext c; unfold divModEnvGuardF
  simp only [hfe, natOpGuardF_congr hfe, natOpStoredOkF_congr hfe]

theorem reduceStoredOkF_congr (hfe : fe₁.find? = fe₂.find?) :
    reduceStoredOkF fe₁ = reduceStoredOkF fe₂ := by
  funext c; unfold reduceStoredOkF; simp only [hfe]

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

theorem checkDivModPinF_congr2 (ops : CheckerOps m) (pins : List NatOpPinSet)
    (fe : FEnv) (hfe : fe₁.find? = fe₂.find?) (c : Name) :
    checkDivModPinF ops pins fe fe₁ c = checkDivModPinF ops pins fe fe₂ c := by
  unfold checkDivModPinF; simp only [hfe, divModEnvGuardF_congr hfe]

theorem checkReducePinF_congr2 (ops : CheckerOps m) (fe : FEnv)
    (hfe : fe₁.find? = fe₂.find?) (c : Name) (value : Expr) :
    checkReducePinF ops fe fe₁ c value = checkReducePinF ops fe fe₂ c value := by
  unfold checkReducePinF; simp only [reduceStoredOkF_congr hfe]

end Congr

/-- A one-constant overlay answers `find?` as the push, on an
environment without an overlay. -/
theorem find?_overlay_push {fe : FEnv} (h : fe.ovl = []) (ci : ConstantInfo) :
    (fe.overlay [ci]).find? = (fe.push ci).find? :=
  find?_overlay_pushAll h [ci]

/-! ## The value checks are their unpushed halves, pushed -/

private theorem ite_bindCM {α β : Type} (c : Prop) [Decidable c] (a b : CheckCM α)
    (f : α → CheckCM β) :
    (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

private theorem throw_bindCM {α β : Type} (e : CheckError) (f : α → CheckCM β) :
    (throw e : CheckCM α) >>= f = throw e := rfl

variable (mode : CheckMode)

theorem checkDefnValC_eq (fe : FEnv) (cvA : ConstantVal) (jty value : Expr)
    (hint : ReducibilityHint) :
    checkDefnValC mode fe cvA jty value hint =
      checkDefnValCI mode fe cvA jty value hint >>= fun ci => pure (fe.push ci) := by
  unfold checkDefnValC checkDefnValCI
  simp only [bind_assoc, pure_bind, ite_bindCM, throw_bindCM]

theorem checkOpaqueValC_eq (fe : FEnv) (cvA : ConstantVal) (jty value : Expr) :
    checkOpaqueValC mode fe cvA jty value =
      checkOpaqueValCI mode fe cvA jty value >>= fun ci => pure (fe.push ci) := by
  unfold checkOpaqueValC checkOpaqueValCI
  simp only [bind_assoc, pure_bind, ite_bindCM, throw_bindCM]

/-! ## The driver is the reference -/

/-- **`checkDeclC` is `checkDeclCRef`**, unconditionally. -/
theorem checkDeclC_eq_ref (pins : List NatOpPinSet) (fe : FEnv) (pd : Declaration) :
    checkDeclC mode pins fe pd = checkDeclCRef mode pins fe pd := by
  unfold checkDeclC
  by_cases hE : fe.ovl.isEmpty
  · have h : fe.ovl = [] := List.isEmpty_iff.mp hE
    simp only [hE, ↓reduceIte]
    cases pd with
    | defnDecl cv value hint =>
      unfold checkDeclCRef
      refine bind_congr fun p => ?_
      obtain ⟨cvA, jty⟩ := p
      dsimp only
      split
      · rw [checkDefnValC_eq, bind_assoc]
        refine bind_congr fun ci => ?_
        have hf := find?_overlay_push h ci
        simp only [pure_bind, hf, natOpGuardF_congr hf, natOpStoredOkF_congr hf,
          checkDivModPinF_congr2 _ _ _ hf]
      · rfl
    | opaqueDecl cv value =>
      unfold checkDeclCRef
      refine bind_congr fun p => ?_
      obtain ⟨cvA, jty⟩ := p
      dsimp only
      split
      · rw [checkOpaqueValC_eq, bind_assoc]
        refine bind_congr fun ci => ?_
        simp only [pure_bind, checkReducePinF_congr2 _ _ (find?_overlay_push h ci)]
      · rfl
    | _ => rfl
  · simp only [hE, Bool.false_eq_true, ↓reduceIte]

end ConLeche.Cached
