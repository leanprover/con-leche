module

public import ConLeche.Kernel.DeclCheck
import ConLeche.Verify.Cached.BlockOverlay
import ConLeche.Verify.Cached.KnotCongr

public section

/-!
# The pinned arms read the pushed environment through `find?` (task #331)

The cached driver's pinned `Nat`-operation and `reduce*` arms
(`checkDeclC`, `ConLeche/Cached/ParsedC.lean`) certify against an
overlay sharing the index (`FEnv.overlay`) and push only afterwards.
The facts the proofs about those arms need: the guards and pin checks
read the "after" environment only through `find?` (the `_congr`
lemmas), and on an environment without an overlay a one-constant
overlay answers `find?` as the push does (`find?_overlay_push`, from
`find?_overlay_pushAll`, `ConLeche/Verify/Cached/BlockOverlay.lean`).
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

end ConLeche.Cached
