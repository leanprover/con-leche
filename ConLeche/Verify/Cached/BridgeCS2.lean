module

public import ConLeche.Verify.Cached.BridgeCS1

public section

/-!
# Cached shared-state walks, part 2: the inductive-install checker
functions

The cached tier's `SimC` form of `unwrapOr`.
-/

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr

variable {mode : CheckMode}

section Walks2

variable {env : Env} {s₀ : CState}

/-- `unwrapOr` as a `SimC`, remembering the unwrapped value. -/
protected theorem SimC.unwrapOr' {α : Type} {o : Option α}
    {err : CheckError} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ o = some v)
      (unwrapOr o err : CheckCM α) (unwrapOr o err : FueledM α) := by
  cases o with
  | none => exact SimC.throw
  | some a => exact SimC.pure hs ⟨rfl, rfl⟩

end Walks2

end ConLeche.Cached
