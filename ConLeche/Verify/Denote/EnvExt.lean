module

public import ConLeche.Verify.Denote

public section

/-!
# Denotation across level-preserving environment correspondences

The denotation reads the environment only through the stored level
parameters and the two literal guards, so it is invariant across any
correspondence preserving those.
-/

namespace ConLeche.Verify

open ConLeche.Term

/-- The stored level parameters only read the constant's
level-parameter slot. -/
theorem levelParamsAt_ext {env₁ env₂ : Env} {n : Name}
    (h : (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
      (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams)) :
    levelParamsAt env₁ n = levelParamsAt env₂ n := by
  unfold levelParamsAt
  cases h1 : env₁.find? n <;> cases h2 : env₂.find? n <;>
    rw [h1, h2] at h <;> simp at h ⊢ <;> exact h

end ConLeche.Verify
