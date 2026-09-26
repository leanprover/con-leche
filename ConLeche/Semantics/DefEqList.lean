module

public import ConLeche.Verify.InferLemmas

@[expose] public section

/-!
# `defEqList` / `recFireComparands` inversions (task #161, S1)

**Model-free** lemmas: pure inversions of the checker's `defEqList`
run and of `recFireComparands`, naming no valuation.
-/

namespace ConLeche.Semantics
variable {mode : CheckMode} {env : Env}

/-- The level comparand reads no arguments, in either fire branch. -/
theorem recFireComparands_fst_nil (rl : RecRule) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    (recFireComparands rl lps us cvjLps args rP).1
      = (recFireComparands rl lps us cvjLps [] rP).1 := by
  unfold recFireComparands
  cases rl.fire <;> rfl

end ConLeche.Semantics
