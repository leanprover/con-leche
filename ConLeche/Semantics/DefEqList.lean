module

public import ConLeche.Verify.InferLemmas

@[expose] public section

/-!
# `defEqList` / `recFireComparands` inversions (task #161, S1)

THE SEPARATION's shared base: three lemmas that were filed in
`SetR/Bridge/Iota.lean` (the R lane's `IotaStepR` discharge) but are
**model-free** — pure inversions of the checker's `defEqList` run and of
`recFireComparands`, naming no `EnvS`, no valuation and no relation of
the `Infer`/`DefEq` family.  Both lanes consume them: `Bridge/Iota.lean`
for `iota_stepR`, `Interp/Steps/IotaRows.lean` for the graded lane's
`IotaStep` (design census §3.3, edge 13).

Statements verbatim from their old home; the namespace is unchanged.
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
