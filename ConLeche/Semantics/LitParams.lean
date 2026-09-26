module

public import ConLeche.Kernel.Core

@[expose] public section

/-!
# The literal families carry no level parameters

Two theorems that read one arity conjunct off the
literal support guards (`natLitSupported`'s `natIndOk`,
`strLitSupported`'s `stringTyOk`) and say the stored declaration has an
empty `levelParams` list.  No model, no environment invariant — pure
`Env`/`ConstantInfo` arithmetic.
-/

namespace ConLeche.Semantics

/-- The `Nat` family's stored declaration carries no level parameters
(read off `natLitSupported`'s `natIndOk` conjunct). -/
theorem natName_levelParams_nil {env : Env}
    (hg : natLitSupported env = true) {ci : ConstantInfo}
    (hf : env.find? natName = some ci) :
    ci.toConstantVal.levelParams = [] := by
  simp only [natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨h1, -⟩, -⟩ := hg
  rw [hf] at h1
  cases ci with
  | indInfo cv caps =>
    simp only [natIndOk, Bool.and_eq_true] at h1
    simpa [ConstantInfo.toConstantVal, List.isEmpty_iff] using h1.1
  | _ => simp [natIndOk] at h1

end ConLeche.Semantics
