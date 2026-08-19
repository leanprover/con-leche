import Setlec.Kernel.Checker

/-!
# Basic facts about the checker

Verification of `Setlec.Kernel.Checker`.  Implementation modules
(`Setlec.Kernel.*`) never import verification modules; all proofs about the
checker live here or in `Setlec.Model.*`.
-/

namespace Setlec

theorem checkDecl_error (env : Env) (d : Declaration) :
    checkDecl env d = .error (.notImplemented d) := rfl

/-- The trivial checker accepts only the empty list of declarations, and then
returns the empty environment. -/
theorem checkDecls_ok {ds : List Declaration} {env : Env}
    (h : checkDecls ds = .ok env) : ds = [] ∧ env = Env.empty := by
  cases ds with
  | nil =>
    simp only [checkDecls, List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨rfl, h.symm⟩
  | cons d ds =>
    simp [checkDecls, List.foldlM, checkDecl, Bind.bind, Except.bind] at h

end Setlec
