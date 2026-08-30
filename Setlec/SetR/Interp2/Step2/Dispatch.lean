import Setlec.SetR.Interp2.Step2.Lit

/-!
# `CheckStep2`, the dispatch — the clause lemmas against the runs

Where the per-clause lemmas of `Step2/{Infer,WhnfCore,DefEq,Loop}.lean`
meet the checker's own case split.  One lemma per `inferBody` branch,
shaped exactly as `Bridge/Infer.lean`'s `infer_*_claimR` family, with
the conclusion in the annotated currency.

The unfolding recipe is v1's, verbatim — `rw [inferTypeCore_succ]` then
`simp only [inferBody, viewM, Expr.view, …]` — and it transfers
unchanged, because the *checker* is the same function; only what the
clause then produces differs.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level inferTypeCore inferBody
  viewM)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- **I1 (`.sort`).**  The clause returns `.sort (.succ u)` outright,
`denote2` evaluates both levels, and the row is `sound_sort`. -/
theorem infer_sort_claim2 (m : EnvS2 V env) {d : Nat} {u : Level}
    {t : Expr} {Δa : List AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.sort u) = .ok t) :
    ∃ ea ta,
      denote2 μ m.acval env φ (fuel + 1) d (.sort u) = some ea ∧
      denote2 μ m.acval env φ (fuel + 1) d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind, Except.ok.injEq] at h
  subst h
  refine ⟨.sort (u.eval φ), .sort (u.eval φ + 1), ?_, ?_, ?_⟩
  · rw [denote2]
  · rw [denote2]; simp [Level.eval]
  · intro ρ _
    simpa [Level.eval] using sound_sort V ρ (u.eval φ)

end Setlec.SetR.Interp2
