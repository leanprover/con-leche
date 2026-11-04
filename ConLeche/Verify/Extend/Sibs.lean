module

public import ConLeche.Verify.EnvPreds

public section

/-!
# Sibs

The per-clause preservation (`.cons`) lemma for extending an environment
by one fresh constant at a clause that is a statement about the
environment alone: `RecCtorsStored`.

The valuation-carrying clauses of the same cons are preserved one tier
up, in `ConLeche/Model/Install.lean`.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

open Expr

/-- `RecCtorsStored` is preserved by a fresh extension, given the
stored-constructor facts for the new member (vacuous unless it is a
recursor). -/
theorem RecCtorsStored.cons {env : Env} {c₀ : ConstantInfo}
    (hold : RecCtorsStored env) (hfresh : env.find? c₀.name = none)
    (hnew : ∀ cvR mI rP isK rules, c₀ = .recInfo cvR mI rP isK rules →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF,
          env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))) :
    RecCtorsStored (⟨c₀ :: env.consts, env.tables⟩ : Env) := by
  have hkeep : ∀ (m : Name) (ci : ConstantInfo),
      (∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) →
      env.find? m = some ci → (⟨c₀ :: env.consts, env.tables⟩ : Env).find? m = some ci := by
    intro m ci _ hf
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]
    exact hf
  intro n cv mI rP isK rules hfp r hr
  rw [Env.find?_cons] at hfp
  split at hfp
  · next hn =>
    obtain hceq := Option.some.inj hfp
    obtain ⟨cvj, cnP, cnF, hf⟩ := hnew _ _ _ _ _ hceq r hr
    exact ⟨cvj, cnP, cnF, hkeep _ _
        (fun _ _ _ _ _ hh => ConstantInfo.noConfusion hh) hf⟩
  · next hn =>
    obtain ⟨cvj, cnP, cnF, hf⟩ := hold n cv mI rP isK rules hfp r hr
    exact ⟨cvj, cnP, cnF, hkeep _ _
        (fun _ _ _ _ _ hh => ConstantInfo.noConfusion hh) hf⟩

end ConLeche
