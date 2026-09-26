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
    (hnew : ∀ cvR mI rP rules, c₀ = .recInfo cvR mI rP rules →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF,
          env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → recRuleKOf env.find? r.ctor = true) ∧
        (r.eta = true → recRuleEtaOf env.find? c₀.name r.ctor = true)) :
    RecCtorsStored (⟨c₀ :: env.consts⟩ : Env) := by
  have hkeep : ∀ (m : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env.find? m = some ci → (⟨c₀ :: env.consts⟩ : Env).find? m = some ci := by
    intro m ci _ hf
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]
    exact hf
  intro n cv mI rP rules hfp r hr
  rw [Env.find?_cons] at hfp
  split at hfp
  · next hn =>
    obtain hceq := Option.some.inj hfp
    obtain ⟨⟨cvj, cnP, cnF, hf⟩, hk, he⟩ := hnew _ _ _ _ hceq r hr
    exact ⟨⟨cvj, cnP, cnF, hkeep _ _
        (fun _ _ _ _ hh => ConstantInfo.noConfusion hh) hf⟩,
      fun hb => recRuleKOf_mono hkeep (hk hb),
      fun hb => recRuleEtaOf_mono hkeep (hn ▸ he hb)⟩
  · next hn =>
    obtain ⟨⟨cvj, cnP, cnF, hf⟩, hk, he⟩ := hold n cv mI rP rules hfp r hr
    exact ⟨⟨cvj, cnP, cnF, hkeep _ _
        (fun _ _ _ _ hh => ConstantInfo.noConfusion hh) hf⟩,
      fun hb => recRuleKOf_mono hkeep (hk hb),
      fun hb => recRuleEtaOf_mono hkeep (he hb)⟩

end ConLeche
