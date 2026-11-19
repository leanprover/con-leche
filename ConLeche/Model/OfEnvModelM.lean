module

public import ConLeche.Model.Denotes
import ConLeche.Model.RuleEqsSound

public section

/-!
# The model the invariant carries

`Model.ofEnvModelM`: `Model V env` (`ConLeche/Denotes.lean`) from the graded invariant
`EnvModelM V env`, through the bridge `Denotes_of_denote` (`Model/Denotes.lean`):

* `mem` from `type_reads` and `mem_type` at depth `0` (a stored type has no `fvar`, so it is its
  own closure);
* `false_empty` from the pinned `False` leaf (`EnvModel.acval_pinned`: the leaf is
  `.const .empty [0]`, whose interpretation is the empty set);
* `eq_equality` from the invariant's `eq_law` (`eq_equality_of`);
* `rule_eqs` from the rules' forward fit and law (`RecRuleFit`, the last conjunct of every
  stored rule's `RecRuleLaw`) and `Eq`'s law (`ruleEqsHold_of`, `Model/RuleEqsSound.lean`);
* `defn_eq` from `defn_reads`.
-/

namespace ConLeche.Model
open ConLeche.Semantics ConLeche.SetModel ConLeche.Verify SetTheory
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantInfo)
open ConLeche.Expr (closeN)

universe w

variable {V : Type w} [SetTheory V]

/-! ### The model -/

/-- **`Eq` is set equality in the invariant's leaves**: the invariant's `eq_law`, whose value
clause is the three-fold application, at the stored `Eq` (`eq_law` is premised on the *pinned*
`Eq` being stored, and the `Denotes` hypothesis supplies only that *something* is stored at
`eqName`; `basis_pinned`'s declaration clause joins the two, as it holds of a stored reserved
name whatever its kind). -/
theorem eq_equality_of {env : Env} (m : EnvModelM V env) :
    ∀ (u : Level) (φ : Name → Nat) (ρ : Nat → V) (E A a b : V),
      ConLeche.Denotes (cvalOf m.base2.acval) env φ ρ (.const ConLeche.eqName [u]) E →
      A ∈ˢ (univ (Level.eval φ u) : V) → a ∈ˢ A → b ∈ˢ A →
      app (app (app E A) a) b = eqv a b := by
  intro u φ ρ E A a b h hA ha hb
  cases h with
  | const hf hlen =>
    rename_i ci
    obtain ⟨-, -, hl⟩ := (m.base2.basis_pinned _ _ hf (by decide)).1
    have hl' : ci.toConstantVal.levelParams.length = 1 := hl
    match hq : ci.toConstantVal.levelParams, hl' with
    | [p], _ =>
    have hψ : Level.substFn φ [p] [u] p = Level.eval φ u := by
      simp [Level.substFn]
    have hlaw := (m.eq_law ci p hf hq (Level.substFn φ [p] [u])).1 ρ A a b
      (by rw [hψ]; exact hA) ha hb
    rw [interp_cvalOf m.base2.cval_closed] at hlaw
    exact hlaw


/-- **The model, read off the invariant**: `Model V env` from
`EnvModelM V env`. -/
noncomputable def Model.ofEnvModelM {env : Env}
    (m : EnvModelM V env) : ConLeche.Model V env where
  cval := cvalOf m.base2.acval
  mem := by
    intro c hc φ ρ
    obtain ⟨ta, hta⟩ := m.type_reads c hc φ
    have hwf := m.base2.wf.consts c hc
    have hnf : c.toConstantVal.type.hasFvar = false := hwf.1
    have hlb : c.toConstantVal.type.looseBVarsBounded 0 = true := hwf.2.2.2.1
    have hbr := Denotes_of_denote (V := V) m.base2.cval_closed 0
      c.toConstantVal.type hta (fvarsBelow_zero_of_not_hasFvar hnf) hlb ρ
    rw [Expr.closeN_of_hasFvar _ 0 0 hnf] at hbr
    refine ⟨interp V ρ ta, hbr, ?_⟩
    rw [← interp_cvalOf m.base2.cval_closed]
    exact m.mem_type c hc φ ta hta ρ
  false_empty := by
    intro φ ρ F h
    suffices hs : ∀ (ψ : Name → Nat) (ci : ConstantInfo),
        env.find? falseName = some ci →
        cvalOf (V := V) m.base2.acval falseName ψ = SetTheory.empty by
      cases h with
      | const hf hlen => exact hs _ _ hf
    intro ψ ci hf
    have hpd : ∀ ψ' : Name → Nat, ConLeche.Verify.pinnedStructT falseName ψ'
        = some (Term.const .empty [0]) := fun _ => by
      simp +decide [ConLeche.Verify.pinnedStructT]
    have he : (m.base2.acval falseName ψ) = Term.const .empty [0] :=
      m.base2.acval_pinned_free hf (by decide) hpd
    rw [cvalOf, he, interp_const]
    rfl
  eq_equality := eq_equality_of m
  rule_eqs := ruleEqsHold_of m
    (fun φ n cv mI rP isK rules hf rl hrl => (m.rec_rules φ n cv mI rP isK rules hf rl hrl).2.2.2)
    (eq_equality_of m)
  defn_eq := by
    intro cv value hint hmem φ ρ
    obtain ⟨t, ht, hl⟩ := m.defn_reads φ cv value ⟨hint, hmem⟩
    obtain ⟨-, -, -, -, hv, -⟩ := m.base2.wf.consts _ hmem
    obtain ⟨hnf, -, -, hlb⟩ := hv cv value hint rfl
    have hbr := Denotes_of_denote (V := V) m.base2.cval_closed 0 value ht
      (fvarsBelow_zero_of_not_hasFvar hnf) hlb ρ
    rw [Expr.closeN_of_hasFvar _ 0 0 hnf] at hbr
    suffices hs : interp V ρ t = cvalOf m.base2.acval cv.name φ by rwa [hs] at hbr
    rw [← interp_cvalOf m.base2.cval_closed cv.name φ ρ]
    rcases hl with rfl | ⟨hp, hpt⟩
    · rfl
    · rw [hp, (hpt ρ).2, interp_prf]


/-- The model's values are the invariant's leaves'. -/
theorem Model.ofEnvModelM_cval {env : Env} (m : EnvModelM V env) :
    (Model.ofEnvModelM m).cval = cvalOf m.base2.acval := by rfl

end ConLeche.Model
