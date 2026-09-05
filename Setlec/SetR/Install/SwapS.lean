import Setlec.SetR.Install.IndMembersS
import Setlec.Verify.Extend.Recs
import Setlec.Verify.Denote.EnvExt

/-!
# The group rule-list swap, [set] form (task #148, T5, stage 3a)

`EnvS.swap` transports the invariant across the step that attaches a
recursor group's checked rule lists to its rule-less provisioned
entries.  The [set] transpose of `EnvTT.swap`
(`Setlec/TTVerify/EnvSwap.lean`), over the shared shape-level swap and
its congruence bundle (`SwapShList`, `SwapCongr`,
`Setlec/Verify/Extend/Recs.lean`).

**Why a swap and not a cons-fold** (the stage-3 architecture record
above): a cons-fold of ruled recursors would leave the accumulator
without the group's later members, and a rule right-hand side that
mentions a sibling recursor then fails to denote there — so
`RecRulesV`, keyed on *every* stored `recInfo`, would be unprovable at
the intermediate environment.  The swap changes no name, so `denote`
and the valuation are untouched.

The three environment-level facts about the *result* — `EnvWF`,
`RecCtorsStored`, `RecRulesV` — are **hypotheses**: they are exactly
what the group install proves (the last from the iota bottoms through
`iotaRuleS`), and taking them here keeps the transport free of the
per-rule content.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 3200000 in
/-- **The group rule-list swap**: an invariant of the provisional
(rule-less) environment transports to the environment carrying the
checked rule lists, with the *same* valuation — definitionally, which
is what keeps the downstream rewrites away. -/
def EnvS.swap {env₀ env₃ : Env} (m₀ : EnvS V env₀)
    (hsw : SwapShList env₀.consts env₃.consts)
    (hwf : EnvWF env₃)
    (hctors : RecCtorsStored env₃)
    (hrec : ∀ φ : Name → Nat, RecRulesV V env₃ m₀.cval φ)
    (hnres : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₀.find? n = some (.recInfo cv mI rP []) →
      env₃.find? n = some (.recInfo cv mI rP rules) →
      rules = [] ∨ reservedBasisNames.contains n = false) :
    EnvS V env₃ := by
  have hcorr : ∀ n : Name,
      env₃.find? n = env₀.find? n ∨
      ∃ cv mI rP rules,
        env₀.find? n = some (.recInfo cv mI rP []) ∧
        env₃.find? n = some (.recInfo cv mI rP rules) ∧
        cv.name = n := swapSh_find?_corr hsw
  have hcg : SwapCongr env₀ env₃ := SwapShList.congr hsw
  have hde : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote m₀.cval env₀ φ d e = denote m₀.cval env₃ φ d e :=
    fun _ => denote_env_ext hcg.levelsEq hcg.natEq hcg.strEq hcg.projEq
  have hdeC : ∀ (φ : Name → Nat) (e : Expr),
      denoteClosed m₀.cval env₀ φ e = denoteClosed m₀.cval env₃ φ e :=
    fun φ e => hde φ 0 e
  -- an unchanged lookup, either way
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  refine
    { cval := m₀.cval
      cval_closed := m₀.cval_closed
      wf := hwf
      val_params := ?_
      annot_okV := m₀.annot_okV
      mem_type := ?_
      defn_eq := ?_
      thm_ok := ?_
      empty_pinned := m₀.empty_pinned
      basis_pinned := ?_
      proj_ok := ?_
      rec_ctors := hctors
      eq_lawV := ?_
      rec_rules := hrec
      caps_ok := ?_
      nat_ops := ?_
      div_mod := ?_
      reduce_ops := ?_ }
  · -- val_params: the swap keeps every stored `ConstantVal`
    intro n ci hf φ₁ φ₂ hp
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · exact m₀.val_params n ci (by rw [← heq]; exact hf) φ₁ φ₂ hp
    · rw [h₃] at hf
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n _ h₀ φ₁ φ₂ hp
  · -- mem_type: the member correspondence plus the denote congruence
    intro c₃ hc₃ φ
    obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hsw c₃ hc₃
    obtain ⟨t, ht, hd⟩ := m₀.mem_type c₀ hc₀ φ
    rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩
    · exact ⟨t, by rw [← hdeC]; exact ht, hd⟩
    · exact ⟨t, by rw [← hdeC]; exact ht, hd⟩
  · -- defn_eq: a definition is never a swap's right side
    intro cv value hint hmem φ
    obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hsw _ hmem
    rcases hpair with rfl | ⟨cv2, mI, rP, rules, rfl, heq⟩
    · rw [← hdeC]
      exact m₀.defn_eq cv value hint hc₀ φ
    · exact nomatch heq
  · -- thm_ok: likewise
    intro cv value hmem φ
    obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hsw _ hmem
    rcases hpair with rfl | ⟨cv2, mI, rP, rules, rfl, heq⟩
    · rw [← hdeC]
      exact m₀.thm_ok cv value hc₀ φ
    · exact nomatch heq
  · -- basis_pinned: reserved names are never genuinely swapped
    intro n ci hf hres
    have hf₀ : env₀.find? n = some ci := by
      rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
      · rw [← heq]; exact hf
      · rcases hnres n cv mI rP rules h₀ h₃ with rfl | hnr
        · rw [h₃] at hf
          obtain rfl := Option.some.inj hf
          exact h₀
        · rw [hnr] at hres
          exact nomatch hres
    exact m₀.basis_pinned n ci hf₀ hres
  · -- proj_ok: projection entries and their blocks are untouched
    obtain ⟨hp1, hp2, hp3⟩ := m₀.proj_ok
    refine ⟨?_, ?_, ?_⟩
    · intro n entry hf hnat
      obtain ⟨he, hps, hpm⟩ :=
        hp1 n entry ((hsame n _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hnat
      refine ⟨he, ?_, ?_⟩
      · exact (hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hps
      · exact (hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hpm
    · intro i entry hf
      exact hp2 i entry ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    · intro n entry hf
      exact hp3 n entry ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
  · -- eq_lawV: `Eq` is stored as an `indInfo`, so it is never swapped
    intro hf
    exact m₀.eq_lawV ((hsame eqName eqA
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
  · -- caps_ok: the `indInfo` entries and the family predicate are
    -- untouched, and the laws mention the environment only through
    -- `denote`
    obtain ⟨he, hu⟩ := m₀.caps_ok
    have hfam : ∀ (T : Name) (caps : IndCaps),
        EtaFamilyStored env₃ T caps → EtaFamilyStored env₀ T caps := by
      intro T caps ⟨h1, ⟨cvC, hC⟩, h3⟩
      refine ⟨h1, ⟨cvC, (hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hC⟩, ?_⟩
      intro j hj
      obtain ⟨cv, mI, rP, rules, hfj⟩ := h3 j hj
      rcases hcorr (projFnName T j) with heq | ⟨cv2, mI2, rP2, rules2,
        h₀, h₃, -⟩
      · exact ⟨cv, mI, rP, rules, by rw [← heq]; exact hfj⟩
      · exact ⟨cv2, mI2, rP2, [], h₀⟩
    refine ⟨?_, ?_⟩
    · intro T cvT caps hf hcap hres hfamS
      have h := he T cvT caps ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hcap hres
        (hfam T caps hfamS)
      intro φ' us ρ xs TV rest B hlen hTV hfit hB
      exact h φ' us ρ xs TV rest B hlen (by rw [hdeC]; exact hTV) hfit
        hB
    · intro T cvT caps hf hcap hres
      have h := hu T cvT caps ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hcap hres
      intro φ' us ρ xs TV rest x y hlen hTV hfit hx hy
      exact h φ' us ρ xs TV rest x y hlen (by rw [hdeC]; exact hTV)
        hfit hx hy
  · -- nat_ops: keyed on definitions, with the guard congruent
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hlaw⟩ := m₀.nat_ops φ c hc cv value hint
      ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    refine ⟨by rw [← hcg.guardEq]; exact hgu, ?_⟩
    intro eq heq
    obtain ⟨L, R, hL, hR, hval⟩ := hlaw eq heq
    exact ⟨L, R, by rw [← hde]; exact hL, by rw [← hde]; exact hR, hval⟩
  · -- div_mod: likewise
    intro φ c hc cv value hint hf
    obtain ⟨hgu, hlaw⟩ := m₀.div_mod φ c hc cv value hint
      ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    exact ⟨by rw [← hcg.guardEq]; exact hgu, hlaw⟩
  · -- reduce_ops: keyed on axioms
    intro c hc cv hf hpin
    obtain ⟨hs, hlaw⟩ := m₀.reduce_ops c hc cv
      ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hpin
    exact ⟨by rw [← hcg.isSomeEq]; exact hs, hlaw⟩

/-- The swap keeps the valuation — definitionally. -/
theorem EnvS.swap_cval {env₀ env₃ : Env} (m₀ : EnvS V env₀)
    (hsw : SwapShList env₀.consts env₃.consts) (hwf : EnvWF env₃)
    (hctors : RecCtorsStored env₃)
    (hrec : ∀ φ : Name → Nat, RecRulesV V env₃ m₀.cval φ)
    (hnres : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₀.find? n = some (.recInfo cv mI rP []) →
      env₃.find? n = some (.recInfo cv mI rP rules) →
      rules = [] ∨ reservedBasisNames.contains n = false) :
    (m₀.swap hsw hwf hctors hrec hnres).cval = m₀.cval := rfl

end Setlec.SetR
