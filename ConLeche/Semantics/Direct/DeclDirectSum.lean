import ConLeche.Semantics.Direct.DeclDirect
import ConLeche.Verify.Direct.SumWF

/-!
# `DeclDirectSumRun`: the direct sum declaration relation (task #175
sum-types, indexed)

The direct sum arm of `checkDecl`'s `.indDecl` clause
(`checkDirectSum`, `ConLeche/Kernel/Direct/SumInstall.lean`), recorded
as a run relation exactly as `DeclDirectRun`: the two front guards
(the elimination restriction, the constructors' distinct names), the
former's run, the constructors' runs at the former's environment, the
recursor's run at the environment holding all constructors, and the
install spine.  Task #175 indexed: the stages carry `p.nIdx` and the
recursor is stored at `p.majorIdx`/`p.rulePrefix`.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  DirectSumParts RecRule fueledOps checkDirectSumInd checkDirectSumCtors
  checkDirectSumRec checkDirectSum consSumCtors directSumRules)

/-- **The direct sum declaration, as checked**: the stage runs of
`checkDirectSum`.  `env` is the pre-block environment. -/
def DeclDirectSumRun (μ : CheckMode) (F : Nat) (env : Env)
    (p : DirectSumParts) (env₂ : Env) : Prop :=
  (p.ctors.map (·.1.name)).Nodup ∧
  ∃ (cvTa : ConstantVal) (env₁ : Env) (p' : DirectSumParts)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level))
    (cvRa : ConstantVal) (rhss : List Expr),
    -- the former's run completes the record with the result sort
    -- (task #195); every later stage runs on `p'`
    checkDirectSumInd (m := ConLeche.CheckM) (fueledOps μ F) env p ConLeche.directSumCaps
      = .ok (env₁, cvTa, p') ∧
    -- the elimination restriction: a large eliminator needs a provably
    -- nonzero sort or fewer than two constructors
    (p'.large = true → p'.resSort.isNeverZero = true ∨ p'.ctors.length < 2) ∧
    checkDirectSumCtors (m := ConLeche.CheckM) (fueledOps μ F) env env₁ p'.cvT.name
      p'.cvT.levelParams p'.nP p'.nIdx p'.resSort p'.isProp p'.large cvTa p'.ctors
      = .ok (ctorsA, sortss) ∧
    checkDirectSumRec (m := ConLeche.CheckM) (fueledOps μ F) (consSumCtors p'.nP ctorsA env₁)
      p' cvTa ctorsA = .ok (cvRa, rhss) ∧
    env₂ = ⟨.recInfo cvRa p'.majorIdx p'.rulePrefix
      (directSumRules p'.nP p'.majorIdx p'.rulePrefix cvRa.type ctorsA rhss)
      :: (consSumCtors p'.nP ctorsA env₁).consts⟩

/-- The bridge inversion: the monad-shape argument, one `cases` per
bind, the two guards by cases. -/
theorem declDirectSumRun_of {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : DirectSumParts}
    (h : checkDirectSum (m := ConLeche.CheckM) (fueledOps μ F) env p = .ok env₂) :
    DeclDirectSumRun μ F env p env₂ := by
  rw [checkDirectSum] at h
  simp only [bind, Except.bind] at h
  -- the distinct-names guard
  by_cases hnd : (p.ctors.map (·.1.name)).Nodup
  case neg =>
    rw [if_neg hnd] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hnd] at h
  try simp only [bind, Except.bind] at h
  cases hInd : checkDirectSumInd (m := ConLeche.CheckM) (fueledOps μ F) env p
      ConLeche.directSumCaps with
  | error e => rw [hInd] at h; exact nomatch h
  | ok r₁ =>
  obtain ⟨env₁, cvTa, p'⟩ := r₁
  rw [hInd] at h
  dsimp only at h
  -- the elimination guard, at the completed record
  by_cases hg : (p'.large && !p'.resSort.isNeverZero && decide (2 ≤ p'.ctors.length)) = true
  · rw [if_pos hg] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_neg hg] at h
  have helim : p'.large = true → p'.resSort.isNeverZero = true ∨ p'.ctors.length < 2 := by
    intro hl
    cases hz : p'.resSort.isNeverZero with
    | true => exact Or.inl rfl
    | false =>
      refine Or.inr ?_
      rcases Nat.lt_or_ge p'.ctors.length 2 with hlt | hge
      · exact hlt
      · exfalso
        apply hg
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
        exact ⟨⟨hl, hz⟩, hge⟩
  try simp only [bind, Except.bind] at h
  cases hCtors : checkDirectSumCtors (m := ConLeche.CheckM) (fueledOps μ F) env env₁
      p'.cvT.name p'.cvT.levelParams p'.nP p'.nIdx p'.resSort p'.isProp p'.large cvTa
      p'.ctors with
  | error e => rw [hCtors] at h; exact nomatch h
  | ok r₂ =>
  obtain ⟨ctorsA, sortss⟩ := r₂
  rw [hCtors] at h
  dsimp only at h
  cases hRec : checkDirectSumRec (m := ConLeche.CheckM) (fueledOps μ F)
      (consSumCtors p'.nP ctorsA env₁) p' cvTa ctorsA with
  | error e => rw [hRec] at h; exact nomatch h
  | ok r₃ =>
  obtain ⟨cvRa, rhss⟩ := r₃
  rw [hRec] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨hnd, cvTa, env₁, p', ctorsA, sortss, cvRa, rhss, hInd, helim, hCtors, hRec, h.symm⟩

/-- The direct sum arm keeps the environment well-formed. -/
theorem declDirectSumRun_wf {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : DirectSumParts} (henv : ConLeche.EnvWF env)
    (h : DeclDirectSumRun μ F env p env₂) : ConLeche.EnvWF env₂ := by
  obtain ⟨-, cvTa, env₁, p', ctorsA, sortss, cvRa, rhss, hInd, -, hCtors, hRec, rfl⟩ := h
  obtain ⟨henv₁, -⟩ := ConLeche.direct_sum_ind_wf henv hInd
  obtain ⟨hlen, -, hall⟩ := ConLeche.checkDirectSumCtors_inv hCtors
  have henv₂ : ConLeche.EnvWF (consSumCtors p'.nP ctorsA env₁) := by
    refine ConLeche.envWF_consSumCtors henv₁ ?_
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p'.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, _, -, hrun⟩ := hall j (p'.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    exact ConLeche.direct_sum_ctor_typeWF hrun
  exact ConLeche.direct_sum_rec_wf henv₂ hRec

/-! The `.indDecl` run dispatch (`DeclIndRunDispatch`) lives in
`ConLeche/Semantics/Direct/DeclDirectFix.lean`, below the recursive arm
(task #188). -/

end ConLeche.Semantics
