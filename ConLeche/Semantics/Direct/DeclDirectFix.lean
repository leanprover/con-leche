import ConLeche.Semantics.Direct.DeclDirectSum
import ConLeche.Verify.Direct.FixWF

/-!
# `DeclDirectFixRun`: the direct recursive declaration relation
(task #188)

The direct recursive arm of `checkDecl`'s `.indDecl` clause
(`checkDirectFix`, `ConLeche/Kernel/Direct/RecInstall.lean`), recorded as
a run relation exactly as `DeclDirectSumRun`: the three front guards
(positivity — no negative field kind; the elimination restriction —
a large eliminator needs a provably nonzero sort, the one-constructor
`Prop` case being declined; the constructors' distinct names), the
former's run (the sum's stage), the constructors' runs at the
former's environment with the resolution guard pointed at that same
environment, the field kinds re-checked on the annotated types, the
recursor's run at the environment holding all constructors, and the
install spine.  The `.indDecl` run dispatch, with the recursive arm
below the two non-recursive ones, closes the module.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  DirectSumParts DirectFixParts RecRule fueledOps checkDirectSumInd checkDirectSumCtors
  checkDirectFixRec checkDirectFix consSumCtors directSumRules directFixFieldsOk)

/-- **The direct recursive declaration, as checked**: the stage runs
of `checkDirectFix`.  `env` is the pre-block environment. -/
def DeclDirectFixRun (μ : CheckMode) (F : Nat) (env : Env)
    (p : DirectFixParts) (env₂ : Env) : Prop :=
  -- positivity: no non-positive occurrence
  p.kinds.any (fun ks => ks.any (· == .negative)) = false ∧
  -- the elimination restriction: a large eliminator needs a provably
  -- nonzero sort unless the block has one constructor (the subsingleton
  -- case, task #202 Stage A2)
  (p.large = true → p.resSort.isNeverZero = true ∨ p.ctors.length < 2) ∧
  (p.ctors.map (·.1.name)).Nodup ∧
  ∃ (cvTa : ConstantVal) (env₁ : Env) (p₁ : DirectSumParts)
    (ctorsA : List (ConstantVal × Nat))
    (cvRa : ConstantVal) (rhss : List Expr) (tfvs : List Expr) (trest : Expr)
    (isorts : List Level),
    -- the former's run completes the record with the sort it read
    -- (task #195); the recursive route runs on its own syntactic record
    -- and pins the two sorts equal
    checkDirectSumInd (m := ConLeche.CheckM) (fueledOps μ F) env p.toDirectSumParts
      = .ok (env₁, cvTa, p₁) ∧
    p₁.resSort = p.resSort ∧
    openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest) ∧
    ConLeche.checkDirectFieldSortsI (m := ConLeche.CheckM) (fueledOps μ F) env₁ true false p.resSort
      p.nP (tfvs.drop p.nP) [] p.nIdx = .ok isorts ∧
    checkDirectSumCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁ p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors = .ok ctorsA ∧
    directFixFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA p.kinds = true ∧
    checkDirectFixRec (m := ConLeche.CheckM) (fueledOps μ F) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) ∧
    env₂ = ⟨.recInfo cvRa p.majorIdx p.rulePrefix
      (directSumRules p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
      :: (consSumCtors p.nP ctorsA env₁).consts⟩

/-- The bridge inversion: the monad-shape argument, one `cases` per
bind, the guards by cases. -/
theorem declDirectFixRun_of {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : DirectFixParts}
    (h : checkDirectFix (m := ConLeche.CheckM) (fueledOps μ F) env p = .ok env₂) :
    DeclDirectFixRun μ F env p env₂ := by
  rw [checkDirectFix] at h
  simp only [bind, Except.bind] at h
  -- positivity
  by_cases hneg : p.kinds.any (fun ks => ks.any (· == .negative)) = true
  · rw [if_pos hneg] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_neg hneg] at h
  -- the elimination guard
  by_cases hg : (p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length)) = true
  · rw [if_pos hg] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_neg hg] at h
  have helim : p.large = true → p.resSort.isNeverZero = true ∨ p.ctors.length < 2 := by
    intro hl
    cases hz : p.resSort.isNeverZero with
    | true => exact Or.inl rfl
    | false =>
      right
      exact Classical.byContradiction fun hge => hg (by simp [hl, hz]; omega)
  -- the distinct-names guard
  by_cases hnd : (p.ctors.map (·.1.name)).Nodup
  case neg =>
    rw [if_neg hnd] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hnd] at h
  try simp only [bind, Except.bind] at h
  cases hInd : checkDirectSumInd (m := ConLeche.CheckM) (fueledOps μ F) env p.toDirectSumParts with
  | error e => rw [hInd] at h; exact nomatch h
  | ok r₁ =>
  obtain ⟨env₁, cvTa, p₁⟩ := r₁
  rw [hInd] at h
  dsimp only at h
  by_cases hsort : (p₁.resSort == p.resSort) = true
  case neg =>
    rw [if_neg hsort] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hsort] at h
  try simp only [bind, Except.bind] at h
  cases htq : openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 with
  | none =>
    rw [htq] at h
    exact absurd h (by simp [unwrapOr, throw, throwThe, MonadExceptOf.throw])
  | some tq =>
  obtain ⟨tfvs, trest⟩ := tq
  rw [htq] at h
  simp only [unwrapOr, pure, Except.pure] at h
  cases hsorts : ConLeche.checkDirectFieldSortsI (m := ConLeche.CheckM) (fueledOps μ F) env₁ true false
      p.resSort p.nP (tfvs.drop p.nP) [] p.nIdx with
  | error e => rw [hsorts] at h; exact nomatch h
  | ok isorts =>
  rw [hsorts] at h
  dsimp only at h
  cases hCtors : checkDirectSumCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁
      p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors with
  | error e => rw [hCtors] at h; exact nomatch h
  | ok ctorsA =>
  rw [hCtors] at h
  dsimp only at h
  by_cases hk : directFixFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      p.kinds = true
  case neg =>
    rw [if_neg hk] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hk] at h
  try simp only [bind, Except.bind] at h
  cases hRec : checkDirectFixRec (m := ConLeche.CheckM) (fueledOps μ F)
      (consSumCtors p.nP ctorsA env₁) p cvTa ctorsA with
  | error e => rw [hRec] at h; exact nomatch h
  | ok r₃ =>
  obtain ⟨cvRa, rhss⟩ := r₃
  rw [hRec] at h
  simp only [Except.ok.injEq] at h
  exact ⟨by simpa using hneg, helim, hnd, cvTa, env₁, p₁, ctorsA, cvRa, rhss, tfvs, trest, isorts,
    hInd, by simpa using hsort, htq, hsorts, hCtors, hk, hRec, h.symm⟩

/-- The direct recursive arm keeps the environment well-formed. -/
theorem declDirectFixRun_wf {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : DirectFixParts} (henv : ConLeche.EnvWF env)
    (h : DeclDirectFixRun μ F env p env₂) : ConLeche.EnvWF env₂ := by
  obtain ⟨-, -, -, cvTa, env₁, p₁, ctorsA, cvRa, rhss, -, -, -, hInd, -, -, -, hCtors, -, hRec,
    rfl⟩ := h
  obtain ⟨henv₁, -⟩ := ConLeche.direct_sum_ind_wf henv hInd
  obtain ⟨hlen, hall⟩ := ConLeche.checkDirectSumCtors_inv hCtors
  have henv₂ : ConLeche.EnvWF (consSumCtors p.nP ctorsA env₁) := by
    refine ConLeche.envWF_consSumCtors henv₁ ?_
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    exact ConLeche.direct_sum_ctor_typeWF hrun
  exact ConLeche.direct_fix_rec_wf henv₂ hRec

/-! ## The run-level dispatch

`checkDeclRun_ofEnvFactsE`'s `Ind` slot: the direct structure arm,
the direct sum arm, the direct recursive arm, the modeled arm — the
kernel's own three-stage case split (`directParts?`, then
`directSumParts?`, then `directFixParts?`). -/

/-- The `.indDecl` dispatch at the run level. -/
def DeclIndRunDispatch (μ : CheckMode) (F : Nat) (env : Env)
    (block : List ConstantInfo) (env₂ : Env) : Prop :=
  match ConLeche.directParts? env block with
  | some p => DeclDirectRun μ F env p env₂
  | none =>
    match ConLeche.directSumParts? env block with
    | some p => DeclDirectSumRun μ F env p env₂
    | none =>
      match ConLeche.directFixParts? block with
      | some p => DeclDirectFixRun μ F env p env₂
      | none => DeclIndRun μ F env block env₂

end ConLeche.Semantics
