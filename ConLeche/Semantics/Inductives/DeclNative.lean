import ConLeche.Semantics.DeclIndRun
import ConLeche.Verify.Inductives.SumWF
import ConLeche.Verify.Inductives.FixWF

/-!
# `DeclNativeRun`: the direct recursive declaration relation
(task #188)

The direct recursive arm of `checkDecl`'s `.indDecl` clause
(`checkNative`, `ConLeche/Kernel/Inductives/NativeInstall.lean`), recorded as
a run relation exactly as `DeclSumRun`: the three front guards
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
  InductiveShape NativeParts RecRule fueledOps checkSumInd checkSumCtors
  checkNativeRec checkNative checkNativeTable consSumCtors sumRules
  nativeFieldsOk nativeCaps)

/-- **The direct recursive declaration, as checked**: the stage runs
of `checkNative`.  `env` is the pre-block environment. -/
def DeclNativeRun (μ : CheckMode) (F : Nat) (env : Env)
    (p₀ : NativeParts) (env₂ : Env) : Prop :=
  (p₀.ctors.map (·.1.name)).Nodup ∧
  ∃ (envP : Env) (cvTaP : ConstantVal) (p₁P : InductiveShape) (ctorsP : List (ConstantVal × Nat))
    (sortssP : List (List Level)) (kinds : List (List RecFieldKind)),
    -- the provisional pass (task #210 Part D): the kinds, classified on
    -- the constructors normalised at a throwaway former
    checkSumInd (m := ConLeche.CheckM) (fueledOps μ F) env p₀.toInductiveShape
      (fun _ => {}) = .ok (envP, cvTaP, p₁P) ∧
    checkSumCtors (m := ConLeche.CheckM) (fueledOps μ F) envP envP
      (p₀.complete p₁P).cvT.name (p₀.complete p₁P).cvT.levelParams (p₀.complete p₁P).nP
      (p₀.complete p₁P).nIdx (p₀.complete p₁P).resSort (p₀.complete p₁P).isProp
      (p₀.complete p₁P).large cvTaP (p₀.complete p₁P).ctors = .ok (ctorsP, sortssP) ∧
    classifyFixKinds (m := ConLeche.CheckM) (p₀.complete p₁P).cvT.name
      (p₀.complete p₁P).cvT.levelParams (p₀.complete p₁P).nP (p₀.complete p₁P).nIdx ctorsP
      = .ok kinds ∧
  ∃ (cvTa : ConstantVal) (env₁ : Env) (p₁ : InductiveShape) (p : NativeParts)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level))
    (cvRa : ConstantVal) (rhss : List Expr) (tfvs : List Expr) (trest : Expr)
    (isorts : List Level),
    -- the former's run completes the record with the sort it read
    -- (task #195; task #210 Part B: this route too); every later stage
    -- runs on the completed record `p` — the sort and the kinds — whose
    -- capability record (`nativeCaps`, Part A) the former carries
    checkSumInd (m := ConLeche.CheckM) (fueledOps μ F) env p₀.toInductiveShape
      (fun p₁ => nativeCaps ((p₀.complete p₁).withKinds kinds)) = .ok (env₁, cvTa, p₁) ∧
    p = (p₀.complete p₁).withKinds kinds ∧
    -- the elimination restriction: a large eliminator needs a provably
    -- nonzero sort unless the block has one constructor (the subsingleton
    -- case, task #202 Stage A2)
    (p.large = true → p.resSort.isNeverZero = true ∨ p.ctors.length < 2) ∧
    openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest) ∧
    ConLeche.checkStructFieldSortsI (m := ConLeche.CheckM) (fueledOps μ F) env₁ true false p.resSort
      p.nP (tfvs.drop p.nP) [] p.nIdx = .ok isorts ∧
    checkSumCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁ p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors
      = .ok (ctorsA, sortss) ∧
    nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA p.kinds = true ∧
    nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP p.ctors.length
      ctorsA p.kinds p.rhss = true ∧
    checkNativeRec (m := ConLeche.CheckM) (fueledOps μ F) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) ∧
    -- the projection table at a structure-like block (task #210 Part A)
    checkNativeTable (m := ConLeche.CheckM) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: (consSumCtors p.nP ctorsA env₁).consts⟩ = .ok env₂

/-- The bridge inversion: the monad-shape argument, one `cases` per
bind, the guards by cases. -/
theorem declNativeRun_of {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p₀ : NativeParts}
    (h : checkNative (m := ConLeche.CheckM) (fueledOps μ F) env p₀ = .ok env₂) :
    DeclNativeRun μ F env p₀ env₂ := by
  rw [checkNative] at h
  simp only [bind, Except.bind] at h
  -- the distinct-names guard
  by_cases hnd : (p₀.ctors.map (·.1.name)).Nodup
  case neg =>
    rw [if_neg hnd] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hnd] at h
  try simp only [bind, Except.bind] at h
  -- the provisional pass
  cases hIndP : checkSumInd (m := ConLeche.CheckM) (fueledOps μ F) env p₀.toInductiveShape
      (fun _ => {}) with
  | error e => rw [hIndP] at h; exact nomatch h
  | ok rP =>
  obtain ⟨envP, cvTaP, p₁P⟩ := rP
  rw [hIndP] at h
  dsimp only at h
  cases hCtorsP : checkSumCtors (m := ConLeche.CheckM) (fueledOps μ F) envP envP
      (p₀.complete p₁P).cvT.name (p₀.complete p₁P).cvT.levelParams (p₀.complete p₁P).nP
      (p₀.complete p₁P).nIdx (p₀.complete p₁P).resSort (p₀.complete p₁P).isProp
      (p₀.complete p₁P).large cvTaP (p₀.complete p₁P).ctors with
  | error e => rw [hCtorsP] at h; exact nomatch h
  | ok rP₂ =>
  obtain ⟨ctorsP, sortssP⟩ := rP₂
  rw [hCtorsP] at h
  dsimp only at h
  cases hK : classifyFixKinds (m := ConLeche.CheckM) (p₀.complete p₁P).cvT.name
      (p₀.complete p₁P).cvT.levelParams (p₀.complete p₁P).nP (p₀.complete p₁P).nIdx ctorsP with
  | error e => rw [hK] at h; exact nomatch h
  | ok kinds =>
  rw [hK] at h
  dsimp only at h
  -- the former
  cases hInd : checkSumInd (m := ConLeche.CheckM) (fueledOps μ F) env p₀.toInductiveShape
      (fun p₁ => nativeCaps ((p₀.complete p₁).withKinds kinds)) with
  | error e => rw [hInd] at h; exact nomatch h
  | ok r₁ =>
  obtain ⟨env₁, cvTa, p₁⟩ := r₁
  rw [hInd] at h
  dsimp only at h
  -- the completed record
  generalize hp : (p₀.complete p₁).withKinds kinds = p at h
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
  try simp only [bind, Except.bind] at h
  cases htq : openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 with
  | none =>
    rw [htq] at h
    exact absurd h (by simp [unwrapOr, throw, throwThe, MonadExceptOf.throw])
  | some tq =>
  obtain ⟨tfvs, trest⟩ := tq
  rw [htq] at h
  simp only [unwrapOr, pure, Except.pure] at h
  cases hsorts : ConLeche.checkStructFieldSortsI (m := ConLeche.CheckM) (fueledOps μ F) env₁ true false
      p.resSort p.nP (tfvs.drop p.nP) [] p.nIdx with
  | error e => rw [hsorts] at h; exact nomatch h
  | ok isorts =>
  rw [hsorts] at h
  dsimp only at h
  cases hCtors : checkSumCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁
      p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors with
  | error e => rw [hCtors] at h; exact nomatch h
  | ok r₂ =>
  obtain ⟨ctorsA, sortss⟩ := r₂
  rw [hCtors] at h
  dsimp only at h
  by_cases hk : nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      p.kinds = true
  case neg =>
    rw [if_neg hk] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hk] at h
  try simp only [bind, Except.bind] at h
  by_cases hr : nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP
      p.ctors.length ctorsA p.kinds p.rhss = true
  case neg =>
    rw [if_neg hr] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hr] at h
  try simp only [bind, Except.bind] at h
  cases hRec : checkNativeRec (m := ConLeche.CheckM) (fueledOps μ F)
      (consSumCtors p.nP ctorsA env₁) p cvTa ctorsA with
  | error e => rw [hRec] at h; exact nomatch h
  | ok r₃ =>
  obtain ⟨cvRa, rhss⟩ := r₃
  rw [hRec] at h
  dsimp only at h
  exact ⟨hnd, envP, cvTaP, p₁P, ctorsP, sortssP, kinds, hIndP, hCtorsP, hK, cvTa, env₁, p₁, p,
    ctorsA, sortss, cvRa, rhss, tfvs, trest, isorts, hInd, hp.symm, helim, htq, hsorts, hCtors,
    hk, hr, hRec, h⟩

/-! ## The run-level dispatch

`checkDeclRun_ofEnvFactsE`'s `Ind` slot: the direct (fixpoint) arm and
the modeled arm — the kernel's own case split (`nativeParts?`; ONE
ROUTE, task #210 Part B). -/

/-- The `.indDecl` dispatch at the run level (the recogniser alone
since task #219). -/
def DeclIndRunDispatch (μ : CheckMode) (F : Nat) (env : Env)
    (block : List ConstantInfo) (nP : Nat) (env₂ : Env) : Prop :=
  match ConLeche.nativeParts? nP block with
  | some p => DeclNativeRun μ F env p env₂
  | none => DeclIndRun μ F env block env₂

end ConLeche.Semantics
