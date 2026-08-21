import Setlec.Verify.Bridge

/-!
# The cache-refinement bridge, part C: the declaration checker

The declaration checker is monad-polymorphic over a `CheckerOps`
record, so the same pair-monad game applies: `bridgeRel` relates
monotone fueled families to plain executable computations
("success on the executable side is reproduced at some fuel"), the
fueled/cached operation records are related by part B's entry-point
bridges, and the projection batteries push the pairing through every
declaration-checker function.  The punchline: a successful
`checkDecls cachedOps` run is reproduced by `checkDecls (fueledOps F)`
for some fuel `F`.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Setlec

/-- Success on the executable side is reproduced at some fuel. -/
def bridgeRel : MonadRel FueledM CheckM where
  R p c := ∀ v, c = .ok v → ∃ F, p.val F = .ok v
  pure_rel a := fun v h => ⟨0, by cases h; rfl⟩
  bind_rel {α β x₁ x₂ f₁ f₂} hx hf := by
    intro v h
    simp only [Bind.bind] at h
    cases hx2 : x₂ with
    | error e => rw [hx2] at h; exact nomatch h
    | ok a =>
      rw [hx2] at h
      dsimp only [Except.bind] at h
      obtain ⟨F₁, h1⟩ := hx a hx2
      obtain ⟨F₂, h2⟩ := hf a v h
      refine ⟨max F₁ F₂, ?_⟩
      rw [FueledM.atF_bind]
      simp only [Bind.bind]
      rw [x₁.property (Nat.le_max_left F₁ F₂) h1]
      dsimp only [Except.bind]
      exact (f₁ a).property (Nat.le_max_right F₁ F₂) h2
  throw_rel e := fun v h => nomatch h

/-- Componentwise relatedness of two operation records. -/
def OpsRel {M₁ M₂ : Type → Type} [Monad M₁] [Monad M₂]
    [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂]
    (rel : MonadRel M₁ M₂) (o₁ : CheckerOps M₁) (o₂ : CheckerOps M₂) :
    Prop :=
  (∀ env d e, rel.R (o₁.annotate env d e) (o₂.annotate env d e)) ∧
  (∀ env d e, rel.R (o₁.inferType env d e) (o₂.inferType env d e)) ∧
  (∀ env d a b, rel.R (o₁.isDefEq env d a b) (o₂.isDefEq env d a b)) ∧
  (∀ env d e, rel.R (o₁.ensureSort env d e) (o₂.ensureSort env d e)) ∧
  (∀ env d e, rel.R (o₁.whnf env d e) (o₂.whnf env d e))

/-- The paired operation record. -/
def pairOps {M₁ M₂ : Type → Type} [Monad M₁] [Monad M₂]
    [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂]
    {rel : MonadRel M₁ M₂} (o₁ : CheckerOps M₁) (o₂ : CheckerOps M₂)
    (h : OpsRel rel o₁ o₂) : CheckerOps (PairM rel) where
  annotate env d e := ⟨(o₁.annotate env d e, o₂.annotate env d e), h.1 env d e⟩
  inferType env d e :=
    ⟨(o₁.inferType env d e, o₂.inferType env d e), h.2.1 env d e⟩
  isDefEq env d a b :=
    ⟨(o₁.isDefEq env d a b, o₂.isDefEq env d a b), h.2.2.1 env d a b⟩
  ensureSort env d e :=
    ⟨(o₁.ensureSort env d e, o₂.ensureSort env d e), h.2.2.2.1 env d e⟩
  whnf env d e := ⟨(o₁.whnf env d e, o₂.whnf env d e), h.2.2.2.2 env d e⟩

/-- The fueled operations as monotone families. -/
def fueledOpsM : CheckerOps FueledM where
  annotate env d e :=
    ⟨fun F => annotateCore env F d e, fun hle h => annotateCore_mono hle h⟩
  inferType env d e :=
    ⟨fun F => inferTypeCore env F d e, fun hle h => inferTypeCore_mono hle h⟩
  isDefEq env d a b :=
    ⟨fun F => isDefEqCore env F d a b, fun hle h => isDefEqCore_mono hle h⟩
  ensureSort env d e :=
    ⟨fun F => ensureSortCore env F d e, fun hle h => ensureSortCore_mono hle h⟩
  whnf env d e :=
    ⟨fun F => whnf env F d e, fun hle h => whnf_mono hle h⟩

/-- Part B's entry-point bridges, packaged. -/
theorem fueledOpsM_cachedOps_rel : OpsRel bridgeRel fueledOpsM cachedOps :=
  ⟨fun _ _ _ _ h => cachedOps_annotate_bridge h,
   fun _ _ _ _ h => cachedOps_inferType_bridge h,
   fun _ _ _ _ _ h => cachedOps_isDefEq_bridge h,
   fun _ _ _ _ h => cachedOps_ensureSort_bridge h,
   fun _ _ _ _ h => cachedOps_whnf_bridge h⟩

section DeclBattery

variable {M₁ M₂ : Type → Type} [Monad M₁] [Monad M₂]
  [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂]
  {rel : MonadRel M₁ M₂} {o₁ : CheckerOps M₁} {o₂ : CheckerOps M₂}
  {h : OpsRel rel o₁ o₂}

theorem foldlM_fst {α β : Type} (g : β → α → PairM rel β) :
    ∀ (l : List α) (init : β),
      (l.foldlM g init).val.1 =
        l.foldlM (fun b a => (g b a).val.1) init
  | [], init => rfl
  | a :: l, init => by
    show ((g init a >>= fun b => l.foldlM g b : PairM rel β)).val.1 = _
    rw [PairM.fst_bind]
    show _ = (g init a).val.1 >>= fun b =>
      l.foldlM (fun b a => (g b a).val.1) b
    congr 1
    funext b
    exact foldlM_fst g l b

theorem foldlM_snd {α β : Type} (g : β → α → PairM rel β) :
    ∀ (l : List α) (init : β),
      (l.foldlM g init).val.2 =
        l.foldlM (fun b a => (g b a).val.2) init
  | [], init => rfl
  | a :: l, init => by
    show ((g init a >>= fun b => l.foldlM g b : PairM rel β)).val.2 = _
    rw [PairM.snd_bind]
    show _ = (g init a).val.2 >>= fun b =>
      l.foldlM (fun b a => (g b a).val.2) b
    congr 1
    funext b
    exact foldlM_snd g l b

macro "dfst_step" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "dfst_tac" : tactic =>
  `(tactic| dfst_step <;> dfst_step <;> dfst_step <;>
    dfst_step <;> dfst_step <;> dfst_step <;>
    dfst_step <;> dfst_step <;> dfst_step <;>
    dfst_step <;> dfst_step <;> dfst_step)

macro "dsnd_step" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_snd_proj])
    | (rw [foldlM_snd])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "dsnd_tac" : tactic =>
  `(tactic| dsnd_step <;> dsnd_step <;> dsnd_step <;>
    dsnd_step <;> dsnd_step <;> dsnd_step <;>
    dsnd_step <;> dsnd_step <;> dsnd_step <;>
    dsnd_step <;> dsnd_step <;> dsnd_step)

theorem checkConstantVal_fst_dproj (env : Env) (cv : ConstantVal) :
    (checkConstantVal (pairOps o₁ o₂ h) env cv).val.1 =
      checkConstantVal o₁ env cv := by
  unfold checkConstantVal
  dfst_tac

theorem checkConstantVal_snd_dproj (env : Env) (cv : ConstantVal) :
    (checkConstantVal (pairOps o₁ o₂ h) env cv).val.2 =
      checkConstantVal o₂ env cv := by
  unfold checkConstantVal
  dsnd_tac

theorem checkProjLookups_fst_dproj (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) :
    (checkProjLookups env' T ctorName lps nP nF i : PairM rel _).val.1 =
      (checkProjLookups env' T ctorName lps nP nF i : M₁ _) := by
  unfold checkProjLookups
  dfst_tac

theorem checkProjLookups_snd_dproj (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) :
    (checkProjLookups env' T ctorName lps nP nF i : PairM rel _).val.2 =
      (checkProjLookups env' T ctorName lps nP nF i : M₂ _) := by
  unfold checkProjLookups
  dsnd_tac

theorem checkProjTy_fst_dproj (env' : Env) (T ctorName : Name) (lps : List Name) (mty : Expr) (nP nF : Nat) :
    (checkProjTy env' T ctorName lps mty nP nF : PairM rel _).val.1 =
      (checkProjTy env' T ctorName lps mty nP nF : M₁ _) := by
  unfold checkProjTy
  dfst_tac

theorem checkProjTy_snd_dproj (env' : Env) (T ctorName : Name) (lps : List Name) (mty : Expr) (nP nF : Nat) :
    (checkProjTy env' T ctorName lps mty nP nF : PairM rel _).val.2 =
      (checkProjTy env' T ctorName lps mty nP nF : M₂ _) := by
  unfold checkProjTy
  dsnd_tac

theorem checkProjIota_fst_dproj (env' : Env) (T ctorName : Name) (lps : List Name) (cvj : ConstantVal) (nP nF i : Nat) :
    (checkProjIota env' T ctorName lps cvj nP nF i : PairM rel _).val.1 =
      (checkProjIota env' T ctorName lps cvj nP nF i : M₁ _) := by
  unfold checkProjIota
  dfst_tac

theorem checkProjIota_snd_dproj (env' : Env) (T ctorName : Name) (lps : List Name) (cvj : ConstantVal) (nP nF i : Nat) :
    (checkProjIota env' T ctorName lps cvj nP nF i : PairM rel _).val.2 =
      (checkProjIota env' T ctorName lps cvj nP nF i : M₂ _) := by
  unfold checkProjIota
  dsnd_tac

set_option maxHeartbeats 12800000 in
theorem checkIotaRule_fst_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm ni j : Nat) (r : RecRule) :
    (checkIotaRule (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
      nP nM nm ni j r).val.1 =
    checkIotaRule o₁ env' envSelf f cvName lps tyA nP nM nm ni j r := by
  unfold checkIotaRule
  dfst_tac

theorem checkIotaRules_fst_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm ni : Nat) :
    ∀ (j : Nat) (rules : List RecRule),
      (checkIotaRules (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
        nP nM nm ni j rules).val.1 =
      checkIotaRules o₁ env' envSelf f cvName lps tyA nP nM nm ni j rules
  | _, [] => rfl
  | j, r :: rest => by
    show ((do
        let r' ← checkIotaRule (pairOps o₁ o₂ h) env' envSelf f cvName
          lps tyA nP nM nm ni j r
        let rest' ← checkIotaRules (pairOps o₁ o₂ h) env' envSelf f
          cvName lps tyA nP nM nm ni (j + 1) rest
        pure (r' :: rest') : PairM rel _)).val.1 = (do
        let r' ← checkIotaRule o₁ env' envSelf f cvName lps tyA
          nP nM nm ni j r
        let rest' ← checkIotaRules o₁ env' envSelf f cvName lps tyA
          nP nM nm ni (j + 1) rest
        pure (r' :: rest'))
    rw [PairM.fst_bind, checkIotaRule_fst_dproj]
    congr 1
    funext r'
    rw [PairM.fst_bind, checkIotaRules_fst_dproj env' envSelf f cvName lps tyA
      nP nM nm ni (j + 1) rest]
    rfl

set_option maxHeartbeats 12800000 in
theorem checkIotaRule_snd_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm ni j : Nat) (r : RecRule) :
    (checkIotaRule (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
      nP nM nm ni j r).val.2 =
    checkIotaRule o₂ env' envSelf f cvName lps tyA nP nM nm ni j r := by
  unfold checkIotaRule
  dsnd_tac

theorem checkIotaRules_snd_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm ni : Nat) :
    ∀ (j : Nat) (rules : List RecRule),
      (checkIotaRules (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
        nP nM nm ni j rules).val.2 =
      checkIotaRules o₂ env' envSelf f cvName lps tyA nP nM nm ni j rules
  | _, [] => rfl
  | j, r :: rest => by
    show ((do
        let r' ← checkIotaRule (pairOps o₁ o₂ h) env' envSelf f cvName
          lps tyA nP nM nm ni j r
        let rest' ← checkIotaRules (pairOps o₁ o₂ h) env' envSelf f
          cvName lps tyA nP nM nm ni (j + 1) rest
        pure (r' :: rest') : PairM rel _)).val.2 = (do
        let r' ← checkIotaRule o₂ env' envSelf f cvName lps tyA
          nP nM nm ni j r
        let rest' ← checkIotaRules o₂ env' envSelf f cvName lps tyA
          nP nM nm ni (j + 1) rest
        pure (r' :: rest'))
    rw [PairM.snd_bind, checkIotaRule_snd_dproj]
    congr 1
    funext r'
    rw [PairM.snd_bind, checkIotaRules_snd_dproj env' envSelf f cvName lps tyA
      nP nM nm ni (j + 1) rest]
    rfl

macro "dfst_step2" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | (rw [checkConstantVal_fst_dproj])
    | (rw [checkProjLookups_fst_dproj])
    | (rw [checkProjTy_fst_dproj])
    | (rw [checkProjIota_fst_dproj])
    | (rw [checkProjRule_fst_dproj])
    | (rw [checkIndMember_fst_dproj])
    | (rw [checkIotaRule_fst_dproj])
    | (rw [checkIotaRules_fst_dproj])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "dfst_tac2" : tactic =>
  `(tactic| dfst_step2 <;> dfst_step2 <;> dfst_step2 <;>
    dfst_step2 <;> dfst_step2 <;> dfst_step2 <;>
    dfst_step2 <;> dfst_step2 <;> dfst_step2 <;>
    dfst_step2 <;> dfst_step2 <;> dfst_step2)

macro "dsnd_step2" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_snd_proj])
    | (rw [foldlM_snd])
    | (rw [checkConstantVal_snd_dproj])
    | (rw [checkProjLookups_snd_dproj])
    | (rw [checkProjTy_snd_dproj])
    | (rw [checkProjIota_snd_dproj])
    | (rw [checkProjRule_snd_dproj])
    | (rw [checkIndMember_snd_dproj])
    | (rw [checkIotaRule_snd_dproj])
    | (rw [checkIotaRules_snd_dproj])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "dsnd_tac2" : tactic =>
  `(tactic| dsnd_step2 <;> dsnd_step2 <;> dsnd_step2 <;>
    dsnd_step2 <;> dsnd_step2 <;> dsnd_step2 <;>
    dsnd_step2 <;> dsnd_step2 <;> dsnd_step2 <;>
    dsnd_step2 <;> dsnd_step2 <;> dsnd_step2)

theorem checkProjRule_fst_dproj (env' : Env) (cvj : ConstantVal) (lps : List Name) (nP nF i : Nat) :
    (checkProjRule (pairOps o₁ o₂ h) env' cvj lps nP nF i).val.1 =
      checkProjRule o₁ env' cvj lps nP nF i := by
  unfold checkProjRule
  dfst_tac2

theorem checkProjRule_snd_dproj (env' : Env) (cvj : ConstantVal) (lps : List Name) (nP nF i : Nat) :
    (checkProjRule (pairOps o₁ o₂ h) env' cvj lps nP nF i).val.2 =
      checkProjRule o₂ env' cvj lps nP nF i := by
  unfold checkProjRule
  dsnd_tac2

theorem checkIndMember_fst_dproj (blockNames : List Name) (caps : IndCaps) (env' : Env) (ci : ConstantInfo) :
    (checkIndMember (pairOps o₁ o₂ h) blockNames caps env' ci).val.1 =
      checkIndMember o₁ blockNames caps env' ci := by
  unfold checkIndMember
  dfst_tac2

theorem checkIndMember_snd_dproj (blockNames : List Name) (caps : IndCaps) (env' : Env) (ci : ConstantInfo) :
    (checkIndMember (pairOps o₁ o₂ h) blockNames caps env' ci).val.2 =
      checkIndMember o₂ blockNames caps env' ci := by
  unfold checkIndMember
  dsnd_tac2

macro "dfst_step3" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | (rw [checkConstantVal_fst_dproj])
    | (rw [checkProjLookups_fst_dproj])
    | (rw [checkProjTy_fst_dproj])
    | (rw [checkProjIota_fst_dproj])
    | (rw [checkProjRule_fst_dproj])
    | (rw [checkIndMember_fst_dproj])
    | (rw [checkIotaRule_fst_dproj])
    | (rw [checkIotaRules_fst_dproj])
    | (rw [checkProjFn_fst_dproj])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "dfst_tac3" : tactic =>
  `(tactic| dfst_step3 <;> dfst_step3 <;> dfst_step3 <;>
    dfst_step3 <;> dfst_step3 <;> dfst_step3 <;>
    dfst_step3 <;> dfst_step3 <;> dfst_step3 <;>
    dfst_step3 <;> dfst_step3 <;> dfst_step3)

macro "dsnd_step3" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_snd_proj])
    | (rw [foldlM_snd])
    | (rw [checkConstantVal_snd_dproj])
    | (rw [checkProjLookups_snd_dproj])
    | (rw [checkProjTy_snd_dproj])
    | (rw [checkProjIota_snd_dproj])
    | (rw [checkProjRule_snd_dproj])
    | (rw [checkIndMember_snd_dproj])
    | (rw [checkIotaRule_snd_dproj])
    | (rw [checkIotaRules_snd_dproj])
    | (rw [checkProjFn_snd_dproj])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "dsnd_tac3" : tactic =>
  `(tactic| dsnd_step3 <;> dsnd_step3 <;> dsnd_step3 <;>
    dsnd_step3 <;> dsnd_step3 <;> dsnd_step3 <;>
    dsnd_step3 <;> dsnd_step3 <;> dsnd_step3 <;>
    dsnd_step3 <;> dsnd_step3 <;> dsnd_step3)

theorem checkProjFn_fst_dproj (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) :
    (checkProjFn (pairOps o₁ o₂ h) env' T ctorName lps nP nF i).val.1 =
      checkProjFn o₁ env' T ctorName lps nP nF i := by
  unfold checkProjFn
  dfst_tac3

theorem checkProjFn_snd_dproj (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) :
    (checkProjFn (pairOps o₁ o₂ h) env' T ctorName lps nP nF i).val.2 =
      checkProjFn o₂ env' T ctorName lps nP nF i := by
  unfold checkProjFn
  dsnd_tac3

theorem installProjFnStep_fst_dproj (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) (e : Env) (i : Nat) :
    (installProjFnStep (pairOps o₁ o₂ h) T ctorName lps nP nF e i).val.1
      = installProjFnStep o₁ T ctorName lps nP nF e i := by
  unfold installProjFnStep
  split
  · exact checkProjFn_fst_dproj e T ctorName lps nP nF i
  · rfl

theorem installBasisDecl_fst_dproj (env : Env) (ci : ConstantInfo) :
    (installBasisDecl env ci : PairM rel _).val.1 =
      (installBasisDecl env ci : M₁ _) := by
  unfold installBasisDecl
  dfst_tac

theorem installProjFnStep_snd_dproj (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) (e : Env) (i : Nat) :
    (installProjFnStep (pairOps o₁ o₂ h) T ctorName lps nP nF e i).val.2
      = installProjFnStep o₂ T ctorName lps nP nF e i := by
  unfold installProjFnStep
  split
  · exact checkProjFn_snd_dproj e T ctorName lps nP nF i
  · rfl

theorem installBasisDecl_snd_dproj (env : Env) (ci : ConstantInfo) :
    (installBasisDecl env ci : PairM rel _).val.2 =
      (installBasisDecl env ci : M₂ _) := by
  unfold installBasisDecl
  dsnd_tac

macro "dfst_step4" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | (simp only [checkIndMember_fst_dproj, checkProjFn_fst_dproj,
        installProjFnStep_fst_dproj, installBasisDecl_fst_dproj])
    | (rw [checkConstantVal_fst_dproj])
    | (rw [checkProjLookups_fst_dproj])
    | (rw [checkProjTy_fst_dproj])
    | (rw [checkProjIota_fst_dproj])
    | (rw [checkProjRule_fst_dproj])
    | (rw [checkIndMember_fst_dproj])
    | (rw [checkIotaRule_fst_dproj])
    | (rw [checkIotaRules_fst_dproj])
    | (rw [checkProjFn_fst_dproj])
    | (rw [checkIndDecl_fst_dproj])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "dfst_tac4" : tactic =>
  `(tactic| dfst_step4 <;> dfst_step4 <;> dfst_step4 <;>
    dfst_step4 <;> dfst_step4 <;> dfst_step4 <;>
    dfst_step4 <;> dfst_step4 <;> dfst_step4 <;>
    dfst_step4 <;> dfst_step4 <;> dfst_step4)

macro "dsnd_step4" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_snd_proj])
    | (rw [foldlM_snd])
    | (simp only [checkIndMember_snd_dproj, checkProjFn_snd_dproj,
        installProjFnStep_snd_dproj, installBasisDecl_snd_dproj])
    | (rw [checkConstantVal_snd_dproj])
    | (rw [checkProjLookups_snd_dproj])
    | (rw [checkProjTy_snd_dproj])
    | (rw [checkProjIota_snd_dproj])
    | (rw [checkProjRule_snd_dproj])
    | (rw [checkIndMember_snd_dproj])
    | (rw [checkIotaRule_snd_dproj])
    | (rw [checkIotaRules_snd_dproj])
    | (rw [checkProjFn_snd_dproj])
    | (rw [checkIndDecl_snd_dproj])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "dsnd_tac4" : tactic =>
  `(tactic| dsnd_step4 <;> dsnd_step4 <;> dsnd_step4 <;>
    dsnd_step4 <;> dsnd_step4 <;> dsnd_step4 <;>
    dsnd_step4 <;> dsnd_step4 <;> dsnd_step4 <;>
    dsnd_step4 <;> dsnd_step4 <;> dsnd_step4)

theorem checkIndDecl_fst_dproj (env : Env) (block : List ConstantInfo) :
    (checkIndDecl (pairOps o₁ o₂ h) env block).val.1 =
      checkIndDecl o₁ env block := by
  unfold checkIndDecl
  dfst_tac4

theorem checkIndDecl_snd_dproj (env : Env) (block : List ConstantInfo) :
    (checkIndDecl (pairOps o₁ o₂ h) env block).val.2 =
      checkIndDecl o₂ env block := by
  unfold checkIndDecl
  dsnd_tac4

macro "dfst_step5" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | (simp only [checkIndMember_fst_dproj, checkProjFn_fst_dproj,
        installProjFnStep_fst_dproj, installBasisDecl_fst_dproj,
        checkIndDecl_fst_dproj])
    | (rw [checkConstantVal_fst_dproj])
    | (rw [checkProjLookups_fst_dproj])
    | (rw [checkProjTy_fst_dproj])
    | (rw [checkProjIota_fst_dproj])
    | (rw [checkProjRule_fst_dproj])
    | (rw [checkIndMember_fst_dproj])
    | (rw [checkIotaRule_fst_dproj])
    | (rw [checkIotaRules_fst_dproj])
    | (rw [checkProjFn_fst_dproj])
    | (rw [checkIndDecl_fst_dproj])
    | (rw [checkDecl_fst_dproj])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "dfst_tac5" : tactic =>
  `(tactic| dfst_step5 <;> dfst_step5 <;> dfst_step5 <;>
    dfst_step5 <;> dfst_step5 <;> dfst_step5 <;>
    dfst_step5 <;> dfst_step5 <;> dfst_step5 <;>
    dfst_step5 <;> dfst_step5 <;> dfst_step5)

macro "dsnd_step5" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_snd_proj])
    | (rw [foldlM_snd])
    | (simp only [checkIndMember_snd_dproj, checkProjFn_snd_dproj,
        installProjFnStep_snd_dproj, installBasisDecl_snd_dproj,
        checkIndDecl_snd_dproj])
    | (rw [checkConstantVal_snd_dproj])
    | (rw [checkProjLookups_snd_dproj])
    | (rw [checkProjTy_snd_dproj])
    | (rw [checkProjIota_snd_dproj])
    | (rw [checkProjRule_snd_dproj])
    | (rw [checkIndMember_snd_dproj])
    | (rw [checkIotaRule_snd_dproj])
    | (rw [checkIotaRules_snd_dproj])
    | (rw [checkProjFn_snd_dproj])
    | (rw [checkIndDecl_snd_dproj])
    | (rw [checkDecl_snd_dproj])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "dsnd_tac5" : tactic =>
  `(tactic| dsnd_step5 <;> dsnd_step5 <;> dsnd_step5 <;>
    dsnd_step5 <;> dsnd_step5 <;> dsnd_step5 <;>
    dsnd_step5 <;> dsnd_step5 <;> dsnd_step5 <;>
    dsnd_step5 <;> dsnd_step5 <;> dsnd_step5)

theorem checkDefnVal_fst_dproj (env : Env) (cv : ConstantVal)
    (value : Expr) :
    (checkDefnVal (pairOps o₁ o₂ h) env cv value).val.1 =
      checkDefnVal o₁ env cv value := by
  unfold checkDefnVal
  dfst_tac

theorem checkThmVal_fst_dproj (env : Env) (cv : ConstantVal)
    (value : Expr) :
    (checkThmVal (pairOps o₁ o₂ h) env cv value).val.1 =
      checkThmVal o₁ env cv value := by
  unfold checkThmVal
  dfst_tac

theorem checkDefnVal_snd_dproj (env : Env) (cv : ConstantVal)
    (value : Expr) :
    (checkDefnVal (pairOps o₁ o₂ h) env cv value).val.2 =
      checkDefnVal o₂ env cv value := by
  unfold checkDefnVal
  dsnd_tac

theorem checkThmVal_snd_dproj (env : Env) (cv : ConstantVal)
    (value : Expr) :
    (checkThmVal (pairOps o₁ o₂ h) env cv value).val.2 =
      checkThmVal o₂ env cv value := by
  unfold checkThmVal
  dsnd_tac

theorem checkOpaqueVal_fst_dproj (env : Env) (cv : ConstantVal)
    (value : Expr) :
    (checkOpaqueVal (pairOps o₁ o₂ h) env cv value).val.1 =
      checkOpaqueVal o₁ env cv value := by
  unfold checkOpaqueVal
  dfst_tac

theorem checkOpaqueVal_snd_dproj (env : Env) (cv : ConstantVal)
    (value : Expr) :
    (checkOpaqueVal (pairOps o₁ o₂ h) env cv value).val.2 =
      checkOpaqueVal o₂ env cv value := by
  unfold checkOpaqueVal
  dsnd_tac

theorem certifyNatEqs_fst_dproj (env : Env) :
    ∀ eqs : List (Expr × Expr),
      (certifyNatEqs (pairOps o₁ o₂ h) env eqs).val.1 =
        certifyNatEqs o₁ env eqs
  | [] => rfl
  | eq :: rest => by
    show ((do
        if ← CheckerOps.isDefEq (pairOps o₁ o₂ h) env 2 eq.1 eq.2 then
          certifyNatEqs (pairOps o₁ o₂ h) env rest
        else pure false : PairM rel _)).val.1 = _
    rw [PairM.fst_bind]
    show _ = (do
        if ← CheckerOps.isDefEq o₁ env 2 eq.1 eq.2 then
          certifyNatEqs o₁ env rest
        else pure false : M₁ _)
    congr 1
    funext b
    cases b with
    | true => exact certifyNatEqs_fst_dproj env rest
    | false => rfl

theorem certifyNatEqs_snd_dproj (env : Env) :
    ∀ eqs : List (Expr × Expr),
      (certifyNatEqs (pairOps o₁ o₂ h) env eqs).val.2 =
        certifyNatEqs o₂ env eqs
  | [] => rfl
  | eq :: rest => by
    show ((do
        if ← CheckerOps.isDefEq (pairOps o₁ o₂ h) env 2 eq.1 eq.2 then
          certifyNatEqs (pairOps o₁ o₂ h) env rest
        else pure false : PairM rel _)).val.2 = _
    rw [PairM.snd_bind]
    show _ = (do
        if ← CheckerOps.isDefEq o₂ env 2 eq.1 eq.2 then
          certifyNatEqs o₂ env rest
        else pure false : M₂ _)
    congr 1
    funext b
    cases b with
    | true => exact certifyNatEqs_snd_dproj env rest
    | false => rfl

theorem checkDecl_fst_dproj (env : Env) (d : Declaration) :
    (checkDecl (pairOps o₁ o₂ h) env d).val.1 =
      checkDecl o₁ env d := by
  unfold checkDecl
  cases d with
  | defnDecl cv value =>
    dsimp only
    rw [PairM.fst_bind, checkConstantVal_fst_dproj]
    congr 1
    funext cv'
    rw [PairM.fst_bind, checkDefnVal_fst_dproj]
    congr 1
    funext env2
    repeat (first
      | (rw [certifyNatEqs_fst_dproj])
      | split
      | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [PairM.fst_pure, PairM.fst_throw]))
  | thmDecl cv value =>
    show ((checkConstantVal (pairOps o₁ o₂ h) env cv >>= fun cv =>
      checkThmVal (pairOps o₁ o₂ h) env cv value : PairM rel _)).val.1
      = _
    rw [PairM.fst_bind, checkConstantVal_fst_dproj]
    congr 1
    funext cv'
    rw [checkThmVal_fst_dproj]
  | opaqueDecl cv value =>
    show ((checkConstantVal (pairOps o₁ o₂ h) env cv >>= fun cv =>
      checkOpaqueVal (pairOps o₁ o₂ h) env cv value : PairM rel _)).val.1
      = _
    rw [PairM.fst_bind, checkConstantVal_fst_dproj]
    congr 1
    funext cv'
    rw [checkOpaqueVal_fst_dproj]
  | axiomDecl cv =>
    show ((checkConstantVal (pairOps o₁ o₂ h) env cv >>= fun cvA =>
      if stdAxiomOk env cvA then
        pure (⟨.axiomInfo cvA :: env.consts⟩ : Env)
      else throw (.notImplemented s!"axiom declaration ({cv.name})")
      : PairM rel _)).val.1 = _
    rw [PairM.fst_bind, checkConstantVal_fst_dproj]
    congr 1
    funext cvA
    simp only [PairM.fst_ite, PairM.fst_pure, PairM.fst_throw]
  | basisDecl kind =>
    dsimp only
    by_cases hq : kind = .quotK
    · rw [if_pos hq, if_pos hq]
      by_cases he : env.find? eqName = some eqA
      · rw [if_pos he, if_pos he, foldlM_fst]
        simp only [installBasisDecl_fst_dproj]
      · rw [if_neg he, if_neg he, PairM.fst_bind]
        simp only [PairM.fst_throw]
        congr 1
        funext x
        rw [foldlM_fst]
        simp only [installBasisDecl_fst_dproj]
    · rw [if_neg hq, if_neg hq, foldlM_fst]
      simp only [installBasisDecl_fst_dproj]
  | indDecl block =>
    exact checkIndDecl_fst_dproj env block

theorem checkDecl_snd_dproj (env : Env) (d : Declaration) :
    (checkDecl (pairOps o₁ o₂ h) env d).val.2 =
      checkDecl o₂ env d := by
  unfold checkDecl
  cases d with
  | defnDecl cv value =>
    dsimp only
    rw [PairM.snd_bind, checkConstantVal_snd_dproj]
    congr 1
    funext cv'
    rw [PairM.snd_bind, checkDefnVal_snd_dproj]
    congr 1
    funext env2
    repeat (first
      | (rw [certifyNatEqs_snd_dproj])
      | split
      | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [PairM.snd_pure, PairM.snd_throw]))
  | thmDecl cv value =>
    show ((checkConstantVal (pairOps o₁ o₂ h) env cv >>= fun cv =>
      checkThmVal (pairOps o₁ o₂ h) env cv value : PairM rel _)).val.2
      = _
    rw [PairM.snd_bind, checkConstantVal_snd_dproj]
    congr 1
    funext cv'
    rw [checkThmVal_snd_dproj]
  | opaqueDecl cv value =>
    show ((checkConstantVal (pairOps o₁ o₂ h) env cv >>= fun cv =>
      checkOpaqueVal (pairOps o₁ o₂ h) env cv value : PairM rel _)).val.2
      = _
    rw [PairM.snd_bind, checkConstantVal_snd_dproj]
    congr 1
    funext cv'
    rw [checkOpaqueVal_snd_dproj]
  | axiomDecl cv =>
    show ((checkConstantVal (pairOps o₁ o₂ h) env cv >>= fun cvA =>
      if stdAxiomOk env cvA then
        pure (⟨.axiomInfo cvA :: env.consts⟩ : Env)
      else throw (.notImplemented s!"axiom declaration ({cv.name})")
      : PairM rel _)).val.2 = _
    rw [PairM.snd_bind, checkConstantVal_snd_dproj]
    congr 1
    funext cvA
    simp only [PairM.snd_ite, PairM.snd_pure, PairM.snd_throw]
  | basisDecl kind =>
    dsimp only
    by_cases hq : kind = .quotK
    · rw [if_pos hq, if_pos hq]
      by_cases he : env.find? eqName = some eqA
      · rw [if_pos he, if_pos he, foldlM_snd]
        simp only [installBasisDecl_snd_dproj]
      · rw [if_neg he, if_neg he, PairM.snd_bind]
        simp only [PairM.snd_throw]
        congr 1
        funext x
        rw [foldlM_snd]
        simp only [installBasisDecl_snd_dproj]
    · rw [if_neg hq, if_neg hq, foldlM_snd]
      simp only [installBasisDecl_snd_dproj]
  | indDecl block =>
    exact checkIndDecl_snd_dproj env block

theorem checkDecls_fst_dproj (ds : List Declaration) :
    (checkDecls (pairOps o₁ o₂ h) ds).val.1 =
      checkDecls o₁ ds := by
  unfold checkDecls
  rw [foldlM_fst]
  simp only [checkDecl_fst_dproj]

theorem checkDecls_snd_dproj (ds : List Declaration) :
    (checkDecls (pairOps o₁ o₂ h) ds).val.2 =
      checkDecls o₂ ds := by
  unfold checkDecls
  rw [foldlM_snd]
  simp only [checkDecl_snd_dproj]

/-! ## The `atF` battery: fueled-family runs are fueled-ops runs -/

theorem foldlM_atF {α β : Type} (g : β → α → FueledM β) (F : Nat) :
    ∀ (l : List α) (init : β),
      (l.foldlM g init).val F =
        l.foldlM (fun b a => (g b a).val F) init
  | [], init => rfl
  | a :: l, init => by
    show ((g init a >>= fun b => l.foldlM g b : FueledM β)).val F = _
    rw [FueledM.atF_bind]
    show _ = (g init a).val F >>= fun b =>
      l.foldlM (fun b a => (g b a).val F) b
    congr 1
    funext b
    exact foldlM_atF g F l b

macro "datF_step" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "datF_tac" : tactic =>
  `(tactic| datF_step <;> datF_step <;> datF_step <;>
    datF_step <;> datF_step <;> datF_step <;>
    datF_step <;> datF_step <;> datF_step <;>
    datF_step <;> datF_step <;> datF_step)

theorem checkConstantVal_datF (env : Env) (cv : ConstantVal) (F : Nat) :
    (checkConstantVal fueledOpsM env cv).val F =
      checkConstantVal (fueledOps F) env cv := by
  unfold checkConstantVal
  datF_tac

theorem checkProjLookups_datF (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) (F : Nat) :
    (checkProjLookups env' T ctorName lps nP nF i : FueledM _).val F =
      (checkProjLookups env' T ctorName lps nP nF i : CheckM _) := by
  unfold checkProjLookups
  datF_tac

theorem checkProjTy_datF (env' : Env) (T ctorName : Name) (lps : List Name) (mty : Expr) (nP nF : Nat) (F : Nat) :
    (checkProjTy env' T ctorName lps mty nP nF : FueledM _).val F =
      (checkProjTy env' T ctorName lps mty nP nF : CheckM _) := by
  unfold checkProjTy
  datF_tac

theorem checkProjIota_datF (env' : Env) (T ctorName : Name) (lps : List Name) (cvj : ConstantVal) (nP nF i : Nat) (F : Nat) :
    (checkProjIota env' T ctorName lps cvj nP nF i : FueledM _).val F =
      (checkProjIota env' T ctorName lps cvj nP nF i : CheckM _) := by
  unfold checkProjIota
  datF_tac

set_option maxHeartbeats 12800000 in
theorem checkIotaRule_datF (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm ni j : Nat) (r : RecRule) (F : Nat) :
    (checkIotaRule fueledOpsM env' envSelf f cvName lps tyA
      nP nM nm ni j r).val F =
    checkIotaRule (fueledOps F) env' envSelf f cvName lps tyA
      nP nM nm ni j r := by
  unfold checkIotaRule
  datF_tac

theorem checkIotaRules_datF (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm ni : Nat) (F : Nat) :
    ∀ (j : Nat) (rules : List RecRule),
      (checkIotaRules fueledOpsM env' envSelf f cvName lps tyA
        nP nM nm ni j rules).val F =
      checkIotaRules (fueledOps F) env' envSelf f cvName lps tyA
        nP nM nm ni j rules
  | _, [] => rfl
  | j, r :: rest => by
    show ((do
        let r' ← checkIotaRule fueledOpsM env' envSelf f cvName lps tyA
          nP nM nm ni j r
        let rest' ← checkIotaRules fueledOpsM env' envSelf f cvName lps
          tyA nP nM nm ni (j + 1) rest
        pure (r' :: rest') : FueledM _)).val F = (do
        let r' ← checkIotaRule (fueledOps F) env' envSelf f cvName lps
          tyA nP nM nm ni j r
        let rest' ← checkIotaRules (fueledOps F) env' envSelf f cvName
          lps tyA nP nM nm ni (j + 1) rest
        pure (r' :: rest'))
    rw [FueledM.atF_bind, checkIotaRule_datF]
    congr 1
    funext r'
    rw [FueledM.atF_bind, checkIotaRules_datF env' envSelf f cvName lps
      tyA nP nM nm ni F (j + 1) rest]
    rfl

macro "datF_step2" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | (rw [checkConstantVal_datF])
    | (rw [checkProjLookups_datF])
    | (rw [checkProjTy_datF])
    | (rw [checkProjIota_datF])
    | (rw [checkProjRule_datF])
    | (rw [checkIndMember_datF])
    | (rw [checkIotaRule_datF])
    | (rw [checkIotaRules_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "datF_tac2" : tactic =>
  `(tactic| datF_step2 <;> datF_step2 <;> datF_step2 <;>
    datF_step2 <;> datF_step2 <;> datF_step2 <;>
    datF_step2 <;> datF_step2 <;> datF_step2 <;>
    datF_step2 <;> datF_step2 <;> datF_step2)

theorem checkProjRule_datF (env' : Env) (cvj : ConstantVal) (lps : List Name) (nP nF i : Nat) (F : Nat) :
    (checkProjRule fueledOpsM env' cvj lps nP nF i).val F =
      checkProjRule (fueledOps F) env' cvj lps nP nF i := by
  unfold checkProjRule
  datF_tac2

theorem checkIndMember_datF (blockNames : List Name) (caps : IndCaps) (env' : Env) (ci : ConstantInfo) (F : Nat) :
    (checkIndMember fueledOpsM blockNames caps env' ci).val F =
      checkIndMember (fueledOps F) blockNames caps env' ci := by
  unfold checkIndMember
  datF_tac2

macro "datF_step3" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | (rw [checkConstantVal_datF])
    | (rw [checkProjLookups_datF])
    | (rw [checkProjTy_datF])
    | (rw [checkProjIota_datF])
    | (rw [checkProjRule_datF])
    | (rw [checkIndMember_datF])
    | (rw [checkIotaRule_datF])
    | (rw [checkIotaRules_datF])
    | (rw [checkProjFn_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "datF_tac3" : tactic =>
  `(tactic| datF_step3 <;> datF_step3 <;> datF_step3 <;>
    datF_step3 <;> datF_step3 <;> datF_step3 <;>
    datF_step3 <;> datF_step3 <;> datF_step3 <;>
    datF_step3 <;> datF_step3 <;> datF_step3)

theorem checkProjFn_datF (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) (F : Nat) :
    (checkProjFn fueledOpsM env' T ctorName lps nP nF i).val F =
      checkProjFn (fueledOps F) env' T ctorName lps nP nF i := by
  unfold checkProjFn
  datF_tac3

theorem installProjFnStep_datF (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) (e : Env) (i : Nat) (F : Nat) :
    (installProjFnStep fueledOpsM T ctorName lps nP nF e i).val F
      = installProjFnStep (fueledOps F) T ctorName lps nP nF e i := by
  unfold installProjFnStep
  split
  · exact checkProjFn_datF e T ctorName lps nP nF i F
  · rfl

theorem installBasisDecl_datF (env : Env) (ci : ConstantInfo) (F : Nat) :
    (installBasisDecl env ci : FueledM _).val F =
      (installBasisDecl env ci : CheckM _) := by
  unfold installBasisDecl
  datF_tac

macro "datF_step4" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | (simp only [checkIndMember_datF, checkProjFn_datF,
        installProjFnStep_datF, installBasisDecl_datF])
    | (rw [checkConstantVal_datF])
    | (rw [checkProjLookups_datF])
    | (rw [checkProjTy_datF])
    | (rw [checkProjIota_datF])
    | (rw [checkProjRule_datF])
    | (rw [checkIndMember_datF])
    | (rw [checkIotaRule_datF])
    | (rw [checkIotaRules_datF])
    | (rw [checkProjFn_datF])
    | (rw [checkIndDecl_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "datF_tac4" : tactic =>
  `(tactic| datF_step4 <;> datF_step4 <;> datF_step4 <;>
    datF_step4 <;> datF_step4 <;> datF_step4 <;>
    datF_step4 <;> datF_step4 <;> datF_step4 <;>
    datF_step4 <;> datF_step4 <;> datF_step4)

theorem checkIndDecl_datF (env : Env) (block : List ConstantInfo) (F : Nat) :
    (checkIndDecl fueledOpsM env block).val F =
      checkIndDecl (fueledOps F) env block := by
  unfold checkIndDecl
  datF_tac4

macro "datF_step5" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | (simp only [checkIndMember_datF, checkProjFn_datF,
        installProjFnStep_datF, installBasisDecl_datF,
        checkIndDecl_datF])
    | (rw [checkConstantVal_datF])
    | (rw [checkProjLookups_datF])
    | (rw [checkProjTy_datF])
    | (rw [checkProjIota_datF])
    | (rw [checkProjRule_datF])
    | (rw [checkIndMember_datF])
    | (rw [checkIotaRule_datF])
    | (rw [checkIotaRules_datF])
    | (rw [checkProjFn_datF])
    | (rw [checkIndDecl_datF])
    | (rw [checkDecl_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [])))

macro "datF_tac5" : tactic =>
  `(tactic| datF_step5 <;> datF_step5 <;> datF_step5 <;>
    datF_step5 <;> datF_step5 <;> datF_step5 <;>
    datF_step5 <;> datF_step5 <;> datF_step5 <;>
    datF_step5 <;> datF_step5 <;> datF_step5)

theorem checkDefnVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (F : Nat) :
    (checkDefnVal fueledOpsM env cv value).val F =
      checkDefnVal (fueledOps F) env cv value := by
  unfold checkDefnVal
  datF_tac

theorem checkThmVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (F : Nat) :
    (checkThmVal fueledOpsM env cv value).val F =
      checkThmVal (fueledOps F) env cv value := by
  unfold checkThmVal
  datF_tac

theorem checkOpaqueVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (F : Nat) :
    (checkOpaqueVal fueledOpsM env cv value).val F =
      checkOpaqueVal (fueledOps F) env cv value := by
  unfold checkOpaqueVal
  datF_tac

theorem certifyNatEqs_datF (env : Env) (F : Nat) :
    ∀ eqs : List (Expr × Expr),
      (certifyNatEqs fueledOpsM env eqs).val F =
        certifyNatEqs (fueledOps F) env eqs
  | [] => rfl
  | eq :: rest => by
    show ((do
        if ← CheckerOps.isDefEq fueledOpsM env 2 eq.1 eq.2 then
          certifyNatEqs fueledOpsM env rest
        else pure false : FueledM _)).val F = _
    rw [FueledM.atF_bind]
    show _ = (do
        if ← CheckerOps.isDefEq (fueledOps F) env 2 eq.1 eq.2 then
          certifyNatEqs (fueledOps F) env rest
        else pure false : CheckM _)
    congr 1
    funext b
    cases b with
    | true => exact certifyNatEqs_datF env F rest
    | false => rfl

theorem checkDecl_datF (env : Env) (d : Declaration) (F : Nat) :
    (checkDecl fueledOpsM env d).val F =
      checkDecl (fueledOps F) env d := by
  unfold checkDecl
  cases d with
  | defnDecl cv value =>
    dsimp only
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [FueledM.atF_bind, checkDefnVal_datF]
    congr 1
    funext env2
    repeat (first
      | (rw [certifyNatEqs_datF])
      | split
      | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [FueledM.atF_pure, FueledM.atF_throw]))
  | thmDecl cv value =>
    show ((checkConstantVal fueledOpsM env cv >>= fun cv =>
      checkThmVal fueledOpsM env cv value : FueledM _)).val F = _
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [checkThmVal_datF]
  | opaqueDecl cv value =>
    show ((checkConstantVal fueledOpsM env cv >>= fun cv =>
      checkOpaqueVal fueledOpsM env cv value : FueledM _)).val F = _
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [checkOpaqueVal_datF]
  | axiomDecl cv =>
    show ((checkConstantVal fueledOpsM env cv >>= fun cvA =>
      if stdAxiomOk env cvA then
        pure (⟨.axiomInfo cvA :: env.consts⟩ : Env)
      else throw (.notImplemented s!"axiom declaration ({cv.name})")
      : FueledM _)).val F = _
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cvA
    simp only [FueledM.atF_ite, FueledM.atF_pure, FueledM.atF_throw]
  | basisDecl kind =>
    dsimp only
    by_cases hq : kind = .quotK
    · rw [if_pos hq, if_pos hq]
      by_cases he : env.find? eqName = some eqA
      · rw [if_pos he, if_pos he, foldlM_atF]
        simp only [installBasisDecl_datF]
      · rw [if_neg he, if_neg he, FueledM.atF_bind]
        simp only [FueledM.atF_throw]
        congr 1
        funext x
        rw [foldlM_atF]
        simp only [installBasisDecl_datF]
    · rw [if_neg hq, if_neg hq, foldlM_atF]
      simp only [installBasisDecl_datF]
  | indDecl block =>
    exact checkIndDecl_datF env block F

theorem checkDecls_datF (ds : List Declaration) (F : Nat) :
    (checkDecls fueledOpsM ds).val F =
      checkDecls (fueledOps F) ds := by
  unfold checkDecls
  rw [foldlM_atF]
  simp only [checkDecl_datF]

/-! ## The punchline -/

/-- A successful executable run of the declaration checker is
reproduced by the pure fueled checker at some fuel. -/
theorem checkDecls_bridge {ds : List Declaration} {env' : Env}
    (h : checkDecls cachedOps ds = .ok env') :
    ∃ F, checkDecls (fueledOps F) ds = .ok env' := by
  have hp := (checkDecls
    (pairOps fueledOpsM cachedOps fueledOpsM_cachedOps_rel) ds).property
  rw [checkDecls_fst_dproj, checkDecls_snd_dproj] at hp
  obtain ⟨F, hF⟩ := hp env' h
  rw [checkDecls_datF] at hF
  exact ⟨F, hF⟩

end DeclBattery

end Setlec
