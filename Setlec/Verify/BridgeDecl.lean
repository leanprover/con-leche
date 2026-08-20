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

set_option maxHeartbeats 25600000 in
theorem checkIotaRules_fst_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm : Nat) :
    ∀ (j : Nat) (rules : List RecRule),
      (checkIotaRules (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
        nP nM nm j rules).val.1 =
      checkIotaRules o₁ env' envSelf f cvName lps tyA nP nM nm j rules
  | _, [] => rfl
  | j, r :: rest => by
    rw [checkIotaRules, checkIotaRules]
    have ih := checkIotaRules_fst_dproj env' envSelf f cvName lps tyA
      nP nM nm (j + 1) rest
    dfst_step <;> (try rw [ih]) <;> dfst_step <;> (try rw [ih]) <;>
      dfst_step <;> (try rw [ih]) <;> dfst_step

set_option maxHeartbeats 25600000 in
theorem checkIotaRules_snd_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (nP nM nm : Nat) :
    ∀ (j : Nat) (rules : List RecRule),
      (checkIotaRules (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
        nP nM nm j rules).val.2 =
      checkIotaRules o₂ env' envSelf f cvName lps tyA nP nM nm j rules
  | _, [] => rfl
  | j, r :: rest => by
    rw [checkIotaRules, checkIotaRules]
    have ih := checkIotaRules_snd_dproj env' envSelf f cvName lps tyA
      nP nM nm (j + 1) rest
    dsnd_step <;> (try rw [ih]) <;> dsnd_step <;> (try rw [ih]) <;>
      dsnd_step <;> (try rw [ih]) <;> dsnd_step

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

macro "dfst_step4" : tactic =>
  `(tactic| repeat (first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | (rw [checkConstantVal_fst_dproj])
    | (rw [checkProjLookups_fst_dproj])
    | (rw [checkProjTy_fst_dproj])
    | (rw [checkProjIota_fst_dproj])
    | (rw [checkProjRule_fst_dproj])
    | (rw [checkIndMember_fst_dproj])
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
    | (rw [checkConstantVal_snd_dproj])
    | (rw [checkProjLookups_snd_dproj])
    | (rw [checkProjTy_snd_dproj])
    | (rw [checkProjIota_snd_dproj])
    | (rw [checkProjRule_snd_dproj])
    | (rw [checkIndMember_snd_dproj])
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
    | (rw [checkConstantVal_fst_dproj])
    | (rw [checkProjLookups_fst_dproj])
    | (rw [checkProjTy_fst_dproj])
    | (rw [checkProjIota_fst_dproj])
    | (rw [checkProjRule_fst_dproj])
    | (rw [checkIndMember_fst_dproj])
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
    | (rw [checkConstantVal_snd_dproj])
    | (rw [checkProjLookups_snd_dproj])
    | (rw [checkProjTy_snd_dproj])
    | (rw [checkProjIota_snd_dproj])
    | (rw [checkProjRule_snd_dproj])
    | (rw [checkIndMember_snd_dproj])
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

theorem checkDecl_fst_dproj (env : Env) (d : Declaration) :
    (checkDecl (pairOps o₁ o₂ h) env d).val.1 =
      checkDecl o₁ env d := by
  unfold checkDecl
  dfst_tac5

theorem checkDecl_snd_dproj (env : Env) (d : Declaration) :
    (checkDecl (pairOps o₁ o₂ h) env d).val.2 =
      checkDecl o₂ env d := by
  unfold checkDecl
  dsnd_tac5

theorem checkDecls_fst_dproj (ds : List Declaration) :
    (checkDecls (pairOps o₁ o₂ h) ds).val.1 =
      checkDecls o₁ ds := by
  unfold checkDecls
  dfst_tac5

theorem checkDecls_snd_dproj (ds : List Declaration) :
    (checkDecls (pairOps o₁ o₂ h) ds).val.2 =
      checkDecls o₂ ds := by
  unfold checkDecls
  dsnd_tac5

end DeclBattery

end Setlec
