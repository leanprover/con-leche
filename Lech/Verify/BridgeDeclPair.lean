import Lech.Verify.BridgeDecl

/-!
# The cache-refinement bridge, part C': the pair-monad projection battery

Split out of `Lech/Verify/BridgeDecl.lean` at task #184 (the build-time
audit); the operation records it stands on stay there.

For every declaration-checker function, `X_fst_dproj` and `X_snd_dproj` say
that the first / second component of a run over the *paired* operation record
`pairOps o₁ o₂ h` is the corresponding run over `o₁` / `o₂` alone — the
pairing pushed through the whole checker.

**Nothing outside this file consumes these theorems today.**  The fuel
conversions the cached lane rewrites by are the `*_datF` family, which stayed
in `Lech.Verify.BridgeDecl`; the punchline this battery was written for
(`checkDecl_wfOpsM_bridge`, named in the old module docstring) no longer
exists.  That is exactly why the file can sit off the build's critical path:
it is reached only from the `Lech` umbrella, so it stays built, sorry-free
and gated, without any chain module waiting for it.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Lech

variable {mode : CheckMode}

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

macro "dfst_step_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dfst_step" : tactic => `(tactic| repeat dfst_step_alt)

macro "dfst_tac" : tactic =>
  `(tactic| repeat' dfst_step_alt)

macro "dsnd_step_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_snd_proj])
    | (rw [foldlM_snd])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dsnd_step" : tactic => `(tactic| repeat dsnd_step_alt)

macro "dsnd_tac" : tactic =>
  `(tactic| repeat' dsnd_step_alt)

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

theorem checkProjShape_fst_dproj (pty cty : Expr) (nP nF : Nat) :
    (checkProjShape pty cty nP nF : PairM rel _).val.1 =
      (checkProjShape pty cty nP nF : M₁ _) := by
  unfold checkProjShape
  dfst_tac

theorem checkProjShape_snd_dproj (pty cty : Expr) (nP nF : Nat) :
    (checkProjShape pty cty nP nF : PairM rel _).val.2 =
      (checkProjShape pty cty nP nF : M₂ _) := by
  unfold checkProjShape
  dsnd_tac

theorem pairOps_isDefEq_fst (env : Env) (d : Nat) (a b : Expr) :
    ((pairOps o₁ o₂ h).isDefEq env d a b).val.1 =
      o₁.isDefEq env d a b := rfl

theorem pairOps_isDefEq_snd (env : Env) (d : Nat) (a b : Expr) :
    ((pairOps o₁ o₂ h).isDefEq env d a b).val.2 =
      o₂.isDefEq env d a b := rfl

theorem unwrapOr_fst_dproj {α : Type} (o : Option α) (e : CheckError) :
    (unwrapOr o e : PairM rel α).val.1 = (unwrapOr o e : M₁ α) := by
  cases o <;> rfl

theorem unwrapOr_snd_dproj {α : Type} (o : Option α) (e : CheckError) :
    (unwrapOr o e : PairM rel α).val.2 = (unwrapOr o e : M₂ α) := by
  cases o <;> rfl

theorem pairOps_inferType_fst (env : Env) (d : Nat) (a : Expr) :
    ((pairOps o₁ o₂ h).inferType env d a).val.1 =
      o₁.inferType env d a := rfl

theorem pairOps_inferType_snd (env : Env) (d : Nat) (a : Expr) :
    ((pairOps o₁ o₂ h).inferType env d a).val.2 =
      o₂.inferType env d a := rfl

theorem pairOps_annotate_fst' (env : Env) (d : Nat) (a : Expr) :
    ((pairOps o₁ o₂ h).annotate env d a).val.1 =
      o₁.annotate env d a := rfl

theorem pairOps_annotate_snd' (env : Env) (d : Nat) (a : Expr) :
    ((pairOps o₁ o₂ h).annotate env d a).val.2 =
      o₂.annotate env d a := rfl

theorem checkTypedList_fst_dproj (env : Env) (depth : Nat) :
    ∀ (as bs : List Expr),
      (checkTypedList (pairOps o₁ o₂ h) env depth as bs).val.1 =
      checkTypedList o₁ env depth as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold checkTypedList
    simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
      PairM.fst_ite, pairOps_isDefEq_fst, pairOps_inferType_fst,
      checkTypedList_fst_dproj env depth as bs]

theorem checkTypedList_snd_dproj (env : Env) (depth : Nat) :
    ∀ (as bs : List Expr),
      (checkTypedList (pairOps o₁ o₂ h) env depth as bs).val.2 =
      checkTypedList o₂ env depth as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold checkTypedList
    simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
      PairM.snd_ite, pairOps_isDefEq_snd, pairOps_inferType_snd,
      checkTypedList_snd_dproj env depth as bs]

theorem checkAnnotList_fst_dproj (env : Env) (depth : Nat) :
    ∀ (as : List Expr),
      (checkAnnotList (pairOps o₁ o₂ h) env depth as).val.1 =
      checkAnnotList o₁ env depth as
  | [] => rfl
  | a :: as => by
    unfold checkAnnotList
    simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
      PairM.fst_ite, pairOps_annotate_fst',
      checkAnnotList_fst_dproj env depth as]

theorem checkAnnotList_snd_dproj (env : Env) (depth : Nat) :
    ∀ (as : List Expr),
      (checkAnnotList (pairOps o₁ o₂ h) env depth as).val.2 =
      checkAnnotList o₂ env depth as
  | [] => rfl
  | a :: as => by
    unfold checkAnnotList
    simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
      PairM.snd_ite, pairOps_annotate_snd',
      checkAnnotList_snd_dproj env depth as]

theorem checkDefEqList_fst_dproj (env : Env) (depth : Nat) :
    ∀ (as bs : List Expr),
      (checkDefEqList (pairOps o₁ o₂ h) env depth as bs).val.1 =
      checkDefEqList o₁ env depth as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold checkDefEqList
    simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
      PairM.fst_ite, pairOps_isDefEq_fst,
      checkDefEqList_fst_dproj env depth as bs]

theorem checkDefEqList_snd_dproj (env : Env) (depth : Nat) :
    ∀ (as bs : List Expr),
      (checkDefEqList (pairOps o₁ o₂ h) env depth as bs).val.2 =
      checkDefEqList o₂ env depth as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold checkDefEqList
    simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
      PairM.snd_ite, pairOps_isDefEq_snd,
      checkDefEqList_snd_dproj env depth as bs]

theorem checkIotaSidesTy_fst_dproj (envSelf : Env) (depth : Nat)
    (alphaS lhsS rhsS : Expr) (ℓA : Level) (cvName : Name) :
    (checkIotaSidesTy mode (pairOps o₁ o₂ h) envSelf depth alphaS lhsS rhsS
      ℓA cvName).val.1 =
    checkIotaSidesTy mode o₁ envSelf depth alphaS lhsS rhsS ℓA cvName := by
  unfold checkIotaSidesTy
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, pairOps_isDefEq_fst, pairOps_inferType_fst]

theorem checkIotaSidesTy_snd_dproj (envSelf : Env) (depth : Nat)
    (alphaS lhsS rhsS : Expr) (ℓA : Level) (cvName : Name) :
    (checkIotaSidesTy mode (pairOps o₁ o₂ h) envSelf depth alphaS lhsS rhsS
      ℓA cvName).val.2 =
    checkIotaSidesTy mode o₂ envSelf depth alphaS lhsS rhsS ℓA cvName := by
  unfold checkIotaSidesTy
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, pairOps_isDefEq_snd, pairOps_inferType_snd]

macro "dfst_stepPI_alt" : tactic =>
  `(tactic| first
    | (rw [checkIotaSidesTy_fst_dproj])
    | (rw [unwrapOr_fst_dproj])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dfst_stepPI" : tactic => `(tactic| repeat dfst_stepPI_alt)

macro "dsnd_stepPI_alt" : tactic =>
  `(tactic| first
    | (rw [checkIotaSidesTy_snd_dproj])
    | (rw [unwrapOr_snd_dproj])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dsnd_stepPI" : tactic => `(tactic| repeat dsnd_stepPI_alt)

theorem checkProjIota_fst_dproj (env' envSelf : Env) (T ctorName : Name) (lps : List Name) (cvj : ConstantVal) (nP nF i : Nat) :
    (checkProjIota mode (pairOps o₁ o₂ h) env' envSelf T ctorName lps cvj nP nF i).val.1 =
      checkProjIota mode o₁ env' envSelf T ctorName lps cvj nP nF i := by
  unfold checkProjIota
  repeat' dfst_stepPI_alt

theorem checkProjIota_snd_dproj (env' envSelf : Env) (T ctorName : Name) (lps : List Name) (cvj : ConstantVal) (nP nF i : Nat) :
    (checkProjIota mode (pairOps o₁ o₂ h) env' envSelf T ctorName lps cvj nP nF i).val.2 =
      checkProjIota mode o₂ env' envSelf T ctorName lps cvj nP nF i := by
  unfold checkProjIota
  repeat' dsnd_stepPI_alt

theorem checkIotaThm_fst_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) :
    (checkIotaThm mode (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA).val.1 =
    checkIotaThm mode o₁ env' envSelf f cvName lps tyA mI rP j r cvj
      cnP cnF rhsA := by
  unfold checkIotaThm
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, pairOps_isDefEq_fst, unwrapOr_fst_dproj,
    checkDefEqList_fst_dproj, checkTypedList_fst_dproj,
    checkIotaSidesTy_fst_dproj]

theorem checkIotaThm_snd_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) :
    (checkIotaThm mode (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA).val.2 =
    checkIotaThm mode o₂ env' envSelf f cvName lps tyA mI rP j r cvj
      cnP cnF rhsA := by
  unfold checkIotaThm
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, pairOps_isDefEq_snd, unwrapOr_snd_dproj,
    checkDefEqList_snd_dproj, checkTypedList_snd_dproj,
    checkIotaSidesTy_snd_dproj]

theorem checkIotaThmN_fst_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) :
    (checkIotaThmN mode (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA).val.1 =
    checkIotaThmN mode o₁ env' envSelf f cvName lps tyA mI rP j r cvj
      cnP cnF rhsA := by
  unfold checkIotaThmN
  split
  · rfl
  · simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
      PairM.fst_ite, pairOps_isDefEq_fst, unwrapOr_fst_dproj,
      checkDefEqList_fst_dproj, checkTypedList_fst_dproj,
      checkAnnotList_fst_dproj, checkIotaSidesTy_fst_dproj]

theorem checkIotaThmN_snd_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) :
    (checkIotaThmN mode (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
      mI rP j r cvj cnP cnF rhsA).val.2 =
    checkIotaThmN mode o₂ env' envSelf f cvName lps tyA mI rP j r cvj
      cnP cnF rhsA := by
  unfold checkIotaThmN
  split
  · rfl
  · simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
      PairM.snd_ite, pairOps_isDefEq_snd, unwrapOr_snd_dproj,
      checkDefEqList_snd_dproj, checkTypedList_snd_dproj,
      checkAnnotList_snd_dproj, checkIotaSidesTy_snd_dproj]

set_option maxHeartbeats 12800000 in
theorem checkIotaRule_fst_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) :
    (checkIotaRule mode (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
      mI rP j r).val.1 =
    checkIotaRule mode o₁ env' envSelf f cvName lps tyA mI rP j r := by
  unfold checkIotaRule
  dfst_tac
  all_goals first
  | rw [checkIotaThm_fst_dproj]
  | rw [checkIotaThmN_fst_dproj]

theorem checkIotaRules_fst_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP : Nat) :
    ∀ (j : Nat) (rules : List RecRule),
      (checkIotaRules mode (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
        mI rP j rules).val.1 =
      checkIotaRules mode o₁ env' envSelf f cvName lps tyA mI rP j rules
  | _, [] => rfl
  | j, r :: rest => by
    show ((do
        let r' ← checkIotaRule mode (pairOps o₁ o₂ h) env' envSelf f cvName
          lps tyA mI rP j r
        let rest' ← checkIotaRules mode (pairOps o₁ o₂ h) env' envSelf f
          cvName lps tyA mI rP (j + 1) rest
        pure (r' :: rest') : PairM rel _)).val.1 = (do
        let r' ← checkIotaRule mode o₁ env' envSelf f cvName lps tyA
          mI rP j r
        let rest' ← checkIotaRules mode o₁ env' envSelf f cvName lps tyA
          mI rP (j + 1) rest
        pure (r' :: rest'))
    rw [PairM.fst_bind, checkIotaRule_fst_dproj]
    congr 1
    funext r'
    rw [PairM.fst_bind, checkIotaRules_fst_dproj env' envSelf f cvName lps tyA
      mI rP (j + 1) rest]
    rfl

set_option maxHeartbeats 12800000 in
theorem checkIotaRule_snd_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) :
    (checkIotaRule mode (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
      mI rP j r).val.2 =
    checkIotaRule mode o₂ env' envSelf f cvName lps tyA mI rP j r := by
  unfold checkIotaRule
  dsnd_tac
  all_goals first
  | rw [checkIotaThm_snd_dproj]
  | rw [checkIotaThmN_snd_dproj]

theorem checkIotaRules_snd_dproj (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP : Nat) :
    ∀ (j : Nat) (rules : List RecRule),
      (checkIotaRules mode (pairOps o₁ o₂ h) env' envSelf f cvName lps tyA
        mI rP j rules).val.2 =
      checkIotaRules mode o₂ env' envSelf f cvName lps tyA mI rP j rules
  | _, [] => rfl
  | j, r :: rest => by
    show ((do
        let r' ← checkIotaRule mode (pairOps o₁ o₂ h) env' envSelf f cvName
          lps tyA mI rP j r
        let rest' ← checkIotaRules mode (pairOps o₁ o₂ h) env' envSelf f
          cvName lps tyA mI rP (j + 1) rest
        pure (r' :: rest') : PairM rel _)).val.2 = (do
        let r' ← checkIotaRule mode o₂ env' envSelf f cvName lps tyA
          mI rP j r
        let rest' ← checkIotaRules mode o₂ env' envSelf f cvName lps tyA
          mI rP (j + 1) rest
        pure (r' :: rest'))
    rw [PairM.snd_bind, checkIotaRule_snd_dproj]
    congr 1
    funext r'
    rw [PairM.snd_bind, checkIotaRules_snd_dproj env' envSelf f cvName lps tyA
      mI rP (j + 1) rest]
    rfl

macro "dfst_step2_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | (rw [checkConstantVal_fst_dproj])
    | (rw [checkProjLookups_fst_dproj])
    | (rw [checkProjTy_fst_dproj])
    | (rw [checkProjShape_fst_dproj])
    | (rw [checkProjIota_fst_dproj])
    | (rw [checkProjRule_fst_dproj])
    | (rw [checkDefEqList_fst_dproj])
    | (rw [checkIndMember_fst_dproj])
    | (rw [checkIotaRule_fst_dproj])
    | (rw [checkIotaRules_fst_dproj])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dfst_step2" : tactic => `(tactic| repeat dfst_step2_alt)

macro "dfst_tac2" : tactic =>
  `(tactic| repeat' dfst_step2_alt)

macro "dsnd_step2_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_snd_proj])
    | (rw [foldlM_snd])
    | (rw [checkConstantVal_snd_dproj])
    | (rw [checkProjLookups_snd_dproj])
    | (rw [checkProjTy_snd_dproj])
    | (rw [checkProjShape_snd_dproj])
    | (rw [checkProjIota_snd_dproj])
    | (rw [checkProjRule_snd_dproj])
    | (rw [checkDefEqList_snd_dproj])
    | (rw [checkIndMember_snd_dproj])
    | (rw [checkIotaRule_snd_dproj])
    | (rw [checkIotaRules_snd_dproj])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dsnd_step2" : tactic => `(tactic| repeat dsnd_step2_alt)

macro "dsnd_tac2" : tactic =>
  `(tactic| repeat' dsnd_step2_alt)

theorem checkProjRule_fst_dproj (env' : Env) (pty : Expr) (cvj : ConstantVal) (lps : List Name) (nP nF i : Nat) :
    (checkProjRule (pairOps o₁ o₂ h) env' pty cvj lps nP nF i).val.1 =
      checkProjRule o₁ env' pty cvj lps nP nF i := by
  unfold checkProjRule
  dfst_tac2 <;> dfst_step2 <;> dfst_step2

theorem checkProjRule_snd_dproj (env' : Env) (pty : Expr) (cvj : ConstantVal) (lps : List Name) (nP nF i : Nat) :
    (checkProjRule (pairOps o₁ o₂ h) env' pty cvj lps nP nF i).val.2 =
      checkProjRule o₂ env' pty cvj lps nP nF i := by
  unfold checkProjRule
  dsnd_tac2 <;> dsnd_step2 <;> dsnd_step2

theorem checkMemberVal_fst_dproj (blockNames : List Name)
    (env' : Env) (cv : ConstantVal) :
    (checkMemberVal (pairOps o₁ o₂ h) blockNames env' cv).val.1 =
      checkMemberVal o₁ blockNames env' cv := by
  unfold checkMemberVal
  dfst_tac2

theorem checkMemberVal_snd_dproj (blockNames : List Name)
    (env' : Env) (cv : ConstantVal) :
    (checkMemberVal (pairOps o₁ o₂ h) blockNames env' cv).val.2 =
      checkMemberVal o₂ blockNames env' cv := by
  unfold checkMemberVal
  dsnd_tac2

theorem checkIndMember_fst_dproj (blockNames : List Name) (caps : IndCaps) (env' : Env) (ci : ConstantInfo) :
    (checkIndMember (pairOps o₁ o₂ h) blockNames caps env' ci).val.1 =
      checkIndMember o₁ blockNames caps env' ci := by
  unfold checkIndMember
  dfst_tac2
  all_goals rw [checkMemberVal_fst_dproj]

theorem checkIndMember_snd_dproj (blockNames : List Name) (caps : IndCaps) (env' : Env) (ci : ConstantInfo) :
    (checkIndMember (pairOps o₁ o₂ h) blockNames caps env' ci).val.2 =
      checkIndMember o₂ blockNames caps env' ci := by
  unfold checkIndMember
  dsnd_tac2
  all_goals rw [checkMemberVal_snd_dproj]

theorem provisionRecs_fst_dproj (blockNames : List Name) :
    ∀ (envAcc : Env) (recs : List ConstantInfo),
      (provisionRecs (pairOps o₁ o₂ h) blockNames envAcc recs).val.1 =
      provisionRecs o₁ blockNames envAcc recs
  | _, [] => rfl
  | envAcc, ci :: rest => by
    unfold provisionRecs
    (dfst_step2 <;> dfst_step2) <;>
      first
        | (rw [checkMemberVal_fst_dproj])
        | exact provisionRecs_fst_dproj blockNames _ rest
        | rfl

theorem provisionRecs_snd_dproj (blockNames : List Name) :
    ∀ (envAcc : Env) (recs : List ConstantInfo),
      (provisionRecs (pairOps o₁ o₂ h) blockNames envAcc recs).val.2 =
      provisionRecs o₂ blockNames envAcc recs
  | _, [] => rfl
  | envAcc, ci :: rest => by
    unfold provisionRecs
    (dsnd_step2 <;> dsnd_step2) <;>
      first
        | (rw [checkMemberVal_snd_dproj])
        | exact provisionRecs_snd_dproj blockNames _ rest
        | rfl

theorem checkIndRecs_fst_dproj (blockNames : List Name) (env₂ : Env)
    (recs : List ConstantInfo) :
    (checkIndRecs mode (pairOps o₁ o₂ h) blockNames env₂ recs).val.1 =
      checkIndRecs mode o₁ blockNames env₂ recs := by
  unfold checkIndRecs
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, provisionRecs_fst_dproj, foldlM_fst,
    checkIotaRules_fst_dproj]

theorem checkIndRecs_snd_dproj (blockNames : List Name) (env₂ : Env)
    (recs : List ConstantInfo) :
    (checkIndRecs mode (pairOps o₁ o₂ h) blockNames env₂ recs).val.2 =
      checkIndRecs mode o₂ blockNames env₂ recs := by
  unfold checkIndRecs
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, provisionRecs_snd_dproj, foldlM_snd,
    checkIotaRules_snd_dproj]

macro "dfst_step3_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | (rw [checkConstantVal_fst_dproj])
    | (rw [checkProjLookups_fst_dproj])
    | (rw [checkProjTy_fst_dproj])
    | (rw [checkProjShape_fst_dproj])
    | (rw [checkProjIota_fst_dproj])
    | (rw [checkProjRule_fst_dproj])
    | (rw [checkIndMember_fst_dproj])
    | (rw [checkIotaRule_fst_dproj])
    | (rw [checkIotaRules_fst_dproj])
    | (rw [checkProjFn_fst_dproj])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dfst_step3" : tactic => `(tactic| repeat dfst_step3_alt)

macro "dfst_tac3" : tactic =>
  `(tactic| repeat' dfst_step3_alt)

macro "dsnd_step3_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_snd_proj])
    | (rw [foldlM_snd])
    | (rw [checkConstantVal_snd_dproj])
    | (rw [checkProjLookups_snd_dproj])
    | (rw [checkProjTy_snd_dproj])
    | (rw [checkProjShape_snd_dproj])
    | (rw [checkProjIota_snd_dproj])
    | (rw [checkProjRule_snd_dproj])
    | (rw [checkIndMember_snd_dproj])
    | (rw [checkIotaRule_snd_dproj])
    | (rw [checkIotaRules_snd_dproj])
    | (rw [checkProjFn_snd_dproj])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dsnd_step3" : tactic => `(tactic| repeat dsnd_step3_alt)

macro "dsnd_tac3" : tactic =>
  `(tactic| repeat' dsnd_step3_alt)

theorem checkProjFn_fst_dproj (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) :
    (checkProjFn mode (pairOps o₁ o₂ h) env' T ctorName lps nP nF i).val.1 =
      checkProjFn mode o₁ env' T ctorName lps nP nF i := by
  unfold checkProjFn
  dfst_tac3 <;> dfst_step3 <;> dfst_step3 <;> dfst_step3

theorem checkProjFn_snd_dproj (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) :
    (checkProjFn mode (pairOps o₁ o₂ h) env' T ctorName lps nP nF i).val.2 =
      checkProjFn mode o₂ env' T ctorName lps nP nF i := by
  unfold checkProjFn
  dsnd_tac3 <;> dsnd_step3 <;> dsnd_step3 <;> dsnd_step3

theorem installProjFnStep_fst_dproj (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) (e : Env) (i : Nat) :
    (installProjFnStep mode (pairOps o₁ o₂ h) T ctorName lps nP nF e i).val.1
      = installProjFnStep mode o₁ T ctorName lps nP nF e i := by
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
    (installProjFnStep mode (pairOps o₁ o₂ h) T ctorName lps nP nF e i).val.2
      = installProjFnStep mode o₂ T ctorName lps nP nF e i := by
  unfold installProjFnStep
  split
  · exact checkProjFn_snd_dproj e T ctorName lps nP nF i
  · rfl

theorem installBasisDecl_snd_dproj (env : Env) (ci : ConstantInfo) :
    (installBasisDecl env ci : PairM rel _).val.2 =
      (installBasisDecl env ci : M₂ _) := by
  unfold installBasisDecl
  dsnd_tac

/-! ### The direct simple-structure path (task #82) -/

theorem pairOps_annotate_fst (env : Env) (d : Nat) (a : Expr) :
    ((pairOps o₁ o₂ h).annotate env d a).val.1 =
      o₁.annotate env d a := rfl

theorem pairOps_annotate_snd (env : Env) (d : Nat) (a : Expr) :
    ((pairOps o₁ o₂ h).annotate env d a).val.2 =
      o₂.annotate env d a := rfl

theorem pairOps_ensureSort_fst (env : Env) (d : Nat) (a : Expr) :
    ((pairOps o₁ o₂ h).ensureSort env d a).val.1 =
      o₁.ensureSort env d a := rfl

theorem pairOps_ensureSort_snd (env : Env) (d : Nat) (a : Expr) :
    ((pairOps o₁ o₂ h).ensureSort env d a).val.2 =
      o₂.ensureSort env d a := rfl

theorem checkDirectFieldSorts_fst_dproj (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs : List Expr) :
    ∀ j : Nat,
      (checkDirectFieldSorts (pairOps o₁ o₂ h) env isProp large s nP fvs
          j).val.1 =
        checkDirectFieldSorts o₁ env isProp large s nP fvs j
  | 0 => rfl
  | j + 1 => by
    unfold checkDirectFieldSorts
    simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
      PairM.fst_ite, pairOps_inferType_fst, pairOps_ensureSort_fst,
      liftFueled_fst_proj, unwrapOr_fst_dproj,
      checkDirectFieldSorts_fst_dproj env isProp large s nP fvs j]

theorem checkDirectFieldSorts_snd_dproj (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs : List Expr) :
    ∀ j : Nat,
      (checkDirectFieldSorts (pairOps o₁ o₂ h) env isProp large s nP fvs
          j).val.2 =
        checkDirectFieldSorts o₂ env isProp large s nP fvs j
  | 0 => rfl
  | j + 1 => by
    unfold checkDirectFieldSorts
    simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
      PairM.snd_ite, pairOps_inferType_snd, pairOps_ensureSort_snd,
      liftFueled_snd_proj, unwrapOr_snd_dproj,
      checkDirectFieldSorts_snd_dproj env isProp large s nP fvs j]

theorem checkDirectDomsAt_fst_dproj (env : Env) (off : Nat)
    (fvs doms : List Expr) :
    ∀ j : Nat,
      (checkDirectDomsAt (pairOps o₁ o₂ h) env off fvs doms j).val.1 =
        checkDirectDomsAt o₁ env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    unfold checkDirectDomsAt
    simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
      PairM.fst_ite, pairOps_isDefEq_fst, unwrapOr_fst_dproj,
      checkDirectDomsAt_fst_dproj env off fvs doms j]

theorem checkDirectDomsAt_snd_dproj (env : Env) (off : Nat)
    (fvs doms : List Expr) :
    ∀ j : Nat,
      (checkDirectDomsAt (pairOps o₁ o₂ h) env off fvs doms j).val.2 =
        checkDirectDomsAt o₂ env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    unfold checkDirectDomsAt
    simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
      PairM.snd_ite, pairOps_isDefEq_snd, unwrapOr_snd_dproj,
      checkDirectDomsAt_snd_dproj env off fvs doms j]

theorem checkDirectInd_fst_dproj (env : Env) (p : DirectParts) :
    (checkDirectInd (pairOps o₁ o₂ h) env p).val.1 =
      checkDirectInd o₁ env p := by
  unfold checkDirectInd
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, unwrapOr_fst_dproj, checkConstantVal_fst_dproj]

theorem checkDirectInd_snd_dproj (env : Env) (p : DirectParts) :
    (checkDirectInd (pairOps o₁ o₂ h) env p).val.2 =
      checkDirectInd o₂ env p := by
  unfold checkDirectInd
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, unwrapOr_snd_dproj, checkConstantVal_snd_dproj]

theorem checkDirectCtor_fst_dproj (env₀ env : Env) (p : DirectParts)
    (cvTa : ConstantVal) :
    (checkDirectCtor (pairOps o₁ o₂ h) env₀ env p cvTa).val.1 =
      checkDirectCtor o₁ env₀ env p cvTa := by
  unfold checkDirectCtor
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, unwrapOr_fst_dproj, checkConstantVal_fst_dproj,
    checkDirectFieldSorts_fst_dproj, checkDirectDomsAt_fst_dproj]

theorem checkDirectCtor_snd_dproj (env₀ env : Env) (p : DirectParts)
    (cvTa : ConstantVal) :
    (checkDirectCtor (pairOps o₁ o₂ h) env₀ env p cvTa).val.2 =
      checkDirectCtor o₂ env₀ env p cvTa := by
  unfold checkDirectCtor
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, unwrapOr_snd_dproj, checkConstantVal_snd_dproj,
    checkDirectFieldSorts_snd_dproj, checkDirectDomsAt_snd_dproj]

theorem checkDirectRec_fst_dproj (env : Env) (p : DirectParts)
    (cvTa cvCa : ConstantVal) :
    (checkDirectRec (pairOps o₁ o₂ h) env p cvTa cvCa).val.1 =
      checkDirectRec o₁ env p cvTa cvCa := by
  unfold checkDirectRec
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, pairOps_isDefEq_fst, pairOps_inferType_fst,
    pairOps_ensureSort_fst, unwrapOr_fst_dproj, checkConstantVal_fst_dproj]

theorem checkDirectRec_snd_dproj (env : Env) (p : DirectParts)
    (cvTa cvCa : ConstantVal) :
    (checkDirectRec (pairOps o₁ o₂ h) env p cvTa cvCa).val.2 =
      checkDirectRec o₂ env p cvTa cvCa := by
  unfold checkDirectRec
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, pairOps_isDefEq_snd, pairOps_inferType_snd,
    pairOps_ensureSort_snd, unwrapOr_snd_dproj, checkConstantVal_snd_dproj]

theorem checkDirectProjTable_fst_dproj (T C : Name) (lps : List Name)
    (nP nF : Nat) (rs : Level) (guards : List Level) (cvCa : ConstantVal)
    (env : Env) :
    (checkDirectProjTable T C lps nP nF rs guards cvCa env : PairM rel _).val.1 =
      (checkDirectProjTable T C lps nP nF rs guards cvCa env : M₁ _) := by
  unfold checkDirectProjTable
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, unwrapOr_fst_dproj]

theorem checkDirectProjTable_snd_dproj (T C : Name) (lps : List Name)
    (nP nF : Nat) (rs : Level) (guards : List Level) (cvCa : ConstantVal)
    (env : Env) :
    (checkDirectProjTable T C lps nP nF rs guards cvCa env : PairM rel _).val.2 =
      (checkDirectProjTable T C lps nP nF rs guards cvCa env : M₂ _) := by
  unfold checkDirectProjTable
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, unwrapOr_snd_dproj]

theorem checkDirectStruct_fst_dproj (env : Env) (p : DirectParts) :
    (checkDirectStruct (pairOps o₁ o₂ h) env p).val.1 =
      checkDirectStruct o₁ env p := by
  unfold checkDirectStruct
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, checkConstantVal_fst_dproj,
    checkDirectInd_fst_dproj, checkDirectCtor_fst_dproj,
    checkDirectRec_fst_dproj, checkDirectProjTable_fst_dproj]

theorem checkDirectStruct_snd_dproj (env : Env) (p : DirectParts) :
    (checkDirectStruct (pairOps o₁ o₂ h) env p).val.2 =
      checkDirectStruct o₂ env p := by
  unfold checkDirectStruct
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, checkConstantVal_snd_dproj,
    checkDirectInd_snd_dproj, checkDirectCtor_snd_dproj,
    checkDirectRec_snd_dproj, checkDirectProjTable_snd_dproj]

/-! ### The direct sum route (task #175 sum-types) -/

theorem checkDirectSumInd_fst_dproj (env : Env) (p : DirectSumParts) :
    (checkDirectSumInd (pairOps o₁ o₂ h) env p).val.1 =
      checkDirectSumInd o₁ env p := by
  unfold checkDirectSumInd
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, unwrapOr_fst_dproj, checkConstantVal_fst_dproj]

theorem checkDirectSumInd_snd_dproj (env : Env) (p : DirectSumParts) :
    (checkDirectSumInd (pairOps o₁ o₂ h) env p).val.2 =
      checkDirectSumInd o₂ env p := by
  unfold checkDirectSumInd
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, unwrapOr_snd_dproj, checkConstantVal_snd_dproj]

/-- `checkDirectFieldSortsI` (task #175 indexed) through the first
projection. -/
theorem checkDirectFieldSortsI_fst_dproj (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) :
    ∀ j : Nat,
      (checkDirectFieldSortsI (pairOps o₁ o₂ h) env isProp large s nP fvs idxArgs
          j).val.1 =
        checkDirectFieldSortsI o₁ env isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    unfold checkDirectFieldSortsI
    simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
      PairM.fst_ite, pairOps_inferType_fst, pairOps_ensureSort_fst,
      liftFueled_fst_proj, unwrapOr_fst_dproj,
      checkDirectFieldSortsI_fst_dproj env isProp large s nP fvs idxArgs j]

/-- `checkDirectFieldSortsI` (task #175 indexed) through the second
projection. -/
theorem checkDirectFieldSortsI_snd_dproj (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) :
    ∀ j : Nat,
      (checkDirectFieldSortsI (pairOps o₁ o₂ h) env isProp large s nP fvs idxArgs
          j).val.2 =
        checkDirectFieldSortsI o₂ env isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    unfold checkDirectFieldSortsI
    simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
      PairM.snd_ite, pairOps_inferType_snd, pairOps_ensureSort_snd,
      liftFueled_snd_proj, unwrapOr_snd_dproj,
      checkDirectFieldSortsI_snd_dproj env isProp large s nP fvs idxArgs j]

theorem checkDirectSumCtor_fst_dproj (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (rs : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat)
    (cvTa : ConstantVal) :
    (checkDirectSumCtor (pairOps o₁ o₂ h) env₀ env T lps nP nIdx rs isProp large
      cvC nF cvTa).val.1 =
      checkDirectSumCtor o₁ env₀ env T lps nP nIdx rs isProp large cvC nF cvTa := by
  unfold checkDirectSumCtor
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, unwrapOr_fst_dproj, checkConstantVal_fst_dproj,
    checkDirectFieldSortsI_fst_dproj, checkDirectDomsAt_fst_dproj]

theorem checkDirectSumCtor_snd_dproj (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (rs : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat)
    (cvTa : ConstantVal) :
    (checkDirectSumCtor (pairOps o₁ o₂ h) env₀ env T lps nP nIdx rs isProp large
      cvC nF cvTa).val.2 =
      checkDirectSumCtor o₂ env₀ env T lps nP nIdx rs isProp large cvC nF cvTa := by
  unfold checkDirectSumCtor
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, unwrapOr_snd_dproj, checkConstantVal_snd_dproj,
    checkDirectFieldSortsI_snd_dproj, checkDirectDomsAt_snd_dproj]

theorem checkDirectSumCtors_fst_dproj (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (rs : Level) (isProp large : Bool) (cvTa : ConstantVal) :
    ∀ cs : List (ConstantVal × Nat),
      (checkDirectSumCtors (pairOps o₁ o₂ h) env₀ env T lps nP nIdx rs isProp large
        cvTa cs).val.1 =
        checkDirectSumCtors o₁ env₀ env T lps nP nIdx rs isProp large cvTa cs
  | [] => rfl
  | c :: cs => by
    unfold checkDirectSumCtors
    simp only [PairM.fst_bind, PairM.fst_pure, checkDirectSumCtor_fst_dproj,
      checkDirectSumCtors_fst_dproj env₀ env T lps nP nIdx rs isProp large cvTa cs]

theorem checkDirectSumCtors_snd_dproj (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (rs : Level) (isProp large : Bool) (cvTa : ConstantVal) :
    ∀ cs : List (ConstantVal × Nat),
      (checkDirectSumCtors (pairOps o₁ o₂ h) env₀ env T lps nP nIdx rs isProp large
        cvTa cs).val.2 =
        checkDirectSumCtors o₂ env₀ env T lps nP nIdx rs isProp large cvTa cs
  | [] => rfl
  | c :: cs => by
    unfold checkDirectSumCtors
    simp only [PairM.snd_bind, PairM.snd_pure, checkDirectSumCtor_snd_dproj,
      checkDirectSumCtors_snd_dproj env₀ env T lps nP nIdx rs isProp large cvTa cs]

theorem checkDirectSumRules_fst_dproj (env : Env) (rlps : List Name) (T : Name)
    (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr)) :
    ∀ k j : Nat,
      (checkDirectSumRules (pairOps o₁ o₂ h) env rlps T lps elim large nP nIdx tty
        ctors k j).val.1 =
        checkDirectSumRules o₁ env rlps T lps elim large nP nIdx tty ctors k j
  | 0, _ => rfl
  | k + 1, j => by
    unfold checkDirectSumRules
    simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw, PairM.fst_ite,
      pairOps_inferType_fst, unwrapOr_fst_dproj,
      checkDirectSumRules_fst_dproj env rlps T lps elim large nP nIdx tty ctors k (j + 1)]

theorem checkDirectSumRules_snd_dproj (env : Env) (rlps : List Name) (T : Name)
    (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr)) :
    ∀ k j : Nat,
      (checkDirectSumRules (pairOps o₁ o₂ h) env rlps T lps elim large nP nIdx tty
        ctors k j).val.2 =
        checkDirectSumRules o₂ env rlps T lps elim large nP nIdx tty ctors k j
  | 0, _ => rfl
  | k + 1, j => by
    unfold checkDirectSumRules
    simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw, PairM.snd_ite,
      pairOps_inferType_snd, unwrapOr_snd_dproj,
      checkDirectSumRules_snd_dproj env rlps T lps elim large nP nIdx tty ctors k (j + 1)]

theorem checkDirectSumRec_fst_dproj (env : Env) (p : DirectSumParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    (checkDirectSumRec (pairOps o₁ o₂ h) env p cvTa ctorsA).val.1 =
      checkDirectSumRec o₁ env p cvTa ctorsA := by
  unfold checkDirectSumRec
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, pairOps_isDefEq_fst, pairOps_inferType_fst,
    pairOps_ensureSort_fst, unwrapOr_fst_dproj, checkConstantVal_fst_dproj,
    checkDirectSumRules_fst_dproj]

theorem checkDirectSumRec_snd_dproj (env : Env) (p : DirectSumParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    (checkDirectSumRec (pairOps o₁ o₂ h) env p cvTa ctorsA).val.2 =
      checkDirectSumRec o₂ env p cvTa ctorsA := by
  unfold checkDirectSumRec
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, pairOps_isDefEq_snd, pairOps_inferType_snd,
    pairOps_ensureSort_snd, unwrapOr_snd_dproj, checkConstantVal_snd_dproj,
    checkDirectSumRules_snd_dproj]

theorem checkDirectSum_fst_dproj (env : Env) (p : DirectSumParts) :
    (checkDirectSum (pairOps o₁ o₂ h) env p).val.1 =
      checkDirectSum o₁ env p := by
  unfold checkDirectSum
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, checkDirectSumInd_fst_dproj, checkDirectSumCtors_fst_dproj,
    checkDirectSumRec_fst_dproj]

theorem checkDirectSum_snd_dproj (env : Env) (p : DirectSumParts) :
    (checkDirectSum (pairOps o₁ o₂ h) env p).val.2 =
      checkDirectSum o₂ env p := by
  unfold checkDirectSum
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, checkDirectSumInd_snd_dproj, checkDirectSumCtors_snd_dproj,
    checkDirectSumRec_snd_dproj]

/-! ### The direct recursive install (task #188) -/

theorem checkDirectFixRules_fst_dproj (envR : Env) (rlps : List Name) (T : Name)
    (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    ∀ k j : Nat,
      (checkDirectFixRules (m := PairM rel) envR rlps T lps elim large nP nIdx tty
        ctors recC rlvls k j).val.1 =
        checkDirectFixRules (m := M₁) envR rlps T lps elim large nP nIdx tty ctors recC
          rlvls k j
  | 0, _ => rfl
  | k + 1, j => by
    unfold checkDirectFixRules
    simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw, PairM.fst_ite,
      unwrapOr_fst_dproj,
      checkDirectFixRules_fst_dproj envR rlps T lps elim large nP nIdx tty ctors recC rlvls
        k (j + 1)]

theorem checkDirectFixRules_snd_dproj (envR : Env) (rlps : List Name) (T : Name)
    (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    ∀ k j : Nat,
      (checkDirectFixRules (m := PairM rel) envR rlps T lps elim large nP nIdx tty
        ctors recC rlvls k j).val.2 =
        checkDirectFixRules (m := M₂) envR rlps T lps elim large nP nIdx tty ctors recC
          rlvls k j
  | 0, _ => rfl
  | k + 1, j => by
    unfold checkDirectFixRules
    simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw, PairM.snd_ite,
      unwrapOr_snd_dproj,
      checkDirectFixRules_snd_dproj envR rlps T lps elim large nP nIdx tty ctors recC rlvls
        k (j + 1)]

theorem checkDirectFixRec_fst_dproj (env : Env) (p : DirectFixParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    (checkDirectFixRec (pairOps o₁ o₂ h) env p cvTa ctorsA).val.1 =
      checkDirectFixRec o₁ env p cvTa ctorsA := by
  unfold checkDirectFixRec
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, pairOps_isDefEq_fst, pairOps_inferType_fst,
    pairOps_ensureSort_fst, unwrapOr_fst_dproj, checkConstantVal_fst_dproj,
    checkDirectFixRules_fst_dproj]

theorem checkDirectFixRec_snd_dproj (env : Env) (p : DirectFixParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    (checkDirectFixRec (pairOps o₁ o₂ h) env p cvTa ctorsA).val.2 =
      checkDirectFixRec o₂ env p cvTa ctorsA := by
  unfold checkDirectFixRec
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, pairOps_isDefEq_snd, pairOps_inferType_snd,
    pairOps_ensureSort_snd, unwrapOr_snd_dproj, checkConstantVal_snd_dproj,
    checkDirectFixRules_snd_dproj]

theorem checkDirectFix_fst_dproj (env : Env) (p : DirectFixParts) :
    (checkDirectFix (pairOps o₁ o₂ h) env p).val.1 =
      checkDirectFix o₁ env p := by
  unfold checkDirectFix
  simp only [PairM.fst_bind, PairM.fst_pure, PairM.fst_throw,
    PairM.fst_ite, checkDirectSumInd_fst_dproj, checkDirectSumCtors_fst_dproj,
    checkDirectFixRec_fst_dproj]

theorem checkDirectFix_snd_dproj (env : Env) (p : DirectFixParts) :
    (checkDirectFix (pairOps o₁ o₂ h) env p).val.2 =
      checkDirectFix o₂ env p := by
  unfold checkDirectFix
  simp only [PairM.snd_bind, PairM.snd_pure, PairM.snd_throw,
    PairM.snd_ite, checkDirectSumInd_snd_dproj, checkDirectSumCtors_snd_dproj,
    checkDirectFixRec_snd_dproj]

macro "dfst_step4_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | (simp only [checkIndMember_fst_dproj, checkProjFn_fst_dproj,
        installProjFnStep_fst_dproj, installBasisDecl_fst_dproj])
    | (rw [checkConstantVal_fst_dproj])
    | (rw [checkProjLookups_fst_dproj])
    | (rw [checkProjTy_fst_dproj])
    | (rw [checkProjShape_fst_dproj])
    | (rw [checkProjIota_fst_dproj])
    | (rw [checkProjRule_fst_dproj])
    | (rw [checkIndMember_fst_dproj])
    | (rw [checkIotaRule_fst_dproj])
    | (rw [checkIotaRules_fst_dproj])
    | (rw [checkIndRecs_fst_dproj])
    | (rw [checkProjFn_fst_dproj])
    | (rw [checkDirectStruct_fst_dproj])
    | (rw [checkIndDecl_fst_dproj])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dfst_step4" : tactic => `(tactic| repeat dfst_step4_alt)

macro "dfst_tac4" : tactic =>
  `(tactic| repeat' dfst_step4_alt)

macro "dsnd_step4_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_snd_proj])
    | (rw [foldlM_snd])
    | (simp only [checkIndMember_snd_dproj, checkProjFn_snd_dproj,
        installProjFnStep_snd_dproj, installBasisDecl_snd_dproj])
    | (rw [checkConstantVal_snd_dproj])
    | (rw [checkProjLookups_snd_dproj])
    | (rw [checkProjTy_snd_dproj])
    | (rw [checkProjShape_snd_dproj])
    | (rw [checkProjIota_snd_dproj])
    | (rw [checkProjRule_snd_dproj])
    | (rw [checkIndMember_snd_dproj])
    | (rw [checkIotaRule_snd_dproj])
    | (rw [checkIotaRules_snd_dproj])
    | (rw [checkIndRecs_snd_dproj])
    | (rw [checkProjFn_snd_dproj])
    | (rw [checkDirectStruct_snd_dproj])
    | (rw [checkIndDecl_snd_dproj])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dsnd_step4" : tactic => `(tactic| repeat dsnd_step4_alt)

macro "dsnd_tac4" : tactic =>
  `(tactic| repeat' dsnd_step4_alt)

theorem checkIndDecl_fst_dproj (env : Env) (block : List ConstantInfo) :
    (checkIndDecl mode (pairOps o₁ o₂ h) env block).val.1 =
      checkIndDecl mode o₁ env block := by
  unfold checkIndDecl
  dfst_tac4

theorem checkIndDecl_snd_dproj (env : Env) (block : List ConstantInfo) :
    (checkIndDecl mode (pairOps o₁ o₂ h) env block).val.2 =
      checkIndDecl mode o₂ env block := by
  unfold checkIndDecl
  dsnd_tac4

macro "dfst_step5_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_fst_proj])
    | (rw [foldlM_fst])
    | (simp only [checkIndMember_fst_dproj, checkProjFn_fst_dproj,
        installProjFnStep_fst_dproj, installBasisDecl_fst_dproj,
        checkIndDecl_fst_dproj])
    | (rw [checkConstantVal_fst_dproj])
    | (rw [checkProjLookups_fst_dproj])
    | (rw [checkProjTy_fst_dproj])
    | (rw [checkProjShape_fst_dproj])
    | (rw [checkProjIota_fst_dproj])
    | (rw [checkProjRule_fst_dproj])
    | (rw [checkIndMember_fst_dproj])
    | (rw [checkIotaRule_fst_dproj])
    | (rw [checkIotaRules_fst_dproj])
    | (rw [checkIndRecs_fst_dproj])
    | (rw [checkProjFn_fst_dproj])
    | (rw [checkDirectStruct_fst_dproj])
    | (rw [checkIndDecl_fst_dproj])
    | (rw [checkDecl_fst_dproj])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dfst_step5" : tactic => `(tactic| repeat dfst_step5_alt)

macro "dfst_tac5" : tactic =>
  `(tactic| repeat' dfst_step5_alt)

macro "dsnd_step5_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_snd_proj])
    | (rw [foldlM_snd])
    | (simp only [checkIndMember_snd_dproj, checkProjFn_snd_dproj,
        installProjFnStep_snd_dproj, installBasisDecl_snd_dproj,
        checkIndDecl_snd_dproj])
    | (rw [checkConstantVal_snd_dproj])
    | (rw [checkProjLookups_snd_dproj])
    | (rw [checkProjTy_snd_dproj])
    | (rw [checkProjShape_snd_dproj])
    | (rw [checkProjIota_snd_dproj])
    | (rw [checkProjRule_snd_dproj])
    | (rw [checkIndMember_snd_dproj])
    | (rw [checkIotaRule_snd_dproj])
    | (rw [checkIotaRules_snd_dproj])
    | (rw [checkIndRecs_snd_dproj])
    | (rw [checkProjFn_snd_dproj])
    | (rw [checkDirectStruct_snd_dproj])
    | (rw [checkIndDecl_snd_dproj])
    | (rw [checkDecl_snd_dproj])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "dsnd_step5" : tactic => `(tactic| repeat dsnd_step5_alt)

macro "dsnd_tac5" : tactic =>
  `(tactic| repeat' dsnd_step5_alt)

theorem checkDefnVal_fst_dproj (env : Env) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) :
    (checkDefnVal (pairOps o₁ o₂ h) env cv value hint).val.1 =
      checkDefnVal o₁ env cv value hint := by
  unfold checkDefnVal
  dfst_tac

theorem checkThmVal_fst_dproj (env : Env) (cv : ConstantVal)
    (value : Expr) :
    (checkThmVal (pairOps o₁ o₂ h) env cv value).val.1 =
      checkThmVal o₁ env cv value := by
  unfold checkThmVal
  dfst_tac

theorem checkDefnVal_snd_dproj (env : Env) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) :
    (checkDefnVal (pairOps o₁ o₂ h) env cv value hint).val.2 =
      checkDefnVal o₂ env cv value hint := by
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

theorem checkDivModCerts_fst_dproj (env : Env) (c : Name) (annVal : Expr) :
    ∀ (stmts : List (List Expr × Expr)) (proofs : List Expr),
      (checkDivModCerts (pairOps o₁ o₂ h) env c annVal stmts proofs).val.1 =
        checkDivModCerts o₁ env c annVal stmts proofs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    simp only [checkDivModCerts]
    split
    · rw [PairM.fst_bind]
      congr 1
      funext appliedA
      rw [PairM.fst_bind]
      congr 1
      funext tp
      rw [PairM.fst_bind]
      congr 1
      funext b
      cases b with
      | true => exact checkDivModCerts_fst_dproj env c annVal srest prest
      | false => rfl
    · rfl

theorem checkDivModCerts_snd_dproj (env : Env) (c : Name) (annVal : Expr) :
    ∀ (stmts : List (List Expr × Expr)) (proofs : List Expr),
      (checkDivModCerts (pairOps o₁ o₂ h) env c annVal stmts proofs).val.2 =
        checkDivModCerts o₂ env c annVal stmts proofs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    simp only [checkDivModCerts]
    split
    · rw [PairM.snd_bind]
      congr 1
      funext appliedA
      rw [PairM.snd_bind]
      congr 1
      funext tp
      rw [PairM.snd_bind]
      congr 1
      funext b
      cases b with
      | true => exact checkDivModCerts_snd_dproj env c annVal srest prest
      | false => rfl
    · rfl

theorem checkDivModPin_fst_dproj (env env2 : Env) (c : Name) :
    (checkDivModPin (pairOps o₁ o₂ h) env env2 c).val.1 =
      checkDivModPin o₁ env env2 c := by
  unfold checkDivModPin
  repeat (first
    | (rw [checkDivModCerts_fst_dproj])
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [PairM.fst_pure, PairM.fst_throw]))

theorem checkDivModPin_snd_dproj (env env2 : Env) (c : Name) :
    (checkDivModPin (pairOps o₁ o₂ h) env env2 c).val.2 =
      checkDivModPin o₂ env env2 c := by
  unfold checkDivModPin
  repeat (first
    | (rw [checkDivModCerts_snd_dproj])
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [PairM.snd_pure, PairM.snd_throw]))

theorem checkReducePin_fst_dproj (env env2 : Env) (c : Name)
    (value : Expr) :
    (checkReducePin (pairOps o₁ o₂ h) env env2 c value).val.1 =
      checkReducePin o₁ env env2 c value := by
  unfold checkReducePin
  repeat (first
    | split
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [PairM.fst_pure, PairM.fst_throw]))

theorem checkReducePin_snd_dproj (env env2 : Env) (c : Name)
    (value : Expr) :
    (checkReducePin (pairOps o₁ o₂ h) env env2 c value).val.2 =
      checkReducePin o₂ env env2 c value := by
  unfold checkReducePin
  repeat (first
    | split
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [PairM.snd_pure, PairM.snd_throw]))

theorem checkDecl_fst_dproj (env : Env) (d : Declaration) :
    (checkDecl mode (pairOps o₁ o₂ h) env d).val.1 =
      checkDecl mode o₁ env d := by
  unfold checkDecl
  cases d with
  | defnDecl cv value hint =>
    dsimp only
    rw [PairM.fst_bind, checkConstantVal_fst_dproj]
    congr 1
    funext cv'
    rw [PairM.fst_bind, checkDefnVal_fst_dproj]
    congr 1
    funext env2
    repeat (first
      | (rw [certifyNatEqs_fst_dproj])
      | (rw [checkDivModPin_fst_dproj])
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
    dsimp only
    rw [PairM.fst_bind, checkConstantVal_fst_dproj]
    congr 1
    funext cv'
    rw [PairM.fst_bind, checkOpaqueVal_fst_dproj]
    congr 1
    funext env2
    repeat (first
      | (rw [checkReducePin_fst_dproj])
      | split
      | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [PairM.fst_pure, PairM.fst_throw]))
  | axiomDecl cv =>
    dsimp only
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
    dsimp only
    split
    · exact checkDirectStruct_fst_dproj env _
    · split
      · exact checkDirectSum_fst_dproj env _
      · split
        · exact checkDirectFix_fst_dproj env _
        · exact checkIndDecl_fst_dproj env block

theorem checkDecl_snd_dproj (env : Env) (d : Declaration) :
    (checkDecl mode (pairOps o₁ o₂ h) env d).val.2 =
      checkDecl mode o₂ env d := by
  unfold checkDecl
  cases d with
  | defnDecl cv value hint =>
    dsimp only
    rw [PairM.snd_bind, checkConstantVal_snd_dproj]
    congr 1
    funext cv'
    rw [PairM.snd_bind, checkDefnVal_snd_dproj]
    congr 1
    funext env2
    repeat (first
      | (rw [certifyNatEqs_snd_dproj])
      | (rw [checkDivModPin_snd_dproj])
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
    dsimp only
    rw [PairM.snd_bind, checkConstantVal_snd_dproj]
    congr 1
    funext cv'
    rw [PairM.snd_bind, checkOpaqueVal_snd_dproj]
    congr 1
    funext env2
    repeat (first
      | (rw [checkReducePin_snd_dproj])
      | split
      | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [PairM.snd_pure, PairM.snd_throw]))
  | axiomDecl cv =>
    dsimp only
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
    dsimp only
    split
    · exact checkDirectStruct_snd_dproj env _
    · split
      · exact checkDirectSum_snd_dproj env _
      · split
        · exact checkDirectFix_snd_dproj env _
        · exact checkIndDecl_snd_dproj env block

theorem checkDecls_fst_dproj (ds : List Declaration) :
    (checkDecls mode (pairOps o₁ o₂ h) ds).val.1 =
      checkDecls mode o₁ ds := by
  unfold checkDecls
  rw [foldlM_fst]
  simp only [checkDecl_fst_dproj]

theorem checkDecls_snd_dproj (ds : List Declaration) :
    (checkDecls mode (pairOps o₁ o₂ h) ds).val.2 =
      checkDecls mode o₂ ds := by
  unfold checkDecls
  rw [foldlM_snd]
  simp only [checkDecl_snd_dproj]
end DeclBattery


end Lech
