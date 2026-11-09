module

public import ConLeche.Verify.Fueled
public import ConLeche.Kernel.CheckDecl

public section

/-!
# The cache-refinement bridge, part C: the declaration checker

The declaration checker is monad-polymorphic over a `CheckerOps`
record, so it runs over the fueled monad as well, and the `atF` battery
reads every declaration-checker function at a fuel.

This module holds the fueled operation record (`fueledOpsM`) and the `atF` battery
— for every `check*` function, `(… (fueledOpsM …) …).val F = … (fueledOps …
F) …`, which is what `Verify/BridgeWfImp` and the cached lane's
`Verify/Cached/Bridge*` rewrite by (#184).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

/-- The fueled operations as monotone families. -/
@[expose] def fueledOpsM (mode : CheckMode) : CheckerOps FueledM where
  inferType env d e :=
    ⟨fun F => inferTypeCore mode false env F d e, fun hle h => inferTypeCore_mono hle h⟩
  isDefEq env d a b :=
    ⟨fun F => isDefEqCore mode false env F d a b, fun hle h => isDefEqCore_mono hle h⟩
  ensureSort env d e :=
    ⟨fun F => ensureSortCore mode false env F d e, fun hle h => ensureSortCore_mono hle h⟩
  whnf env d e :=
    ⟨fun F => whnf mode false env F d e, fun hle h => whnf_mono hle h⟩

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

macro "datF_step_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "datF_tac" : tactic =>
  `(tactic| repeat' datF_step_alt)

theorem checkConstantVal_datF (env : Env) (cv : ConstantVal) (F : Nat) {a : Bool} :
    (checkConstantVal (fueledOpsM mode) env cv a).val F =
      checkConstantVal (fueledOps mode F) env cv a := by
  unfold checkConstantVal
  datF_tac

theorem fueledOpsM_isDefEq_atF (env : Env) (d : Nat) (a b : Expr)
    (F : Nat) :
    ((fueledOpsM mode).isDefEq env d a b).val F =
      (fueledOps mode F).isDefEq env d a b := by rfl

theorem unwrapOr_atF {α : Type} (o : Option α) (e : CheckError)
    (F : Nat) :
    (unwrapOr o e : FueledM α).val F = (unwrapOr o e : CheckM α) := by
  cases o <;> rfl

theorem fueledOpsM_inferType_atF (env : Env) (d : Nat) (a : Expr)
    (F : Nat) :
    ((fueledOpsM mode).inferType env d a).val F =
      (fueledOps mode F).inferType env d a := by rfl

theorem installBasisDecl_datF (env : Env) (ci : ConstantInfo) (F : Nat) :
    (installBasisDecl env ci : FueledM _).val F =
      (installBasisDecl env ci : CheckM _) := by
  unfold installBasisDecl
  datF_tac

/-! ### The per-member stages, at fuel `F` -/

theorem fueledOpsM_ensureSort_atF (env : Env) (d : Nat) (a : Expr)
    (F : Nat) :
    ((fueledOpsM mode).ensureSort env d a).val F =
      (fueledOps mode F).ensureSort env d a := by rfl

theorem checkStructDomsAt_datF (env : Env) (off : Nat)
    (fvs doms : List Expr) (F : Nat) :
    ∀ j : Nat,
      (checkStructDomsAt (fueledOpsM mode) env off fvs doms j).val F =
        checkStructDomsAt (fueledOps mode F) env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    unfold checkStructDomsAt
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_isDefEq_atF, unwrapOr_atF,
      checkStructDomsAt_datF env off fvs doms F j]

theorem checkStructProjTable_datF (t : ProjTable) (env : Env) (F : Nat) :
    (checkStructProjTable t env : FueledM _).val F = (checkStructProjTable t env : CheckM _) := by
  unfold checkStructProjTable
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite]

/-! ### The constructor-list stages (#175) -/

theorem fueledOpsM_whnf_atF (env : Env) (d : Nat) (a : Expr) (F : Nat) :
    ((fueledOpsM mode).whnf env d a).val F = (fueledOps mode F).whnf env d a := by rfl

/-- Official's telescope loop (task #195) at fuel `F`. -/
theorem whnfTelescope_datF (env : Env) (F : Nat) :
    ∀ (i n : Nat) (e : Expr),
      (whnfTelescope (fueledOpsM mode) env i n e).val F =
        whnfTelescope (fueledOps mode F) env i n e
  | i, 0, e => by
    unfold whnfTelescope
    simp only [FueledM.atF_bind, fueledOpsM_whnf_atF]
    congr 1
    funext e'
    split <;> simp only [FueledM.atF_pure, FueledM.atF_throw]
  | i, n + 1, e => by
    unfold whnfTelescope
    simp only [FueledM.atF_bind, fueledOpsM_whnf_atF]
    congr 1
    funext e'
    split
    · next dom body =>
      simp only [FueledM.atF_bind, FueledM.atF_pure,
        whnfTelescope_datF env F (i + 1) n (body.instantiate1 (.fvar i dom))]
    · simp only [FueledM.atF_throw]

/-- The former's telescope stage at fuel `F`. -/
theorem checkSumTele_datF (n : Nat) (cvTa₀ : ConstantVal) (F : Nat) :
    (checkSumTele n cvTa₀ : FueledM _).val F = checkSumTele n cvTa₀ := by
  unfold checkSumTele
  split
  · simp only [FueledM.atF_pure]
  · simp only [FueledM.atF_throw]

/-- `checkStructFieldSortsI` (task #175 indexed) at fuel `F`. -/
theorem checkStructFieldSortsI_datF (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) (F : Nat) :
    ∀ j : Nat,
      (checkStructFieldSortsI (fueledOpsM mode) env isProp large s nP fvs idxArgs
          j).val F =
        checkStructFieldSortsI (fueledOps mode F) env isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    unfold checkStructFieldSortsI
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_inferType_atF, fueledOpsM_ensureSort_atF,
      liftFueled_atF, unwrapOr_atF,
      checkStructFieldSortsI_datF env isProp large s nP fvs idxArgs F j]

/-! ### The positivity function (`nestPos`) at fuel `F` -/

section NestPos

open ConLeche (NestCtx NestKey NestHole NestState NestFieldKind nestInstType nestGrowGroup
  nestGroupCtors nestFields nestCtors nestFrame nestCont nestPos nestRoot nestUniform
  nestedBlockPositivity nestContainer)

theorem reducedFormer_datF (env : Env) (cv : ConstantVal) (n F : Nat) :
    (reducedFormer (fueledOpsM mode) env cv n).val F =
      reducedFormer (fueledOps mode F) env cv n := by
  unfold reducedFormer
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    whnfTelescope_datF]

theorem familyTelescope_datF (env : Env) (cv : ConstantVal) (caps : IndCaps) (F : Nat) :
    (familyTelescope (fueledOpsM mode) env cv caps).val F =
      familyTelescope (fueledOps mode F) env cv caps := by
  unfold familyTelescope
  split
  · simp only [FueledM.atF_bind, FueledM.atF_pure, reducedFormer_datF]
  · rfl

theorem checkSpineAt_datF (env : Env) (d F : Nat) :
    ∀ (ds : List Expr) (T : Expr), (checkSpineAt (fueledOpsM mode) env d T ds).val F =
      checkSpineAt (fueledOps mode F) env d T ds
  | [], _ => rfl
  | a :: as, T => by
    unfold checkSpineAt
    split
    · simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
        fueledOpsM_inferType_atF, fueledOpsM_isDefEq_atF, checkSpineAt_datF env d F as]
    · rfl

theorem familyKeyCheck_datF (env : Env) (find? : Name → Option ConstantInfo) (d : Nat) (c : Name)
    (us : List Level) (ds : List Expr) (F : Nat) :
    (familyKeyCheck (fueledOpsM mode) env find? d c us ds).val F =
      familyKeyCheck (fueledOps mode F) env find? d c us ds := by
  unfold familyKeyCheck
  split
  · simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      familyTelescope_datF, checkSpineAt_datF]
  · rfl

theorem nestInstType_datF (ctx : NestCtx) (env : Env) (hi : Nat) (key : NestKey) (F : Nat) :
    (nestInstType ctx (fueledOpsM mode) env hi key).val F =
      nestInstType ctx (fueledOps mode F) env hi key := by
  unfold nestInstType
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite, unwrapOr_atF,
    liftFueled_atF, familyTelescope_datF]

theorem nestGrowGroup_datF (ctx : NestCtx) (env : Env) (hi : Nat) (us : List Level)
    (ds : List Expr) (F : Nat) :
    ∀ (cs : List Name) (grp : List (Name × Expr)),
      (nestGrowGroup ctx (fueledOpsM mode) env hi us ds cs grp).val F
        = nestGrowGroup ctx (fueledOps mode F) env hi us ds cs grp
  | [], _ => rfl
  | c :: cs, grp => by
    unfold nestGrowGroup
    simp only [FueledM.atF_bind, nestInstType_datF]
    congr 1
    funext q
    exact nestGrowGroup_datF ctx env hi us ds F cs _

theorem nestGroupCtors_datF (ctx : NestCtx) (nPc : Nat) (F : Nat) :
    ∀ (cs : List Name),
      (nestGroupCtors (m := FueledM) ctx nPc cs).val F = nestGroupCtors (m := CheckM) ctx nPc cs
  | [] => rfl
  | c :: cs => by
    unfold nestGroupCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF, nestGroupCtors_datF ctx nPc F cs]

variable {rec : List NestHole → Nat → Nat → Expr → NestState →
    FueledM (NestFieldKind × Expr × NestState)}
  {rec' : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}

theorem nestFields_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (prog : List NestHole) (base : Nat) (err : CheckError) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState),
      (nestFields rec prog base err nF j cur st).val F
        = nestFields rec' prog base err nF j cur st
  | 0, _, _, _ => rfl
  | nF + 1, j, cur, st => by
    unfold nestFields
    split
    · simp only [FueledM.atF_bind, hrec]
      congr 1
      funext q
      simp only [FueledM.atF_pure, FueledM.atF_bind,
        nestFields_datF hrec prog base err nF (j + 1)]
    · rfl

theorem nestCtors_datF {F : Nat}
    {recC : Expr → List NestHole → Nat → Nat → Expr → NestState →
      FueledM (NestFieldKind × Expr × NestState)}
    {recC' : Expr → List NestHole → Nat → Nat → Expr → NestState →
      CheckM (NestFieldKind × Expr × NestState)}
    (hrec : ∀ x a b c d e, (recC x a b c d e).val F = recC' x a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (names : List Name) (holes : List Expr) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState),
      (nestCtors ctx (fueledOpsM mode) env recC prog hi us ds names holes cs st).val F
        = nestCtors ctx (fueledOps mode F) env recC' prog hi us ds names holes cs st
  | [], _ => rfl
  | (cv, nF) :: cs, st => by
    unfold nestCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF, fueledOpsM_inferType_atF, fueledOpsM_ensureSort_atF,
      nestFields_datF (hrec _), nestCtors_datF hrec ctx env prog hi us ds names holes cs]

theorem nestFrame_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (nPc : Nat) (grp : List (Name × Expr)) (st : NestState) :
    (nestFrame ctx (fueledOpsM mode) env rec prog hi us ds nPc grp st).val F
      = nestFrame ctx (fueledOps mode F) env rec' prog hi us ds nPc grp st := by
  unfold nestFrame
  simp only [FueledM.atF_bind, FueledM.atF_pure, familyKeyCheck_datF, nestGroupCtors_datF]
  congr 1
  funext _
  congr 1
  funext q
  simp only [FueledM.atF_bind, FueledM.atF_pure, nestCtors_datF (fun _ => hrec)]

theorem nestContNew_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level)
    (ds : List Expr) (nPc : Nat) (cty : Expr) (st : NestState) :
    (ConLeche.nestContNew ctx (fueledOpsM mode) env rec prog kb n us ds nPc cty st).val F
      = ConLeche.nestContNew ctx (fueledOps mode F) env rec' prog kb n us ds nPc cty st := by
  unfold ConLeche.nestContNew
  simp only [FueledM.atF_bind, FueledM.atF_pure, nestGrowGroup_datF, nestFrame_datF hrec]

theorem nestContKey_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level)
    (ds : List Expr) (nPc : Nat) (cty : Expr) (st : NestState) :
    (ConLeche.nestContKey ctx (fueledOpsM mode) env rec prog kb n us ds nPc cty st).val F
      = ConLeche.nestContKey ctx (fueledOps mode F) env rec' prog kb n us ds nPc cty st := by
  unfold ConLeche.nestContKey
  split
  · simp only [FueledM.atF_throw]
  · split
    · rfl
    · exact nestContNew_datF hrec ctx env prog kb n us ds nPc cty st

theorem nestCont_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level)
    (args : List Expr) (st : NestState) :
    (nestCont ctx (fueledOpsM mode) env rec prog kb n us args st).val F
      = nestCont ctx (fueledOps mode F) env rec' prog kb n us args st := by
  unfold nestCont
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, nestContKey_datF hrec, nestInstType_datF]

end NestPos

theorem nestPos_datF (env : Env) (ctx : ConLeche.NestCtx) (F : Nat) :
    ∀ (fuel : Nat) (prog : List ConLeche.NestHole) (dep kb : Nat) (e : Expr)
      (st : ConLeche.NestState),
      (ConLeche.nestPos (fueledOpsM mode) env ctx fuel prog dep kb e st).val F
        = ConLeche.nestPos (fueledOps mode F) env ctx fuel prog dep kb e st := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ _ _ _ => rfl
  | succ fuel ih =>
    intro prog dep kb e st
    unfold ConLeche.nestPos
    simp only [FueledM.atF_bind, fueledOpsM_whnf_atF]
    congr 1
    funext w
    simp only [FueledM.atF_ite, FueledM.atF_pure]
    split
    · rfl
    · split
      · simp only [FueledM.atF_ite, FueledM.atF_throw, FueledM.atF_bind, FueledM.atF_pure, ih]
      · repeat' split
        all_goals (try simp only [FueledM.atF_ite, FueledM.atF_throw, FueledM.atF_bind,
          FueledM.atF_pure, nestCont_datF (rec := ConLeche.nestPos (fueledOpsM mode) env ctx fuel)
            (rec' := ConLeche.nestPos (fueledOps mode F) env ctx fuel) ih])
        all_goals (try rfl)

theorem nestRoot_datF (env : Env) (ctx : ConLeche.NestCtx) (holes : List Expr)
    (F : Nat) :
    ∀ (css : List (List (ConstantVal × Nat))) (st : ConLeche.NestState),
      (nestRoot (fueledOpsM mode) env ctx holes css st).val F
        = nestRoot (fueledOps mode F) env ctx holes css st
  | [], _ => rfl
  | cs :: css, st => by
    unfold nestRoot
    simp only [FueledM.atF_bind, FueledM.atF_pure,
      nestCtors_datF (fun x => nestPos_datF env ctx F (ConLeche.whnfWalkFuel x)),
      nestRoot_datF env ctx holes F css]

theorem nestUniform_datF (ctx : ConLeche.NestCtx)
    (ctorss : List (List (ConstantVal × Nat))) (F : Nat) :
    (nestUniform (m := FueledM) ctx ctorss).val F
      = nestUniform (m := CheckM) ctx ctorss := by
  unfold nestUniform
  split <;> simp only [FueledM.atF_throw, FueledM.atF_pure]

theorem checkSumCtor_datF (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (rs : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat)
    (cvTa : ConstantVal) (F : Nat) :
    (checkSumCtor (fueledOpsM mode) env₀ env T lps nP nIdx rs isProp large
      cvC nF cvTa).val F =
      checkSumCtor (fueledOps mode F) env₀ env T lps nP nIdx rs isProp large
        cvC nF cvTa := by
  unfold checkSumCtor
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, unwrapOr_atF, checkConstantVal_datF,
    checkStructFieldSortsI_datF, checkStructDomsAt_datF]

theorem checkSumCtors_datF (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (rs : Level) (isProp large : Bool) (cvTa : ConstantVal) (F : Nat) :
    ∀ cs : List (ConstantVal × Nat),
      (checkSumCtors (fueledOpsM mode) env₀ env T lps nP nIdx rs isProp large
        cvTa cs).val F =
        checkSumCtors (fueledOps mode F) env₀ env T lps nP nIdx rs isProp large
          cvTa cs
  | [] => rfl
  | c :: cs => by
    unfold checkSumCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkSumCtor_datF,
      checkSumCtors_datF env₀ env T lps nP nIdx rs isProp large cvTa F cs]

/-! ### The recursor conformance check's generator (#188) -/

/-! ### The uniform install at k members

Every stage of `checkBlock` at fuel `F`, read off the same program at
the two monads, at EVERY `k`. -/

theorem checkBlockTele_datF (env : Env) (nP : Nat) (ms : MemberShape) (F : Nat) :
    (checkBlockTele (fueledOpsM mode) env nP ms).val F =
      checkBlockTele (fueledOps mode F) env nP ms := by
  unfold checkBlockTele
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, checkConstantVal_datF, checkSumTele_datF]

theorem checkBlockTeles_datF (env : Env) (nP F : Nat) :
    ∀ mss : List MemberShape,
      (checkBlockTeles (fueledOpsM mode) env nP mss).val F =
        checkBlockTeles (fueledOps mode F) env nP mss
  | [] => rfl
  | ms :: rest => by
    unfold checkBlockTeles
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkBlockTele_datF,
      checkBlockTeles_datF env nP F rest]

theorem checkBlockDomsAt_datF (env : Env) (off : Nat) (fvs doms : List Expr) (F : Nat) :
    ∀ j : Nat,
      (checkBlockDomsAt (fueledOpsM mode) env off fvs doms j).val F =
        checkBlockDomsAt (fueledOps mode F) env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    unfold checkBlockDomsAt
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_isDefEq_atF, unwrapOr_atF,
      checkBlockDomsAt_datF env off fvs doms F j]

theorem checkBlockAgree_datF (env : Env) (nP : Nat) (cvTa0 : ConstantVal) (s0 : Level)
    (F : Nat) :
    ∀ cvs : List (ConstantVal × Level),
      (checkBlockAgree (fueledOpsM mode) env nP cvTa0 s0 cvs).val F =
        checkBlockAgree (fueledOps mode F) env nP cvTa0 s0 cvs
  | [] => rfl
  | (cvTa, s) :: rest => by
    unfold checkBlockAgree
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, unwrapOr_atF, checkBlockDomsAt_datF, liftFueled_atF,
      checkBlockAgree_datF env nP cvTa0 s0 F rest]

theorem checkBlockInds_datF (env : Env) (p : BlockShape) (isRec : Bool) (F : Nat) :
    (checkBlockInds (fueledOpsM mode) env p isRec).val F =
      checkBlockInds (fueledOps mode F) env p isRec := by
  unfold checkBlockInds
  split
  · rfl
  · simp only [FueledM.atF_bind, FueledM.atF_pure, checkBlockTele_datF,
      checkBlockTeles_datF, checkBlockAgree_datF]

theorem checkBlockCtors_datF (env₀ env : Env) (p : BlockShape)
    (F : Nat) :
    ∀ l : List MemberShape,
      (checkBlockCtors (fueledOpsM mode) env₀ env p l).val F =
        checkBlockCtors (fueledOps mode F) env₀ env p l
  | [] => rfl
  | ms :: rest => by
    unfold checkBlockCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkSumCtors_datF,
      checkBlockCtors_datF env₀ env p F rest]

theorem checkBlockIdxSorts_datF (env₁ : Env) (p : BlockShape) (F : Nat) :
    ∀ l : List MemberShape,
      (checkBlockIdxSorts (fueledOpsM mode) env₁ p l).val F =
        checkBlockIdxSorts (fueledOps mode F) env₁ p l
  | [] => rfl
  | ms :: rest => by
    unfold checkBlockIdxSorts
    simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF,
      checkStructFieldSortsI_datF, checkBlockIdxSorts_datF env₁ p F rest]

theorem FueledM.atF_mapConst {α : Type} (x : FueledM α) (F : Nat) :
    (Functor.mapConst PUnit.unit x : FueledM PUnit).val F
      = (Functor.mapConst PUnit.unit (x.val F) : CheckM PUnit) := by
  show (x >>= fun _ => pure PUnit.unit : FueledM PUnit).val F = _
  rw [FueledM.atF_bind]
  cases x.val F <;> rfl

/-! ### The recursor stage's class kit at fuel `F` -/

macro "tdatF_tac" : tactic =>
  `(tactic| repeat' (first
    | rfl
    | (simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
        unwrapOr_atF, fueledOpsM_isDefEq_atF, fueledOpsM_inferType_atF,
        fueledOpsM_ensureSort_atF, fueledOpsM_whnf_atF,
        liftFueled_atF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)))

theorem checkConstantValF_datF (fe : FEnv) (cv : ConstantVal) (F : Nat) {a : Bool} :
    (checkConstantValF (fueledOpsM mode) fe cv a).val F =
      checkConstantValF (fueledOps mode F) fe cv a := by
  unfold checkConstantValF
  datF_tac

theorem targetOutsideInst_datF (fe : FEnv) (I : Name) (us : List Level) (ds : List Expr)
    (F : Nat) :
    (targetOutsideInst (fueledOpsM mode) fe I us ds).val F =
      targetOutsideInst (fueledOps mode F) fe I us ds := by
  unfold targetOutsideInst
  split
  · rw [FueledM.atF_bind, familyTelescope_datF]
    congr 1
    funext tyI
    split
    · dsimp only; split; all_goals rfl
    · rfl
  · rfl

theorem targetParamsDefEq_datF (env : Env) (d : Nat) (absM : Expr → Expr) (pfvs : List Expr)
    (F : Nat) :
    ∀ (as bs : List Expr),
      (targetParamsDefEq (fueledOpsM mode) env d absM pfvs as bs).val F =
        targetParamsDefEq (fueledOps mode F) env d absM pfvs as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold targetParamsDefEq
    simp only [FueledM.atF_bind, FueledM.atF_pure, fueledOpsM_inferType_atF,
      fueledOpsM_isDefEq_atF, FueledM.atF_ite, targetParamsDefEq_datF env d absM pfvs F as bs]
    repeat' split <;> try rfl

theorem targetClassMatch_datF (env : Env) (p : BlockShape) (formerTys pfvs : List Expr)
    (us : List Level) (ds : List Expr) (lvls : List Level) (eds : List Expr) (F : Nat) :
    (targetClassMatch (fueledOpsM mode) env p formerTys pfvs us ds lvls eds).val F =
      targetClassMatch (fueledOps mode F) env p formerTys pfvs us ds lvls eds := by
  unfold targetClassMatch
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_ite, targetParamsDefEq_datF]

theorem targetMajorNfs_datF (env : Env) (p : BlockShape) (formerTys pfvs : List Expr)
    (us : List Level) (ds : List Expr) (ctors : List (ConstantVal × Nat)) (F : Nat) :
    ∀ (es : List NestCtorNf),
      (targetMajorNfs (fueledOpsM mode) env p formerTys pfvs us ds ctors es).val F =
        targetMajorNfs (fueledOps mode F) env p formerTys pfvs us ds ctors es
  | [] => rfl
  | e :: es => by
    unfold targetMajorNfs
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_ite, targetClassMatch_datF,
      targetMajorNfs_datF env p formerTys pfvs us ds ctors F es]

theorem targetMajorOf_datF (fe : FEnv) (p : BlockShape) (pfvs fvs : List Expr) (mty : Expr) (F : Nat) :
    (targetMajorOf (fueledOpsM mode) fe p pfvs fvs mty).val F =
      targetMajorOf (fueledOps mode F) fe p pfvs fvs mty := by
  unfold targetMajorOf
  repeat' (first
    | rfl
    | (simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
        unwrapOr_atF, liftFueled_atF, targetOutsideInst_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _))

theorem targetPinTys_datF (env : Env) (d : Nat) (F : Nat) :
    ∀ (xs : List Expr),
      (targetPinTys (fueledOpsM mode) env d xs).val F = targetPinTys (fueledOps mode F) env d xs
  | [] => rfl
  | x :: xs => by
    unfold targetPinTys
    simp only [FueledM.atF_bind, fueledOpsM_inferType_atF, targetPinTys_datF env d F xs]

theorem targetMajorPins_datF (fe : FEnv) (rP : Nat) (M : TargetMajor) (F : Nat) :
    (targetMajorPins (fueledOpsM mode) fe rP M).val F
      = targetMajorPins (fueledOps mode F) fe rP M := by
  unfold targetMajorPins
  split
  · simp only [FueledM.atF_bind, FueledM.atF_pure, familyKeyCheck_datF,
      targetPinTys_datF fe.env rP F M.ds]
  · rfl

theorem targetRecPins_datF (p : BlockShape) (block : List ConstantInfo) (F : Nat) :
    (targetRecPins (m := FueledM) p block).val F = targetRecPins (m := CheckM) p block := by
  unfold targetRecPins
  datF_tac

theorem targetK53_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (Mc : TargetMajor)
    (tele : List Expr) (majDom f : Expr) (F : Nat) :
    (targetK53 (fueledOpsM mode) env p formerTys Mc tele majDom f).val F =
      targetK53 (fueledOps mode F) env p formerTys Mc tele majDom f := by
  unfold targetK53
  repeat' split
  all_goals first | rfl | exact targetClassMatch_datF _ _ _ _ _ _ _ _ _

theorem checkBlockTables_datF (env : Env) (F : Nat) :
    ∀ Q : List ProjTable,
      (checkBlockTables (m := FueledM) env Q).val F = checkBlockTables (m := CheckM) env Q
  | [] => rfl
  | t :: rest => by
    unfold checkBlockTables
    rw [FueledM.atF_bind, checkStructProjTable_datF]
    congr 1
    funext _
    exact checkBlockTables_datF env F rest

theorem checkAbsCtorSorts_datF (env : Env) (ctx : ConLeche.NestCtx) (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (os : List (List NestFieldKind × Expr)),
      (checkAbsCtorSorts (fueledOpsM mode) env ctx cs os).val F
        = checkAbsCtorSorts (fueledOps mode F) env ctx cs os
  | [], _ => rfl
  | _ :: _, [] => rfl
  | c :: cs, o :: os => by
    unfold checkAbsCtorSorts
    simp only [FueledM.atF_bind, unwrapOr_atF, FueledM.atF_ite,
      FueledM.atF_throw, FueledM.atF_pure, checkStructFieldSortsI_datF,
      checkAbsCtorSorts_datF env ctx F cs os]

theorem checkAbsCtorSortsAll_datF (env : Env) (ctx : ConLeche.NestCtx) (F : Nat) :
    ∀ (css : List (List (ConstantVal × Nat))) (oss : List (List (List NestFieldKind × Expr))),
      (checkAbsCtorSortsAll (fueledOpsM mode) env ctx css oss).val F
        = checkAbsCtorSortsAll (fueledOps mode F) env ctx css oss
  | [], _ => rfl
  | _ :: _, [] => rfl
  | cs :: css, os :: oss => by
    unfold checkAbsCtorSortsAll
    simp only [FueledM.atF_bind, checkAbsCtorSorts_datF, checkAbsCtorSortsAll_datF env ctx F css oss]

theorem nestSeeds_datF (env : Env) (ctx : ConLeche.NestCtx) (F : Nat) :
    ∀ (ks : List (ConLeche.NestKey × Nat)) (st : ConLeche.NestState),
      (ConLeche.nestSeeds (fueledOpsM mode) env ctx ks st).val F
        = ConLeche.nestSeeds (fueledOps mode F) env ctx ks st
  | [], _ => rfl
  | (key, nPc) :: ks, st => by
    unfold ConLeche.nestSeeds
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      ConLeche.nestInstType_datF,
      nestContKey_datF (rec := ConLeche.nestPos (fueledOpsM mode) env ctx _)
        (rec' := ConLeche.nestPos (fueledOps mode F) env ctx _) (nestPos_datF env ctx F _),
      nestSeeds_datF env ctx F ks]

theorem blockNestCtx_datF (p : BlockShape)
    (find? : Name → Option ConstantInfo) (F : Nat) :
    (blockNestCtx (m := FueledM) p find?).val F =
      blockNestCtx (m := CheckM) p find? := by
  unfold blockNestCtx
  simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF]

/-! ### The generated recursor stage at fuel `F` -/

theorem classMinorSlot_datF (rd : ClassRead) (c : Nat) (C : Name) (F : Nat) :
    (classMinorSlot (m := FueledM) rd c C).val F = classMinorSlot (m := CheckM) rd c C := by
  unfold classMinorSlot
  dsimp only
  split <;> rfl

theorem classFieldsOf_datF (p : BlockShape) (ctor : Name) (ihs : List (Nat × Nat)) (F : Nat) :
    ∀ (i : Nat) (fs : List Expr),
      (classFieldsOf (m := FueledM) p ctor ihs i fs).val F =
        classFieldsOf (m := CheckM) p ctor ihs i fs
  | _, [] => rfl
  | i, f :: fs => by
    unfold classFieldsOf
    dsimp only
    split <;>
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      classFieldsOf_datF p ctor ihs F (i + 1) fs] <;> rfl

theorem classNodesAgree_datF (env : Env) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List Expr) (leaf : Expr) (fvs : List Expr)
    (i : Nat) (ctor : Name) (F : Nat) :
    ∀ (es : List NestCtorNf),
      (classNodesAgree (fueledOpsM mode) env p formerTys Mc tele leaf fvs i ctor es).val F =
        classNodesAgree (fueledOps mode F) env p formerTys Mc tele leaf fvs i ctor es
  | [] => rfl
  | e :: es => by
    unfold classNodesAgree
    split
    · simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
        targetK53_datF, classNodesAgree_datF env p formerTys Mc tele leaf fvs i ctor F es]
    · rfl

theorem classFieldsAgree_datF (env : Env) (p : BlockShape) (formerTys : List Expr)
    (Ms : List TargetMajor) (fvs : List Expr) (ctor : Name) (E : List NestCtorNf) (F : Nat) :
    ∀ (i : Nat) (ks : List ClassField),
      (classFieldsAgree (fueledOpsM mode) env p formerTys Ms fvs ctor E i ks).val F =
        classFieldsAgree (fueledOps mode F) env p formerTys Ms fvs ctor E i ks
  | _, [] => rfl
  | i, .ordinary :: ks => by
    unfold classFieldsAgree
    exact classFieldsAgree_datF env p formerTys Ms fvs ctor E F (i + 1) ks
  | i, .recursive t tele :: ks => by
    unfold classFieldsAgree
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF, classNodesAgree_datF,
      classFieldsAgree_datF env p formerTys Ms fvs ctor E F (i + 1) ks]

theorem classCtorOf_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (rd : ClassRead)
    (Ms : List TargetMajor) (c : Nat) (ctor : ConstantVal × Nat) (F : Nat) :
    (classCtorOf (fueledOpsM mode) env p formerTys rd Ms c ctor).val F =
      classCtorOf (fueledOps mode F) env p formerTys rd Ms c ctor := by
  unfold classCtorOf
  simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF, classMinorSlot_datF,
    classFieldsOf_datF, classFieldsAgree_datF]

theorem classCtorsOf_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (rd : ClassRead)
    (Ms : List TargetMajor) (c : Nat) (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)),
      (classCtorsOf (fueledOpsM mode) env p formerTys rd Ms c cs).val F =
        classCtorsOf (fueledOps mode F) env p formerTys rd Ms c cs
  | [] => rfl
  | ctor :: cs => by
    unfold classCtorsOf
    simp only [FueledM.atF_bind, FueledM.atF_pure, classCtorOf_datF,
      classCtorsOf_datF env p formerTys rd Ms c F cs]

theorem classesCtors_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (rd : ClassRead)
    (Ms : List TargetMajor) (F : Nat) :
    ∀ (c : Nat) (l : List TargetMajor),
      (classesCtors (fueledOpsM mode) env p formerTys rd Ms c l).val F =
        classesCtors (fueledOps mode F) env p formerTys rd Ms c l
  | _, [] => rfl
  | c, M :: rest => by
    unfold classesCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, classCtorsOf_datF,
      classesCtors_datF env p formerTys rd Ms F (c + 1) rest]

theorem classMajors_datF (fe : FEnv) (p : BlockShape) (pfvs : List Expr) (F : Nat) :
    ∀ (keys : List ClassKey),
      (classMajors (fueledOpsM mode) fe p pfvs keys).val F =
        classMajors (fueledOps mode F) fe p pfvs keys
  | [] => rfl
  | key :: keys => by
    unfold classMajors
    simp only [FueledM.atF_bind, FueledM.atF_pure, targetMajorOf_datF, targetMajorPins_datF,
      classMajors_datF fe p pfvs F keys]

theorem classesNfs_datF (env : Env) (p : BlockShape) (formerTys : List Expr)
    (tbl : List NestCtorNf) (F : Nat) :
    ∀ (Ms : List TargetMajor),
      (classesNfs (fueledOpsM mode) env p formerTys tbl Ms).val F =
        classesNfs (fueledOps mode F) env p formerTys tbl Ms
  | [] => rfl
  | M :: Ms => by
    unfold classesNfs
    simp only [FueledM.atF_bind, FueledM.atF_pure, targetMajorNfs_datF,
      classesNfs_datF env p formerTys tbl F Ms]

theorem classFormerTy_datF (fe : FEnv) (formers : List ConstantVal) (M : TargetMajor) (F : Nat) :
    (classFormerTy (fueledOpsM mode) fe formers M).val F =
      classFormerTy (fueledOps mode F) fe formers M := by
  unfold classFormerTy
  repeat' split
  all_goals first
    | rfl
    | simp only [FueledM.atF_bind, FueledM.atF_pure, familyTelescope_datF]

theorem mapMLoop_atF {α β : Type} (f : α → FueledM β) (F : Nat) :
    ∀ (l : List α) (bs : List β),
      (List.mapM.loop f l bs).val F = List.mapM.loop (fun a => (f a).val F) l bs
  | [], _ => rfl
  | a :: l, bs => by
    simp only [List.mapM.loop, FueledM.atF_bind, mapMLoop_atF f F l]

theorem mapM_atF {α β : Type} (f : α → FueledM β) (F : Nat) (l : List α) :
    (l.mapM f).val F = l.mapM (fun a => (f a).val F) :=
  mapMLoop_atF f F l []

theorem classFormerTys_datF (fe : FEnv) (formers : List ConstantVal) (F : Nat)
    (Ms : List TargetMajor) :
    (Ms.mapM (classFormerTy (fueledOpsM mode) fe formers)).val F =
      Ms.mapM (classFormerTy (fueledOps mode F) fe formers) := by
  rw [mapM_atF]
  simp only [classFormerTy_datF]

theorem classKeyOf_datF (nP : Nat) (params : List Expr) (k : ClassKey)
    (F : Nat) :
    (classKeyOf (m := FueledM) nP params k).val F =
      classKeyOf (m := CheckM) nP params k := by
  unfold classKeyOf
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite, mapM_atF]

theorem checkBlockClasses_datF (fe₁ : FEnv) (p : BlockShape) (params : List Expr) (F : Nat) :
    (checkBlockClasses (fueledOpsM mode) fe₁ p params).val F =
      checkBlockClasses (fueledOps mode F) fe₁ p params := by
  unfold checkBlockClasses
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, mapM_atF, classKeyOf_datF, classMajors_datF]

theorem classConstOk_datF (fe : FEnv) (cv : ConstantVal) (F : Nat) :
    (classConstOk (fueledOpsM mode) fe cv).val F = classConstOk (fueledOps mode F) fe cv := by
  unfold classConstOk
  datF_tac

theorem classRecTyCheck_datF (fe : FEnv) (cvRi cvG : ConstantVal) (F : Nat) :
    (classRecTyCheck (fueledOpsM mode) fe cvRi cvG).val F =
      classRecTyCheck (fueledOps mode F) fe cvRi cvG := by
  unfold classRecTyCheck
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    classConstOk_datF, fueledOpsM_isDefEq_atF]

theorem classRecTyOk_datF (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (cvRi : ConstantVal) (c : Nat) (F : Nat) :
    (classRecTyOk (fueledOpsM mode) fe g k rc cvRi c).val F =
      classRecTyOk (fueledOps mode F) fe g k rc cvRi c := by
  unfold classRecTyOk
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, classRecTyCheck_datF]

theorem classRecTysOk_datF (fe : FEnv) (g : ClassGen) (k : Nat) (F : Nat) :
    ∀ (recs : List RecShape) (cvs : List ConstantVal) (cls : List Nat),
      (classRecTysOk (fueledOpsM mode) fe g k recs cvs cls).val F =
        classRecTysOk (fueledOps mode F) fe g k recs cvs cls
  | rc :: rcs, cvRi :: cvs, c :: cs => by
    unfold classRecTysOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, classRecTyOk_datF,
      classRecTysOk_datF fe g k F rcs cvs cs]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl

theorem classRuleCheck_datF (feT feR : FEnv) (cvR : ConstantVal) (n : Nat)
    (gen : Expr) (F : Nat) :
    (classRuleCheck (fueledOpsM mode) feT feR cvR n gen).val F =
      classRuleCheck (fueledOps mode F) feT feR cvR n gen := by
  unfold classRuleCheck
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, fueledOpsM_inferType_atF]

theorem classRuleOk_datF (feT feR : FEnv) (cvR : ConstantVal) (n : Nat)
    (gen : Expr) (F : Nat) :
    (classRuleOk (fueledOpsM mode) feT feR cvR n gen).val F =
      classRuleOk (fueledOps mode F) feT feR cvR n gen := by
  unfold classRuleOk
  simp only [FueledM.atF_bind, FueledM.atF_pure, classRuleCheck_datF]

theorem classRulesOk_datF (feT feR : FEnv) (g : ClassGen) (recOf : Nat → Option Name)
    (cvR : ConstantVal) (c : Nat) (F : Nat) :
    ∀ (xs : List ClassCtor),
      (classRulesOk (fueledOpsM mode) feT feR g recOf cvR c xs).val F =
        classRulesOk (fueledOps mode F) feT feR g recOf cvR c xs
  | [] => rfl
  | x :: xs => by
    unfold classRulesOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF, classRuleOk_datF,
      classRulesOk_datF feT feR g recOf cvR c F xs]

theorem classRecsRulesOk_datF (feT feR : FEnv) (g : ClassGen) (recOf : Nat → Option Name)
    (F : Nat) :
    ∀ (cvs : List ConstantVal) (cs : List Nat),
      (classRecsRulesOk (fueledOpsM mode) feT feR g recOf cvs cs).val F =
        classRecsRulesOk (fueledOps mode F) feT feR g recOf cvs cs
  | cvG :: cvs, c :: cs => by
    unfold classRecsRulesOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, classRulesOk_datF,
      classRecsRulesOk_datF feT feR g recOf F cvs cs]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem classStreamRecs_datF (fe : FEnv) (F : Nat) :
    ∀ (recs : List RecShape),
      (classStreamRecs (fueledOpsM mode) fe recs).val F = classStreamRecs (fueledOps mode F) fe recs
  | [] => rfl
  | rc :: rcs => by
    unfold classStreamRecs
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkConstantValF_datF,
      classStreamRecs_datF fe F rcs]

/-- **The generated recursor stage at fuel `F`**: the pure install's run
(`ShadowOps.ofOps` at the fueled family) is the model's fueled run. -/
theorem genRecCheck_datF (fe : FEnv) (p : BlockShape) (nestedBit : Bool) (params : List Expr)
    (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor)
    (block : List ConstantInfo) (F : Nat) :
    (genRecCheck (ShadowOps.ofOps (fueledOpsM mode)) fe p nestedBit params tbl rd Ms
        block).val F =
      genRecCheck (ShadowOps.fueled mode F) fe p nestedBit params tbl rd Ms block := by
  unfold genRecCheck
  simp only [ShadowOps.ofOps, ShadowOps.fueled, FueledM.atF_bind, FueledM.atF_pure,
    FueledM.atF_throw, FueledM.atF_ite, unwrapOr_atF, targetRecPins_datF, classStreamRecs_datF,
    classesNfs_datF, classesCtors_datF, classFormerTys_datF, classRecTysOk_datF,
    classRecsRulesOk_datF]

theorem checkBlockRec_datF (env : Env) (p : BlockShape) (nested : Bool) (params : List Expr)
    (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor) (block : List ConstantInfo) (F : Nat) :
    (checkBlockRec (fueledOpsM mode) env p nested params tbl rd Ms block).val F =
      checkBlockRec (fueledOps mode F) env p nested params tbl rd Ms block := by
  unfold checkBlockRec
  exact genRecCheck_datF _ _ _ _ _ _ _ _ F

theorem checkBlockPositivity_datF (env₁ : Env) (find? : Name → Option ConstantInfo)
    (p : BlockShape) (F : Nat) :
    (checkBlockPositivity (fueledOpsM mode) env₁ find? p).val F
      = checkBlockPositivity (fueledOps mode F) env₁ find? p := by
  unfold checkBlockPositivity
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    blockNestCtx_datF, nestUniform_datF, nestRoot_datF, checkAbsCtorSortsAll_datF]

theorem checkBlockPass_datF (env : Env) (p : BlockShape) (isRec : Bool) (F : Nat) :
    (checkBlockPass (fueledOpsM mode) env p isRec).val F =
      checkBlockPass (fueledOps mode F) env p isRec := by
  unfold checkBlockPass
  simp only [FueledM.atF_bind, FueledM.atF_pure, checkBlockInds_datF, checkBlockCtors_datF,
    blockNestCtx_datF, checkBlockClasses_datF, checkBlockPositivity_datF, nestSeeds_datF,
    unwrapOr_atF]

theorem recDomsAt_datF (env : Env) (rec : Name) (sfvs gfvs : List Expr) (F : Nat) :
    ∀ (j k : Nat),
      (recDomsAt (fueledOpsM mode) env rec sfvs gfvs j k).val F =
        recDomsAt (fueledOps mode F) env rec sfvs gfvs j k
  | _, 0 => rfl
  | j, k + 1 => by
    unfold recDomsAt
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF, fueledOpsM_isDefEq_atF, recDomsAt_datF env rec sfvs gfvs F (j + 1) k]

theorem recTyOpened_datF (env : Env) (rec : Name) (n : Nat) (F : Nat) :
    ∀ (os og : Option (List Expr × Expr)),
      (recTyOpened (fueledOpsM mode) env rec n os og).val F =
        recTyOpened (fueledOps mode F) env rec n os og
  | some (_, _), some (_, _) => by
    simp only [recTyOpened, FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_isDefEq_atF, recDomsAt_datF]
  | none, _ => by simp only [recTyOpened, FueledM.atF_throw]
  | some (_, _), none => by simp only [recTyOpened, FueledM.atF_throw]

theorem recTyCheck_datF (fe : FEnv) (rec : Name) (lps : List Name) (n : Nat) (s g : Expr)
    (F : Nat) :
    (recTyCheck (fueledOpsM mode) fe rec lps n s g).val F =
      recTyCheck (fueledOps mode F) fe rec lps n s g := by
  unfold recTyCheck
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    fueledOpsM_inferType_atF, fueledOpsM_ensureSort_atF, recTyOpened_datF]

theorem ruleAgree_datF (fe : FEnv) (rec ctor : Name) (lps : List Name) (s g : Expr)
    (F : Nat) :
    (ruleAgree (fueledOpsM mode) fe rec ctor lps s g).val F =
      ruleAgree (fueledOps mode F) fe rec ctor lps s g := by
  unfold ruleAgree
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    fueledOpsM_inferType_atF, fueledOpsM_isDefEq_atF]

theorem streamRulesShape_datF (rec : Name) (F : Nat) :
    ∀ (rs : List RecRule) (cs : List (ConstantVal × Nat)),
      (streamRulesShape (m := FueledM) rec rs cs).val F = streamRulesShape (m := CheckM) rec rs cs
  | [], [] => rfl
  | r :: rs, c :: cs => by
    unfold streamRulesShape
    simp only [FueledM.atF_bind, FueledM.atF_throw, FueledM.atF_ite,
      streamRulesShape_datF rec F rs cs]
  | [], _ :: _ => by unfold streamRulesShape; simp only [FueledM.atF_throw]
  | _ :: _, [] => by unfold streamRulesShape; simp only [FueledM.atF_throw]

theorem streamRulesCheck_datF (fe : FEnv) (rec : Name) (lps : List Name) (F : Nat) :
    ∀ (rs : List RecRule) (gs : List Expr),
      (streamRulesCheck (fueledOpsM mode) fe rec lps rs gs).val F =
        streamRulesCheck (fueledOps mode F) fe rec lps rs gs
  | [], [] => by unfold streamRulesCheck; rfl
  | [], _ :: _ => by unfold streamRulesCheck; simp only [FueledM.atF_throw]
  | _ :: _, [] => by unfold streamRulesCheck; simp only [FueledM.atF_throw]
  | r :: rs, g :: gs => by
    unfold streamRulesCheck
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_ite, ruleAgree_datF,
      streamRulesCheck_datF fe rec lps F rs gs]

theorem streamRecCompare_datF (fe : FEnv) (rc : RecShape)
    (g : ConstantVal × TargetMajor × List Expr) (F : Nat) :
    (streamRecCompare (fueledOpsM mode) fe rc g).val F =
      streamRecCompare (fueledOps mode F) fe rc g := by
  unfold streamRecCompare
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_ite, recTyCheck_datF,
    streamRulesCheck_datF]

theorem streamRecCheck_datF (fe : FEnv) (rc : RecShape)
    (g : ConstantVal × TargetMajor × List Expr) (F : Nat) :
    (streamRecCheck (fueledOpsM mode) fe rc g).val F =
      streamRecCheck (fueledOps mode F) fe rc g := by
  unfold streamRecCheck
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    streamRulesShape_datF, streamRecCompare_datF]

theorem streamRecsCheck_datF (fe : FEnv) (F : Nat) :
    ∀ (recs : List RecShape) (out : List (ConstantVal × TargetMajor × List Expr)),
      (streamRecsCheck (fueledOpsM mode) fe recs out).val F =
        streamRecsCheck (fueledOps mode F) fe recs out
  | [], [] => rfl
  | rc :: rcs, g :: gs => by
    unfold streamRecsCheck
    simp only [FueledM.atF_bind, streamRecCheck_datF, streamRecsCheck_datF fe F rcs gs]
  | [], _ :: _ => by unfold streamRecsCheck; simp only [FueledM.atF_throw]
  | _ :: _, [] => by unfold streamRecsCheck; simp only [FueledM.atF_throw]

theorem streamKCheck_datF (p : BlockShape) (F : Nat) :
    ∀ (recs : List RecShape) (out : List (ConstantVal × TargetMajor × List Expr)),
      (streamKCheck (m := FueledM) p recs out).val F = streamKCheck (m := CheckM) p recs out
  | [], _ => rfl
  | _ :: _, [] => rfl
  | rc :: rcs, g :: gs => by
    unfold streamKCheck
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      streamKCheck_datF p F rcs gs]

theorem checkBlockTail_datF (block : List ConstantInfo) (q : BlockPass Env)
    (Q : List ProjTable) (F : Nat) :
    (checkBlockTail (fueledOpsM mode) block q Q).val F =
      checkBlockTail (fueledOps mode F) block q Q := by
  unfold checkBlockTail
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    checkBlockIdxSorts_datF, checkBlockRec_datF, streamKCheck_datF, streamRecsCheck_datF,
    checkBlockTables_datF]


theorem reduceMember_datF (env : Env) (nP : Nat) (ms : MemberShape) (F : Nat) :
    (reduceMember (fueledOpsM mode) env ms nP).val F =
      reduceMember (fueledOps mode F) env ms nP := by
  unfold reduceMember
  split
  · simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      checkConstantVal_datF, reducedFormer_datF, fueledOpsM_isDefEq_atF]
  · rfl

theorem reduceMembers_datF (env : Env) (nP F : Nat) :
    ∀ l : List MemberShape, (reduceMembers (fueledOpsM mode) env nP l).val F =
      reduceMembers (fueledOps mode F) env nP l
  | [] => rfl
  | ms :: rest => by
    unfold reduceMembers
    simp only [FueledM.atF_bind, FueledM.atF_pure, reduceMember_datF, reduceMembers_datF env nP F rest]

/-- **The uniform install at fuel `F`, at k members**: the same program
at the two monads, stage by stage. -/
theorem checkBlock_datF (env : Env) (block : List ConstantInfo) (p : BlockShape)
    (F : Nat) :
    (checkBlock (fueledOpsM mode) env block p).val F =
      checkBlock (fueledOps mode F) env block p := by
  unfold checkBlock
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    checkBlockPass_datF, checkBlockTail_datF, reduceMembers_datF, unwrapOr_atF]

theorem checkDefnVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (hint : ReducibilityHint) (F : Nat) :
    (checkDefnVal (fueledOpsM mode) env cv value hint).val F =
      checkDefnVal (fueledOps mode F) env cv value hint := by
  unfold checkDefnVal
  datF_tac

theorem checkThmVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (F : Nat) :
    (checkThmVal (fueledOpsM mode) env cv value).val F =
      checkThmVal (fueledOps mode F) env cv value := by
  unfold checkThmVal
  datF_tac

theorem checkOpaqueVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (F : Nat) :
    (checkOpaqueVal (fueledOpsM mode) env cv value).val F =
      checkOpaqueVal (fueledOps mode F) env cv value := by
  unfold checkOpaqueVal
  datF_tac

theorem certifyNatEqs_datF (env : Env) (F : Nat) :
    ∀ eqs : List (Expr × Expr),
      (certifyNatEqs (fueledOpsM mode) env eqs).val F =
        certifyNatEqs (fueledOps mode F) env eqs
  | [] => rfl
  | eq :: rest => by
    show ((do
        if ← CheckerOps.isDefEq (fueledOpsM mode) env 2 eq.1 eq.2 then
          certifyNatEqs (fueledOpsM mode) env rest
        else pure false : FueledM _)).val F = _
    rw [FueledM.atF_bind]
    show _ = (do
        if ← CheckerOps.isDefEq (fueledOps mode F) env 2 eq.1 eq.2 then
          certifyNatEqs (fueledOps mode F) env rest
        else pure false : CheckM _)
    congr 1
    funext b
    cases b with
    | true => exact certifyNatEqs_datF env F rest
    | false => rfl

theorem checkDivModCerts_datF (env : Env) (c : Name) (annVal : Expr)
    (F : Nat) :
    ∀ (stmts : List (List Expr × Expr)) (proofs : List Expr),
      (checkDivModCerts (fueledOpsM mode) env c annVal stmts proofs).val F =
        checkDivModCerts (fueledOps mode F) env c annVal stmts proofs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    simp only [checkDivModCerts]
    split
    · rw [FueledM.atF_bind]
      congr 1
      funext tp
      rw [FueledM.atF_bind]
      congr 1
      funext b
      cases b with
      | true => exact checkDivModCerts_datF env c annVal F srest prest
      | false => rfl
    · rfl

theorem checkTypePins_datF (env : Env) (F : Nat) :
    ∀ (tps : List (Name × Expr)),
      (checkTypePins (fueledOpsM mode) env tps).val F =
        checkTypePins (fueledOps mode F) env tps
  | [] => rfl
  | p :: rest => by
    simp only [checkTypePins]
    rw [FueledM.atF_bind]
    congr 1
    funext b
    cases b with
    | true => exact checkTypePins_datF env F rest
    | false => rfl

theorem checkDivModPinAt_datF (env : Env) (c : Name) (value' : Expr)
    (ps : NatOpPinSet) (F : Nat) :
    (checkDivModPinAt (fueledOpsM mode) env c value' ps).val F =
      checkDivModPinAt (fueledOps mode F) env c value' ps := by
  unfold checkDivModPinAt
  repeat (first
    | (rw [checkTypePins_datF])
    | (rw [checkDivModCerts_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [FueledM.atF_pure, FueledM.atF_throw]))

theorem checkDivModPinLoop_datF (env : Env) (c : Name) (value' : Expr)
    (F : Nat) :
    ∀ (pss : List NatOpPinSet) (tried : List String),
      (checkDivModPinLoop (fueledOpsM mode) env c value' pss tried).val F =
        checkDivModPinLoop (fueledOps mode F) env c value' pss tried
  | [], _ => rfl
  | ps :: rest, tried => by
    unfold checkDivModPinLoop
    split
    · rw [FueledM.atF_bind, checkDivModPinAt_datF]
      congr 1
      funext b
      cases b with
      | true => rfl
      | false => exact checkDivModPinLoop_datF env c value' F rest _
    · exact checkDivModPinLoop_datF env c value' F rest _

theorem checkDivModPin_datF (env env2 : Env) (c : Name) (F : Nat) :
    (checkDivModPin (fueledOpsM mode) pins env env2 c).val F =
      checkDivModPin (fueledOps mode F) pins env env2 c := by
  unfold checkDivModPin
  repeat (first
    | (rw [checkDivModPinLoop_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [FueledM.atF_pure, FueledM.atF_throw]))

theorem checkReducePin_datF (env env2 : Env) (c : Name) (value : Expr)
    (F : Nat) :
    (checkReducePin (fueledOpsM mode) env env2 c value).val F =
      checkReducePin (fueledOps mode F) env env2 c value := by
  unfold checkReducePin
  repeat (first
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [FueledM.atF_pure, FueledM.atF_throw]))

/-- A quotient record's check and install at a fuel datum. -/
theorem checkQuotRecord_datF (env : Env) (k : QuotKind) (cv : ConstantVal) (F : Nat) :
    (checkQuotRecord (m := FueledM) env k cv).val F =
      checkQuotRecord (m := CheckM) env k cv := by
  unfold checkQuotRecord
  by_cases h : quotPinHit k cv = true
  · rw [ite_eq_left h, ite_eq_left h]
    by_cases h2 : quotPredsOk env.find? k = true
    · rw [ite_eq_left h2, ite_eq_left h2]
      exact installBasisDecl_datF _ _ _
    · rw [ite_eq_right h2, ite_eq_right h2, FueledM.atF_bind]
      simp only [FueledM.atF_throw]
      rfl
  · rw [ite_eq_right h, ite_eq_right h, FueledM.atF_bind]
    simp only [FueledM.atF_throw]
    rfl


theorem checkDeclKind_datF (env : Env) (d : Declaration) (F : Nat) :
    (checkDeclKind (fueledOpsM mode) pins env d).val F =
      checkDeclKind (fueledOps mode F) pins env d := by
  unfold checkDeclKind
  cases d with
  | defnDecl cv value hint =>
    dsimp only
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [FueledM.atF_bind, checkDefnVal_datF]
    congr 1
    funext env2
    repeat (first
      | (rw [certifyNatEqs_datF])
      | (rw [checkDivModPin_datF])
      | split
      | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [FueledM.atF_pure, FueledM.atF_throw]))
  | thmDecl cv value =>
    show ((checkConstantVal (fueledOpsM mode) env cv >>= fun _ =>
      checkThmVal (fueledOpsM mode) env cv value : FueledM _)).val F = _
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [checkThmVal_datF]
  | opaqueDecl cv value =>
    dsimp only
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [FueledM.atF_bind, checkOpaqueVal_datF]
    congr 1
    funext env2
    repeat (first
      | (rw [checkReducePin_datF])
      | split
      | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [FueledM.atF_pure, FueledM.atF_throw]))
  | axiomDecl cv =>
    dsimp only
    by_cases hqs : cv.name = quotSoundName
    · rw [ite_eq_left hqs, ite_eq_left hqs]
      exact checkQuotRecord_datF env .sound cv F
    · rw [ite_eq_right hqs, ite_eq_right hqs]
      rw [FueledM.atF_bind, checkConstantVal_datF]
      congr 1
      funext cv
      simp only [FueledM.atF_ite, FueledM.atF_pure, FueledM.atF_throw]
  | quotDecl k cv => exact checkQuotRecord_datF env k cv F
  | indDecl block nP =>
    dsimp only
    -- the declared parameter count (task #228) is a pure guard: the two
    -- sides take the same branch, and the guard's `throw` is fuel-free
    split
    · split
      · exact checkBlock_datF env block _ F
      · rfl
    · rfl

theorem checkDecl_datF (env : Env) (d : Declaration) (F : Nat) :
    (checkDecl mode (fueledOpsM mode) pins env d).val F =
      checkDecl mode (fueledOps mode F) pins env d := by
  unfold checkDecl
  rw [FueledM.atF_bind, checkDeclKind_datF]
  congr 1
  funext env₂
  simp only [FueledM.atF_bind, FueledM.atF_ite, FueledM.atF_pure, FueledM.atF_throw]

/-- **A declaration's check, inverted**: its own checks, then the reserved names'. -/
theorem checkDecl_inv {ops : CheckerOps CheckM} {pins : List NatOpPinSet} {env env₂ : Env}
    {d : Declaration} (h : checkDecl mode ops pins env d = .ok env₂) :
    checkDeclKind ops pins env d = .ok env₂ ∧ basisNamesOk d = true := by
  simp only [checkDecl, Bind.bind, Except.bind] at h
  cases hk : checkDeclKind ops pins env d with
  | error e => rw [hk] at h; exact nomatch h
  | ok env₁ =>
    rw [hk] at h
    by_cases hb : basisNamesOk d = true
    · simp only [hb, ↓reduceIte, Pure.pure, Except.pure,
        Except.ok.injEq] at h
      exact ⟨by rw [h], hb⟩
    · simp [hb, throw, throwThe, MonadExceptOf.throw] at h

/-- **A declaration's check from its parts**: its own checks, then the reserved names'. -/
theorem checkDecl_of_kind {ops : CheckerOps CheckM} {env env₂ : Env} {d : Declaration}
    (h : checkDeclKind ops pins env d = .ok env₂) (hb : basisNamesOk d = true) :
    checkDecl mode ops pins env d = .ok env₂ := by
  simp only [checkDecl, Bind.bind, Except.bind, h, hb]
  rfl

end ConLeche
