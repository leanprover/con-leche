module

public import ConLeche.Kernel.Inductives.BlockTail
public import ConLeche.Verify.Inductives.HookOuts
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.ExceptBind

public section

/-!
# The TARGET recursor check's RUN RECORDS

ONE inversion per stage of the classification-free recursor check
(`ConLeche/Kernel/Inductives/RecCheck.lean`, `targetRecCheck`), each
returning a record with NAMED fields (the pattern of
`Verify/Inductives/BlockRecRun.lean`).  Every proof about the recursor stage is to read
these records and never unfold a stage.

| stage | kernel function | record / inversion |
|---|---|---|
| the major | `targetMajorOf` | `TargetMajorRun` / `targetMajorOf_run` |
| the index domains | `targetIdxDoms` | `targetIdxDoms_member` |
| (b) one recursor's type | `targetRecTy` | `TargetTyEntry` / `targetRecTy_run` |
| (b) every recursor's type | `targetRecTys` | `targetRecTys_run` |
| (c) one call's typing (K.53 included) | `targetCallOk` | `TargetCallRun` / `targetCallOk_run` |
| (c) every call's typing | `targetCallsOk` | `targetCallsOk_run` |
| (c) the fields' abstract telescopes | `targetFieldNorms` | `targetFieldNorms_run` |
| (c) one rule | `targetRule` | `TargetRuleRun` / `targetRule_run` |
| (c) one recursor's rules | `targetRules` | `TargetRulesRun` / `targetRules_run` |
| (c) every recursor's rules | `targetRecsRules` | `targetRecsRules_run` |
| the whole check | `targetRecCheck` | `TargetRecRun` / `targetRecCheck_run` |

The records are stated at the fueled pure instantiation
(`ShadowOps.fueled mode F`).  `TargetMajorRun` has one constructor per
arm of `targetMajorOf`: `member`, and `outside` (a nested block's
container, the `none` branch of the member lookup).  Nothing else in
this file reads which arm the major took: the entry, the rule and the
call records are stated over the resolved `TargetMajor`.
-/

namespace ConLeche

variable {mode : CheckMode}

local syntax "close_throw" term : tactic
local macro_rules
  | `(tactic| close_throw $h:term) =>
    `(tactic| first
        | exact nomatch $h
        | exact absurd $h (by
            simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            exact fun hh => nomatch hh)
        | exact absurd $h
            (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-! ## The major -/

/-- **The major's resolution, as run**: the arm `targetMajorOf` took.
One constructor per arm: `member` and `outside` (a nested block's
containers). -/
inductive TargetMajorRun (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs fvs : List Expr) (mty : Expr) :
    TargetMajor → Type where
  /-- a MEMBER of the block, at the block's levels and parameters -/
  | member (I : Name) (t : Nat) (ms : MemberShape) (ctorsA : List (ConstantVal × Nat))
      (hfn : mty.getAppFn = .const I (p.lps.map .param))
      (ht : p.memberNames.findIdx? (· == I) = some t)
      (hms : p.members[t]? = some ms)
      (hctors : ctorsAs[t]? = some ctorsA)
      (hpar : mty.getAppArgs.take p.nP = fvs.take p.nP) :
      TargetMajorRun fe p ctorsAs pfvs fvs mty
        { ind := I, lvls := p.lps.map .param, ds := fvs.take p.nP, nPc := p.nP,
          nIdx := ms.nIdx, ctors := ctorsA, member := some t, pfvs := pfvs }
  /-- an OUTSIDE inductive (a nested block's container), at its own
  levels `us` and parameters `ds` (the major type's first `nPc`
  arguments, mentioning only the recursor's parameter binders), in the
  block's universe -/
  | outside (I : Name) (us : List Level) (nPc nIdx : Nat) (ctors : List (ConstantVal × Nat))
      (sI : Level)
      (hfn : mty.getAppFn = .const I us)
      (ht : p.memberNames.findIdx? (· == I) = none)
      (hnq : I ≠ quotName)
      (hctors : targetCtorsOf fe I = some (nPc, ctors))
      (hdsLen : (mty.getAppArgs.take nPc).length = nPc)
      (hdsSc : ∀ x ∈ mty.getAppArgs.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ p.nP)
      (hment : ∃ x ∈ mty.getAppArgs.take nPc, x.nestOcc p.memberNames 0 0 = true)
      (hinst : targetOutsideInst (m := CheckM) fe I us (mty.getAppArgs.take nPc)
        = .ok (nIdx, sI))
      (hsort : Level.isEquiv sI p.resSort = some true) :
      TargetMajorRun fe p ctorsAs pfvs fvs mty
        { ind := I, lvls := us, ds := mty.getAppArgs.take nPc, nPc := nPc, nIdx := nIdx,
          ctors := ctors, member := none, pfvs := pfvs }

/-- **`targetNodeTie`, inverted**: some recorded class names `I` and
matches. -/
theorem targetNodeTie_true {ops : CheckerOps CheckM} {env : Env} {p : BlockShape}
    {formerTys pfvs : List Expr} {I : Name} {us : List Level} {ds : List Expr} :
    ∀ {ks : List NestKey}, targetNodeTie ops env p formerTys pfvs I us ds ks = .ok true →
      ∃ k ∈ ks, k.cname = I ∧ targetClassMatch ops env p formerTys pfvs us ds k.lvls k.ds = .ok true
  | [], h => by simp [targetNodeTie, pure, Except.pure] at h
  | k :: ks, h => by
    unfold targetNodeTie at h
    split at h
    · rename_i hk
      obtain ⟨b, hb, h⟩ := exceptBind_ok h
      cases b
      · obtain ⟨k', hk', h1, h2⟩ := targetNodeTie_true h
        exact ⟨k', List.mem_cons_of_mem _ hk', h1, h2⟩
      · exact ⟨k, List.mem_cons_self, by simpa using hk, hb⟩
    · obtain ⟨k', hk', h1, h2⟩ := targetNodeTie_true h
      exact ⟨k', List.mem_cons_of_mem _ hk', h1, h2⟩

/-- **`targetMajorOf`, inverted**: the arm it took and the class's
parameter openers. -/
theorem targetMajorOf_run {fe : FEnv} {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs fvs : List Expr} {mty : Expr}
    {M : TargetMajor}
    (h : targetMajorOf (m := CheckM) fe p ctorsAs pfvs fvs mty = .ok M) :
    Nonempty (TargetMajorRun fe p ctorsAs pfvs fvs mty M) ∧ M.pfvs = pfvs := by
  unfold targetMajorOf at h
  simp only at h
  split at h
  · next I us hfn =>
    split at h
    · next t ht =>
      obtain ⟨ms, hms, h⟩ := exceptBind_ok h
      obtain ⟨ctorsA, hctorsA, h⟩ := exceptBind_ok h
      by_cases hc : (us == p.lps.map .param && mty.getAppArgs.take p.nP == fvs.take p.nP) = true
      case neg => rw [if_neg hc] at h; close_throw h
      rw [if_pos hc] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hpar⟩ := hc
      exact ⟨⟨.member I t ms ctorsA hfn ht (unwrapOr_ok hms) (unwrapOr_ok hctorsA) hpar⟩, rfl⟩
    · next ht =>
      split at h
      · close_throw h
      · next hq =>
        split at h
        · next nPc ctors hct =>
          split at h
          · next hds =>
            split at h
            case isFalse => close_throw h
            next hment =>
            obtain ⟨⟨nIdx, sI⟩, hinst, h⟩ := exceptBind_ok h
            obtain ⟨bq, hbq, h⟩ := exceptBind_ok h
            split at h
            · next hs =>
              have hs : sI.isEquiv p.resSort = some true := by
                unfold liftFueled at hbq
                split at hbq
                · next a ha =>
                  simp only [pure, Except.pure, Except.ok.injEq] at hbq
                  subst hbq; subst hs; exact ha
                · simp [throw, throwThe, MonadExceptOf.throw] at hbq
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
                at hds
              simp only [List.any_eq_true] at hment
              exact ⟨⟨.outside I us nPc nIdx ctors sI hfn ht (by simpa using hq) hct hds.1
                (fun x hx => by simpa using hds.2 x hx) hment hinst (by simpa using hs)⟩, rfl⟩
            · close_throw h
          · close_throw h
        · close_throw h
  · close_throw h

/-- **`targetIdxDoms` at a member**: the member's own index telescope,
opened at the recursor's numbering. -/
theorem targetIdxDoms_member {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal}
    {rP : Nat} {M : TargetMajor} {t : Nat} (hM : M.member = some t) {idoms : List Expr}
    (h : targetIdxDoms (m := CheckM) fe p cvTas rP M = .ok idoms) :
    ∃ cvTa tfs trest, cvTas[t]? = some cvTa ∧
      openPisParamsIdx p.nP M.nIdx rP cvTa.type = some (tfs, trest) ∧
      idoms = (tfs.drop p.nP).map Expr.fvarTypeD := by
  unfold targetIdxDoms at h
  rw [hM] at h
  simp only at h
  obtain ⟨cvTa, hcvTa, h⟩ := exceptBind_ok h
  obtain ⟨x, hx, h⟩ := exceptBind_ok h
  obtain ⟨tfs, trest⟩ := x
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨cvTa, tfs, trest, unwrapOr_ok hcvTa, unwrapOr_ok hx, h.symm⟩

/-! ## Stage (b): one recursor's TYPE -/

/-- **Stage (b) at ONE recursor**, every bind of `targetRecTy`'s body
named. -/
structure TargetTyEntry (mode : CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape)
    (nested : Bool) (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (rc : RecShape) (cvRi : ConstantVal) (M : TargetMajor) (u : Level) : Type where
  cvTP : ConstantVal
  fvs : List Expr
  concl : Expr
  tfvs : List Expr
  trest : Expr
  maj : Expr
  idoms : List Expr
  sty : Expr
  hcv : checkConstantValF (fueledOps mode F) fe rc.cvR = .ok cvRi
  /-- the prefix starts with the block's parameters -/
  hroom : p.nP ≤ rc.rP
  hle : rc.rP ≤ rc.mI
  hopen : openPisAtFvars (rc.mI + 1) cvRi.type 0 = some (fvs, concl)
  hmaj : fvs[rc.mI]? = some maj
  /-- THE MAJOR, resolved (a member, or — at `outside` — a container) -/
  major : TargetMajorRun fe p ctorsAs (fvs.take rc.rP) fvs maj.fvarTypeD M
  /-- (K7) a member major is the member the record names -/
  htgt : M.member.all (· == rc.tgt) = true
  /-- (K6) the major's former (a member's own) -/
  hcvTP : M.member.elim cvTas.head? (fun t => cvTas[t]?) = some cvTP
  hopenT : openPisAtFvars p.nP cvTP.type 0 = some (tfvs, trest)
  /-- the parameter domains, binder by binder, against the major's former's -/
  hparLen : (tfvs.map Expr.fvarTypeD).length = ((fvs.take p.nP).map Expr.fvarTypeD).length
  hparams : ∀ l, l < (tfvs.map Expr.fvarTypeD).length →
    isDefEqCore mode fe.env F p.nP ((tfvs.map Expr.fvarTypeD).getD l default)
      (((fvs.take p.nP).map Expr.fvarTypeD).getD l default) = .ok true
  hmI : rc.mI = rc.rP + M.nIdx
  hmajLen : maj.fvarTypeD.getAppArgs.length = M.nPc + M.nIdx
  hmajIdx : maj.fvarTypeD.getAppArgs.drop M.nPc = (fvs.drop rc.rP).take (rc.mI - rc.rP)
  hidoms : targetIdxDoms (m := CheckM) fe p cvTas rc.rP M = .ok idoms
  hidxLen : idoms.length = (((fvs.drop rc.rP).take (rc.mI - rc.rP)).map Expr.fvarTypeD).length
  hidx : ∀ l, l < idoms.length →
    isDefEqCore mode fe.env F rc.mI (idoms.getD l default)
      ((((fvs.drop rc.rP).take (rc.mI - rc.rP)).map Expr.fvarTypeD).getD l default) = .ok true
  hsty : inferTypeCore mode fe.env F (rc.mI + 1) concl = .ok sty
  hu : ensureSortCore mode fe.env F (rc.mI + 1) sty = .ok u
  /-- the elimination restriction's per-recursor half -/
  hsmall : blockLargeElimAllowed p nested = true ∨
    isDefEqCore mode fe.env F (rc.mI + 1) sty (.sort .zero) = .ok true
  /-- an outside major's parameters, typed at the rule prefix -/
  hpinTys : targetMajorPins (fueledOps mode F) fe.env rc.rP M = .ok ()

namespace TargetTyEntry

variable {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
  {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape} {cvRi : ConstantVal}
  {M : TargetMajor} {u : Level}


/-- **An OUTSIDE major**: the major type is the stored
inductive `M.ind` at the major's levels, not a member, not `Quot`; its
parameters are the major type's first `nPc` arguments, mentioning only
the recursor's parameter binders; its constructors and parameter count
are the environment's; its instantiated type former has `nIdx` indices
and ends in the block's universe. -/
theorem outside_of (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member = none) :
    ∃ sI, E.maj.fvarTypeD.getAppFn = .const M.ind M.lvls ∧
      p.memberNames.findIdx? (· == M.ind) = none ∧ M.ind ≠ quotName ∧
      targetCtorsOf fe M.ind = some (M.nPc, M.ctors) ∧
      M.ds = E.maj.fvarTypeD.getAppArgs.take M.nPc ∧ M.ds.length = M.nPc ∧
      (∀ x ∈ M.ds, x.bvarB = 0 ∧ x.fvarB ≤ p.nP) ∧
      targetOutsideInst (m := CheckM) fe M.ind M.lvls M.ds = .ok (M.nIdx, sI) ∧
      Level.isEquiv sI p.resSort = some true := by
  obtain ⟨_, _, _, _, _, _, maj, _, _, _, _, _, _, major, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _⟩ := E
  cases major with
  | member => exact nomatch hM
  | outside I us nPc nIdx ctors sI hfn ht hnq hct hl hsc _ hinst hs =>
    exact ⟨sI, hfn, ht, hnq, hct, rfl, hl, hsc, hinst, hs⟩

/-- **An OUTSIDE major names the block** (official's `is_nested`): some
parameter mentions a member. -/
theorem outside_ment (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member = none) : ∃ x ∈ M.ds, x.nestOcc p.memberNames 0 0 = true := by
  obtain ⟨_, _, _, _, _, _, maj, _, _, _, _, _, _, major, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _⟩ := E
  cases major with
  | member => exact nomatch hM
  | outside I us nPc nIdx ctors sI hfn ht hnq hct hl hsc hment hinst hs => exact hment

end TargetTyEntry

/-- **The parameter typing at an outside major, inverted**: every parameter
`D_i` of the major is typed at the rule
prefix, and so is the instantiation `I.{us} D⃗` — the `D⃗` satisfy the
container's parameter telescope there (official's `tc.check` of the
replaced nested application, `inductive.cpp` v4.33.0 :1223–1231). -/
theorem targetPinTys_run {env : Env} {d F : Nat} :
    ∀ {xs : List Expr}, targetPinTys (fueledOps mode F) env d xs = .ok () →
      ∀ x ∈ xs, ∃ ty, inferTypeCore mode env F d x = .ok ty
  | [], _, x, hx => nomatch hx
  | y :: ys, h, x, hx => by
    unfold targetPinTys at h
    obtain ⟨ty, hty, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨ty, hty⟩
    · exact targetPinTys_run h x hx

theorem targetMajorPins_run {env : Env} {rP F : Nat} {M : TargetMajor}
    (h : targetMajorPins (fueledOps mode F) env rP M = .ok ()) (hout : M.member = none) :
    (∀ x ∈ M.ds, ∃ ty, inferTypeCore mode env F rP x = .ok ty) ∧
      ∃ ty, inferTypeCore mode env F rP (Expr.mkAppN (.const M.ind M.lvls) M.ds) = .ok ty := by
  unfold targetMajorPins at h
  rw [if_pos (by rw [hout]; rfl)] at h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨ty, hty, -⟩ := exceptBind_ok h
  exact ⟨targetPinTys_run (by cases u; exact hu), ty, hty⟩

/-- **The parameter typing, inverted at the entry**: at an OUTSIDE major
every parameter, and the instantiation `I.{us} D⃗`, infer at the rule
prefix. -/
theorem TargetTyEntry.pinTys_of {fe : FEnv} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {F : Nat} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member = none) :
    (∀ x ∈ M.ds, ∃ ty, inferTypeCore mode fe.env F rc.rP x = .ok ty) ∧
      ∃ ty, inferTypeCore mode fe.env F rc.rP (Expr.mkAppN (.const M.ind M.lvls) M.ds) = .ok ty :=
  targetMajorPins_run E.hpinTys hM

/-- **The elimination guard at one recursor, inverted**: allowed, or the
conclusion's inferred type is `Prop`. -/
theorem targetRecElim_run {fe : FEnv} {p : BlockShape} {nested : Bool} {rc : RecShape}
    {cvRi : ConstantVal} {F : Nat}
    (h : targetRecElim (fueledOps mode F) fe p nested rc cvRi = .ok ()) :
    blockLargeElimAllowed p nested = true ∨ ∃ fvs concl sty,
      openPisAtFvars (rc.mI + 1) cvRi.type 0 = some (fvs, concl) ∧
      inferTypeCore mode fe.env F (rc.mI + 1) concl = .ok sty ∧
      isDefEqCore mode fe.env F (rc.mI + 1) sty (.sort .zero) = .ok true := by
  unfold targetRecElim at h
  by_cases hlarge : blockLargeElimAllowed p nested = true
  · exact .inl hlarge
  rw [if_neg (by simpa using hlarge)] at h
  obtain ⟨⟨fvs, concl⟩, hx, h⟩ := exceptBind_ok h
  obtain ⟨sty, hsty, h⟩ := exceptBind_ok h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  by_cases hbt : b = true
  case neg => rw [if_neg (by simpa using hbt)] at h; close_throw h
  subst hbt
  exact .inr ⟨fvs, concl, sty, unwrapOr_ok hx, hsty, hb⟩

/-- **Stage (b) at one recursor, inverted**, its elimination guard read
off the run after the walk (`targetRecElim`, at the walk's container
bit `nested`). -/
theorem targetRecTy_run {fe : FEnv} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {F : Nat} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (h : targetRecTy (fueledOps mode F) fe p cvTas ctorsAs rc = .ok (cvRi, M, u))
    (hel : targetRecElim (fueledOps mode F) fe p nested rc cvRi = .ok ()) :
    Nonempty (TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u) := by
  unfold targetRecTy at h
  obtain ⟨cvRi', hcv, h⟩ := exceptBind_ok h
  by_cases hroom : p.nP ≤ rc.rP
  case neg => rw [if_neg hroom] at h; close_throw h
  rw [if_pos hroom] at h
  by_cases hle : rc.rP ≤ rc.mI
  case neg => rw [if_neg hle] at h; close_throw h
  rw [if_pos hle] at h
  obtain ⟨x1, hx1, h⟩ := exceptBind_ok h
  obtain ⟨fvs, concl⟩ := x1
  obtain ⟨maj, hmaj, h⟩ := exceptBind_ok h
  obtain ⟨M', hM', h⟩ := exceptBind_ok h
  obtain ⟨⟨R⟩, -⟩ := targetMajorOf_run hM'
  by_cases htgt : (M'.member.all (· == rc.tgt)) = true
  case neg => rw [if_neg htgt] at h; close_throw h
  rw [if_pos htgt] at h
  -- the outside major's pins typed (nothing at a member)
  obtain ⟨u0, hpinTys, h⟩ := exceptBind_ok h
  obtain ⟨cvTP, hcvTP, h⟩ := exceptBind_ok h
  obtain ⟨x2, hx2, h⟩ := exceptBind_ok h
  obtain ⟨tfvs, trest⟩ := x2
  obtain ⟨ud, hud, h⟩ := exceptBind_ok h
  by_cases hmI : (rc.mI == rc.rP + M'.nIdx) = true
  case neg => rw [if_neg hmI] at h; close_throw h
  rw [if_pos hmI] at h
  by_cases hargs : (maj.fvarTypeD.getAppArgs.length == M'.nPc + M'.nIdx &&
      maj.fvarTypeD.getAppArgs.drop M'.nPc == (fvs.drop rc.rP).take (rc.mI - rc.rP)) = true
  case neg => rw [if_neg hargs] at h; close_throw h
  rw [if_pos hargs] at h
  obtain ⟨idoms, hidoms, h⟩ := exceptBind_ok h
  obtain ⟨ui, hui, h⟩ := exceptBind_ok h
  obtain ⟨sty, hsty, h⟩ := exceptBind_ok h
  obtain ⟨u', hu', h⟩ := exceptBind_ok h
  obtain ⟨hpl, hpall⟩ := checkBlockDefEqList_inv (mode := mode) (by cases ud; exact hud)
  obtain ⟨hil, hiall⟩ := checkBlockDefEqList_inv (mode := mode) (by cases ui; exact hui)
  simp only [Bool.and_eq_true, beq_iff_eq] at hargs hmI
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hsmall : blockLargeElimAllowed p nested = true ∨
      isDefEqCore mode fe.env F (rc.mI + 1) sty (.sort .zero) = .ok true := by
    rcases targetRecElim_run hel with hl | ⟨fvs', concl', sty', ho', hs', hd'⟩
    · exact .inl hl
    · rw [unwrapOr_ok hx1] at ho'
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ho')
      have hsty' : inferTypeCore mode fe.env F (rc.mI + 1) concl = .ok sty := hsty
      rw [hsty'] at hs'
      obtain rfl := Except.ok.inj hs'
      exact .inr hd'
  exact ⟨{
        cvTP := cvTP, fvs := fvs, concl := concl, tfvs := tfvs, trest := trest,
        maj := maj, idoms := idoms, sty := sty, hcv := hcv,
        hroom := hroom, hle := hle, hopen := unwrapOr_ok hx1, hmaj := unwrapOr_ok hmaj,
        major := R, htgt := htgt, hcvTP := unwrapOr_ok hcvTP, hopenT := unwrapOr_ok hx2,
        hparLen := hpl, hparams := hpall, hmI := hmI,
        hmajLen := hargs.1, hmajIdx := hargs.2, hidoms := hidoms,
        hidxLen := (by simpa using hil), hidx := fun l hl => hiall l hl, hsty := hsty,
        hu := hu', hsmall := hsmall, hpinTys := by cases u0; exact hpinTys }⟩

/-- **The major → node tie, inverted** (`targetTies`, after the walk):
every outside class matches a recorded node class of its inductive. -/
theorem targetTies_run {env : Env} {p : BlockShape} {formerTys : List Expr}
    {keys : List NestKey} {F : Nat} :
    ∀ {tys : List (ConstantVal × TargetMajor × Level)},
      targetTies (fueledOps mode F) env p formerTys keys tys = .ok () →
      ∀ t ∈ tys, t.2.1.member = none → ∃ k ∈ keys, k.cname = t.2.1.ind ∧
        targetClassMatch (fueledOps mode F) env p formerTys t.2.1.pfvs t.2.1.lvls t.2.1.ds
          k.lvls k.ds = .ok true
  | [], _, t, ht, _ => nomatch ht
  | (cvRi, M, u) :: ts, h, t, ht, hM => by
    unfold targetTies at h
    have hrest : targetTies (fueledOps mode F) env p formerTys keys ts = .ok () := by
      split at h
      · obtain ⟨b, -, h⟩ := exceptBind_ok h
        split at h
        · exact h
        · close_throw h
      · exact h
    rcases List.mem_cons.mp ht with rfl | ht
    · rw [if_pos (by simpa using hM)] at h
      obtain ⟨b, hb, h⟩ := exceptBind_ok h
      by_cases hbt : b = true
      case neg => rw [if_neg (by simpa using hbt)] at h; close_throw h
      subst hbt
      exact targetNodeTie_true hb
    · exact targetTies_run hrest t ht hM

/-- **The elimination guards, inverted**: at every recursor its own. -/
theorem targetRecElims_run {fe : FEnv} {p : BlockShape} {nested : Bool} {F : Nat} :
    ∀ {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)},
      targetRecElims (fueledOps mode F) fe p nested recs tys = .ok () →
      ∀ (i : Nat) (rc : RecShape) (t : ConstantVal × TargetMajor × Level),
        recs[i]? = some rc → tys[i]? = some t →
        targetRecElim (fueledOps mode F) fe p nested rc t.1 = .ok ()
  | [], _, _, i, rc, t, hi, _ => nomatch hi
  | _ :: _, [], _, i, rc, t, _, ht => nomatch ht
  | rc0 :: rcs, (cvRi, M, u) :: ts, h, i, rc, t, hi, ht => by
    unfold targetRecElims at h
    obtain ⟨u1, h1, h⟩ := exceptBind_ok h
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      obtain rfl := Option.some.inj ht
      cases u1; exact h1
    | succ i => exact targetRecElims_run h i rc t (by simpa using hi) (by simpa using ht)

/-- **Stage (b) at every recursor, inverted**: one entry per recursor,
its elimination guard read off the run after the walk. -/
theorem targetRecTys_run {fe : FEnv} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat} :
    ∀ {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)},
      targetRecTys (fueledOps mode F) fe p cvTas ctorsAs recs = .ok tys →
      targetRecElims (fueledOps mode F) fe p nested recs tys = .ok () →
      tys.length = recs.length ∧
      ∀ (i : Nat) (rc : RecShape), recs[i]? = some rc →
        ∃ cvRi M u, tys[i]? = some (cvRi, M, u) ∧
        Nonempty (TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
  | [], tys, h, _ => by
    simp only [targetRecTys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i rc hi => nomatch hi⟩
  | rc :: rcs, tys, h, hel => by
    unfold targetRecTys at h
    obtain ⟨t, ht, h⟩ := exceptBind_ok h
    obtain ⟨ts, hts, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨cvRi, M, u⟩ := t
    unfold targetRecElims at hel
    obtain ⟨u1, hel1, hel⟩ := exceptBind_ok hel
    obtain ⟨hlen, hall⟩ := targetRecTys_run hts hel
    refine ⟨by simp [hlen], fun i rc' hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl : rc = rc' := by simpa using hi
      exact ⟨cvRi, M, u, rfl, targetRecTy_run ht (by cases u1; exact hel1)⟩
    | succ i =>
      obtain ⟨cvRi, M, u, hti, E⟩ := hall i rc' (by simpa using hi)
      exact ⟨cvRi, M, u, by simpa using hti, E⟩

/-! ## Stage (c): the fields' abstract telescopes, and the calls' typing -/

/-- **`targetFieldNorms`, inverted**: one whnf-telescope run per field,
on the member-abstracted field type. -/
theorem targetFieldNorms_run {env : Env} {depth F : Nat} {absM : Expr → Expr} :
    ∀ {fvs fnorm : List Expr},
      targetFieldNorms (fueledOps mode F) env depth absM fvs = .ok fnorm →
      fnorm.length = fvs.length ∧
      ∀ (i : Nat) (f : Expr), fvs[i]? = some f → ∃ t, fnorm[i]? = some t ∧
        targetWhnfPis (fueledOps mode F) env depth (whnfWalkFuel (absM f.fvarTypeD))
          (absM f.fvarTypeD) = .ok t
  | [], fnorm, h => by
    simp only [targetFieldNorms, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i f hi => nomatch hi⟩
  | f :: fs, fnorm, h => by
    unfold targetFieldNorms at h
    obtain ⟨t, ht, h⟩ := exceptBind_ok h
    obtain ⟨ts, hts, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := targetFieldNorms_run hts
    refine ⟨by simp [hlen], fun i f' hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl : f = f' := by simpa using hi
      exact ⟨t, rfl, ht⟩
    | succ i =>
      obtain ⟨t', ht', hrun⟩ := hall i f' (by simpa using hi)
      exact ⟨t', by simpa using ht', hrun⟩

/-- **One call's typing, as run**: the field's abstract whnf-telescope
`fty`, its hole-free telescope, the callee's stored type instantiated
at the call's arguments, both abstract sides inferred, and the
field-vs-major defeq at the depth past the holes. -/
structure TargetCallRun (mode : CheckMode) (F : Nat) (env : Env) (fam : TargetFamily)
    (fvsPref fvsF fnorm : List Expr) (teles : List (List (Expr × BinderMeta)))
    (absM : Expr → Expr) (base k : Nat) (pw : PropWhen) (ih : TargetIh) : Type where
  calleeAt : Expr
  majDom : Expr
  majBody : Expr
  majBm : BinderMeta
  fldTy : Expr
  wantTy : Expr
  /-- the telescope the call applies the field along is hole-free -/
  htele : ∀ b ∈ teles.getD ih.field [], targetHoleFree base k b.1 = true
  /-- (K5) the call's index arguments are left alone by the abstraction -/
  hidxAbs : ∀ x ∈ ih.idx, absM x = x
  hcallee : Expr.instPisAtLift (fvsPref ++ ih.idx) (fam.recTys.getD ih.callee (.sort .zero))
    = some calleeAt
  hmajDom : calleeAt = .forallE majDom majBody majBm
  /-- both abstract sides inferred at the depth past the holes -/
  hfld : inferTypeCore mode env F (base + k) (absM ((fvsF.getD ih.field default).fvarTypeD))
    = .ok fldTy
  hwant : inferTypeCore mode env F (base + k)
    (Expr.mkPisOf (teles.getD ih.field []) (absM majDom)) = .ok wantTy
  /-- THE CALL'S TYPING: the field's abstract telescope is the callee's
  abstract major type at the call's arguments -/
  hdeq : isDefEqCore mode env F (base + k) (fnorm.getD ih.field default)
    (Expr.mkPisOf (teles.getD ih.field []) (absM majDom)) = .ok true
  /-- the call's own type at the frame and the telescope -/
  callTy : Expr
  /-- THE CALL IS WELL-TYPED: `λ a⃗ : A⃗, c x⃗ e⃗ (f a⃗)`, the callee a
  variable of its stored type after the frame -/
  hcall : inferTypeCore mode env F (base + 1)
    (Expr.mkLamsOf ((teles.getD ih.field []).map fun b => (b.1, ⟨pw⟩))
      (Expr.mkAppN (.fvar base (fam.recTys.getD ih.callee (.sort .zero)))
        (fvsPref ++ ih.idx ++
          [Expr.mkAppN (fvsF.getD ih.field default)
            (structTeleVars (teles.getD ih.field []).length)]))) = .ok callTy
  /-- the `ih` variable's type is inferred at the frame -/
  ihTyTy : Expr
  hihTy : inferTypeCore mode env F base ih.ty = .ok ihTyTy
  /-- and it IS the call's type -/
  hcallEq : isDefEqCore mode env F (base + 1) callTy ih.ty = .ok true

/-- **One call's typing, inverted.** -/
theorem targetCallOk_run {env : Env} {p : BlockShape} {formerTys : List Expr} {cn : Name}
    {fam : TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k F : Nat} {pw : PropWhen} {fws : List Expr}
    {ih : TargetIh}
    (h : targetCallOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF fnorm teles absM base
      k pw fws ih = .ok ()) :
    Nonempty (TargetCallRun mode F env fam fvsPref fvsF fnorm teles absM base k pw ih) := by
  unfold targetCallOk at h
  by_cases htele : ((teles.getD ih.field []).all fun b => targetHoleFree base k b.1) = true
  case neg => rw [if_neg htele] at h; close_throw h
  rw [if_pos htele] at h
  by_cases hidx : (ih.idx.all fun x => absM x == x) = true
  case neg => rw [if_neg hidx] at h; close_throw h
  rw [if_pos hidx] at h
  dsimp only at h
  split at h
  · next calleeAt hcallee =>
    split at h
    · next majDom majBody majBm =>
      obtain ⟨fldTy, hfld, h⟩ := exceptBind_ok h
      obtain ⟨wantTy, hwant, h⟩ := exceptBind_ok h
      obtain ⟨b, hb, h⟩ := exceptBind_ok h
      by_cases hbt : b = true
      case neg => rw [if_neg hbt] at h; close_throw h
      subst hbt
      rw [if_pos rfl] at h
      obtain ⟨callTy, hcallTy, h⟩ := exceptBind_ok h
      obtain ⟨ihTyTy, hihTy, h⟩ := exceptBind_ok h
      obtain ⟨b2, hb2, h⟩ := exceptBind_ok h
      by_cases hbt2 : b2 = true
      case neg => rw [if_neg hbt2] at h; close_throw h
      subst hbt2
      exact ⟨{ calleeAt := .forallE majDom majBody majBm, majDom := majDom, majBody := majBody,
               majBm := majBm, fldTy := fldTy, wantTy := wantTy,
               htele := fun b hb => List.all_eq_true.mp htele b hb,
               hidxAbs := fun x hx => eq_of_beq (List.all_eq_true.mp hidx x hx),
               hcallee := hcallee, hmajDom := rfl, hfld := hfld, hwant := hwant,
               hdeq := hb, callTy := callTy, hcall := hcallTy, ihTyTy := ihTyTy, hihTy := hihTy,
               hcallEq := hb2 }⟩
    · close_throw h
  · close_throw h

/-- **Every call's typing, inverted**: one `TargetCallRun` per call. -/
theorem targetCallsOk_run {env : Env} {p : BlockShape} {formerTys : List Expr} {cn : Name}
    {fam : TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k F : Nat} {pw : PropWhen} {fws : List Expr} :
    ∀ {ihs : List TargetIh},
      targetCallsOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF fnorm teles absM base k
        pw fws ihs = .ok () →
      ∀ ih ∈ ihs,
        Nonempty (TargetCallRun mode F env fam fvsPref fvsF fnorm teles absM base k pw ih)
  | [], _, ih, hih => nomatch hih
  | ih0 :: ihs, h, ih, hih => by
    unfold targetCallsOk at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hih with rfl | hih
    · exact targetCallOk_run (by cases u; exact hu)
    · exact targetCallsOk_run h ih hih

/-- **K.53′ at one recorded field, inverted** (`targetK53`): the field
is a telescope, up to the free variables' annotations the call's, over a
leaf headed by the callee major's constant, its indices the major's up to
the annotations, its class matching the callee's (`targetClassMatch`). -/
theorem targetK53_true {ops : CheckerOps CheckM} {env : Env} {p : BlockShape}
    {formerTys : List Expr} {Mc : TargetMajor} {tele : List (Expr × BinderMeta)}
    {majDom f : Expr}
    (h : targetK53 ops env p formerTys Mc tele majDom f = .ok true) :
    ∃ (teleW : List (Expr × BinderMeta)) (leafW : Expr) (I : Name) (us' us : List Level),
      f.stripPis tele.length = some (teleW, leafW) ∧
      teleW.map (fun b => (b.1.eraseFVarTys, b.2)) = tele.map (fun b => (b.1.eraseFVarTys, b.2)) ∧
      leafW.getAppFn = .const I us' ∧ majDom.getAppFn = .const I us ∧
      leafW.getAppArgs.length = majDom.getAppArgs.length ∧
      (leafW.getAppArgs.drop Mc.nPc).map Expr.eraseFVarTys
        = (majDom.getAppArgs.drop Mc.nPc).map Expr.eraseFVarTys ∧
      (Expr.mkAppN (.const I us') (leafW.getAppArgs.take Mc.nPc)).nestOcc p.memberNames 0 0
        = true ∧
      targetClassMatch ops env p formerTys Mc.pfvs Mc.lvls Mc.ds us'
        (leafW.getAppArgs.take Mc.nPc) = .ok true := by
  unfold targetK53 at h
  split at h
  · simp [pure, Except.pure] at h
  rename_i teleW leafW hstrip
  split at h
  · simp [pure, Except.pure] at h
  rename_i htele
  split at h
  · rename_i I' us' I us hW hM
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨rfl, hl⟩, hidx⟩, hment⟩ := hc
      exact ⟨teleW, leafW, I', us', us, hstrip, by simpa using htele, hW, hM, hl, hidx, hment, h⟩
    · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

/-- **K.53′, inverted**: at a call's typing that ran through, the walked
field at the node (`fws`, the walked constructor's fields at the rule's
field variables) passed `targetK53` against the callee's class. -/
theorem targetCallOk_k53 {env : Env} {p : BlockShape} {formerTys : List Expr} {cn : Name}
    {fam : TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k F : Nat} {pw : PropWhen} {fws : List Expr}
    {ih : TargetIh}
    (h : targetCallOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF fnorm teles absM base
      k pw fws ih = .ok ())
    (C : TargetCallRun mode F env fam fvsPref fvsF fnorm teles absM base k pw ih) :
    ∃ f, fws[ih.field]? = some f ∧
      targetK53 (fueledOps mode F) env p formerTys (fam.majs.getD ih.callee default)
        (teles.getD ih.field []) C.majDom f = .ok true := by
  have hC := C.hcallee
  rw [C.hmajDom] at hC
  unfold targetCallOk at h
  by_cases htele : ((teles.getD ih.field []).all fun b => targetHoleFree base k b.1) = true
  case neg => rw [if_neg htele] at h; close_throw h
  rw [if_pos htele] at h
  by_cases hidx : (ih.idx.all fun x => absM x == x) = true
  case neg => rw [if_neg hidx] at h; close_throw h
  rw [if_pos hidx] at h
  dsimp only at h
  rw [hC] at h
  dsimp only at h
  obtain ⟨fldTy, hfld, h⟩ := exceptBind_ok h
  obtain ⟨wantTy, hwant, h⟩ := exceptBind_ok h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  by_cases hbt : b = true
  case neg => rw [if_neg hbt] at h; close_throw h
  subst hbt
  rw [if_pos rfl] at h
  obtain ⟨callTy, hcallTy, h⟩ := exceptBind_ok h
  obtain ⟨ihTyTy, hihTy, h⟩ := exceptBind_ok h
  obtain ⟨b2, hb2, h⟩ := exceptBind_ok h
  by_cases hbt2 : b2 = true
  case neg => rw [if_neg hbt2] at h; close_throw h
  subst hbt2
  rw [if_pos rfl] at h
  obtain ⟨b3, hb3, h⟩ := exceptBind_ok h
  by_cases hk : b3 = true
  case neg => rw [if_neg (by simpa using hk)] at h; close_throw h
  subst hk
  split at hb3
  · simp [pure, Except.pure] at hb3
  · rename_i f hf
    exact ⟨f, hf, hb3⟩

/-! ## Stage (c): ONE rule -/

/-- The rule frame `targetRule` walks against, as the function builds
it (the record states the abstraction at it). -/
@[expose] def targetFrameOf (fam : TargetFamily) (rP : Nat) (fvsPref fvsF fnorm : List Expr)
    (pw : PropWhen) : TargetFrame :=
  { recNames := fam.recNames, rlvls := fam.rlvls, recTys := fam.recTys, mIs := fam.mIs,
    rPs := fam.rPs, rP := rP, pref := fvsPref, fields := fvsF,
    teles := fnorm.map fun t => t.piBinders.1, pw := pw }

/-- **Stage (c) at ONE rule**, every bind of `targetRule`'s body named:
the stream's right-hand side `rhs` is annotated into `out` (the STORED
rule) at the rule-less recursor environment `feR`, its λ-tower compared
binder by binder with the stored recursor type's prefix and the
constructor's fields at the major's instantiation, every recursive
call abstracted into an `ih` variable (`targetAbstract`, first
occurrence), each call typed on the member-abstracted terms (K.53′
against the walked constructor `ety` of a node the rule was typed at),
and the residue typed against the recursor's conclusion at the
constructor. -/
structure TargetRuleRun (mode : CheckMode) (F : Nat) (feR feT : FEnv) (p : BlockShape)
    (formerTys : List Expr) (fam : TargetFamily) (cvR : ConstantVal) (rP : Nat)
    (recTy : Expr) (M : TargetMajor) (c : ConstantVal × Nat) (rhs out : Expr) : Type where
  /-- the walked constructor (read back, `NestCtorNf.ty`) of the node the
  rule was typed at -/
  ety : Expr
  tyR : Expr
  rbs : List (Expr × BinderMeta)
  body : Expr
  fvsPref : List Expr
  oPref : Expr
  crest : Expr
  fvsF : List Expr
  cbody : Expr
  ldoms : List Expr
  lrest : Expr
  fnorm : List Expr
  bodyO : Expr
  ihs : Array TargetIh
  ty : Expr
  concl : Expr
  hbv : rhs.looseBVarsBounded 0 = true
  hfv : rhs.hasFvar = false
  hann : annotateCore mode feR.env F 0 rhs = .ok out
  hlp : out.allLevelParamsDefined cvR.levelParams = true
  hres : StructWalkers.plain.resolve feR out = true
  htyR : inferTypeCore mode feR.env F 0 out = .ok tyR
  hstrip : Expr.stripLams (rP + c.2) out = some (rbs, body)
  hpw : ∀ b ∈ rbs, b.2.pw = Level.zeronessOf (structElimLevel p.elim p.large)
  hpref : openPisAtFvars rP recTy 0 = some (fvsPref, oPref)
  hcrest : instPisWith M.ds (targetCtorAt M c.1) = some crest
  hfld : openPisAtFvars c.2 crest rP = some (fvsF, cbody)
  hlams : Expr.instLamsAt (fvsPref ++ fvsF) out = some (ldoms, lrest)
  /-- the λ-domains resolve at the constructors' environment -/
  hldomsRes : ∀ t ∈ ldoms, StructWalkers.plain.resolve feT t = true
  hG2len : ((fvsPref ++ fvsF).map Expr.fvarTypeD).length = ldoms.length
  hG2 : ∀ l, l < ((fvsPref ++ fvsF).map Expr.fvarTypeD).length →
    isDefEqCore mode feT.env F (rP + c.2)
      (((fvsPref ++ fvsF).map Expr.fvarTypeD).getD l default) (ldoms.getD l default) = .ok true
  /-- the fields' member-abstracted telescopes, through whnf -/
  hfnorm : targetFieldNorms (fueledOps mode F) feT.env (rP + c.2 + formerTys.length)
    (targetAbs p.memberNames (p.lps.map .param) (targetHoles formerTys (rP + c.2))) fvsF
      = .ok fnorm
  /-- K4: the fields' telescopes name only the recursor's universe parameters -/
  hfnormLp : ∀ t ∈ fnorm, t.allLevelParamsDefined cvR.levelParams = true
  /-- THE ABSTRACTION: every call replaced by its `ih` variable -/
  habs : targetAbstract (targetFrameOf fam rP fvsPref fvsF fnorm
      (Level.zeronessOf (structElimLevel p.elim p.large))) (rP + c.2) 0
    (body.instantiateList (fvsPref ++ fvsF).reverse) #[] = some (bodyO, ihs)
  /-- every call's typing, on the member-abstracted terms -/
  hcalls : targetCallsOk (fueledOps mode F) feT.env p formerTys c.1.name fam fvsPref fvsF fnorm
    (fnorm.map fun t => t.piBinders.1)
    (targetAbs p.memberNames (p.lps.map .param) (targetHoles formerTys (rP + c.2)))
    (rP + c.2) formerTys.length (Level.zeronessOf (structElimLevel p.elim p.large))
    ((targetPiDomsWith fvsF ety).getD []) ihs.toList = .ok ()
  hty : inferTypeCore mode feT.env F (rP + c.2 + ihs.size) bodyO = .ok ty
  hconcl : Expr.instPisAtLift
      (fvsPref ++ (cbody.getAppArgs.drop M.nPc) ++
        [Expr.mkAppN (.const c.1.name M.lvls) (M.ds ++ fvsF)])
      recTy = some concl
  hdeq : isDefEqCore mode feT.env F (rP + c.2 + ihs.size) ty concl = .ok true

namespace TargetRuleRun

variable {F : Nat} {feR feT : FEnv} {p : BlockShape} {formerTys : List Expr}
  {fam : TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr} {M : TargetMajor}
  {c : ConstantVal × Nat} {rhs out : Expr}

/-- Every call's typing record, at the rule's own frame. -/
theorem call (R : TargetRuleRun mode F feR feT p formerTys fam cvR rP recTy M c rhs out)
    {ih : TargetIh} (hih : ih ∈ R.ihs.toList) :
    Nonempty (TargetCallRun mode F feT.env fam R.fvsPref R.fvsF R.fnorm
      (R.fnorm.map fun t => t.piBinders.1)
      (targetAbs p.memberNames (p.lps.map .param) (targetHoles formerTys (rP + c.2)))
      (rP + c.2) formerTys.length (Level.zeronessOf (structElimLevel p.elim p.large)) ih) :=
  targetCallsOk_run R.hcalls ih hih

end TargetRuleRun

/-- **Stage (c) at ONE rule, inverted.** -/
theorem targetRule_run {feR feT : FEnv} {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr} {M : TargetMajor}
    {c : ConstantVal × Nat} {rhs ety out : Expr} {F : Nat}
    (h : targetRule (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam cvR rP
      recTy M c rhs ety = .ok out) :
    ∃ R : TargetRuleRun mode F feR feT p formerTys fam cvR rP recTy M c rhs out, R.ety = ety := by
  unfold targetRule at h
  by_cases hbv : Expr.looseBVarsBounded 0 rhs = true
  case neg => rw [if_neg hbv] at h; close_throw h
  rw [if_pos hbv] at h
  by_cases hfv : rhs.hasFvar = true
  case pos => rw [if_pos hfv] at h; close_throw h
  rw [if_neg hfv] at h
  obtain ⟨rhsA, hann, h⟩ := exceptBind_ok h
  by_cases hlp : Expr.allLevelParamsDefined cvR.levelParams rhsA = true
  case neg => rw [if_neg hlp] at h; close_throw h
  rw [if_pos hlp] at h
  by_cases hres : StructWalkers.plain.resolve feR rhsA = true
  case neg => rw [if_neg hres] at h; close_throw h
  rw [if_pos hres] at h
  obtain ⟨tyR, htyR, h⟩ := exceptBind_ok h
  obtain ⟨x1, hx1, h⟩ := exceptBind_ok h; obtain ⟨rbs, body⟩ := x1
  dsimp only at h
  by_cases hpw : rbs.all
      (fun b => b.2.pw == Level.zeronessOf (structElimLevel p.elim p.large)) = true
  case neg => rw [if_neg hpw] at h; close_throw h
  rw [if_pos hpw] at h
  obtain ⟨x2, hx2, h⟩ := exceptBind_ok h; obtain ⟨fvsPref, oPref⟩ := x2
  obtain ⟨crest, hcrest, h⟩ := exceptBind_ok h
  obtain ⟨x4, hx4, h⟩ := exceptBind_ok h; obtain ⟨fvsF, cbody⟩ := x4
  obtain ⟨x5, hx5, h⟩ := exceptBind_ok h; obtain ⟨ldoms, lrest⟩ := x5
  dsimp only at h
  by_cases hcbd : ldoms.all (fun t => StructWalkers.plain.resolve feT t) = true
  case neg => rw [if_neg hcbd] at h; close_throw h
  rw [if_pos hcbd] at h
  obtain ⟨u2, hG2, h⟩ := exceptBind_ok h
  cases u2
  obtain ⟨fnorm, hfnorm, h⟩ := exceptBind_ok h
  by_cases hflp : fnorm.all (fun t => t.allLevelParamsDefined cvR.levelParams) = true
  case neg => rw [if_neg hflp] at h; close_throw h
  rw [if_pos hflp] at h
  obtain ⟨x9, hx9, h⟩ := exceptBind_ok h; obtain ⟨bodyO, ihs⟩ := x9
  obtain ⟨u3, hcalls, h⟩ := exceptBind_ok h
  cases u3
  obtain ⟨ty, hty, h⟩ := exceptBind_ok h
  obtain ⟨concl, hconcl, h⟩ := exceptBind_ok h
  obtain ⟨b, hb, h⟩ := exceptBind_ok h
  by_cases hd : b = true
  case neg => rw [if_neg hd] at h; close_throw h
  subst hd
  have hout : out = rhsA := by
    simpa [pure, Except.pure] using h.symm
  subst hout
  obtain ⟨hG2len, hG2all⟩ := checkBlockDefEqList_inv (mode := mode) hG2
  exact ⟨{
          ety := ety,
          tyR := tyR, rbs := rbs, body := body, fvsPref := fvsPref, oPref := oPref,
          crest := crest, fvsF := fvsF, cbody := cbody, ldoms := ldoms, lrest := lrest,
          fnorm := fnorm, bodyO := bodyO, ihs := ihs, ty := ty, concl := concl,
          hbv := hbv, hfv := Bool.not_eq_true _ |>.mp hfv, hann := hann, hlp := hlp,
          hres := hres, htyR := htyR, hstrip := unwrapOr_ok hx1,
          hpw := fun b hb => eq_of_beq ((List.all_eq_true.mp hpw) b hb),
          hpref := unwrapOr_ok hx2, hcrest := unwrapOr_ok hcrest, hfld := unwrapOr_ok hx4,
          hlams := unwrapOr_ok hx5, hldomsRes := List.all_eq_true.mp hcbd,
          hG2len := hG2len, hG2 := hG2all, hfnorm := hfnorm,
          hfnormLp := List.all_eq_true.mp hflp, habs := unwrapOr_ok hx9,
          hcalls := hcalls, hty := hty, hconcl := unwrapOr_ok hconcl, hdeq := hb }, rfl⟩

/-! ## Stage (c): one recursor's rules, read off the walk's hook -/

/-- **One recursor's rules**: one stored rule per constructor of its
major and per stream right-hand side, each a `targetRule` run (at the
walked constructor `ety` of a node the rule was typed at). -/
structure TargetRulesRun (mode : CheckMode) (F : Nat) (feR feT : FEnv) (p : BlockShape)
    (formerTys : List Expr) (fam : TargetFamily) (cvRi : ConstantVal) (rP : Nat)
    (M : TargetMajor) (cs : List (ConstantVal × Nat)) (rhss out : List Expr) : Prop where
  len : out.length = cs.length
  lenRhs : rhss.length = cs.length
  rule : ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr), cs[j]? = some cA →
    rhss[j]? = some rhs → ∃ o ety, out[j]? = some o ∧
      targetRule (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam cvRi rP
        cvRi.type M cA rhs ety = .ok o

/-- **Class `c`'s rule at a walked constructor, inverted**: its output
is the rule of one of the class's constructors, typed at the walked
constructor. -/
theorem targetEntryRule_out {feR feT : FEnv} {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {e : NestCtorNf} {c : Nat} {rc : RecShape} {cvRi : ConstantVal}
    {M : TargetMajor} {F : Nat} {xs : List (Nat × Nat × Expr)}
    (h : targetEntryRule (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam e c
      rc cvRi M = .ok xs) :
    ∀ x ∈ xs, x.1 = c ∧ ∃ cA rhs, M.ctors[x.2.1]? = some cA ∧ rc.rhss[x.2.1]? = some rhs ∧
      targetRule (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam cvRi rc.rP
        cvRi.type M cA rhs e.ty = .ok x.2.2 := by
  unfold targetEntryRule at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro x hx; exact nomatch hx
  rename_i j hj
  obtain ⟨b, -, h⟩ := exceptBind_ok h
  by_cases hb : b = true
  case neg =>
    rw [if_neg (by simpa using hb)] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro x hx; exact nomatch hx
  rw [if_pos hb] at h
  obtain ⟨cA, hcA, h⟩ := exceptBind_ok h
  obtain ⟨rhs, hrhs, h⟩ := exceptBind_ok h
  obtain ⟨o, ho, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨rfl, cA, rhs, unwrapOr_ok hcA, unwrapOr_ok hrhs, ho⟩

/-- **The rules of every class at a walked constructor, inverted.** -/
theorem targetEntryRules_out {feR feT : FEnv} {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {e : NestCtorNf} {F : Nat} :
    ∀ {c : Nat} {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)}
      {xs : List (Nat × Nat × Expr)},
      targetEntryRules (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam e c
        recs tys = .ok xs →
      ∀ x ∈ xs, ∃ i, x.1 = c + i ∧ ∃ rc t, recs[i]? = some rc ∧ tys[i]? = some t ∧
        ∃ cA rhs, t.2.1.ctors[x.2.1]? = some cA ∧ rc.rhss[x.2.1]? = some rhs ∧
          targetRule (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam t.1
            rc.rP t.1.type t.2.1 cA rhs e.ty = .ok x.2.2
  | _, [], _, xs, h => by
    simp only [targetEntryRules, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro x hx; exact nomatch hx
  | _, _ :: _, [], xs, h => by
    simp only [targetEntryRules, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro x hx; exact nomatch hx
  | c, rc :: rcs, (cvRi, M, u) :: ts, xs, h => by
    unfold targetEntryRules at h
    obtain ⟨here, hh, h⟩ := exceptBind_ok h
    obtain ⟨rest, hr, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨h1, cA, rhs, h2, h3, h4⟩ := targetEntryRule_out hh x hx
      exact ⟨0, by simpa using h1, rc, (cvRi, M, u), rfl, rfl, cA, rhs, h2, h3, h4⟩
    · obtain ⟨i, hi, rc', t', h1, h2, rest'⟩ := targetEntryRules_out hr x hx
      exact ⟨i + 1, by rw [hi]; omega, rc', t', by simpa using h1, by simpa using h2, rest'⟩

/-- **A hook output, inverted**: the rule of recursor `c`'s constructor
`j`, typed at some walked constructor. -/
theorem targetHook_out {fe feR : FEnv} {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)}
    {F : Nat} {x : Nat × Nat × Expr}
    (h : HookOut (targetHook (ShadowOps.fueled mode F) fe feR p formerTys fam recs tys) x) :
    ∃ rc t, recs[x.1]? = some rc ∧ tys[x.1]? = some t ∧
      ∃ cA rhs ety, t.2.1.ctors[x.2.1]? = some cA ∧ rc.rhss[x.2.1]? = some rhs ∧
        targetRule (fueledOps mode F) .plain feR (fueledOps mode F) fe p formerTys fam t.1
          rc.rP t.1.type t.2.1 cA rhs ety = .ok x.2.2 := by
  obtain ⟨e, xs, he, hx⟩ := h
  simp only [targetHook, ShadowOps.fueled, ShadowOps.ofOps] at he
  obtain ⟨u1, -, he⟩ := exceptBind_ok he
  obtain ⟨xs', hxs', he⟩ := exceptBind_ok he
  obtain ⟨u2, -, he⟩ := exceptBind_ok he
  simp only [pure, Except.pure, Except.ok.injEq] at he
  subst he
  obtain ⟨i, hi, rc, t, h1, h2, cA, rhs, h3, h4, h5⟩ := targetEntryRules_out hxs' x hx
  rw [show x.1 = i by simpa using hi]
  exact ⟨rc, t, h1, h2, cA, rhs, e.ty, h3, h4, h5⟩

/-- **One recursor's rules read off the hook's outputs, inverted.** -/
theorem targetOutRules_run {done : List (Nat × Nat × Expr)} {c : Nat} :
    ∀ {j n : Nat} {os : List Expr}, targetOutRules (m := CheckM) done c j n = .ok os →
      os.length = n ∧ ∀ l o, os[l]? = some o → (c, j + l, o) ∈ done
  | _, 0, os, h => by
    simp only [targetOutRules, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun l o h => nomatch h⟩
  | j, n + 1, os, h => by
    unfold targetOutRules at h
    obtain ⟨o, ho, h⟩ := exceptBind_ok h
    obtain ⟨os', hos, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := targetOutRules_run hos
    refine ⟨by simp [hlen], fun l o' hl => ?_⟩
    cases l with
    | zero =>
      obtain rfl := Option.some.inj hl
      have ho' := unwrapOr_ok ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp ho'
      have hmem := List.mem_of_find?_eq_some hx
      have hp := List.find?_some hx
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨x1, x2, x3⟩ := x
      simp only at hp
      obtain ⟨rfl, rfl⟩ := hp
      simpa using hmem
    | succ l =>
      have := hall l o' (by simpa using hl)
      rwa [show j + 1 + l = j + (l + 1) by omega] at this

/-- **The checked family read off the hook's outputs, inverted.** -/
theorem targetOutOf_run {done : List (Nat × Nat × Expr)} :
    ∀ {c : Nat} {tys : List (ConstantVal × TargetMajor × Level)}
      {out : List (ConstantVal × TargetMajor × List Expr)},
      targetOutOf (m := CheckM) done c tys = .ok out →
      out.length = tys.length ∧ ∀ (i : Nat) (t : ConstantVal × TargetMajor × Level),
        tys[i]? = some t → ∃ rhssA, out[i]? = some (t.1, t.2.1, rhssA) ∧
          rhssA.length = t.2.1.ctors.length ∧ ∀ j o, rhssA[j]? = some o → (c + i, j, o) ∈ done
  | _, [], out, h => by
    simp only [targetOutOf, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun i t h => nomatch h⟩
  | c, (cvRi, M, u) :: ts, out, h => by
    unfold targetOutOf at h
    obtain ⟨rhssA, hr, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := targetOutOf_run hrest
    refine ⟨by simp [hlen], fun i t hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      obtain ⟨hl, hr'⟩ := targetOutRules_run hr
      exact ⟨rhssA, rfl, hl, fun j o hj => by simpa using hr' j o hj⟩
    | succ i =>
      obtain ⟨r, hr2, hl, hall'⟩ := hall i t (by simpa using hi)
      exact ⟨r, by simpa using hr2, hl, fun j o hj => by
        rw [show c + (i + 1) = c + 1 + i by omega]; exact hall' j o hj⟩

/-- The rule counts, inverted: every recursor's rules cover its major's
constructors. -/
theorem targetRhssLen_run :
    ∀ {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)},
      targetRhssLen (m := CheckM) recs tys = .ok () →
      ∀ (i : Nat) (rc : RecShape) (t : ConstantVal × TargetMajor × Level),
        recs[i]? = some rc → tys[i]? = some t → rc.rhss.length = t.2.1.ctors.length
  | [], _, _, i, rc, t, hi, _ => nomatch hi
  | _ :: _, [], _, i, rc, t, _, ht => nomatch ht
  | rc0 :: rcs, (cvRi, M, u) :: ts, h, i, rc, t, hi, ht => by
    unfold targetRhssLen at h
    by_cases hl : (rc0.rhss.length == M.ctors.length) = true
    case neg => rw [if_neg hl] at h; close_throw h
    rw [if_pos hl] at h
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      obtain rfl := Option.some.inj ht
      exact beq_iff_eq.mp hl
    | succ i => exact targetRhssLen_run h i rc t (by simpa using hi) (by simpa using ht)

/-! ## The whole CHECK -/

/-- **The target recursor check, as run** (its positivity half read in
`PositivityInv`/`PosDerivInv`, through `targetRecCheck_run`'s walk
equation): the pins, the recursors' types (`tys`), the family's
agreements, the rule pins and counts, the elimination guard at the walk's
container bit `nested`, the tie against the walk's node classes `keys`,
and the family read off the walk's hook outputs `done` (each a hook
run's, `HookOut`). -/
structure TargetRecRun (mode : CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape)
    (nested : Bool) (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × TargetMajor × List Expr)) : Type where
  /-- stage (b)'s list -/
  tys : List (ConstantVal × TargetMajor × Level)
  /-- the classes of the walk's nodes (the tie's) -/
  keys : List NestKey
  /-- the walk's hook outputs -/
  done : List (Nat × Nat × Expr)
  /-- (a) the records' pins -/
  pins : targetRecPins (m := CheckM) p block = .ok ()
  /-- (b) every recursor's type -/
  htys : targetRecTys (fueledOps mode F) fe p cvTas ctorsAs p.recs = .ok tys
  /-- (b') the counting half of the elimination guard, at the container bit
  the walk read or'ed with every checked outside major -/
  small : 0 < p.k ∧
    (blockLargeElimAllowed p (nested || tys.any (fun t => t.2.1.member.isNone)) = true ∨
    ∀ u ∈ tys.map (·.2.2), Level.isEquiv u Level.zero = some true)
  /-- (b') the elimination-level pin -/
  pin : ∀ u ∈ tys.map (·.2.2), Level.isEquiv u (structElimLevel p.elim p.large) = some true
  /-- (b') the shared rule prefix -/
  prefixAgree : checkBlockRecPrefixAgree (fueledOps mode F) fe.env p (tys.map (·.1)) = .ok ()
  /-- the rule pins at the majors -/
  rulePins : targetRulePinsAll (m := CheckM) tys (targetRecRules block) = .ok ()
  /-- the rule counts -/
  rhssLen : targetRhssLen (m := CheckM) p.recs tys = .ok ()
  /-- the elimination guard's per-recursor half, at the walk's bit -/
  elims : targetRecElims (fueledOps mode F) fe p nested p.recs tys = .ok ()
  /-- the major → node tie -/
  ties : targetTies (fueledOps mode F) fe.env p (cvTas.map (·.type)) keys tys = .ok ()
  /-- every hook output a hook run's -/
  doneOk : ∀ x ∈ done, HookOut (targetHook (ShadowOps.fueled mode F) fe
    (consBlockRecsBareF p 0 (tys.map fun t => (t.1, t.2.1.nIdx)) fe) p (cvTas.map (·.type))
    (targetFamilyOf p tys) p.recs tys) x
  /-- (c) the family, read off the hook's outputs -/
  outOf : targetOutOf (m := CheckM) done 0 tys = .ok out

/-- **Every recursor's rules**, read off the run: at every position the
stored entry keeps stage (b)'s constant and major, its rules cover the
major's constructors and are a `TargetRulesRun`. -/
theorem TargetRecRun.rules {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    out.length = min p.recs.length R.tys.length ∧
      ∀ (i : Nat) (rc : RecShape) (t : ConstantVal × TargetMajor × Level),
        p.recs[i]? = some rc → R.tys[i]? = some t →
        ∃ rhssA, out[i]? = some (t.1, t.2.1, rhssA) ∧
          rc.rhss.length = t.2.1.ctors.length ∧
          TargetRulesRun mode F (consBlockRecsBareF p 0 (R.tys.map fun t => (t.1, t.2.1.nIdx)) fe)
            fe p (cvTas.map (·.type)) (targetFamilyOf p R.tys) t.1 rc.rP t.2.1 t.2.1.ctors rc.rhss
            rhssA := by
  obtain ⟨hlenO, hallO⟩ := targetOutOf_run R.outOf
  have hlenT : R.tys.length = p.recs.length := by
    clear hallO hlenO
    have := R.htys
    generalize p.recs = recs at this
    generalize R.tys = tys at this
    induction recs generalizing tys with
    | nil => simp only [targetRecTys, pure, Except.pure, Except.ok.injEq] at this; subst this; rfl
    | cons rc rcs ih =>
      unfold targetRecTys at this
      obtain ⟨t, -, h⟩ := exceptBind_ok this
      obtain ⟨ts, hts, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [ih ts hts]
  refine ⟨by rw [hlenO, hlenT, Nat.min_self], fun i rc t hrc ht => ?_⟩
  obtain ⟨rhssA, hout, hl, hdone⟩ := hallO i t ht
  have hrl := targetRhssLen_run R.rhssLen i rc t hrc ht
  refine ⟨rhssA, hout, hrl, hl, by rw [hrl], fun j cA rhs hcA hrhs => ?_⟩
  obtain ⟨o, ho⟩ : ∃ o, rhssA[j]? = some o := by
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    rw [hl]; exact (List.getElem?_eq_some_iff.mp hcA).1
  have hmem := hdone j o ho
  obtain ⟨rc', t', h1, h2, cA', rhs', ety, h3, h4, h5⟩ := targetHook_out (R.doneOk _ hmem)
  simp only [Nat.zero_add] at h1 h2 h3 h4 h5
  rw [hrc] at h1; obtain rfl := Option.some.inj h1
  rw [ht] at h2; obtain rfl := Option.some.inj h2
  rw [hcA] at h3; obtain rfl := Option.some.inj h3
  rw [hrhs] at h4; obtain rfl := Option.some.inj h4
  exact ⟨o, ety, ho, h5⟩

/-- **The target recursor check, inverted** — the ONE unfolding of
`targetRecCheck`: its record at the walk's container bit, and the walk's
own run (positivity with the hook), its node classes and hook outputs
the record's. -/
theorem targetRecCheck_run {fe₁ : FEnv} {env₁ : Env} {fe : FEnv} {p : BlockParts}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {F : Nat}
    (h : targetRecCheck (ShadowOps.fueled mode F) fe₁ env₁ fe p block cvTas ctorsAs
      = .ok (out, kinds, nfs)) :
    ∃ R : TargetRecRun mode F fe p.toBlockShape (blockNestedBit p.toBlockShape kinds) block cvTas
        ctorsAs out,
      checkBlockPositivity (fueledOps mode F) env₁ fe₁.find? env₁.consts p cvTas ctorsAs
        (targetHook (ShadowOps.fueled mode F) fe
          (consBlockRecsBareF p.toBlockShape 0 (R.tys.map fun t => (t.1, t.2.1.nIdx)) fe)
          p.toBlockShape (cvTas.map (·.type)) (targetFamilyOf p.toBlockShape R.tys)
          p.toBlockShape.recs R.tys) = .ok (kinds, nfs, R.keys, R.done) := by
  unfold targetRecCheck at h
  simp only [ShadowOps.fueled, ShadowOps.ofOps] at h
  obtain ⟨u0, hpins, h⟩ := exceptBind_ok h
  obtain ⟨tys, htys, h⟩ := exceptBind_ok h
  obtain ⟨u2, hpin, h⟩ := exceptBind_ok h
  obtain ⟨u3, hpref, h⟩ := exceptBind_ok h
  obtain ⟨u4, hrp, h⟩ := exceptBind_ok h
  obtain ⟨u5, hrl, h⟩ := exceptBind_ok h
  obtain ⟨u6, -, h⟩ := exceptBind_ok h
  obtain ⟨⟨kinds', nfs', keys, dn⟩, hpos, h⟩ := exceptBind_ok h
  obtain ⟨u7, -, h⟩ := exceptBind_ok h
  obtain ⟨u8, hel, h⟩ := exceptBind_ok h
  obtain ⟨u9, hsmall, h⟩ := exceptBind_ok h
  obtain ⟨u10, hties, h⟩ := exceptBind_ok h
  obtain ⟨out', hout, h⟩ := exceptBind_ok h
  obtain ⟨u11, -, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases u0; cases u2; cases u3; cases u4; cases u5; cases u8; cases u9; cases u10
  exact ⟨⟨tys, keys, dn, hpins, htys, checkBlockRecSmallElim_inv hsmall,
    checkBlockRecElimPin_inv hpin, hpref, hrp, hrl, hel, hties, checkBlockPositivity_done hpos,
    hout⟩, hpos⟩

/-! ## Facts of a run, shared by the stage record and the model -/

section RunFacts

variable {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
  {block : List ConstantInfo}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

/-- `instPisWith` is `instPisAt`'s residual. -/
theorem instPisWith_eq_instPisAt :
    ∀ (as : List Expr) (e : Expr), instPisWith as e = (Expr.instPisAt as e).map (·.2)
  | [], e => by simp [instPisWith, Expr.instPisAt]
  | a :: as, e => by
    cases e with
    | forallE dom body bm =>
      simp only [instPisWith, Expr.instPisAt, Option.map_map]
      rw [instPisWith_eq_instPisAt as]
      cases Expr.instPisAt as (body.instantiate1 a) <;> rfl
    | _ => simp [instPisWith, Expr.instPisAt]

theorem targetRecRun_out_fst
    (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    out.map (fun t => (t.1, t.2.1)) = R.tys.map (fun t => (t.1, t.2.1)) := by
  obtain ⟨hlenT, -⟩ := targetRecTys_run R.htys R.elims
  obtain ⟨hlenO, hall⟩ := R.rules
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_map]
  by_cases hk : k < p.recs.length
  · obtain ⟨rc, hrc⟩ : ∃ rc, p.recs[k]? = some rc := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨t, ht⟩ : ∃ t, R.tys[k]? = some t :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenT]; exact hk)⟩
    obtain ⟨rhssA, ho, -, -⟩ := hall k rc t hrc ht
    rw [ho, ht]
    rfl
  · rw [List.getElem?_eq_none (by rw [hlenO]; omega),
      List.getElem?_eq_none (by rw [hlenT]; omega)]
    rfl

/-- **THE MAJOR → NODE TIE, the recursor half**: every outside major of the
checked family MATCHES one of the classes of the positivity walk's nodes
(`R.keys`, `targetClassMatch`). -/
theorem TargetRecRun.tie (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    ∀ o ∈ out, o.2.1.member = none → ∃ k ∈ R.keys, k.cname = o.2.1.ind ∧
      targetClassMatch (fueledOps mode F) fe.env p (cvTas.map (·.type)) o.2.1.pfvs o.2.1.lvls
        o.2.1.ds k.lvls k.ds = .ok true := by
  intro o ho hM
  have hmem : (o.1, o.2.1) ∈ R.tys.map (fun t => (t.1, t.2.1)) := by
    rw [← targetRecRun_out_fst R]; exact List.mem_map_of_mem ho
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at hte
  have := targetTies_run R.ties t ht (by rw [hte.2]; exact hM)
  rwa [hte.2] at this

theorem targetRecRun_bare_eq
    (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    R.tys.map (fun t => (t.1, t.2.1.nIdx)) = (tgtRs out).map (fun r => (r.1, r.2.2.1)) := by
  have h0 := targetRecRun_out_fst R
  have h1 : out.map (fun t => (t.1, t.2.1.nIdx)) = R.tys.map (fun t => (t.1, t.2.1.nIdx)) := by
    have := congrArg (List.map fun q : ConstantVal × TargetMajor => (q.1, q.2.nIdx)) h0
    simpa [List.map_map, Function.comp_def] using this
  simp only [tgtRs, List.map_map, Function.comp_def]
  rw [← h1]

/-- A member major's parameters are the recursor type's first `nP`
openers. -/
theorem TargetTyEntry.ds_eq_of {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member.isSome = true) :
    M.ds = E.fvs.take p.nP := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, major, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _⟩ := E
  cases major with
  | member I t ms ctorsA hfn ht hms hctors hpar => rfl
  | outside => exact nomatch hM

/-- Opening fewer binders opens a prefix of the same variables. -/
theorem openPisAtFvars_prefix :
    ∀ (k n : Nat) (e : Expr) (d : Nat) {fvs : List Expr} {o : Expr}, k ≤ n →
      openPisAtFvars n e d = some (fvs, o) →
      ∃ o', openPisAtFvars k e d = some (fvs.take k, o')
  | 0, _, e, _, _, _, _, _ => ⟨e, rfl⟩
  | k + 1, 0, _, _, _, _, hk, _ => absurd hk (by omega)
  | k + 1, n + 1, e, d, fvs, o, hk, h => by
    cases e with
    | forallE dom body bm =>
      simp only [openPisAtFvars] at h ⊢
      split at h
      · next fvs' e' h' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨o', ho'⟩ := openPisAtFvars_prefix k n _ (d + 1) (by omega) h'
        rw [ho']
        exact ⟨o', by simp⟩
      · exact nomatch h
    | _ => simp [openPisAtFvars] at h

/-- A member major's parameter count and levels are the block's. -/
theorem targetTyEntry_major_of {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member.isSome = true) :
    M.nPc = p.nP ∧ M.lvls = p.lps.map .param := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, major, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _⟩ := E
  cases major with
  | member I t ms ctorsA hfn ht hms hctors hpar => exact ⟨rfl, rfl⟩
  | outside => exact nomatch hM


end RunFacts

/-- **The recursor stage, read back to the target check**:
`checkBlockRecT` at the fueled operations is `targetRecCheck` at
`ShadowOps.fueled` on the constructors' index, its walk at the formers'. -/
theorem checkBlockRecT_run {env env₁ : Env} {p : BlockParts} {block : List ConstantInfo}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {r : List (ConstantVal × TargetMajor × List Expr) × List (List (List NestFieldKind)) ×
      List (List Expr)} {F : Nat}
    (h : checkBlockRecT (fueledOps mode F) env env₁ p block cvTas ctorsAs = .ok r) :
    targetRecCheck (ShadowOps.fueled mode F) (mkFEnv env₁) env₁ (mkFEnv env) p block cvTas
        ctorsAs = .ok r :=
  h

end ConLeche
