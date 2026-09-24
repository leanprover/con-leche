module

public import ConLeche.Kernel.Inductives.BlockTail
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.ExceptBind

public section

/-!
# The TARGET recursor check's RUN RECORDS (lane RECLIB, Phase B's first brick)

ONE inversion per stage of the classification-free recursor check
(`ConLeche/Kernel/Inductives/RecCheck.lean`, `targetRecCheck`), each
returning a record with NAMED fields — INVERT's pattern
(`Verify/Inductives/BlockRecRun.lean`) for the check that replaces
`checkBlockRecK`.  Every proof about the recursor stage is to read
these records and never unfold a stage.

| stage | kernel function | record / inversion |
|---|---|---|
| the major | `targetMajorOf` | `TargetMajorRun` / `targetMajorOf_run` |
| the index domains | `targetIdxDoms` | `targetIdxDoms_member` |
| (b) one recursor's type | `targetRecTy` | `TargetTyEntry` / `targetRecTy_run` |
| (b) every recursor's type | `targetRecTys` | `targetRecTys_run` |
| (c) one call's typing | `targetCallOk` | `TargetCallRun` / `targetCallOk_run` |
| (c) every call's typing | `targetCallsOk` | `targetCallsOk_run` |
| (c) the fields' abstract telescopes | `targetFieldNorms` | `targetFieldNorms_run` |
| (c) one rule | `targetRule` | `TargetRuleRun` / `targetRule_run` |
| (c) one recursor's rules | `targetRules` | `TargetRulesRun` / `targetRules_run` |
| (c) every recursor's rules | `targetRecsRules` | `targetRecsRules_run` |
| the whole check | `targetRecCheck` | `TargetRecRun` / `targetRecCheck_run` |

The records are stated at the fueled pure instantiation
(`ShadowOps.fueled mode F`) and the UNIFORM route's `outside = false`:
every major is a member.  **The nested extension point** (lane NESTED):
`TargetMajorRun` has ONE constructor today, `member`; the container
arm of `targetMajorOf` at `outside = true` is its second constructor,
`outside`, and `targetMajorOf_run` gains the matching case (the
`none` branch of the member lookup).  Nothing else in this file reads
which arm the major took: the entry, the rule and the call records are
stated over the resolved `TargetMajor`.
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
One constructor per arm; the uniform route (`outside = false`) has only
the member arm.  Lane NESTED adds `outside` here. -/
inductive TargetMajorRun (p : BlockShape) (ctorsAs : List (List (ConstantVal × Nat)))
    (fvs : List Expr) (mty : Expr) : TargetMajor → Type where
  /-- a MEMBER of the block, at the block's levels and parameters -/
  | member (I : Name) (t : Nat) (ms : MemberShape) (ctorsA : List (ConstantVal × Nat))
      (hfn : mty.getAppFn = .const I (p.lps.map .param))
      (ht : p.memberNames.findIdx? (· == I) = some t)
      (hms : p.members[t]? = some ms)
      (hctors : ctorsAs[t]? = some ctorsA)
      (hpar : mty.getAppArgs.take p.nP = fvs.take p.nP) :
      TargetMajorRun p ctorsAs fvs mty
        { ind := I, lvls := p.lps.map .param, ds := fvs.take p.nP, nPc := p.nP,
          nIdx := ms.nIdx, ctors := ctorsA, member := some t }

/-- **`targetMajorOf`, inverted** on the uniform route. -/
theorem targetMajorOf_run {fe : FEnv} {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {fvs : List Expr} {mty : Expr}
    {M : TargetMajor}
    (h : targetMajorOf (m := CheckM) fe p false ctorsAs fvs mty = .ok M) :
    Nonempty (TargetMajorRun p ctorsAs fvs mty M) := by
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
      exact ⟨.member I t ms ctorsA hfn ht (unwrapOr_ok hms) (unwrapOr_ok hctorsA) hpar⟩
    · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      exact nomatch h
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
named, on the uniform route. -/
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
  /-- THE MAJOR, resolved (the uniform route: a member) -/
  major : TargetMajorRun p ctorsAs fvs maj.fvarTypeD M
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

namespace TargetTyEntry

variable {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape} {cvRi : ConstantVal}
  {M : TargetMajor} {u : Level}

/-- The major is a member (the uniform route). -/
theorem member (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u) :
    ∃ t ms, M.member = some t ∧ p.members[t]? = some ms ∧ M.nIdx = ms.nIdx ∧
      M.nPc = p.nP ∧ ctorsAs[t]? = some M.ctors := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, major, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _⟩ := E
  cases major with
  | member I t ms ctorsA hfn ht hms hctors hpar => exact ⟨t, ms, rfl, hms, rfl, rfl, hctors⟩

end TargetTyEntry

/-- **Stage (b) at one recursor, inverted** (uniform route). -/
theorem targetRecTy_run {fe : FEnv} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {F : Nat} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (h : targetRecTy (fueledOps mode F) fe p false nested cvTas ctorsAs rc = .ok (cvRi, M, u)) :
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
  obtain ⟨R⟩ := targetMajorOf_run hM'
  by_cases htgt : (M'.member.all (· == rc.tgt)) = true
  case neg => rw [if_neg htgt] at h; close_throw h
  rw [if_pos htgt] at h
  -- F2: the outside major's pins typed (nothing at a member)
  obtain ⟨_, -, h⟩ := exceptBind_ok h
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
  have mk : (blockLargeElimAllowed p nested = true ∨
      isDefEqCore mode fe.env F (rc.mI + 1) sty (.sort .zero) = .ok true) →
      (cvRi', M', u') = (cvRi, M, u) →
      Nonempty (TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u) := by
    intro hsmall heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨{
          cvTP := cvTP, fvs := fvs, concl := concl, tfvs := tfvs, trest := trest,
          maj := maj, idoms := idoms, sty := sty, hcv := hcv,
          hroom := hroom, hle := hle, hopen := unwrapOr_ok hx1, hmaj := unwrapOr_ok hmaj,
          major := R, htgt := htgt, hcvTP := unwrapOr_ok hcvTP, hopenT := unwrapOr_ok hx2,
          hparLen := hpl, hparams := hpall, hmI := hmI,
          hmajLen := hargs.1, hmajIdx := hargs.2, hidoms := hidoms,
          hidxLen := (by simpa using hil), hidx := fun l hl => hiall l hl, hsty := hsty,
          hu := hu', hsmall := hsmall }⟩
  by_cases hlarge : blockLargeElimAllowed p nested = true
  case pos =>
    rw [if_pos hlarge] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact mk (.inl hlarge) h
  case neg =>
    rw [if_neg hlarge] at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    by_cases hbt : b = true
    case neg => rw [if_neg hbt] at h; close_throw h
    rw [if_pos hbt] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact mk (.inr (by rw [hbt] at hb; exact hb)) h

/-- **Stage (b) at every recursor, inverted**: one entry per recursor. -/
theorem targetRecTys_run {fe : FEnv} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat} :
    ∀ {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)},
      targetRecTys (fueledOps mode F) fe p false nested cvTas ctorsAs recs = .ok tys →
      tys.length = recs.length ∧
      ∀ (i : Nat) (rc : RecShape), recs[i]? = some rc →
        ∃ cvRi M u, tys[i]? = some (cvRi, M, u) ∧
        Nonempty (TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
  | [], tys, h => by
    simp only [targetRecTys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i rc hi => nomatch hi⟩
  | rc :: rcs, tys, h => by
    unfold targetRecTys at h
    obtain ⟨t, ht, h⟩ := exceptBind_ok h
    obtain ⟨ts, hts, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hall⟩ := targetRecTys_run hts
    refine ⟨by simp [hlen], fun i rc' hi => ?_⟩
    cases i with
    | zero =>
      obtain rfl : rc = rc' := by simpa using hi
      obtain ⟨cvRi, M, u⟩ := t
      exact ⟨cvRi, M, u, rfl, targetRecTy_run ht⟩
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
theorem targetCallOk_run {env : Env} {cn : Name} {fam : TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k F : Nat} {pw : PropWhen} {ih : TargetIh}
    (h : targetCallOk (fueledOps mode F) env cn fam fvsPref fvsF fnorm teles absM base k pw ih
      = .ok ()) :
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
theorem targetCallsOk_run {env : Env} {cn : Name} {fam : TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k F : Nat} {pw : PropWhen} :
    ∀ {ihs : List TargetIh},
      targetCallsOk (fueledOps mode F) env cn fam fvsPref fvsF fnorm teles absM base k pw ihs
        = .ok () →
      ∀ ih ∈ ihs,
        Nonempty (TargetCallRun mode F env fam fvsPref fvsF fnorm teles absM base k pw ih)
  | [], _, ih, hih => nomatch hih
  | ih0 :: ihs, h, ih, hih => by
    unfold targetCallsOk at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hih with rfl | hih
    · exact targetCallOk_run (by cases u; exact hu)
    · exact targetCallsOk_run h ih hih

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
occurrence), each call typed on the member-abstracted terms, and the
residue typed against the recursor's conclusion at the constructor. -/
structure TargetRuleRun (mode : CheckMode) (F : Nat) (feR feT : FEnv) (p : BlockShape)
    (formerTys : List Expr) (fam : TargetFamily) (cvR : ConstantVal) (rP : Nat)
    (recTy : Expr) (M : TargetMajor) (c : ConstantVal × Nat) (rhs out : Expr) : Type where
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
  hcalls : targetCallsOk (fueledOps mode F) feT.env c.1.name fam fvsPref fvsF fnorm
    (fnorm.map fun t => t.piBinders.1)
    (targetAbs p.memberNames (p.lps.map .param) (targetHoles formerTys (rP + c.2)))
    (rP + c.2) formerTys.length (Level.zeronessOf (structElimLevel p.elim p.large)) ihs.toList
    = .ok ()
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
    {c : ConstantVal × Nat} {rhs out : Expr} {F : Nat}
    (h : targetRule (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam cvR rP
      recTy M c rhs = .ok out) :
    Nonempty (TargetRuleRun mode F feR feT p formerTys fam cvR rP recTy M c rhs out) := by
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
          hcalls := hcalls, hty := hty, hconcl := unwrapOr_ok hconcl, hdeq := hb }⟩

/-! ## Stage (c): one recursor's rules, and every recursor's -/

/-- **One recursor's rules**: one stored rule per constructor of its
major and per stream right-hand side, each a `targetRule` run. -/
structure TargetRulesRun (mode : CheckMode) (F : Nat) (feR feT : FEnv) (p : BlockShape)
    (formerTys : List Expr) (fam : TargetFamily) (cvRi : ConstantVal) (rP : Nat)
    (M : TargetMajor) (cs : List (ConstantVal × Nat)) (rhss out : List Expr) : Prop where
  len : out.length = cs.length
  lenRhs : rhss.length = cs.length
  rule : ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr), cs[j]? = some cA →
    rhss[j]? = some rhs → ∃ o, out[j]? = some o ∧
      targetRule (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam cvRi rP
        cvRi.type M cA rhs = .ok o

/-- **One recursor's rules, inverted.** -/
theorem targetRules_run {feR feT : FEnv} {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {cvRi : ConstantVal} {rP : Nat} {M : TargetMajor} {F : Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {rhss out : List Expr},
      targetRules (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam cvRi rP M
        cs rhss = .ok out →
      TargetRulesRun mode F feR feT p formerTys fam cvRi rP M cs rhss out
  | [], [], out, h => by
    simp only [targetRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, fun j cA rhs hq _ => nomatch hq⟩
  | [], _ :: _, out, h => by unfold targetRules at h; close_throw h
  | _ :: _, [], out, h => by unfold targetRules at h; close_throw h
  | cA0 :: cs, rhs0 :: rhss, out, h => by
    unfold targetRules at h
    obtain ⟨o0, ho0, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hlenR, hall⟩ := targetRules_run hrest
    refine ⟨by simp [hlen], by simp [hlenR], fun j cA rhs hq hrhs => ?_⟩
    cases j with
    | zero =>
      obtain rfl := Option.some.inj hq
      obtain rfl := Option.some.inj hrhs
      exact ⟨o0, rfl, ho0⟩
    | succ j =>
      obtain ⟨o, ho, hrun⟩ := hall j cA rhs (by simpa using hq) (by simpa using hrhs)
      exact ⟨o, by simpa using ho, hrun⟩

/-- **Every recursor's rules, inverted**: at every position the stored
entry keeps stage (b)'s constant and major, its rules cover the
major's constructors and are a `TargetRulesRun`. -/
theorem targetRecsRules_run {feR feT : FEnv} {p : BlockShape} {formerTys : List Expr}
    {fam : TargetFamily} {F : Nat} :
    ∀ {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)}
      {out : List (ConstantVal × TargetMajor × List Expr)},
      targetRecsRules (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam
        recs tys = .ok out →
      out.length = min recs.length tys.length ∧
      ∀ (i : Nat) (rc : RecShape) (t : ConstantVal × TargetMajor × Level),
        recs[i]? = some rc → tys[i]? = some t →
        ∃ rhssA, out[i]? = some (t.1, t.2.1, rhssA) ∧
          rc.rhss.length = t.2.1.ctors.length ∧
          TargetRulesRun mode F feR feT p formerTys fam t.1 rc.rP t.2.1 t.2.1.ctors rc.rhss
            rhssA
  | [], _, out, h => by
    simp only [targetRecsRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨by simp, fun i rc t hi => nomatch hi⟩
  | _ :: _, [], out, h => by
    simp only [targetRecsRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨by simp, fun i rc t _ ht => nomatch ht⟩
  | rc0 :: rcs, (cvRi, M, u) :: ts, out, h => by
    unfold targetRecsRules at h
    by_cases hlen : (rc0.rhss.length == M.ctors.length) = true
    case neg => rw [if_neg hlen] at h; close_throw h
    rw [if_pos hlen] at h
    obtain ⟨rhssA, hrules, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hall⟩ := targetRecsRules_run hrest
    refine ⟨by simp [hl, Nat.succ_min_succ], fun i rc t hi ht => ?_⟩
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      obtain rfl := Option.some.inj ht
      exact ⟨rhssA, rfl, beq_iff_eq.mp hlen, targetRules_run hrules⟩
    | succ i =>
      obtain ⟨r, hr, hl', R⟩ := hall i rc t (by simpa using hi) (by simpa using ht)
      exact ⟨r, by simpa using hr, hl', R⟩

/-! ## The whole CHECK -/

/-- **The target recursor check, as run** (uniform route): the pins, the
recursors' types (`tys`), the family's agreements, the rule pins, and
the rules at the environment holding the rule-less recursors. -/
structure TargetRecRun (mode : CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape)
    (nested : Bool) (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × TargetMajor × List Expr)) : Type where
  /-- stage (b)'s list -/
  tys : List (ConstantVal × TargetMajor × Level)
  /-- (a) the records' pins -/
  pins : targetRecPins (m := CheckM) p block = .ok ()
  /-- (b) every recursor's type -/
  htys : targetRecTys (fueledOps mode F) fe p false nested cvTas ctorsAs p.recs = .ok tys
  /-- (b') the counting half of the elimination guard, at the container bit
  the caller read or'ed with every checked outside major (F4) -/
  small : 0 < p.k ∧
    (blockLargeElimAllowed p (nested || tys.any (fun t => t.2.1.member.isNone)) = true ∨
    ∀ u ∈ tys.map (·.2.2), Level.isEquiv u Level.zero = some true)
  /-- (b') the elimination-level pin -/
  pin : ∀ u ∈ tys.map (·.2.2), Level.isEquiv u (structElimLevel p.elim p.large) = some true
  /-- (b') the shared rule prefix -/
  prefixAgree : checkBlockRecPrefixAgree (fueledOps mode F) fe.env p (tys.map (·.1)) = .ok ()
  /-- the rule pins at the majors -/
  rulePins : targetRulePinsAll (m := CheckM) tys (targetRecRules block) = .ok ()
  /-- (c) every recursor's rules -/
  rules : targetRecsRules (fueledOps mode F) .plain
    (consBlockRecsBareF p 0 (tys.map fun t => (t.1, t.2.1.nIdx)) fe) (fueledOps mode F) fe p
    (cvTas.map (·.type)) (targetFamilyOf p tys) p.recs tys = .ok out

/-- **The target recursor check, inverted** — the ONE unfolding of
`targetRecCheck` (uniform route). -/
theorem targetRecCheck_run {fe : FEnv} {p : BlockShape} {nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : targetRecCheck (ShadowOps.fueled mode F) fe p false nested block cvTas ctorsAs
      = .ok out) :
    Nonempty (TargetRecRun mode F fe p nested block cvTas ctorsAs out) := by
  unfold targetRecCheck at h
  obtain ⟨u0, hpins, h⟩ := exceptBind_ok h
  obtain ⟨tys, htys, h⟩ := exceptBind_ok h
  obtain ⟨u1, hsmall, h⟩ := exceptBind_ok h
  obtain ⟨u2, hpin, h⟩ := exceptBind_ok h
  obtain ⟨u3, hpref, h⟩ := exceptBind_ok h
  obtain ⟨u4, hrp, h⟩ := exceptBind_ok h
  obtain ⟨out', hrules, h⟩ := exceptBind_ok h
  obtain ⟨u5, -, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨{ tys := tys, pins := by cases u0; exact hpins, htys := htys,
           small := checkBlockRecSmallElim_inv (by cases u1; exact hsmall),
           pin := checkBlockRecElimPin_inv (by cases u2; exact hpin),
           prefixAgree := by cases u3; exact hpref, rulePins := by cases u4; exact hrp,
           rules := hrules }⟩

/-! ## Facts of a run, shared by the stage record and the model -/

section RunFacts

variable {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool} {block : List ConstantInfo}
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

theorem targetRecRun_out_fst (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    out.map (fun t => (t.1, t.2.1)) = R.tys.map (fun t => (t.1, t.2.1)) := by
  obtain ⟨hlenT, -⟩ := targetRecTys_run R.htys
  obtain ⟨hlenO, hall⟩ := targetRecsRules_run R.rules
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

theorem targetRecRun_bare_eq (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    R.tys.map (fun t => (t.1, t.2.1.nIdx)) = (tgtRs out).map (fun r => (r.1, r.2.2.1)) := by
  have h0 := targetRecRun_out_fst R
  have h1 : out.map (fun t => (t.1, t.2.1.nIdx)) = R.tys.map (fun t => (t.1, t.2.1.nIdx)) := by
    have := congrArg (List.map fun q : ConstantVal × TargetMajor => (q.1, q.2.nIdx)) h0
    simpa [List.map_map, Function.comp_def] using this
  simp only [tgtRs, List.map_map, Function.comp_def]
  rw [← h1]

/-- A member major's parameters are the recursor type's first `nP`
openers. -/
theorem TargetTyEntry.ds_eq {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u) :
    M.ds = E.fvs.take p.nP := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, major, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _⟩ := E
  cases major with
  | member I t ms ctorsA hfn ht hms hctors hpar => rfl

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

/-- **The major's parameters are the rule prefix's first `nP` openers**:
both openings start at the recursor's stored type, and `nP ≤ rP ≤ mI`. -/
theorem targetDs_eq_prefTake {F : Nat} {fe : FEnv} {p : BlockShape}
    {nested : Bool} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rc : RecShape} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
    {fvsPref : List Expr} {oP : Expr}
    (hpref : openPisAtFvars rc.rP cvRi.type 0 = some (fvsPref, oP)) :
    M.ds = fvsPref.take p.nP := by
  rw [TargetTyEntry.ds_eq E]
  obtain ⟨o', ho'⟩ := openPisAtFvars_prefix rc.rP (rc.mI + 1) _ 0 (by have := E.hle; omega) E.hopen
  rw [hpref] at ho'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj ho')
  rw [List.take_take, Nat.min_eq_left E.hroom]

/-- A member major's parameter count and levels are the block's. -/
theorem targetTyEntry_major {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u) :
    M.nPc = p.nP ∧ M.lvls = p.lps.map .param := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, major, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _⟩ := E
  cases major with
  | member I t ms ctorsA hfn ht hms hctors hpar => exact ⟨rfl, rfl⟩

end RunFacts

/-- **The uniform route's recursor stage, read back to the target check**:
`checkBlockRecT` at the fueled operations is `targetRecCheck` at
`ShadowOps.fueled` on the constructors' index, its result `tgtRs` of the
check's output. -/
theorem checkBlockRecT_run {env : Env} {p : BlockParts} {block : List ConstantInfo}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : checkBlockRecT (fueledOps mode F) env p block cvTas ctorsAs = .ok rs) :
    ∃ out, targetRecCheck (ShadowOps.fueled mode F) (mkFEnv env) p.toBlockShape false false
        block cvTas ctorsAs = .ok out ∧ rs = tgtRs out := by
  unfold checkBlockRecT at h
  obtain ⟨out, hout, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨out, hout, h.symm⟩

end ConLeche
