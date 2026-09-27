module

public import ConLeche.Kernel.Inductives.BlockTail
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
    (ctorsAs : List (List (ConstantVal × Nat))) (fvs : List Expr) (mty : Expr) :
    TargetMajor → Type where
  /-- a MEMBER of the block, at the block's levels and parameters -/
  | member (I : Name) (t : Nat) (ms : MemberShape) (ctorsA : List (ConstantVal × Nat))
      (hfn : mty.getAppFn = .const I (p.lps.map .param))
      (ht : p.memberNames.findIdx? (· == I) = some t)
      (hms : p.members[t]? = some ms)
      (hctors : ctorsAs[t]? = some ctorsA)
      (hpar : mty.getAppArgs.take p.nP = fvs.take p.nP) (nfs : Option (List NestCtorNf))
      (hnf : Option (List NestCtorNf)) :
      TargetMajorRun fe p ctorsAs fvs mty
        { ind := I, lvls := p.lps.map .param, ds := fvs.take p.nP, nPc := p.nP,
          nIdx := ms.nIdx, ctors := ctorsA, member := some t, sort := p.resSort, nfs := nfs,
          home := p.memberNames, homeNfs := hnf }
  /-- an OUTSIDE inductive (a nested block's container), at its own
  levels `us` and parameters `ds` (the major type's first `nPc`
  arguments, mentioning only the recursor's parameter binders), in its
  own universe `sI` -/
  | outside (I : Name) (us : List Level) (nPc nIdx : Nat) (ctors : List (ConstantVal × Nat))
      (sI : Level)
      (hfn : mty.getAppFn = .const I us)
      (hnq : I ≠ quotName)
      (hctors : targetCtorsOf fe I = some (nPc, ctors))
      (hdsLen : (mty.getAppArgs.take nPc).length = nPc)
      (hdsSc : ∀ x ∈ mty.getAppArgs.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ p.nP)
      (hinst : targetOutsideInst (m := CheckM) fe I us (mty.getAppArgs.take nPc)
        = .ok (nIdx, sI)) (nfs : Option (List NestCtorNf)) (hnf : Option (List NestCtorNf)) :
      TargetMajorRun fe p ctorsAs fvs mty
        { ind := I, lvls := us, ds := mty.getAppArgs.take nPc, nPc := nPc, nIdx := nIdx,
          ctors := ctors, member := none, sort := sI, nfs := nfs,
          home := match fe.find? I with
            | some (.indInfo _ caps) => caps.all
            | _ => [],
          homeNfs := hnf }

/-- **`targetOutsideMajorOf`, inverted.** -/
theorem targetOutsideMajorOf_inv {fe : FEnv} {p : BlockShape} {aux : Option NestNodes}
    {I : Name} {us : List Level} {args : List Expr} {M : TargetMajor}
    {hnf : Option (List NestCtorNf)}
    (h : targetOutsideMajorOf (m := CheckM) fe p aux I us args hnf = .ok M) :
    ∃ nPc nIdx ctors sI, I ≠ quotName ∧ targetCtorsOf fe I = some (nPc, ctors) ∧
      (args.take nPc).length = nPc ∧
      (∀ x ∈ args.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ p.nP) ∧
      (aux.all fun a => !p.memberNames.contains I &&
        (args.take nPc).any (fun x => x.nestOcc p.memberNames 0 0) &&
        a.keys.contains ⟨I, us, args.take nPc⟩) = true ∧
      targetOutsideInst (m := CheckM) fe I us (args.take nPc) = .ok (nIdx, sI) ∧
      M = { ind := I, lvls := us, ds := args.take nPc, nPc := nPc, nIdx := nIdx, ctors := ctors,
            member := none, sort := sI,
            nfs := aux.map (targetMajorNfs · us (args.take nPc)),
            home := match fe.find? I with
              | some (.indInfo _ caps) => caps.all
              | _ => [],
            homeNfs := hnf } := by
  unfold targetOutsideMajorOf at h
  simp only at h
  split at h
  · close_throw h
  · next hq =>
    split at h
    · next nPc ctors hct =>
      split at h
      · next hds =>
        split at h
        case isFalse => close_throw h
        next haux =>
        obtain ⟨⟨nIdx, sI⟩, hinst, h⟩ := exceptBind_ok h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hds
        exact ⟨nPc, nIdx, ctors, sI, by simpa using hq, hct, hds.1,
          fun x hx => by simpa using hds.2 x hx, haux, hinst, rfl⟩
      · close_throw h
    · close_throw h

/-- **`targetMajorOf`'s two arms**: a member at the block's levels and
parameters, or `targetOutsideMajorOf` at the major's head. -/
theorem targetMajorOf_cases {fe : FEnv} {p : BlockShape} {aux : Option NestNodes}
    {ctorsAs : List (List (ConstantVal × Nat))} {fvs : List Expr} {mty : Expr}
    {M : TargetMajor} {hnf : Option (List NestCtorNf)}
    (h : targetMajorOf (m := CheckM) fe p aux ctorsAs fvs mty hnf = .ok M) :
    (∃ I t ms ctorsA, mty.getAppFn = .const I (p.lps.map .param) ∧
      p.memberNames.findIdx? (· == I) = some t ∧ p.members[t]? = some ms ∧
      ctorsAs[t]? = some ctorsA ∧ mty.getAppArgs.take p.nP = fvs.take p.nP ∧
      M = { ind := I, lvls := p.lps.map .param, ds := fvs.take p.nP, nPc := p.nP,
            nIdx := ms.nIdx, ctors := ctorsA, member := some t, sort := p.resSort,
            nfs := aux.map (targetMajorNfs · (p.lps.map .param) (fvs.take p.nP)),
            home := p.memberNames, homeNfs := hnf }) ∨
    (∃ I us, mty.getAppFn = .const I us ∧
      targetOutsideMajorOf (m := CheckM) fe p aux I us mty.getAppArgs hnf = .ok M) := by
  unfold targetMajorOf at h
  simp only at h
  split at h
  · next I us hfn =>
    split at h
    · next t ht =>
      split at h
      · next hc =>
        obtain ⟨ms, hms, h⟩ := exceptBind_ok h
        obtain ⟨ctorsA, hctorsA, h⟩ := exceptBind_ok h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, hpar⟩ := hc
        exact Or.inl ⟨I, t, ms, ctorsA, hfn, ht, unwrapOr_ok hms, unwrapOr_ok hctorsA, hpar, rfl⟩
      · exact Or.inr ⟨I, us, hfn, h⟩
    · exact Or.inr ⟨I, us, hfn, h⟩
  · close_throw h

/-- **`targetMajorOf`, inverted.** -/
theorem targetMajorOf_run {fe : FEnv} {p : BlockShape} {aux : Option NestNodes}
    {ctorsAs : List (List (ConstantVal × Nat))} {fvs : List Expr} {mty : Expr}
    {M : TargetMajor} {hnf : Option (List NestCtorNf)}
    (h : targetMajorOf (m := CheckM) fe p aux ctorsAs fvs mty hnf = .ok M) :
    Nonempty (TargetMajorRun fe p ctorsAs fvs mty M) := by
  rcases targetMajorOf_cases h with
    ⟨I, t, ms, ctorsA, hfn, ht, hms, hctorsA, hpar, rfl⟩ | ⟨I, us, hfn, h⟩
  · exact ⟨.member I t ms ctorsA hfn ht hms hctorsA hpar _ _⟩
  · obtain ⟨nPc, nIdx, ctors, sI, hq, hct, hl, hsc, -, hinst, rfl⟩ :=
      targetOutsideMajorOf_inv h
    exact ⟨.outside I us nPc nIdx ctors sI hfn hq hct hl hsc hinst _ _⟩

/-- **An outside major is an auxiliary type of the block** where the family
is checked against the walk (`aux = some a`, `targetLegacyAux`): it is not
a member, some parameter names a member (official's `is_nested`) and `a`
holds its instantiation. -/
theorem targetMajorOf_legacy {fe : FEnv} {p : BlockShape} {a : NestNodes}
    {ctorsAs : List (List (ConstantVal × Nat))} {fvs : List Expr} {mty : Expr}
    {M : TargetMajor} {hnf : Option (List NestCtorNf)}
    (h : targetMajorOf (m := CheckM) fe p (some a) ctorsAs fvs mty hnf = .ok M)
    (hM : M.member = none) :
    M.ind ∉ p.memberNames ∧ (∃ x ∈ M.ds, x.nestOcc p.memberNames 0 0 = true) ∧
      a.keys.contains ⟨M.ind, M.lvls, M.ds⟩ = true := by
  rcases targetMajorOf_cases h with hmem | hout
  · obtain ⟨_, _, _, _, _, _, _, _, _, hMe⟩ := hmem
    rw [hMe] at hM
    exact nomatch hM
  · obtain ⟨I, us, -, h⟩ := hout
    obtain ⟨nPc, nIdx, ctors, sI, -, -, -, -, haux, -, hMe⟩ := targetOutsideMajorOf_inv h
    subst hMe
    simp only [Option.all_some, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, decide_eq_true_eq, List.any_eq_true] at haux
    exact ⟨haux.1.1, haux.1.2, by simpa using haux.2⟩

/-- **The major's recorded normal forms** (K.53′): the walk's entries at
the major's levels and parameters (`targetMajorNfs`). -/
theorem targetMajorOf_nfs {fe : FEnv} {p : BlockShape} {aux : Option NestNodes}
    {ctorsAs : List (List (ConstantVal × Nat))} {fvs : List Expr} {mty : Expr}
    {M : TargetMajor} {hnf : Option (List NestCtorNf)}
    (h : targetMajorOf (m := CheckM) fe p aux ctorsAs fvs mty hnf = .ok M) :
    M.nfs = aux.map (targetMajorNfs · M.lvls M.ds) := by
  rcases targetMajorOf_cases h with hmem | hout
  · obtain ⟨_, _, _, _, _, _, _, _, _, hMe⟩ := hmem
    subst hMe; rfl
  · obtain ⟨I, us, _, h⟩ := hout
    obtain ⟨nPc, nIdx, ctors, sI, _, _, _, _, _, _, hMe⟩ := targetOutsideMajorOf_inv h
    subst hMe; rfl

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
  major : TargetMajorRun fe p ctorsAs fvs maj.fvarTypeD M
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
  /-- the elimination restriction's per-recursor half: the major's
  own licence (`targetMajorLicensed`) -/
  hsmall : targetMajorLicensed fe p nested M = true ∨
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
and ends in the major's universe `M.sort`. -/
theorem outside_of (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member = none) :
    ∃ sI, E.maj.fvarTypeD.getAppFn = .const M.ind M.lvls ∧ M.ind ≠ quotName ∧
      targetCtorsOf fe M.ind = some (M.nPc, M.ctors) ∧
      M.ds = E.maj.fvarTypeD.getAppArgs.take M.nPc ∧ M.ds.length = M.nPc ∧
      (∀ x ∈ M.ds, x.bvarB = 0 ∧ x.fvarB ≤ p.nP) ∧
      targetOutsideInst (m := CheckM) fe M.ind M.lvls M.ds = .ok (M.nIdx, sI) ∧
      sI = M.sort := by
  obtain ⟨_, _, _, _, _, _, maj, _, _, _, _, _, _, major, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _⟩ := E
  cases major with
  | member => exact nomatch hM
  | outside I us nPc nIdx ctors sI hfn hnq hct hl hsc hinst =>
    exact ⟨sI, hfn, hnq, hct, rfl, hl, hsc, hinst, rfl⟩

/-- An outside major's home is its recorded block (`IndCaps.all`). -/
theorem home_of (E : TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member = none) :
    M.home = match fe.find? M.ind with
      | some (.indInfo _ caps) => caps.all
      | _ => [] := by
  obtain ⟨_, _, _, _, _, _, maj, _, _, _, _, _, _, major, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _⟩ := E
  cases major with
  | member => exact nomatch hM
  | outside I us nPc nIdx ctors sI hfn hnq hct hl hsc hinst => rfl

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

/-- **Stage (b) at one recursor, inverted.** -/
theorem targetRecTy_run {fe : FEnv} {p : BlockShape} {nested : Bool}
    {aux : Option NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {F : Nat} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    {hnf : Option (List NestCtorNf)}
    (h : targetRecTy (fueledOps mode F) fe p nested aux cvTas ctorsAs rc hnf
      = .ok (cvRi, M, u)) :
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
  have mk : (targetMajorLicensed fe p nested M' = true ∨
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
          hu := hu', hsmall := hsmall, hpinTys := by cases u0; exact hpinTys }⟩
  by_cases hlarge : targetMajorLicensed fe p nested M' = true
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

/-- **Stage (b) at one recursor: the stored major is `targetMajorOf`'s.** -/
theorem targetRecTy_majorOf {fe : FEnv} {p : BlockShape} {nested : Bool}
    {aux : Option NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {F : Nat} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    {hnf : Option (List NestCtorNf)}
    (h : targetRecTy (fueledOps mode F) fe p nested aux cvTas ctorsAs rc hnf
      = .ok (cvRi, M, u)) :
    ∃ fvs mty, targetMajorOf (m := CheckM) fe p aux ctorsAs fvs mty hnf = .ok M := by
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
  suffices hMM : M' = M by subst hMM; exact ⟨_, _, hM'⟩
  by_cases htgt : (M'.member.all (· == rc.tgt)) = true
  case neg => rw [if_neg htgt] at h; close_throw h
  rw [if_pos htgt] at h
  obtain ⟨u0, hpinTys, h⟩ := exceptBind_ok h
  obtain ⟨cvTP, hcvTP, h⟩ := exceptBind_ok h
  obtain ⟨x2, hx2, h⟩ := exceptBind_ok h
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
  by_cases hlarge : targetMajorLicensed fe p nested M' = true
  case pos =>
    rw [if_pos hlarge] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.1
  case neg =>
    rw [if_neg hlarge] at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    by_cases hbt : b = true
    case neg => rw [if_neg hbt] at h; close_throw h
    rw [if_pos hbt] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.1

/-- **Stage (b): every stored major is `targetMajorOf`'s.** -/
theorem targetRecTys_majorOf {fe : FEnv} {p : BlockShape} {nested : Bool}
    {aux : Option NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat} :
    ∀ {recs : List RecShape} {hn : List (Option (List NestCtorNf))}
      {tys : List (ConstantVal × TargetMajor × Level)},
      targetRecTys (fueledOps mode F) fe p nested aux cvTas ctorsAs recs hn = .ok tys →
      ∀ t ∈ tys, ∃ fvs mty hnf, targetMajorOf (m := CheckM) fe p aux ctorsAs fvs mty hnf = .ok t.2.1
  | [], _, tys, h => by
    simp only [targetRecTys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro t ht; exact nomatch ht
  | rc :: rcs, hn, tys, h => by
    unfold targetRecTys at h
    obtain ⟨t, ht, h⟩ := exceptBind_ok h
    obtain ⟨ts, hts, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro t' ht'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · obtain ⟨cvRi, M, u⟩ := t'
      obtain ⟨fvs, mty, hM⟩ := targetRecTy_majorOf ht
      exact ⟨fvs, mty, _, hM⟩
    · exact targetRecTys_majorOf hts t' ht'

/-- **Stage (b), against the walk: every outside major is an auxiliary
type** (`targetMajorOf_legacy`). -/
theorem targetRecTys_legacy {fe : FEnv} {p : BlockShape} {nested : Bool}
    {a : NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat}
    {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)}
    {hn : List (Option (List NestCtorNf))}
    (h : targetRecTys (fueledOps mode F) fe p nested (some a) cvTas ctorsAs recs hn = .ok tys) :
    ∀ t ∈ tys, t.2.1.member = none → t.2.1.ind ∉ p.memberNames ∧
      (∃ x ∈ t.2.1.ds, x.nestOcc p.memberNames 0 0 = true) ∧
        a.keys.contains ⟨t.2.1.ind, t.2.1.lvls, t.2.1.ds⟩ = true :=
  fun t ht hM => let ⟨_, _, _, h'⟩ := targetRecTys_majorOf h t ht; targetMajorOf_legacy h' hM

/-- **Every checked major records its class's normal forms**
(`targetMajorOf_nfs` through the list). -/
theorem targetRecTys_nfs {fe : FEnv} {p : BlockShape} {nested : Bool}
    {aux : Option NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat}
    {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)}
    {hn : List (Option (List NestCtorNf))}
    (h : targetRecTys (fueledOps mode F) fe p nested aux cvTas ctorsAs recs hn = .ok tys) :
    ∀ t ∈ tys, t.2.1.nfs = aux.map (targetMajorNfs · t.2.1.lvls t.2.1.ds) :=
  fun t ht => let ⟨_, _, _, h'⟩ := targetRecTys_majorOf h t ht; targetMajorOf_nfs h'

/-- **The major's carried home normal forms** are the resolution's. -/
theorem targetMajorOf_homeNfs {fe : FEnv} {p : BlockShape} {aux : Option NestNodes}
    {ctorsAs : List (List (ConstantVal × Nat))} {fvs : List Expr} {mty : Expr}
    {M : TargetMajor} {hnf : Option (List NestCtorNf)}
    (h : targetMajorOf (m := CheckM) fe p aux ctorsAs fvs mty hnf = .ok M) :
    M.homeNfs = hnf := by
  rcases targetMajorOf_cases h with hmem | hout
  · obtain ⟨_, _, _, _, _, _, _, _, _, hMe⟩ := hmem
    subst hMe; rfl
  · obtain ⟨I, us, _, h⟩ := hout
    obtain ⟨nPc, nIdx, ctors, sI, _, _, _, _, _, _, hMe⟩ := targetOutsideMajorOf_inv h
    subst hMe; rfl

/-- **Stage (b) carries the home table's normal forms by position.** -/
theorem targetRecTys_homeNfs {fe : FEnv} {p : BlockShape} {nested : Bool}
    {aux : Option NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat} :
    ∀ {recs : List RecShape} {hn : List (Option (List NestCtorNf))}
      {tys : List (ConstantVal × TargetMajor × Level)},
      targetRecTys (fueledOps mode F) fe p nested aux cvTas ctorsAs recs hn = .ok tys →
      ∀ (i : Nat) (t : ConstantVal × TargetMajor × Level), tys[i]? = some t →
        t.2.1.homeNfs = hn.getD i none
  | [], _, tys, h => by
    simp only [targetRecTys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro i t hi; exact nomatch hi
  | rc :: rcs, hn, tys, h => by
    unfold targetRecTys at h
    obtain ⟨t, ht, h⟩ := exceptBind_ok h
    obtain ⟨ts, hts, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro i t' hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      obtain ⟨cvRi, M, u⟩ := t
      obtain ⟨fvs, mty, hM⟩ := targetRecTy_majorOf ht
      rw [targetMajorOf_homeNfs hM]
      cases hn <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      rw [targetRecTys_homeNfs hts i t' hi]
      cases hn <;> simp

/-- **Stage (b) at every recursor, inverted**: one entry per recursor. -/
theorem targetRecTys_run {fe : FEnv} {p : BlockShape} {nested : Bool}
    {aux : Option NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat} :
    ∀ {recs : List RecShape} {hn : List (Option (List NestCtorNf))}
      {tys : List (ConstantVal × TargetMajor × Level)},
      targetRecTys (fueledOps mode F) fe p nested aux cvTas ctorsAs recs hn = .ok tys →
      tys.length = recs.length ∧
      ∀ (i : Nat) (rc : RecShape), recs[i]? = some rc →
        ∃ cvRi M u, tys[i]? = some (cvRi, M, u) ∧
        Nonempty (TargetTyEntry mode F fe p nested cvTas ctorsAs rc cvRi M u)
  | [], _, tys, h => by
    simp only [targetRecTys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i rc hi => nomatch hi⟩
  | rc :: rcs, hn, tys, h => by
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

/-- **Stage (b) against the walk resolves every major with the walk's
normal forms**, so such a family is off the route (`targetRouteOf`)
unless it has no recursor. -/
theorem targetRecTys_legacy_off {fe : FEnv} {p : BlockShape} {nested : Bool} {a : NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat}
    {recs : List RecShape} {hn : List (Option (List NestCtorNf))}
    {tys : List (ConstantVal × TargetMajor × Level)}
    (h : targetRecTys (fueledOps mode F) fe p nested (some a) cvTas ctorsAs recs hn = .ok tys)
    (hne : tys ≠ []) : targetRouteOf p (tys.map (·.2.1)) = false := by
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil tys hne
  have hn := targetRecTys_nfs h t ht
  unfold targetRouteOf
  simp only [Bool.and_eq_false_iff]
  left
  rw [List.all_eq_false]
  exact ⟨t.2.1, List.mem_map_of_mem ht, by rw [hn]; simp⟩

/-- **Stage (b), routed, inverted**: it is stage (b) at the aux the route
of its own majors names (`targetLegacyAux`), carrying the home table's
normal forms `hn` — none, or the ones `targetHomeOf` gave at the majors
resolved without the walk. -/
theorem targetRecTysRouted_run {fe : FEnv} {p : BlockShape} {nested : Bool} {aux : NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat}
    {tys : List (ConstantVal × TargetMajor × Level)}
    (h : targetRecTysRouted (fueledOps mode F) fe p nested aux cvTas ctorsAs = .ok tys) :
    ∃ hn, targetRecTys (fueledOps mode F) fe p nested (targetLegacyAux p (tys.map (·.2.1)) aux)
      cvTas ctorsAs p.recs hn = .ok tys ∧
      (hn = [] ∨ targetHomeOf p aux (tys.map (·.2.1)) = some hn) ∧
      ((targetLegacyAux p (tys.map (·.2.1)) aux).isSome → hn = []) := by
  have hleg : ∀ {tys'}, targetRecTys (fueledOps mode F) fe p nested (some aux) cvTas ctorsAs
      p.recs = .ok tys' →
      targetRecTys (fueledOps mode F) fe p nested (targetLegacyAux p (tys'.map (·.2.1)) aux)
        cvTas ctorsAs p.recs = .ok tys' := by
    intro tys' h'
    by_cases hne : tys' = []
    · subst hne
      have hl := (targetRecTys_run h').1
      have hr : p.recs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
      rw [hr] at h' ⊢
      rfl
    · unfold targetLegacyAux
      rw [targetRecTys_legacy_off h' hne]
      exact h'
  have hon : ∀ {hn tys'}, targetRecTys (fueledOps mode F) fe p nested none cvTas ctorsAs p.recs hn
      = .ok tys' → targetRouteOf p (tys'.map (·.2.1)) = true →
      targetRecTys (fueledOps mode F) fe p nested (targetLegacyAux p (tys'.map (·.2.1)) aux)
        cvTas ctorsAs p.recs hn = .ok tys' := by
    intro hn tys' h' hr
    unfold targetLegacyAux
    rw [if_pos hr]
    exact h'
  unfold targetRecTysRouted at h
  split at h
  · obtain ⟨tys0, h0, h⟩ := exceptBind_ok h
    split at h
    · next hr =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨[], hon h0 hr, Or.inl rfl, fun _ => rfl⟩
    · split at h
      · next hn hH =>
        obtain ⟨tys1, h1, h⟩ := exceptBind_ok h
        split at h
        · next hr =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [Bool.and_eq_true, beq_iff_eq] at hr
          refine ⟨hn, hon h1 hr.1, Or.inr hr.2, fun hs => ?_⟩
          unfold targetLegacyAux at hs
          rw [if_pos hr.1] at hs
          exact nomatch hs
        · exact ⟨[], hleg h, Or.inl rfl, fun _ => rfl⟩
      · exact ⟨[], hleg h, Or.inl rfl, fun _ => rfl⟩
  · exact ⟨[], hleg h, Or.inl rfl, fun _ => rfl⟩

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
    {absM : Expr → Expr} {base k F : Nat} {pw : PropWhen} {fwss : Option (List (List Expr))}
    {ih : TargetIh}
    (h : targetCallOk (fueledOps mode F) env cn fam fvsPref fvsF fnorm teles absM base k pw fwss
      ih = .ok ()) :
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
    {absM : Expr → Expr} {base k F : Nat} {pw : PropWhen} {fwss : Option (List (List Expr))} :
    ∀ {ihs : List TargetIh},
      targetCallsOk (fueledOps mode F) env cn fam fvsPref fvsF fnorm teles absM base k pw fwss ihs
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

/-- **K.53′, inverted**: at a call's typing that ran through, the walk
recorded at least one normal form of the rule's constructor at its class,
and in every one the called field IS the callee's major type at the
call's arguments under the field's telescope, up to the free variables'
annotations. -/
theorem targetCallOk_k53 {env : Env} {cn : Name} {fam : TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k F : Nat} {pw : PropWhen} {fwss : List (List Expr)}
    {ih : TargetIh}
    (h : targetCallOk (fueledOps mode F) env cn fam fvsPref fvsF fnorm teles absM base k pw
      (some fwss) ih = .ok ())
    (C : TargetCallRun mode F env fam fvsPref fvsF fnorm teles absM base k pw ih) :
    fwss ≠ [] ∧ ∀ fws ∈ fwss, fws[ih.field]?.map Expr.eraseFVarTys =
      some (Expr.mkPisOf (teles.getD ih.field []) C.majDom).eraseFVarTys := by
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
  by_cases hk : ((some fwss).all fun fwss => !fwss.isEmpty &&
      fwss.all (fun fws => fws[ih.field]?.map Expr.eraseFVarTys ==
        some (Expr.mkPisOf (teles.getD ih.field []) C.majDom).eraseFVarTys)) = true
  case neg => rw [if_neg hk] at h; close_throw h
  simp only [Option.all_some, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, beq_iff_eq] at hk
  exact ⟨hk.1, hk.2⟩

/-! ## A call around a cycle of a family checked off the walk -/

/-- The callee's hole at an intra-SCC call: its index in the caller's
home and the home's group entry there. -/
@[expose] def targetIntraHole (fe : FEnv) (fam : TargetFamily) (M : TargetMajor) (base : Nat)
    (ih : TargetIh) : Expr :=
  .fvar (base + M.home.idxOf (fam.majors.getD ih.callee default).ind)
    ((targetHomeGrp fe M).getD (M.home.idxOf (fam.majors.getD ih.callee default).ind)
      default).2

/-- **An intra-SCC call's check, as run** (`targetIntraCallOk` at a call
inside a cycle of a family checked off the walk): the callee is in the
caller's home; the constructor with the home abstracted to its holes,
instantiated at the class's parameters (`crestH`); the called field's
domain there and the callee's hole at the call's arguments, under the
call's telescope, both inferred and defeq at the frame past the holes. -/
structure TargetIntraCallRun (mode : CheckMode) (F : Nat) (fe : FEnv) (fam : TargetFamily)
    (M : TargetMajor) (cA : ConstantVal) (fvsF : List Expr)
    (teles : List (List (Expr × BinderMeta))) (base : Nat) (ih : TargetIh) : Type where
  crestH : Expr
  hhome : M.home.contains (fam.majors.getD ih.callee default).ind = true
  hcrest : instPisWith M.ds ((cA.type.instantiateLevelParams cA.levelParams M.lvls).replaceConsts
    (grpSub M.lvls base (targetHomeGrp fe M))) = some crestH
  fldTy : Expr
  wantTy : Expr
  hfld : inferTypeCore mode fe.env F (base + (targetHomeGrp fe M).length)
    (((targetPiDomsWith fvsF crestH).getD []).getD ih.field default) = .ok fldTy
  hwant : inferTypeCore mode fe.env F (base + (targetHomeGrp fe M).length)
    (Expr.mkPisOf (teles.getD ih.field [])
      (Expr.mkAppN (targetIntraHole fe fam M base ih) (M.ds ++ ih.idx))) = .ok wantTy
  hdeq : isDefEqCore mode fe.env F (base + (targetHomeGrp fe M).length)
    (((targetPiDomsWith fvsF crestH).getD []).getD ih.field default)
    (Expr.mkPisOf (teles.getD ih.field [])
      (Expr.mkAppN (targetIntraHole fe fam M base ih) (M.ds ++ ih.idx))) = .ok true

/-- **An intra-SCC call's check, inverted**: at a family checked off the
walk (`fam.ranks = some rk`) and a call whose callee shares the caller's
rank. -/
theorem targetIntraCallOk_run {fe : FEnv} {cn rn : Name} {fam : TargetFamily}
    {M : TargetMajor} {cA : ConstantVal} {fvsPref fvsF : List Expr}
    {teles : List (List (Expr × BinderMeta))} {base F : Nat} {ih : TargetIh}
    (h : targetIntraCallOk (fueledOps mode F) fe cn rn fam M cA fvsPref fvsF teles base ih
      = .ok ()) {rk : List Nat} (hrk : fam.ranks = some rk)
    (heq : rk.getD ih.callee 0 = rk.getD ((nameIdxOf? fam.recNames rn).getD 0) 0)
    (hnh : M.homeNfs = none) :
    Nonempty (TargetIntraCallRun mode F fe fam M cA fvsF teles base ih) := by
  unfold targetIntraCallOk at h
  rw [hrk] at h
  dsimp only at h
  rw [if_neg (show ¬((rk.getD ih.callee 0 != rk.getD ((nameIdxOf? fam.recNames rn).getD 0) 0) ||
    M.homeNfs.isSome) = true by rw [heq, hnh]; simp)] at h
  by_cases hhm : M.home.contains (fam.majors.getD ih.callee default).ind = true
  case neg => rw [if_neg hhm] at h; close_throw h
  rw [if_pos hhm] at h
  split at h
  · next crestH hcrestH =>
    split at h
    · next calleeAt hcallee =>
      split at h
      · next majDom mb mbm =>
        obtain ⟨fldTy, hfld, h⟩ := exceptBind_ok h
        obtain ⟨wantTy, hwant, h⟩ := exceptBind_ok h
        obtain ⟨b, hb, h⟩ := exceptBind_ok h
        by_cases hbt : b = true
        case neg => rw [if_neg hbt] at h; close_throw h
        subst hbt
        exact ⟨{ crestH := crestH, hhome := hhm, hcrest := hcrestH, fldTy := fldTy,
                 wantTy := wantTy, hfld := hfld, hwant := hwant, hdeq := hb }⟩
      · close_throw h
    · close_throw h
  · close_throw h

/-- **Every intra-SCC call's check ran**, one by one. -/
theorem targetIntraCallsOk_each {fe : FEnv} {cn rn : Name} {fam : TargetFamily}
    {M : TargetMajor} {cA : ConstantVal} {fvsPref fvsF : List Expr}
    {teles : List (List (Expr × BinderMeta))} {base F : Nat} :
    ∀ {ihs : List TargetIh},
      targetIntraCallsOk (fueledOps mode F) fe cn rn fam M cA fvsPref fvsF teles base ihs
        = .ok () →
      ∀ ih ∈ ihs,
        targetIntraCallOk (fueledOps mode F) fe cn rn fam M cA fvsPref fvsF teles base ih
          = .ok ()
  | [], _, ih, hih => nomatch hih
  | ih0 :: ihs, h, ih, hih => by
    unfold targetIntraCallsOk at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hih with rfl | hih
    · cases u; exact hu
    · exact targetIntraCallsOk_each h ih hih

/-! ## The route off the walk, inverted -/

/-- **An edge inside a layer that is not hot is flat**: it joins two
outside classes of one home at the same levels and parameters. -/
theorem targetHot_false_edge {p : BlockShape} {Ms : List TargetMajor} {n : Nat}
    (h : targetHot p Ms n = false) {c c' : Nat} (hc : c < (targetGraphOf p).length)
    (he : c' ∈ (targetGraphOf p).getD c [])
    (hr : (graphRank (targetGraphOf p)).getD c 0 = n)
    (hr' : (graphRank (targetGraphOf p)).getD c' 0 = n) :
    (Ms.getD c default).member = none ∧ (Ms.getD c' default).member = none ∧
      (Ms.getD c default).home.contains (Ms.getD c' default).ind = true ∧
      (Ms.getD c' default).lvls = (Ms.getD c default).lvls ∧
      (Ms.getD c' default).ds = (Ms.getD c default).ds := by
  unfold targetHot at h
  have h1 := List.any_eq_false.mp h c (List.mem_range.mpr hc)
  rw [hr, beq_self_eq_true, Bool.true_and] at h1
  have h2 := List.any_eq_false.mp (Bool.not_eq_true _ ▸ h1) c' he
  rw [hr', beq_self_eq_true, Bool.true_and] at h2
  have hf : targetFlatEdge (Ms.getD c default) (Ms.getD c' default) = true := by
    cases hfe : targetFlatEdge (Ms.getD c default) (Ms.getD c' default)
    · rw [hfe] at h2; exact absurd rfl h2
    · rfl
  unfold targetFlatEdge at hf
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩ := hf
  exact ⟨h3, h4, h5, h6, h7⟩

/-- On the route every major was resolved without the walk. -/
theorem targetRouteOf_nfs {p : BlockShape} {Ms : List TargetMajor}
    (h : targetRouteOf p Ms = true) : ∀ M ∈ Ms, M.nfs = none := by
  unfold targetRouteOf at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  intro M hM
  simpa using h.1 M hM

/-- **On the route exactly the hot layers' classes carry home normal
forms.** -/
theorem targetRouteOf_homeNfs {p : BlockShape} {Ms : List TargetMajor}
    (h : targetRouteOf p Ms = true) {c : Nat} (hc : c < Ms.length) :
    (Ms.getD c default).homeNfs.isSome =
      targetHot p Ms ((graphRank (targetGraphOf p)).getD c 0) := by
  unfold targetRouteOf at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact (h.2 c hc).symm

/-- The recursor records' names are distinct (`targetRecPins`). -/
theorem targetRecPins_nodup {p : BlockShape} {block : List ConstantInfo}
    (h : targetRecPins (m := CheckM) p block = .ok ()) : (p.recs.map (·.cvR.name)).Nodup := by
  unfold targetRecPins at h
  by_cases h1 : blockRecLpsOk p = true
  case neg => rw [if_neg h1] at h; close_throw h
  rw [if_pos h1] at h
  by_cases h2 : blockRecNamesUnreserved p = true
  case neg => rw [if_neg h2] at h; close_throw h
  rw [if_pos h2] at h
  dsimp only at h
  split at h
  case isFalse => close_throw h
  split at h
  case isFalse => close_throw h
  by_cases h5 : (p.recs.map (·.cvR.name)).Nodup
  · exact h5
  · rw [if_neg (by simpa using h5)] at h; close_throw h

/-- A name's index in a duplicate-free list. -/
theorem nameIdxOf?_of_nodup {names : List Name} (hnd : names.Nodup) {c : Nat}
    (hc : c < names.length) : nameIdxOf? names (names.getD c default) = some c := by
  unfold nameIdxOf?
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, c, by simpa using hc, by simp, fun j hj => ?_⟩
  have hjc : j < names.length := by omega
  simp only [List.getElem_range]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjc, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hc]
  simp only [Option.getD_some, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  intro he
  have := (List.getElem_inj hnd).mp he
  omega

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
    (rP + c.2) formerTys.length (Level.zeronessOf (structElimLevel p.elim p.large))
    (targetFieldNfs (targetClassNfs M) c.1.name fvsF) ihs.toList = .ok ()
  /-- every call around a cycle of a family checked off the walk, typed at
  its home's holes (`targetIntraCallOk`) -/
  hintra : targetIntraCallsOk (fueledOps mode F) feT c.1.name cvR.name fam M c.1 fvsPref fvsF
    (fnorm.map fun t => t.piBinders.1) (rP + c.2) ihs.toList = .ok ()
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
  obtain ⟨u4, hintra, h⟩ := exceptBind_ok h
  cases u4
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
          hcalls := hcalls, hintra := hintra, hty := hty, hconcl := unwrapOr_ok hconcl,
          hdeq := hb }⟩

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

/-- **The target recursor check, as run**: the pins, the
recursors' types (`tys`), the family's agreements, the rule pins, and
the rules at the environment holding the rule-less recursors. -/
structure TargetRecRun (mode : CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape)
    (nested : Bool) (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × TargetMajor × List Expr)) : Type where
  /-- stage (b)'s list -/
  tys : List (ConstantVal × TargetMajor × Level)
  /-- the positivity walk's auxiliary types, as the caller passed them
  (read only at a family with a cyclic call graph, `targetLegacyAux`) -/
  aux : NestNodes
  /-- (a) the records' pins -/
  pins : targetRecPins (m := CheckM) p block = .ok ()
  /-- the home table's normal forms stage (b) carried (PRIMREC/NESTHOME) -/
  hn : List (Option (List NestCtorNf))
  /-- (b) every recursor's type -/
  htys : targetRecTys (fueledOps mode F) fe p nested (targetLegacyAux p (tys.map (·.2.1)) aux)
    cvTas ctorsAs p.recs hn = .ok tys
  /-- (b) the carried normal forms: none, or the home table's at the
  majors (`targetHomeOf`) -/
  hnOk : hn = [] ∨ targetHomeOf p aux (tys.map (·.2.1)) = some hn
  /-- against the walk, no home table's normal forms -/
  hnLeg : (targetLegacyAux p (tys.map (·.2.1)) aux).isSome → hn = []
  /-- (b') the counting half of the elimination guard, at the block's
  container bit -/
  small : 0 < p.k ∧
    ((blockLargeElimAllowed p nested = true ∧
      (tys.all fun t => targetMajorLicensed fe p nested t.2.1) = true) ∨
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
`targetRecCheck`, its `aux` the caller's. -/
theorem targetRecCheck_run_aux {fe : FEnv} {p : BlockShape} {nested : Bool}
    {aux : NestNodes}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : targetRecCheck (ShadowOps.fueled mode F) fe p nested aux block cvTas ctorsAs
      = .ok out) :
    ∃ R : TargetRecRun mode F fe p nested block cvTas ctorsAs out, R.aux = aux := by
  unfold targetRecCheck at h
  obtain ⟨u0, hpins, h⟩ := exceptBind_ok h
  obtain ⟨tys, htys, h⟩ := exceptBind_ok h
  obtain ⟨hn, htys, hnOk, hnLeg⟩ := targetRecTysRouted_run htys
  obtain ⟨u1, hsmall, h⟩ := exceptBind_ok h
  obtain ⟨u2, hpin, h⟩ := exceptBind_ok h
  obtain ⟨u3, hpref, h⟩ := exceptBind_ok h
  obtain ⟨u4, hrp, h⟩ := exceptBind_ok h
  obtain ⟨out', hrules, h⟩ := exceptBind_ok h
  obtain ⟨u5, -, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨{ tys := tys, aux := aux, pins := by cases u0; exact hpins, hn := hn, htys := htys,
           hnOk := hnOk, hnLeg := hnLeg,
           small := checkBlockRecSmallElim_inv (by cases u1; exact hsmall),
           pin := checkBlockRecElimPin_inv (by cases u2; exact hpin),
           prefixAgree := by cases u3; exact hpref, rulePins := by cases u4; exact hrp,
           rules := hrules }, rfl⟩

/-- **The target recursor check, inverted** (`targetRecCheck_run_aux`). -/
theorem targetRecCheck_run {fe : FEnv} {p : BlockShape} {nested : Bool}
    {aux : NestNodes}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : targetRecCheck (ShadowOps.fueled mode F) fe p nested aux block cvTas ctorsAs
      = .ok out) :
    Nonempty (TargetRecRun mode F fe p nested block cvTas ctorsAs out) :=
  ⟨(targetRecCheck_run_aux h).choose⟩

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

/-- The stored majors are stage (b)'s. -/
theorem targetRecRun_majors (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    out.map (·.2.1) = R.tys.map (·.2.1) := by
  have := congrArg (List.map Prod.snd) (targetRecRun_out_fst R)
  simpa [List.map_map, Function.comp_def] using this

/-- **THE MAJOR → NODE TIE, the recursor half**: at a family checked
against the walk (`targetLegacyAux`), every outside major of the checked
family names the block and is one of `aux` — at the install, the classes
of the positivity walk's nodes (`BlockPass.nodes`). -/
theorem targetRecRun_legacy (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out)
    (hleg : targetLegacyAux p (out.map (·.2.1)) R.aux = some R.aux) :
    ∀ o ∈ out, o.2.1.member = none → o.2.1.ind ∉ p.memberNames ∧
      (∃ x ∈ o.2.1.ds, x.nestOcc p.memberNames 0 0 = true) ∧
        R.aux.keys.contains ⟨o.2.1.ind, o.2.1.lvls, o.2.1.ds⟩ = true := by
  intro o ho hM
  rw [targetRecRun_majors R] at hleg
  have hmem : (o.1, o.2.1) ∈ R.tys.map (fun t => (t.1, t.2.1)) := by
    rw [← targetRecRun_out_fst R]; exact List.mem_map_of_mem ho
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at hte
  have hty := R.htys
  rw [hleg] at hty
  have := targetRecTys_legacy hty t ht (by rw [hte.2]; exact hM)
  rwa [hte.2] at this

/-- `targetRecRun_legacy` at the check's own run (its `aux` the caller's). -/
theorem targetRecCheck_aux {aux : NestNodes}
    (h : targetRecCheck (ShadowOps.fueled mode F) fe p nested aux block cvTas ctorsAs
      = .ok out) (hleg : targetLegacyAux p (out.map (·.2.1)) aux = some aux) :
    ∀ o ∈ out, o.2.1.member = none → aux.keys.contains ⟨o.2.1.ind, o.2.1.lvls, o.2.1.ds⟩ = true := by
  obtain ⟨R, rfl⟩ := targetRecCheck_run_aux h
  exact fun o ho hM => (targetRecRun_legacy R hleg o ho hM).2.2

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
`ShadowOps.fueled` on the constructors' index. -/
theorem checkBlockRecT_run {env : Env} {p : BlockParts} {nested : Bool}
    {aux : NestNodes} {block : List ConstantInfo}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : checkBlockRecT (fueledOps mode F) env p nested aux block cvTas ctorsAs = .ok out) :
    targetRecCheck (ShadowOps.fueled mode F) (mkFEnv env) p.toBlockShape nested aux
        block cvTas ctorsAs = .ok out :=
  h

/-! ## The home layers, inverted -/

/-- **The home layers, inverted** (`targetHomeOf`): every class of a hot
layer is covered, the matching is consistent at the hot classes, and the
carried normal forms are the matched entries' at the hot classes. -/
theorem targetHomeOf_some {p : BlockShape} {aux : NestNodes} {Ms : List TargetMajor}
    {hn : List (Option (List NestCtorNf))} (h : targetHomeOf p aux Ms = some hn) :
    (∀ c, c < Ms.length → targetHot p Ms ((graphRank (targetGraphOf p)).getD c 0) = true →
      homeCovered (p.nestCtx [] (fun _ => none) []) (Ms.map (·.homeClass))
        ((Ms.map (·.homeClass)).map (homeMatch (p.nestCtx [] (fun _ => none) []) aux.homes)) c
        = true) ∧
    homeConsistent (p.nestCtx [] (fun _ => none) []) (Ms.map (·.homeClass))
      ((Ms.map (·.homeClass)).map (homeMatch (p.nestCtx [] (fun _ => none) []) aux.homes))
      (fun c => targetHot p Ms ((graphRank (targetGraphOf p)).getD c 0)) = true ∧
    homePairConsistent (Ms.map (·.homeClass))
      ((Ms.map (·.homeClass)).map (homeMatch (p.nestCtx [] (fun _ => none) []) aux.homes))
      (fun c => targetHot p Ms ((graphRank (targetGraphOf p)).getD c 0)) = true ∧
    hn = (List.range Ms.length).map fun c =>
      if targetHot p Ms ((graphRank (targetGraphOf p)).getD c 0) then
        (((Ms.map (·.homeClass)).map (homeMatch (p.nestCtx [] (fun _ => none) []) aux.homes)).getD
          c none).map (·.nfs.map (·.entry))
      else none := by
  unfold targetHomeOf at h
  simp only [List.length_map] at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Bool.not_eq_true'] at hc
    obtain ⟨⟨hcov, hcons⟩, hpair⟩ := hc
    refine ⟨fun c hc hot => ?_, hcons, hpair, h.symm⟩
    rcases hcov c hc with h1 | h1
    · rw [hot] at h1; exact nomatch h1
    · exact h1
  · exact nomatch h


/-! ## The stored family's home normal forms -/

/-- The call graph has one row per record. -/
theorem targetGraphOf_length (p : BlockShape) : (targetGraphOf p).length = p.recs.length := by
  simp [targetGraphOf, targetCallGraph]

/-- A hot layer has a class. -/
theorem targetHot_witness {p : BlockShape} {Ms : List TargetMajor} {n : Nat}
    (h : targetHot p Ms n = true) :
    ∃ c, c < p.recs.length ∧ (graphRank (targetGraphOf p)).getD c 0 = n := by
  unfold targetHot at h
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨c, hc, hr, -⟩ := h
  exact ⟨c, targetGraphOf_length p ▸ hc, hr⟩

/-- **The stored majors carry the run's home normal forms by position.** -/
theorem targetRecRun_homeNfs {fe : FEnv} {p : BlockShape} {nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    {F : Nat} (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    ∀ c, c < out.length → (out.getD c default).2.1.homeNfs = R.hn.getD c none := by
  intro c hc
  have hm := targetRecRun_majors R
  have hlen : c < R.tys.length := by
    have := congrArg List.length hm; simp only [List.length_map] at this; omega
  have h1 := targetRecTys_homeNfs R.htys c R.tys[c] (List.getElem?_eq_getElem hlen)
  have h2 : (out.getD c default).2.1 = R.tys[c].2.1 := by
    have := congrArg (·[c]?) hm
    simp only [List.getElem?_map, List.getElem?_eq_getElem hc, List.getElem?_eq_getElem hlen,
      Option.map_some, Option.some.injEq] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some]
    exact this
  rw [h2, h1]

/-- **On the route with a hot layer, the run carries the home table's
normal forms at its own majors.** -/
theorem targetRecRun_home {fe : FEnv} {p : BlockShape} {nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    {F : Nat} (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out)
    (hroute : targetRouteOf p (out.map (·.2.1)) = true) {n : Nat}
    (hhot : targetHot p (out.map (·.2.1)) n = true) :
    targetHomeOf p R.aux (out.map (·.2.1)) = some R.hn := by
  rcases R.hnOk with h0 | h
  · exfalso
    obtain ⟨c, hc, hr⟩ := targetHot_witness hhot
    have hlenO : out.length = p.recs.length := by
      obtain ⟨hlenT, -⟩ := targetRecTys_run R.htys
      have := congrArg List.length (targetRecRun_majors R)
      simp only [List.length_map] at this; omega
    have hs := targetRouteOf_homeNfs hroute (c := c) (by simp; omega)
    rw [hr, hhot] at hs
    have hh := targetRecRun_homeNfs R c (by omega)
    rw [h0] at hh
    have : ((out.map (·.2.1)).getD c default) = (out.getD c default).2.1 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases out[c]? <;> rfl
    rw [this, hh] at hs
    simp at hs
  · rw [targetRecRun_majors R]; exact h

end ConLeche
