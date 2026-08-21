import Setlec.Model.Extend.Inversions
import Setlec.Model.IotaWalk

/-!
# Iota — split out of `Setlec.Model.Extend`

The kernel-checked hypothesis kits of modeled recursor rules
(`RuleChecked`, from `checkIotaRules_inv`) and of a block's
capability record (`EtaPins`, from `checkEtaThm_inv` /
`checkUnitThm_inv`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- The kernel-checked data of a *canonical* rule's `iota_j` theorem:
everything `modeled_rule_fold` consumes.  `env` is the environment the
theorem is stored in, `env₀` the provisional one carrying the block's
rule-less recursors (the definitional-equality checks ran there). -/
def PlainChecked (F : Nat) (env env₀ : Env) (f : Name → Name)
    (cvA : ConstantVal) (nP nM nm ni cnP cnF : Nat) (r : RecRule)
    (cvj : ConstantVal) : Prop :=
  ∃ (thmName : Name) (cvt : ConstantVal) (tval : Expr)
    (fvs : List Expr) (tbody : Expr) (ℓA : Level) (αS lhsS rhsS : Expr)
    (cdoms : List Expr) (cres : Expr) (rdoms : List Expr) (rrest : Expr)
    (fvsP : List Expr) (restP : Expr) (cdomsP : List Expr)
    (crestP : Expr) (xFvsP : List Expr) (crest2 : Expr)
    (ldoms : List Expr) (lrest : Expr),
    env.find? thmName = some (.thmInfo cvt tval) ∧
    cvt.levelParams = cvA.levelParams ∧
    openPisAtFvars (nP + nM + nm + cnF) cvt.type 0 = some (fvs, tbody) ∧
    tbody.getAppFn = .const eqName [ℓA] ∧
    tbody.getAppArgs = [αS, lhsS, rhsS] ∧
    lhsS.getAppFn = Expr.const (f cvA.name) (cvA.levelParams.map .param) ∧
    lhsS.getAppArgs.length = nP + nM + nm + ni + 1 ∧
    lhsS.getAppArgs.take (nP + nM + nm) = fvs.take (nP + nM + nm) ∧
    lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f (RecRule.ctor r)) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop (nP + nM + nm)) ∧
    (cvj.type.stripPis (cnP + cnF)).isSome = true ∧
    Expr.instPisAt (fvs.take cnP ++ fvs.drop (nP + nM + nm))
      (cvj.type.renameConsts f) = some (cdoms, cres) ∧
    cres.getAppArgs.length = cnP + ni ∧
    DefEqListOk F env₀ (nP + nM + nm + cnF)
      ((lhsS.getAppArgs.drop (nP + nM + nm)).take ni)
      (cres.getAppArgs.drop cnP) ∧
    DefEqListOk F env₀ (nP + nM + nm + cnF)
      ((fvs.drop (nP + nM + nm)).map Expr.fvarTypeD) (cdoms.drop cnP) ∧
    Expr.instPisAt (fvs.take (nP + nM + nm)) (cvA.type.renameConsts f) =
      some (rdoms, rrest) ∧
    DefEqListOk F env₀ (nP + nM + nm + cnF)
      ((fvs.take (nP + nM + nm)).map Expr.fvarTypeD) rdoms ∧
    openPisAtFvars (nP + nM + nm) cvA.type 0 = some (fvsP, restP) ∧
    Expr.instPisAt (fvsP.take cnP) cvj.type = some (cdomsP, crestP) ∧
    openPisAtFvars cnF crestP (nP + nM + nm) = some (xFvsP, crest2) ∧
    Expr.instLamsAt (fvsP ++ xFvsP) (RecRule.rhs r) =
      some (ldoms, lrest) ∧
    DefEqListOk F env₀ (nP + nM + nm + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms ∧
    isDefEqCore env₀ F (nP + nM + nm + cnF) rhsS
      (Expr.mkAppN ((RecRule.rhs r).renameConsts f) fvs) = .ok true

/-- Invert a successful `checkIotaThm` run (on the rule as returned,
whose `rhs` is the annotated right-hand side). -/
theorem checkIotaThm_inv {env' env₀ : Env} {f : Name → Name}
    {cvA cvj : ConstantVal} {nP nM nm ni j cnP cnF : Nat}
    {r : RecRule} {rhsA : Expr} {u : Unit}
    (h : checkIotaThm (fueledOps F) env' env₀ f cvA.name cvA.levelParams
      cvA.type nP nM nm ni j r cvj cnP cnF rhsA = .ok u) :
    PlainChecked F env' env₀ f cvA nP nM nm ni cnP cnF
      { r with rhs := rhsA } cvj := by
  simp only [checkIotaThm, fueledOps_annotate, fueledOps_inferType,
    fueledOps_isDefEq, fueledOps_ensureSort, fueledOps_whnf, Bind.bind,
    Except.bind, pure, Except.pure] at h
  revert h
  match hfthm : env'.find? ((cvA.name.str "_model").str s!"iota_{j}") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo cvt tval) => ?_
  intro h
  dsimp only at h
  by_cases hlpt : cvt.levelParams = cvA.levelParams
  case neg => rw [if_neg hlpt] at h; exact nomatch h
  rw [if_pos hlpt] at h
  try dsimp only at h
  revert h
  match hopen : openPisAtFvars (nP + nM + nm + cnF) cvt.type 0 with
  | none => intro h; exact nomatch h
  | some (fvs, tbody) => ?_
  intro h
  dsimp only at h
  by_cases hhead : isEqHead tbody.getAppFn = true
  case neg => rw [if_neg hhead] at h; exact nomatch h
  rw [if_pos hhead] at h
  obtain ⟨ℓA, hheadEq⟩ := isEqHead_inv hhead
  try dsimp only at h
  by_cases hlen3 : tbody.getAppArgs.length = 3
  case neg => rw [if_neg hlen3] at h; exact nomatch h
  rw [if_pos hlen3] at h
  obtain ⟨αS, lhsS, rhsS, hargs3⟩ :
      ∃ αS lhsS rhsS, tbody.getAppArgs = [αS, lhsS, rhsS] := by
    match hta : tbody.getAppArgs with
    | [a, b, c] => exact ⟨a, b, c, rfl⟩
    | [] => rw [hta] at hlen3; exact nomatch hlen3
    | [_] => rw [hta] at hlen3; exact nomatch hlen3
    | [_, _] => rw [hta] at hlen3; exact nomatch hlen3
    | _ :: _ :: _ :: _ :: _ => rw [hta] at hlen3; simp at hlen3
  rw [hargs3] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  by_cases hlhead : (lhsS.getAppFn ==
      Expr.const (f cvA.name) (cvA.levelParams.map .param)) = true
  case neg => rw [if_neg hlhead] at h; exact nomatch h
  rw [if_pos hlhead] at h
  try dsimp only at h
  by_cases hlarity : lhsS.getAppArgs.length = nP + nM + nm + ni + 1
  case neg => rw [if_neg hlarity] at h; exact nomatch h
  rw [if_pos hlarity] at h
  try dsimp only at h
  by_cases hlpre : (lhsS.getAppArgs.take (nP + nM + nm) ==
      fvs.take (nP + nM + nm)) = true
  case neg => rw [if_neg hlpre] at h; exact nomatch h
  rw [if_pos hlpre] at h
  try dsimp only at h
  by_cases hmaj : (lhsS.getAppArgs.getLastD (.bvar 0) ==
      Expr.mkAppN (.const (f (RecRule.ctor r)) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop (nP + nM + nm))) = true
  case neg => rw [if_neg hmaj] at h; exact nomatch h
  rw [if_pos hmaj] at h
  try dsimp only at h
  by_cases hcstrip : (cvj.type.stripPis (cnP + cnF)).isSome = true
  case neg => rw [if_neg hcstrip] at h; exact nomatch h
  rw [if_pos hcstrip] at h
  try dsimp only at h
  revert h
  match hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop (nP + nM + nm))
      (cvj.type.renameConsts f) with
  | none => intro h; exact nomatch h
  | some (cdoms, cres) => ?_
  intro h
  dsimp only at h
  by_cases hclen : cres.getAppArgs.length = cnP + ni
  case neg => rw [if_neg hclen] at h; exact nomatch h
  rw [if_pos hclen] at h
  try dsimp only at h
  cases hdq1 : checkDefEqList (fueledOps F) env₀ (nP + nM + nm + cnF)
      ((lhsS.getAppArgs.drop (nP + nM + nm)).take ni)
      (cres.getAppArgs.drop cnP) with
  | error e => rw [hdq1] at h; exact nomatch h
  | ok u1 =>
  rw [hdq1] at h
  try dsimp only at h
  cases hdq2 : checkDefEqList (fueledOps F) env₀ (nP + nM + nm + cnF)
      ((fvs.drop (nP + nM + nm)).map Expr.fvarTypeD)
      (cdoms.drop cnP) with
  | error e => rw [hdq2] at h; exact nomatch h
  | ok u2 =>
  rw [hdq2] at h
  try dsimp only at h
  revert h
  match hrinst : Expr.instPisAt (fvs.take (nP + nM + nm))
      (cvA.type.renameConsts f) with
  | none => intro h; exact nomatch h
  | some (rdoms, rrest) => ?_
  intro h
  dsimp only at h
  cases hdq3 : checkDefEqList (fueledOps F) env₀ (nP + nM + nm + cnF)
      ((fvs.take (nP + nM + nm)).map Expr.fvarTypeD) rdoms with
  | error e => rw [hdq3] at h; exact nomatch h
  | ok u3 =>
  rw [hdq3] at h
  try dsimp only at h
  revert h
  match hopenP : openPisAtFvars (nP + nM + nm) cvA.type 0 with
  | none => intro h; exact nomatch h
  | some (fvsP, restP) => ?_
  intro h
  dsimp only at h
  revert h
  match hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type with
  | none => intro h; exact nomatch h
  | some (cdomsP, crestP) => ?_
  intro h
  dsimp only at h
  revert h
  match hopenX : openPisAtFvars cnF crestP (nP + nM + nm) with
  | none => intro h; exact nomatch h
  | some (xFvsP, crest2) => ?_
  intro h
  dsimp only at h
  revert h
  match hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA with
  | none => intro h; exact nomatch h
  | some (ldoms, lrest) => ?_
  intro h
  dsimp only at h
  cases hdq4 : checkDefEqList (fueledOps F) env₀ (nP + nM + nm + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms with
  | error e => rw [hdq4] at h; exact nomatch h
  | ok u4 =>
  rw [hdq4] at h
  try dsimp only at h
  revert h
  cases hde : isDefEqCore env₀ F (nP + nM + nm + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) with
  | error e => intro h; exact nomatch h
  | ok v =>
    cases v with
    | false => intro h; simp at h
    | true =>
      intro h
      exact ⟨(cvA.name.str "_model").str s!"iota_{j}", cvt, tval, fvs,
        tbody, ℓA, αS, lhsS, rhsS, cdoms, cres, rdoms, rrest, fvsP,
        restP, cdomsP, crestP, xFvsP, crest2, ldoms, lrest,
        hfthm, hlpt, hopen, hheadEq, hargs3, eq_of_beq hlhead, hlarity,
        eq_of_beq hlpre, eq_of_beq hmaj, hcstrip, hcinst, hclen,
        checkDefEqList_inv hdq1, checkDefEqList_inv hdq2, hrinst,
        checkDefEqList_inv hdq3, hopenP, hcinstP, hopenX, hlinst,
        checkDefEqList_inv hdq4, hde⟩

/-- The kernel-checked data of one modeled recursor rule: the
hypothesis kit its fold obligation consumes.  `env` is the environment
before the recursor group's installation, `env₀` the provisional one
with the block's rule-less recursors (in which the rule's right-hand
side was annotated). -/
def RuleChecked (F : Nat) (env env₀ : Env) (f : Name → Name)
    (cvA : ConstantVal) (nP nM nm ni : Nat) (r : RecRule) : Prop :=
  ∃ (cvj : ConstantVal) (cnP cnF : Nat) (raw rhsTy : Expr)
    (rbinders : List (Name × Expr × BinderMeta)) (rbody : Expr),
    env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF) ∧
    RecRule.nfields r = cnF ∧
    raw.hasFvar = false ∧ raw.looseBVarsBounded 0 = true ∧
    annotateCore env₀ F 0 raw = .ok (RecRule.rhs r) ∧
    (RecRule.rhs r).hasFvar = false ∧
    (RecRule.rhs r).looseBVarsBounded 0 = true ∧
    (RecRule.rhs r).allLevelParamsDefined cvA.levelParams = true ∧
    (RecRule.rhs r).constsResolve env₀ = true ∧
    (RecRule.rhs r).stripLams (nP + nM + nm + cnF) =
      some (rbinders, rbody) ∧
    inferTypeCore env₀ F 0 (RecRule.rhs r) = .ok rhsTy ∧
    (Expr.recRulePlain cvA.type nP nM nm ni cnP = true →
      PlainChecked F env env₀ f cvA nP nM nm ni cnP cnF r cvj)

/-- Invert one `checkIotaRule` run. -/
theorem checkIotaRule_inv {env' env₀ : Env} {f : Name → Name}
    {cvA : ConstantVal} {nP nM nm ni j : Nat} {r r' : RecRule}
    (h : checkIotaRule (fueledOps F) env' env₀ f cvA.name cvA.levelParams
      cvA.type nP nM nm ni j r = .ok r') :
    RuleChecked F env' env₀ f cvA nP nM nm ni r' := by
  simp only [checkIotaRule, fueledOps_annotate, fueledOps_inferType,
    fueledOps_isDefEq, fueledOps_ensureSort, fueledOps_whnf, Bind.bind,
    Except.bind, pure, Except.pure] at h
  revert h
  match hfc : env'.find? (RecRule.ctor r) with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj cnP cnF) => ?_
  intro h
  dsimp only at h
  by_cases hnf : RecRule.nfields r = cnF
  case neg => rw [if_neg hnf] at h; exact nomatch h
  rw [if_pos hnf] at h
  try dsimp only at h
  by_cases hrb : (RecRule.rhs r).looseBVarsBounded 0 = true
  case neg => rw [if_neg hrb] at h; exact nomatch h
  rw [if_pos hrb] at h
  try dsimp only at h
  by_cases hrf : (RecRule.rhs r).hasFvar = true
  case pos => rw [if_pos hrf] at h; exact nomatch h
  rw [if_neg hrf] at h
  have hrfF : (RecRule.rhs r).hasFvar = false := by
    revert hrf; cases (RecRule.rhs r).hasFvar <;> simp
  try dsimp only at h
  cases hann : annotateCore env₀ F 0 (RecRule.rhs r) with
  | error e => rw [hann] at h; exact nomatch h
  | ok rhsA =>
  rw [hann] at h
  try dsimp only at h
  by_cases hrlp : rhsA.allLevelParamsDefined cvA.levelParams = true
  case neg => rw [if_neg hrlp] at h; exact nomatch h
  rw [if_pos hrlp] at h
  try dsimp only at h
  by_cases hrres : rhsA.constsResolve env₀ = true
  case neg => rw [if_neg hrres] at h; exact nomatch h
  rw [if_pos hrres] at h
  try dsimp only at h
  by_cases hstrip : (rhsA.stripLams (nP + nM + nm + cnF)).isSome = true
  case neg => rw [if_neg hstrip] at h; exact nomatch h
  rw [if_pos hstrip] at h
  obtain ⟨⟨rbinders, rbody⟩, hstripEq⟩ :=
    Option.isSome_iff_exists.mp hstrip
  try dsimp only at h
  cases hity : inferTypeCore env₀ F 0 rhsA with
  | error e => rw [hity] at h; exact nomatch h
  | ok rhsTy =>
  rw [hity] at h
  try dsimp only at h
  by_cases hplain : Expr.recRulePlain cvA.type nP nM nm ni cnP = true
  case pos =>
    rw [if_pos hplain] at h
    revert h
    cases hthm : checkIotaThm (fueledOps F) env' env₀ f cvA.name
        cvA.levelParams cvA.type nP nM nm ni j r cvj cnP cnF rhsA with
    | error e => intro h; exact nomatch h
    | ok u =>
      intro h
      simp only [Except.ok.injEq] at h
      subst h
      have hkit := checkIotaThm_inv (cvA := cvA) hthm
      exact ⟨cvj, cnP, cnF, RecRule.rhs r, rhsTy, rbinders, rbody,
        hfc, hnf, hrfF, hrb, hann,
        not_hasFvar_of_fvarsBelow_zero
          ((annotateCore_WScoped F _ hann
            (WScoped.of_not_hasFvar hrfF)).fvarsBelow),
        annotateCore_looseBVars F _ hann hrb, hrlp, hrres, hstripEq,
        hity, fun _ => hkit⟩
  case neg =>
    rw [if_neg hplain] at h
    try dsimp only at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨cvj, cnP, cnF, RecRule.rhs r, rhsTy, rbinders, rbody,
      hfc, hnf, hrfF, hrb, hann,
      not_hasFvar_of_fvarsBelow_zero
        ((annotateCore_WScoped F _ hann
          (WScoped.of_not_hasFvar hrfF)).fvarsBelow),
      annotateCore_looseBVars F _ hann hrb, hrlp, hrres, hstripEq,
      hity, fun hp => absurd hp hplain⟩

/-- Invert a successful `checkIotaRules` run: every returned rule
carries the full `RuleChecked` hypothesis kit. -/
theorem checkIotaRules_inv {env' env₀ : Env} {f : Name → Name}
    {cvA : ConstantVal} {nP nM nm ni : Nat} :
    ∀ (j : Nat) (rules rules' : List RecRule),
    checkIotaRules (fueledOps F) env' env₀ f cvA.name cvA.levelParams
      cvA.type nP nM nm ni j rules = .ok rules' →
    ∀ r' ∈ rules', RuleChecked F env' env₀ f cvA nP nM nm ni r' := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h r' hr'
    simp only [checkIotaRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact nomatch hr'
  | cons r rest ih =>
    intro rules' h r' hr'
    simp only [checkIotaRules, Bind.bind, Except.bind] at h
    revert h
    cases hr1 : checkIotaRule (fueledOps F) env' env₀ f cvA.name
        cvA.levelParams cvA.type nP nM nm ni j r with
    | error e => intro h; exact nomatch h
    | ok r₁ => ?_
    intro h
    try dsimp only at h
    revert h
    cases hrest : checkIotaRules (fueledOps F) env' env₀ f cvA.name
        cvA.levelParams cvA.type nP nM nm ni (j + 1) rest with
    | error e => intro h; exact nomatch h
    | ok rest' => ?_
    intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · exact checkIotaRule_inv hr1
    · exact ih (j + 1) rest' hrest r' hr'

set_option maxHeartbeats 1600000 in
/-- The kernel-checked eta pins of a block's capability record,
carried through the member fold: `find?`-facts (preserved by fresh
installs) and plain syntax about the model-side statement. -/
def EtaPins (env' : Env) (T : Name) (lps : List Name)
    (caps : IndCaps) : Prop :=
  (caps.eta = true →
  ∃ (tcv : ConstantVal) (tval : Expr) (cvmT : ConstantVal) (mvalT : Expr)
    (sbinders tbindersM : List (Name × Expr × BinderMeta))
    (sbody tbodyM tySlot : Expr) (ℓA : Level),
    env'.find? ((T.str "_model").str "eta") = some (.thmInfo tcv tval) ∧
    tcv.levelParams = lps ∧
    env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT) ∧
    cvmT.levelParams = lps ∧
    (∃ cvmC mvalC, env'.find? (caps.etaCtor.str "_model") =
      some (.defnInfo cvmC mvalC) ∧ cvmC.levelParams = lps) ∧
    (∀ j, j < caps.etaFields → ∃ cvmj mvalj,
      env'.find? (projModelName T j) = some (.defnInfo cvmj mvalj) ∧
      cvmj.levelParams = lps) ∧
    env'.find? eqName = some eqA ∧
    tcv.type.stripPis (caps.etaParams + 1) = some (sbinders, sbody) ∧
    cvmT.type.stripPis caps.etaParams = some (tbindersM, tbodyM) ∧
    (∀ (k : Nat) (b b' : Name × Expr × BinderMeta), k < caps.etaParams →
      sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.2.1 = b'.2.1) ∧
    (∃ nx mx, sbinders[caps.etaParams]? = some (nx,
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range caps.etaParams).map fun k =>
          Expr.bvar (caps.etaParams - 1 - k)), mx)) ∧
    sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot, .bvar 0,
       Expr.mkAppN (.const (caps.etaCtor.str "_model") (lps.map .param))
        (((List.range caps.etaParams).map fun k =>
            Expr.bvar (caps.etaParams - k)) ++
         (List.range caps.etaFields).map fun j => Expr.mkAppN
           (.const (projModelName T j) (lps.map .param))
           (((List.range caps.etaParams).map fun k =>
               Expr.bvar (caps.etaParams - k)) ++
            [Expr.bvar 0]))]) ∧
  (caps.unitlike = true →
  ∃ (tcv : ConstantVal) (tval : Expr) (cvmT : ConstantVal) (mvalT : Expr)
    (sbinders tbindersM : List (Name × Expr × BinderMeta))
    (sbody tbodyM tySlot : Expr) (ℓA : Level),
    env'.find? ((T.str "_model").str "unitlike") =
      some (.thmInfo tcv tval) ∧
    tcv.levelParams = lps ∧
    env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT) ∧
    cvmT.levelParams = lps ∧
    env'.find? eqName = some eqA ∧
    tcv.type.stripPis (caps.unitParams + 2) = some (sbinders, sbody) ∧
    cvmT.type.stripPis caps.unitParams = some (tbindersM, tbodyM) ∧
    (∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      k < caps.unitParams →
      sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.2.1 = b'.2.1) ∧
    (∃ nx mx, sbinders[caps.unitParams]? = some (nx,
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range caps.unitParams).map fun k =>
          Expr.bvar (caps.unitParams - 1 - k)), mx)) ∧
    (∃ ny my, sbinders[caps.unitParams + 1]? = some (ny,
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range caps.unitParams).map fun k =>
          Expr.bvar (caps.unitParams - k)), my)) ∧
    sbody = Expr.mkAppN (.const eqName [ℓA]) [tySlot, .bvar 1, .bvar 0])

set_option maxHeartbeats 3200000 in
/-- Invert a positive unit-capability check into the stored pins. -/
theorem checkUnitThm_inv {env' : Env} {T : Name}
    {lps : List Name} {nP : Nat}
    (h : checkUnitThm env' T lps nP = true) :
    ∃ (tcv : ConstantVal) (tval : Expr) (cvmT : ConstantVal)
      (mvalT : Expr)
      (sbinders tbindersM : List (Name × Expr × BinderMeta))
      (sbody tbodyM tySlot : Expr) (ℓA : Level),
      env'.find? ((T.str "_model").str "unitlike") =
        some (.thmInfo tcv tval) ∧
      tcv.levelParams = lps ∧
      env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT) ∧
      cvmT.levelParams = lps ∧
      env'.find? eqName = some eqA ∧
      tcv.type.stripPis (nP + 2) = some (sbinders, sbody) ∧
      cvmT.type.stripPis nP = some (tbindersM, tbodyM) ∧
      (∀ (k : Nat) (b b' : Name × Expr × BinderMeta), k < nP →
        sbinders[k]? = some b → tbindersM[k]? = some b' →
        b.2.1 = b'.2.1) ∧
      (∃ nx mx, sbinders[nP]? = some (nx,
        Expr.mkAppN (.const (T.str "_model") (lps.map .param))
          ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx)) ∧
      (∃ ny my, sbinders[nP + 1]? = some (ny,
        Expr.mkAppN (.const (T.str "_model") (lps.map .param))
          ((List.range nP).map fun k => Expr.bvar (nP - k)), my)) ∧
      sbody = Expr.mkAppN (.const eqName [ℓA])
        [tySlot, .bvar 1, .bvar 0] := by
  rw [checkUnitThm] at h
  revert h
  match hthm : env'.find? ((T.str "_model").str "unitlike") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo tcv tval) => ?_
  intro h
  revert h
  match hTm : env'.find? (T.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvmT mvalT) => ?_
  intro h
  revert h
  match heqf : env'.find? eqName with
  | none => intro h; exact nomatch h
  | some eqStored => ?_
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨heqA, htlps⟩, hTlps⟩ := h.1
  have hrest := h.2
  revert hrest
  match hS_strip : tcv.type.stripPis (nP + 2) with
  | none => intro hrest; exact nomatch hrest
  | some (sbinders, sbody) => ?_
  intro hrest
  revert hrest
  match hTm_strip : cvmT.type.stripPis nP with
  | none => intro hrest; exact nomatch hrest
  | some (tbindersM, tbodyM) => ?_
  intro hrest
  simp only [Bool.and_eq_true] at hrest
  obtain ⟨⟨⟨hdomsB, hxdomB⟩, hydomB⟩, hbodyB⟩ := hrest
  have hdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta), k < nP →
      sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.2.1 = b'.2.1 := by
    intro k b b' hk hb hb'
    exact domsMatchAux_inv hdomsB hk
      (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
  have hxdom : ∃ nx mx, sbinders[nP]? = some (nx,
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx) := by
    revert hxdomB
    match hbx : sbinders[nP]? with
    | none => intro hx; exact nomatch hx
    | some (nx, xdom, mx) =>
      intro hx
      exact ⟨nx, mx, by rw [eq_of_beq hx]⟩
  have hydom : ∃ ny my, sbinders[nP + 1]? = some (ny,
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - k)), my) := by
    revert hydomB
    match hby : sbinders[nP + 1]? with
    | none => intro hy; exact nomatch hy
    | some (ny, ydom, my) =>
      intro hy
      exact ⟨ny, my, by rw [eq_of_beq hy]⟩
  revert hbodyB
  match hsb : sbody with
  | .app (.app (.app (.const c ℓs) tySlot) lhsC) rhsC => ?_
  | .bvar _ => intro hb; exact nomatch hb
  | .fvar _ _ _ => intro hb; exact nomatch hb
  | .sort _ => intro hb; exact nomatch hb
  | .const _ _ => intro hb; exact nomatch hb
  | .lam _ _ _ _ => intro hb; exact nomatch hb
  | .forallE _ _ _ _ => intro hb; exact nomatch hb
  | .letE _ _ _ _ => intro hb; exact nomatch hb
  | .lit _ => intro hb; exact nomatch hb
  | .proj _ _ _ => intro hb; exact nomatch hb
  | .app (.bvar _) _ => intro hb; exact nomatch hb
  | .app (.fvar _ _ _) _ => intro hb; exact nomatch hb
  | .app (.sort _) _ => intro hb; exact nomatch hb
  | .app (.const _ _) _ => intro hb; exact nomatch hb
  | .app (.lam _ _ _ _) _ => intro hb; exact nomatch hb
  | .app (.forallE _ _ _ _) _ => intro hb; exact nomatch hb
  | .app (.letE _ _ _ _) _ => intro hb; exact nomatch hb
  | .app (.lit _) _ => intro hb; exact nomatch hb
  | .app (.proj _ _ _) _ => intro hb; exact nomatch hb
  | .app (.app (.bvar _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.fvar _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.sort _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.const _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.lam _ _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.forallE _ _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.letE _ _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.lit _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.proj _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.bvar _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.fvar _ _ _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.sort _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.app _ _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.lam _ _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.forallE _ _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.letE _ _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.lit _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.proj _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  intro hb
  revert hb
  match ℓs with
  | [] => intro hb; exact nomatch hb
  | _ :: _ :: _ => intro hb; exact nomatch hb
  | [ℓA] => ?_
  intro hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨hceq, hlhs⟩, hrhs⟩ := hb
  refine ⟨tcv, tval, cvmT, mvalT, sbinders, tbindersM, _, tbodyM,
    tySlot, ℓA, rfl, eq_of_beq htlps, rfl, eq_of_beq hTlps,
    (by rw [eq_of_beq heqA]), hS_strip, hTm_strip, hdoms, hxdom, hydom,
    ?_⟩
  rw [eq_of_beq hceq, eq_of_beq hlhs, eq_of_beq hrhs]
  rfl

set_option maxHeartbeats 3200000 in
/-- Invert a positive eta-capability check into the stored pins. -/
theorem checkEtaThm_inv {env' : Env} {T ctorName : Name}
    {lps : List Name} {nP nF : Nat}
    (h : checkEtaThm env' T ctorName lps nP nF = true) :
    ∃ (tcv : ConstantVal) (tval : Expr) (cvmT : ConstantVal)
      (mvalT : Expr)
      (sbinders tbindersM : List (Name × Expr × BinderMeta))
      (sbody tbodyM tySlot : Expr) (ℓA : Level),
      env'.find? ((T.str "_model").str "eta") =
        some (.thmInfo tcv tval) ∧
      tcv.levelParams = lps ∧
      env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT) ∧
      cvmT.levelParams = lps ∧
      (∃ cvmC mvalC, env'.find? (ctorName.str "_model") =
        some (.defnInfo cvmC mvalC) ∧ cvmC.levelParams = lps) ∧
      (∀ j, j < nF → ∃ cvmj mvalj,
        env'.find? (projModelName T j) = some (.defnInfo cvmj mvalj) ∧
        cvmj.levelParams = lps) ∧
      env'.find? eqName = some eqA ∧
      tcv.type.stripPis (nP + 1) = some (sbinders, sbody) ∧
      cvmT.type.stripPis nP = some (tbindersM, tbodyM) ∧
      (∀ (k : Nat) (b b' : Name × Expr × BinderMeta), k < nP →
        sbinders[k]? = some b → tbindersM[k]? = some b' →
        b.2.1 = b'.2.1) ∧
      (∃ nx mx, sbinders[nP]? = some (nx,
        Expr.mkAppN (.const (T.str "_model") (lps.map .param))
          ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx)) ∧
      sbody = Expr.mkAppN (.const eqName [ℓA])
        [tySlot, .bvar 0,
         Expr.mkAppN (.const (ctorName.str "_model") (lps.map .param))
          (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
           (List.range nF).map fun j => Expr.mkAppN
             (.const (projModelName T j) (lps.map .param))
             (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
              [Expr.bvar 0]))] := by
  rw [checkEtaThm] at h
  revert h
  match hthm : env'.find? ((T.str "_model").str "eta") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo tcv tval) => ?_
  intro h
  revert h
  match hTm : env'.find? (T.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvmT mvalT) => ?_
  intro h
  revert h
  match hCm : env'.find? (ctorName.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvmC mvalC) => ?_
  intro h
  revert h
  match heqf : env'.find? eqName with
  | none => intro h; exact nomatch h
  | some eqStored => ?_
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨heqA, htlps⟩, hTlps⟩, hClps⟩, hproj⟩, hrest⟩ := h
  have hprojf : ∀ j, j < nF → ∃ cvmj mvalj,
      env'.find? (projModelName T j) = some (.defnInfo cvmj mvalj) ∧
      cvmj.levelParams = lps := by
    intro j hj
    have h1 := List.all_eq_true.mp hproj j (List.mem_range.mpr hj)
    revert h1
    match hfj : env'.find? (projModelName T j) with
    | none => intro h1; exact nomatch h1
    | some (.axiomInfo _) => intro h1; exact nomatch h1
    | some (.thmInfo _ _) => intro h1; exact nomatch h1
    | some (.indInfo _ _) => intro h1; exact nomatch h1
    | some (.ctorInfo _ _ _) => intro h1; exact nomatch h1
    | some (.recInfo _ _ _ _ _ _) => intro h1; exact nomatch h1
    | some (.defnInfo cvmj mvalj) =>
      intro h1
      exact ⟨cvmj, mvalj, rfl, eq_of_beq h1⟩
  revert hrest
  match hS_strip : tcv.type.stripPis (nP + 1) with
  | none => intro hrest; exact nomatch hrest
  | some (sbinders, sbody) => ?_
  intro hrest
  revert hrest
  match hTm_strip : cvmT.type.stripPis nP with
  | none => intro hrest; exact nomatch hrest
  | some (tbindersM, tbodyM) => ?_
  intro hrest
  simp only [Bool.and_eq_true] at hrest
  obtain ⟨⟨hdomsB, hxdomB⟩, hbodyB⟩ := hrest
  have htMlen : tbindersM.length = nP := Expr.stripPis_length _ hTm_strip
  have hdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta), k < nP →
      sbinders[k]? = some b → tbindersM[k]? = some b' →
      b.2.1 = b'.2.1 := by
    intro k b b' hk hb hb'
    exact domsMatchAux_inv hdomsB hk
      (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
  have hxdom : ∃ nx mx, sbinders[nP]? = some (nx,
      Expr.mkAppN (.const (T.str "_model") (lps.map .param))
        ((List.range nP).map fun k => Expr.bvar (nP - 1 - k)), mx) := by
    revert hxdomB
    match hbx : sbinders[nP]? with
    | none => intro hx; exact nomatch hx
    | some (nx, xdom, mx) =>
      intro hx
      exact ⟨nx, mx, by rw [eq_of_beq hx]⟩
  revert hbodyB
  match hsb : sbody with
  | .app (.app (.app (.const c ℓs) tySlot) lhsC) rhsC => ?_
  | .bvar _ => intro hb; exact nomatch hb
  | .fvar _ _ _ => intro hb; exact nomatch hb
  | .sort _ => intro hb; exact nomatch hb
  | .const _ _ => intro hb; exact nomatch hb
  | .lam _ _ _ _ => intro hb; exact nomatch hb
  | .forallE _ _ _ _ => intro hb; exact nomatch hb
  | .letE _ _ _ _ => intro hb; exact nomatch hb
  | .lit _ => intro hb; exact nomatch hb
  | .proj _ _ _ => intro hb; exact nomatch hb
  | .app (.bvar _) _ => intro hb; exact nomatch hb
  | .app (.fvar _ _ _) _ => intro hb; exact nomatch hb
  | .app (.sort _) _ => intro hb; exact nomatch hb
  | .app (.const _ _) _ => intro hb; exact nomatch hb
  | .app (.lam _ _ _ _) _ => intro hb; exact nomatch hb
  | .app (.forallE _ _ _ _) _ => intro hb; exact nomatch hb
  | .app (.letE _ _ _ _) _ => intro hb; exact nomatch hb
  | .app (.lit _) _ => intro hb; exact nomatch hb
  | .app (.proj _ _ _) _ => intro hb; exact nomatch hb
  | .app (.app (.bvar _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.fvar _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.sort _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.const _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.lam _ _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.forallE _ _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.letE _ _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.lit _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.proj _ _ _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.bvar _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.fvar _ _ _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.sort _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.app _ _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.lam _ _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.forallE _ _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.letE _ _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  | .app (.app (.app (.lit _) _) _) _ => intro hb; exact nomatch hb
  | .app (.app (.app (.proj _ _ _) _) _) _ =>
    intro hb; exact nomatch hb
  intro hb
  revert hb
  match ℓs with
  | [] => intro hb; exact nomatch hb
  | _ :: _ :: _ => intro hb; exact nomatch hb
  | [ℓA] => ?_
  intro hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨hceq, hlhs⟩, hrhs⟩ := hb
  refine ⟨tcv, tval, cvmT, mvalT, sbinders, tbindersM, _, tbodyM,
    tySlot, ℓA, rfl, eq_of_beq htlps, rfl, eq_of_beq hTlps,
    ⟨cvmC, mvalC, rfl, eq_of_beq hClps⟩, hprojf,
    (by rw [eq_of_beq heqA]), hS_strip,
    hTm_strip, hdoms, hxdom, ?_⟩
  rw [eq_of_beq hceq, eq_of_beq hlhs, eq_of_beq hrhs]
  rfl

/-- The pins persist under a fresh install. -/
theorem EtaPins.step {env' : Env} {c₁ : ConstantInfo} {T : Name}
    {lps : List Name} {caps : IndCaps}
    (h : EtaPins env' T lps caps)
    (hfresh : env'.find? c₁.name = none) :
    EtaPins ⟨c₁ :: env'.consts⟩ T lps caps := by
  have hkeep : ∀ (n : Name) (ci : ConstantInfo),
      env'.find? n = some ci →
      (⟨c₁ :: env'.consts⟩ : Env).find? n = some ci := by
    intro n ci hf
    rw [Env.find?_cons, if_neg ?_]
    · exact hf
    · intro he
      rw [← he, hfresh] at hf
      exact nomatch hf
  refine ⟨?_, ?_⟩
  · intro hcape
    obtain ⟨tcv, tval, cvmT, mvalT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hthm, h2, hTm, h4, ⟨cvmC, mvalC, hCm, hClps⟩, hPj,
      heqf, h8, h9, h10, h11, h12⟩ := h.1 hcape
    refine ⟨tcv, tval, cvmT, mvalT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hkeep _ _ hthm, h2, hkeep _ _ hTm, h4,
      ⟨cvmC, mvalC, hkeep _ _ hCm, hClps⟩, ?_, hkeep _ _ heqf,
      h8, h9, h10, h11, h12⟩
    intro j hj
    obtain ⟨cvmj, mvalj, hfj, hjlps⟩ := hPj j hj
    exact ⟨cvmj, mvalj, hkeep _ _ hfj, hjlps⟩
  · intro hcapu
    obtain ⟨tcv, tval, cvmT, mvalT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hthm, h2, hTm, h4, heqf, h6, h7, h8, h9, h10, h11⟩ :=
      h.2 hcapu
    exact ⟨tcv, tval, cvmT, mvalT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hkeep _ _ hthm, h2, hkeep _ _ hTm, h4,
      hkeep _ _ heqf, h6, h7, h8, h9, h10, h11⟩

end Setlec
