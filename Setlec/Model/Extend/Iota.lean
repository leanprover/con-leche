import Setlec.Model.Extend.Inversions

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

/-- The kernel-checked data of one modeled recursor rule: the
hypothesis kit its fold obligation consumes.  `env` is the environment
before the recursor's installation, `env₀` the provisional one with
the rules-free recursor (in which the rule's right-hand side was
annotated). -/
def RuleChecked (F : Nat) (env env₀ : Env) (f : Name → Name)
    (cvA : ConstantVal) (nP nm ni : Nat) (r : RecRule) : Prop :=
  ∃ (cvj : ConstantVal) (cnF : Nat) (raw : Expr)
    (rbinders tbinders cbinders sbinders :
      List (Name × Expr × BinderMeta))
    (rbody tybody cbody sbody : Expr)
    (thmName : Name) (cvt : ConstantVal) (tval : Expr) (ℓA : Level),
    env.find? (RecRule.ctor r) = some (.ctorInfo cvj nP cnF) ∧
    r.nfields = cnF ∧
    annotateCore env₀ F 0 raw = .ok (RecRule.rhs r) ∧
    raw.hasFvar = false ∧ raw.looseBVarsBounded 0 = true ∧
    (RecRule.rhs r).hasFvar = false ∧
    (RecRule.rhs r).looseBVarsBounded 0 = true ∧
    (RecRule.rhs r).stripLams (nP + 1 + nm + cnF) =
      some (rbinders, rbody) ∧
    cvA.type.stripPis (nP + 1 + nm + ni + 1) = some (tbinders, tybody) ∧
    cvj.type.stripPis (nP + cnF) = some (cbinders, cbody) ∧
    cbody.getAppArgs.length = nP + ni ∧
    cvt.type.stripPis ((nP + (1 + nm)) + cnF) = some (sbinders, sbody) ∧
    (∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
      i < nP + 1 + nm →
      rbinders[i]? = some b → tbinders[i]? = some b' →
      b.2.1 = b'.2.1) ∧
    (∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
      rbinders[(nP + (1 + nm)) + i]? = some b →
      cbinders[nP + i]? = some b' →
      b.2.1 = (b'.2.1).liftLooseBVars (1 + nm) i) ∧
    (∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[i]? = some b → rbinders[i]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f) ∧
    sbody = Expr.mkAppN (.const eqName [ℓA])
      [Expr.mkAppN (.bvar (cnF + nm))
        (((cbody.getAppArgs.drop nP).map fun e =>
            (e.liftLooseBVars (1 + nm) cnF).renameConsts f) ++
         [Expr.mkAppN (.const (f (RecRule.ctor r))
            (cvj.levelParams.map .param))
          (((List.range nP).map fun k =>
              Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
           ((List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)))]),
       Expr.mkAppN (.const (f cvA.name) (cvA.levelParams.map .param))
        (((((List.range nP).map fun k =>
            Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
          ((List.range (1 + nm)).map fun k =>
            Expr.bvar (nP + 1 + nm + cnF - 1 - nP - k))) ++
          ((cbody.getAppArgs.drop nP).map fun e =>
            (e.liftLooseBVars (1 + nm) cnF).renameConsts f)) ++
         [Expr.mkAppN (.const (f (RecRule.ctor r))
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
            ((List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)))]),
       rbody.renameConsts f] ∧
    env.find? thmName = some (.thmInfo cvt tval) ∧
    cvt.levelParams = cvA.levelParams ∧
    (RecRule.rhs r).allLevelParamsDefined cvA.levelParams = true ∧
    (RecRule.rhs r).constsResolve env₀ = true

/-- Invert the pure rule-shape check. -/
theorem checkIotaRuleShape_inv {tyA cvjty rhsA : Expr}
    {nP nM nm ni cnP cnF : Nat}
    {rbinders : List (Name × Expr × BinderMeta)} {rbody : Expr}
    (h : checkIotaRuleShape tyA cvjty rhsA nP nM nm ni cnP cnF =
      some (rbinders, rbody)) :
    ∃ tbinders tybody cbinders cbody,
      rhsA.stripLams (nP + nM + nm + cnF) = some (rbinders, rbody) ∧
      tyA.stripPis (nP + nM + nm + ni + 1) = some (tbinders, tybody) ∧
      cvjty.stripPis (cnP + cnF) = some (cbinders, cbody) ∧
      domsMatchAux (fun _ e => e) rbinders tbinders 0 0 (nP + nM + nm)
        = true ∧
      domsMatchAux (fun i e => e.liftLooseBVars (nM + nm) i) rbinders
        cbinders (nP + nM + nm) cnP cnF = true := by
  unfold checkIotaRuleShape at h
  revert h
  match hstR : rhsA.stripLams (nP + nM + nm + cnF),
      hstT : tyA.stripPis (nP + nM + nm + ni + 1),
      hstC : cvjty.stripPis (cnP + cnF) with
  | some (rb, rb'), some (tb, tb'), some (cb, cb') => ?_
  | none, _, _ => intro h; exact nomatch h
  | some _, none, _ => intro h; exact nomatch h
  | some _, some _, none => intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  split
  case isTrue hd =>
    intro h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at hd
    first
    | exact ⟨tb, tb', cb, cb', rfl, rfl, rfl, hd.1, hd.2⟩
    | exact ⟨tb, tb', cb, cb', hstR, hstT, hstC, hd.1, hd.2⟩
    | exact ⟨tb, tb', cb, cb', rfl, hstT, hstC, hd.1, hd.2⟩
    | exact ⟨tb, tb', cb, cb', rfl, rfl, hstC, hd.1, hd.2⟩
  case isFalse =>
    intro h
    exact nomatch h

/-- Invert the pure statement-shape check. -/
theorem checkIotaStmtShape_inv {f : Name → Name} {cvName ctorName : Name}
    {lps cvjlps : List Name} {nP nM nm ni cnF : Nat} {cvjty cvtType : Expr}
    {rbinders : List (Name × Expr × BinderMeta)} {rbody : Expr}
    (h : checkIotaStmtShape f cvName ctorName lps cvjlps nP nM nm ni cnF
      cvjty cvtType rbinders rbody = true) :
    ∃ sbinders sbody mna mdomA mbm ℓA cbindersS cbodyS,
      cvtType.stripPis (nP + nM + nm + cnF) = some (sbinders, sbody) ∧
      rbinders[nP]? = some (mna, mdomA, mbm) ∧
      cvjty.stripPis (nP + cnF) = some (cbindersS, cbodyS) ∧
      mdomA.resultSort = some ℓA ∧
      cbodyS.getAppArgs.length = nP + ni ∧
      domsMatchAux (fun _ e => e.renameConsts f) sbinders rbinders 0 0
        (nP + nM + nm + cnF) = true ∧
      sbody = Expr.mkAppN (.const eqName [ℓA])
        [Expr.mkAppN (Expr.bvar (cnF + nm + (nM - 1)))
          (((cbodyS.getAppArgs.drop nP).map fun e =>
              (e.liftLooseBVars (nM + nm) cnF).renameConsts f) ++
           [Expr.mkAppN (.const (f ctorName) (cvjlps.map .param))
            (((List.range nP).map fun k =>
                Expr.bvar (nP + nM + nm + cnF - 1 - k)) ++
             ((List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)))]),
         Expr.mkAppN (.const (f cvName) (lps.map .param))
          (((((List.range nP).map fun k =>
              Expr.bvar (nP + nM + nm + cnF - 1 - k)) ++
            ((List.range (nM + nm)).map fun k =>
              Expr.bvar (nP + nM + nm + cnF - 1 - nP - k))) ++
            ((cbodyS.getAppArgs.drop nP).map fun e =>
              (e.liftLooseBVars (nM + nm) cnF).renameConsts f)) ++
           [Expr.mkAppN (.const (f ctorName) (cvjlps.map .param))
             (((List.range nP).map fun k =>
                 Expr.bvar (nP + nM + nm + cnF - 1 - k)) ++
              ((List.range cnF).map fun k =>
                Expr.bvar (cnF - 1 - k)))]),
         rbody.renameConsts f] := by
  unfold checkIotaStmtShape at h
  revert h
  match hstS : cvtType.stripPis (nP + nM + nm + cnF),
      hmb : rbinders[nP]?,
      hstC : cvjty.stripPis (nP + cnF) with
  | some (sbinders, sbody), some (mna, mdomA, mbm),
      some (cbindersS, cbodyS) => ?_
  | none, _, _ => intro h; exact nomatch h
  | some _, none, _ => intro h; exact nomatch h
  | some _, some _, none => intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hms : mdomA.resultSort with
  | none => intro h; exact nomatch h
  | some ℓA => ?_
  intro h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  exact ⟨_, _, _, _, _, _, _, _, rfl, rfl, rfl, hms, eq_of_beq h.1.1,
    h.1.2, eq_of_beq h.2⟩

/-- Invert a successful `checkIotaRules` run: every returned rule
carries the full `RuleChecked` hypothesis kit. -/
theorem checkIotaRules_inv {env' envSelf : Env} {f : Name → Name}
    {cvA : ConstantVal} {nP nm ni : Nat} :
    ∀ (j : Nat) (rules rules' : List RecRule),
    checkIotaRules (fueledOps F) env' envSelf f cvA.name cvA.levelParams cvA.type
      nP 1 nm ni j rules = .ok rules' →
    ∀ r' ∈ rules', RuleChecked F env' envSelf f cvA nP nm ni r' := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h r' hr'
    simp only [checkIotaRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact nomatch hr'
  | cons r rest ih =>
    intro rules' h r' hr'
    simp only [checkIotaRules, checkIotaRule, fueledOps_annotate,
      fueledOps_inferType, fueledOps_isDefEq, fueledOps_ensureSort,
      fueledOps_whnf, Bind.bind, Except.bind, pure, Except.pure] at h
    revert h
    match hfc : env'.find? r.ctor with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) => intro h; exact nomatch h
    | some (.defnInfo _ _ _) => intro h; exact nomatch h
    | some (.thmInfo _ _) => intro h; exact nomatch h
    | some (.indInfo _ _) => intro h; exact nomatch h
    | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
    | some (.ctorInfo cvj cnP cnF) => ?_
    intro h
    dsimp only at h
    by_cases hcnP : cnP = nP
    case neg => rw [if_neg hcnP] at h; exact nomatch h
    rw [if_pos hcnP] at h
    subst cnP
    try dsimp only at h
    by_cases hnf : r.nfields = cnF
    case neg => rw [if_neg hnf] at h; exact nomatch h
    rw [if_pos hnf] at h
    try dsimp only at h
    by_cases hrb : r.rhs.looseBVarsBounded 0 = true
    case neg => rw [if_neg hrb] at h; exact nomatch h
    rw [if_pos hrb] at h
    try dsimp only at h
    by_cases hrf : r.rhs.hasFvar = true
    case pos => rw [if_pos hrf] at h; exact nomatch h
    rw [if_neg hrf] at h
    have hrfF : r.rhs.hasFvar = false := by
      revert hrf; cases r.rhs.hasFvar <;> simp
    try dsimp only at h
    cases hann : annotateCore envSelf F 0 r.rhs with
    | error e => rw [hann] at h; exact nomatch h
    | ok rhsA =>
    rw [hann] at h
    try dsimp only at h
    by_cases hrlp : rhsA.allLevelParamsDefined cvA.levelParams = true
    case neg => rw [if_neg hrlp] at h; exact nomatch h
    rw [if_pos hrlp] at h
    try dsimp only at h
    by_cases hrres : rhsA.constsResolve envSelf = true
    case neg => rw [if_neg hrres] at h; exact nomatch h
    rw [if_pos hrres] at h
    try dsimp only at h
    revert h
    match hshape : checkIotaRuleShape cvA.type cvj.type rhsA nP 1 nm ni
        nP cnF with
    | none => intro h; exact nomatch h
    | some pr => ?_
    intro h
    obtain ⟨rbinders, rbody⟩ := pr
    dsimp only at h
    obtain ⟨tbinders, tybody, cbinders, cbody, hstR, hstT, hstC, hallPre,
      hallF⟩ := checkIotaRuleShape_inv hshape
    cases hity : inferTypeCore envSelf F 0 rhsA with
    | error e => rw [hity] at h; exact nomatch h
    | ok rhsTy =>
    rw [hity] at h
    try dsimp only at h
    revert h
    match hbuild : buildIotaStmt f cvA.name r.ctor cvA.levelParams
        cvj.levelParams nP 1 nm ni cnF cvA.type cvj.type r.rhs with
    | none => intro h; exact nomatch h
    | some stmtRaw => ?_
    intro h
    dsimp only at h
    cases hstmtA : annotateCore env' F 0 stmtRaw with
    | error e => rw [hstmtA] at h; exact nomatch h
    | ok stmtA =>
    rw [hstmtA] at h
    try dsimp only at h
    revert h
    match hfthm : env'.find? ((cvA.name.str "_model").str s!"iota_{j}") with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) => intro h; exact nomatch h
    | some (.defnInfo _ _ _) => intro h; exact nomatch h
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
    by_cases hbeq : (cvt.type == stmtA) = true
    case neg => rw [if_neg hbeq] at h; exact nomatch h
    rw [if_pos hbeq] at h
    try dsimp only at h
    by_cases hstmt : checkIotaStmtShape f cvA.name r.ctor cvA.levelParams
        cvj.levelParams nP 1 nm ni cnF cvj.type cvt.type rbinders
        rbody = true
    case neg => rw [if_neg hstmt] at h; exact nomatch h
    rw [if_pos hstmt] at h
    try dsimp only at h
    obtain ⟨sbinders, sbody, mna, mdomA, mbm, ℓA, cbindersS, cbodyS,
      hstS, hmb, hstC2, hms, hclen2, hallS, hsbeq⟩ :=
      checkIotaStmtShape_inv hstmt
    cases hrec : checkIotaRules (fueledOps F) env' envSelf f cvA.name cvA.levelParams
        cvA.type nP 1 nm ni (j + 1) rest with
    | error e => rw [hrec] at h; exact nomatch h
    | ok rest' =>
    rw [hrec] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    case inr => exact ih (j + 1) rest' hrec r' hr'
    -- the head rule
    unfold RuleChecked
    have hrlen : rbinders.length = nP + 1 + nm + cnF :=
      Expr.stripLams_length _ hstR
    have htlen : tbinders.length = nP + 1 + nm + ni + 1 :=
      Expr.stripPis_length _ hstT
    have hclen : cbinders.length = nP + cnF :=
      Expr.stripPis_length _ hstC
    have hslen : sbinders.length = nP + 1 + nm + cnF :=
      Expr.stripPis_length _ hstS
    have hcc : cbinders = cbindersS ∧ cbody = cbodyS := by
      have h2 := hstC.symm.trans hstC2
      simpa using h2
    obtain ⟨-, rfl⟩ := hcc
    refine ⟨cvj, cnF, r.rhs, rbinders, tbinders, cbinders, sbinders,
      rbody, tybody, cbody, sbody,
      (cvA.name.str "_model").str s!"iota_{j}", cvt, tval, ℓA,
      hfc, hnf, hann, hrfF, hrb, ?_, ?_, hstR, hstT, hstC, hclen2, ?_,
      ?_, ?_, ?_, ?_, hfthm, hlpt, hrlp, hrres⟩
    · -- rhsA has no fvars
      exact not_hasFvar_of_fvarsBelow_zero
        ((annotateCore_WScoped F _ hann (WScoped.of_not_hasFvar hrfF)).fvarsBelow)
    · -- rhsA stays closed
      exact annotateCore_looseBVars F _ hann hrb
    · -- statement strip at the reassociated arity
      rw [show (nP + (1 + nm)) + cnF = nP + 1 + nm + cnF from by omega]
      exact hstS
    · -- prefix domains
      intro i b b' hi hb hb'
      exact domsMatchAux_inv hallPre hi
        (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
    · -- field domains
      intro i b b' hbF hcF
      have hicnF : i < cnF := by
        rcases Nat.lt_or_ge i cnF with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at hcF
          exact nomatch hcF
      exact domsMatchAux_inv hallF hicnF
        (by rw [show nP + 1 + nm + i = (nP + (1 + nm)) + i from by omega]
            exact hbF) hcF
    · -- statement domains
      intro i b b' hsb hrbi
      have hi : i < nP + 1 + nm + cnF := by
        rcases Nat.lt_or_ge i (nP + 1 + nm + cnF) with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at hsb
          exact nomatch hsb
      exact domsMatchAux_inv hallS hi
        (by rw [Nat.zero_add]; exact hsb) (by rw [Nat.zero_add]; exact hrbi)
    · -- the pinned equation body
      exact hsbeq

set_option maxHeartbeats 1600000 in
/-- The kernel-checked eta pins of a block's capability record,
carried through the member fold: `find?`-facts (preserved by fresh
installs) and plain syntax about the model-side statement. -/
def EtaPins (env' : Env) (T : Name) (lps : List Name)
    (caps : IndCaps) : Prop :=
  (caps.eta = true →
  ∃ (tcv : ConstantVal) (tval : Expr) (cvmT : ConstantVal) (mvalT : Expr)
    (hmcvmT : ReducibilityHint)
    (sbinders tbindersM : List (Name × Expr × BinderMeta))
    (sbody tbodyM tySlot : Expr) (ℓA : Level),
    env'.find? ((T.str "_model").str "eta") = some (.thmInfo tcv tval) ∧
    tcv.levelParams = lps ∧
    env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT hmcvmT) ∧
    cvmT.levelParams = lps ∧
    (∃ cvmC mvalC hmcvmC, env'.find? (caps.etaCtor.str "_model") =
      some (.defnInfo cvmC mvalC hmcvmC) ∧ cvmC.levelParams = lps) ∧
    (∀ j, j < caps.etaFields → ∃ cvmj mvalj hmcvmj,
      env'.find? (projModelName T j) = some (.defnInfo cvmj mvalj hmcvmj) ∧
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
    (hmcvmT : ReducibilityHint)
    (sbinders tbindersM : List (Name × Expr × BinderMeta))
    (sbody tbodyM tySlot : Expr) (ℓA : Level),
    env'.find? ((T.str "_model").str "unitlike") =
      some (.thmInfo tcv tval) ∧
    tcv.levelParams = lps ∧
    env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT hmcvmT) ∧
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
      (mvalT : Expr) (hmcvmT : ReducibilityHint)
      (sbinders tbindersM : List (Name × Expr × BinderMeta))
      (sbody tbodyM tySlot : Expr) (ℓA : Level),
      env'.find? ((T.str "_model").str "unitlike") =
        some (.thmInfo tcv tval) ∧
      tcv.levelParams = lps ∧
      env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT hmcvmT) ∧
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
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
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
  | some (.defnInfo cvmT mvalT hmcvmT) => ?_
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
  refine ⟨tcv, tval, cvmT, mvalT, hmcvmT, sbinders, tbindersM, _, tbodyM,
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
      (mvalT : Expr) (hmcvmT : ReducibilityHint)
      (sbinders tbindersM : List (Name × Expr × BinderMeta))
      (sbody tbodyM tySlot : Expr) (ℓA : Level),
      env'.find? ((T.str "_model").str "eta") =
        some (.thmInfo tcv tval) ∧
      tcv.levelParams = lps ∧
      env'.find? (T.str "_model") = some (.defnInfo cvmT mvalT hmcvmT) ∧
      cvmT.levelParams = lps ∧
      (∃ cvmC mvalC hmcvmC, env'.find? (ctorName.str "_model") =
        some (.defnInfo cvmC mvalC hmcvmC) ∧ cvmC.levelParams = lps) ∧
      (∀ j, j < nF → ∃ cvmj mvalj hmcvmj,
        env'.find? (projModelName T j) = some (.defnInfo cvmj mvalj hmcvmj) ∧
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
  | some (.defnInfo _ _ _) => intro h; exact nomatch h
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
  | some (.defnInfo cvmT mvalT hmcvmT) => ?_
  intro h
  revert h
  match hCm : env'.find? (ctorName.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvmC mvalC hmcvmC) => ?_
  intro h
  revert h
  match heqf : env'.find? eqName with
  | none => intro h; exact nomatch h
  | some eqStored => ?_
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨heqA, htlps⟩, hTlps⟩, hClps⟩, hproj⟩, hrest⟩ := h
  have hprojf : ∀ j, j < nF → ∃ cvmj mvalj hmcvmj,
      env'.find? (projModelName T j) = some (.defnInfo cvmj mvalj hmcvmj) ∧
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
    | some (.defnInfo cvmj mvalj hmcvmj) =>
      intro h1
      exact ⟨cvmj, mvalj, hmcvmj, rfl, eq_of_beq h1⟩
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
  refine ⟨tcv, tval, cvmT, mvalT, hmcvmT, sbinders, tbindersM, _, tbodyM,
    tySlot, ℓA, rfl, eq_of_beq htlps, rfl, eq_of_beq hTlps,
    ⟨cvmC, mvalC, hmcvmC, rfl, eq_of_beq hClps⟩, hprojf,
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
    obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hthm, h2, hTm, h4, ⟨cvmC, mvalC, hmC, hCm, hClps⟩, hPj,
      heqf, h8, h9, h10, h11, h12⟩ := h.1 hcape
    refine ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hkeep _ _ hthm, h2, hkeep _ _ hTm, h4,
      ⟨cvmC, mvalC, hmC, hkeep _ _ hCm, hClps⟩, ?_, hkeep _ _ heqf,
      h8, h9, h10, h11, h12⟩
    intro j hj
    obtain ⟨cvmj, mvalj, hmj, hfj, hjlps⟩ := hPj j hj
    exact ⟨cvmj, mvalj, hmj, hkeep _ _ hfj, hjlps⟩
  · intro hcapu
    obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hthm, h2, hTm, h4, heqf, h6, h7, h8, h9, h10, h11⟩ :=
      h.2 hcapu
    exact ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody, tbodyM,
      tySlot, ℓA, hkeep _ _ hthm, h2, hkeep _ _ hTm, h4,
      hkeep _ _ heqf, h6, h7, h8, h9, h10, h11⟩

end Setlec
