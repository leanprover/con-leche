import Setlec.Kernel.Checker
import Setlec.Model.Annotate
import Setlec.Model.BasisInstall
import Setlec.Model.IndInstall
import Setlec.Model.ProjInstall
import Setlec.Model.EtaInstall
import Setlec.Model.Extend.BasisOne
import Setlec.Model.Extend.Model
import Setlec.Model.Extend.Sibs
import Setlec.Model.Extend.Inversions

/-!
# Model extension steps

One lemma per way the checker extends the environment: plain constants
(`extend_model`), pinned basis constants (`extend_basis_one`), opaque
modeled inductive-kind members (`extend_modeled_one`) and modeled
recursors with their checked iota rules (`extend_modeled_rec`,
consuming the `RuleChecked` bundles that `checkIotaRules_inv`
extracts).  `Setlec.Model.Consistency` assembles these into
`checkDecl_sound`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Extend a model by one opaque modeled inductive-kind member (an
inductive type former or constructor; the recursor carries rule
obligations and is handled separately): its value is its `_model`
counterpart's, and its type interprets identically through the block
renaming. -/
theorem extend_modeled_one {env : Env} (m : EnvModel V env)
    (ci : ConstantInfo) (f : Name → Name) (mname : Name)
    {cvm : ConstantVal} {mval : Expr}
    (hfind' : env.find? ci.name = none)
    (hnres : reservedBasisNames.contains ci.name = false)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (hkind : (∃ cv caps, ci = .indInfo cv caps) ∨
      (∃ cv nP nF, ci = .ctorInfo cv nP nF) ∨
      (∃ cv nP nM nm ni, ci = .recInfo cv nP nM nm ni []))
    (hmodel : env.find? mname = some (.defnInfo cvm mval))
    (hlps : cvm.levelParams = ci.toConstantVal.levelParams)
    (hren : ci.toConstantVal.type.renameConsts f = cvm.type)
    (hro : RenameOk m.val env f)
    (hmodm : ((∃ cv caps, ci = .indInfo cv caps) ∨
        (∃ cv cnP cnF, ci = .ctorInfo cv cnP cnF)) →
      (env.find? (ci.name.str "_model")).isSome = true ∧
      ∀ ψ : Name → Nat, m.val mname ψ = m.val (ci.name.str "_model") ψ)
    (hprojm : ∀ (T : Name) (j : Nat), ci.name = projFnName T j →
      (env.find? (projModelName T j)).isSome = true ∧
      ∀ ψ : Name → Nat, m.val mname ψ = m.val (projModelName T j) ψ)
    (hetaLm : ∀ cv caps, ci = .indInfo cv caps → caps.eta = true →
      reservedBasisNames.contains ci.name = false →
      (env.find? (caps.etaCtor.str "_model")).isSome = true ∧
      (∀ j, j < caps.etaFields →
        (env.find? (projModelName ci.name j)).isSome = true) ∧
      ∀ (φ'' : Name → Nat) (us : List Level) (ps : List V) (x : V)
        (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V)
        (rest : Expr),
        ps.length = caps.etaParams →
        x ∈ˢ SpineFold V
          (m.val mname (Level.substFn φ'' cv.levelParams us)) ps →
        TeleFit V m.val env φ'' d₁ ρ₁
          (cv.type.instantiateLevelParams cv.levelParams us) ps d₂ ρ₂
          rest →
        x = SpineFold V (m.val (caps.etaCtor.str "_model")
            (Level.substFn φ'' cv.levelParams us))
          (ps ++ (List.range caps.etaFields).map fun j =>
            SpineFold V (m.val (projModelName ci.name j)
              (Level.substFn φ'' cv.levelParams us)) (ps ++ [x])))
    (hunitLm : ∀ cv caps, ci = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains ci.name = false →
      ∀ (φ'' : Name → Nat) (us : List Level) (ps : List V) (x y : V)
        (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V)
        (rest : Expr),
        ps.length = caps.unitParams →
        x ∈ˢ SpineFold V
          (m.val mname (Level.substFn φ'' cv.levelParams us)) ps →
        y ∈ˢ SpineFold V
          (m.val mname (Level.substFn φ'' cv.levelParams us)) ps →
        TeleFit V m.val env φ'' d₁ ρ₁
          (cv.type.instantiateLevelParams cv.levelParams us) ps d₂ ρ₂
          rest →
        x = y) :
    ∃ m' : EnvModel V ⟨ci :: env.consts⟩,
      (∀ ψ, m'.val ci.name ψ = m.val mname ψ) ∧
      (∀ n ψ, n ≠ ci.name → m'.val n ψ = m.val n ψ) := by
  have hmm : ConstantInfo.defnInfo cvm mval ∈ env.consts :=
    List.mem_of_find?_eq_some hmodel
  have hkey : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m.val env ψ ci.toConstantVal.type = some T ∧
        m.val (mname) ψ ∈ˢ T := by
    intro ψ
    obtain ⟨T, hT, hmem⟩ := m.mem_type _ hmm ψ
    have hname : cvm.name = mname := by
      have := List.find?_some hmodel
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
    refine ⟨T, ?_, by rw [← hname]; exact hmem⟩
    have hri : interpClosed V m.val env ψ (ci.toConstantVal.type.renameConsts f) =
        interpClosed V m.val env ψ ci.toConstantVal.type :=
      interp_renameConsts hro _ 0 (rho0 V)
    rw [← hri, hren]
    exact hT
  exact extend_basis_one m ci (fun ψ => m.val (mname) ψ)
    hfind' hwf htyres0
    (fun cv2 value2 => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nM', nm', ni', rfl⟩ <;> simp)
    hkey
    (fun ψ₁ ψ₂ hψ => by
      refine m.val_params _ _ hmodel ψ₁ ψ₂ ?_
      intro p hp
      refine hψ p ?_
      rwa [show (ConstantInfo.defnInfo cvm mval).toConstantVal = cvm from rfl,
        hlps] at hp)
    (fun ψ => by
      obtain ⟨hA, -⟩ := m.annot_ok _ hmm ψ
      have hA' : AnnotOk V m.val env ψ 0 (rho0 V)
          (ci.toConstantVal.type.renameConsts f) := by
        rw [hren]; exact hA
      exact AnnotOk_renameConsts hro _ 0 (rho0 V) hA')
    (fun cv caps heq hn => absurd (hn ▸ hnres) (by decide))
    (fun cv nP nF heq hn => absurd (hn ▸ hnres) (by decide))
    (fun cv caps heq hn => absurd (hn ▸ hnres) (by decide))
    (fun hn => absurd (hn ▸ hnres) (by decide))
    (fun _ hres2 => absurd (hres2 ▸ hnres) (by simp))
    (fun cv nP nM nm ni rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nM', nm', ni', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · exact ⟨fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide)⟩)
    (fun val' _ _ cvR nP nM nm ni rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nM', nm', ni', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with h1 h2 h3 h4 h5 h6
        subst h6
        intro r hr
        cases hr)
    (fun cvR nP nM nm ni rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nM', nm', ni', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with h1 h2 h3 h4 h5 h6
        subst h6
        intro r hr
        cases hr)
    (fun _ => hmodm) hprojm hetaLm hunitLm

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
    | some (.defnInfo _ _) => intro h; exact nomatch h
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

/-- Extend a model by an installed projection function: a degenerate
recursor (no motive, no minors) whose value is its `_model.proj_i`
counterpart's and whose single rule's fold obligation is discharged by
the checked `proj_i.iota` theorem (`proj_rule_fold`). -/
theorem extend_proj_fn {env : Env} (m : EnvModel V env)
    (cvA : ConstantVal) (nP nF i : Nat) (rule : RecRule)
    (f : Name → Name) (mnameP : Name)
    {cvm : ConstantVal} {mval : Expr} {cvj : ConstantVal}
    (hfind' : env.find? cvA.name = none)
    (hnres : reservedBasisNames.contains cvA.name = false)
    (hwf : ConstWF ⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩
      (.recInfo cvA nP 0 0 0 [rule]))
    (htyres0 : cvA.type.constsResolve env = true)
    (hmodel : env.find? mnameP = some (.defnInfo cvm mval))
    (hlps : cvm.levelParams = cvA.levelParams)
    (hprojm : ∀ (T : Name) (j : Nat), cvA.name = projFnName T j →
      (env.find? (projModelName T j)).isSome = true ∧
      ∀ ψ : Name → Nat, m.val mnameP ψ = m.val (projModelName T j) ψ)
    (hren : cvA.type.renameConsts f = cvm.type)
    (f₀ : Name → Name) (hro : RenameOk m.val env f₀)
    (hff₀ : ∀ n, n ≠ cvA.name → f n = f₀ n)
    (hfself : f cvA.name = mnameP)
    (hfnot : ∀ n, f n ≠ cvA.name)
    (heqfind : env.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m.val eqName ψ'' = eqVal V ψ'')
    (hi : i < nF)
    (hctor : env.find? (RecRule.ctor rule) = some (.ctorInfo cvj nP nF))
    (_hnf : rule.nfields = nF)
    {raw : Expr}
    (hann : annotateCore env F 0 raw = .ok (RecRule.rhs rule))
    (hrawf : raw.hasFvar = false)
    (hrawb : raw.looseBVarsBounded 0 = true)
    (hrhsf : (RecRule.rhs rule).hasFvar = false)
    (hrhsb : (RecRule.rhs rule).looseBVarsBounded 0 = true)
    (hrhsres : (RecRule.rhs rule).constsResolve env = true)
    {rbinders cbinders sbinders : List (Name × Expr × BinderMeta)}
    {rbody cbody sbody tySlot : Expr} {ℓA : Level}
    {thmName : Name} {cvt : ConstantVal} {tval : Expr}
    (hstripR : (RecRule.rhs rule).stripLams (nP + nF) =
      some (rbinders, rbody))
    (hrbody : rbody = .bvar (nF - 1 - i))
    (hC_strip : cvj.type.stripPis (nP + nF) = some (cbinders, cbody))
    (hS_strip : cvt.type.stripPis (nP + nF) = some (sbinders, sbody))
    (hdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      rbinders[k]? = some b → cbinders[k]? = some b' →
      b.2.1 = b'.2.1)
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[k]? = some b → cbinders[k]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f)
    (hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const (f cvA.name) (cvA.levelParams.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const (f (RecRule.ctor rule))
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)])
    (hthm : env.find? thmName = some (.thmInfo cvt tval))
    (_hlpt : cvt.levelParams = cvA.levelParams) :
    ∃ m' : EnvModel V ⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩,
      (∀ ψ, m'.val cvA.name ψ = m.val mnameP ψ) ∧
      (∀ n ψ, n ≠ cvA.name → m'.val n ψ = m.val n ψ) := by
  -- phase 0: install the rules-free provisional recursor
  have hisoRes : ∀ n,
      ((⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env).find? n).isSome
      =
      ((⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env).find? n).isSome := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : cvA.name = n
    · rw [if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
          [rule]).name = n from h),
        if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
          []).name = n from h)]
      rfl
    · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
          [rule]).name = n from h),
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
          []).name = n from h)]
  have hwf₀ : ConstWF (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env)
      (.recInfo cvA nP 0 0 0 []) := by
    obtain ⟨h1, h2, h3, h4, -, -⟩ := hwf
    refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
    · rw [← Expr.constsResolve_congr hisoRes]
      exact h3
    · intro cv2 v2 heq
      exact nomatch heq
    · intro cv nP' nM' nm' ni' rules heq
      injection heq with e1 e2 e3 e4 e5 e6
      subst e6
      intro r hr
      cases hr
  have hren₀ : cvA.type.renameConsts f₀ = cvm.type := by
    rw [← Expr.renameConsts_congr_resolve
      (fun n hn => hff₀ n (fun he => by
        rw [he, hfind'] at hn; exact nomatch hn))
      cvA.type htyres0]
    exact hren
  obtain ⟨m₀, hval₀, hpres₀⟩ := extend_modeled_one m
    (.recInfo cvA nP 0 0 0 []) f₀ (mnameP)
    hfind' hnres hwf₀ htyres0
    (Or.inr (Or.inr ⟨cvA, nP, 0, 0, 0, rfl⟩)) hmodel hlps hren₀ hro
    (fun hk => by
      rcases hk with ⟨_, _, hcon⟩ | ⟨_, _, _, hcon⟩ <;> exact nomatch hcon)
    hprojm
    (fun cv caps hcon => nomatch hcon)
    (fun cv caps hcon => nomatch hcon)
  have henv01 : ∀ n,
      ((⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : cvA.name = n
    · rw [if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
          []).name = n from h),
        if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
          [rule]).name = n from h)]
      rfl
    · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
          []).name = n from h),
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
          [rule]).name = n from h)]
  -- shared transports between the provisional and final environments
  have hfindEq : ∀ n, n ≠ cvA.name →
      (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env).find? n =
      (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env).find? n := by
    intro n hn
    rw [Env.find?_cons, Env.find?_cons,
      if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 [rule]).name = n
        from fun h => hn h.symm),
      if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 []).name = n
        from fun h => hn h.symm)]
  have hitrans : ∀ (e : Expr) (ψ : Name → Nat),
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ e =
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env) ψ e := by
    intro e ψ
    exact (interp_env_ext henv01 natLitSupported_cons_recRules e 0 (rho0 V)).symm
  have hAtrans01 : ∀ (e : Expr) (ψ : Name → Nat) (d : Nat) (ρ : Nat → V),
      AnnotOk V m₀.val (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env)
        ψ d ρ e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ d ρ e :=
    fun e ψ d ρ h => AnnotOk.env_ext henv01 natLitSupported_cons_recRules e d ρ h
  have hCWtrans : ∀ c,
      ConstWF (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env) c →
      ConstWF (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) c := by
    intro c hc
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
    refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
    · rw [Expr.constsResolve_congr hisoRes]
      exact h3
    · intro cv2 v2 heq
      obtain ⟨a, b, cres, dd⟩ := h5 cv2 v2 heq
      exact ⟨a, b, by rw [Expr.constsResolve_congr hisoRes]; exact cres,
        dd⟩
    · intro cv nP' nM' nm' ni' rules heq r hr
      obtain ⟨a, b, cres, dd⟩ := h6 cv nP' nM' nm' ni' rules heq r hr
      exact ⟨a, b, by rw [Expr.constsResolve_congr hisoRes]; exact cres,
        dd⟩
  -- hoisted: parameter-dependence over the final environment, and
  -- transports from the base model
  have hvp₁ : ConstValParams m₀.val
      (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) := by
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n (.recInfo cvA nP 0 0 0 [])
        (by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0 []).name = n
            from hn)]) ψ₁ ψ₂ (by exact hψ)
    · next hn =>
      refine m₀.val_params n ci ?_ ψ₁ ψ₂ hψ
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 []).name = n
          from hn)]
      exact hf
  have hagreeM : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      m₀.val n ψ = m.val n ψ := by
    intro n hn ψ
    refine hpres₀ n ψ ?_
    intro h
    have h2 : n = cvA.name := h
    rw [h2, hfind'] at hn
    exact nomatch hn
  have htransM : ∀ (e : Expr), e.constsResolve env = true →
      ∀ ψ : Name → Nat,
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ e =
      interpClosed V m.val env ψ e := by
    intro e hres ψ
    rw [interpClosed_mono (cval := m₀.val) hfind' hres]
    exact interp_cval_ext hagreeM e 0 (rho0 V)
  have hAtransM : ∀ (e : Expr), e.constsResolve env = true →
      ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ 0
        (rho0 V) e := by
    intro e hres ψ ha
    refine AnnotOk.mono hfind' e 0 (rho0 V) hres ?_
    exact AnnotOk.cval_ext (fun n hn ψ' => (hagreeM n hn ψ').symm)
      e 0 (rho0 V) ha
  have henv10 : ∀ n,
      ((⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) :=
    fun n => (henv01 n).symm
  refine ⟨⟨m₀.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun ψ => hval₀ ψ, fun n ψ hne => hpres₀ n ψ hne⟩
  · -- wf
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hwf
    · exact hCWtrans c (m₀.wf c (List.mem_cons_of_mem _ hc))
  · -- val_params
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n (.recInfo cvA nP 0 0 0 [])
        (by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0 []).name = n
            from hn)]) ψ₁ ψ₂ (by exact hψ)
    · next hn =>
      refine m₀.val_params n ci ?_ ψ₁ ψ₂ hψ
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 []).name = n
          from hn)]
      exact hf
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type (.recInfo cvA nP 0 0 0 [])
        List.mem_cons_self ψ
      exact ⟨t, by rw [hitrans]; exact ht, hmem⟩
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type c (List.mem_cons_of_mem _ hc) ψ
      exact ⟨t, by rw [hitrans]; exact ht, hmem⟩
  · -- defn_eq
    intro cv2 v2 hmem2 ψ
    rcases List.mem_cons.mp hmem2 with heq | hmem2
    · exact nomatch heq
    · have h := m₀.defn_eq cv2 v2 (List.mem_cons_of_mem _ hmem2) ψ
      rw [hitrans]
      exact h
  · -- annot_ok
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok (.recInfo cvA nP 0 0 0 [])
        List.mem_cons_self ψ
      exact ⟨hAtrans01 _ ψ 0 (rho0 V) hA1,
        fun cv2 v2 heq => nomatch heq⟩
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok c (List.mem_cons_of_mem _ hc) ψ
      exact ⟨hAtrans01 _ ψ 0 (rho0 V) hA1,
        fun cv2 v2 heq => hAtrans01 _ ψ 0 (rho0 V) (hA2 cv2 v2 heq)⟩
  · -- ind_ok
    have hneName : ∀ x : Name, reservedBasisNames.contains x = true →
        x ≠ cvA.name := by
      intro x hx h
      rw [h] at hx
      rw [hx] at hnres
      exact nomatch hnres
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := m₀.ind_ok
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, i7⟩
    · intro cv caps hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i1 cv caps hfp
    · intro cv nP' nF' hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i2 cv nP' nF' hfp
    · intro cv caps hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i3 cv caps hfp
    · -- decl_ok
      intro n ci hfp hbasis hres2
      by_cases hn : cvA.name = n
      · exfalso
        subst hn
        rw [hnres] at hres2
        exact nomatch hres2
      · have hfp₀ : (⟨.recInfo cvA nP 0 0 0 [] ::
            env.consts⟩ : Env).find? n = some ci := by
          rw [← hfindEq n (fun h => hn h.symm)]
          exact hfp
        exact i4 n ci hfp₀ hbasis hres2
    · -- BasisBlocks
      obtain ⟨b1, b2, b3, b4⟩ := i5
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b1 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2, f3⟩ := b2 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f3⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b3 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b4 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
    · -- RecCtorsStored
      intro n cv nP' nM' nm' ni' rules hfp r hr
      by_cases hn : cvA.name = n
      · subst hn
        rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = cvA.name from rfl)] at hfp
        obtain heq := Option.some.inj hfp
        injection heq with e1 e2 e3 e4 e5 e6
        subst e6
        obtain rfl : rule = r := by
          rcases List.mem_cons.mp hr with h | h
          · exact h.symm
          · cases h
        refine ⟨cvj, nP, nF, ?_⟩
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = RecRule.ctor rule from ?_)]
        · exact hctor
        · intro h
          have h2 := find?_none_ne hfind' _ (find?_mem hctor)
          have h3 : (ConstantInfo.ctorInfo cvj nP nF).name =
              RecRule.ctor rule := by
            have h4 := List.find?_some hctor
            simpa using h4
          exact h2 (by rw [h3, ← h]; rfl)
      · have hfp₀ : (⟨.recInfo cvA nP 0 0 0 [] ::
            env.consts⟩ : Env).find? n =
            some (.recInfo cv nP' nM' nm' ni' rules) := by
          rw [← hfindEq n (fun h => hn h.symm)]
          exact hfp
        obtain ⟨cvj, cnP', cnF', hc⟩ := i6 n cv nP' nM' nm' ni' rules
          hfp₀ r hr
        refine ⟨cvj, cnP', cnF', ?_⟩
        have hnc : RecRule.ctor r ≠ cvA.name := by
          intro h
          rw [Env.find?_cons,
            if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
              []).name = RecRule.ctor r from h.symm)] at hc
          exact nomatch (Option.some.inj hc)
        rw [hfindEq _ hnc]
        exact hc
  · -- rec_rules
    intro n cvR nP' nM' nm' ni' rules hfp r hr
    rw [Env.find?_cons] at hfp
    split at hfp
    · next hn =>
      obtain rfl : cvA.name = n := hn
      obtain hceq := Option.some.inj hfp
      injection hceq with e1 e2 e3 e4 e5 e6
      subst e1 e2 e3 e4 e5 e6
      obtain rfl : rule = r := by
        rcases List.mem_cons.mp hr with h | h
        · exact h.symm
        · cases h
      have hncc : RecRule.ctor rule ≠ cvA.name := by
        intro h
        have h2 := find?_none_ne hfind' _ (find?_mem hctor)
        have h3 : (ConstantInfo.ctorInfo cvj nP nF).name =
            RecRule.ctor rule := by
          have h4 := List.find?_some hctor
          simpa using h4
        exact h2 (by rw [h3, h])
      have hArhs₁ : ∀ ψ : Name → Nat,
          AnnotOk V m₀.val
            (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ 0
            (rho0 V) (RecRule.rhs rule) := by
        intro ψ
        exact hAtransM _ hrhsres ψ
          (annotate_sound m raw hann (WScoped.of_not_hasFvar hrawf)
            hrawb (Expr.LeavesBounded.of_not_hasFvar hrawf) (rho0 V)
            (FvarsOk.of_not_hasFvar hrawf))
      refine ⟨hArhs₁, ?_⟩
      intro cvj' cnP' cnF' hfj ψ ψj args margs tv hl hml hch hmch htv
        hpeq hlev hfit
      have hctor₁ : (⟨.recInfo cvA nP 0 0 0 [rule] ::
          env.consts⟩ : Env).find? (RecRule.ctor rule) =
          some (.ctorInfo cvj nP nF) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = RecRule.ctor rule from fun h => hncc h.symm)]
        exact hctor
      rw [hctor₁] at hfj
      obtain hje := Option.some.inj hfj
      injection hje with j1 j2 j3
      subst j1 j2 j3
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2, hidx⟩ := hfit
      subst hψeq hψjeq
      have hro₁ : RenameOk m₀.val
          (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) f := by
        refine ⟨?_, ?_, ?_⟩
        · intro n₂ ci₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · next hh =>
            obtain rfl := Option.some.inj hf₂
            refine ⟨.defnInfo cvm mval, ?_, ?_⟩
            · rw [show f n₂ = mnameP from by
                rw [← (show cvA.name = n₂ from hh)]
                exact hfself]
              rw [Env.find?_cons,
                if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
                  [rule]).name = mnameP from
                  fun h => hfnot cvA.name (hfself.trans h.symm))]
              exact hmodel
            · show cvm.levelParams = _
              rw [hlps]
              exact (show cvA.levelParams =
                (ConstantInfo.recInfo cvA nP 0 0 0
                  [rule]).toConstantVal.levelParams from rfl)
          · next hh =>
            obtain ⟨ci₃, hf₃, hlp₃⟩ := hro.1 n₂ ci₂ hf₂
            refine ⟨ci₃, ?_, hlp₃⟩
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
                [rule]).name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hf₃
        · intro n₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · exact nomatch hf₂
          · next hh =>
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
                [rule]).name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hro.2.1 n₂ hf₂
        · intro n₂ ψ₂
          by_cases hh : n₂ = cvA.name
          · subst hh
            rw [show f cvA.name = mnameP from hfself]
            rw [hpres₀ _ ψ₂
              (fun h => hfnot cvA.name (hfself.trans h))]
            exact (hval₀ ψ₂).symm
          · by_cases hh₂ : f n₂ = cvA.name
            · exact absurd hh₂ (hfnot n₂)
            · rw [hpres₀ _ ψ₂ hh₂, hpres₀ _ ψ₂ hh, hff₀ n₂ hh,
                hro.2.2 n₂]
      have hfRm₁ : (⟨.recInfo cvA nP 0 0 0 [rule] ::
          env.consts⟩ : Env).find? (f cvA.name) =
          some (.defnInfo cvm mval) := by
        rw [hfself, Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = mnameP from
            fun h => hfnot cvA.name (hfself.trans h.symm))]
        exact hmodel
      have heqne : eqName ≠ cvA.name := by
        intro h
        rw [← h] at hnres
        exact absurd hnres (by decide)
      have heqfind₁ : (⟨.recInfo cvA nP 0 0 0 [rule] ::
          env.consts⟩ : Env).find? eqName = some eqA := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = eqName from fun h => heqne h.symm)]
        exact heqfind
      have heqval₁ : ∀ ψ'' : Name → Nat, m₀.val eqName ψ'' = eqVal V ψ'' :=
        fun ψ'' => by
          rw [hagreeM eqName (by rw [heqfind]; rfl) ψ'', heqval ψ'']
      obtain ⟨hthw, -, hthres, -, -, -⟩ := m.wf _ (find?_mem hthm)
      have hthmne : thmName ≠ cvA.name := by
        intro h
        have h2 := find?_none_ne hfind' _ (find?_mem hthm)
        have h3 : (ConstantInfo.thmInfo cvt tval).name = thmName := by
          have h4 := List.find?_some hthm
          simpa using h4
        exact h2 (by rw [h3, h])
      have hthm_mem₁ : ∀ ψ'' : Name → Nat, ∃ P,
          interpClosed V m₀.val
            (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ''
            cvt.type = some P ∧
          m₀.val thmName ψ'' ∈ˢ P := by
        intro ψ''
        obtain ⟨P, hP, hmem⟩ := m.mem_type _ (find?_mem hthm) ψ''
        have h3 : (ConstantInfo.thmInfo cvt tval).name = thmName := by
          simpa using List.find?_some hthm
        refine ⟨P, ?_, ?_⟩
        · rw [htransM cvt.type hthres ψ'']
          exact hP
        · rw [← h3, hagreeM _ (by rw [h3, hthm]; rfl) ψ'']
          exact hmem
      have hthm_annot₁ : ∀ ψ'' : Name → Nat,
          AnnotOk V m₀.val
            (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ'' 0
            (rho0 V) cvt.type := by
        intro ψ''
        obtain ⟨hA1, -⟩ := m.annot_ok _ (find?_mem hthm) ψ''
        exact hAtransM cvt.type hthres ψ'' hA1
      obtain ⟨hCtf, hCtp, -, -, -, -⟩ := m.wf _ (find?_mem hctor)
      have htyw₁ : cvA.type.hasFvar = false := hwf.1
      have hClps₁ : ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ p ∈ cvj.levelParams, ψ₁ p = ψ₂ p) →
          m₀.val (RecRule.ctor rule) ψ₁ = m₀.val (RecRule.ctor rule) ψ₂ :=
        fun ψ₁ ψ₂ hψ => hvp₁ _ _ hctor₁ ψ₁ ψ₂ (by exact hψ)
      have hl' : args.length = nP := by simpa using hl
      have hml' : margs.length = nP + nF := by simpa using hml
      have hout := proj_rule_fold (P := cvA.name) (i := i)
        hro₁ hvp₁ hi hctor₁ hfRm₁
        (show (ConstantInfo.defnInfo cvm
          mval).toConstantVal.levelParams = cvA.levelParams from hlps)
        hClps₁ heqfind₁ heqval₁ hthm_mem₁ hthm_annot₁ hthw hstripR
        hrbody hC_strip hS_strip hsdoms hdoms hsbody hrhsf
        hrhsb hArhs₁ hCtf
        (show cvj.type.allLevelParamsDefined cvj.levelParams = true from
          hCtp)
        hl' hml' htv hpeq hlev hfit2
      obtain ⟨Rv, hRi, hfoldEq, hslots⟩ := hout
      exact ⟨Rv, hRi, by simpa using hfoldEq, by simpa using hslots⟩
    · next hn =>
      have hfp₀ : (⟨.recInfo cvA nP 0 0 0 [] ::
          env.consts⟩ : Env).find? n =
          some (.recInfo cvR nP' nM' nm' ni' rules) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
            []).name = n from hn)]
        exact hfp
      obtain ⟨hA, hfold⟩ := m₀.rec_rules n cvR nP' nM' nm' ni' rules
        hfp₀ r hr
      refine ⟨fun ψ => hAtrans01 _ ψ 0 (rho0 V) (hA ψ), ?_⟩
      intro cvj' cnP' cnF' hfj ψ ψj args margs tv hl hml hch hmch htv
        hpeq hlev hfit
      have hncc : RecRule.ctor r ≠ cvA.name := by
        intro h
        rw [h, Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = cvA.name from rfl)] at hfj
        exact nomatch (Option.some.inj hfj)
      have hfj₀ : (⟨.recInfo cvA nP 0 0 0 [] ::
          env.consts⟩ : Env).find? (RecRule.ctor r) =
          some (.ctorInfo cvj' cnP' cnF') := by
        rw [← hfindEq _ hncc]
        exact hfj
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2, hidx⟩ := hfit
      obtain ⟨R', hRi, hfoldEq, hRch⟩ := hfold cvj' cnP' cnF' hfj₀ ψ ψj
        args margs tv hl hml hch hmch htv hpeq hlev
        ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
          hψeq, hψjeq, TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit1,
          TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit2, by
            rw [← mapM_interp_congr (fun e => interp_env_ext henv10
              natLitSupported_cons_recRules e dd₂ ρρ₂)]
            exact hidx⟩
      refine ⟨R', ?_, hfoldEq, hRch⟩
      rw [hitrans]
      exact hRi
  · -- modeled_ok: lookups only differ in the head's rule list
    obtain ⟨mo1, mo2, mo3, mo4, mo5⟩ := m₀.modeled_ok
    have hisoF : ∀ n,
        (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env).find? n =
        if cvA.name = n then some (.recInfo cvA nP 0 0 0 [rule])
        else (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env).find? n := by
      intro n
      rw [Env.find?_cons]
      by_cases h : cvA.name = n
      · rw [if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0 [rule]).name = n from h), if_pos h]
      · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 [rule]).name = n from h), if_neg h,
          Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 []).name = n from h)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n cv caps hf hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨hms, hveq⟩ := mo1 n cv caps hf hres
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
    · intro n cv cnP' cnF' hf hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨hms, hveq⟩ := mo2 n cv cnP' cnF' hf hres
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
    · intro T j ci hf
      rw [hisoF] at hf
      split at hf
      · next hh =>
        obtain ⟨hms, hveq⟩ := mo3 T j (.recInfo cvA nP 0 0 0 [])
          (by rw [Env.find?_cons,
            if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0 []).name = projFnName T j from hh)])
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
      · obtain ⟨hms, hveq⟩ := mo3 T j ci hf
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
    · intro T cvT caps hf hcape hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨hmsC, hmsP, hlaw⟩ := mo4 T cvT caps hf hcape hres
        refine ⟨?_, ?_, ?_⟩
        · rw [hisoF]
          split
          · rfl
          · exact hmsC
        · intro j hj
          rw [hisoF]
          split
          · rfl
          · exact hmsP j hj
        · intro φ'' us ps x dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hfit
          exact hlaw φ'' us ps x dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx
            (TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit)
    · intro T cvT caps hf hcapu hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · have hlaw := mo5 T cvT caps hf hcapu hres
        intro φ'' us ps x y dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hy hfit
        exact hlaw φ'' us ps x y dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hy
          (TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit)
  · -- nat_ops: lookups only differ in the head's rule list
    exact NatOpsOk.cons_recRules m₀.nat_ops

/-- Invert a successful `checkIndMember` run. -/
theorem checkIndMember_inv {blockNames : List Name} {caps : IndCaps}
    {env' env₁ : Env} {ci : ConstantInfo}
    (h : checkIndMember (fueledOps F) blockNames caps env' ci = .ok env₁) :
    ∃ cvA cvm mval,
      checkConstantVal (fueledOps F) env' ci.toConstantVal = .ok cvA ∧
      cvA.name.isModelSuffix = false ∧
      env'.find? (cvA.name.str "_model") = some (.defnInfo cvm mval) ∧
      cvm.levelParams = cvA.levelParams ∧
      cvA.type.renameConsts (fun n =>
        if blockNames.contains n then n.str "_model" else n) = cvm.type ∧
      ((∃ cv caps', ci = .indInfo cv caps') ∧
         env₁ = ⟨.indInfo cvA caps :: env'.consts⟩ ∨
       (∃ cv nP nF, ci = .ctorInfo cv nP nF ∧
         env₁ = ⟨.ctorInfo cvA nP nF :: env'.consts⟩) ∨
       (∃ cv nP nm ni rules rules', ci = .recInfo cv nP 1 nm ni rules ∧
         blockNames.all (fun n =>
           n == cvA.name || (env'.find? n).isSome) = true ∧
         env'.find? eqName = some eqA ∧
         checkIotaRules (fueledOps F) env'
           ⟨.recInfo cvA nP 1 nm ni [] :: env'.consts⟩
           (fun n => if blockNames.contains n then n.str "_model" else n)
           cvA.name cvA.levelParams cvA.type nP 1 nm ni 0 rules =
           .ok rules' ∧
         env₁ = ⟨.recInfo cvA nP 1 nm ni rules' :: env'.consts⟩)) := by
  simp only [checkIndMember, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps F) env' ci.toConstantVal with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cvA =>
  rw [hccv] at h
  try dsimp only at h
  by_cases hms : cvA.name.isModelSuffix = true
  case pos => rw [if_pos hms] at h; exact nomatch h
  rw [if_neg hms] at h
  have hmsF : cvA.name.isModelSuffix = false := by
    revert hms; cases cvA.name.isModelSuffix <;> simp
  try dsimp only at h
  revert h
  match hfm : env'.find? (cvA.name.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvm mval) => ?_
  intro h
  dsimp only at h
  by_cases hlps : cvm.levelParams = cvA.levelParams
  case neg => rw [if_neg hlps] at h; exact nomatch h
  rw [if_pos hlps] at h
  try dsimp only at h
  by_cases hren : (cvA.type.renameConsts (fun n =>
      if blockNames.contains n then n.str "_model" else n) ==
      cvm.type) = true
  case neg => rw [if_neg hren] at h; exact nomatch h
  rw [if_pos hren] at h
  try dsimp only at h
  refine ⟨cvA, cvm, mval, rfl, hmsF, hfm, hlps, eq_of_beq hren, ?_⟩
  cases ci with
  | axiomInfo cv => exact nomatch h
  | defnInfo cv value => exact nomatch h
  | thmInfo cv value => exact nomatch h
  | indInfo cv caps' =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨⟨cv, caps', rfl⟩, h.symm⟩
  | ctorInfo cv nP nF =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inr (Or.inl ⟨cv, nP, nF, rfl, h.symm⟩)
  | recInfo cv nP nM nm ni rules =>
    refine Or.inr (Or.inr ?_)
    simp only [Bind.bind, Except.bind] at h
    by_cases hnM : nM = 1
    case neg => rw [if_neg hnM] at h; exact nomatch h
    rw [if_pos hnM] at h
    subst hnM
    try dsimp only at h
    by_cases hall : (blockNames.all fun n =>
        n == cvA.name || (env'.find? n).isSome) = true
    case neg => rw [if_neg hall] at h; exact nomatch h
    rw [if_pos hall] at h
    try dsimp only at h
    by_cases heqf : env'.find? eqName = some eqA
    case neg => rw [if_neg heqf] at h; exact nomatch h
    rw [if_pos heqf] at h
    try dsimp only at h
    try dsimp only at h
    cases hcir : checkIotaRules (fueledOps F) env'
        ⟨.recInfo cvA nP 1 nm ni [] :: env'.consts⟩
        (fun n => if blockNames.contains n then n.str "_model" else n)
        cvA.name cvA.levelParams cvA.type nP 1 nm ni 0 rules with
    | error e => rw [hcir] at h; exact nomatch h
    | ok rules' =>
    rw [hcir] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨cv, nP, nm, ni, rules, rules', rfl, hall, heqf, hcir, h.symm⟩

/-- Extend a model by an opaque modeled *recursor*: its value is its
`_model`'s, and every rule's fold obligation is discharged by the
checked `iota` theorem (`modeled_rule_fold`).  Two-phase: the rule
right-hand sides were annotated against the provisional rules-free
recursor, whose model exists trivially; the final environment differs
only in the attached rule list, which the interpretation never
reads. -/
theorem extend_modeled_rec {env : Env} (m : EnvModel V env)
    (cvA : ConstantVal) (nP nm ni : Nat) (rules' : List RecRule)
    (f : Name → Name) {cvm : ConstantVal} {mval : Expr}
    (hfind' : env.find? cvA.name = none)
    (hnres : reservedBasisNames.contains cvA.name = false)
    (hpshape : cvA.name.isProjFnShape = false)
    (hwf : ConstWF ⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩
      (.recInfo cvA nP 1 nm ni rules'))
    (htyres0 : cvA.type.constsResolve env = true)
    (hmodel : env.find? (cvA.name.str "_model") = some (.defnInfo cvm mval))
    (hlps : cvm.levelParams = cvA.levelParams)
    (hren : cvA.type.renameConsts f = cvm.type)
    (f₀ : Name → Name) (hro : RenameOk m.val env f₀)
    (hff₀ : ∀ n, n ≠ cvA.name → f n = f₀ n)
    (hfself : f cvA.name = cvA.name.str "_model")
    (hfnot : ∀ n, f n ≠ cvA.name)
    (heqfind : env.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m.val eqName ψ'' = eqVal V ψ'')
    (hrules : ∀ r ∈ rules', RuleChecked F env
      ⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ f cvA nP nm ni r) :
    ∃ m' : EnvModel V ⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩,
      (∀ ψ, m'.val cvA.name ψ = m.val (cvA.name.str "_model") ψ) ∧
      (∀ n ψ, n ≠ cvA.name → m'.val n ψ = m.val n ψ) := by
  -- phase 0: install the rules-free provisional recursor
  have hisoRes : ∀ n,
      ((⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env).find? n).isSome
      =
      ((⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env).find? n).isSome := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : cvA.name = n
    · rw [if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
          rules').name = n from h),
        if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
          []).name = n from h)]
      rfl
    · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
          rules').name = n from h),
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
          []).name = n from h)]
  have hwf₀ : ConstWF (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env)
      (.recInfo cvA nP 1 nm ni []) := by
    obtain ⟨h1, h2, h3, h4, -, -⟩ := hwf
    refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
    · rw [← Expr.constsResolve_congr hisoRes]
      exact h3
    · intro cv2 v2 heq
      exact nomatch heq
    · intro cv nP' nM' nm' ni' rules heq
      injection heq with e1 e2 e3 e4 e5 e6
      subst e6
      intro r hr
      cases hr
  have hren₀ : cvA.type.renameConsts f₀ = cvm.type := by
    rw [← Expr.renameConsts_congr_resolve
      (fun n hn => hff₀ n (fun he => by
        rw [he, hfind'] at hn; exact nomatch hn))
      cvA.type htyres0]
    exact hren
  obtain ⟨m₀, hval₀, hpres₀⟩ := extend_modeled_one m
    (.recInfo cvA nP 1 nm ni []) f₀ (cvA.name.str "_model")
    hfind' hnres hwf₀ htyres0
    (Or.inr (Or.inr ⟨cvA, nP, 1, nm, ni, rfl⟩)) hmodel hlps hren₀ hro
    (fun hk => by
      rcases hk with ⟨_, _, hcon⟩ | ⟨_, _, _, hcon⟩ <;> exact nomatch hcon)
    (fun T j hh => by
      have hh' : cvA.name = projFnName T j := hh
      rw [hh'] at hpshape
      exact nomatch hpshape)
    (fun cv caps hcon => nomatch hcon)
    (fun cv caps hcon => nomatch hcon)
  have henv01 : ∀ n,
      ((⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : cvA.name = n
    · rw [if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
          []).name = n from h),
        if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
          rules').name = n from h)]
      rfl
    · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
          []).name = n from h),
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
          rules').name = n from h)]
  -- shared transports between the provisional and final environments
  have hfindEq : ∀ n, n ≠ cvA.name →
      (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env).find? n =
      (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env).find? n := by
    intro n hn
    rw [Env.find?_cons, Env.find?_cons,
      if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni rules').name = n
        from fun h => hn h.symm),
      if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni []).name = n
        from fun h => hn h.symm)]
  have hitrans : ∀ (e : Expr) (ψ : Name → Nat),
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ e =
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env) ψ e := by
    intro e ψ
    exact (interp_env_ext henv01 natLitSupported_cons_recRules e 0 (rho0 V)).symm
  have hAtrans01 : ∀ (e : Expr) (ψ : Name → Nat) (d : Nat) (ρ : Nat → V),
      AnnotOk V m₀.val (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env)
        ψ d ρ e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ d ρ e :=
    fun e ψ d ρ h => AnnotOk.env_ext henv01 natLitSupported_cons_recRules e d ρ h
  have hCWtrans : ∀ c,
      ConstWF (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env) c →
      ConstWF (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) c := by
    intro c hc
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
    refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
    · rw [Expr.constsResolve_congr hisoRes]
      exact h3
    · intro cv2 v2 heq
      obtain ⟨a, b, cres, dd⟩ := h5 cv2 v2 heq
      exact ⟨a, b, by rw [Expr.constsResolve_congr hisoRes]; exact cres,
        dd⟩
    · intro cv nP' nM' nm' ni' rules heq r hr
      obtain ⟨a, b, cres, dd⟩ := h6 cv nP' nM' nm' ni' rules heq r hr
      exact ⟨a, b, by rw [Expr.constsResolve_congr hisoRes]; exact cres,
        dd⟩
  -- hoisted: parameter-dependence over the final environment, and
  -- transports from the base model
  have hvp₁ : ConstValParams m₀.val
      (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) := by
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n (.recInfo cvA nP 1 nm ni [])
        (by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni []).name = n
            from hn)]) ψ₁ ψ₂ (by exact hψ)
    · next hn =>
      refine m₀.val_params n ci ?_ ψ₁ ψ₂ hψ
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni []).name = n
          from hn)]
      exact hf
  have hagreeM : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      m₀.val n ψ = m.val n ψ := by
    intro n hn ψ
    refine hpres₀ n ψ ?_
    intro h
    have h2 : n = cvA.name := h
    rw [h2, hfind'] at hn
    exact nomatch hn
  have htransM : ∀ (e : Expr), e.constsResolve env = true →
      ∀ ψ : Name → Nat,
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ e =
      interpClosed V m.val env ψ e := by
    intro e hres ψ
    rw [interpClosed_mono (cval := m₀.val) hfind' hres]
    exact interp_cval_ext hagreeM e 0 (rho0 V)
  have hAtransM : ∀ (e : Expr), e.constsResolve env = true →
      ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ 0
        (rho0 V) e := by
    intro e hres ψ ha
    refine AnnotOk.mono hfind' e 0 (rho0 V) hres ?_
    exact AnnotOk.cval_ext (fun n hn ψ' => (hagreeM n hn ψ').symm)
      e 0 (rho0 V) ha
  have henv10 : ∀ n,
      ((⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) :=
    fun n => (henv01 n).symm
  refine ⟨⟨m₀.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun ψ => hval₀ ψ, fun n ψ hne => hpres₀ n ψ hne⟩
  · -- wf
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hwf
    · exact hCWtrans c (m₀.wf c (List.mem_cons_of_mem _ hc))
  · -- val_params
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n (.recInfo cvA nP 1 nm ni [])
        (by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni []).name = n
            from hn)]) ψ₁ ψ₂ (by exact hψ)
    · next hn =>
      refine m₀.val_params n ci ?_ ψ₁ ψ₂ hψ
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni []).name = n
          from hn)]
      exact hf
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type (.recInfo cvA nP 1 nm ni [])
        List.mem_cons_self ψ
      exact ⟨t, by rw [hitrans]; exact ht, hmem⟩
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type c (List.mem_cons_of_mem _ hc) ψ
      exact ⟨t, by rw [hitrans]; exact ht, hmem⟩
  · -- defn_eq
    intro cv2 v2 hmem2 ψ
    rcases List.mem_cons.mp hmem2 with heq | hmem2
    · exact nomatch heq
    · have h := m₀.defn_eq cv2 v2 (List.mem_cons_of_mem _ hmem2) ψ
      rw [hitrans]
      exact h
  · -- annot_ok
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok (.recInfo cvA nP 1 nm ni [])
        List.mem_cons_self ψ
      exact ⟨hAtrans01 _ ψ 0 (rho0 V) hA1,
        fun cv2 v2 heq => nomatch heq⟩
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok c (List.mem_cons_of_mem _ hc) ψ
      exact ⟨hAtrans01 _ ψ 0 (rho0 V) hA1,
        fun cv2 v2 heq => hAtrans01 _ ψ 0 (rho0 V) (hA2 cv2 v2 heq)⟩
  · -- ind_ok
    have hneName : ∀ x : Name, reservedBasisNames.contains x = true →
        x ≠ cvA.name := by
      intro x hx h
      rw [h] at hx
      rw [hx] at hnres
      exact nomatch hnres
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := m₀.ind_ok
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, i7⟩
    · intro cv caps hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i1 cv caps hfp
    · intro cv nP' nF' hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i2 cv nP' nF' hfp
    · intro cv caps hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i3 cv caps hfp
    · -- decl_ok
      intro n ci hfp hbasis hres2
      by_cases hn : cvA.name = n
      · exfalso
        subst hn
        rw [hnres] at hres2
        exact nomatch hres2
      · have hfp₀ : (⟨.recInfo cvA nP 1 nm ni [] ::
            env.consts⟩ : Env).find? n = some ci := by
          rw [← hfindEq n (fun h => hn h.symm)]
          exact hfp
        exact i4 n ci hfp₀ hbasis hres2
    · -- BasisBlocks
      obtain ⟨b1, b2, b3, b4⟩ := i5
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b1 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2, f3⟩ := b2 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f3⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b3 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b4 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
    · -- RecCtorsStored
      intro n cv nP' nM' nm' ni' rules hfp r hr
      by_cases hn : cvA.name = n
      · subst hn
        rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = cvA.name from rfl)] at hfp
        obtain heq := Option.some.inj hfp
        injection heq with e1 e2 e3 e4 e5 e6
        subst e6
        obtain ⟨cvj, cnF, _, _, _, _, _, _, _, _, _, _, _, _, _, hctor,
          hnf, -⟩ := hrules r hr
        refine ⟨cvj, nP, cnF, ?_⟩
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = RecRule.ctor r from ?_)]
        · exact hctor
        · intro h
          have h2 := find?_none_ne hfind' _ (find?_mem hctor)
          have h3 : (ConstantInfo.ctorInfo cvj nP cnF).name =
              RecRule.ctor r := by
            have h4 := List.find?_some hctor
            simpa using h4
          exact h2 (by rw [h3, ← h]; rfl)
      · have hfp₀ : (⟨.recInfo cvA nP 1 nm ni [] ::
            env.consts⟩ : Env).find? n =
            some (.recInfo cv nP' nM' nm' ni' rules) := by
          rw [← hfindEq n (fun h => hn h.symm)]
          exact hfp
        obtain ⟨cvj, cnP', cnF', hc⟩ := i6 n cv nP' nM' nm' ni' rules
          hfp₀ r hr
        refine ⟨cvj, cnP', cnF', ?_⟩
        have hnc : RecRule.ctor r ≠ cvA.name := by
          intro h
          rw [Env.find?_cons,
            if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
              []).name = RecRule.ctor r from h.symm)] at hc
          exact nomatch (Option.some.inj hc)
        rw [hfindEq _ hnc]
        exact hc
  · -- rec_rules
    intro n cvR nP' nM' nm' ni' rules hfp r hr
    rw [Env.find?_cons] at hfp
    split at hfp
    · next hn =>
      obtain rfl : cvA.name = n := hn
      obtain hceq := Option.some.inj hfp
      injection hceq with e1 e2 e3 e4 e5 e6
      subst e1 e2 e3 e4 e5 e6
      obtain ⟨cvj, cnF, raw, rbinders, tbinders, cbinders, sbinders,
        rbody, tybody, cbody, sbody, thmName, cvt, tval, ℓA,
        hctor, hnf, hann, hrawf, hrawb, hrhsf, hrhsb, hstripR,
        hR_strip, hC_strip, hclen, hS_strip, hdomsPre, hdomsF, hsdoms,
        hsbody, hthm, hlpt, -, -⟩ := hrules r hr
      have hncc : RecRule.ctor r ≠ cvA.name := by
        intro h
        have h2 := find?_none_ne hfind' _ (find?_mem hctor)
        have h3 : (ConstantInfo.ctorInfo cvj nP cnF).name =
            RecRule.ctor r := by
          have h4 := List.find?_some hctor
          simpa using h4
        exact h2 (by rw [h3, h])
      have hArhs₁ : ∀ ψ : Name → Nat,
          AnnotOk V m₀.val
            (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ 0
            (rho0 V) (RecRule.rhs r) := by
        intro ψ
        refine hAtrans01 _ ψ 0 (rho0 V) ?_
        exact annotate_sound m₀ raw hann (WScoped.of_not_hasFvar hrawf)
          hrawb (Expr.LeavesBounded.of_not_hasFvar hrawf) (rho0 V)
          (FvarsOk.of_not_hasFvar hrawf)
      refine ⟨hArhs₁, ?_⟩
      intro cvj' cnP' cnF' hfj ψ ψj args margs tv hl hml hch hmch htv
        hpeq hlev hfit
      have hctor₁ : (⟨.recInfo cvA nP 1 nm ni rules' ::
          env.consts⟩ : Env).find? (RecRule.ctor r) =
          some (.ctorInfo cvj nP cnF) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = RecRule.ctor r from fun h => hncc h.symm)]
        exact hctor
      rw [hctor₁] at hfj
      obtain hje := Option.some.inj hfj
      injection hje with j1 j2 j3
      subst j1 j2 j3
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2, hidx⟩ := hfit
      subst hψeq hψjeq
      have hro₁ : RenameOk m₀.val
          (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) f := by
        refine ⟨?_, ?_, ?_⟩
        · intro n₂ ci₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · next hh =>
            obtain rfl := Option.some.inj hf₂
            refine ⟨.defnInfo cvm mval, ?_, ?_⟩
            · rw [show f n₂ = cvA.name.str "_model" from by
                rw [← (show cvA.name = n₂ from hh)]
                exact hfself]
              rw [Env.find?_cons,
                if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
                  rules').name = cvA.name.str "_model" from
                  fun h => Name.str_ne cvA.name "_model" h.symm)]
              exact hmodel
            · show cvm.levelParams = _
              rw [hlps]
              exact (show cvA.levelParams =
                (ConstantInfo.recInfo cvA nP 1 nm ni
                  rules').toConstantVal.levelParams from rfl)
          · next hh =>
            obtain ⟨ci₃, hf₃, hlp₃⟩ := hro.1 n₂ ci₂ hf₂
            refine ⟨ci₃, ?_, hlp₃⟩
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
                rules').name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hf₃
        · intro n₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · exact nomatch hf₂
          · next hh =>
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
                rules').name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hro.2.1 n₂ hf₂
        · intro n₂ ψ₂
          by_cases hh : n₂ = cvA.name
          · subst hh
            rw [show f cvA.name = cvA.name.str "_model" from hfself]
            rw [hpres₀ _ ψ₂ (Name.str_ne cvA.name "_model")]
            exact (hval₀ ψ₂).symm
          · by_cases hh₂ : f n₂ = cvA.name
            · exact absurd hh₂ (hfnot n₂)
            · rw [hpres₀ _ ψ₂ hh₂, hpres₀ _ ψ₂ hh, hff₀ n₂ hh,
                hro.2.2 n₂]
      have hfRm₁ : (⟨.recInfo cvA nP 1 nm ni rules' ::
          env.consts⟩ : Env).find? (f cvA.name) =
          some (.defnInfo cvm mval) := by
        rw [hfself, Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = cvA.name.str "_model" from
            fun h => Name.str_ne cvA.name "_model" h.symm)]
        exact hmodel
      have heqne : eqName ≠ cvA.name := by
        intro h
        rw [← h] at hnres
        exact absurd hnres (by decide)
      have heqfind₁ : (⟨.recInfo cvA nP 1 nm ni rules' ::
          env.consts⟩ : Env).find? eqName = some eqA := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = eqName from fun h => heqne h.symm)]
        exact heqfind
      have heqval₁ : ∀ ψ'' : Name → Nat, m₀.val eqName ψ'' = eqVal V ψ'' :=
        fun ψ'' => by
          rw [hagreeM eqName (by rw [heqfind]; rfl) ψ'', heqval ψ'']
      obtain ⟨hthw, -, hthres, -, -, -⟩ := m.wf _ (find?_mem hthm)
      have hthmne : thmName ≠ cvA.name := by
        intro h
        have h2 := find?_none_ne hfind' _ (find?_mem hthm)
        have h3 : (ConstantInfo.thmInfo cvt tval).name = thmName := by
          have h4 := List.find?_some hthm
          simpa using h4
        exact h2 (by rw [h3, h])
      have hthm_mem₁ : ∀ ψ'' : Name → Nat, ∃ P,
          interpClosed V m₀.val
            (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ''
            cvt.type = some P ∧
          m₀.val thmName ψ'' ∈ˢ P := by
        intro ψ''
        obtain ⟨P, hP, hmem⟩ := m.mem_type _ (find?_mem hthm) ψ''
        have h3 : (ConstantInfo.thmInfo cvt tval).name = thmName := by
          simpa using List.find?_some hthm
        refine ⟨P, ?_, ?_⟩
        · rw [htransM cvt.type hthres ψ'']
          exact hP
        · rw [← h3, hagreeM _ (by rw [h3, hthm]; rfl) ψ'']
          exact hmem
      have hthm_annot₁ : ∀ ψ'' : Name → Nat,
          AnnotOk V m₀.val
            (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ'' 0
            (rho0 V) cvt.type := by
        intro ψ''
        obtain ⟨hA1, -⟩ := m.annot_ok _ (find?_mem hthm) ψ''
        exact hAtransM cvt.type hthres ψ'' hA1
      obtain ⟨hCtf, hCtp, -, hCtb, -, -⟩ := m.wf _ (find?_mem hctor)
      have htyw₁ : cvA.type.hasFvar = false := hwf.1
      have hClps₁ : ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ p ∈ cvj.levelParams, ψ₁ p = ψ₂ p) →
          m₀.val (RecRule.ctor r) ψ₁ = m₀.val (RecRule.ctor r) ψ₂ :=
        fun ψ₁ ψ₂ hψ => hvp₁ _ _ hctor₁ ψ₁ ψ₂ (by exact hψ)
      have hl' : args.length = nP + 1 + nm + ni := by simpa using hl
      exact modeled_rule_fold (ni := ni) hro₁ hvp₁ hctor₁ hfRm₁
        (show (ConstantInfo.defnInfo cvm
          mval).toConstantVal.levelParams = cvA.levelParams from hlps)
        hClps₁ heqfind₁ heqval₁ hthm_mem₁ hthm_annot₁ hthw hstripR
        hR_strip hC_strip hclen hS_strip hdomsPre hdomsF hsdoms hsbody
        hrhsf hrhsb hArhs₁ htyw₁ hCtf hCtb
        (show cvj.type.allLevelParamsDefined cvj.levelParams = true from
          hCtp)
        hl' hml htv hpeq hlev hfit1 hfit2 hidx
    · next hn =>
      have hfp₀ : (⟨.recInfo cvA nP 1 nm ni [] ::
          env.consts⟩ : Env).find? n =
          some (.recInfo cvR nP' nM' nm' ni' rules) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
            []).name = n from hn)]
        exact hfp
      obtain ⟨hA, hfold⟩ := m₀.rec_rules n cvR nP' nM' nm' ni' rules
        hfp₀ r hr
      refine ⟨fun ψ => hAtrans01 _ ψ 0 (rho0 V) (hA ψ), ?_⟩
      intro cvj' cnP' cnF' hfj ψ ψj args margs tv hl hml hch hmch htv
        hpeq hlev hfit
      have hncc : RecRule.ctor r ≠ cvA.name := by
        intro h
        rw [h, Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = cvA.name from rfl)] at hfj
        exact nomatch (Option.some.inj hfj)
      have hfj₀ : (⟨.recInfo cvA nP 1 nm ni [] ::
          env.consts⟩ : Env).find? (RecRule.ctor r) =
          some (.ctorInfo cvj' cnP' cnF') := by
        rw [← hfindEq _ hncc]
        exact hfj
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2, hidx⟩ := hfit
      obtain ⟨R', hRi, hfoldEq, hRch⟩ := hfold cvj' cnP' cnF' hfj₀ ψ ψj
        args margs tv hl hml hch hmch htv hpeq hlev
        ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
          hψeq, hψjeq, TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit1,
          TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit2, by
            rw [← mapM_interp_congr (fun e => interp_env_ext henv10
              natLitSupported_cons_recRules e dd₂ ρρ₂)]
            exact hidx⟩
      refine ⟨R', ?_, hfoldEq, hRch⟩
      rw [hitrans]
      exact hRi
  · -- modeled_ok: lookups only differ in the head's rule list
    obtain ⟨mo1, mo2, mo3, mo4, mo5⟩ := m₀.modeled_ok
    have hisoF : ∀ n,
        (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env).find? n =
        if cvA.name = n then some (.recInfo cvA nP 1 nm ni rules')
        else (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env).find? n := by
      intro n
      rw [Env.find?_cons]
      by_cases h : cvA.name = n
      · rw [if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni rules').name = n from h), if_pos h]
      · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni rules').name = n from h), if_neg h,
          Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni []).name = n from h)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n cv caps hf hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨hms, hveq⟩ := mo1 n cv caps hf hres
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
    · intro n cv cnP' cnF' hf hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨hms, hveq⟩ := mo2 n cv cnP' cnF' hf hres
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
    · intro T j ci hf
      rw [hisoF] at hf
      split at hf
      · next hh =>
        obtain ⟨hms, hveq⟩ := mo3 T j (.recInfo cvA nP 1 nm ni [])
          (by rw [Env.find?_cons,
            if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni []).name = projFnName T j from hh)])
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
      · obtain ⟨hms, hveq⟩ := mo3 T j ci hf
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
    · intro T cvT caps hf hcape hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨hmsC, hmsP, hlaw⟩ := mo4 T cvT caps hf hcape hres
        refine ⟨?_, ?_, ?_⟩
        · rw [hisoF]
          split
          · rfl
          · exact hmsC
        · intro j hj
          rw [hisoF]
          split
          · rfl
          · exact hmsP j hj
        · intro φ'' us ps x dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hfit
          exact hlaw φ'' us ps x dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx
            (TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit)
    · intro T cvT caps hf hcapu hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · have hlaw := mo5 T cvT caps hf hcapu hres
        intro φ'' us ps x y dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hy hfit
        exact hlaw φ'' us ps x y dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hy
          (TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit)
  · -- nat_ops: lookups only differ in the head's rule list
    exact NatOpsOk.cons_recRules m₀.nat_ops

/-- The fold invariant of `checkIndDecl`: every installed block member
has its `_model` companion stored (as a definition with the same level
parameters) and is interpreted by it. -/
def BlockInstalled (blockNames : List Name) (env' : Env)
    (val : ConstVal V) : Prop :=
  ∀ n, blockNames.contains n = true → ∀ ci, env'.find? n = some ci →
    ∃ cvm mval, env'.find? (n.str "_model") = some (.defnInfo cvm mval) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat, val n ψ = val (n.str "_model") ψ

omit [SetTheory V] in
/-- Installing one member with its model's value preserves the fold
invariant. -/
theorem BlockInstalled.step {blockNames : List Name} {env' : Env}
    {val val₁ : ConstVal V} {ci₁ : ConstantInfo} {cvm : ConstantVal}
    {mval : Expr}
    (hI : BlockInstalled blockNames env' val)
    (hms : ci₁.name.isModelSuffix = false)
    (hfm : env'.find? (ci₁.name.str "_model") = some (.defnInfo cvm mval))
    (hlps : cvm.levelParams = ci₁.toConstantVal.levelParams)
    (hval₁ : ∀ ψ, val₁ ci₁.name ψ = val (ci₁.name.str "_model") ψ)
    (hpres₁ : ∀ n ψ, n ≠ ci₁.name → val₁ n ψ = val n ψ) :
    BlockInstalled blockNames ⟨ci₁ :: env'.consts⟩ val₁ := by
  intro n hbn ci₂ hf₂
  rw [Env.find?_cons] at hf₂
  split at hf₂
  · next hh =>
    obtain rfl := Option.some.inj hf₂
    obtain rfl : ci₁.name = n := hh
    refine ⟨cvm, mval, ?_, hlps, ?_⟩
    · rw [Env.find?_cons,
        if_neg (fun h => Name.str_ne ci₁.name "_model" h.symm)]
      exact hfm
    · intro ψ
      rw [hval₁ ψ, hpres₁ _ ψ (Name.str_ne ci₁.name "_model")]
  · next hh =>
    obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hI n hbn ci₂ hf₂
    refine ⟨cvm₂, mval₂, ?_, hlps₂, ?_⟩
    · rw [Env.find?_cons, if_neg (show ¬ci₁.name = n.str "_model" from
        fun h => Name.str_model_ne hms h.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres₁ _ ψ (fun h => hh h.symm),
        hpres₁ _ ψ (fun h => Name.str_model_ne hms h),
        hv₂ ψ]

/-- One `checkIndMember` step preserves having a model together with
the fold invariant. -/
theorem checkIndMember_sound {blockNames : List Name} {caps : IndCaps}
    {env' env₁ : Env} {ci : ConstantInfo}
    (h : checkIndMember (fueledOps F) blockNames caps env' ci = .ok env₁)
    (hpins : ∀ cv caps₂, ci = .indInfo cv caps₂ →
      EtaPins env' cv.name cv.levelParams caps)
    (hbn : blockNames.contains ci.name = true)
    (m : EnvModel V env') (hI : BlockInstalled blockNames env' m.val) :
    ∃ m₁ : EnvModel V env₁, BlockInstalled blockNames env₁ m₁.val := by
  obtain ⟨cvA, cvm, mval, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
    checkIndMember_inv h
  obtain ⟨hfind0, hnres0, hpshape0, hnd, hlb, hfv, tyA, stype, u, hann,
    hlp, hres, hst, hsort, hcvA⟩ := checkConstantVal_inv hccv
  have hnameA : cvA.name = ci.name := by rw [hcvA]; rfl
  have hlpsA : cvA.levelParams = ci.toConstantVal.levelParams := by
    rw [hcvA]
  have htypeA : cvA.type = tyA := by rw [hcvA]
  have hfind' : env'.find? cvA.name = none := by rw [hnameA]; exact hfind0
  have hnres : reservedBasisNames.contains cvA.name = false := by
    rw [hnameA]; exact hnres0
  have hshapeA : cvA.name.isProjFnShape = false := by
    rw [hnameA]; exact hpshape0
  have hprojRef : ∀ (T : Name) (j : Nat), cvA.name = projFnName T j →
      ∀ {p : Prop}, p := by
    intro T j hh
    rw [hh] at hshapeA
    exact nomatch hshapeA
  have hbnA : blockNames.contains cvA.name = true := by
    rw [hnameA]; exact hbn
  have htyf : cvA.type.hasFvar = false := by
    rw [htypeA]
    exact not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F _ hann (WScoped.of_not_hasFvar hfv)).fvarsBelow)
  have htyb : cvA.type.looseBVarsBounded 0 = true := by
    rw [htypeA]
    exact annotateCore_looseBVars F _ hann hlb
  have htlp : cvA.type.allLevelParamsDefined cvA.levelParams = true := by
    rw [htypeA, hlpsA]; exact hlp
  have htres : cvA.type.constsResolve env' = true := by
    rw [htypeA]; exact hres
  -- the block renaming and its semantic pruning
  obtain ⟨fb, hfb⟩ : ∃ fb : Name → Name, fb = fun n =>
      if blockNames.contains n then n.str "_model" else n := ⟨_, rfl⟩
  rw [← hfb] at hrenf hkind
  obtain ⟨fS, hfS⟩ : ∃ fS : Name → Name, fS = fun n =>
      if (env'.find? n).isSome then fb n else n := ⟨_, rfl⟩
  have hfSfound : ∀ n, (env'.find? n).isSome = true → fS n = fb n := by
    intro n hn
    rw [hfS]; simp only [hn, if_true]
  have hfSnone : ∀ n, env'.find? n = none → fS n = n := by
    intro n hn
    rw [hfS]; simp [hn]
  have hroS : RenameOk m.val env' fS := by
    refine ⟨?_, ?_, ?_⟩
    · intro n ci₂ hf₂
      have hsome : (env'.find? n).isSome = true := by rw [hf₂]; rfl
      rw [hfSfound n hsome, hfb]
      dsimp only
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, -⟩ := hI n hc ci₂ hf₂
        exact ⟨.defnInfo cvm₂ mval₂, hfm₂, hlps₂⟩
      · rw [if_neg hc]
        exact ⟨ci₂, hf₂, rfl⟩
    · intro n hf₂
      rw [hfSnone n hf₂]
      exact hf₂
    · intro n ψ
      cases hf₂ : env'.find? n with
      | none => rw [hfSnone n hf₂]
      | some ci₂ =>
        have hsome : (env'.find? n).isSome = true := by rw [hf₂]; rfl
        rw [hfSfound n hsome, hfb]
        dsimp only
        by_cases hc : blockNames.contains n = true
        · rw [if_pos hc]
          obtain ⟨cvm₂, mval₂, -, -, hv₂⟩ := hI n hc ci₂ hf₂
          exact (hv₂ ψ).symm
        · rw [if_neg hc]
  have hrenS : cvA.type.renameConsts fS = cvm.type := by
    rw [htypeA, ← Expr.renameConsts_congr_resolve
      (fun n hn => (hfSfound n hn).symm) tyA hres]
    rw [← htypeA]
    exact hrenf
  rcases hkind with ⟨⟨cv, caps', rfl⟩, rfl⟩ | ⟨cv, nP, nF, rfl, rfl⟩ |
    ⟨cv, nP, nm, ni, rules, rules', rfl, hall, heqf, hcir, rfl⟩
  · -- inductive type former
    have hwf : ConstWF ⟨.indInfo cvA caps :: env'.consts⟩
        (.indInfo cvA caps) := by
      refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_⟩
      · intro cv2 v2 heq; exact nomatch heq
      · intro cv2 nP' nM' nm' ni' rules heq; exact nomatch heq
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_one m
      (.indInfo cvA caps) fS (cvA.name.str "_model") hfind' hnres hwf htres
      (Or.inl ⟨_, _, rfl⟩) hfm hlps hrenS hroS
      (fun _ => ⟨show (env'.find? (cvA.name.str "_model")).isSome = true
        by rw [hfm]; rfl, fun ψ => rfl⟩)
      (fun T j hh => hprojRef T j hh)
      (fun cv₂ caps₂ heq hcape _hres' => by
        injection heq with hcv hcaps
        subst hcv
        subst hcaps
        have hpinsA : EtaPins env' cvA.name cvA.levelParams caps := by
          rw [hnameA, hlpsA]
          exact hpins cv caps' rfl
        obtain ⟨tcv, tval, cvmT, mvalT, sbinders, tbindersM, sbody,
          tbodyM, tySlot, ℓA, hthmE, htlpsE, hTmE, hTmlpsE,
          ⟨cvmC, mvalC, hCmE, hCmlpsE⟩, hPjE, heqfE, hS_stripE,
          hTm_stripE, hsdomsE, hxdomE, hsbodyE⟩ :=
          hpinsA.1 hcape
        obtain ⟨rfl, rfl⟩ : cvm = cvmT ∧ mval = mvalT := by
          rw [hfm] at hTmE
          have h1 := Option.some.inj hTmE
          exact ⟨by injection h1, by injection h1⟩
        refine ⟨by rw [hCmE]; rfl, ?_, ?_⟩
        · intro j hj
          obtain ⟨cvmj, mvalj, hfj, -⟩ := hPjE j hj
          show (env'.find? (projModelName cvA.name j)).isSome = true
          rw [hfj]
          rfl
        · intro φ'' us ps x d₁ ρ₁ d₂ ρ₂ rest hlen hx hfit
          obtain ⟨tbinders, tbody, hT_strip, hbsmap, -⟩ :=
            Expr.stripPis_renameConsts_inv (f := fS) caps.etaParams
              (by rw [hrenS]; exact hTm_stripE)
          have hsdomsF : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
              k < caps.etaParams →
              sbinders[k]? = some b → tbinders[k]? = some b' →
              b.2.1 = (b'.2.1).renameConsts fS := by
            intro k b b' hk hb hb'
            have hbm : tbindersM[k]? =
                some (b'.1, (b'.2.1).renameConsts fS, b'.2.2) := by
              rw [hbsmap, List.getElem?_map, hb']
              rfl
            exact hsdomsE k b _ hk hb hbm
          have hcvp : ConstValParams m.val env' :=
            fun n ci₂ hf ψ₁ ψ₂ hψ => m.val_params n ci₂ hf ψ₁ ψ₂ hψ
          have heqval : ∀ ψ'' : Name → Nat,
              m.val eqName ψ'' = eqVal V ψ'' := by
            intro ψ''
            obtain ⟨-, hpv⟩ :=
              m.ind_ok.2.2.2.1 eqName eqA heqfE (by rfl) (by decide)
            rw [hpv ψ'']
            simp [pinnedVal]
          have hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
              interpClosed V m.val env' ψ'' tcv.type = some Pv ∧
              m.val tcv.name ψ'' ∈ˢ Pv := by
            intro ψ''
            obtain ⟨P, hP, hmem⟩ := m.mem_type _ (find?_mem hthmE) ψ''
            exact ⟨P, hP, hmem⟩
          have hSw : tcv.type.hasFvar = false := by
            obtain ⟨h1, -⟩ := m.wf _ (find?_mem hthmE)
            exact h1
          have hthm_annot : ∀ ψ'' : Name → Nat,
              AnnotOk V m.val env' ψ'' 0 (rho0 V) tcv.type :=
            fun ψ'' => (m.annot_ok _ (find?_mem hthmE) ψ'').1
          exact eta_rule_fold hroS hcvp hTmE hTmlpsE
            (cimC := .defnInfo cvmC mvalC) hCmE hCmlpsE
            (fun j hj => by
              obtain ⟨cvmj, mvalj, hfj, hjlps⟩ := hPjE j hj
              exact ⟨.defnInfo cvmj mvalj, hfj, hjlps⟩)
            heqfE heqval hthm_mem hthm_annot hSw hS_stripE hT_strip
            hsdomsF hxdomE hsbodyE htyf hlen hx hfit)
      (fun cv₂ caps₂ heq hcapu _hres' => by
        injection heq with hcv hcaps
        subst hcv
        subst hcaps
        have hpinsA : EtaPins env' cvA.name cvA.levelParams caps := by
          rw [hnameA, hlpsA]
          exact hpins cv caps' rfl
        obtain ⟨tcv, tval, cvmT, mvalT, sbinders, tbindersM, sbody,
          tbodyM, tySlot, ℓA, hthmE, htlpsE, hTmE, hTmlpsE, heqfE,
          hS_stripE, hTm_stripE, hsdomsE, hxdomE, hydomE, hsbodyE⟩ :=
          hpinsA.2 hcapu
        obtain ⟨rfl, rfl⟩ : cvm = cvmT ∧ mval = mvalT := by
          rw [hfm] at hTmE
          have h1 := Option.some.inj hTmE
          exact ⟨by injection h1, by injection h1⟩
        intro φ'' us ps x y d₁ ρ₁ d₂ ρ₂ rest hlen hx hy hfit
        obtain ⟨tbinders, tbody, hT_strip, hbsmap, -⟩ :=
          Expr.stripPis_renameConsts_inv (f := fS) caps.unitParams
            (by rw [hrenS]; exact hTm_stripE)
        have hsdomsF : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
            k < caps.unitParams →
            sbinders[k]? = some b → tbinders[k]? = some b' →
            b.2.1 = (b'.2.1).renameConsts fS := by
          intro k b b' hk hb hb'
          have hbm : tbindersM[k]? =
              some (b'.1, (b'.2.1).renameConsts fS, b'.2.2) := by
            rw [hbsmap, List.getElem?_map, hb']
            rfl
          exact hsdomsE k b _ hk hb hbm
        have hcvp : ConstValParams m.val env' :=
          fun n ci₂ hf ψ₁ ψ₂ hψ => m.val_params n ci₂ hf ψ₁ ψ₂ hψ
        have heqval : ∀ ψ'' : Name → Nat,
            m.val eqName ψ'' = eqVal V ψ'' := by
          intro ψ''
          obtain ⟨-, hpv⟩ :=
            m.ind_ok.2.2.2.1 eqName eqA heqfE (by rfl) (by decide)
          rw [hpv ψ'']
          simp [pinnedVal]
        have hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
            interpClosed V m.val env' ψ'' tcv.type = some Pv ∧
            m.val tcv.name ψ'' ∈ˢ Pv := by
          intro ψ''
          obtain ⟨P, hP, hmem⟩ := m.mem_type _ (find?_mem hthmE) ψ''
          exact ⟨P, hP, hmem⟩
        have hSw : tcv.type.hasFvar = false := by
          obtain ⟨h1, -⟩ := m.wf _ (find?_mem hthmE)
          exact h1
        have hthm_annot : ∀ ψ'' : Name → Nat,
            AnnotOk V m.val env' ψ'' 0 (rho0 V) tcv.type :=
          fun ψ'' => (m.annot_ok _ (find?_mem hthmE) ψ'').1
        exact unit_rule_fold hroS hcvp hTmE hTmlpsE heqfE heqval
          hthm_mem hthm_annot hSw hS_stripE hT_strip hsdomsF hxdomE
          hydomE hsbodyE htyf hlen hx hy hfit)
    exact ⟨m₁, BlockInstalled.step hI hms hfm hlps hval₁ hpres₁⟩
  · -- constructor
    have hwf : ConstWF ⟨.ctorInfo cvA nP nF :: env'.consts⟩
        (.ctorInfo cvA nP nF) := by
      refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_⟩
      · intro cv2 v2 heq; exact nomatch heq
      · intro cv2 nP' nM' nm' ni' rules heq; exact nomatch heq
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_one m
      (.ctorInfo cvA nP nF) fS (cvA.name.str "_model")
      hfind' hnres hwf htres
      (Or.inr (Or.inl ⟨_, _, _, rfl⟩)) hfm hlps hrenS hroS
      (fun _ => ⟨show (env'.find? (cvA.name.str "_model")).isSome = true
        by rw [hfm]; rfl, fun ψ => rfl⟩)
      (fun T j hh => hprojRef T j hh)
      (fun cv₂ caps₂ hcon => nomatch hcon)
      (fun cv₂ caps₂ hcon => nomatch hcon)
    exact ⟨m₁, BlockInstalled.step hI hms hfm hlps hval₁ hpres₁⟩
  · -- recursor
    have hfself : fb cvA.name = cvA.name.str "_model" := by
      rw [hfb]; dsimp only; rw [if_pos hbnA]
    have hfnot : ∀ n, fb n ≠ cvA.name := by
      intro n
      rw [hfb]
      dsimp only
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        exact Name.str_model_ne hms
      · rw [if_neg hc]
        intro hn
        rw [hn] at hc
        exact hc hbnA
    have hff₀ : ∀ n, n ≠ cvA.name → fb n = fS n := by
      intro n hn
      cases hf₂ : env'.find? n with
      | some ci₂ =>
        exact (hfSfound n (by rw [hf₂]; rfl)).symm
      | none =>
        rw [hfSnone n hf₂, hfb]
        have hnc : ¬blockNames.contains n = true := by
          intro hc
          have hmem : n ∈ blockNames := by
            simpa using hc
          have hor := List.all_eq_true.mp hall n hmem
          simp only [Bool.or_eq_true, beq_iff_eq] at hor
          rcases hor with h1 | h1
          · exact hn h1
          · rw [hf₂] at h1; exact nomatch h1
        dsimp only
        rw [if_neg hnc]
    have heqval : ∀ ψ'' : Name → Nat, m.val eqName ψ'' = eqVal V ψ'' := by
      intro ψ''
      obtain ⟨-, hpv⟩ :=
        m.ind_ok.2.2.2.1 eqName eqA heqf (by rfl) (by decide)
      rw [hpv ψ'']
      simp [pinnedVal]
    have hwf : ConstWF ⟨.recInfo cvA nP 1 nm ni rules' :: env'.consts⟩
        (.recInfo cvA nP 1 nm ni rules') := by
      have hiso : ∀ n,
          ((⟨.recInfo cvA nP 1 nm ni [] :: env'.consts⟩ : Env).find? n).isSome
          =
          ((⟨.recInfo cvA nP 1 nm ni rules' ::
            env'.consts⟩ : Env).find? n).isSome := by
        intro n
        rw [Env.find?_cons, Env.find?_cons]
        by_cases hh : cvA.name = n
        · rw [if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
              []).name = n from hh),
            if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
              rules').name = n from hh)]
          rfl
        · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
              []).name = n from hh),
            if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
              rules').name = n from hh)]
      refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_⟩
      · intro cv2 v2 heq; exact nomatch heq
      · intro cv2 nP' nM' nm' ni' rules'' heq r hr
        injection heq with e1 e2 e3 e4 e5 e6
        subst e6
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
          -, -, -, -, -, hrf, hrb', -, -, -, -, -, -, -, -, -, -, -,
          hrlp, hrres⟩ :=
          checkIotaRules_inv 0 rules rules' hcir r hr
        refine ⟨hrf, by rw [← e1]; exact hrlp, ?_, hrb'⟩
        rw [← Expr.constsResolve_congr hiso]
        exact hrres
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_rec m cvA nP nm ni rules'
      fb hfind' hnres hshapeA hwf htres hfm hlps hrenf
      fS hroS hff₀ hfself hfnot heqf heqval
      (checkIotaRules_inv 0 rules rules' hcir)
    exact ⟨m₁, BlockInstalled.step
      (ci₁ := .recInfo cvA nP 1 nm ni rules') hI hms hfm hlps hval₁ hpres₁⟩

/-- A successful fold's members were all fresh at their own step, hence
already fresh at any earlier point. -/
theorem checkIndMember_fold_names {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' = .ok env₂ →
    ∀ ci ∈ rest, env'.find? ci.name = none
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ =>
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0, -⟩ := checkConstantVal_inv hccv
    rw [List.mem_cons] at hci
    rcases hci with rfl | hci
    · exact hfind0
    · have hnone₁ := checkIndMember_fold_names rest env₁ env₂ h ci hci
      have henv₁ : ∃ ci₁, env₁ = (⟨ci₁ :: env'.consts⟩ : Env) := by
        rcases hkind with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩ |
          ⟨cv, nP, nm, rules, rules', -, -, -, -, -, rfl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      obtain ⟨ci₁, rfl⟩ := henv₁
      rw [Env.find?_cons] at hnone₁
      split at hnone₁
      · exact nomatch hnone₁
      · exact hnone₁

/-- The fold of `checkIndDecl` preserves having a model together with
the block-install invariant. -/
theorem checkIndFold_sound {blockNames : List Name} {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    (∀ ci ∈ rest, blockNames.contains ci.name = true) →
    (∀ cv caps₂,
      (ConstantInfo.indInfo cv caps₂) ∈ rest →
      EtaPins env' cv.name cv.levelParams caps) →
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' = .ok env₂ →
    ∀ m : EnvModel V env', BlockInstalled blockNames env' m.val →
    ∃ m₂ : EnvModel V env₂, BlockInstalled blockNames env₂ m₂.val
  | [], env', env₂, hns, _hp, h, m, hI => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨m, hI⟩
  | ci :: rest, env', env₂, hns, hp, h, m, hI => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env' ci with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨m₁, hI₁⟩ := checkIndMember_sound hstep
      (fun cv caps₂ heq => hp cv caps₂
        (by rw [← heq]; exact List.mem_cons_self))
      (hns ci (by simp)) m hI
    obtain ⟨cvA', cvm', mval', hccv', -, -, -, -, hkind'⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0', -, -, -, -, -, tyA', stype', u', -, -, -, -, -,
      hcvA'⟩ := checkConstantVal_inv hccv'
    have hnameA' : cvA'.name = ci.name := by
      rw [hcvA']
      rfl
    have henv₁ : ∃ ci₁ : ConstantInfo, ci₁.name = cvA'.name ∧
        env₁ = ⟨ci₁ :: env'.consts⟩ := by
      rcases hkind' with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩ |
        ⟨cv, nP, nm, ni, rules, rules', -, -, -, -, rfl⟩
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
    obtain ⟨ci₁, hname₁, rfl⟩ := henv₁
    have hfresh₁ : env'.find? ci₁.name = none := by
      rw [hname₁, hnameA']
      exact hfind0'
    exact checkIndFold_sound rest _ env₂
      (fun ci' hci' => hns ci' (by simp [hci']))
      (fun cv caps₂ hmem => EtaPins.step
        (hp cv caps₂ (List.mem_cons_of_mem _ hmem)) hfresh₁)
      h m₁ hI₁

/-- Invert stage 1 of `checkProjFn` (the stored-constant lookups). -/
theorem checkProjLookups_inv {env' : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat} {cvj mcv : ConstantVal}
    (h : (checkProjLookups env' T ctorName lps nP nF i : CheckM _) =
      .ok (cvj, mcv)) :
    ∃ mval,
      env'.find? ctorName = some (.ctorInfo cvj nP nF) ∧
      env'.find? (projModelName T i) = some (.defnInfo mcv mval) ∧
      mcv.levelParams = lps ∧
      env'.find? (projFnName T i) = none ∧
      (env'.find? T).isSome = true ∧
      env'.find? eqName = some eqA := by
  simp only [checkProjLookups, Bind.bind, Except.bind] at h
  revert h
  match hctor : env'.find? ctorName with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.ctorInfo cvj' cnP cnF) => ?_
  intro h
  dsimp only at h
  by_cases hpp : cnP = nP ∧ cnF = nF
  case neg => rw [if_neg hpp] at h; exact nomatch h
  rw [if_pos hpp] at h
  obtain ⟨rfl, rfl⟩ := hpp
  try dsimp only at h
  revert h
  match hfm : env'.find? (projModelName T i) with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo mcv' mval) => ?_
  intro h
  dsimp only at h
  by_cases hmlps : mcv'.levelParams = lps
  case neg => rw [if_neg hmlps] at h; exact nomatch h
  rw [if_pos hmlps] at h
  try dsimp only at h
  by_cases hpn : (env'.find? (projFnName T i)).isNone = true
  case neg => rw [if_neg hpn] at h; exact nomatch h
  rw [if_pos hpn] at h
  have hpnone : env'.find? (projFnName T i) = none := by
    revert hpn
    cases env'.find? (projFnName T i) <;> simp
  try dsimp only at h
  by_cases hTf : (env'.find? T).isSome = true
  case neg => rw [if_neg hTf] at h; exact nomatch h
  rw [if_pos hTf] at h
  try dsimp only at h
  by_cases heqf : env'.find? eqName = some eqA
  case neg => rw [if_neg heqf] at h; exact nomatch h
  rw [if_pos heqf] at h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨mval, rfl, rfl, hmlps, hpnone, hTf, heqf⟩

/-- Invert stage 2 of `checkProjFn` (the public projection type). -/
theorem checkProjTy_inv {env' : Env} {T ctorName : Name} {lps : List Name}
    {mty pty : Expr} {nP nF : Nat}
    (h : (checkProjTy env' T ctorName lps mty nP nF : CheckM _) =
      .ok pty) :
    pty = mty.renameConsts (projBack T ctorName nF) ∧
    pty.renameConsts (projFwd T ctorName nF) = mty ∧
    pty.constsResolve env' = true ∧
    pty.looseBVarsBounded 0 = true ∧
    pty.hasFvar = false ∧
    pty.allLevelParamsDefined lps = true := by
  simp only [checkProjTy, Bind.bind, Except.bind] at h
  by_cases hround : ((mty.renameConsts (projBack T ctorName nF)).renameConsts
      (projFwd T ctorName nF) == mty) = true
  case neg => rw [if_neg hround] at h; exact nomatch h
  rw [if_pos hround] at h
  try dsimp only at h
  by_cases hres : (mty.renameConsts (projBack T ctorName nF)).constsResolve
      env' = true
  case neg => rw [if_neg hres] at h; exact nomatch h
  rw [if_pos hres] at h
  try dsimp only at h
  by_cases hwf3 : ((mty.renameConsts
        (projBack T ctorName nF)).looseBVarsBounded 0 &&
      !(mty.renameConsts (projBack T ctorName nF)).hasFvar &&
      (mty.renameConsts (projBack T ctorName nF)).allLevelParamsDefined
        lps) = true
  case neg => rw [if_neg hwf3] at h; exact nomatch h
  rw [if_pos hwf3] at h
  simp only [Bool.and_eq_true] at hwf3
  obtain ⟨⟨hptyb, hptyf'⟩, hptylp⟩ := hwf3
  have hptyf : (mty.renameConsts (projBack T ctorName nF)).hasFvar
      = false := by
    revert hptyf'
    cases (mty.renameConsts (projBack T ctorName nF)).hasFvar <;> simp
  try dsimp only at h
  by_cases hpis : ((mty.renameConsts
      (projBack T ctorName nF)).stripPis (nP + 1)).isSome = true
  case neg => rw [if_neg hpis] at h; exact nomatch h
  rw [if_pos hpis] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, eq_of_beq hround, hres, hptyb, hptyf, hptylp⟩

/-- Invert stage 3 of `checkProjFn` (the reduction rule). -/
theorem checkProjRule_inv {env' : Env} {cvj : ConstantVal} {lps : List Name}
    {nP nF i : Nat} {rhsA : Expr}
    (h : checkProjRule (fueledOps F) env' cvj lps nP nF i = .ok rhsA) :
    ∃ raw rbinders cbindersR cbody,
      Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) = some raw ∧
      raw.hasFvar = false ∧
      raw.looseBVarsBounded 0 = true ∧
      annotateCore env' F 0 raw = .ok rhsA ∧
      rhsA.allLevelParamsDefined lps = true ∧
      rhsA.constsResolve env' = true ∧
      rhsA.looseBVarsBounded 0 = true ∧
      rhsA.hasFvar = false ∧
      rhsA.stripLams (nP + nF) = some (rbinders, .bvar (nF - 1 - i)) ∧
      cvj.type.stripPis (nP + nF) = some (cbindersR, cbody) ∧
      domsMatchAux (fun _ e => e) rbinders cbindersR 0 0 (nP + nF)
        = true := by
  simp only [checkProjRule, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
  revert h
  match hraw : Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i)) with
  | none => intro h; exact nomatch h
  | some raw => ?_
  intro h
  dsimp only at h
  by_cases hrawwf : (!raw.hasFvar && raw.looseBVarsBounded 0) = true
  case neg => rw [if_neg hrawwf] at h; exact nomatch h
  rw [if_pos hrawwf] at h
  simp only [Bool.and_eq_true] at hrawwf
  obtain ⟨hrawf', hrawb⟩ := hrawwf
  have hrawf : raw.hasFvar = false := by
    revert hrawf'
    cases raw.hasFvar <;> simp
  try dsimp only at h
  cases hann : annotateCore env' F 0 raw with
  | error e => rw [hann] at h; exact nomatch h
  | ok rhsA' => ?_
  rw [hann] at h
  try dsimp only at h
  by_cases hrwf : (rhsA'.allLevelParamsDefined lps &&
      rhsA'.constsResolve env' && rhsA'.looseBVarsBounded 0 &&
      !rhsA'.hasFvar) = true
  case neg => rw [if_neg hrwf] at h; exact nomatch h
  rw [if_pos hrwf] at h
  simp only [Bool.and_eq_true] at hrwf
  obtain ⟨⟨⟨hrlp, hrres⟩, hrb⟩, hrf'⟩ := hrwf
  have hrf : rhsA'.hasFvar = false := by
    revert hrf'
    cases rhsA'.hasFvar <;> simp
  try dsimp only at h
  revert h
  match hstripR : rhsA'.stripLams (nP + nF) with
  | none => intro h; exact nomatch h
  | some (rbinders, rrbody) => ?_
  intro h
  dsimp only at h
  by_cases hrrb : (rrbody == Expr.bvar (nF - 1 - i)) = true
  case neg => rw [if_neg hrrb] at h; exact nomatch h
  rw [if_pos hrrb] at h
  obtain rfl := eq_of_beq hrrb
  try dsimp only at h
  revert h
  match hC_strip : cvj.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (cbindersR, cbody) => ?_
  intro h
  dsimp only at h
  by_cases hdomsB : domsMatchAux (fun _ e => e) rbinders cbindersR 0 0
      (nP + nF) = true
  case neg => rw [if_neg hdomsB] at h; exact nomatch h
  rw [if_pos hdomsB] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨raw, rbinders, cbindersR, cbody, rfl, hrawf, hrawb, hann,
    hrlp, hrres, hrb, hrf, hstripR, rfl, hdomsB⟩

/-- Invert stage 4 of `checkProjFn` (the pinned iota statement). -/
theorem checkProjIota_inv {env' : Env} {T ctorName : Name}
    {lps : List Name} {cvj : ConstantVal} {nP nF i : Nat} {u : Unit}
    (h : (checkProjIota env' T ctorName lps cvj nP nF i : CheckM _) =
      .ok u) :
    ∃ tcv tval sbinders cbindersR cbody tySlot ℓA,
      env'.find? ((projModelName T i).str "iota") =
        some (.thmInfo tcv tval) ∧
      tcv.levelParams = lps ∧
      cvj.type.stripPis (nP + nF) = some (cbindersR, cbody) ∧
      domsMatchAux (fun _ e => e.renameConsts (projFwd T ctorName nF))
        sbinders cbindersR 0 0 (nP + nF) = true ∧
      tcv.type.stripPis (nP + nF) = some (sbinders,
        .app (.app (.app (.const eqName [ℓA]) tySlot)
          (Expr.mkAppN (.const (projModelName T i) (lps.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
             [Expr.mkAppN
               (.const (ctorName.str "_model")
                 (cvj.levelParams.map .param))
               (((List.range nP).map fun k =>
                   Expr.bvar (nP + nF - 1 - k)) ++
                ((List.range nF).map fun k =>
                  Expr.bvar (nF - 1 - k)))])))
          (.bvar (nF - 1 - i))) := by
  simp only [checkProjIota, Bind.bind, Except.bind] at h
  revert h
  match hthm : env'.find? ((projModelName T i).str "iota") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.thmInfo tcv tval) => ?_
  intro h
  dsimp only at h
  by_cases htlps : tcv.levelParams = lps
  case neg => rw [if_neg htlps] at h; exact nomatch h
  rw [if_pos htlps] at h
  try dsimp only at h
  revert h
  match hS_strip : tcv.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (sbinders, sbody) => ?_
  intro h
  dsimp only at h
  revert h
  match hC_strip : cvj.type.stripPis (nP + nF) with
  | none => intro h; exact nomatch h
  | some (cbindersR, cbody) => ?_
  intro h
  dsimp only at h
  by_cases hsdomsB : domsMatchAux
      (fun _ e => e.renameConsts (projFwd T ctorName nF))
      sbinders cbindersR 0 0 (nP + nF) = true
  case neg => rw [if_neg hsdomsB] at h; exact nomatch h
  rw [if_pos hsdomsB] at h
  try dsimp only at h
  cases sbody
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case const => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i sA rhsC
  cases sA
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case const => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i sB lhsC
  cases sB
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case const => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i sEq tySlot
  cases sEq
  case bvar => exact nomatch h
  case fvar => exact nomatch h
  case sort => exact nomatch h
  case app => exact nomatch h
  case lam => exact nomatch h
  case forallE => exact nomatch h
  case letE => exact nomatch h
  case lit => exact nomatch h
  case proj => exact nomatch h
  rename_i c ℓs
  cases ℓs
  case nil => exact nomatch h
  rename_i ℓA ℓtail
  cases ℓtail
  case cons => exact nomatch h
  try dsimp only at h
  by_cases hc : c = eqName
  case neg => rw [if_neg hc] at h; exact nomatch h
  rw [if_pos hc] at h
  subst hc
  try dsimp only at h
  by_cases hlhs : (lhsC == Expr.mkAppN
      (.const (projModelName T i) (lps.map .param))
      (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
       [Expr.mkAppN
         (.const (ctorName.str "_model") (cvj.levelParams.map .param))
         (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
          ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))])) = true
  case neg => rw [if_neg hlhs] at h; exact nomatch h
  rw [if_pos hlhs] at h
  obtain rfl := eq_of_beq hlhs
  try dsimp only at h
  by_cases hrhsC : (rhsC == Expr.bvar (nF - 1 - i)) = true
  case neg => rw [if_neg hrhsC] at h; exact nomatch h
  rw [if_pos hrhsC] at h
  obtain rfl := eq_of_beq hrhsC
  exact ⟨tcv, tval, sbinders, cbindersR, cbody, tySlot, ℓA,
    rfl, htlps, rfl, hsdomsB, hS_strip⟩

/-- Invert a successful `checkProjFn` into its stages. -/
theorem checkProjFn_inv {env' env₁ : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat}
    (h : checkProjFn (fueledOps F) env' T ctorName lps nP nF i = .ok env₁) :
    ∃ cvj mcv,
      (checkProjLookups env' T ctorName lps nP nF i : CheckM _) =
        .ok (cvj, mcv) ∧
      ∃ pty, (checkProjTy env' T ctorName lps mcv.type nP nF : CheckM _) =
        .ok pty ∧
      i < nF ∧
      ∃ rhsA, checkProjRule (fueledOps F) env' cvj lps nP nF i = .ok rhsA ∧
      (∃ u : Unit, (checkProjIota env' T ctorName lps cvj nP nF i : CheckM _)
        = .ok u) ∧
      env₁ = ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP 0 0 0
        [⟨ctorName, nF, rhsA⟩] :: env'.consts⟩ := by
  simp only [checkProjFn, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
  cases hlk : (checkProjLookups env' T ctorName lps nP nF i : CheckM _) with
  | error e => rw [hlk] at h; exact nomatch h
  | ok pr => ?_
  rw [hlk] at h
  obtain ⟨cvj, mcv⟩ := pr
  try dsimp only at h
  cases hty : (checkProjTy env' T ctorName lps mcv.type nP nF : CheckM _) with
  | error e => rw [hty] at h; exact nomatch h
  | ok pty => ?_
  rw [hty] at h
  try dsimp only at h
  by_cases hi : i < nF
  case neg => rw [if_neg hi] at h; exact nomatch h
  rw [if_pos hi] at h
  try dsimp only at h
  cases hrule : checkProjRule (fueledOps F) env' cvj lps nP nF i with
  | error e => rw [hrule] at h; exact nomatch h
  | ok rhsA => ?_
  rw [hrule] at h
  try dsimp only at h
  cases hio : (checkProjIota env' T ctorName lps cvj nP nF i : CheckM _) with
  | error e => rw [hio] at h; exact nomatch h
  | ok u => ?_
  rw [hio] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨cvj, mcv, rfl, pty, hty, hi, rhsA, hrule, ⟨u, hio⟩, h.symm⟩

/-- The projection-phase fold invariant: the parent type and the
constructor still carry their model values, and every installed
projection function carries its `_model.proj_j`'s. -/
def ProjPhaseInv (T ctorName : Name) (nF : Nat) (env' : Env)
    (val : ConstVal V) : Prop :=
  (∀ ci, env'.find? T = some ci →
    ∃ cvm mval, env'.find? (T.str "_model") = some (.defnInfo cvm mval) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat, val T ψ = val (T.str "_model") ψ) ∧
  (∀ ci, env'.find? ctorName = some ci →
    ∃ cvm mval,
      env'.find? (ctorName.str "_model") = some (.defnInfo cvm mval) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        val ctorName ψ = val (ctorName.str "_model") ψ) ∧
  (∀ j, j < nF → ∀ ci, env'.find? (projFnName T j) = some ci →
    ∃ cvm mval,
      env'.find? (projModelName T j) = some (.defnInfo cvm mval) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        val (projFnName T j) ψ = val (projModelName T j) ψ)

set_option maxHeartbeats 1600000 in
/-- One projection-function install preserves having a model together
with the phase invariant. -/
theorem checkProjFn_sound {env' env₁ : Env} {T ctorName : Name}
    {lps : List Name} {nP nF i : Nat}
    (h : checkProjFn (fueledOps F) env' T ctorName lps nP nF i = .ok env₁)
    (m : EnvModel V env')
    (hinv : ProjPhaseInv T ctorName nF env' m.val) :
    ∃ m₁ : EnvModel V env₁, ProjPhaseInv T ctorName nF env₁ m₁.val := by
  obtain ⟨cvj, mcv, hlk, pty, hty, hi, rhsA, hrule, ⟨u, hio⟩, henv₁⟩ :=
    checkProjFn_inv h
  obtain ⟨mval, hctor, hfm, hmlps, hpnone, hTf, heqf⟩ :=
    checkProjLookups_inv hlk
  obtain ⟨hptyB, hround, hptyres, hptyb, hptyf, hptylp⟩ :=
    checkProjTy_inv hty
  obtain ⟨raw, rbinders, cbindersR, cbody, hraw, hrawf, hrawb, hann,
    hrlp, hrres, hrb, hrf, hstripR, hC_strip, hdomsB⟩ :=
    checkProjRule_inv hrule
  obtain ⟨tcv, tval, sbinders, cbindersR₂, cbody₂, tySlot, ℓA,
    hthm, htlps, hC_strip₂, hsdomsB, hS_strip⟩ := checkProjIota_inv hio
  obtain ⟨rfl, rfl⟩ : cbindersR = cbindersR₂ ∧ cbody = cbody₂ := by
    have hpair := Option.some.inj (hC_strip.symm.trans hC_strip₂)
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  subst henv₁
  -- basic disequalities from freshness
  have hTne : T ≠ projFnName T i := by
    intro he
    rw [he, hpnone] at hTf
    exact nomatch hTf
  have hCne : ctorName ≠ projFnName T i := by
    intro he
    rw [he, hpnone] at hctor
    exact nomatch hctor
  -- the semantically pruned renaming and the rule's full renaming
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Name → Name, f₀ = fun n =>
      if (env'.find? n).isSome then projFwd T ctorName nF n else n :=
    ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : Name → Name, f = fun n =>
      if n = projFnName T i then projModelName T i else f₀ n := ⟨_, rfl⟩
  have hfound : ∀ n ci₂, env'.find? n = some ci₂ →
      (∃ ci', env'.find? (projFwd T ctorName nF n) = some ci' ∧
        ci'.toConstantVal.levelParams = ci₂.toConstantVal.levelParams) ∧
      (∀ ψ : Name → Nat,
        m.val (projFwd T ctorName nF n) ψ = m.val n ψ) := by
    intro n ci₂ hf₂
    unfold projFwd
    try dsimp only
    by_cases h1 : n = T
    · subst h1
      rw [if_pos rfl]
      obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.1 ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
    rw [if_neg h1]
    by_cases h2 : n = ctorName
    · subst h2
      rw [if_pos rfl]
      obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.1 ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
    rw [if_neg h2]
    cases hfind : (List.range nF).find? (fun j => n == projFnName T j) with
    | none => exact ⟨⟨ci₂, hf₂, rfl⟩, fun ψ => rfl⟩
    | some j =>
      have hjlt : j < nF :=
        List.mem_range.mp (List.mem_of_find?_eq_some hfind)
      have hprop := List.find?_some hfind
      have hprop' : (n == projFnName T j) = true := by
        simpa using hprop
      have hn : n = projFnName T j := eq_of_beq hprop'
      subst hn
      obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.2 j hjlt ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
  have hro : RenameOk m.val env' f₀ := by
    refine ⟨?_, ?_, ?_⟩
    · intro n ci₂ hf₂
      rw [hf₀]
      dsimp only
      rw [if_pos (show (env'.find? n).isSome = true by rw [hf₂]; rfl)]
      exact (hfound n ci₂ hf₂).1
    · intro n hf₂
      rw [hf₀]
      dsimp only
      rw [if_neg (show ¬(env'.find? n).isSome = true by
        rw [hf₂]; exact fun hx => nomatch hx)]
      exact hf₂
    · intro n ψ
      rw [hf₀]
      dsimp only
      cases hf₂ : env'.find? n with
      | none =>
        rw [if_neg (show ¬(none : Option ConstantInfo).isSome = true
          from fun hx => nomatch hx)]
      | some ci₂ =>
        rw [if_pos (show (some ci₂ : Option ConstantInfo).isSome = true
          from rfl)]
        exact (hfound n ci₂ hf₂).2 ψ
  have hagree : ∀ n, (env'.find? n).isSome = true →
      f n = projFwd T ctorName nF n := by
    intro n hn
    have hne : n ≠ projFnName T i := by
      intro he
      rw [he, hpnone] at hn
      exact nomatch hn
    rw [hf]
    dsimp only
    rw [if_neg hne, hf₀]
    dsimp only
    rw [if_pos hn]
  have hff₀ : ∀ n, n ≠ projFnName T i → f n = f₀ n := by
    intro n hn
    rw [hf]
    dsimp only
    rw [if_neg hn]
  have hfself : f (projFnName T i) = projModelName T i := by
    rw [hf]
    dsimp only
    rw [if_pos rfl]
  have hfnot : ∀ n, f n ≠ projFnName T i := by
    intro n
    rw [hf]
    dsimp only
    by_cases hn : n = projFnName T i
    · rw [if_pos hn]
      exact fun hh => Name.num_ne_str _ _ _ _ hh.symm
    · rw [if_neg hn, hf₀]
      dsimp only
      cases hf₂ : env'.find? n with
      | none =>
        rw [if_neg (show ¬(none : Option ConstantInfo).isSome = true
          from fun hx => nomatch hx)]
        exact hn
      | some ci₂ =>
        rw [if_pos (show (some ci₂ : Option ConstantInfo).isSome = true
          from rfl)]
        unfold projFwd
        try dsimp only
        by_cases h1 : n = T
        · rw [if_pos h1]
          exact fun hh => Name.num_ne_str _ _ _ _ hh.symm
        rw [if_neg h1]
        by_cases h2 : n = ctorName
        · rw [if_pos h2]
          exact fun hh => Name.num_ne_str _ _ _ _ hh.symm
        rw [if_neg h2]
        cases (List.range nF).find? (fun j => n == projFnName T j) with
        | none => exact hn
        | some j => exact fun hh => Name.num_ne_str _ _ _ _ hh.symm
  have hren : pty.renameConsts f = mcv.type := by
    rw [Expr.renameConsts_congr_resolve hagree pty hptyres]
    exact hround
  have hcres : cvj.type.constsResolve env' = true := by
    obtain ⟨-, -, h3, -⟩ := m.wf _ (find?_mem hctor)
    exact h3
  have hdomres :=
    (Expr.constsResolve_stripPis (nP + nF) hC_strip hcres).1
  have hclen : cbindersR.length = nP + nF :=
    Expr.stripPis_length _ hC_strip
  have hdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      rbinders[k]? = some b → cbindersR[k]? = some b' →
      b.2.1 = b'.2.1 := by
    intro k b b' hb hb'
    have hk : k < nP + nF := by
      rcases Nat.lt_or_ge k (nP + nF) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by omega)] at hb'
        exact nomatch hb'
    exact domsMatchAux_inv hdomsB hk
      (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
  have hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[k]? = some b → cbindersR[k]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f := by
    intro k b b' hb hb'
    have hk : k < nP + nF := by
      rcases Nat.lt_or_ge k (nP + nF) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by omega)] at hb'
        exact nomatch hb'
    have hkfwd := domsMatchAux_inv hsdomsB hk
      (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
    rw [hkfwd]
    exact (Expr.renameConsts_congr_resolve hagree _
      (hdomres b' (List.mem_of_getElem? hb'))).symm
  have hfctor : f ctorName = ctorName.str "_model" := by
    rw [hagree ctorName (by rw [hctor]; rfl)]
    unfold projFwd
    try dsimp only
    by_cases hCT : ctorName = T
    · rw [if_pos hCT, hCT]
    · rw [if_neg hCT, if_pos rfl]
  have heqval : ∀ ψ'' : Name → Nat, m.val eqName ψ'' = eqVal V ψ'' := by
    intro ψ''
    obtain ⟨-, hpv⟩ :=
      m.ind_ok.2.2.2.1 eqName eqA heqf (by rfl) (by decide)
    rw [hpv ψ'']
    simp [pinnedVal]
  have hwf : ConstWF
      ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP 0 0 0
        [⟨ctorName, nF, rhsA⟩] :: env'.consts⟩
      (.recInfo ⟨projFnName T i, lps, pty⟩ nP 0 0 0
        [⟨ctorName, nF, rhsA⟩]) := by
    refine ⟨hptyf, hptylp, Expr.constsResolve_mono hptyres, hptyb,
      ?_, ?_⟩
    · intro cv2 v2 heq
      exact nomatch heq
    · intro cv2 nP' nM' nm' ni' rules'' heq r hr
      injection heq with e1 e2 e3 e4 e5 e6
      subst e6
      rcases List.mem_cons.mp hr with rfl | hr
      · refine ⟨hrf, ?_, Expr.constsResolve_mono hrres, hrb⟩
        rw [← e1]
        exact hrlp
      · exact absurd hr List.not_mem_nil
  have hsbody' : (Expr.app (.app (.app (.const eqName [ℓA]) tySlot)
      (Expr.mkAppN (.const (projModelName T i) (lps.map .param))
        (((List.range nP).map fun k => Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN
           (.const (ctorName.str "_model")
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k =>
              Expr.bvar (nF - 1 - k)))])))
      (.bvar (nF - 1 - i))) = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const (f (projFnName T i)) (lps.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const (f ctorName)
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)] := by
    rw [hfself, hfctor]
    rfl
  have hprojmArg : ∀ (T' : Name) (j : Nat),
      projFnName T i = projFnName T' j →
      (env'.find? (projModelName T' j)).isSome = true ∧
      ∀ ψ : Name → Nat,
        m.val (projModelName T i) ψ = m.val (projModelName T' j) ψ := by
    intro T' j hh
    have hh' : Name.num (T.str "proj") i = Name.num (T'.str "proj") j := hh
    injection hh' with hp hij
    injection hp with hT hs
    subst hij
    subst hT
    exact ⟨by rw [hfm]; rfl, fun ψ => rfl⟩
  obtain ⟨m₁, hval₁, hpres₁⟩ := extend_proj_fn m
    ⟨projFnName T i, lps, pty⟩ nP nF i ⟨ctorName, nF, rhsA⟩ f
    (projModelName T i) hpnone
    (reservedBasisNames_not_num _ _) hwf hptyres hfm hmlps hprojmArg hren
    f₀ hro hff₀ hfself hfnot heqf heqval hi hctor rfl
    hann hrawf hrawb hrf hrb hrres hstripR rfl hC_strip hS_strip
    hdoms hsdoms hsbody' hthm htlps
  have hval₁' : ∀ ψ : Name → Nat,
      m₁.val (projFnName T i) ψ = m.val (projModelName T i) ψ := hval₁
  have hpres₁' : ∀ (n : Name) (ψ : Name → Nat), n ≠ projFnName T i →
      m₁.val n ψ = m.val n ψ := hpres₁
  have hfindNe : ∀ n : Name, n ≠ projFnName T i →
      (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP 0 0 0
        [⟨ctorName, nF, rhsA⟩] :: env'.consts⟩ : Env).find? n
        = env'.find? n := by
    intro n hn
    rw [Env.find?_cons,
      if_neg (show ¬(ConstantInfo.recInfo ⟨projFnName T i, lps, pty⟩
        nP 0 0 0 [⟨ctorName, nF, rhsA⟩]).name = n from
        fun hh => hn hh.symm)]
  refine ⟨m₁, ?_, ?_, ?_⟩
  · -- the parent type's clause
    intro ci₂ hf₂
    rw [hfindNe T hTne] at hf₂
    obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.1 ci₂ hf₂
    refine ⟨cvm₂, mval₂, ?_, hlps₂, ?_⟩
    · rw [hfindNe (T.str "_model")
        (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres₁' _ ψ hTne,
        hpres₁' _ ψ (fun hh => Name.num_ne_str _ _ _ _ hh.symm),
        hv₂ ψ]
  · -- the constructor's clause
    intro ci₂ hf₂
    rw [hfindNe ctorName hCne] at hf₂
    obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.1 ci₂ hf₂
    refine ⟨cvm₂, mval₂, ?_, hlps₂, ?_⟩
    · rw [hfindNe (ctorName.str "_model")
        (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres₁' _ ψ hCne,
        hpres₁' _ ψ (fun hh => Name.num_ne_str _ _ _ _ hh.symm),
        hv₂ ψ]
  · -- the projection-family clause
    intro j hj ci₂ hf₂
    by_cases hji : projFnName T j = projFnName T i
    · -- the freshly installed projection
      have hn' : Name.num (T.str "proj") j =
          Name.num (T.str "proj") i := hji
      injection hn' with hp hij
      subst hij
      refine ⟨mcv, mval, ?_, ?_, ?_⟩
      · rw [hfindNe (projModelName T j)
          (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hfm
      · rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo ⟨projFnName T j, lps, pty⟩
            nP 0 0 0 [⟨ctorName, nF, rhsA⟩]).name = projFnName T j
            from rfl)] at hf₂
        obtain rfl := Option.some.inj hf₂
        exact hmlps
      · intro ψ
        rw [hval₁' ψ,
          hpres₁' (projModelName T j) ψ
            (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
    · -- an earlier install, preserved
      rw [hfindNe (projFnName T j) hji] at hf₂
      obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.2 j hj ci₂ hf₂
      refine ⟨cvm₂, mval₂, ?_, hlps₂, ?_⟩
      · rw [hfindNe (projModelName T j)
          (fun hh => Name.num_ne_str _ _ _ _ hh.symm)]
        exact hfm₂
      · intro ψ
        rw [hpres₁' _ ψ hji,
          hpres₁' (projModelName T j) ψ
            (fun hh => Name.num_ne_str _ _ _ _ hh.symm),
          hv₂ ψ]

/-- The projection-phase fold preserves having a model together with
the phase invariant. -/
theorem checkProjFold_sound {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) (env' env₁ : Env),
    idxs.foldlM (fun e i =>
      if (e.find? (projModelName T i)).isSome then
        checkProjFn (fueledOps F) e T ctorName lps nP nF i
      else pure e) env' = .ok env₁ →
    ∀ m : EnvModel V env', ProjPhaseInv T ctorName nF env' m.val →
    ∃ m₁ : EnvModel V env₁, ProjPhaseInv T ctorName nF env₁ m₁.val
  | [], env', env₁, h, m, hinv => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨m, hinv⟩
  | i₀ :: rest, env', env₁, h, m, hinv => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    by_cases hm : (env'.find? (projModelName T i₀)).isSome = true
    · rw [if_pos hm] at h
      cases hstep : checkProjFn (fueledOps F) env' T ctorName lps nP nF i₀ with
      | error e => rw [hstep] at h; exact nomatch h
      | ok env₂ => ?_
      rw [hstep] at h
      obtain ⟨m₂, hinv₂⟩ := checkProjFn_sound hstep m hinv
      exact checkProjFold_sound rest env₂ env₁ h m₂ hinv₂
    · rw [if_neg hm] at h
      simp only [pure, Except.pure, Except.bind] at h
      exact checkProjFold_sound rest env' env₁ h m hinv

/-- Checking a modeled inductive block preserves having a model. -/
theorem checkIndDecl_sound {env env₂ : Env} {block : List ConstantInfo}
    (h : checkIndDecl (fueledOps F) env block = .ok env₂) (m : EnvModel V env) :
    Nonempty (EnvModel V env₂) := by
  rw [checkIndDecl] at h
  have hbn : ∀ ci ∈ block, (block.map (·.name)).contains ci.name = true :=
    fun ci hci => by
      have : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
      simpa using this
  split at h
  · -- the single-constructor arm installs the projection family
    rename_i cvT capsT cvC nP nF heqI heqC
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨env₁, hfold, h⟩ := Except.bind_ok h
    have hI₀ : BlockInstalled (block.map (·.name)) env m.val := by
      intro n hn ci₂ hf₂
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [checkIndMember_fold_names block env env₁ hfold ci₀ hci₀] at hf₂
      exact nomatch hf₂
    have hpins0 : ∀ (cv : ConstantVal) (caps₂ : IndCaps),
        (ConstantInfo.indInfo cv caps₂) ∈ block →
        EtaPins env cv.name cv.levelParams
          (indBlockCaps env cvT cvC nP nF) := by
      intro cv caps₂ hmem
      have hmemf : (ConstantInfo.indInfo cv caps₂) ∈
          ([ConstantInfo.indInfo cvT capsT] : List ConstantInfo) := by
        rw [← heqI]
        exact List.mem_filter.mpr ⟨hmem, rfl⟩
      have hid := List.mem_singleton.mp hmemf
      injection hid with h1 h2
      rw [h1]
      refine ⟨?_, ?_⟩
      · intro hcape
        simp only [indBlockCaps, Bool.and_eq_true] at hcape
        exact checkEtaThm_inv hcape.2
      · intro hcapu
        simp only [indBlockCaps] at hcapu
        exact checkUnitThm_inv hcapu
    obtain ⟨m₁, hI₁⟩ := checkIndFold_sound block env env₁ hbn hpins0
      hfold m hI₀
    have hTin : (ConstantInfo.indInfo cvT capsT) ∈ block := by
      have h1 : ConstantInfo.indInfo cvT capsT ∈
          [ConstantInfo.indInfo cvT capsT] :=
        List.mem_singleton.mpr rfl
      rw [← heqI] at h1
      exact (List.mem_filter.mp h1).1
    have hCin : (ConstantInfo.ctorInfo cvC nP nF) ∈ block := by
      have h1 : ConstantInfo.ctorInfo cvC nP nF ∈
          [ConstantInfo.ctorInfo cvC nP nF] :=
        List.mem_singleton.mpr rfl
      rw [← heqC] at h1
      exact (List.mem_filter.mp h1).1
    have hbnT : (block.map (·.name)).contains cvT.name = true := by
      have hmm : cvT.name ∈ block.map (fun x => x.name) :=
        List.mem_map_of_mem (f := fun x => x.name) hTin
      simpa using hmm
    have hbnC : (block.map (·.name)).contains cvC.name = true := by
      have hmm : cvC.name ∈ block.map (fun x => x.name) :=
        List.mem_map_of_mem (f := fun x => x.name) hCin
      simpa using hmm
    try simp only [Bind.bind, Except.bind] at h
    by_cases hfresh : ((List.range nF).all
        (fun j => (env₁.find? (projFnName cvT.name j)).isNone)) = true
    case neg => rw [if_neg hfresh] at h; exact nomatch h
    rw [if_pos hfresh] at h
    try simp only [pure, Except.pure] at h
    try dsimp only at h
    have hinv₀ : ProjPhaseInv cvT.name cvC.name nF env₁ m₁.val := by
      refine ⟨?_, ?_, ?_⟩
      · intro ci hf
        exact hI₁ cvT.name hbnT ci hf
      · intro ci hf
        exact hI₁ cvC.name hbnC ci hf
      · intro j hj ci hf
        have hnone := List.all_eq_true.mp hfresh j (List.mem_range.mpr hj)
        rw [Option.isNone_iff_eq_none.mp hnone] at hf
        exact nomatch hf
    obtain ⟨mf, -⟩ :=
      checkProjFold_sound (List.range nF) env₁ env₂ h m₁ hinv₀
    exact ⟨mf⟩
  · -- no single-constructor structure: the plain member fold
    have hI₀ : BlockInstalled (block.map (·.name)) env m.val := by
      intro n hn ci₂ hf₂
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [checkIndMember_fold_names block env env₂ h ci₀ hci₀] at hf₂
      exact nomatch hf₂
    obtain ⟨m₂, -⟩ := checkIndFold_sound block env env₂ hbn
      (fun _ _ _ => ⟨fun hcape => absurd hcape (by decide),
        fun hcapu => absurd hcapu (by decide)⟩) h m hI₀
    exact ⟨m₂⟩

end Setlec
