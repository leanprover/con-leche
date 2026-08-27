import Setlec.Verify.BridgeS4
import Setlec.Model.DirectWF

/-!
# Shared-state checker: the direct simple-structure phases (task #51)

The tail of the per-declaration composition whose `V`-free bulk is
`Setlec/Verify/BridgeS4.lean`: the run-level simulation of the direct
simple-structure install (task #82) and the two drivers above it,
`checkIndOrDirectSF_run` and `checkDeclSharedF_bridge`.

This is in `Setlec/Model/*` for exactly one reason: the direct path's
inversions (`checkDirect{Ind,Ctor,Rule,Proj}_inv`) live in
`Setlec/Model/DirectDecl.lean`, reached through `Setlec/Model/DirectWF.lean`.
Nothing here mentions `V` either — when the direct path is retired (§4
of the #148 design), the whole file folds into
`Setlec/Verify/BridgeS4.lean`.

One name changed in the split, and only because a private helper cannot
cross a module boundary: `checkDirectStructS_run` used
`Setlec/Verify/BridgeS4.lean`'s `private cvA_type_facts'`, which is the
same statement as the public `checkConstantVal_typeWF`
(`Setlec/Verify/BridgeWfImp.lean`) it is reached through here.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

open Expr EStore

/-! ## The direct simple-structure install (task #82) -/

/-- The projection-install phase of the direct path (one flush per
field, the accumulator's environment carried along).  The threaded
residual is pinned to `directProjResid` at the current index — the
invariant `checkDirectProjF_push` consumes; the step to `i + 1` is
its defining equation. -/
theorem checkDirectProjsS_run {T C : Name} {lps : List Name} {nP nF : Nat}
    {cvTa cvCa : ConstantVal} (hCf : cvCa.type.hasFvar = false) :
    ∀ (todo i : Nat) (rt? : Option Expr) (env : Env) {s₀ : IState}
      {fe' : FEnv} {s' : IState},
      EnvWF env → ISOKF s₀ →
      rt? = directProjResid T lps nP cvCa.type i →
      checkDirectProjsS mode T C lps nP nF cvTa cvCa todo i rt? (mkFEnv env) s₀
        = .ok (fe', s') →
      ISOKF s' ∧ Ext s₀.store s'.store ∧ fe' = mkFEnv fe'.env ∧
      EnvWF fe'.env ∧
      ∃ F, ((List.range' i todo).foldlM
        (checkDirectProj (fueledOpsM mode) T C lps nP nF cvTa cvCa) env).val F
        = .ok fe'.env
  | 0, i, rt?, env, s₀, fe', s', henv, hwf, _, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨hwf, Ext.refl _, rfl, henv, 0, rfl⟩
  | todo + 1, i, rt?, env, s₀, fe', s', henv, hwf, hrt, h => by
    rw [checkDirectProjsS] at h
    obtain ⟨u, sf, hflush, h⟩ := bindI_ok h
    rw [flushS_run] at hflush
    injection hflush with hflush
    obtain rfl : s₀.flushed = sf := congrArg Prod.snd hflush
    rw [checkDirectProjF_push (hr := hrt), bind_assoc] at h
    obtain ⟨e₁, s₂, hpj, h⟩ := bindI_ok h
    obtain ⟨hs₂, hext₂, e₁', hP, F₁, hF₁⟩ :=
      (checkDirectProjS_sim henv hCf (flushS_isok hwf)) e₁ s₂ hpj
    obtain rfl : e₁ = e₁' := hP
    rw [pure_bind] at h
    have hF₁p : checkDirectProj (fueledOps mode F₁) T C lps nP nF cvTa cvCa
        env i = .ok e₁ := by rw [← checkDirectProj_datF]; exact hF₁
    have hrt' : rt?.bind (Expr.instPisAtLift [directProjArg T lps nP i])
        = directProjResid T lps nP cvCa.type (i + 1) := by
      rw [hrt]; rfl
    obtain ⟨hwf', hext', hfe', henv', F₂, hF₂⟩ :=
      checkDirectProjsS_run hCf todo (i + 1) _ e₁
        (direct_proj_wf henv hF₁p)
        (hs₂.residue (tierOffE hext₂ hwf.wf.tier_off)) hrt' h
    refine ⟨hwf', (Ext.refl _).trans (hext₂.trans hext'), hfe', henv',
      max F₁ F₂, ?_⟩
    rw [List.range'_succ, List.foldlM_cons]
    exact atF_bind_intro hF₁ hF₂

set_option maxHeartbeats 1600000 in
/-- The direct simple-structure install at the shared driver is
reproduced by the pure fueled `checkDirectStruct`. -/
theorem checkDirectStructS_run {env : Env} (henv : EnvWF env)
    {p : DirectParts} {s₀ : IState} (hwf : ISOKF s₀)
    {feOut : FEnv} {s' : IState}
    (h : checkDirectStructS mode (mkFEnv env) p s₀ = .ok (feOut, s')) :
    ISOKF s' ∧ Ext s₀.store s'.store ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDirectStruct (fueledOps mode F) env p = .ok feOut.env := by
  unfold checkDirectStructS at h
  -- stage 1: the type former
  obtain ⟨u0, sA, hfl0, h⟩ := bindI_ok h
  rw [flushS_run] at hfl0
  injection hfl0 with hfl0
  obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
  rw [checkDirectIndF_push] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨q1, s₁, hind, h⟩ := bindI_ok h
  obtain ⟨hs₁, hext₁, q1', hP1, F₁, hF₁⟩ :=
    (checkDirectIndS_sim henv (flushS_isok hwf)) q1 s₁ hind
  obtain ⟨rfl, -⟩ := hP1
  obtain ⟨env₁, cvTa⟩ := q1
  have hF₁p : checkDirectInd (fueledOps mode F₁) env p = .ok (env₁, cvTa) := by
    rw [← checkDirectInd_datF]; exact hF₁
  obtain ⟨henv₁, hTf⟩ := direct_ind_wf henv hF₁p
  -- stage 2: the constructor
  obtain ⟨u1, sB, hfl1, h⟩ := bindI_ok h
  rw [flushS_run] at hfl1
  injection hfl1 with hfl1
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl1
  rw [checkDirectCtorF_push] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨q2, s₂, hct, h⟩ := bindI_ok h
  obtain ⟨hs₂, hext₂, q2', hP2, F₂, hF₂⟩ :=
    (checkDirectCtorS_sim henv₁ hTf (flushS_isok
      (hs₁.residue (tierOffE hext₁ hwf.wf.tier_off)))) q2 s₂ hct
  obtain ⟨rfl, -⟩ := hP2
  obtain ⟨env₂, cvCa⟩ := q2
  have hF₂p : checkDirectCtor (fueledOps mode F₂) env env₁ p cvTa
      = .ok (env₂, cvCa) := by rw [← checkDirectCtor_datF]; exact hF₂
  obtain ⟨henv₂, hCf, -⟩ := direct_ctor_wf henv₁ hF₂p
  -- stage 3: the recursor's constant and type
  obtain ⟨u2, sC, hfl2, h⟩ := bindI_ok h
  rw [flushS_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : s₂.flushed = sC := congrArg Prod.snd hfl2
  rw [checkConstantValF_eq] at h
  obtain ⟨cvRa, s₃, hcv, h⟩ := bindI_ok h
  obtain ⟨hs₃, hext₃, cvRa', hP3, F₃, hF₃⟩ :=
    (checkConstantValS_sim henv₂ (flushS_isok
      (hs₂.residue (tierOffE (hext₁.trans hext₂) hwf.wf.tier_off)))) cvRa s₃ hcv
  obtain ⟨rfl, -⟩ := hP3
  have hF₃p : checkConstantVal (fueledOps mode F₃) env₂ p.cvR = .ok cvRa := by
    rw [← checkConstantVal_datF]; exact hF₃
  obtain ⟨hRf, -, -, -⟩ := checkConstantVal_typeWF hF₃p
  rw [checkDirectRecTyF_eq] at h
  obtain ⟨u3, s₄, hrt, h⟩ := bindI_ok h
  obtain ⟨hs₄, hext₄, u3', hP4, F₄, hF₄⟩ :=
    (checkDirectRecTyS_sim henv₂ hCf hRf hs₃) u3 s₄ hrt
  have hF₄p : checkDirectRecTy (fueledOps mode F₄) env₂ p cvTa cvCa cvRa
      = .ok u3' := by rw [← checkDirectRecTy_datF]; exact hF₄
  -- stage 4: the rule
  rw [checkDirectRuleF_eq] at h
  obtain ⟨rhsA, s₅, hru, h⟩ := bindI_ok h
  obtain ⟨hs₅, hext₅, rhsA', hP5, F₅, hF₅⟩ :=
    (checkDirectRuleS_sim henv₂ hCf hRf hs₄) rhsA s₅ hru
  obtain rfl : rhsA = rhsA' := hP5
  have hF₅p : checkDirectRule (fueledOps mode F₅) env₂ p cvCa cvRa = .ok rhsA := by
    rw [← checkDirectRule_datF]; exact hF₅
  have henv₃ := direct_rec_wf henv₂ hF₃p hF₅p
  -- the projection phase
  rw [push_mkFEnv] at h
  simp only [mkFEnv_find?] at h
  by_cases hguard : (List.range p.nF).all (fun j =>
      (Env.find? ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
            .plain else .inert, rhsA⟩] :: env₂.consts⟩
        (projFnName p.cvT.name j)).isNone) = true
  case neg =>
    rw [if_neg hguard] at h
    exact absurd h throwI_bind_ok
  rw [if_pos hguard] at h
  obtain ⟨hwfO, hextO, hfeO, henvO, F₆, hF₆⟩ :=
    checkDirectProjsS_run (T := p.cvT.name) (C := p.cvC.name)
      (lps := p.cvT.levelParams) (nP := p.nP) (nF := p.nF)
      (cvTa := cvTa) (cvCa := cvCa) hCf p.nF 0 _ _ henv₃
      (hs₅.residue (tierOffE (hext₁.trans (hext₂.trans (hext₃.trans
        (hext₄.trans hext₅)))) hwf.wf.tier_off)) rfl h
  obtain ⟨G, hle₁, hle₂, hle₃, hle₄, hle₅, hle₆⟩ :
      ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G ∧ F₄ ≤ G ∧ F₅ ≤ G ∧ F₆ ≤ G :=
    ⟨max F₁ (max F₂ (max F₃ (max F₄ (max F₅ F₆)))),
      by omega, by omega, by omega, by omega, by omega, by omega⟩
  refine ⟨hwfO, hext₁.trans (hext₂.trans (hext₃.trans (hext₄.trans
    (hext₅.trans hextO)))), hfeO, G, ?_⟩
  have g₁ : checkDirectInd (fueledOps mode G) env p = .ok (env₁, cvTa) := by
    rw [← checkDirectInd_datF]; exact FueledM.up hle₁ hF₁
  have g₂ : checkDirectCtor (fueledOps mode G) env env₁ p cvTa
      = .ok (env₂, cvCa) := by
    rw [← checkDirectCtor_datF]; exact FueledM.up hle₂ hF₂
  have g₃ : checkConstantVal (fueledOps mode G) env₂ p.cvR = .ok cvRa := by
    rw [← checkConstantVal_datF]; exact FueledM.up hle₃ hF₃
  have g₄ : checkDirectRecTy (fueledOps mode G) env₂ p cvTa cvCa cvRa = .ok u3' := by
    rw [← checkDirectRecTy_datF]; exact FueledM.up hle₄ hF₄
  have g₅ : checkDirectRule (fueledOps mode G) env₂ p cvCa cvRa = .ok rhsA := by
    rw [← checkDirectRule_datF]; exact FueledM.up hle₅ hF₅
  have g₆ : (List.range p.nF).foldlM
      (checkDirectProj (fueledOps mode G) p.cvT.name p.cvC.name
        p.cvT.levelParams p.nP p.nF cvTa cvCa)
      ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
            .plain else .inert, rhsA⟩] :: env₂.consts⟩ = .ok feOut.env := by
    have := FueledM.up hle₆ hF₆
    rw [foldlM_atF] at this
    rw [List.range_eq_range']
    simpa only [checkDirectProj_datF] using this
  simp only [checkDirectStruct, Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind]
  rw [g₂]
  simp only [Except.bind]
  rw [g₃]
  simp only [Except.bind]
  rw [g₄]
  simp only [Except.bind]
  rw [g₅]
  simp only [Except.bind]
  rw [if_pos hguard]
  exact g₆

/-! ## `checkIndDecl` and the final bridge -/

set_option maxHeartbeats 1600000 in
/-- The inductive block at the shared driver is reproduced by the
pure fueled `checkIndDecl`. -/
theorem checkIndDeclSF_run {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {s₀ : IState} (hwf : ISOKF s₀)
    {feOut : FEnv} {s' : IState}
    (h : checkIndDeclSF mode (mkFEnv env) block s₀ = .ok (feOut, s')) :
    ISOKF s' ∧ Ext s₀.store s'.store ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkIndDecl mode (fueledOps mode F) env block = .ok feOut.env := by
  unfold checkIndDeclSF at h
  have hbnAll : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => true | _ => false),
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have : ci.name ∈ block.map (·.name) :=
      List.mem_map_of_mem (List.mem_filter.mp hci).1
    simpa using this
  split at h
  case isFalse hsplit =>
    exact absurd h throwI_bind_ok
  case isTrue hsplit =>
  split at h
  case _ cvT c0 cvC nP nF heq1 heq2 =>
    obtain ⟨caps, s₁, hcaps, h⟩ := bindI_ok h
    obtain ⟨hcapsv, rfl⟩ := pureI_ok hcaps
    have hcapsv' : indBlockCaps mode env cvT cvC nP nF = caps := by
      rw [← indBlockCapsF_eq]; exact hcapsv
    obtain ⟨fe₂, s₂, hfold, h⟩ := bindI_ok h
    obtain ⟨hwf₂, hext₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run _ env henv hwf hfold
    obtain ⟨fe₃, s₃, hrecs, h⟩ := bindI_ok h
    rw [hfe₂] at hrecs
    obtain ⟨hwf₃, hext₃, hfe₃, henv₃, F₂, hF₂⟩ :=
      checkIndRecsS_run henv₂ hbnAll hwf₂ hrecs
    rw [hfe₃] at h
    simp only [mkFEnv_find?] at h
    rw [ctorResidualOkF_eq] at h
    by_cases hctorRes : ctorResidualOk mode fe₃.env cvT.name cvC.name
        cvT.levelParams nP nF caps.eta = true
    case neg =>
      rw [if_neg hctorRes] at h
      exact absurd h throwI_bind_ok
    rw [if_pos hctorRes] at h
    by_cases hguard : (List.range nF).all
        (fun j => (fe₃.env.find? (projFnName cvT.name j)).isNone) = true
    case neg =>
      rw [if_neg hguard] at h
      exact absurd h throwI_bind_ok
    rw [if_pos hguard] at h
    obtain ⟨fe₄, s₄, hart, h⟩ := bindI_ok h
    obtain ⟨hwf₄, hext₄, hfe₄, henv₄, F₃, hF₃⟩ :=
      foldProjFnS_run _ fe₃.env henv₃ hwf₃ hart
    rw [hfe₄] at h
    obtain ⟨hs4', hfeOut, F₄, hF₄⟩ := foldProjTemplatesS_run _ fe₄.env h
    refine ⟨hs4' ▸ hwf₄,
      hs4' ▸ (hext₂.trans (hext₃.trans hext₄)), hfeOut,
      max F₁ (max F₂ (max F₃ F₄)), ?_⟩
    have hF₁p := FueledM.up (Nat.le_max_left F₁ (max F₂ (max F₃ F₄))) hF₁
    rw [foldlM_atF] at hF₁p
    simp only [checkIndMember_datF] at hF₁p
    have hF₂p := FueledM.up (Nat.le_trans (Nat.le_max_left F₂ (max F₃ F₄))
      (Nat.le_max_right F₁ (max F₂ (max F₃ F₄)))) hF₂
    rw [checkIndRecs_datF] at hF₂p
    have hF₃p := FueledM.up (Nat.le_trans (Nat.le_max_left F₃ F₄)
      (Nat.le_trans (Nat.le_max_right F₂ (max F₃ F₄))
        (Nat.le_max_right F₁ (max F₂ (max F₃ F₄))))) hF₃
    rw [foldlM_atF] at hF₃p
    simp only [installProjFnStep_datF] at hF₃p
    have hF₄p := FueledM.up (Nat.le_trans (Nat.le_max_right F₃ F₄)
      (Nat.le_trans (Nat.le_max_right F₂ (max F₃ F₄))
        (Nat.le_max_right F₁ (max F₂ (max F₃ F₄))))) hF₄
    rw [foldlM_atF] at hF₄p
    simp only [installProjTemplateStep_datF] at hF₄p
    have hF₁p' : List.foldlM (checkIndMember
        (fueledOps mode (max F₁ (max F₂ (max F₃ F₄))))
        (block.map (·.name)) caps) env _ = .ok fe₂.env := hF₁p
    have hF₃p' : List.foldlM (installProjFnStep mode
        (fueledOps mode (max F₁ (max F₂ (max F₃ F₄))))
        cvT.name cvC.name cvT.levelParams nP nF) fe₃.env _ =
        .ok fe₄.env := hF₃p
    have hF₄p' : List.foldlM (installProjTemplateStep cvT.name cvC.name
        cvT.levelParams nP nF : Env → Nat → CheckM Env) fe₄.env _ =
        .ok feOut.env := hF₄p
    simp only [checkIndDecl]
    split
    case isFalse hgs => exact absurd hsplit hgs
    case isTrue hgs =>
    split
    next cvT' c0' cvC' nP' nF' heq1' heq2' =>
      have h12 : ([(.indInfo cvT c0 : ConstantInfo)]) =
          [(.indInfo cvT' c0' : ConstantInfo)] :=
        heq1.symm.trans heq1'
      have h34 : ([(.ctorInfo cvC nP nF : ConstantInfo)]) =
          [(.ctorInfo cvC' nP' nF' : ConstantInfo)] :=
        heq2.symm.trans heq2'
      simp only [List.cons.injEq, and_true,
        ConstantInfo.indInfo.injEq, ConstantInfo.ctorInfo.injEq]
        at h12 h34
      obtain ⟨rfl, rfl⟩ := h12
      obtain ⟨rfl, rfl, rfl⟩ := h34
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      rw [hcapsv']
      split
      next err herr => exact nomatch (hF₁p'.symm.trans herr)
      next v hok =>
      obtain rfl : fe₂.env = v := by
        have hv : (Except.ok fe₂.env : Except CheckError Env) = .ok v :=
          hF₁p'.symm.trans hok
        injection hv
      split
      next err herr => exact nomatch (hF₂p.symm.trans herr)
      next v hok =>
      obtain rfl : fe₃.env = v := by
        have hv : (Except.ok fe₃.env : Except CheckError Env) = .ok v :=
          hF₂p.symm.trans hok
        injection hv
      rw [if_pos hctorRes, if_pos hguard]
      split
      next err herr => exact nomatch (hF₃p'.symm.trans herr)
      next v hok =>
      obtain rfl : fe₄.env = v := by
        have hv : (Except.ok fe₄.env : Except CheckError Env) = .ok v :=
          hF₃p'.symm.trans hok
        injection hv
      exact hF₄p'
    next x1 x2 hne' =>
      exact (hne' cvT c0 cvC nP nF heq1 heq2).elim
  case _ =>
    rename_i x1 x2 hne
    obtain ⟨fe₂, s₂, hfold, h⟩ := bindI_ok h
    obtain ⟨hwf₂, hext₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run _ env henv hwf hfold
    rw [hfe₂] at h
    obtain ⟨hwf₃, hext₃, hfe₃, henv₃, F₂, hF₂⟩ :=
      checkIndRecsS_run henv₂ hbnAll hwf₂ h
    refine ⟨hwf₃, hext₂.trans hext₃, hfe₃, max F₁ F₂, ?_⟩
    have hF₁p := FueledM.up (Nat.le_max_left F₁ F₂) hF₁
    rw [foldlM_atF] at hF₁p
    simp only [checkIndMember_datF] at hF₁p
    have hF₂p := FueledM.up (Nat.le_max_right F₁ F₂) hF₂
    rw [checkIndRecs_datF] at hF₂p
    have hF₁p' : List.foldlM (checkIndMember (fueledOps mode (max F₁ F₂))
        (block.map (·.name)) {}) env _ = .ok fe₂.env := hF₁p
    simp only [checkIndDecl]
    split
    case isFalse hgs => exact absurd hsplit hgs
    case isTrue hgs =>
    split
    next cvT' c0' cvC' nP' nF' heq1' heq2' =>
      exact (hne cvT' c0' cvC' nP' nF' heq1' heq2').elim
    next y1 y2 hne' =>
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      split
      next err herr => exact nomatch (hF₁p'.symm.trans herr)
      next v hok =>
      obtain rfl : fe₂.env = v := by
        have hv : (Except.ok fe₂.env : Except CheckError Env) = .ok v :=
          hF₁p'.symm.trans hok
        injection hv
      exact hF₂p

/-- The inductive-block dispatch of the shared driver (task #82): a
recognised artifact-free simple structure goes to `checkDirectStructS`,
everything else to `checkIndDeclSF`, and either way the pure fueled
`checkDecl` reproduces the run. -/
theorem checkIndOrDirectSF_run {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {s₀ : IState} (hwf : ISOKF s₀)
    {feOut : FEnv} {s' : IState}
    (h : (match directPartsF? (mkFEnv env) block with
          | some p => checkDirectStructS mode (mkFEnv env) p
          | none => checkIndDeclSF mode (mkFEnv env) block) s₀ =
      .ok (feOut, s')) :
    ISOKF s' ∧ Ext s₀.store s'.store ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) env (.indDecl block) = .ok feOut.env := by
  rw [directPartsF?_eq] at h
  show ISOKF s' ∧ Ext s₀.store s'.store ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (match directParts? env block with
      | some p => checkDirectStruct (fueledOps mode F) env p
      | none => checkIndDecl mode (fueledOps mode F) env block) = .ok feOut.env
  cases hdp : directParts? env block with
  | none =>
    rw [hdp] at h
    obtain ⟨hres, hext, hfe, F, hF⟩ := checkIndDeclSF_run henv hwf h
    exact ⟨hres, hext, hfe, F, hF⟩
  | some p =>
    rw [hdp] at h
    obtain ⟨hres, hext, hfe, F, hF⟩ := checkDirectStructS_run henv hwf h
    exact ⟨hres, hext, hfe, F, hF⟩

/-- The per-declaration bridge: a successful shared-state run over a
well-formed environment is reproduced by the pure fueled checker, and
the resulting index is `mkFEnv` of its environment (so the
cross-declaration fold threads `mkFEnv`-shaped indices). -/
theorem checkDeclSharedF_bridge {env : Env} {d : Declaration}
    {fe' : FEnv} (henv : EnvWF env)
    (h : checkDeclSharedF mode (mkFEnv env) d = .ok fe') :
    fe' = mkFEnv fe'.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) env d = .ok fe'.env := by
  unfold checkDeclSharedF at h
  simp only [StateT.run'] at h
  cases hrun : checkDeclSF mode (mkFEnv env) d ({} : IState) with
  | error e =>
    rw [hrun] at h
    simp only [Functor.map, Except.map] at h
    exact nomatch h
  | ok pr =>
    obtain ⟨feO, s'⟩ := pr
    rw [hrun] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have hwf0 : ISOKF ({} : IState) := ISOKF.fresh empty_wf
    cases d with
    | indDecl block =>
      obtain ⟨-, -, hfe, F, hF⟩ := checkIndOrDirectSF_run henv hwf0 hrun
      exact ⟨hfe, F, hF⟩
    | defnDecl cv value hint =>
      rw [checkDeclSF_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindI_ok hrun
      obtain ⟨hfe, rfl⟩ := pureI_ok hrun
      subst hfe
      obtain ⟨hs', hext, v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim henv (ISOK.fresh env hwf0.wf)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF
    | thmDecl cv value =>
      rw [checkDeclSF_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindI_ok hrun
      obtain ⟨hfe, rfl⟩ := pureI_ok hrun
      subst hfe
      obtain ⟨hs', hext, v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim henv (ISOK.fresh env hwf0.wf)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF
    | opaqueDecl cv value =>
      rw [checkDeclSF_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindI_ok hrun
      obtain ⟨hfe, rfl⟩ := pureI_ok hrun
      subst hfe
      obtain ⟨hs', hext, v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim henv (ISOK.fresh env hwf0.wf)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF
    | axiomDecl cv =>
      rw [checkDeclSF_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindI_ok hrun
      obtain ⟨hfe, rfl⟩ := pureI_ok hrun
      subst hfe
      obtain ⟨hs', hext, v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim henv (ISOK.fresh env hwf0.wf)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF
    | basisDecl kind =>
      rw [checkDeclSF_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindI_ok hrun
      obtain ⟨hfe, rfl⟩ := pureI_ok hrun
      subst hfe
      obtain ⟨hs', hext, v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim henv (ISOK.fresh env hwf0.wf)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF

end Setlec
