import Setlec.Verify.BridgeS4
import Setlec.Verify.BridgeWFDecl

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

/-! The direct-structure run's shared-state bridge
(`checkDirectProjsS_run`, `checkDirectStructS_run`) lived here and is
**deleted**: `directStructsEnabled = false` makes the arm that called
it unreachable, and `directParts?_none` collapses that arm at one
`rw`.  Deleting it is what removes this file's last dependence on
`Setlec/Model/*` and lets it serve both soundness routes
(task #148 T6). -/

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
  -- task #148 T6: the direct arm is unreachable
  -- (`directStructsEnabled = false`); collapsing it is what lets this
  -- file live in the shared tier.
  rw [directParts?_none] at h ⊢
  obtain ⟨hres, hext, hfe, F, hF⟩ := checkIndDeclSF_run henv hwf h
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
