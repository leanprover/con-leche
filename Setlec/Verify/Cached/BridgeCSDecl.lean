import Setlec.Verify.Cached.BridgeCS4

/-!
# Cached shared-state checker: the inductive block and the per-declaration bridge

Port of `Setlec/Verify/BridgeSDecl.lean` for the cached tier.  The tail
of the per-declaration composition whose bulk is
`Setlec/Verify/Cached/BridgeCS4.lean`: the inductive-block driver
(`checkIndDeclSF_run`), its dispatch (`checkIndOrDirectSF_run`), and the
per-declaration bridge (`checkDeclSharedF_bridge`).

As in the interned original the *direct simple-structure* run has no
bridge here: `directStructsEnabled = false` makes the arm that would
call it unreachable and `directParts?_none` collapses it at one `rw`.

Against `BridgeSDecl` the systematic deletions of the tier carry
through: no arena, hence no `Ext` conjunct anywhere and no
`tierOffE`/tier-flag side condition; `ISOKF` becomes `CSOKF`, whose
`residue` needs no flag witness; the fresh state is `CSOK.empty` rather
than `ISOK.fresh`.  Every pure comparand is byte-identical to the
interned original's.

One piece the interned tier keeps in a *shared* file has to be
replicated here: `checkDeclSF_nonind` (`Setlec/Verify/CheckerF.lean`)
is stated for `CheckIM`, because the `throw`/`ite` peels it uses are
monad-specific (`rfl` at a concrete `StateT`).  Its `CheckCM` twin —
`checkDeclSFC_nonind`, with the `_push` lemmas it consumes — is proved
below; the pure comparand (`checkDecl` at `sharedOpsC`) is the same
program.  These are the only additions: everything else in the file is
the transposition.
-/

set_option linter.unusedSimpArgs false

namespace Setlec.Cached

open Setlec

variable {mode : CheckMode}

/-! ## `CheckCM` peels (the `CheckIM` helpers of
`Setlec/Verify/CheckerF.lean` at the cached monad) -/

theorem throwC_bind_eq {α β : Type} (e : CheckError)
    (f : α → CheckCM β) : ((throw e : CheckCM α) >>= f) = throw e := rfl

theorem bindC_congr {α β : Type} {x : CheckCM α} {f g : α → CheckCM β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  rw [funext h]

theorem ite_bindC {α β : Type} (c : Prop) [Decidable c]
    (a b : CheckCM α) (f : α → CheckCM β) :
    ((if c then a else b) >>= f)
      = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem checkDefnValF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint) :
    checkDefnValF ops (mkFEnv env) cv value hint
      = checkDefnVal ops env cv value hint
          >>= fun e => pure (mkFEnv e) := by
  unfold checkDefnValF checkDefnVal
  simp only [constsResolveF_eq, mkFEnv_env, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

theorem checkThmValF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (cv : ConstantVal) (value : Expr) :
    checkThmValF ops (mkFEnv env) cv value
      = checkThmVal ops env cv value >>= fun e => pure (mkFEnv e) := by
  unfold checkThmValF checkThmVal
  simp only [constsResolveF_eq, mkFEnv_env, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

theorem checkOpaqueValF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (cv : ConstantVal) (value : Expr) :
    checkOpaqueValF ops (mkFEnv env) cv value
      = checkOpaqueVal ops env cv value >>= fun e => pure (mkFEnv e) := by
  unfold checkOpaqueValF checkOpaqueVal
  simp only [constsResolveF_eq, mkFEnv_env, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

theorem installBasisDeclF_pushC (env : Env) (ci : ConstantInfo) :
    (installBasisDeclF (mkFEnv env) ci : CheckCM FEnv)
      = installBasisDecl env ci >>= fun e => pure (mkFEnv e) := by
  unfold installBasisDeclF installBasisDecl
  simp only [mkFEnv_find?, push_mkFEnv, pure_bind, ite_bindC,
    throwC_bind_eq] <;> rfl

theorem installBasisFoldF_pushC :
    ∀ (l : List ConstantInfo) (env : Env),
      (l.foldlM installBasisDeclF (mkFEnv env) : CheckCM FEnv)
        = l.foldlM installBasisDecl env >>= fun e => pure (mkFEnv e)
  | [], env => by
    simp only [List.foldlM_nil, pure_bind]
  | ci :: l, env => by
    rw [List.foldlM_cons, List.foldlM_cons, installBasisDeclF_pushC,
      bind_assoc, bind_assoc]
    refine bindC_congr fun e => ?_
    rw [pure_bind, installBasisFoldF_pushC l e]

/-- The non-inductive branches of the cached `checkDeclSF` are the
generic `checkDecl` (at the cached shared operations) followed by
`mkFEnv` — the `CheckCM` twin of `checkDeclSF_nonind`. -/
theorem checkDeclSFC_nonind (env : Env) (d : Declaration)
    (hnotind : ∀ block, d ≠ .indDecl block) :
    checkDeclSF mode (mkFEnv env) d
      = checkDecl mode (sharedOpsC mode (mkFEnv env)) env d
          >>= fun e => pure (mkFEnv e) := by
  cases d with
  | indDecl block => exact absurd rfl (hnotind block)
  | defnDecl cv value hint =>
    show (do
        let cv ← checkConstantValF (sharedOpsC mode (mkFEnv env))
          (mkFEnv env) cv
        if natOpNames.contains cv.name ||
            natDivModNames.contains cv.name then
          let fe2 ← checkDefnValF (sharedOpsC mode (mkFEnv env)) (mkFEnv env)
            cv value hint
          if natOpNames.contains cv.name then
            unless natOpGuardF fe2 cv.name &&
                (natOpDeps cv.name).all (natOpStoredOkF fe2) do
              throw (.notImplemented
                s!"nonstandard structural Nat operation environment ({cv.name})")
            match fe2.find? cv.name with
            | some (.defnInfo _ value' _) =>
              let ok ← certifyNatEqs (sharedOpsC mode (mkFEnv env))
                (mkFEnv env).env
                ((natOpEquations 0 cv.name).map fun eq =>
                  (Expr.substConst0 cv.name value' eq.1,
                   Expr.substConst0 cv.name value' eq.2))
              unless ok do
                throw (.notImplemented
                  s!"nonstandard structural Nat operation ({cv.name})")
            | _ => throw (.internal
                s!"structural Nat operation not stored ({cv.name})")
          if natDivModNames.contains cv.name then
            checkDivModPinF (sharedOpsC mode (mkFEnv env)) (mkFEnv env) fe2
              cv.name
          pure fe2
        else
          checkDefnValF (sharedOpsC mode (mkFEnv env)) (mkFEnv env)
            cv value hint : CheckCM FEnv) = _
    unfold checkDecl
    simp only [checkConstantValF_eq, mkFEnv_env, bind_assoc]
    refine bindC_congr fun cvA => ?_
    by_cases hb : (natOpNames.contains cvA.name ||
        natDivModNames.contains cvA.name) = true
    case neg =>
      obtain ⟨h1, h4⟩ : ¬(natOpNames.contains cvA.name = true) ∧
          ¬(natDivModNames.contains cvA.name = true) := by
        simpa [not_or] using hb
      rw [if_neg hb, checkDefnValF_pushC]
      simp only [if_neg h1, if_neg h4, pure_bind]
    simp only [if_pos hb]
    rw [checkDefnValF_pushC]
    simp only [bind_assoc, pure_bind]
    refine bindC_congr fun env2 => ?_
    simp only [natOpGuardF_eq, natOpStoredOkF_eq_fun, mkFEnv_find?,
      checkDivModPinF_eq, bind_assoc, pure_bind,
      ite_bindC, throwC_bind_eq]
    by_cases hnat : natOpNames.contains cvA.name = true
    case neg => simp only [if_neg hnat] <;> rfl
    simp only [if_pos hnat]
    by_cases hg : (natOpGuard env2 cvA.name &&
        (natOpDeps cvA.name).all (natOpStoredOk env2)) = true
    case neg => simp only [if_neg hg] <;> rfl
    simp only [if_pos hg]
    cases env2.find? cvA.name with
    | none => rfl
    | some ci =>
      cases ci <;>
        simp only [bind_assoc, pure_bind, ite_bindC, throwC_bind_eq] <;>
        rfl
  | thmDecl cv value =>
    show (do
        let cv ← checkConstantValF (sharedOpsC mode (mkFEnv env))
          (mkFEnv env) cv
        checkThmValF (sharedOpsC mode (mkFEnv env)) (mkFEnv env) cv value :
        CheckCM FEnv) = _
    unfold checkDecl
    simp only [checkConstantValF_eq, checkThmValF_pushC, bind_assoc]
  | opaqueDecl cv value =>
    show (do
        let cv ← checkConstantValF (sharedOpsC mode (mkFEnv env))
          (mkFEnv env) cv
        let fe2 ← checkOpaqueValF (sharedOpsC mode (mkFEnv env))
          (mkFEnv env) cv value
        if reduceOpNames.contains cv.name then
          checkReducePinF (sharedOpsC mode (mkFEnv env)) (mkFEnv env) fe2
            cv.name value
        pure fe2 : CheckCM FEnv) = _
    unfold checkDecl
    simp only [checkConstantValF_eq, bind_assoc]
    refine bindC_congr fun cvA => ?_
    rw [checkOpaqueValF_pushC]
    simp only [checkReducePinF_eq, mkFEnv_env, bind_assoc, pure_bind,
      ite_bindC, throwC_bind_eq] <;> rfl
  | axiomDecl cv =>
    show (do
        let cvA ← checkConstantValF (sharedOpsC mode (mkFEnv env))
          (mkFEnv env) cv
        if stdAxiomOkF (mkFEnv env) cvA then
          pure ((mkFEnv env).push (.axiomInfo cvA))
        else if cvA.name = trustCompilerName then
          if trustCompilerOkF (mkFEnv env) cvA then
            pure ((mkFEnv env).push (.axiomInfo cvA))
          else throw (.notImplemented
            s!"unsupported Lean.trustCompiler shape ({cv.name})")
        else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
          if ofReduceAxOkF (mkFEnv env) cvA then
            pure ((mkFEnv env).push (.axiomInfo cvA))
          else throw (.notImplemented
            s!"unsupported compiler-trust axiom environment ({cv.name})")
        else if cvA.name = propextName ∨ cvA.name = choiceName then
          throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
        else if toleratedAxiomNames.contains cvA.name then
          pure (mkFEnv env)
        else
          throw (.notImplemented s!"non-standard axiom ({cv.name})") :
        CheckCM FEnv) = _
    unfold checkDecl
    simp only [checkConstantValF_eq, stdAxiomOkF_eq, trustCompilerOkF_eq,
      ofReduceAxOkF_eq, push_mkFEnv, bind_assoc, pure_bind, ite_bindC,
      throwC_bind_eq] <;> rfl
  | basisDecl kind =>
    show (do
        if kind = .quotK then
          unless (mkFEnv env).find? eqName = some eqA do
            throw (.notImplemented
              "quotient basis requires the pinned Eq basis")
        kind.declsA.foldlM installBasisDeclF (mkFEnv env) :
        CheckCM FEnv) = _
    unfold checkDecl
    simp only [mkFEnv_find?, installBasisFoldF_pushC, bind_assoc,
      pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-! ## `checkIndDecl` and the final bridge -/

/-! The direct-structure run's cached bridge (`checkDirectProjsS_run`,
`checkDirectStructS_run`) is **deleted** for the same reason as in the
interned original: `directStructsEnabled = false` makes the arm that
called it unreachable, and `directParts?_none` collapses that arm at
one `rw`. -/

/-- The inductive block at the cached driver is reproduced by the
pure fueled `checkIndDecl`. -/
theorem checkIndDeclSF_run {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkIndDeclSF mode (mkFEnv env) block s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
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
    exact absurd h throwC_bind_ok
  case isTrue hsplit =>
  split at h
  case _ cvT c0 cvC nP nF heq1 heq2 =>
    obtain ⟨caps, s₁, hcaps, h⟩ := bindC_ok h
    obtain ⟨hcapsv, rfl⟩ := pureC_ok hcaps
    have hcapsv' : indBlockCaps mode env cvT cvC nP nF = caps := by
      rw [← indBlockCapsF_eq]; exact hcapsv
    obtain ⟨fe₂, s₂, hfold, h⟩ := bindC_ok h
    obtain ⟨hwf₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run _ env henv hwf hfold
    obtain ⟨fe₃, s₃, hrecs, h⟩ := bindC_ok h
    rw [hfe₂] at hrecs
    obtain ⟨hwf₃, hfe₃, henv₃, F₂, hF₂⟩ :=
      checkIndRecsS_run henv₂ hbnAll hwf₂ hrecs
    rw [hfe₃] at h
    simp only [mkFEnv_find?] at h
    rw [ctorResidualOkF_eq] at h
    by_cases hctorRes : ctorResidualOk mode fe₃.env cvT.name cvC.name
        cvT.levelParams nP nF caps.eta = true
    case neg =>
      rw [if_neg hctorRes] at h
      exact absurd h throwC_bind_ok
    rw [if_pos hctorRes] at h
    by_cases hguard : (List.range nF).all
        (fun j => (fe₃.env.find? (projFnName cvT.name j)).isNone) = true
    case neg =>
      rw [if_neg hguard] at h
      exact absurd h throwC_bind_ok
    rw [if_pos hguard] at h
    obtain ⟨fe₄, s₄, hart, h⟩ := bindC_ok h
    obtain ⟨hwf₄, hfe₄, henv₄, F₃, hF₃⟩ :=
      foldProjFnS_run _ fe₃.env henv₃ hwf₃ hart
    rw [hfe₄] at h
    obtain ⟨hs4', hfeOut, F₄, hF₄⟩ := foldProjTemplatesS_run _ fe₄.env h
    refine ⟨hs4' ▸ hwf₄, hfeOut,
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
    obtain ⟨fe₂, s₂, hfold, h⟩ := bindC_ok h
    obtain ⟨hwf₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run _ env henv hwf hfold
    rw [hfe₂] at h
    obtain ⟨hwf₃, hfe₃, henv₃, F₂, hF₂⟩ :=
      checkIndRecsS_run henv₂ hbnAll hwf₂ h
    refine ⟨hwf₃, hfe₃, max F₁ F₂, ?_⟩
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

/-- The inductive-block dispatch of the cached driver: a recognised
artifact-free simple structure goes to `checkDirectStructS`, everything
else to `checkIndDeclSF`, and either way the pure fueled `checkDecl`
reproduces the run. -/
theorem checkIndOrDirectSF_run {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : (match directPartsF? (mkFEnv env) block with
          | some p => checkDirectStructS mode (mkFEnv env) p
          | none => checkIndDeclSF mode (mkFEnv env) block) s₀ =
      .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) env (.indDecl block) =
      .ok feOut.env := by
  rw [directPartsF?_eq] at h
  show CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (match directParts? env block with
      | some p => checkDirectStruct (fueledOps mode F) env p
      | none => checkIndDecl mode (fueledOps mode F) env block) = .ok feOut.env
  -- the direct arm is unreachable (`directStructsEnabled = false`)
  rw [directParts?_none] at h ⊢
  obtain ⟨hres, hfe, F, hF⟩ := checkIndDeclSF_run henv hwf h
  exact ⟨hres, hfe, F, hF⟩

/-- The per-declaration bridge: a successful cached shared-state run
over a well-formed environment is reproduced by the pure fueled
checker, and the resulting index is `mkFEnv` of its environment. -/
theorem checkDeclSharedF_bridge {env : Env} {d : Declaration}
    {fe' : FEnv} (henv : EnvWF env)
    (h : checkDeclSharedF mode (mkFEnv env) d = .ok fe') :
    fe' = mkFEnv fe'.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) env d = .ok fe'.env := by
  unfold checkDeclSharedF at h
  simp only [StateT.run'] at h
  cases hrun : checkDeclSF mode (mkFEnv env) d ({} : CState) with
  | error e =>
    rw [hrun] at h
    simp only [Functor.map, Except.map] at h
    exact nomatch h
  | ok pr =>
    obtain ⟨feO, s'⟩ := pr
    rw [hrun] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have hwf0 : CSOKF ({} : CState) := CSOKF.empty
    cases d with
    | indDecl block =>
      obtain ⟨-, hfe, F, hF⟩ := checkIndOrDirectSF_run henv hwf0 hrun
      exact ⟨hfe, F, hF⟩
    | defnDecl cv value hint =>
      rw [checkDeclSFC_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindC_ok hrun
      obtain ⟨hfe, rfl⟩ := pureC_ok hrun
      subst hfe
      obtain ⟨hs', v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim henv (CSOK.empty env)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF
    | thmDecl cv value =>
      rw [checkDeclSFC_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindC_ok hrun
      obtain ⟨hfe, rfl⟩ := pureC_ok hrun
      subst hfe
      obtain ⟨hs', v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim henv (CSOK.empty env)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF
    | opaqueDecl cv value =>
      rw [checkDeclSFC_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindC_ok hrun
      obtain ⟨hfe, rfl⟩ := pureC_ok hrun
      subst hfe
      obtain ⟨hs', v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim henv (CSOK.empty env)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF
    | axiomDecl cv =>
      rw [checkDeclSFC_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindC_ok hrun
      obtain ⟨hfe, rfl⟩ := pureC_ok hrun
      subst hfe
      obtain ⟨hs', v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim henv (CSOK.empty env)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF
    | basisDecl kind =>
      rw [checkDeclSFC_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindC_ok hrun
      obtain ⟨hfe, rfl⟩ := pureC_ok hrun
      subst hfe
      obtain ⟨hs', v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim henv (CSOK.empty env)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF

end Setlec.Cached
