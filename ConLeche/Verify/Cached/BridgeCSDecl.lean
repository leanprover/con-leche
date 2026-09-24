module

public import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.Inductives.StructWF

public section

/-!
# Cached shared-state checker: the inductive block and the per-declaration bridge

Port of `ConLeche/Verify/BridgeSDecl.lean` for the cached tier.  The tail
of the per-declaration composition whose bulk is
`ConLeche/Verify/Cached/BridgeCS4.lean`: the inductive-block driver
(`checkIndDeclSF_run`) and the per-declaration bridge
(`checkDeclSharedF_bridge`).  The `.indDecl` dispatch
(`checkModeledOrNativeSF_run`) is in `ConLeche/Verify/Cached/TargetRecC.lean`,
beside the uniform route's k-ary run it dispatches to.

As in the interned original the *direct simple-structure* run has no
bridge here: `structsEnabled = false` makes the arm that would
call it unreachable and `structParts?_none` collapses it at one `rw`.

Against `BridgeSDecl` the systematic deletions of the tier carry
through: no arena, hence no `Ext` conjunct anywhere and no
`tierOffE`/tier-flag side condition; `ISOKF` becomes `CSOKF`, whose
`residue` needs no flag witness; the fresh state is `CSOK.empty` rather
than `ISOK.fresh`.  Every pure comparand is byte-identical to the
interned original's.

One piece the interned tier keeps in a *shared* file has to be
replicated here: `checkDeclSF_nonind` (`ConLeche/Verify/CheckerF.lean`)
is stated for `CheckIM`, because the `throw`/`ite` peels it uses are
monad-specific (`rfl` at a concrete `StateT`).  Its `CheckCM` twin —
`checkDeclSFC_nonind`, with the `_push` lemmas it consumes — is proved
below; the pure comparand (`checkDecl` at `sharedOpsC`) is the same
program.  These are the only additions: everything else in the file is
the transposition.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

theorem throwC_bind_eq {α β : Type} (e : CheckError)
    (f : α → CheckCM β) : ((throw e : CheckCM α) >>= f) = throw e := rfl


open ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## `CheckCM` peels (the `CheckIM` helpers of
`ConLeche/Verify/CheckerF.lean` at the cached monad) -/

theorem bindC_congr {α β : Type} {x : CheckCM α} {f g : α → CheckCM β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  rw [funext h]

theorem ite_bindC {α β : Type} (c : Prop) [Decidable c]
    (a b : CheckCM α) (f : α → CheckCM β) :
    ((if c then a else b) >>= f)
      = if c then a >>= f else b >>= f := by
  split <;> rfl

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

/-! ### The direct simple-structure path's extending stages (task #175
W4c: the cached run bridge restored) -/

/-- The former's telescope stage through the index (task #195): the
whnf loop reads the index's environment, the re-check is the indexed
`checkConstantValF`. -/
theorem checkSumTeleF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal) :
    checkSumTeleF ops (mkFEnv env) cv n cvTa₀
      = checkSumTele ops env cv n cvTa₀ := by
  unfold checkSumTeleF checkSumTele
  cases hst : cvTa₀.type.stripPis n with
  | none => simp only [checkConstantValF_eq, mkFEnv_env]
  | some q =>
    obtain ⟨bs, body⟩ := q
    cases body <;> simp only [checkConstantValF_eq, mkFEnv_env]

/-- The projection table through the index (task #175 S1). -/
theorem checkStructProjTableF_pushC (T C : Name) (lps : List Name)
    (nP nF : Nat) (rs : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal)
    (env : Env) :
    checkStructProjTableF (m := CheckCM) .plain T C lps nP nF rs guards off cvCa (mkFEnv env)
      = checkStructProjTable (m := CheckCM) T C lps nP nF rs guards off cvCa env
          >>= fun e => pure (mkFEnv e) := by
  unfold checkStructProjTableF checkStructProjTable
  simp only [StructWalkers.plain, constsResolveF_eq, mkFEnv_find?, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-! ## `checkModeled` and the final bridge -/

/-! ## The direct simple-structure install (task #82; the cached run
bridge restored at task #175 W4c, the direct install being the only
projection route) -/

/-- The projection-table stage of the cached driver, run-level (task
#175 S1): operation-free, the state is unchanged, the environment is
the pure stage's. -/
theorem checkStructProjTableS_run {T C : Name} {lps : List Name} {nP nF : Nat}
    {rs : Level} {guards : List Level} {off : Nat} {cvCa : ConstantVal}
    (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : checkStructProjTableF (m := CheckCM) .plain T C lps nP nF rs guards off cvCa
      (mkFEnv env) s₀ = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkStructProjTable T C lps nP nF rs guards off cvCa env : FueledM Env).val F
      = .ok fe'.env := by
  rw [checkStructProjTableF_pushC] at h
  obtain ⟨e₁, s₁, hstep, h⟩ := bindC_ok h
  obtain ⟨hfe, rfl⟩ := pureC_ok h
  subst hfe
  -- the pure stage in the cached monad: state unchanged, the value the
  -- `CheckM` instantiation's
  have hrun : s₀ = s₁ ∧ checkStructProjTable (m := CheckM) T C lps nP nF rs guards off cvCa env
      = .ok e₁ := by
    unfold checkStructProjTable at hstep ⊢
    cases hb : structProjBodies T nP nF cvCa.type with
    | none =>
      try rw [hb] at hstep
      exact absurd hstep throwC_bind_ok
    | some bodies =>
      try rw [hb] at hstep
      simp only [unwrapOr, pure_bind] at hstep ⊢
      split at hstep
      · next hg =>
        rw [if_pos hg]
        split at hstep
        · next hfam =>
          rw [if_pos hfam]
          split at hstep
          · next hn =>
            rw [if_pos hn]
            obtain ⟨hfe, rfl⟩ := pureC_ok hstep
            subst hfe
            exact ⟨rfl, rfl⟩
          · exact absurd hstep throwC_bind_ok
        · exact absurd hstep throwC_bind_ok
      · exact absurd hstep throwC_bind_ok
  obtain ⟨rfl, hpure⟩ := hrun
  refine ⟨hwf, rfl, direct_table_wf henv hpure, 0, ?_⟩
  rw [checkStructProjTable_datF]
  exact hpure

set_option maxHeartbeats 1600000 in

/-- The inductive block at the cached driver is reproduced by the
pure fueled `checkModeled`. -/
theorem checkIndDeclSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {nPd : Nat} {block : List ConstantInfo} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkIndDeclSF mode (mkFEnv env) nPd block s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkModeled mode (fueledOps mode F) env nPd block = .ok feOut.env := by
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
    -- the block's capability pins at its (single) inductive member:
    -- the member IS the former the record was computed for
    obtain ⟨hwf₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run hμ _ env henv hwf (by
        intro ci hci cv caps₀ hceq
        have hmemI : ci ∈ [ConstantInfo.indInfo cvT c0] := by
          rw [← heq1]
          exact List.mem_filter.mpr ⟨(List.mem_filter.mp hci).1, by subst hceq; rfl⟩
        obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj
          (hceq ▸ List.mem_singleton.mp hmemI)
        rw [← hcapsv']
        exact ConLeche.etaPins_of_indBlockCaps) hfold
    obtain ⟨fe₃, s₃, hrecs, h⟩ := bindC_ok h
    rw [hfe₂] at hrecs
    obtain ⟨hwf₃, hfe₃, henv₃, F₂, hF₂⟩ :=
      checkIndRecsS_run hμ henv₂ hbnAll hwf₂ hrecs
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
    -- the projection phase: structure-like blocks only (task #175
    -- SigmaHom); off the shape the phase is the identity
    by_cases hsl : ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF
        = true
    case neg =>
      rw [if_neg hsl] at h
      obtain ⟨hfe₄, rfl⟩ := pureC_ok h
      subst hfe₄
      refine ⟨hwf₃, rfl, max F₁ F₂, ?_⟩
      have hF₁p := FueledM.up (Nat.le_max_left F₁ F₂) hF₁
      rw [foldlM_atF] at hF₁p
      simp only [checkIndMember_datF] at hF₁p
      have hF₂p := FueledM.up (Nat.le_max_right F₁ F₂) hF₂
      rw [checkIndRecs_datF] at hF₂p
      have hF₁p' : List.foldlM (checkIndMember (fueledOps mode (max F₁ F₂))
          (block.map (·.name)) caps) env _ = .ok fe₂.env := hF₁p
      simp only [checkModeled]
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
        rw [if_pos hctorRes, if_pos hguard, if_neg hsl]
        rfl
      next x1 x2 hne' =>
        exact (hne' cvT c0 cvC nP nF heq1 heq2).elim
    rw [if_pos hsl] at h
    obtain ⟨hwf₄, hfe₄, henv₄, F₃, hF₃⟩ :=
      foldProjFnS_run hμ _ fe₃.env henv₃ hwf₃ h
    refine ⟨hwf₄, hfe₄, max F₁ (max F₂ F₃), ?_⟩
    have hF₁p := FueledM.up (Nat.le_max_left F₁ (max F₂ F₃)) hF₁
    rw [foldlM_atF] at hF₁p
    simp only [checkIndMember_datF] at hF₁p
    have hF₂p := FueledM.up (Nat.le_trans (Nat.le_max_left F₂ F₃)
      (Nat.le_max_right F₁ (max F₂ F₃))) hF₂
    rw [checkIndRecs_datF] at hF₂p
    have hF₃p := FueledM.up (Nat.le_trans (Nat.le_max_right F₂ F₃)
      (Nat.le_max_right F₁ (max F₂ F₃))) hF₃
    rw [foldlM_atF] at hF₃p
    simp only [installProjFnStep_datF] at hF₃p
    have hF₁p' : List.foldlM (checkIndMember
        (fueledOps mode (max F₁ (max F₂ F₃)))
        (block.map (·.name)) caps) env _ = .ok fe₂.env := hF₁p
    have hF₃p' : List.foldlM (installProjFnStep mode
        (fueledOps mode (max F₁ (max F₂ F₃)))
        cvT.name cvC.name cvT.levelParams nP nF) fe₃.env _ =
        .ok feOut.env := hF₃p
    simp only [checkModeled]
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
      rw [if_pos hctorRes, if_pos hguard, if_pos hsl]
      exact hF₃p'
    next x1 x2 hne' =>
      exact (hne' cvT c0 cvC nP nF heq1 heq2).elim
  case _ =>
    rename_i x1 x2 hne
    obtain ⟨fe₂, s₂, hfold, h⟩ := bindC_ok h
    obtain ⟨hwf₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run hμ _ env henv hwf
        (fun _ _ _ _ _ => ⟨(fun h => absurd h Bool.false_ne_true),
          (fun h => absurd h Bool.false_ne_true)⟩) hfold
    rw [hfe₂] at h
    obtain ⟨hwf₃, hfe₃, henv₃, F₂, hF₂⟩ :=
      checkIndRecsS_run hμ henv₂ hbnAll hwf₂ h
    refine ⟨hwf₃, hfe₃, max F₁ F₂, ?_⟩
    have hF₁p := FueledM.up (Nat.le_max_left F₁ F₂) hF₁
    rw [foldlM_atF] at hF₁p
    simp only [checkIndMember_datF] at hF₁p
    have hF₂p := FueledM.up (Nat.le_max_right F₁ F₂) hF₂
    rw [checkIndRecs_datF] at hF₂p
    have hF₁p' : List.foldlM (checkIndMember (fueledOps mode (max F₁ F₂))
        (block.map (·.name)) { nparams := nPd }) env _ = .ok fe₂.env := hF₁p
    simp only [checkModeled]
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

end ConLeche.Cached
