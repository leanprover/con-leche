import Setlec.Verify.Cached.BridgeCS4
import Setlec.Verify.Direct.DirectWF
import Setlec.Verify.Direct.DirectResid
import Setlec.Verify.Direct.SumWF

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

/-! ### The direct simple-structure path's extending stages (task #175
W4c: the cached run bridge restored) -/

theorem checkDirectIndF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (p : DirectParts) :
    checkDirectIndF ops (mkFEnv env) p
      = checkDirectInd ops env p
          >>= fun q => pure (mkFEnv q.1, q.2) := by
  unfold checkDirectIndF checkDirectInd
  simp only [checkConstantValF_eq, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-- The direct sum's type-former stage through the index (task #175
sum-types). -/
theorem checkDirectSumIndF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (p : DirectSumParts) :
    checkDirectSumIndF ops (mkFEnv env) p
      = checkDirectSumInd ops env p
          >>= fun q => pure (mkFEnv q.1, q.2) := by
  unfold checkDirectSumIndF checkDirectSumInd
  simp only [checkConstantValF_eq, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

theorem checkDirectCtorF_pushC (ops : CheckerOps CheckCM) (env₀ env : Env)
    (p : DirectParts) (cvTa : ConstantVal) :
    checkDirectCtorF ops (mkFEnv env₀) (mkFEnv env) p cvTa
      = checkDirectCtor ops env₀ env p cvTa
          >>= fun q => pure (mkFEnv q.1, q.2) := by
  unfold checkDirectCtorF checkDirectCtor
  simp only [checkConstantValF_eq, checkDirectDomsAtFA_eq,
    checkDirectDomsAtF_eq, openPisAtFvarsF_eq, checkDirectFieldSortsFA_eq,
    checkDirectFieldSortsF_eq, constsResolveF_eq, mkFEnv_env, push_mkFEnv,
    bind_assoc, pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-- The projection table through the index (task #175 S1). -/
theorem checkDirectProjTableF_pushC (T C : Name) (lps : List Name)
    (nP nF : Nat) (rs : Level) (guards : List Level) (cvCa : ConstantVal)
    (env : Env) :
    checkDirectProjTableF (m := CheckCM) T C lps nP nF rs guards cvCa (mkFEnv env)
      = checkDirectProjTable (m := CheckCM) T C lps nP nF rs guards cvCa env
          >>= fun e => pure (mkFEnv e) := by
  unfold checkDirectProjTableF checkDirectProjTable
  simp only [constsResolveF_eq, mkFEnv_find?, push_mkFEnv, bind_assoc, pure_bind,
    ite_bindC, throwC_bind_eq] <;> rfl

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

/-! ## The direct simple-structure install (task #82; the cached run
bridge restored at task #175 W4c, the direct install being the only
projection route) -/

/-- The projection-table stage of the cached driver, run-level (task
#175 S1): operation-free, the state is unchanged, the environment is
the pure stage's. -/
theorem checkDirectProjTableS_run {T C : Name} {lps : List Name} {nP nF : Nat}
    {rs : Level} {guards : List Level} {cvCa : ConstantVal}
    (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : checkDirectProjTableF (m := CheckCM) T C lps nP nF rs guards cvCa
      (mkFEnv env) s₀ = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkDirectProjTable T C lps nP nF rs guards cvCa env : FueledM Env).val F
      = .ok fe'.env := by
  rw [checkDirectProjTableF_pushC] at h
  obtain ⟨e₁, s₁, hstep, h⟩ := bindC_ok h
  obtain ⟨hfe, rfl⟩ := pureC_ok h
  subst hfe
  -- the pure stage in the cached monad: state unchanged, the value the
  -- `CheckM` instantiation's
  have hrun : s₀ = s₁ ∧ checkDirectProjTable (m := CheckM) T C lps nP nF rs guards cvCa env
      = .ok e₁ := by
    unfold checkDirectProjTable at hstep ⊢
    cases hb : directProjBodies T nP nF cvCa.type with
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
  rw [checkDirectProjTable_datF]
  exact hpure

set_option maxHeartbeats 1600000 in
/-- The direct simple-structure install at the cached driver is
reproduced by the pure fueled `checkDirectStruct`. -/
theorem checkDirectStructS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {p : DirectParts} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkDirectStructS mode (mkFEnv env) p s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDirectStruct (fueledOps mode F) env p = .ok feOut.env := by
  unfold checkDirectStructS at h
  -- stage 1: the type former
  obtain ⟨u0, sA, hfl0, h⟩ := bindC_ok h
  rw [flushC_run] at hfl0
  injection hfl0 with hfl0
  obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
  rw [checkDirectIndF_pushC] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨q1, s₁, hind, h⟩ := bindC_ok h
  obtain ⟨hs₁, q1', hP1, F₁, hF₁⟩ :=
    (checkDirectIndS_sim hμ henv (flushC_csok hwf)) q1 s₁ hind
  obtain ⟨rfl, -⟩ := hP1
  obtain ⟨env₁, cvTa⟩ := q1
  have hF₁p : checkDirectInd (fueledOps mode F₁) env p = .ok (env₁, cvTa) := by
    rw [← checkDirectInd_datF]; exact hF₁
  obtain ⟨henv₁, hTf⟩ := direct_ind_wf henv hF₁p
  -- stage 2: the constructor
  obtain ⟨u1, sB, hfl1, h⟩ := bindC_ok h
  rw [flushC_run] at hfl1
  injection hfl1 with hfl1
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl1
  rw [checkDirectCtorF_pushC] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨q2, s₂, hct, h⟩ := bindC_ok h
  obtain ⟨hs₂, q2', hP2, F₂, hF₂⟩ :=
    (checkDirectCtorS_sim hμ henv₁ hTf (flushC_csok hs₁.residue)) q2 s₂ hct
  obtain ⟨rfl, -⟩ := hP2
  obtain ⟨env₂, cvCa, sorts⟩ := q2
  have hF₂p : checkDirectCtor (fueledOps mode F₂) env env₁ p cvTa
      = .ok (env₂, cvCa, sorts) := by
    rw [← checkDirectCtor_datF]; exact hF₂
  obtain ⟨henv₂, hCf, -⟩ := direct_ctor_wf henv₁ hF₂p
  -- stage 3: the recursor, generated and compared (task #175 S2)
  obtain ⟨u2, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : s₂.flushed = sC := congrArg Prod.snd hfl2
  rw [checkDirectRecF_eq] at h
  obtain ⟨q3, s₃, hrc, h⟩ := bindC_ok h
  obtain ⟨hs₃, q3', hP3, F₃, hF₃⟩ :=
    (checkDirectRecS_sim hμ henv₂ (flushC_csok hs₂.residue)) q3 s₃ hrc
  obtain rfl : q3 = q3' := hP3
  obtain ⟨cvRa, rhsA⟩ := q3
  have hF₃p : checkDirectRec (fueledOps mode F₃) env₂ p cvTa cvCa
      = .ok (cvRa, rhsA) := by
    rw [← checkDirectRec_datF]; exact hF₃
  have henv₃ := direct_rec_wf henv₂ hF₃p
  -- the projection table (task #175 S1)
  rw [push_mkFEnv] at h
  obtain ⟨hwfO, hfeO, henvO, F₆, hF₆⟩ :=
    checkDirectProjTableS_run (T := p.cvT.name) (C := p.cvC.name)
      (lps := p.cvT.levelParams) (nP := p.nP) (nF := p.nF) (rs := p.resSort)
      (guards := directProjGuards cvCa.type p.nP p.nF sorts)
      (cvCa := cvCa) _ henv₃ hs₃.residue h
  obtain ⟨G, hle₁, hle₂, hle₃, hle₆⟩ :
      ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G ∧ F₆ ≤ G :=
    ⟨max F₁ (max F₂ (max F₃ F₆)), by omega, by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₁ : checkDirectInd (fueledOps mode G) env p = .ok (env₁, cvTa) := by
    rw [← checkDirectInd_datF]; exact FueledM.up hle₁ hF₁
  have g₂ : checkDirectCtor (fueledOps mode G) env env₁ p cvTa
      = .ok (env₂, cvCa, sorts) := by
    rw [← checkDirectCtor_datF]; exact FueledM.up hle₂ hF₂
  have g₃ : checkDirectRec (fueledOps mode G) env₂ p cvTa cvCa = .ok (cvRa, rhsA) := by
    rw [← checkDirectRec_datF]; exact FueledM.up hle₃ hF₃
  have g₆ : checkDirectProjTable (m := CheckM) p.cvT.name p.cvC.name
      p.cvT.levelParams p.nP p.nF p.resSort
      (directProjGuards cvCa.type p.nP p.nF sorts) cvCa
      ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
            .plain else .inert, rhsA⟩] :: env₂.consts⟩ = .ok feOut.env := by
    rw [← checkDirectProjTable_datF]; exact FueledM.up hle₆ hF₆
  simp only [checkDirectStruct, Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind]
  rw [g₂]
  simp only [Except.bind]
  rw [g₃]
  simp only [Except.bind]
  exact g₆

set_option maxHeartbeats 1600000 in
/-- The direct sum install at the cached driver is reproduced by the
pure fueled `checkDirectSum` (task #175 sum-types). -/
theorem checkDirectSumS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {p : DirectSumParts} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkDirectSumS mode (mkFEnv env) p s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDirectSum (fueledOps mode F) env p = .ok feOut.env := by
  unfold checkDirectSumS at h
  -- the two front guards
  by_cases hg : (p.large && !p.resSort.isNeverZero &&
      decide (2 ≤ p.ctors.length)) = true
  · rw [if_pos hg] at h; exact absurd h throwC_bind_ok
  rw [if_neg hg] at h
  by_cases hnd : (p.ctors.map (·.1.name)).Nodup
  case neg => rw [if_neg hnd] at h; exact absurd h throwC_bind_ok
  rw [if_pos hnd] at h
  -- stage 1: the type former
  obtain ⟨u0, sA, hfl0, h⟩ := bindC_ok h
  rw [flushC_run] at hfl0
  injection hfl0 with hfl0
  obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
  rw [checkDirectSumIndF_pushC] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨q1, s₁, hind, h⟩ := bindC_ok h
  obtain ⟨hs₁, q1', hP1, F₁, hF₁⟩ :=
    (checkDirectSumIndS_sim hμ henv (flushC_csok hwf)) q1 s₁ hind
  obtain ⟨rfl, -⟩ := hP1
  obtain ⟨env₁, cvTa⟩ := q1
  have hF₁p : checkDirectSumInd (fueledOps mode F₁) env p = .ok (env₁, cvTa) := by
    rw [← checkDirectSumInd_datF]; exact hF₁
  obtain ⟨henv₁, hTf⟩ := direct_sum_ind_wf henv hF₁p
  -- stage 2: every constructor, at the former's environment
  obtain ⟨u1, sB, hfl1, h⟩ := bindC_ok h
  rw [flushC_run] at hfl1
  injection hfl1 with hfl1
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl1
  rw [checkDirectSumCtorsF_eq] at h
  obtain ⟨ctorsA, s₂, hct, h⟩ := bindC_ok h
  obtain ⟨hs₂, ctorsA', hP2, F₂, hF₂⟩ :=
    (checkDirectSumCtorsS_sim hμ henv₁ hTf (flushC_csok hs₁.residue)) ctorsA s₂ hct
  obtain rfl : ctorsA = ctorsA' := hP2
  have hF₂p : checkDirectSumCtors (fueledOps mode F₂) env env₁ p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors
      = .ok ctorsA := by
    rw [← checkDirectSumCtors_datF]; exact hF₂
  -- the constructors' conses
  obtain ⟨hlen, hall⟩ := checkDirectSumCtors_inv hF₂p
  have henv₂ : EnvWF (consSumCtors p.nP ctorsA env₁) := by
    refine envWF_consSumCtors henv₁ ?_
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    exact direct_sum_ctor_typeWF hrun
  rw [consSumCtorsF_mkFEnv] at h
  -- stage 3: the recursor, generated and compared
  obtain ⟨u2, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : s₂.flushed = sC := congrArg Prod.snd hfl2
  rw [checkDirectSumRecF_eq] at h
  obtain ⟨q3, s₃, hrc, h⟩ := bindC_ok h
  obtain ⟨hs₃, q3', hP3, F₃, hF₃⟩ :=
    (checkDirectSumRecS_sim hμ henv₂ (flushC_csok hs₂.residue)) q3 s₃ hrc
  obtain rfl : q3 = q3' := hP3
  obtain ⟨cvRa, rhss⟩ := q3
  have hF₃p : checkDirectSumRec (fueledOps mode F₃) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) := by
    rw [← checkDirectSumRec_datF]; exact hF₃
  -- the final push
  rw [push_mkFEnv] at h
  obtain ⟨rfl, rfl⟩ := pureC_ok h
  obtain ⟨G, hle₁, hle₂, hle₃⟩ : ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G :=
    ⟨max F₁ (max F₂ F₃), by omega, by omega, by omega⟩
  refine ⟨hs₃.residue, rfl, G, ?_⟩
  have g₁ : checkDirectSumInd (fueledOps mode G) env p = .ok (env₁, cvTa) := by
    rw [← checkDirectSumInd_datF]; exact FueledM.up hle₁ hF₁
  have g₂ : checkDirectSumCtors (fueledOps mode G) env env₁ p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors
      = .ok ctorsA := by
    rw [← checkDirectSumCtors_datF]; exact FueledM.up hle₂ hF₂
  have g₃ : checkDirectSumRec (fueledOps mode G) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) := by
    rw [← checkDirectSumRec_datF]; exact FueledM.up hle₃ hF₃
  unfold checkDirectSum
  rw [if_neg hg, if_pos hnd]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind]
  rw [g₂]
  simp only [Except.bind]
  rw [g₃]
  rfl

/-- The inductive block at the cached driver is reproduced by the
pure fueled `checkIndDecl`. -/
theorem checkIndDeclSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
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
      foldIndMemberS_run hμ _ env henv hwf hfold
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
      rw [if_pos hctorRes, if_pos hguard, if_pos hsl]
      exact hF₃p'
    next x1 x2 hne' =>
      exact (hne' cvT c0 cvC nP nF heq1 heq2).elim
  case _ =>
    rename_i x1 x2 hne
    obtain ⟨fe₂, s₂, hfold, h⟩ := bindC_ok h
    obtain ⟨hwf₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run hμ _ env henv hwf hfold
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
theorem checkIndOrDirectSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : (match directPartsF? (mkFEnv env) block with
          | some p => checkDirectStructS mode (mkFEnv env) p
          | none =>
            match directSumPartsF? (mkFEnv env) block with
            | some p => checkDirectSumS mode (mkFEnv env) p
            | none => checkIndDeclSF mode (mkFEnv env) block) s₀ =
      .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) env (.indDecl block) =
      .ok feOut.env := by
  rw [directPartsF?_eq, directSumPartsF?_eq] at h
  show CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (match directParts? env block with
      | some p => checkDirectStruct (fueledOps mode F) env p
      | none =>
        match directSumParts? env block with
        | some p => checkDirectSum (fueledOps mode F) env p
        | none => checkIndDecl mode (fueledOps mode F) env block) = .ok feOut.env
  cases hdp : directParts? env block with
  | some p =>
    rw [hdp] at h
    obtain ⟨hres, hfe, F, hF⟩ := checkDirectStructS_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩
  | none =>
    rw [hdp] at h
    dsimp only
    cases hsp : directSumParts? env block with
    | some p =>
      rw [hsp] at h
      obtain ⟨hres, hfe, F, hF⟩ := checkDirectSumS_run hμ henv hwf h
      exact ⟨hres, hfe, F, hF⟩
    | none =>
      rw [hsp] at h
      obtain ⟨hres, hfe, F, hF⟩ := checkIndDeclSF_run hμ henv hwf h
      exact ⟨hres, hfe, F, hF⟩

/-- The per-declaration bridge: a successful cached shared-state run
over a well-formed environment is reproduced by the pure fueled
checker, and the resulting index is `mkFEnv` of its environment. -/
theorem checkDeclSharedF_bridge (hμ : mode.verifiedChecks = true) {env : Env} {d : Declaration}
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
      obtain ⟨-, hfe, F, hF⟩ := checkIndOrDirectSF_run hμ henv hwf0 hrun
      exact ⟨hfe, F, hF⟩
    | defnDecl cv value hint =>
      rw [checkDeclSFC_nonind env _ (fun _ h => Declaration.noConfusion h)]
        at hrun
      obtain ⟨envO, s₁, hgen, hrun⟩ := bindC_ok hrun
      obtain ⟨hfe, rfl⟩ := pureC_ok hrun
      subst hfe
      obtain ⟨hs', v', hP, F, hF⟩ :=
        (checkDeclS_nonind_sim hμ henv (CSOK.empty env)
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
        (checkDeclS_nonind_sim hμ henv (CSOK.empty env)
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
        (checkDeclS_nonind_sim hμ henv (CSOK.empty env)
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
        (checkDeclS_nonind_sim hμ henv (CSOK.empty env)
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
        (checkDeclS_nonind_sim hμ henv (CSOK.empty env)
          (fun _ h => Declaration.noConfusion h)) envO s₁ hgen
      obtain rfl : envO = v' := hP
      refine ⟨rfl, F, ?_⟩
      rw [← checkDecl_datF]
      exact hF

end Setlec.Cached
