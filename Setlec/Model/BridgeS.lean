import Setlec.Verify.BridgeS2
import Setlec.Model.Extend

/-!
# Shared-state checker: the per-declaration composition (task #51)

Composes the single-environment walks (`Setlec/Verify/BridgeS*.lean`)
along the thin phase drivers of `Setlec/Kernel/CheckerS.lean` into the
per-declaration bridge: a successful `checkDeclShared` run over a
well-formed environment is reproduced by the pure fueled checker.

The environment changes between phases; the state facts threaded
across a transition are only `EStore.WF` of the arena (environment
independent) — each phase starts with `flushS`, which re-establishes
`ISOK` for the phase's environment (`flushS_isok`).  The `EnvWF` facts
for the intermediate environments are derived from the pure runs
exactly as `Setlec/Model/BridgeWF.lean` does (the small `ConstWF`
derivations are replicated here; the heavy machinery —
inversions, `ProvFacts`, `RulesChain` — is the same public kit).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open Expr EStore

/-! ## Run-level toolkit -/

/-- Dissect a successful `CheckIM` bind. -/
theorem bindI_ok {α β : Type} {x : CheckIM α} {k : α → CheckIM β}
    {s₀ : IState} {v : β} {s' : IState}
    (h : (x >>= k) s₀ = .ok (v, s')) :
    ∃ a s₁, x s₀ = .ok (a, s₁) ∧ k a s₁ = .ok (v, s') := by
  simp only [Bind.bind, StateT.bind] at h
  cases hx : x s₀ with
  | error e => rw [hx] at h; exact nomatch h
  | ok pr =>
    obtain ⟨a, s₁⟩ := pr
    rw [hx] at h
    exact ⟨a, s₁, rfl, h⟩

theorem pureI_ok {α : Type} {a : α} {s₀ : IState} {v : α} {s' : IState}
    (h : (pure a : CheckIM α) s₀ = .ok (v, s')) : a = v ∧ s₀ = s' := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at h
  exact h

/-- Compose fueled runs at the joined fuel. -/
theorem atF_bind_intro {α β : Type} {x : FueledM α} {g : α → FueledM β}
    {F₁ F₂ : Nat} {a : α} {v : β} (hx : x.val F₁ = .ok a)
    (hg : (g a).val F₂ = .ok v) :
    (x >>= g).val (max F₁ F₂) = .ok v := by
  rw [FueledM.atF_bind, x.property (Nat.le_max_left F₁ F₂) hx]
  simp only [Bind.bind, Except.bind]
  exact (g a).property (Nat.le_max_right F₁ F₂) hg

/-! ## `ConstWF` derivations (replicated from `BridgeWF`'s private
helpers, over the public inversions) -/

/-- Introduction for `ConstWF` with the clause types spelled out. -/
private theorem constWF_intro' {env : Env} {c : ConstantInfo}
    (h1 : c.toConstantVal.type.hasFvar = false)
    (h2 : c.toConstantVal.type.allLevelParamsDefined
      c.toConstantVal.levelParams = true)
    (h3 : c.toConstantVal.type.constsResolve env = true)
    (h4 : c.toConstantVal.type.looseBVarsBounded 0 = true)
    (h5 : ∀ cv value hint, c = .defnInfo cv value hint →
      value.hasFvar = false ∧
      value.allLevelParamsDefined cv.levelParams = true ∧
      value.constsResolve env = true ∧
      value.looseBVarsBounded 0 = true)
    (h6 : ∀ cv mI rP rules, c = .recInfo cv mI rP rules →
      ∀ r, r ∈ rules →
        (RecRule.rhs r).hasFvar = false ∧
        (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
        (RecRule.rhs r).constsResolve env = true ∧
        (RecRule.rhs r).looseBVarsBounded 0 = true ∧
        ∀ lvls pins, RecRule.fire r = .nested lvls pins →
          mI = rP ∧
          (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
          (∀ pin ∈ pins, pin.hasFvar = false ∧
            pin.allLevelParamsDefined cv.levelParams = true ∧
            pin.constsResolve env = true ∧
            pin.looseBVarsBounded mI = true) ∧
          ∃ pre nm dom body bm D,
            cv.type.stripPis mI = some (pre, .forallE nm dom body bm) ∧
            dom.getAppFn = .const D lvls ∧
            dom.getAppArgs = pins) :
    ConstWF env c := ⟨h1, h2, h3, h4, h5, h6⟩

/-- The four `ConstWF` type-slot facts of a checked constant. -/
private theorem cvA_type_facts' {env : Env} {cv cvA : ConstantVal}
    {F : Nat}
    (h : checkConstantVal (fueledOps F) env cv = .ok cvA) :
    cvA.type.hasFvar = false ∧
    cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
    cvA.type.constsResolve env = true ∧
    cvA.type.looseBVarsBounded 0 = true := by
  obtain ⟨hfind, hres, hshape, hnd, hlbt, hitf, type, stype, u, hann, htp,
    htr, hst, hsort, rfl⟩ := checkConstantVal_inv h
  refine ⟨?_, htp, htr, annotateCore_looseBVars F cv.type hann hlbt⟩
  exact not_hasFvar_of_fvarsBelow_zero
    ((annotateCore_WScoped F cv.type hann
      (WScoped.of_not_hasFvar hitf)).fvarsBelow)

/-- The provisioned (rule-less) recursor cons is well-formed. -/
private theorem envWF_cons_provRec {env : Env} (henv : EnvWF env)
    {cvA : ConstantVal} {mI rP F : Nat} {cv : ConstantVal}
    (hccv : checkConstantVal (fueledOps F) env cv = .ok cvA) :
    EnvWF ⟨.recInfo cvA mI rP [] :: env.consts⟩ := by
  obtain ⟨htf, htp, htr, htb⟩ := cvA_type_facts' hccv
  exact EnvWF.cons henv (constWF_intro' htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq)
    (fun cvR mI' rP' rules' heq r hr => by
      injection heq with h1 h2 h3 h4
      subst h4
      exact nomatch hr))

/-! ## The member fold -/

/-- One member step of the shared driver, run-level: the state's arena
stays canonical, the index invariant is maintained, the output
environment is well-formed, and the step is reproduced by the fueled
generic step. -/
theorem checkIndMemberS_run {blockNames : List Name} {caps : IndCaps}
    {env : Env} (henv : EnvWF env) {ci : ConstantInfo} {fe' : FEnv}
    {s₀ s' : IState} (hwf : s₀.store.WF)
    (h : checkIndMemberS blockNames caps (mkFEnv env) ci s₀ =
      .ok (fe', s')) :
    s'.store.WF ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkIndMember fueledOpsM blockNames caps env ci).val F =
      .ok fe'.env := by
  unfold checkIndMemberS at h
  obtain ⟨u, s₁, hflush, h⟩ := bindI_ok h
  rw [flushS_run] at hflush
  injection hflush with hflush
  obtain ⟨rfl, rfl⟩ : u = () ∧ ({ store := s₀.store } : IState) = s₁ :=
    ⟨rfl, congrArg Prod.snd hflush⟩
  obtain ⟨cvA, s₂, hcm, h⟩ := bindI_ok h
  obtain ⟨hs₂, hext₂, cvA', ⟨rfl, hwty⟩, F₁, hFm⟩ :=
    (checkMemberValS_sim henv (ISOK.fresh env hwf)) cvA s₂ hcm
  have hFmp : checkMemberVal (fueledOps F₁) blockNames env
      ci.toConstantVal = .ok cvA := by
    rw [← checkMemberVal_datF]; exact hFm
  obtain ⟨hccv, -⟩ := checkMemberVal_inv hFmp
  obtain ⟨htf, htp, htr, htb⟩ := cvA_type_facts' hccv
  cases ci with
  | indInfo cv caps0 =>
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    refine ⟨hs₂.wf, rfl, ?_, F₁, ?_⟩
    · exact EnvWF.cons henv (constWF_intro' htf htp
        (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq))
    · unfold checkIndMember
      rw [FueledM.atF_bind, hFm]
      simp only [Bind.bind, Except.bind]
      rfl
  | ctorInfo cv nP nF =>
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    refine ⟨hs₂.wf, rfl, ?_, F₁, ?_⟩
    · exact EnvWF.cons henv (constWF_intro' htf htp
        (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq))
    · unfold checkIndMember
      rw [FueledM.atF_bind, hFm]
      simp only [Bind.bind, Except.bind]
      rfl
  | axiomInfo cv => exact nomatch h
  | projInfo e => exact nomatch h
  | defnInfo cv v hint => exact nomatch h
  | thmInfo cv v => exact nomatch h
  | recInfo cv mI rP rules => exact nomatch h

/-- The member fold of the shared driver. -/
theorem foldIndMemberS_run {blockNames : List Name} {caps : IndCaps} :
    ∀ (cis : List ConstantInfo) (env : Env) {s₀ : IState}
      {fe' : FEnv} {s' : IState},
      EnvWF env → s₀.store.WF →
      (cis.foldlM (checkIndMemberS blockNames caps) (mkFEnv env)) s₀ =
        .ok (fe', s') →
      s'.store.WF ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
      ∃ F, (cis.foldlM (checkIndMember fueledOpsM blockNames caps)
        env).val F = .ok fe'.env
  | [], env, s₀, fe', s', henv, hwf, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | ci :: cis, env, s₀, fe', s', henv, hwf, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨hwf₁, hfe₁, henv₁, F₁, hF₁⟩ :=
      checkIndMemberS_run henv hwf hstep
    rw [hfe₁] at h
    obtain ⟨hwf', hfe', henv', F₂, hF₂⟩ :=
      foldIndMemberS_run cis fe₁.env henv₁ hwf₁ h
    refine ⟨hwf', hfe', henv', max F₁ F₂, ?_⟩
    rw [List.foldlM_cons]
    exact atF_bind_intro hF₁ hF₂

/-! ## The recursor group -/

/-- The provisioning fold of the shared driver. -/
theorem provisionRecsS_run {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (env : Env) {s₀ : IState}
      {p : FEnv × List (ConstantVal × Nat × Nat × List RecRule)}
      {s' : IState},
      EnvWF env → s₀.store.WF →
      provisionRecsS blockNames (mkFEnv env) recs s₀ = .ok (p, s') →
      s'.store.WF ∧ p.1 = mkFEnv p.1.env ∧ EnvWF p.1.env ∧
      ∃ F, (provisionRecs fueledOpsM blockNames env recs).val F =
        .ok (p.1.env, p.2)
  | [], env, s₀, p, s', henv, hwf, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | ci :: rest, env, s₀, p, s', henv, hwf, h => by
    unfold provisionRecsS at h
    cases ci with
    | axiomInfo cv => exact nomatch h
    | projInfo e => exact nomatch h
    | defnInfo cv v hint => exact nomatch h
    | thmInfo cv v => exact nomatch h
    | indInfo cv caps0 => exact nomatch h
    | ctorInfo cv nP nF => exact nomatch h
    | recInfo cv mI rP rules =>
    obtain ⟨u, s₁, hflush, h⟩ := bindI_ok h
    rw [flushS_run] at hflush
    injection hflush with hflush
    obtain rfl : ({ store := s₀.store } : IState) = s₁ :=
      congrArg Prod.snd hflush
    obtain ⟨cvA, s₂, hcm, h⟩ := bindI_ok h
    obtain ⟨hs₂, hext₂, cvA', ⟨rfl, hwty⟩, F₁, hFm⟩ :=
      (checkMemberValS_sim henv (ISOK.fresh env hwf)) cvA s₂ hcm
    have hFmp : checkMemberVal (fueledOps F₁) blockNames env
        (ConstantInfo.recInfo cv mI rP rules).toConstantVal = .ok cvA := by
      rw [← checkMemberVal_datF]; exact hFm
    obtain ⟨hccv, -⟩ := checkMemberVal_inv hFmp
    have henv₁ : EnvWF ⟨.recInfo cvA mI rP [] :: env.consts⟩ :=
      envWF_cons_provRec henv hccv
    obtain ⟨p', s₃, hrec, h⟩ := bindI_ok h
    rw [show (mkFEnv env).push (.recInfo cvA mI rP []) =
      mkFEnv ⟨.recInfo cvA mI rP [] :: env.consts⟩ from rfl] at hrec
    obtain ⟨hwf₃, hfeS, henvS, F₂, hF₂⟩ :=
      provisionRecsS_run rest _ henv₁ hs₂.wf hrec
    obtain ⟨feSelf, others⟩ := p'
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    refine ⟨hwf₃, hfeS, henvS, max F₁ F₂, ?_⟩
    show (provisionRecs fueledOpsM blockNames env
      (ConstantInfo.recInfo cv mI rP rules :: rest)).val (max F₁ F₂) = _
    unfold provisionRecs
    rw [FueledM.atF_bind,
      (checkMemberVal fueledOpsM blockNames env _).property
        (Nat.le_max_left F₁ F₂) hFm]
    simp only [Bind.bind, Except.bind]
    rw [(provisionRecs fueledOpsM blockNames
        ⟨.recInfo cvA mI rP [] :: env.consts⟩ rest).property
        (Nat.le_max_right F₁ F₂) hF₂]
    rfl

/-- Transport `ConstWF` along lookup-presence monotonicity. -/
private theorem constWF_le' {envA envB : Env}
    (hle : ∀ n, (envA.find? n).isSome = true →
      (envB.find? n).isSome = true)
    {c : ConstantInfo} (h : ConstWF envA c) : ConstWF envB c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, Expr.constsResolve_le hle h3, h4, ?_, ?_⟩
  · intro cv v hint heq
    obtain ⟨g1, g2, g3, g4⟩ := h5 cv v hint heq
    exact ⟨g1, g2, Expr.constsResolve_le hle g3, g4⟩
  · intro cv a b e heq r hr
    obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv a b e heq r hr
    refine ⟨g1, g2, Expr.constsResolve_le hle g3, g4, ?_⟩
    intro lvls pins hf
    obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hf
    refine ⟨n1, n2, ?_, n4⟩
    intro pin hp
    obtain ⟨p1, p2, p3, p4⟩ := n3 pin hp
    exact ⟨p1, p2, Expr.constsResolve_le hle p3, p4⟩

/-- A `CheckIM` throw composed with anything never succeeds. -/
theorem throwI_bind_ok {α β : Type} {e : CheckError} {k : α → CheckIM β}
    {s₀ : IState} {v : β} {s' : IState}
    (h : ((throw e : CheckIM α) >>= k) s₀ = .ok (v, s')) : False := by
  exact nomatch h

/-- The iota fold of the shared driver: all operations run at
`envSelf`, one shared state across the whole fold. -/
private theorem iotaFoldS_run {env₂ envSelf : Env}
    (henv₂ : EnvWF env₂) (henvS : EnvWF envSelf) {f : Name → Name} :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      (acc : FEnv) {s₀ : IState} {fe₃ : FEnv} {s' : IState},
      (∀ c ∈ checked, c.1.type.hasFvar = false) →
      ISOK envSelf s₀ →
      (checked.foldlM (fun (acc : FEnv) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules (sharedOps (mkFEnv envSelf)) env₂
            envSelf f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1
            0 c.2.2.2
          pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules'))) acc) s₀ =
        .ok (fe₃, s') →
      s'.store.WF ∧ (acc = mkFEnv acc.env → fe₃ = mkFEnv fe₃.env) ∧
      ∃ F, (checked.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules fueledOpsM env₂ envSelf f c.1.name
            c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
          acc.env).val F = .ok fe₃.env
  | [], acc, s₀, fe₃, s', _, hs, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨hs.wf, fun hacc => hacc, 0, rfl⟩
  | c :: rest, acc, s₀, fe₃, s', htys, hs, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨rules', s₂, hir, hstep⟩ := bindI_ok hstep
    obtain ⟨hs₂, hext₂, rules'', hPr, F₁, hF₁⟩ :=
      (checkIotaRulesS_sim henv₂ henvS
        (htys c List.mem_cons_self) hs) rules' s₂ hir
    obtain rfl : rules' = rules'' := hPr
    obtain ⟨hacc₁, rfl⟩ := pureI_ok hstep
    subst hacc₁
    obtain ⟨hwf', hfe', F₂, hF₂⟩ := iotaFoldS_run henv₂ henvS rest
      (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules'))
      (fun c' hc' => htys c' (List.mem_cons_of_mem _ hc')) hs₂ h
    refine ⟨hwf', fun hacc => hfe' (by rw [hacc]; rfl), max F₁ F₂, ?_⟩
    rw [List.foldlM_cons]
    have hF₂' : (rest.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
        let rules' ← checkIotaRules fueledOpsM env₂ envSelf f c.1.name
          c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
        (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.env.consts⟩ :
          Env)).val F₂ = .ok fe₃.env := hF₂
    refine atF_bind_intro (F₁ := F₁) (F₂ := F₂) ?_ hF₂'
    rw [FueledM.atF_bind, hF₁]
    rfl

/-- Convert the constructed fueled iota fold to a pure fold at the
same fuel. -/
private theorem iotaFold_datF {env₂ envSelf : Env} {f : Name → Name}
    {F : Nat} :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      (acc : Env) {env₃ : Env},
      (checked.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules fueledOpsM env₂ envSelf f c.1.name
            c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
          acc).val F = .ok env₃ →
      checked.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules (fueledOps F) env₂ envSelf f
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
          acc = .ok env₃
  | [], acc, env₃, h => h
  | c :: rest, acc, env₃, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨e₁, hstep, h⟩ := atF_bind_ok h
    obtain ⟨rules', hir, hstep⟩ := atF_bind_ok hstep
    rw [checkIotaRules_datF] at hir
    show ((checkIotaRules (fueledOps F) env₂ envSelf f c.1.name
      c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2 >>= _ :
        CheckM Env) >>= _) = _
    rw [hir]
    simp only [Bind.bind, Except.bind]
    have hstep' : (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' ::
        acc.consts⟩ : Env) = e₁ := by
      have hst : (Except.ok (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' ::
          acc.consts⟩ : Env) : Except CheckError Env) = .ok e₁ := hstep
      exact Except.ok.inj hst
    simp only [pure, Except.pure]
    rw [hstep']
    exact iotaFold_datF rest e₁ h

/-- The recursor group of the shared driver. -/
theorem checkIndRecsS_run {blockNames : List Name} {env₂ : Env}
    {recs : List ConstantInfo} (henv₂ : EnvWF env₂)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    {s₀ : IState} (hwf : s₀.store.WF) {fe₃ : FEnv} {s' : IState}
    (h : checkIndRecsS blockNames (mkFEnv env₂) recs s₀ =
      .ok (fe₃, s')) :
    s'.store.WF ∧ fe₃ = mkFEnv fe₃.env ∧ EnvWF fe₃.env ∧
    ∃ F, (checkIndRecs fueledOpsM blockNames env₂ recs).val F =
      .ok fe₃.env := by
  unfold checkIndRecsS at h
  by_cases hemp : recs.isEmpty = true
  · rw [if_pos hemp] at h
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    refine ⟨hwf, rfl, henv₂, 0, ?_⟩
    show (checkIndRecs fueledOpsM blockNames env₂ recs).val 0 = _
    unfold checkIndRecs
    rw [FueledM.atF_ite, if_pos hemp]
    rfl
  rw [if_neg hemp] at h
  dsimp only at h
  by_cases heqf : env₂.find? eqName = some eqA
  case neg =>
    rw [if_neg (show ¬((mkFEnv env₂).find? eqName = some eqA) by
      rw [mkFEnv_find?]; exact heqf)] at h
    exact absurd h throwI_bind_ok
  rw [if_pos (show (mkFEnv env₂).find? eqName = some eqA by
    rw [mkFEnv_find?]; exact heqf)] at h
  obtain ⟨p, s₁, hprovR, h⟩ := bindI_ok h
  obtain ⟨feSelf, checked⟩ := p
  obtain ⟨hwf₁, hfeS, henvS, F₁, hF₁⟩ :=
    provisionRecsS_run recs env₂ henv₂ hwf hprovR
  obtain ⟨u, s₂, hflush, h⟩ := bindI_ok h
  rw [flushS_run] at hflush
  injection hflush with hflush
  obtain rfl : ({ store := s₁.store } : IState) = s₂ :=
    congrArg Prod.snd hflush
  -- the pure provisioning run and its facts
  have hprovP : provisionRecs (fueledOps F₁) blockNames env₂ recs =
      .ok (feSelf.env, checked) := by
    rw [← provisionRecs_datF]; exact hF₁
  have hProvF₁ := provisionRecs_facts (F := F₁) recs env₂
    (feSelf.env, checked) hprovP hbn
  have htys : ∀ c ∈ checked, c.1.type.hasFvar = false := by
    intro c hc
    obtain ⟨-, -, -, -, htyf, -, -, -, -, -⟩ :=
      ProvFacts.mem_facts hProvF₁ c hc
    exact htyf
  -- the iota fold in the shared state at `envSelf`
  rw [hfeS] at h
  obtain ⟨hwf', hfe₃, F₂, hF₂⟩ := iotaFoldS_run henv₂ henvS checked
    (mkFEnv env₂) htys (ISOK.fresh feSelf.env hwf₁) h
  have hfe₃' : fe₃ = mkFEnv fe₃.env := hfe₃ rfl
  -- both phases at the joined fuel, for the `RulesChain` machinery
  have hF₁M : (provisionRecs fueledOpsM blockNames env₂ recs).val
      (max F₁ F₂) = .ok (feSelf.env, checked) :=
    (provisionRecs fueledOpsM blockNames env₂ recs).property
      (Nat.le_max_left F₁ F₂) hF₁
  have hF₂M := (checked.foldlM (fun (acc : Env)
      (c : ConstantVal × Nat × Nat × List RecRule) => do
      let rules' ← checkIotaRules fueledOpsM env₂ feSelf.env
        (fun n => if blockNames.contains n then n.str "_model" else n)
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
      pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
      env₂ : FueledM Env).property (Nat.le_max_right F₁ F₂) hF₂
  have hprovPM : provisionRecs (fueledOps (max F₁ F₂)) blockNames env₂
      recs = .ok (feSelf.env, checked) := by
    rw [← provisionRecs_datF]; exact hF₁M
  have hProv := provisionRecs_facts (F := max F₁ F₂) recs env₂
    (feSelf.env, checked) hprovPM hbn
  refine ⟨hwf', hfe₃', ?_, ?_⟩
  · -- the final environment is well-formed (as in `checkIndRecs_wfimp`)
    have hpure := iotaFold_datF checked env₂ hF₂M
    obtain ⟨zipped, hmap, hchain⟩ := rulesFold_inv checked env₂ fe₃.env
      hpure
    rw [show checked = zipped.map Prod.fst from hmap.symm] at hProv htys
    have hswSh := chains_swapSh hProv hchain
      (SwapShList.of_eq env₂.consts)
    have hcorr := swapSh_find?_corr hswSh
    have hisoSome : ∀ n, (feSelf.env.find? n).isSome =
        (fe₃.env.find? n).isSome := by
      intro n
      rcases hcorr n with heq | ⟨cv, a, b, e0, h₀, h₃, -⟩
      · rw [heq]
      · rw [h₀, h₃]
        rfl
    intro c₃ hc₃
    rcases rulesChain_mem hchain c₃ hc₃ with hc₂ | ⟨z, hz, rfl⟩
    · refine constWF_le' (fun n hn => ?_) (henv₂ c₃ hc₂)
      rw [← hisoSome n]
      cases hf2 : env₂.find? n with
      | none =>
        rw [hf2] at hn
        exact nomatch hn
      | some ci₂ =>
        rw [ProvFacts.find?_preserved hProv n ci₂ hf2]
        rfl
    · have hz1 : z.1 ∈ zipped.map Prod.fst := List.mem_map_of_mem hz
      obtain ⟨-, -, -, -, htyf, htyb, htlp, htres, -, -⟩ :=
        ProvFacts.mem_facts hProv z.1 hz1
      have hkits := checkIotaRules_inv 0 _ _
        (RulesChain.mem_facts hchain z hz)
      refine constWF_intro' htyf htlp ?_ htyb
        (fun _ _ _ heq => nomatch heq) ?_
      · rw [← Expr.constsResolve_congr hisoSome]
        exact htres
      · intro cvR mI' rP' rules'' heq r hr
        injection heq with e1 e2 e3 e4
        subst e4
        obtain ⟨cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, -, -, -, -,
          hnest, -, -, -, hrf, hrb, hrlp, hrres, -, -, -⟩ := hkits r hr
        refine ⟨hrf, by rw [← e1]; exact hrlp, ?_, hrb, ?_⟩
        · rw [← Expr.constsResolve_congr hisoSome]
          exact hrres
        · intro lvls pins hfe
          obtain ⟨hmi, hlvls, hpins, hshape, -⟩ := hnest lvls pins hfe
          refine ⟨by rw [← e2, ← e3]; exact hmi,
            by rw [← e1]; exact hlvls, ?_, ?_⟩
          · intro pin hp
            obtain ⟨p1, p2, p3, p4⟩ := hpins pin hp
            exact ⟨p1, by rw [← e1]; exact p2,
              by rw [← Expr.constsResolve_congr hisoSome]; exact p3,
              by rw [← e2]; exact p4⟩
          · rw [← e1, ← e2]
            exact hshape
  · refine ⟨max F₁ F₂, ?_⟩
    unfold checkIndRecs
    rw [FueledM.atF_ite, if_neg hemp]
    dsimp only
    rw [if_pos heqf]
    rw [FueledM.atF_bind, hF₁M]
    simp only [Bind.bind, Except.bind]
    exact hF₂M

/-! ## The projection phases -/

/-- The projection-function install (mirrors `checkProjFn`). -/
theorem checkProjFnS_run {env : Env} (henv : EnvWF env)
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {s₀ : IState} (hs : ISOK env s₀) {fe' : FEnv} {s' : IState}
    (h : checkProjFnS (mkFEnv env) T ctorName lps nP nF i s₀ =
      .ok (fe', s')) :
    s'.store.WF ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkProjFn fueledOpsM env T ctorName lps nP nF i).val F =
      .ok fe'.env := by
  unfold checkProjFnS at h
  obtain ⟨pr, s₁, hlk, h⟩ := bindI_ok h
  obtain ⟨hs₁, hext₁, pr', hPlk, F₀, hFlk⟩ :=
    (checkProjLookupsS_sim hs) pr s₁ hlk
  obtain rfl : pr = pr' := hPlk
  obtain ⟨cvj, mcv⟩ := pr
  obtain ⟨pty, s₂, hty, h⟩ := bindI_ok h
  obtain ⟨hs₂, hext₂, pty', hPty, F₀', hFty⟩ :=
    (checkProjTyS_sim hs₁) pty s₂ hty
  obtain rfl : pty = pty' := hPty
  by_cases hi : i < nF
  case neg =>
    rw [if_neg hi] at h
    exact absurd h throwI_bind_ok
  rw [if_pos hi] at h
  obtain ⟨rhsA, s₃, hrule, h⟩ := bindI_ok h
  obtain ⟨hs₃, hext₃, rhsA', hPr, F₁, hFr⟩ :=
    (checkProjRuleS_sim henv hs₂) rhsA s₃ hrule
  obtain rfl : rhsA = rhsA' := hPr
  obtain ⟨u, s₄, hio, h⟩ := bindI_ok h
  obtain ⟨hs₄, hext₄, u', hPu, F₂, hFio⟩ :=
    (checkProjIotaS_sim hs₃) u s₄ hio
  obtain ⟨hfe, rfl⟩ := pureI_ok h
  subst hfe
  -- the ops-free stages, `CheckM`-level
  have hLKc : (checkProjLookups env T ctorName lps nP nF i :
      CheckM _) = .ok (cvj, mcv) := by
    rw [← checkProjLookups_datF (F := F₀)]
    exact hFlk
  have hTYc : (checkProjTy env T ctorName lps mcv.type nP nF :
      CheckM _) = .ok pty := by
    rw [← checkProjTy_datF (F := F₀')]
    exact hFty
  have hIOc : (checkProjIota env T ctorName lps cvj nP nF i :
      CheckM _) = .ok u := by
    rw [← checkProjIota_datF (F := F₂)]
    exact hFio
  have hFrp : checkProjRule (fueledOps F₁) env cvj lps nP nF i =
      .ok rhsA := by
    rw [← checkProjRule_datF]
    exact hFr
  have hFnp : checkProjFn (fueledOps F₁) env T ctorName lps nP nF i =
      .ok (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, if Expr.recRulePlain pty nP nP nP then
          .plain else .inert, rhsA⟩] :: env.consts⟩ : Env) := by
    unfold checkProjFn
    show ((checkProjLookups env T ctorName lps nP nF i :
      CheckM _) >>= _) = _
    rw [hLKc]
    simp only [Bind.bind, Except.bind]
    show ((checkProjTy env T ctorName lps mcv.type nP nF :
      CheckM _) >>= _) = _
    rw [hTYc]
    simp only [Bind.bind, Except.bind]
    try dsimp only
    rw [if_pos hi]
    show (checkProjRule (fueledOps F₁) env cvj lps nP nF i >>= _) = _
    rw [hFrp]
    simp only [Bind.bind, Except.bind]
    show ((checkProjIota env T ctorName lps cvj nP nF i :
      CheckM _) >>= _) = _
    rw [hIOc]
    simp only [Bind.bind, Except.bind]
    rfl
  have hFn : (checkProjFn fueledOpsM env T ctorName lps nP nF
      i).val F₁ = .ok (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, if Expr.recRulePlain pty nP nP nP then
          .plain else .inert, rhsA⟩] :: env.consts⟩ : Env) := by
    rw [checkProjFn_datF]
    exact hFnp
  refine ⟨hs₄.wf, rfl, ?_, F₁, hFn⟩
  -- the installed projection recursor is well-formed
  obtain ⟨cvj', mcv', hlk', pty', hty', hi', rhsA', hrule', ⟨_, hio'⟩,
    heq⟩ := checkProjFn_inv hFnp
  have heq' := heq
  simp only [Env.mk.injEq, List.cons.injEq] at heq'
  obtain ⟨hrecEq, -⟩ := heq'
  obtain ⟨-, -, hres, hbv, hfv, hlp⟩ := checkProjTy_inv hty'
  obtain ⟨raw, rb, cb, cbody, hraw, hrf, hrb, hann, halp, hrres, hrbv,
    hrfv, hsl, hsp, hdm⟩ := checkProjRule_inv hrule'
  show EnvWF (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
      [⟨ctorName, nF, nP, if Expr.recRulePlain pty nP nP nP then
        RecRuleFire.plain else .inert, rhsA⟩] :: env.consts⟩ : Env)
  rw [show (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
      [⟨ctorName, nF, nP, if Expr.recRulePlain pty nP nP nP then
        RecRuleFire.plain else .inert, rhsA⟩] :: env.consts⟩ : Env) =
    ⟨.recInfo ⟨projFnName T i, lps, pty'⟩ nP nP
      [⟨ctorName, nF, nP, if Expr.recRulePlain pty' nP nP nP then
        RecRuleFire.plain else .inert, rhsA'⟩] :: env.consts⟩
    from by rw [hrecEq]]
  refine EnvWF.cons henv (constWF_intro' hfv hlp
    (Expr.constsResolve_mono hres) hbv
    (fun _ _ _ heq2 => nomatch heq2) ?_)
  intro cvR mI' rP' rules'' heq2 r hr
  injection heq2 with e1 e2 e3 e4
  subst e1
  subst e4
  rcases List.mem_singleton.mp hr with rfl
  refine ⟨hrfv, halp, Expr.constsResolve_mono hrres, hrbv, ?_⟩
  intro lvls pins hf
  cases hcond : Expr.recRulePlain pty' nP nP nP <;>
    simp [hcond] at hf

/-- One projection-function install step. -/
theorem installProjFnStepS_run {env : Env} (henv : EnvWF env)
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {s₀ : IState} (hwf : s₀.store.WF) {fe' : FEnv} {s' : IState}
    (h : installProjFnStepS T ctorName lps nP nF (mkFEnv env) i s₀ =
      .ok (fe', s')) :
    s'.store.WF ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (installProjFnStep fueledOpsM T ctorName lps nP nF env
      i).val F = .ok fe'.env := by
  unfold installProjFnStepS at h
  rw [mkFEnv_find?] at h
  by_cases hart : (env.find? (projModelName T i)).isSome = true
  · rw [if_pos hart] at h
    obtain ⟨u, s₁, hflush, h⟩ := bindI_ok h
    rw [flushS_run] at hflush
    injection hflush with hflush
    obtain rfl : ({ store := s₀.store } : IState) = s₁ :=
      congrArg Prod.snd hflush
    obtain ⟨hwf', hfe', henv', F, hF⟩ :=
      checkProjFnS_run henv (ISOK.fresh env hwf) h
    refine ⟨hwf', hfe', henv', F, ?_⟩
    unfold installProjFnStep
    rw [FueledM.atF_ite, if_pos hart]
    exact hF
  · rw [if_neg hart] at h
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    refine ⟨hwf, rfl, henv, 0, ?_⟩
    unfold installProjFnStep
    rw [FueledM.atF_ite, if_neg hart]
    rfl

/-- The artifact-phase fold. -/
theorem foldProjFnS_run {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) (env : Env) {s₀ : IState} {fe' : FEnv}
      {s' : IState},
      EnvWF env → s₀.store.WF →
      (idxs.foldlM (installProjFnStepS T ctorName lps nP nF)
        (mkFEnv env)) s₀ = .ok (fe', s') →
      s'.store.WF ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
      ∃ F, (idxs.foldlM (installProjFnStep fueledOpsM T ctorName lps
        nP nF) env).val F = .ok fe'.env
  | [], env, s₀, fe', s', henv, hwf, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | i :: idxs, env, s₀, fe', s', henv, hwf, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨hwf₁, hfe₁, henv₁, F₁, hF₁⟩ :=
      installProjFnStepS_run henv hwf hstep
    rw [hfe₁] at h
    obtain ⟨hwf', hfe', henv', F₂, hF₂⟩ :=
      foldProjFnS_run idxs fe₁.env henv₁ hwf₁ h
    refine ⟨hwf', hfe', henv', max F₁ F₂, ?_⟩
    rw [List.foldlM_cons]
    exact atF_bind_intro hF₁ hF₂

/-- One template install step (operation-free; state unchanged; the
comparand computed at the `CheckM` instantiation). -/
theorem installProjTemplateStepS_run {env : Env}
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {s₀ : IState} {fe' : FEnv} {s' : IState}
    (h : installProjTemplateStepS T ctorName lps nP nF (mkFEnv env) i
      s₀ = .ok (fe', s')) :
    s₀ = s' ∧ fe' = mkFEnv fe'.env ∧
    (installProjTemplateStep T ctorName lps nP nF env i :
      CheckM Env) = .ok fe'.env := by
  unfold installProjTemplateStepS installProjTemplateS at h
  unfold installProjTemplateStep installProjTemplate
  simp only [mkFEnv_find?] at h
  by_cases hfn : (env.find? (projFnName T i)).isNone = true
  case neg =>
    rw [if_neg hfn] at h ⊢
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨rfl, rfl, rfl⟩
  rw [if_pos hfn] at h ⊢
  cases hrec : env.find? (T.str "rec") with
  | none =>
    rw [hrec] at h
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨rfl, rfl, rfl⟩
  | some ci =>
    rw [hrec] at h
    cases ci with
    | recInfo cvR mI rP rules =>
      cases rules with
      | nil =>
        obtain ⟨hfe, rfl⟩ := pureI_ok h
        subst hfe
        exact ⟨rfl, rfl, rfl⟩
      | cons rule rules' =>
        cases rules' with
        | cons _ _ =>
          obtain ⟨hfe, rfl⟩ := pureI_ok h
          subst hfe
          exact ⟨rfl, rfl, rfl⟩
        | nil =>
          dsimp only at h ⊢
          by_cases hcond : (env.find? (projFnName T i)).isNone =
              true ∧ mI = rP ∧ rP = nP + 2 ∧ rule.ctor = ctorName ∧
              i < nF
          · rw [if_pos hcond] at h ⊢
            obtain ⟨hfe, rfl⟩ := pureI_ok h
            subst hfe
            exact ⟨rfl, rfl, rfl⟩
          · rw [if_neg hcond] at h ⊢
            obtain ⟨hfe, rfl⟩ := pureI_ok h
            subst hfe
            exact ⟨rfl, rfl, rfl⟩
    | axiomInfo cv =>
      obtain ⟨hfe, rfl⟩ := pureI_ok h
      subst hfe
      exact ⟨rfl, rfl, rfl⟩
    | projInfo e =>
      obtain ⟨hfe, rfl⟩ := pureI_ok h
      subst hfe
      exact ⟨rfl, rfl, rfl⟩
    | defnInfo cv v hint =>
      obtain ⟨hfe, rfl⟩ := pureI_ok h
      subst hfe
      exact ⟨rfl, rfl, rfl⟩
    | thmInfo cv v =>
      obtain ⟨hfe, rfl⟩ := pureI_ok h
      subst hfe
      exact ⟨rfl, rfl, rfl⟩
    | indInfo cv caps =>
      obtain ⟨hfe, rfl⟩ := pureI_ok h
      subst hfe
      exact ⟨rfl, rfl, rfl⟩
    | ctorInfo cv nP' nF' =>
      obtain ⟨hfe, rfl⟩ := pureI_ok h
      subst hfe
      exact ⟨rfl, rfl, rfl⟩

/-- The template-phase fold. -/
theorem foldProjTemplatesS_run {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) (env : Env) {s₀ : IState} {fe' : FEnv}
      {s' : IState},
      (idxs.foldlM (installProjTemplateStepS T ctorName lps nP nF)
        (mkFEnv env)) s₀ = .ok (fe', s') →
      ∃ F, (idxs.foldlM (fun (e : Env) (i : Nat) =>
        (installProjTemplateStep T ctorName lps nP nF e i :
          FueledM Env)) env).val F = .ok fe'.env
  | [], env, s₀, fe', s', h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨0, rfl⟩
  | i :: idxs, env, s₀, fe', s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨hs01, hfe₁, hpure⟩ := installProjTemplateStepS_run hstep
    rw [hfe₁] at h
    obtain ⟨F₂, hF₂⟩ := foldProjTemplatesS_run idxs fe₁.env h
    have hstepF : (installProjTemplateStep T ctorName lps nP nF env i :
        FueledM Env).val F₂ = .ok fe₁.env := by
      rw [installProjTemplateStep_datF]
      exact hpure
    refine ⟨F₂, ?_⟩
    rw [List.foldlM_cons]
    have := atF_bind_intro
      (x := (installProjTemplateStep T ctorName lps nP nF env i :
        FueledM Env))
      (g := fun e => idxs.foldlM (fun (e : Env) (i : Nat) =>
        (installProjTemplateStep T ctorName lps nP nF e i :
          FueledM Env)) e)
      hstepF hF₂
    simpa [Nat.max_self] using this

end Setlec
