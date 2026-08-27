import Setlec.Verify.BridgeS3
import Setlec.Verify.CheckerF
import Setlec.Model.DirectWF

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

variable {mode : CheckMode}

open Expr EStore

/-! ## Run-level toolkit -/

/-- Flag-off-ness transports along store extension (task #64): every
operation walk's `Ext` preserves the tier flag, so the boundary
witness reaches every interior state. -/
theorem tierOffE {st st' : EStore} (hext : Ext st st')
    (h : st.tierTwo = false) : st'.tierTwo = false := hext.flag.trans h

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

/-- Upgrade a fueled run (subject inferred from the hypothesis). -/
theorem FueledM.up {α : Type} {x : FueledM α} {F F' : Nat} {v : α}
    (hle : F ≤ F') (h : x.val F = .ok v) : x.val F' = .ok v :=
  x.property hle h

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
          rP ≤ mI ∧
          (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
          (∀ pin ∈ pins, pin.hasFvar = false ∧
            pin.allLevelParamsDefined cv.levelParams = true ∧
            pin.constsResolve env = true ∧
            pin.looseBVarsBounded rP = true) ∧
          ∃ pre nm dom body bm D,
            cv.type.stripPis mI = some (pre, .forallE nm dom body bm) ∧
            dom.getAppFn = .const D lvls ∧
            dom.getAppArgs =
              pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
                (List.range (mI - rP)).map
                  (fun i => Expr.bvar (mI - rP - 1 - i)))
    (h7 : ∀ cv value, c = .thmInfo cv value →
      value.hasFvar = false ∧
      value.allLevelParamsDefined cv.levelParams = true ∧
      value.constsResolve env = true ∧
      value.looseBVarsBounded 0 = true := by
        intro cv value h
        exact ConstantInfo.noConfusion h) :
    ConstWF env c := ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The four `ConstWF` type-slot facts of a checked constant. -/
private theorem cvA_type_facts' {env : Env} {cv cvA : ConstantVal}
    {F : Nat}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
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
    (hccv : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
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
    {s₀ s' : IState} (hwf : ISOKF s₀)
    (h : checkIndMemberS mode blockNames caps (mkFEnv env) ci s₀ =
      .ok (fe', s')) :
    ISOKF s' ∧ Ext s₀.store s'.store ∧ fe' = mkFEnv fe'.env ∧
    EnvWF fe'.env ∧
    ∃ F, (checkIndMember (fueledOpsM mode) blockNames caps env ci).val F =
      .ok fe'.env := by
  unfold checkIndMemberS at h
  simp only [checkMemberValF_eq] at h
  obtain ⟨u, s₁, hflush, h⟩ := bindI_ok h
  rw [flushS_run] at hflush
  injection hflush with hflush
  obtain ⟨rfl, rfl⟩ : u = () ∧ s₀.flushed = s₁ :=
    ⟨rfl, congrArg Prod.snd hflush⟩
  obtain ⟨cvA, s₂, hcm, h⟩ := bindI_ok h
  obtain ⟨hs₂, hext₂, cvA', ⟨rfl, hwty⟩, F₁, hFm⟩ :=
    (checkMemberValS_sim henv (flushS_isok hwf)) cvA s₂ hcm
  have hFmp : checkMemberVal (fueledOps mode F₁) blockNames env
      ci.toConstantVal = .ok cvA := by
    rw [← checkMemberVal_datF]; exact hFm
  obtain ⟨hccv, -⟩ := checkMemberVal_inv hFmp
  obtain ⟨htf, htp, htr, htb⟩ := cvA_type_facts' hccv
  cases ci with
  | indInfo cv caps0 =>
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    refine ⟨hs₂.residue (tierOffE hext₂ hwf.wf.tier_off), hext₂, rfl,
      ?_, F₁, ?_⟩
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
    refine ⟨hs₂.residue (tierOffE hext₂ hwf.wf.tier_off), hext₂, rfl,
      ?_, F₁, ?_⟩
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
      EnvWF env → ISOKF s₀ →
      (cis.foldlM (checkIndMemberS mode blockNames caps) (mkFEnv env)) s₀ =
        .ok (fe', s') →
      ISOKF s' ∧ Ext s₀.store s'.store ∧ fe' = mkFEnv fe'.env ∧
      EnvWF fe'.env ∧
      ∃ F, (cis.foldlM (checkIndMember (fueledOpsM mode) blockNames caps)
        env).val F = .ok fe'.env
  | [], env, s₀, fe', s', henv, hwf, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨hwf, Ext.refl _, rfl, henv, 0, rfl⟩
  | ci :: cis, env, s₀, fe', s', henv, hwf, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨hwf₁, hext₁, hfe₁, henv₁, F₁, hF₁⟩ :=
      checkIndMemberS_run henv hwf hstep
    rw [hfe₁] at h
    obtain ⟨hwf', hext', hfe', henv', F₂, hF₂⟩ :=
      foldIndMemberS_run cis fe₁.env henv₁ hwf₁ h
    refine ⟨hwf', hext₁.trans hext', hfe', henv', max F₁ F₂, ?_⟩
    rw [List.foldlM_cons]
    exact atF_bind_intro hF₁ hF₂

/-! ## The recursor group -/

/-- The provisioning fold of the shared driver. -/
theorem provisionRecsS_run {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (env : Env) {s₀ : IState}
      {p : FEnv × List (ConstantVal × Nat × Nat × List RecRule)}
      {s' : IState},
      EnvWF env → ISOKF s₀ →
      provisionRecsS mode blockNames (mkFEnv env) recs s₀ = .ok (p, s') →
      ISOKF s' ∧ Ext s₀.store s'.store ∧ p.1 = mkFEnv p.1.env ∧
      EnvWF p.1.env ∧
      ∃ F, (provisionRecs (fueledOpsM mode) blockNames env recs).val F =
        .ok (p.1.env, p.2)
  | [], env, s₀, p, s', henv, hwf, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨hwf, Ext.refl _, rfl, henv, 0, rfl⟩
  | ci :: rest, env, s₀, p, s', henv, hwf, h => by
    unfold provisionRecsS at h
    simp only [checkMemberValF_eq] at h
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
    obtain rfl : s₀.flushed = s₁ :=
      congrArg Prod.snd hflush
    obtain ⟨cvA, s₂, hcm, h⟩ := bindI_ok h
    obtain ⟨hs₂, hext₂, cvA', ⟨rfl, hwty⟩, F₁, hFm⟩ :=
      (checkMemberValS_sim henv (flushS_isok hwf)) cvA s₂ hcm
    have hFmp : checkMemberVal (fueledOps mode F₁) blockNames env
        (ConstantInfo.recInfo cv mI rP rules).toConstantVal = .ok cvA := by
      rw [← checkMemberVal_datF]; exact hFm
    obtain ⟨hccv, -⟩ := checkMemberVal_inv hFmp
    have henv₁ : EnvWF ⟨.recInfo cvA mI rP [] :: env.consts⟩ :=
      envWF_cons_provRec henv hccv
    obtain ⟨p', s₃, hrec, h⟩ := bindI_ok h
    rw [show (mkFEnv env).push (.recInfo cvA mI rP []) =
      mkFEnv ⟨.recInfo cvA mI rP [] :: env.consts⟩ from rfl] at hrec
    obtain ⟨hwf₃, hext₃, hfeS, henvS, F₂, hF₂⟩ :=
      provisionRecsS_run rest _ henv₁
        (hs₂.residue (tierOffE hext₂ hwf.wf.tier_off)) hrec
    obtain ⟨feSelf, others⟩ := p'
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    refine ⟨hwf₃, Ext.trans hext₂ hext₃, hfeS, henvS, max F₁ F₂, ?_⟩
    show (provisionRecs (fueledOpsM mode) blockNames env
      (ConstantInfo.recInfo cv mI rP rules :: rest)).val (max F₁ F₂) = _
    unfold provisionRecs
    rw [FueledM.atF_bind,
      (checkMemberVal (fueledOpsM mode) blockNames env _).property
        (Nat.le_max_left F₁ F₂) hFm]
    simp only [Bind.bind, Except.bind]
    rw [(provisionRecs (fueledOpsM mode) blockNames
        ⟨.recInfo cvA mI rP [] :: env.consts⟩ rest).property
        (Nat.le_max_right F₁ F₂) hF₂]
    rfl

/-- Transport `ConstWF` along lookup-presence monotonicity. -/
private theorem constWF_le' {envA envB : Env}
    (hle : ∀ n, (envA.find? n).isSome = true →
      (envB.find? n).isSome = true)
    {c : ConstantInfo} (h : ConstWF envA c) : ConstWF envB c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, Expr.constsResolve_le hle h3, h4, ?_, ?_,
    fun cv value heq =>
      let ⟨g1, g2, g3, g4⟩ := h7 cv value heq
      ⟨g1, g2, Expr.constsResolve_le hle g3, g4⟩⟩
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
      ISOK mode envSelf s₀ → s₀.store.tierTwo = false →
      (checked.foldlM (fun (acc : FEnv) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules mode (sharedOps mode (mkFEnv envSelf)) env₂
            envSelf f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1
            0 c.2.2.2
          pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules'))) acc) s₀ =
        .ok (fe₃, s') →
      ISOKF s' ∧ Ext s₀.store s'.store ∧
      (acc = mkFEnv acc.env → fe₃ = mkFEnv fe₃.env) ∧
      ∃ F, (checked.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules mode (fueledOpsM mode) env₂ envSelf f c.1.name
            c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
          acc.env).val F = .ok fe₃.env
  | [], acc, s₀, fe₃, s', _, hs, hoff, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨hs.residue hoff, Ext.refl _, fun hacc => hacc, 0, rfl⟩
  | c :: rest, acc, s₀, fe₃, s', htys, hs, hoff, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨rules', s₂, hir, hstep⟩ := bindI_ok hstep
    obtain ⟨hs₂, hext₂, rules'', hPr, F₁, hF₁⟩ :=
      (checkIotaRulesS_sim henv₂ henvS
        (htys c List.mem_cons_self) hs) rules' s₂ hir
    obtain rfl : rules' = rules'' := hPr
    obtain ⟨hacc₁, rfl⟩ := pureI_ok hstep
    subst hacc₁
    obtain ⟨hwf', hext', hfe', F₂, hF₂⟩ := iotaFoldS_run henv₂ henvS rest
      (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules'))
      (fun c' hc' => htys c' (List.mem_cons_of_mem _ hc')) hs₂
      (tierOffE hext₂ hoff) h
    refine ⟨hwf', Ext.trans hext₂ hext',
      fun hacc => hfe' (by rw [hacc]; rfl), max F₁ F₂, ?_⟩
    rw [List.foldlM_cons]
    have hF₂' : (rest.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
        let rules' ← checkIotaRules mode (fueledOpsM mode) env₂ envSelf f c.1.name
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
          let rules' ← checkIotaRules mode (fueledOpsM mode) env₂ envSelf f c.1.name
            c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
          acc).val F = .ok env₃ →
      checked.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules mode (fueledOps mode F) env₂ envSelf f
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
          acc = .ok env₃
  | [], acc, env₃, h => h
  | c :: rest, acc, env₃, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨e₁, hstep, h⟩ := atF_bind_ok h
    obtain ⟨rules', hir, hstep⟩ := atF_bind_ok hstep
    rw [checkIotaRules_datF] at hir
    show ((checkIotaRules mode (fueledOps mode F) env₂ envSelf f c.1.name
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
    {s₀ : IState} (hwf : ISOKF s₀) {fe₃ : FEnv} {s' : IState}
    (h : checkIndRecsS mode blockNames (mkFEnv env₂) recs s₀ =
      .ok (fe₃, s')) :
    ISOKF s' ∧ Ext s₀.store s'.store ∧ fe₃ = mkFEnv fe₃.env ∧
    EnvWF fe₃.env ∧
    ∃ F, (checkIndRecs mode (fueledOpsM mode) blockNames env₂ recs).val F =
      .ok fe₃.env := by
  unfold checkIndRecsS at h
  by_cases hemp : recs.isEmpty = true
  · rw [if_pos hemp] at h
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    refine ⟨hwf, Ext.refl _, rfl, henv₂, 0, ?_⟩
    show (checkIndRecs mode (fueledOpsM mode) blockNames env₂ recs).val 0 = _
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
  obtain ⟨hwf₁, hext₁, hfeS, henvS, F₁, hF₁⟩ :=
    provisionRecsS_run recs env₂ henv₂ hwf hprovR
  obtain ⟨u, s₂, hflush, h⟩ := bindI_ok h
  rw [flushS_run] at hflush
  injection hflush with hflush
  obtain rfl : s₁.flushed = s₂ :=
    congrArg Prod.snd hflush
  -- the pure provisioning run and its facts
  have hprovP : provisionRecs (fueledOps mode F₁) blockNames env₂ recs =
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
  simp only [checkIotaRulesF_eq] at h
  obtain ⟨hwf', hext', hfe₃, F₂, hF₂⟩ := iotaFoldS_run henv₂ henvS checked
    (mkFEnv env₂) htys (flushS_isok hwf₁) hwf₁.wf.tier_off h
  have hfe₃' : fe₃ = mkFEnv fe₃.env := hfe₃ rfl
  -- both phases at the joined fuel, for the `RulesChain` machinery
  have hF₁M : (provisionRecs (fueledOpsM mode) blockNames env₂ recs).val
      (max F₁ F₂) = .ok (feSelf.env, checked) :=
    (provisionRecs (fueledOpsM mode) blockNames env₂ recs).property
      (Nat.le_max_left F₁ F₂) hF₁
  have hF₂M := (checked.foldlM (fun (acc : Env)
      (c : ConstantVal × Nat × Nat × List RecRule) => do
      let rules' ← checkIotaRules mode (fueledOpsM mode) env₂ feSelf.env
        (fun n => if blockNames.contains n then n.str "_model" else n)
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
      pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
      env₂ : FueledM Env).property (Nat.le_max_right F₁ F₂) hF₂
  have hprovPM : provisionRecs (fueledOps mode (max F₁ F₂)) blockNames env₂
      recs = .ok (feSelf.env, checked) := by
    rw [← provisionRecs_datF]; exact hF₁M
  have hProv := provisionRecs_facts (F := max F₁ F₂) recs env₂
    (feSelf.env, checked) hprovPM hbn
  refine ⟨hwf', Ext.trans hext₁ hext', hfe₃', ?_, ?_⟩
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
        subst e1; subst e2; subst e3; subst e4
        obtain ⟨cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, -, -, -, -,
          hnest, -, -, -, hrf, hrb, hrlp, hrres, -, -, -⟩ := hkits r hr
        refine ⟨hrf, hrlp, ?_, hrb, ?_⟩
        · rw [← Expr.constsResolve_congr hisoSome]
          exact hrres
        · intro lvls pins hfe
          obtain ⟨hmi, hlvls, hpins, hshape, -⟩ := hnest lvls pins hfe
          refine ⟨hmi, hlvls, ?_, hshape⟩
          intro pin hp
          obtain ⟨p1, p2, p3, p4⟩ := hpins pin hp
          exact ⟨p1, p2,
            by rw [← Expr.constsResolve_congr hisoSome]; exact p3, p4⟩
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
    {s₀ : IState} (hs : ISOK mode env s₀) (hoff : s₀.store.tierTwo = false)
    {fe' : FEnv} {s' : IState}
    (h : checkProjFnS mode (mkFEnv env) T ctorName lps nP nF i s₀ =
      .ok (fe', s')) :
    ISOKF s' ∧ Ext s₀.store s'.store ∧ fe' = mkFEnv fe'.env ∧
    EnvWF fe'.env ∧
    ∃ F, (checkProjFn mode (fueledOpsM mode) env T ctorName lps nP nF i).val F =
      .ok fe'.env := by
  unfold checkProjFnS at h
  simp only [checkProjLookupsF_eq, checkProjTyF_eq, checkProjRuleF_eq,
    checkProjIotaF_eq] at h
  obtain ⟨pr, s₁, hlk, h⟩ := bindI_ok h
  obtain ⟨hs₁, hext₁, pr', hPlk, F₀, hFlk⟩ :=
    (checkProjLookupsS_sim hs) pr s₁ hlk
  obtain rfl : pr = pr' := hPlk
  obtain ⟨cvj, mcv⟩ := pr
  obtain ⟨pty, s₂, hty, h⟩ := bindI_ok h
  obtain ⟨hs₂, hext₂, pty', hPty, F₀', hFty⟩ :=
    (checkProjTyS_sim hs₁) pty s₂ hty
  obtain rfl : pty = pty' := hPty
  obtain ⟨u0, s₂', hshape, h⟩ := bindI_ok h
  obtain ⟨hs₂', hext₂', u0', hPu0, F₀'', hFshape⟩ :=
    (checkProjShapeS_sim hs₂) u0 s₂' hshape
  by_cases hi : i < nF
  case neg =>
    rw [if_neg hi] at h
    exact absurd h throwI_bind_ok
  rw [if_pos hi] at h
  obtain ⟨rhsA, s₃, hrule, h⟩ := bindI_ok h
  have hTYc0 : (checkProjTy env T ctorName lps mcv.type nP nF :
      CheckM _) = .ok pty := by
    rw [← checkProjTy_datF (F := F₀')]
    exact hFty
  obtain ⟨hptyf, hptyb⟩ := checkProjTy_wf hTYc0
  have hLKc0 : (checkProjLookups env T ctorName lps nP nF i :
      CheckM _) = .ok (cvj, mcv) := by
    rw [← checkProjLookups_datF (F := F₀)]
    exact hFlk
  obtain ⟨cnP0, cnF0, hctorE⟩ := checkProjLookups_ctor hLKc0
  obtain ⟨hs₃, hext₃, rhsA', hPr, F₁, hFr⟩ :=
    (checkProjRuleS_sim henv hptyf
      (show cvj.type.hasFvar = false from
        (henv _ (find?_mem hctorE)).1) hs₂') rhsA s₃ hrule
  obtain rfl : rhsA = rhsA' := hPr
  obtain ⟨u, s₄, hio, h⟩ := bindI_ok h
  obtain ⟨hs₄, hext₄, u', hPu, F₂, hFio⟩ :=
    (checkProjIotaS_sim henv hs₃) u s₄ hio
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
  have hSHc : (checkProjShape pty cvj.type nP nF : CheckM Unit)
      = .ok u0 := by
    rw [← checkProjShape_datF (F := F₀'')]
    exact hFshape
  -- both fueled stages at a common fuel
  obtain ⟨F₃, hF₁₃, hF₂₃⟩ : ∃ F₃, F₁ ≤ F₃ ∧ F₂ ≤ F₃ :=
    ⟨max F₁ F₂, Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  have hIOc : checkProjIota mode (fueledOps mode F₃) env env T ctorName lps cvj
      nP nF i = .ok u' := by
    rw [← checkProjIota_datF (F := F₃)]
    exact (checkProjIota mode (fueledOpsM mode) env env T ctorName lps cvj nP nF
      i).property hF₂₃ hFio
  have hFrp : checkProjRule (fueledOps mode F₃) env pty cvj lps nP nF i =
      .ok rhsA := by
    rw [← checkProjRule_datF]
    exact (checkProjRule (fueledOpsM mode) env pty cvj lps nP nF
      i).property hF₁₃ hFr
  have hFnp : checkProjFn mode (fueledOps mode F₃) env T ctorName lps nP nF i =
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
    show ((checkProjShape pty cvj.type nP nF : CheckM Unit) >>= _) = _
    rw [hSHc]
    simp only [Bind.bind, Except.bind]
    try dsimp only
    rw [if_pos hi]
    show (checkProjRule (fueledOps mode F₃) env pty cvj lps nP nF i >>= _)
      = _
    rw [hFrp]
    simp only [Bind.bind, Except.bind]
    show (checkProjIota mode (fueledOps mode F₃) env env T ctorName lps cvj nP
      nF i >>= _) = _
    rw [hIOc]
    simp only [Bind.bind, Except.bind]
    rfl
  have hFn : (checkProjFn mode (fueledOpsM mode) env T ctorName lps nP nF
      i).val F₃ = .ok (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [⟨ctorName, nF, nP, if Expr.recRulePlain pty nP nP nP then
          .plain else .inert, rhsA⟩] :: env.consts⟩ : Env) := by
    rw [checkProjFn_datF]
    exact hFnp
  refine ⟨hs₄.residue (tierOffE
      (hext₁.trans (hext₂.trans (hext₂'.trans (hext₃.trans hext₄)))) hoff),
    hext₁.trans (hext₂.trans (hext₂'.trans (hext₃.trans hext₄))),
    rfl, ?_, F₃, hFn⟩
  -- the installed projection recursor is well-formed
  obtain ⟨cvj', mcv', hlk', pty', hty', ⟨_, hshape'⟩, hi', rhsA',
    hrule', ⟨_, hio'⟩, heq⟩ := checkProjFn_inv hFnp
  have heq' := heq
  simp only [Env.mk.injEq, List.cons.injEq] at heq'
  obtain ⟨hrecEq, -⟩ := heq'
  obtain ⟨-, -, hres, hbv, hfv, hlp⟩ := checkProjTy_inv hty'
  obtain ⟨raw, rb, cb, cbody, hraw, hrf, hrb, hann, halp, hrres, hrbv,
    hrfv, hsl, hsp, hdm, -⟩ := checkProjRule_inv hrule'
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
    {s₀ : IState} (hwf : ISOKF s₀) {fe' : FEnv} {s' : IState}
    (h : installProjFnStepS mode T ctorName lps nP nF (mkFEnv env) i s₀ =
      .ok (fe', s')) :
    ISOKF s' ∧ Ext s₀.store s'.store ∧ fe' = mkFEnv fe'.env ∧
    EnvWF fe'.env ∧
    ∃ F, (installProjFnStep mode (fueledOpsM mode) T ctorName lps nP nF env
      i).val F = .ok fe'.env := by
  unfold installProjFnStepS at h
  rw [mkFEnv_find?] at h
  by_cases hart : (env.find? (projModelName T i)).isSome = true
  · rw [if_pos hart] at h
    obtain ⟨u, s₁, hflush, h⟩ := bindI_ok h
    rw [flushS_run] at hflush
    injection hflush with hflush
    obtain rfl : s₀.flushed = s₁ :=
      congrArg Prod.snd hflush
    obtain ⟨hwf', hext', hfe', henv', F, hF⟩ :=
      checkProjFnS_run henv (flushS_isok hwf) hwf.wf.tier_off h
    refine ⟨hwf', hext', hfe', henv', F, ?_⟩
    unfold installProjFnStep
    rw [FueledM.atF_ite, if_pos hart]
    exact hF
  · rw [if_neg hart] at h
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    refine ⟨hwf, Ext.refl _, rfl, henv, 0, ?_⟩
    unfold installProjFnStep
    rw [FueledM.atF_ite, if_neg hart]
    rfl

/-- The artifact-phase fold. -/
theorem foldProjFnS_run {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) (env : Env) {s₀ : IState} {fe' : FEnv}
      {s' : IState},
      EnvWF env → ISOKF s₀ →
      (idxs.foldlM (installProjFnStepS mode T ctorName lps nP nF)
        (mkFEnv env)) s₀ = .ok (fe', s') →
      ISOKF s' ∧ Ext s₀.store s'.store ∧ fe' = mkFEnv fe'.env ∧
      EnvWF fe'.env ∧
      ∃ F, (idxs.foldlM (installProjFnStep mode (fueledOpsM mode) T ctorName lps
        nP nF) env).val F = .ok fe'.env
  | [], env, s₀, fe', s', henv, hwf, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨hwf, Ext.refl _, rfl, henv, 0, rfl⟩
  | i :: idxs, env, s₀, fe', s', henv, hwf, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨hwf₁, hext₁, hfe₁, henv₁, F₁, hF₁⟩ :=
      installProjFnStepS_run henv hwf hstep
    rw [hfe₁] at h
    obtain ⟨hwf', hext', hfe', henv', F₂, hF₂⟩ :=
      foldProjFnS_run idxs fe₁.env henv₁ hwf₁ h
    refine ⟨hwf', hext₁.trans hext', hfe', henv', max F₁ F₂, ?_⟩
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
      s₀ = s' ∧ fe' = mkFEnv fe'.env ∧
      ∃ F, (idxs.foldlM (fun (e : Env) (i : Nat) =>
        (installProjTemplateStep T ctorName lps nP nF e i :
          FueledM Env)) env).val F = .ok fe'.env
  | [], env, s₀, fe', s', h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact ⟨rfl, rfl, 0, rfl⟩
  | i :: idxs, env, s₀, fe', s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨hs01, hfe₁, hpure⟩ := installProjTemplateStepS_run hstep
    rw [hfe₁] at h
    obtain ⟨hs1', hfe', F₂, hF₂⟩ := foldProjTemplatesS_run idxs fe₁.env h
    have hstepF : (installProjTemplateStep T ctorName lps nP nF env i :
        FueledM Env).val F₂ = .ok fe₁.env := by
      rw [installProjTemplateStep_datF]
      exact hpure
    refine ⟨hs01.trans hs1', hfe', F₂, ?_⟩
    rw [List.foldlM_cons]
    have := atF_bind_intro
      (x := (installProjTemplateStep T ctorName lps nP nF env i :
        FueledM Env))
      (g := fun e => idxs.foldlM (fun (e : Env) (i : Nat) =>
        (installProjTemplateStep T ctorName lps nP nF e i :
          FueledM Env)) e)
      hstepF hF₂
    simpa [Nat.max_self] using this

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
  obtain ⟨hRf, -, -, -⟩ := cvA_type_facts' hF₃p
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
