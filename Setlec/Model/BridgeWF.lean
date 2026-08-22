import Setlec.Verify.BridgeWfImp
import Setlec.Model.Extend

/-!
# Threading `EnvWF` through the declaration checker

Part C of the refinement bridge left a successful cached `checkDecl`
run reproduced by the `wfOpsM` instantiation (`checkDecl_wfOpsM_bridge`)
— the comparand that is the pure fueled family exactly over well-formed
environments.  This file turns such runs into plain pure runs
(`checkDecl (fueledOps F)`), given `EnvWF` of the *input* environment
only: every intermediate environment the declaration checker calls the
core operations at (the block-install fold's, the provisional recursor
self, the projection-install fold's) is shown well-formed from the
checker's own guards, using the syntactic inversions of
`Setlec/Model/Extend`.  There is **no runtime well-formedness check**
anywhere — the consistency layer (`Setlec/Model/ConsistencyC.lean`)
supplies `EnvWF` of the input environment from the environment model
(`EnvModel.wf`), which `checkDecl_sound` preserves.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Setlec

open Expr

/-- Introduction for `ConstWF` with the clause types spelled out (the
anonymous constructor does not see through the definition). -/
private theorem constWF_intro {env : Env} {c : ConstantInfo}
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

/-- The four `ConstWF` type-slot facts for the constant returned by a
successful `checkConstantVal` run: level parameters and constant
resolution are checked outright; closedness and fvar-freeness of the
annotated type follow from the raw checks and annotation preserving
scoping. -/
private theorem cvA_type_facts {env : Env} {cv cvA : ConstantVal} {F : Nat}
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

/-- Two conses of same-named constants store the same names. -/
private theorem find?_isSome_cons_swap {env : Env} {c₁ c₂ : ConstantInfo}
    (hn : c₁.name = c₂.name) (n : Name) :
    (Env.find? ⟨c₁ :: env.consts⟩ n).isSome =
      (Env.find? ⟨c₂ :: env.consts⟩ n).isSome := by
  rw [Env.find?_cons, Env.find?_cons, hn]
  split <;> rfl

/-- The four `ConstWF` facts `RuleChecked` provides for a checked
rule's right-hand side. -/
private theorem ruleChecked_rhs_facts {F : Nat} {env env₀ : Env}
    {f : Name → Name} {cvA : ConstantVal} {mI rP : Nat}
    {r : RecRule} (h : RuleChecked F env env₀ f cvA mI rP r) :
    (RecRule.rhs r).hasFvar = false ∧
    (RecRule.rhs r).looseBVarsBounded 0 = true ∧
    (RecRule.rhs r).allLevelParamsDefined cvA.levelParams = true ∧
    (RecRule.rhs r).constsResolve env₀ = true := by
  obtain ⟨cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, -, -, -, -, -, -, -,
    -, hrhsf, hrhsb, hrlp, hrres, -, -, -⟩ := h
  exact ⟨hrhsf, hrhsb, hrlp, hrres⟩

/-! ## `checkIndMember` -/

/-- A successful `wfOpsM` run of `checkIndMember` over a well-formed
environment is the pure run at the same fuel, and its output
environment is well-formed again. -/
theorem checkIndMember_wfimp {blockNames : List Name} {caps : IndCaps}
    {env' env₁ : Env} {ci : ConstantInfo} {F : Nat}
    (henv' : EnvWF env')
    (h : (checkIndMember wfOpsM blockNames caps env' ci).val F =
      .ok env₁) :
    checkIndMember (fueledOps F) blockNames caps env' ci = .ok env₁ ∧
      EnvWF env₁ := by
  unfold checkIndMember at h
  try dsimp only [] at h
  obtain ⟨cvA, hcmvW, h⟩ := atF_bind_ok h
  have hcmv := checkMemberVal_wfimp henv' hcmvW
  have hpure : checkIndMember (fueledOps F) blockNames caps env' ci =
      .ok env₁ := by
    unfold checkIndMember
    try dsimp only []
    show (checkMemberVal (fueledOps F) blockNames env' ci.toConstantVal
      >>= _) = _
    rw [hcmv]
    simp only [Bind.bind, Except.bind]
    revert h
    match hci : ci with
    | .indInfo cvI capsI => intro h; exact h
    | .ctorInfo cvI nPI nFI => intro h; exact h
    | .axiomInfo _ => intro h; exact nomatch h
    | .projInfo _ => intro h; exact nomatch h
    | .defnInfo _ _ _ => intro h; exact nomatch h
    | .thmInfo _ _ => intro h; exact nomatch h
    | .recInfo _ _ _ _ => intro h; exact nomatch h
  refine ⟨hpure, ?_⟩
  obtain ⟨cvA', cvm, mval, hmcvm, hccv', hms, hfm, hlps, hren, hcases⟩ :=
    checkIndMember_inv hpure
  obtain ⟨htf, htp, htr, htb⟩ := cvA_type_facts hccv'
  rcases hcases with ⟨⟨cv, caps', rfl⟩, rfl⟩ | ⟨cv, nP, nF, rfl, rfl⟩
  · exact EnvWF.cons henv' (constWF_intro htf htp
      (Expr.constsResolve_mono htr) htb
      (fun _ _ _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq))
  · exact EnvWF.cons henv' (constWF_intro htf htp
      (Expr.constsResolve_mono htr) htb
      (fun _ _ _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq))

/-- The recursor-provisioning fold, `wfOpsM` to pure, with the
provisional environment well-formed. -/
private theorem provisionRecs_wfimp {blockNames : List Name} {F : Nat} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      {p : Env × List (ConstantVal × Nat × Nat × List RecRule)},
      EnvWF envAcc →
      (provisionRecs wfOpsM blockNames envAcc recs).val F = .ok p →
      provisionRecs (fueledOps F) blockNames envAcc recs = .ok p ∧
        EnvWF p.1
  | [], envAcc, p, henv, h => by
    have h' : (Except.ok ((envAcc, []) : Env × _) :
        Except CheckError _) = Except.ok p := h
    cases h'
    exact ⟨rfl, henv⟩
  | ci :: rest, envAcc, p, henv, h => by
    unfold provisionRecs at h ⊢
    revert h
    match hci : ci with
    | .recInfo cv mI rP rules => ?_
    | .axiomInfo _ => intro h; exact nomatch h
    | .projInfo _ => intro h; exact nomatch h
    | .defnInfo _ _ _ => intro h; exact nomatch h
    | .thmInfo _ _ => intro h; exact nomatch h
    | .indInfo _ _ => intro h; exact nomatch h
    | .ctorInfo _ _ _ => intro h; exact nomatch h
    intro h
    dsimp only [] at h ⊢
    obtain ⟨cvA, hcmvW, h⟩ := atF_bind_ok h
    have hcmv := checkMemberVal_wfimp henv hcmvW
    obtain ⟨hccv, -, -, -, -, -, -, -⟩ := checkMemberVal_inv hcmv
    obtain ⟨htf, htp, htr, htb⟩ := cvA_type_facts hccv
    have henv₁ : EnvWF ⟨.recInfo cvA mI rP [] ::
        envAcc.consts⟩ :=
      EnvWF.cons henv (constWF_intro htf htp
        (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq)
        (fun cvR mI' rP' rules' heq r hr => by
          injection heq with h1 h2 h3 h4
          subst h4
          exact nomatch hr))
    obtain ⟨p', hrecW, h⟩ := atF_bind_ok h
    obtain ⟨hrec, hwfS⟩ := provisionRecs_wfimp rest _ henv₁ hrecW
    obtain ⟨envSelf, others⟩ := p'
    refine ⟨?_, ?_⟩
    · show (checkMemberVal (fueledOps F) blockNames envAcc _ >>= _) = _
      rw [hcmv]
      simp only [Bind.bind, Except.bind]
      show (provisionRecs (fueledOps F) blockNames _ rest >>= _) = _
      rw [hrec]
      simp only [Bind.bind, Except.bind]
      exact h
    · have h' : (Except.ok ((envSelf, (cvA, mI, rP, rules) ::
          others) : Env × _) : Except CheckError _) = Except.ok p := h
      cases h'
      exact hwfS

/-- Transport `ConstWF` along lookup-presence monotonicity. -/
private theorem constWF_le {envA envB : Env}
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

/-- The recursor-group check, `wfOpsM` to pure, with the final
environment well-formed. -/
theorem checkIndRecs_wfimp {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo} {F : Nat} (henv₂ : EnvWF env₂)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (h : (checkIndRecs wfOpsM blockNames env₂ recs).val F = .ok env₃) :
    checkIndRecs (fueledOps F) blockNames env₂ recs = .ok env₃ ∧
      EnvWF env₃ := by
  unfold checkIndRecs at h ⊢
  by_cases hemp : recs.isEmpty = true
  · rw [if_pos hemp] at h ⊢
    have h' : (Except.ok env₂ : CheckM Env) = .ok env₃ := h
    cases h'
    exact ⟨rfl, henv₂⟩
  rw [if_neg hemp] at h ⊢
  dsimp only [] at h ⊢
  by_cases heqf : env₂.find? eqName = some eqA
  case neg =>
    rw [if_neg heqf] at h
    exact absurd h atF_throw_bind
  rw [if_pos heqf] at h ⊢
  try dsimp only [] at h
  obtain ⟨p, hprovW, h⟩ := atF_bind_ok h
  obtain ⟨envSelf, checked⟩ := p
  try dsimp only [] at h
  obtain ⟨hprov, henvSelf⟩ := provisionRecs_wfimp recs env₂ henv₂ hprovW
  have hProv := provisionRecs_facts recs env₂ (envSelf, checked)
    hprov hbn
  -- the rule-checking fold, `wfOpsM` to pure
  have hfold : ∀ (cs : List (ConstantVal × Nat × Nat × List RecRule)),
      (∀ c ∈ cs, c.1.type.hasFvar = false) →
      ∀ (acc : Env) {envO : Env},
      (cs.foldlM (fun (acc : Env)
          (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules wfOpsM env₂ envSelf
            (fun n => if blockNames.contains n then n.str "_model"
              else n) c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1
            0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1
            rules' :: acc.consts⟩ : Env)) acc).val F = .ok envO →
      cs.foldlM (fun (acc : Env)
          (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules (fueledOps F) env₂ envSelf
            (fun n => if blockNames.contains n then n.str "_model"
              else n) c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1
            0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1
            rules' :: acc.consts⟩ : Env)) acc = .ok envO := by
    intro cs
    induction cs with
    | nil =>
      intro _ acc envO hrun
      exact hrun
    | cons c cs ih =>
      intro hty acc envO hrun
      rw [List.foldlM_cons] at hrun ⊢
      obtain ⟨e₁, hstep, hrun⟩ := atF_bind_ok hrun
      obtain ⟨rules', hir, hstep⟩ := atF_bind_ok hstep
      have hir' := checkIotaRules_wfimp henv₂ henvSelf
        (hty c List.mem_cons_self) hir
      have hstep' : (⟨.recInfo c.1 c.2.1 c.2.2.1
          rules' :: acc.consts⟩ : Env) = e₁ := by
        have hs : (Except.ok (⟨.recInfo c.1 c.2.1 c.2.2.1
            rules' :: acc.consts⟩ : Env) :
            Except CheckError Env) = .ok e₁ := hstep
        exact Except.ok.inj hs
      show ((do
          let rules' ← checkIotaRules (fueledOps F) env₂ envSelf _
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1
            0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1
            rules' :: acc.consts⟩ : Env)) >>= _) = _
      rw [hir']
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      rw [hstep']
      exact ih (fun c' hc' => hty c' (List.mem_cons_of_mem _ hc'))
        e₁ hrun
  have htys : ∀ c ∈ checked, c.1.type.hasFvar = false := by
    intro c hc
    obtain ⟨-, -, -, -, htyf, -, -, -, -, -⟩ :=
      ProvFacts.mem_facts hProv c hc
    exact htyf
  have hpure := hfold checked htys env₂ h
  refine ⟨?_, ?_⟩
  · show (provisionRecs (fueledOps F) blockNames env₂ recs >>= _) = _
    rw [hprov]
    simp only [Bind.bind, Except.bind]
    exact hpure
  · -- the final environment is well-formed
    obtain ⟨zipped, hmap, hchain⟩ := rulesFold_inv checked env₂ env₃
      hpure
    rw [show checked = zipped.map Prod.fst from hmap.symm] at hProv htys
    have hswSh := chains_swapSh hProv hchain
      (SwapShList.of_eq env₂.consts)
    have hcorr := swapSh_find?_corr hswSh
    have hisoSome : ∀ n, (envSelf.find? n).isSome =
        (env₃.find? n).isSome := by
      intro n
      rcases hcorr n with heq | ⟨cv, a, b, e0, h₀, h₃, -⟩
      · rw [heq]
      · rw [h₀, h₃]
        rfl
    intro c₃ hc₃
    rcases rulesChain_mem hchain c₃ hc₃ with hc₂ | ⟨z, hz, rfl⟩
    · -- an untouched constant of the base environment
      refine constWF_le (fun n hn => ?_) (henv₂ c₃ hc₂)
      rw [← hisoSome n]
      cases hf2 : env₂.find? n with
      | none =>
        rw [hf2] at hn
        exact nomatch hn
      | some ci₂ =>
        rw [ProvFacts.find?_preserved hProv n ci₂ hf2]
        rfl
    · -- an installed recursor of the chain
      have hz1 : z.1 ∈ zipped.map Prod.fst := List.mem_map_of_mem hz
      obtain ⟨-, -, -, -, htyf, htyb, htlp, htres, -, -⟩ :=
        ProvFacts.mem_facts hProv z.1 hz1
      have hkits := checkIotaRules_inv 0 _ _
        (RulesChain.mem_facts hchain z hz)
      refine constWF_intro htyf htlp ?_ htyb
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
        · intro lvls pins hf
          obtain ⟨hmi, hlvls, hpins, hshape, -⟩ := hnest lvls pins hf
          refine ⟨by rw [← e2, ← e3]; exact hmi,
            by rw [← e1]; exact hlvls, ?_, ?_⟩
          · intro pin hp
            obtain ⟨p1, p2, p3, p4⟩ := hpins pin hp
            exact ⟨p1, by rw [← e1]; exact p2,
              by rw [← Expr.constsResolve_congr hisoSome]; exact p3,
              by rw [← e2]; exact p4⟩
          · rw [← e1, ← e2]
            exact hshape

/-- The `checkIndMember` fold over a block, `wfOpsM` to pure. -/
private theorem foldIndMember_wfimp {blockNames : List Name}
    {caps : IndCaps} {F : Nat} :
    ∀ (block : List ConstantInfo) (env' : Env) {env₂ : Env},
      EnvWF env' →
      (block.foldlM (checkIndMember wfOpsM blockNames caps) env').val F =
        .ok env₂ →
      block.foldlM (checkIndMember (fueledOps F) blockNames caps) env' =
        .ok env₂ ∧ EnvWF env₂
  | [], env', env₂, henv', h => by
    have h' : (Except.ok env' : CheckM Env) = Except.ok env₂ := h
    cases h'
    exact ⟨rfl, henv'⟩
  | ci :: block, env', env₂, henv', h => by
    have h' : ((checkIndMember wfOpsM blockNames caps env' ci >>=
        fun env₁ => block.foldlM (checkIndMember wfOpsM blockNames caps)
          env₁ : FueledM Env)).val F = .ok env₂ := h
    rw [FueledM.atF_bind] at h'
    cases hm : (checkIndMember wfOpsM blockNames caps env' ci).val F with
    | error e => rw [hm] at h'; exact nomatch h'
    | ok env₁ =>
      rw [hm] at h'
      have h'' : (block.foldlM (checkIndMember wfOpsM blockNames caps)
          env₁).val F = .ok env₂ := h'
      obtain ⟨hp, henv₁⟩ := checkIndMember_wfimp henv' hm
      obtain ⟨hrest, hwf⟩ := foldIndMember_wfimp block env₁ henv₁ h''
      refine ⟨?_, hwf⟩
      show (checkIndMember (fueledOps F) blockNames caps env' ci >>=
        fun env₁ => block.foldlM (checkIndMember (fueledOps F) blockNames
          caps) env₁) = .ok env₂
      rw [hp]
      exact hrest

/-! ## The projection-function install fold -/

/-- One projection-install step, `wfOpsM` to pure, output well-formed:
the stored degenerate recursor's type and rule right-hand side are
fully re-checked by the projection stages, so its `ConstWF` needs no
annotation-preservation reasoning. -/
private theorem installProjFnStepE_wfimp {T ctorName : Name}
    {lps : List Name} {nP nF : Nat} {e e' : Env} {i F : Nat}
    (he : EnvWF e)
    (h : (installProjFnStep wfOpsM T ctorName lps nP nF e i).val F =
      .ok e') :
    installProjFnStep (fueledOps F) T ctorName lps nP nF e i = .ok e' ∧
      EnvWF e' := by
  have h := installProjFnStep_wfimp he h
  refine ⟨h, ?_⟩
  unfold installProjFnStep at h
  split at h
  · obtain ⟨cvj, mcv, hlk, pty, hty, hi, rhsA, hrule, ⟨_, hio⟩, heq⟩ :=
      checkProjFn_inv h
    subst heq
    obtain ⟨-, -, hres, hbv, hfv, hlp⟩ := checkProjTy_inv hty
    obtain ⟨raw, rb, cb, cbody, hraw, hrf, hrb, hann, halp, hrres, hrbv,
      hrfv, hsl, hsp, hdm⟩ := checkProjRule_inv hrule
    refine EnvWF.cons he (constWF_intro hfv hlp
      (Expr.constsResolve_mono hres) hbv
      (fun _ _ _ heq => nomatch heq) ?_)
    intro cvR mI' rP' rules'' heq r hr
    injection heq with h1 h2 h3 h4
    subst h1; subst h4
    rcases List.mem_singleton.mp hr with rfl
    refine ⟨hrfv, halp, Expr.constsResolve_mono hrres, hrbv, ?_⟩
    intro lvls pins hf
    cases hcond : Expr.recRulePlain pty nP nP nP <;>
      simp [hcond] at hf
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact he

/-- The projection-install fold, `wfOpsM` to pure. -/
private theorem foldProjFn_wfimp {T ctorName : Name} {lps : List Name}
    {nP nF F : Nat} :
    ∀ (idxs : List Nat) (e : Env) {e₂ : Env},
      EnvWF e →
      (idxs.foldlM (installProjFnStep wfOpsM T ctorName lps nP nF)
        e).val F = .ok e₂ →
      idxs.foldlM (installProjFnStep (fueledOps F) T ctorName lps nP nF)
        e = .ok e₂ ∧ EnvWF e₂
  | [], e, e₂, he, h => by
    have h' : (Except.ok e : CheckM Env) = Except.ok e₂ := h
    cases h'
    exact ⟨rfl, he⟩
  | i :: idxs, e, e₂, he, h => by
    have h' : ((installProjFnStep wfOpsM T ctorName lps nP nF e i >>=
        fun e₁ => idxs.foldlM (installProjFnStep wfOpsM T ctorName lps nP
          nF) e₁ : FueledM Env)).val F = .ok e₂ := h
    rw [FueledM.atF_bind] at h'
    cases hm : (installProjFnStep wfOpsM T ctorName lps nP nF e i).val F
      with
    | error err => rw [hm] at h'; exact nomatch h'
    | ok e₁ =>
      rw [hm] at h'
      have h'' : (idxs.foldlM (installProjFnStep wfOpsM T ctorName lps nP
          nF) e₁).val F = .ok e₂ := h'
      obtain ⟨hp, he₁⟩ := installProjFnStepE_wfimp he hm
      obtain ⟨hrest, hwf⟩ := foldProjFn_wfimp idxs e₁ he₁ h''
      refine ⟨?_, hwf⟩
      show (installProjFnStep (fueledOps F) T ctorName lps nP nF e i >>=
        fun e₁ => idxs.foldlM (installProjFnStep (fueledOps F) T ctorName
          lps nP nF) e₁) = .ok e₂
      rw [hp]
      exact hrest

/-- The template-install step, `wfOpsM`-run to pure run, preserving
environment well-formedness (the consed entry has the closed junk
`Prop` type). -/
private theorem installProjTemplateStepE_wfimp {T ctorName : Name}
    {lps : List Name} {nP nF : Nat} {e e₁ : Env} {i F : Nat}
    (he : EnvWF e)
    (h : (installProjTemplateStep T ctorName lps nP nF e i :
      FueledM _).val F = .ok e₁) :
    (installProjTemplateStep T ctorName lps nP nF e i : CheckM _)
      = .ok e₁ ∧ EnvWF e₁ := by
  rw [installProjTemplateStep_datF] at h
  refine ⟨h, ?_⟩
  revert h
  unfold installProjTemplateStep installProjTemplate
  split
  case isFalse =>
    intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ he
  case isTrue hfree =>
    split
    case h_2 =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ he
    case h_1 cvR mI2 rP2 rule heqR =>
      split
      case isFalse =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ he
      case isTrue hcond =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        refine h ▸ EnvWF.cons he ?_
        refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
        · intro _ _ _ heq
          exact nomatch heq
        · intro _ _ _ _ heq
          exact nomatch heq

/-- The template-install fold, `wfOpsM` to pure. -/
private theorem foldProjTemplates_wfimp {T ctorName : Name}
    {lps : List Name} {nP nF F : Nat} :
    ∀ (idxs : List Nat) (e : Env) {e₂ : Env},
      EnvWF e →
      (idxs.foldlM
        (installProjTemplateStep (m := FueledM) T ctorName lps nP nF)
        e).val F = .ok e₂ →
      idxs.foldlM
        (installProjTemplateStep (m := CheckM) T ctorName lps nP nF)
        e = .ok e₂ ∧ EnvWF e₂
  | [], e, e₂, he, h => by
    have h' : (Except.ok e : CheckM Env) = Except.ok e₂ := h
    cases h'
    exact ⟨rfl, he⟩
  | i :: idxs, e, e₂, he, h => by
    have h' : ((installProjTemplateStep T ctorName lps nP nF e i >>=
        fun e₁ => idxs.foldlM
          (installProjTemplateStep T ctorName lps nP nF) e₁ :
        FueledM Env)).val F = .ok e₂ := h
    rw [FueledM.atF_bind] at h'
    cases hm : (installProjTemplateStep T ctorName lps nP nF e i :
        FueledM _).val F with
    | error err => rw [hm] at h'; exact nomatch h'
    | ok e₁ =>
      rw [hm] at h'
      have h'' : (idxs.foldlM
          (installProjTemplateStep T ctorName lps nP nF) e₁ :
          FueledM _).val F = .ok e₂ := h'
      obtain ⟨hp, he₁⟩ := installProjTemplateStepE_wfimp he hm
      obtain ⟨hrest, hwf⟩ := foldProjTemplates_wfimp idxs e₁ he₁ h''
      refine ⟨?_, hwf⟩
      show (installProjTemplateStep T ctorName lps nP nF e i >>=
        fun e₁ => idxs.foldlM
          (installProjTemplateStep T ctorName lps nP nF) e₁ :
        CheckM Env) = .ok e₂
      rw [hp]
      exact hrest

/-! ## `checkIndDecl` and `checkDecl` -/

/-- A successful `wfOpsM` run of `checkIndDecl` over a well-formed
environment is the pure run at the same fuel. -/
theorem checkIndDecl_wfimp {env env₂ : Env} {block : List ConstantInfo}
    {F : Nat} (henv : EnvWF env)
    (h : (checkIndDecl wfOpsM env block).val F = .ok env₂) :
    checkIndDecl (fueledOps F) env block = .ok env₂ := by
  simp only [checkIndDecl] at h ⊢
  have hbnAll : ∀ ci ∈ block,
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
    simpa using this
  split at h
  case isFalse => exact absurd h atF_throw_bind
  rename_i hsplit
  rw [if_pos hsplit]
  try dsimp only [] at h
  split at h
  case _ cvT c0 cvC nP nF heq1 heq2 =>
    obtain ⟨caps, hcaps, h⟩ := atF_bind_ok h
    obtain rfl : indBlockCaps env cvT cvC nP nF = caps := by
      have hc : (Except.ok (indBlockCaps env cvT cvC nP nF) :
          Except CheckError IndCaps) = .ok caps := hcaps
      exact Except.ok.inj hc
    obtain ⟨env₁, hfoldW, h⟩ := atF_bind_ok h
    obtain ⟨hfold, henv₁⟩ := foldIndMember_wfimp _ env henv hfoldW
    obtain ⟨env₃, hrecsW, h⟩ := atF_bind_ok h
    obtain ⟨hrecs, henv₃⟩ := checkIndRecs_wfimp henv₁
      (fun ci hci => hbnAll ci (List.mem_filter.mp hci).1) hrecsW
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    rw [hfold]
    simp only [Except.bind]
    rw [hrecs]
    simp only [Except.bind]
    by_cases hguard : (List.range nF).all (fun j =>
        (env₃.find? (projFnName cvT.name j)).isNone) = true
    case neg =>
      rw [if_neg hguard] at h
      exact absurd h atF_throw_bind
    rw [if_pos hguard] at h ⊢
    obtain ⟨env₄, hartW, htplW⟩ := atF_bind_ok h
    obtain ⟨hart, henv₄⟩ := foldProjFn_wfimp (List.range nF) env₃ henv₃
      hartW
    obtain ⟨htpl, -⟩ := foldProjTemplates_wfimp (List.range nF) env₄
      henv₄ htplW
    show (_ >>= _ : CheckM Env) = _
    rw [hart]
    try simp only [Except.bind]
    exact htpl
  case _ =>
    try dsimp only [] at h
    obtain ⟨env₁, hfoldW, h⟩ := atF_bind_ok h
    obtain ⟨hfold, henv₁⟩ := foldIndMember_wfimp _ env henv hfoldW
    show (_ >>= _ : CheckM Env) = _
    rw [hfold]
    simp only [Bind.bind, Except.bind]
    exact (checkIndRecs_wfimp henv₁
      (fun ci hci => hbnAll ci (List.mem_filter.mp hci).1) h).1

/-- Successful pure `checkDefnVal` runs annotate the value and store
it (shape inversion for the structural-Nat certification's stored
value). -/
private theorem checkDefnVal_run_shape {env : Env} {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint} {F : Nat} {env2 : Env}
    (h : checkDefnVal (fueledOps F) env cv value hint = .ok env2) :
    ∃ value', annotateCore env F 0 value = .ok value' ∧
      value.hasFvar = false ∧
      env2 = ⟨.defnInfo cv value' hint :: env.consts⟩ := by
  unfold checkDefnVal at h
  dsimp only [] at h
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => rw [if_neg h1] at h; exact nomatch h
  rw [if_pos h1] at h
  by_cases h2 : value.hasFvar = true
  · rw [if_pos h2] at h; exact nomatch h
  rw [if_neg h2] at h
  revert h
  cases hann : annotateCore env F 0 value with
  | error e =>
    intro h
    rw [show CheckerOps.annotate (fueledOps F) env 0 value =
      annotateCore env F 0 value from rfl, hann] at h
    exact nomatch h
  | ok value' =>
    intro h
    rw [show CheckerOps.annotate (fueledOps F) env 0 value =
      annotateCore env F 0 value from rfl, hann] at h
    simp only [Bind.bind, Except.bind] at h
    refine ⟨value', rfl, Bool.not_eq_true _ ▸ h2, ?_⟩
    by_cases h3 : Expr.allLevelParamsDefined cv.levelParams value' = true
    case neg => rw [if_neg h3] at h; exact nomatch h
    rw [if_pos h3] at h
    by_cases h4 : Expr.constsResolve env value' = true
    case neg => rw [if_neg h4] at h; exact nomatch h
    rw [if_pos h4] at h
    revert h
    cases hvt : inferTypeCore env F 0 value' with
    | error e =>
      intro h
      rw [show CheckerOps.inferType (fueledOps F) env 0 value' =
        inferTypeCore env F 0 value' from rfl, hvt] at h
      exact nomatch h
    | ok vtype =>
      intro h
      rw [show CheckerOps.inferType (fueledOps F) env 0 value' =
        inferTypeCore env F 0 value' from rfl, hvt] at h
      simp only [Bind.bind, Except.bind] at h
      revert h
      cases hde : isDefEqCore env F 0 vtype cv.type with
      | error e =>
        intro h
        rw [show CheckerOps.isDefEq (fueledOps F) env 0 vtype cv.type =
          isDefEqCore env F 0 vtype cv.type from rfl, hde] at h
        exact nomatch h
      | ok b =>
        intro h
        rw [show CheckerOps.isDefEq (fueledOps F) env 0 vtype cv.type =
          isDefEqCore env F 0 vtype cv.type from rfl, hde] at h
        simp only [Bind.bind, Except.bind] at h
        cases b with
        | true =>
          simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
          exact h.symm
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          exact nomatch h

set_option maxHeartbeats 1600000 in
theorem checkDecl_wfimp {env env₂ : Env} {d : Declaration} {F : Nat}
    (henv : EnvWF env)
    (h : (checkDecl wfOpsM env d).val F = .ok env₂) :
    checkDecl (fueledOps F) env d = .ok env₂ := by
  cases d with
  | defnDecl cv value hint =>
    unfold checkDecl at h ⊢
    dsimp only [] at h ⊢
    obtain ⟨cvA, hccvW, h⟩ := atF_bind_ok h
    have hccv : checkConstantVal (fueledOps F) env cv = .ok cvA :=
      checkConstantVal_wfimp henv hccvW
    show (checkConstantVal (fueledOps F) env cv >>= _) = _
    rw [hccv]
    simp only [Bind.bind, Except.bind]
    obtain ⟨htf, -, -, -⟩ := cvA_type_facts hccv
    obtain ⟨env2, hdefW, h⟩ := atF_bind_ok h
    have hdefn : checkDefnVal (fueledOps F) env cvA value hint =
        .ok env2 := checkDefnVal_wfimp henv htf hdefW
    show (checkDefnVal (fueledOps F) env cvA value hint >>= _) = _
    rw [hdefn]
    simp only [Bind.bind, Except.bind]
    obtain ⟨value', hann, hvf, henv2⟩ := checkDefnVal_run_shape hdefn
    have hfind : env2.find? cvA.name =
        some (.defnInfo cvA value' hint) := by
      rw [henv2, Env.find?_cons]
      exact if_pos rfl
    have hval'f : value'.hasFvar = false :=
      not_hasFvar_of_fvarsBelow_zero
        ((annotateCore_WScoped F value hann
          (WScoped.of_not_hasFvar hvf)).fvarsBelow)
    have hv'fD : ∀ cv' v' h', env2.find? cvA.name =
        some (.defnInfo cv' v' h') → v'.hasFvar = false := by
      intro cv' v' h' hf
      rw [hfind] at hf
      simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf
      obtain ⟨-, rfl, -⟩ := hf
      exact hval'f
    by_cases h1 : natOpNames.contains cvA.name = true
    case neg =>
      rw [if_neg h1] at h ⊢
      by_cases h4 : natDivModNames.contains cvA.name = true
      case neg =>
        rw [if_neg h4] at h ⊢
        exact h
      rw [if_pos h4] at h ⊢
      obtain ⟨u, hpinW, h⟩ := atF_bind_ok h
      have hpin' := checkDivModPin_wfimp henv
        (List.contains_iff_mem.mp h4) hv'fD hpinW
      show (checkDivModPin (fueledOps F) env env2 cvA.name >>= _) = _
      rw [hpin']
      simp only [Bind.bind, Except.bind]
      exact h
    rw [if_pos h1] at h ⊢
    by_cases h2 : (natOpGuard env2 cvA.name &&
        (natOpDeps cvA.name).all (natOpStoredOk env2)) = true
    case neg => rw [if_neg h2] at h; exact absurd h atF_throw_bind
    rw [if_pos h2] at h ⊢
    rw [hfind] at h ⊢
    obtain ⟨ok, hcert, h⟩ := atF_bind_ok h
    have hsc : ∀ eq ∈ (natOpEquations 0 cvA.name).map
        (fun eq => (Expr.substConst0 cvA.name value' eq.1,
          Expr.substConst0 cvA.name value' eq.2)),
        eq.1.wscopedB 2 = true ∧ eq.2.wscopedB 2 = true := by
      intro eq heq
      obtain ⟨eq₀, heq₀, rfl⟩ := List.mem_map.mp heq
      obtain ⟨hs1, hs2⟩ := natOpEquations_wscopedB
        (by simpa using h1) eq₀ heq₀
      exact ⟨wscopedB_substConst0 hval'f _ hs1,
        wscopedB_substConst0 hval'f _ hs2⟩
    have hcert' := certifyNatEqs_wfimp henv hsc hcert
    show (certifyNatEqs (fueledOps F) env _ >>= _) = _
    rw [hcert']
    simp only [Bind.bind, Except.bind]
    by_cases h3 : ok = true
    case neg =>
      rw [if_neg h3] at h
      exact absurd h atF_throw_bind
    rw [if_pos h3] at h ⊢
    by_cases h4 : natDivModNames.contains cvA.name = true
    case neg =>
      rw [if_neg h4] at h ⊢
      exact h
    rw [if_pos h4] at h ⊢
    obtain ⟨u, hpinW, h⟩ := atF_bind_ok h
    have hpin' := checkDivModPin_wfimp henv
      (List.contains_iff_mem.mp h4) hv'fD hpinW
    show (checkDivModPin (fueledOps F) env env2 cvA.name >>= _) = _
    rw [hpin']
    simp only [Bind.bind, Except.bind]
    exact h
  | thmDecl cv value =>
    unfold checkDecl at h ⊢
    dsimp only [] at h ⊢
    obtain ⟨cvA, hccvW, h⟩ := atF_bind_ok h
    have hccv : checkConstantVal (fueledOps F) env cv = .ok cvA :=
      checkConstantVal_wfimp henv hccvW
    show (checkConstantVal (fueledOps F) env cv >>= _) = _
    rw [hccv]
    simp only [Bind.bind, Except.bind]
    obtain ⟨htf, -, -, -⟩ := cvA_type_facts hccv
    exact checkThmVal_wfimp henv htf h
  | opaqueDecl cv value =>
    unfold checkDecl at h ⊢
    dsimp only [] at h ⊢
    obtain ⟨cvA, hccvW, h⟩ := atF_bind_ok h
    have hccv : checkConstantVal (fueledOps F) env cv = .ok cvA :=
      checkConstantVal_wfimp henv hccvW
    show (checkConstantVal (fueledOps F) env cv >>= _) = _
    rw [hccv]
    simp only [Bind.bind, Except.bind]
    obtain ⟨htf, -, -, -⟩ := cvA_type_facts hccv
    exact checkOpaqueVal_wfimp henv htf h
  | axiomDecl cv =>
    unfold checkDecl at h ⊢
    dsimp only [] at h ⊢
    obtain ⟨cvA, hccvW, h⟩ := atF_bind_ok h
    have hccv : checkConstantVal (fueledOps F) env cv = .ok cvA :=
      checkConstantVal_wfimp henv hccvW
    show (checkConstantVal (fueledOps F) env cv >>= _) = _
    rw [hccv]
    simp only [Bind.bind, Except.bind]
    by_cases h1 : stdAxiomOk env cvA = true
    · rw [if_pos h1] at h ⊢
      exact h
    · rw [if_neg h1] at h
      exact nomatch h
  | basisDecl kind =>
    have heq : checkDecl wfOpsM env (.basisDecl kind) =
        checkDecl fueledOpsM env (.basisDecl kind) := rfl
    rw [heq, checkDecl_datF] at h
    exact h
  | indDecl block =>
    exact checkIndDecl_wfimp henv h

/-! ## The punchline (part two) -/

/-- Under `EnvWF env` — supplied by the environment model at the
consistency layer — a successful cached `checkDecl` run is reproduced
by the pure fueled checker at some fuel. -/
theorem checkDecl_bridge {env env₂ : Env} {d : Declaration}
    (henv : EnvWF env) (h : checkDecl cachedOps env d = .ok env₂) :
    ∃ F, checkDecl (fueledOps F) env d = .ok env₂ := by
  obtain ⟨F, hF⟩ := checkDecl_wfOpsM_bridge h
  exact ⟨F, checkDecl_wfimp henv hF⟩

end Setlec
