import Setlec.Verify.BridgeDecl
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
    (h6 : ∀ cv nP nM nm ni rules, c = .recInfo cv nP nM nm ni rules →
      ∀ r, r ∈ rules →
        (RecRule.rhs r).hasFvar = false ∧
        (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
        (RecRule.rhs r).constsResolve env = true ∧
        (RecRule.rhs r).looseBVarsBounded 0 = true) :
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
    {f : Name → Name} {cvA : ConstantVal} {nP nm ni : Nat} {r : RecRule}
    (h : RuleChecked F env env₀ f cvA nP nm ni r) :
    (RecRule.rhs r).hasFvar = false ∧
    (RecRule.rhs r).looseBVarsBounded 0 = true ∧
    (RecRule.rhs r).allLevelParamsDefined cvA.levelParams = true ∧
    (RecRule.rhs r).constsResolve env₀ = true := by
  obtain ⟨cvj, cnF, raw, rb, tb, cb, sb, rbody, tybody, cbody, sbody,
    thmName, cvt, tval, ℓA, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  exact ⟨h6, h7, h19, h20⟩

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
  simp only [checkIndMember] at h
  rw [checkConstantVal_wfeq henv', FueledM.atF_bind,
    checkConstantVal_datF] at h
  cases hccv : checkConstantVal (fueledOps F) env' ci.toConstantVal with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cvA =>
    rw [hccv] at h
    simp only [Bind.bind, Except.bind] at h
    obtain ⟨htf, htp, htr, htb⟩ := cvA_type_facts hccv
    have henvSelf : ∀ a b c d,
        EnvWF ⟨.recInfo cvA a b c d [] :: env'.consts⟩ := by
      intro a b c d
      refine EnvWF.cons henv' (constWF_intro htf htp
        (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) ?_)
      intro cvR nP' nM' nm' ni' rules' heq r hr
      injection heq with h1 h2 h3 h4 h5 h6
      subst h6
      exact nomatch hr
    simp only [fun a b c d =>
      checkIotaRules_wfeq henv' (henvSelf a b c d)] at h
    have hpure : checkIndMember (fueledOps F) blockNames caps env' ci =
        .ok env₁ := by
      rw [← checkIndMember_datF]
      simp only [checkIndMember]
      rw [FueledM.atF_bind, checkConstantVal_datF, hccv]
      simp only [Bind.bind, Except.bind]
      exact h
    refine ⟨hpure, ?_⟩
    obtain ⟨cvA', cvm, mval, hmcvm, hccv', hms, hfm, hlps, hren, hcases⟩ :=
      checkIndMember_inv hpure
    obtain rfl : cvA = cvA' := by
      rw [hccv'] at hccv
      injection hccv with hAA
      exact hAA.symm
    rcases hcases with ⟨⟨cv, caps', rfl⟩, rfl⟩ |
      ⟨cv, nP, nF, rfl, rfl⟩ |
      ⟨cv, nP, nm, ni, rules, rules', rfl, hall, heqf, hcir, rfl⟩
    · exact EnvWF.cons henv' (constWF_intro htf htp
        (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq))
    · exact EnvWF.cons henv' (constWF_intro htf htp
        (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq))
    · have hrc := checkIotaRules_inv 0 rules rules' hcir
      refine EnvWF.cons henv' (constWF_intro htf htp
        (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) ?_)
      intro cvR nP' nM' nm' ni' rules'' heq r hr
      injection heq with h1 h2 h3 h4 h5 h6
      subst h1; subst h6
      obtain ⟨hf1, hf2, hf3, hf4⟩ := ruleChecked_rhs_facts (hrc r hr)
      refine ⟨hf1, hf3, ?_, hf2⟩
      rw [Expr.constsResolve_congr
        (env₁ := ⟨.recInfo cvA nP 1 nm ni rules' :: env'.consts⟩)
        (env₂ := ⟨.recInfo cvA nP 1 nm ni [] :: env'.consts⟩)
        (fun n => find?_isSome_cons_swap
          (c₁ := .recInfo cvA nP 1 nm ni rules')
          (c₂ := .recInfo cvA nP 1 nm ni []) rfl n)]
      exact hf4

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
private theorem installProjFnStep_wfimp {T ctorName : Name}
    {lps : List Name} {nP nF : Nat} {e e' : Env} {i F : Nat}
    (he : EnvWF e)
    (h : (installProjFnStep wfOpsM T ctorName lps nP nF e i).val F =
      .ok e') :
    installProjFnStep (fueledOps F) T ctorName lps nP nF e i = .ok e' ∧
      EnvWF e' := by
  rw [installProjFnStep_wfeq he, installProjFnStep_datF] at h
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
    intro cvR nP' nM' nm' ni' rules'' heq r hr
    injection heq with h1 h2 h3 h4 h5 h6
    subst h1; subst h6
    rcases List.mem_singleton.mp hr with rfl
    exact ⟨hrfv, halp, Expr.constsResolve_mono hrres, hrbv⟩
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
      obtain ⟨hp, he₁⟩ := installProjFnStep_wfimp he hm
      obtain ⟨hrest, hwf⟩ := foldProjFn_wfimp idxs e₁ he₁ h''
      refine ⟨?_, hwf⟩
      show (installProjFnStep (fueledOps F) T ctorName lps nP nF e i >>=
        fun e₁ => idxs.foldlM (installProjFnStep (fueledOps F) T ctorName
          lps nP nF) e₁) = .ok e₂
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
  split at h
  case _ cvT c0 cvC nP nF heq1 heq2 =>
    have h' : ((block.foldlM (checkIndMember wfOpsM (block.map (·.name))
        (indBlockCaps env cvT cvC nP nF)) env >>= fun env₂' =>
        (if (List.range nF).all (fun j =>
            (env₂'.find? (projFnName cvT.name j)).isNone) = true then
          (List.range nF).foldlM (installProjFnStep wfOpsM cvT.name
            cvC.name cvT.levelParams nP nF) env₂'
        else throw (.invalid "projection name family taken"))
        : FueledM Env)).val F = .ok env₂ := h
    rw [FueledM.atF_bind] at h'
    cases hfold : (block.foldlM (checkIndMember wfOpsM
        (block.map (·.name)) (indBlockCaps env cvT cvC nP nF)) env).val F
      with
    | error e => rw [hfold] at h'; exact nomatch h'
    | ok env₂' =>
      rw [hfold] at h'
      simp only [Bind.bind, Except.bind] at h'
      obtain ⟨hp, henv₂'⟩ :=
        foldIndMember_wfimp block env henv hfold
      by_cases hguard : (List.range nF).all (fun j =>
          (env₂'.find? (projFnName cvT.name j)).isNone) = true
      · rw [if_pos hguard] at h'
        have h'' : ((List.range nF).foldlM (installProjFnStep wfOpsM
            cvT.name cvC.name cvT.levelParams nP nF) env₂').val F =
            .ok env₂ := h'
        obtain ⟨hpp, -⟩ := foldProjFn_wfimp (List.range nF) env₂' henv₂' h''
        show (block.foldlM (checkIndMember (fueledOps F)
            (block.map (·.name)) (indBlockCaps env cvT cvC nP nF)) env >>=
          fun env₂' =>
            (if (List.range nF).all (fun j =>
                (env₂'.find? (projFnName cvT.name j)).isNone) = true then
              (List.range nF).foldlM (installProjFnStep (fueledOps F)
                cvT.name cvC.name cvT.levelParams nP nF) env₂'
            else throw (.invalid "projection name family taken"))) =
          .ok env₂
        rw [hp]
        show (if (List.range nF).all (fun j =>
            (env₂'.find? (projFnName cvT.name j)).isNone) = true then
          (List.range nF).foldlM (installProjFnStep (fueledOps F) cvT.name
            cvC.name cvT.levelParams nP nF) env₂'
        else throw (.invalid "projection name family taken")) = .ok env₂
        rw [if_pos hguard]
        exact hpp
      · rw [if_neg hguard] at h'
        exact nomatch h'
  case _ =>
    exact (foldIndMember_wfimp block env henv h).1

/-- A successful `wfOpsM` run of `checkDecl` over a well-formed
environment is the pure run at the same fuel: every operation call a
non-inductive declaration makes is at the input environment itself;
inductive blocks go through `checkIndDecl_wfimp`. -/
theorem checkDecl_wfimp {env env₂ : Env} {d : Declaration} {F : Nat}
    (henv : EnvWF env)
    (h : (checkDecl wfOpsM env d).val F = .ok env₂) :
    checkDecl (fueledOps F) env d = .ok env₂ := by
  cases d with
  | defnDecl cv value hint =>
    have heq : checkDecl wfOpsM env (.defnDecl cv value hint) =
        checkDecl fueledOpsM env (.defnDecl cv value hint) := by
      unfold checkDecl
      simp only [checkConstantVal_wfeq henv, checkDefnVal_wfeq henv,
        certifyNatEqs_wfeq henv]
    rw [heq, checkDecl_datF] at h
    exact h
  | thmDecl cv value =>
    have heq : checkDecl wfOpsM env (.thmDecl cv value) =
        checkDecl fueledOpsM env (.thmDecl cv value) := by
      unfold checkDecl
      simp only [checkConstantVal_wfeq henv, checkThmVal_wfeq henv]
    rw [heq, checkDecl_datF] at h
    exact h
  | opaqueDecl cv value =>
    have heq : checkDecl wfOpsM env (.opaqueDecl cv value) =
        checkDecl fueledOpsM env (.opaqueDecl cv value) := by
      unfold checkDecl
      simp only [checkConstantVal_wfeq henv, checkOpaqueVal_wfeq henv]
    rw [heq, checkDecl_datF] at h
    exact h
  | axiomDecl cv =>
    have heq : checkDecl wfOpsM env (.axiomDecl cv) =
        checkDecl fueledOpsM env (.axiomDecl cv) := by
      unfold checkDecl
      simp only [checkConstantVal_wfeq henv]
    rw [heq, checkDecl_datF] at h
    exact h
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
