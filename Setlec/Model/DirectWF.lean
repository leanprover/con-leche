import Setlec.Verify.BridgeWfImp
import Setlec.Model.Extend

/-!
# The direct simple-structure install: environment well-formedness

`EnvWF` for the environments `checkDirectStruct` walks through — one
per installed constant.  Every fact is read off the stage inversions
of `Setlec/Model/DirectDecl.lean`; the two bridges that consume them
(`Setlec/Model/BridgeS.lean` for the shared-state driver,
`Setlec/Model/BridgeWF.lean` for the cached one) need the same
sequence, so it lives here once.
-/

namespace Setlec

/-- Introduction for `ConstWF` with the clause types spelled out (the
`thmInfo` clause defaulted, as every constant installed by the direct
path is an inductive-kind one). -/
theorem directConstWF {env : Env} {c : ConstantInfo}
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


/-- A checked inductive-kind cons is well-formed (its `ConstWF` is the
four type-slot facts; every value clause is refuted by the kind). -/
theorem envWF_cons_ind {env : Env} (henv : EnvWF env)
    {cvA : ConstantVal} {caps : IndCaps} {F : Nat} {cv : ConstantVal}
    (hccv : checkConstantVal (fueledOps F) env cv = .ok cvA) :
    EnvWF ⟨.indInfo cvA caps :: env.consts⟩ := by
  obtain ⟨htf, htp, htr, htb⟩ := checkConstantVal_typeWF hccv
  exact EnvWF.cons henv (directConstWF htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq))

/-- A checked constructor cons is well-formed. -/
theorem envWF_cons_ctor {env : Env} (henv : EnvWF env)
    {cvA : ConstantVal} {nP nF F : Nat} {cv : ConstantVal}
    (hccv : checkConstantVal (fueledOps F) env cv = .ok cvA) :
    EnvWF ⟨.ctorInfo cvA nP nF :: env.consts⟩ := by
  obtain ⟨htf, htp, htr, htb⟩ := checkConstantVal_typeWF hccv
  exact EnvWF.cons henv (directConstWF htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq))

/-- Stage 1 at the run level: the environment it produces is
well-formed and the stored type is closed. -/
theorem direct_ind_wf {env env₁ : Env} (henv : EnvWF env)
    {p : DirectParts} {cvTa : ConstantVal} {F : Nat}
    (h : checkDirectInd (fueledOps F) env p = .ok (env₁, cvTa)) :
    EnvWF env₁ ∧ cvTa.type.hasFvar = false := by
  obtain ⟨cvTa', bs, hccv, -, hv⟩ := checkDirectInd_inv h
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  exact ⟨envWF_cons_ind henv hccv, (checkConstantVal_typeWF hccv).1⟩

/-- Stage 2 at the run level. -/
theorem direct_ctor_wf {env₀ env env₂ : Env} (henv : EnvWF env)
    {p : DirectParts} {cvTa cvCa : ConstantVal} {F : Nat}
    (h : checkDirectCtor (fueledOps F) env₀ env p cvTa = .ok (env₂, cvCa)) :
    EnvWF env₂ ∧ cvCa.type.hasFvar = false ∧
      cvCa.type.looseBVarsBounded 0 = true := by
  obtain ⟨cvCa', cbs, fvsC, crestC, tfvs, trest, xFvs, hccv, -, -, -, -, -,
    -, -, hv⟩ := checkDirectCtor_inv h
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  obtain ⟨htf, -, -, htb⟩ := checkConstantVal_typeWF hccv
  exact ⟨envWF_cons_ctor henv hccv, htf, htb⟩

/-- Stage 3/4 at the run level: the recursor cons carrying its single
rule is well-formed (the rule's right-hand side facts come from
`checkDirectRule_inv`, the fire mode is never `.nested`). -/
theorem direct_rec_wf {env : Env} (henv : EnvWF env)
    {p : DirectParts} {cvCa cvRa : ConstantVal} {rhsA : Expr} {F G : Nat}
    (hcv : checkConstantVal (fueledOps F) env p.cvR = .ok cvRa)
    (hru : checkDirectRule (fueledOps G) env p cvCa cvRa = .ok rhsA) :
    EnvWF ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP,
        if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
          .plain else .inert, rhsA⟩] :: env.consts⟩ := by
  obtain ⟨htf, htp, htr, htb⟩ := checkConstantVal_typeWF hcv
  obtain ⟨rbs, fvsP, restR, cdomsP, crest, xFvs, crest2, ldoms, lrest,
    -, -, -, hrlp, hrres, hrbv, hrfv, -, -, -, -, -, -, -⟩ :=
    checkDirectRule_inv hru
  refine EnvWF.cons henv (directConstWF htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq) ?_)
  intro cvR' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e4
  rcases List.mem_singleton.mp hr with rfl
  refine ⟨hrfv, hrlp, Expr.constsResolve_mono hrres, hrbv, ?_⟩
  intro lvls pins hf
  cases hcond : Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP <;>
    simp [hcond] at hf

/-- One projection-function install of the direct path at the run
level: the environment it produces is well-formed. -/
theorem direct_proj_wf {env envOut : Env} (henv : EnvWF env)
    {T C : Name} {lps : List Name} {nP nF i F : Nat}
    {cvTa cvCa : ConstantVal}
    (h : checkDirectProj (fueledOps F) T C lps nP nF cvTa cvCa env i
      = .ok envOut) :
    EnvWF envOut := by
  obtain ⟨pty, ptyA, sty, u, fvsP, prest, sbs, sbody, sdom, tFvs, resid,
    tfv, cds, fn, fdom, fbody, fm, rhsA, -, -, -, -, hlp, hres, hbv, hfv,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hrule, rfl⟩ := checkDirectProj_inv h
  obtain ⟨raw, rb, cb, cbody, hraw, hrf, hrb, hann, halp, hrres, hrbv,
    hrfv, hsl, hsp, hdm, -⟩ := checkProjRule_inv hrule
  refine EnvWF.cons henv (directConstWF hfv hlp
    (Expr.constsResolve_mono hres) hbv
    (fun _ _ _ heq => nomatch heq) ?_)
  intro cvR' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e4
  rcases List.mem_singleton.mp hr with rfl
  refine ⟨hrfv, halp, Expr.constsResolve_mono hrres, hrbv, ?_⟩
  intro lvls pins hf
  cases hcond : Expr.recRulePlain ptyA nP nP nP <;> simp [hcond] at hf


end Setlec
