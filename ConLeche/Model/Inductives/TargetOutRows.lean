module

public import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.ContInstRule
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.SumRecRead
import ConLeche.Semantics.Tower.TowerIntro

public section

/-!
# The rule rows at an OUTSIDE class, at the base frame (lane NESTIND, session 5)

`tgtOutDec_core` (`TargetOutRow.lean`) is the decoding row at an outside
class under the class's reading premises; `tgtOutSat`
(`TargetOutSat.lean`) discharges them from the run.  This file fixes the
class's parameter readings as a FUNCTION of the level valuation
(`tgtOutDsa`, the unique reading of the major's parameters at the rule
prefix), factors the rule's opening of the instantiated constructor
(`tgtOutOpen`), and states the rows the graph producer reads at an
outside class, at the base frame and at a prefix spine fitting the
rule's prefix domains (the class's index set is guarded by that fit,
as a member class's is, `blockRecIs`):

* `tgtOutSpF` — `hspF`: a hole fit of the recorded constructor at the
  carrier of the key frame fits the rule's field domains;
* `tgtOutDec` — `hdec`: a spine fitting the rule's prefix and field
  domains hole-fits the constructor at the tuple of the class's index
  expressions, and the fired spine reads to the injection.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **An outside major's parameters, read at the rule prefix** — a
function of the level valuation (the reading is unique,
`denoteMetaSpine_eq_map`). -/
@[expose] def tgtOutDsa (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (p : BlockShape)
    (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat) (j : Nat) :
    List AnnotTerm :=
  (tgtMajor out j).ds.map fun x => (denoteMeta acval envC ψ (tgtRP p j) x).getD default

/-- A read spine is the list of its arguments' readings. -/
theorem denoteMetaSpine_eq_map {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      vs = as.map fun x => (denoteMeta acval env φ d x).getD default
  | [], _, .nil => rfl
  | _ :: _, _, .cons ha hs => by
    rw [List.map_cons, ha, Option.getD_some, ← denoteMetaSpine_eq_map hs]

section Rows

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {p : BlockShape}
  {outside nested : Bool} {block : List ConstantInfo} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- **The rule's opening of the instantiated container constructor**
(the setup `tgtOutDec_core` performs, factored): at the `(j, i)`-th rule
of an outside class, at the class's reading, the fired constructor is
`D`'s `(mm, i)`, its level parameters the inductive's, and the rule's
field domains are the recorded fields substituted by `instTau`. -/
theorem tgtOutOpen
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) p outside nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI)
    (hul : (tgtMajor out j).lvls.length = cvI.levelParams.length)
    (hds : ∀ x ∈ (tgtMajor out j).ds, Expr.WScoped (tgtRP p j) x ∧ x.looseBVarsBounded 0 = true)
    (ψ : Name → Nat) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mpC.base2.acval envC ψ (tgtRP p j) (tgtMajor out j).ds dsa)
    (hlenP : (D.params (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)).length
      = (tgtMajor out j).ds.length) :
    i < D.nctors mm ∧ cA.1.levelParams = cvI.levelParams ∧
      (∀ mm', mm' < D.k → ∃ cv caps, envC.find? (D.member mm') = some (.indInfo cv caps) ∧
        cv.levelParams = cvI.levelParams) ∧
      ∃ (ab : List (Nat × Nat × AnnotTerm)) (Tys : List AnnotTerm), Tys.length = D.k ∧
        (∀ mm', mm' < D.k → ∃ cvm caps, envC.find? (D.member mm') = some (.indInfo cvm caps) ∧
          denoteMeta mpC.base2.acval envC
              (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) 0 cvm.type
            = some (Tys.getD mm' default)) ∧
        FieldsEqOn V (D.params (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
            ++ Tys).reverse (ab.map (·.2.2))
          (D.fields (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) mm i) ∧
        ab.length = cA.2 ∧
        tgtFdomsAV p out mpC.base2.acval envC ψ j i
          = (AnnotTerm.substTele (instTau mpC ψ D (tgtMajor out j).lvls (tgtRP p j)
              (tgtMajor out j).ds) 0 ab).map (·.2.2) := by
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, ⟨E⟩, _, _, hFld, _, _, _⟩ :=
    targetRuleAtG R hr hcA hrhs
  subst hMaj
  have hnd := hcl.hnd
  obtain ⟨-, -, -, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by
    rw [← tgtRs_ctors hr]; exact hcA
  have hiL : i < (tgtMajor out j).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
  have hcAi : (tgtMajor out j).ctors[i] = cA := (List.getElem?_eq_some_iff.mp hcAM).2
  have hiD : i < D.nctors mm := by rw [← hcl.hlen]; exact hiL
  have hfc0 := hcl.hctor i hiL
  rw [hcAi] at hfc0
  obtain ⟨-, -, -, hcrd⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv', nPc', nF', hf', -, hlpsC, -⟩ := hcrd.2 mm hcl.hmm i hiD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ (tgtMajor out j).nPc = nPc' ∧ cA.2 = nF' := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hlpsI : cvI.levelParams = cA.1.levelParams := by
    obtain ⟨caps, hfI⟩ := hcl.hfind
    obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC mm hcl.hmm
    rw [hcl.hmem, hfI] at hfm
    injection hfm with h; injection h with h1 _
    rw [h1, hlm]
  have hlps : ∀ mm', mm' < D.k → ∃ cv caps, envC.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = cvI.levelParams := by
    rw [hlpsI]; exact hlpsC
  refine ⟨hiD, hlpsI.symm, hlps, ?_⟩
  rw [hlpsI] at hnd hul hlenP ⊢
  rw [hlpsI] at hlps
  have hfc : envC.find? (D.ctorName mm i)
      = some (.ctorInfo cA.1 (tgtMajor out j).ds.length cA.2) := by
    rw [hdsLen]; exact hfc0
  have hcr : ConLeche.instPisWith (tgtMajor out j).ds
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls) = some Q.crest := by
    have h := Q.hcrest
    simpa [ConLeche.targetCtorAt, hMo] using h
  have hRP : tgtRP p j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hfld : ConLeche.openPisAtFvars cA.2 Q.crest (tgtRP p j) = some (Q.fvsF, Q.cbody) := by
    rw [hRP]; exact Q.hfld
  obtain ⟨-, ab, ⟨Tys, hlT, hTys, hEq⟩, hlab, hrdF, -, -⟩ :=
    instCtor_open mpC hcl.hD hcl.hnN hcl.hkN hlps hnd hul hds hdsa hlenP hcl.hmm hiD hfc hcr hfld
  refine ⟨ab, Tys, hlT, hTys, hEq, hlab, ?_⟩
  rw [tgtFdomsAV, ← hFld, hrdF]

/-- **Row `hspF` at an outside class**: at a prefix spine fitting the
rule's prefix domains, a hole fit of `D`'s constructor `(mm, i)` at the
carrier of the key frame fits the rule's field domains. -/
theorem tgtOutSpF (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (ρ : Nat → V)
    {xs : List V}
    (hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j) xs)
    {t : V} {fs : List V}
    (hf : D.HFits (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
      (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
        (tgtRP pp.toBlockShape j) (consList xs ρ))
      (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
        (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs ρ))) t mm i fs) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i) (xs ++ fs) := by
  obtain ⟨dsa, hdsa, hul, hds, hlenP, hsatF⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  have hs := hsatF ρ xs hpref
  obtain ⟨hiD, -, hlps, ab, Tys, hlT, hTys, hEq, hlab, hfd⟩ :=
    tgtOutOpen R hr hcA hrhs hMo hcl hul hds ψ hdsa hlenP
  obtain ⟨hF, -⟩ := instCtor_fit mpC hcl.hD hcl.hnN hcl.hkN hlps hcl.hnd hul hds hdsa hlenP
    hcl.hmm hiD hlT hTys hEq hlab hs
  refine SpineFit.append hpref ?_
  rw [hfd]
  exact (hF fs).mpr hf.2.1

/-- **Row `hdec` at an outside class**: a spine fitting the rule's
prefix and field domains hole-fits `D`'s constructor `(mm, i)` at the
carrier of the key frame, at the tuple of the class's index expressions
(`tgtOutEs`), and the fired spine reads to the injection. -/
theorem tgtOutDec (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (ρ : Nat → V)
    {xs fs : List V}
    (hxl : xs.length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length)
    (hfit : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i) (xs ++ fs)) :
    D.HFits (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
        (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs ρ))
        (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
          (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
            (tgtRP pp.toBlockShape j) (consList xs ρ)))
        (tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
          ((tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP pp.toBlockShape j) ψ i).map
            (interp V (consList (xs ++ fs) ρ))))
        mm i fs ∧
      interp V (consList (xs ++ fs) ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i)
        = D.inj (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) mm i fs := by
  obtain ⟨dsa, hdsa, hul, hds, hlenP, hsatF⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  obtain ⟨as₁, as₂, heq, hp, hf⟩ := spineFit_append_inv hfit
  have hl₁ : as₁.length = xs.length := by rw [hp.length_eq, hxl]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl₁
  have hlenPd := blockRulePdomsAV_length (V := V) hμ mpC h hr ψ
  exact tgtOutDec_core R hr hcA hrhs hMo hcl hul hds ψ hdsa hlenP
    (by rw [hxl, hlenPd]; rfl) (hsatF ρ _ hp) hf

end Rows

end ConLeche.Model
