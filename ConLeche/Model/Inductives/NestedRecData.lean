module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockDeclRun
public import ConLeche.Model.Inductives.TargetIhData
public import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.TargetRuleData
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutGrade
import ConLeche.Model.Inductives.TargetOutConv
import ConLeche.Model.Inductives.TargetOutCa
import ConLeche.Model.Inductives.ContInst
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.CheckerF

public section

/-!
# The nested recursors' rule contract at every fired pair (lane RECREST, `data`)

`NestedRecRest.data` (L5/O12): `BlockRuleDataB` at the target rule data
at every `(recursor, constructor)` pair whose stored rule fires.  The
contract's five conjuncts split as the `eqB` rows did:

* the FIRST three (the frame's fit, the index readings, the fired
  spine) are about the rule's DATA — at a member major the block's
  (`blockRuleFit_tele`, `blockRuleHes_run`, `blockRuleHmk_run` at one
  recursor, through `tgt…_eq_block`), at an outside major the
  instantiated container constructor's (the NESTIND outside kit);
* the last two (the residue at the `ih` values, the λ-tower's fit) are
  about the rule's RIGHT-HAND SIDE and hold at ANY major from the
  target rule run (`tgtRuleResidueG`, `tgtRuleTowerFitG` below), given
  the first conjunct, the field readings (`hdF`) and the frame's
  grading (`hokPF`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section AnyMajor

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {outside nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC}

/-! ## The frame's field readings and grading, at any major -/

/-- **The field readings at an OUTSIDE major** — the instantiated
container constructor's opening (`tgtOutOpen`). -/
theorem tgtHdF_out (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none) (ψ : Name → Nat) :
    ∀ (l : Nat) (x : Expr), (tgtFieldFvs pp.toBlockShape out j i)[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
        = some ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default) := by
  obtain ⟨rc', u', -, ⟨E⟩⟩ := targetEntryAt R hr
  obtain ⟨D, mm, cvI, hcl⟩ := tgtOutCls_of hcov E hMo
  obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSatW hμ mpC hcov h R hr hMo hcl ψ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrd, -⟩ :=
    tgtOutOpen R hr hcA hrhs hMo hcl hul hds ψ hdsa hlenP
  exact hrd

/-- **The frame's grading at an OUTSIDE major**: the prefix by the
recursor type's tower (`blockRulePdomsAV_graded`), the fields by the
instantiated constructor's graded reading (`tgtOutCrestWd`), whose
Π-tower's domains they are (`tgtOutOpen`). -/
theorem tgtHokPF_out (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none) (ψ : Name → Nat) :
    ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default) := by
  obtain ⟨rc', u', -, ⟨E⟩⟩ := targetEntryAt R hr
  obtain ⟨D, mm, cvI, hcl⟩ := tgtOutCls_of hcov E hMo
  obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSatW hμ mpC hcov h R hr hMo hcl ψ
  obtain ⟨-, -, -, ab, -, -, -, -, hlab, hfdE, -, hcrR⟩ :=
    tgtOutOpen R hr hcA hrhs hMo hcl hul hds ψ hdsa hlenP
  have hlenPd := blockRulePdomsAV_length hμ mpC h hr ψ
  intro l hl σ ys hys
  rcases Nat.lt_or_ge l (pp.toBlockShape.rulePrefixAt j) with hlt | hge
  · rw [List.take_append_of_le_length (by omega)] at hys
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD]
    exact blockRulePdomsAV_graded hμ mpC h hr ψ l hlt σ ys hys
  · obtain ⟨q, rfl⟩ : ∃ q, l = pp.toBlockShape.rulePrefixAt j + q :=
      ⟨l - pp.toBlockShape.rulePrefixAt j, by omega⟩
    rw [← hlenPd, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left] at hys
    rw [List.getD_eq_getElem?_getD, ← hlenPd, List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
    obtain ⟨ys₁, ys₂, rfl, hy1, hy2⟩ := spineFit_append_inv hys
    rw [consList_append]
    have hC := tgtOutCrestWd hμ hcov h R hr hcA hrhs hMo hcl ψ σ hy1 hcrR
    rw [hfdE] at hy2 ⊢
    exact wdV_mkPisAV_dom hC q (by rw [substTele_length, hlab]; omega) ys₂ hy2

/-! ## The λ-tower's fit, at any major -/

/-- **`BlockRuleDataB`'s FIFTH conjunct at ANY major** (`blockRuleTowerFit_run`
at the target rule run): the rule's λ-domains, read, fit wherever the
openers' stored types do — the check's own binder-by-binder comparison
(`TargetRuleRun.hG2`) through `twoStageOpeners_spineFit`, the openers'
readings and gradings at the frame (`hdF`, `hokPF`), the λ-domains'
off the graded reading of the rule (`hokRa`). -/
theorem tgtRuleTowerFitG (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hDs : TgtDsOk envC (tgtRP pp.toBlockShape j) (tgtPrefFvs pp.toBlockShape out j)
      (tgtMajor out j).ds)
    (hCf : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).looseBVarsBounded 0 = true)
    {ψ : Name → Nat} {acv : Name → (Name → Nat) → AnnotTerm} {env₃ : Env} {Ra : AnnotTerm}
    (hread : denoteMeta acv env₃ ψ 0 rhs = some Ra)
    (hokRa : ∀ σ : Nat → V, WellDenotedV V σ Ra)
    (hcross : ∀ (l : Nat) (e : Expr), ConstsBound envC e →
      denoteMeta mpC.base2.acval envC ψ l e = denoteMeta acv env₃ ψ l e)
    (hdF : ∀ (l : Nat) (x : Expr), (tgtFieldFvs pp.toBlockShape out j i)[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
        = some ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default))
    (hokPF : ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default))
    {ρ : Nat → V} {as : List V}
    (hfit : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i) as) :
    ∀ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A →
      lds.length = pp.toBlockShape.rulePrefixAt j + cA.2 →
      SpineFit ρ (lds.map (·.2)) as := by
  intro lds A hlam hldslen
  obtain ⟨rc, rhs0, M, Q, hrP, -, hFld, -, -, -, hMaj, hPref⟩ :=
    tgtRuleAt_factsG (fe := ConLeche.mkFEnv envC) h R hr hcA hrhs
  subst hMaj
  have hds : TgtDsOk envC rc.rP Q.fvsPref (tgtMajor out j).ds := by
    rw [hPref, hrP]; exact hDs
  -- the stored recursor type and rule
  obtain ⟨hfvR, -, -, hbR, hallRhs⟩ := ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  obtain ⟨hfvRhs, -, -, hbRhs⟩ := hallRhs rhs (List.mem_of_getElem? hrhs)
  -- the instantiated constructor's scoping
  have hcr := Q.hcrest
  rw [ConLeche.instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨doms, crest'⟩, hinstC, hcr'⟩ := Option.map_eq_some_iff.mp hcr
  obtain rfl : crest' = Q.crest := hcr'
  have hwC : Expr.WScoped rc.rP Q.crest :=
    (instPisAt_WScoped (d := rc.rP) _ _ hinstC (Expr.WScoped.of_not_hasFvar hCf)
      (fun a ha => (hds a ha).1)).2
  have hbC : Q.crest.looseBVarsBounded 0 = true :=
    (ConLeche.Verify.instPisAt_bounded _ hinstC hCb (fun a ha => (hds a ha).2.1)).2
  have hleafC : ∀ lf ∈ Q.crest.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ Q.fvsPref := by
    intro lf hlf
    rcases ConLeche.Verify.instPisAt_leaves _ hinstC lf (Or.inr hlf) with hq | hq
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf] at hq; exact nomatch hq
    · obtain ⟨a, ha, hlfa⟩ := hq
      exact (hds a ha).2.2.2 lf hlfa
  -- lengths
  have hlenP : Q.fvsPref.length = rc.rP := ConLeche.Verify.openPisAtFvars_length _ Q.hpref
  have hlenF : Q.fvsF.length = cA.2 := ConLeche.Verify.openPisAtFvars_length _ Q.hfld
  have hlenPd : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
      = rc.rP := by rw [blockRulePdomsAV_length hμ mpC h hr ψ, hrP]
  have hlenFd : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length = cA.2 := by
    rw [tgtFdomsAV, readOpenedDoms_length_eq, ← hFld, hlenF]
  -- the rule's λ-tower, read
  obtain ⟨Γ, C, htele, hΓlen, -, hdoms₀⟩ :=
    instLamsAt_denotePTele (acval := acv) (env := env₃) (φ := ψ) _ Q.hlams
      (blockRuleOpeners_index Q.hpref Q.hfld) hread
  obtain ⟨lds₀, hmap, hT⟩ := lamTele_mkLamsAV htele
  have hsplen : (Q.fvsPref ++ Q.fvsF).length = rc.rP + cA.2 := by
    rw [List.length_append, hlenP, hlenF]
  have hlen₀ : lds₀.length = rc.rP + cA.2 := by
    have hq : (lds₀.map (·.2)).length = Γ.reverse.length := by rw [hmap]
    simp only [List.length_map, List.length_reverse] at hq
    rw [hq, hΓlen, hsplen]
  obtain ⟨rfl, rfl⟩ : lds = lds₀ ∧ A = C :=
    mkLamsAV_length_inj (by rw [hldslen, hlen₀, hrP]) (hlam ▸ hT)
  have hlenLd : Q.ldoms.length = rc.rP + cA.2 := by
    rw [ConLeche.Verify.instLamsAt_length _ Q.hlams, hsplen]
  -- the openers' readings
  have hdA : ∀ (l : Nat) (x : Expr), (Q.fvsPref ++ Q.fvsF)[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ l (Expr.fvarTypeD x)
        = some ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default) := by
    intro l x hx
    rcases Nat.lt_or_ge l Q.fvsPref.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hx
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      exact blockRulePdomsAV_reads hμ mpC h hr ψ (by rw [← hrP]; exact Q.hpref) l x hx
    · rw [List.getElem?_append_right hge, hlenP, hFld] at hx
      rw [hlenP] at hge
      have hq := hdF (l - rc.rP) x hx
      rw [← hrP, show rc.rP + (l - rc.rP) = l from by omega] at hq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlenPd,
        ← List.getD_eq_getElem?_getD]
      exact hq
  -- the tower's domains
  have hdB : ∀ l, l < rc.rP + cA.2 →
      denoteMeta mpC.base2.acval envC ψ l (Q.ldoms.getD l default)
        = some ((lds.map (·.2)).getD l default) := by
    intro l hl
    obtain ⟨x, hx⟩ : ∃ x, Q.ldoms[l]? = some x :=
      ⟨Q.ldoms[l]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hcb : ConstsBound envC x := by
      refine constsBound_of_constsResolve _ ?_
      have hres := Q.hldomsRes x (List.mem_of_getElem? hx)
      simp only [ConLeche.StructWalkers.plain] at hres
      rwa [ConLeche.constsResolveF_eq] at hres
    rw [List.getD_eq_getElem?_getD, hx, Option.getD_some, hcross l x hcb]
    have hd := hdoms₀ l x hx
    rw [Nat.zero_add] at hd
    rw [hd, hmap, getD_reverse_lt (by rw [hΓlen, hsplen]; exact hl), hΓlen]
  have hokB : ∀ l, l < rc.rP + cA.2 → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((lds.map (·.2)).take l) ys →
      WellDenotedV V (consList ys σ) ((lds.map (·.2)).getD l default) :=
    fun l hl σ ys hys =>
      mkLamsAV_doms_graded (b := A) (by rw [← hlam]; exact hokRa σ)
        (by rw [hlen₀]; exact hl) hys
  exact twoStageOpeners_spineFit (fuel := F) hμ mpC Q.hpref Q.hfld hfvR hbR hwC hbC hleafC
    Q.hlams hfvRhs hbRhs
    (by rw [List.length_append, hlenPd, hlenFd])
    (by rw [List.length_map, hlen₀]) hdA hdB
    (fun l hl => hokPF l (by rw [← hrP]; exact hl)) hokB
    (fun l hl => Q.hG2 l (by rw [List.length_map, hsplen]; exact hl))
    hfit

section Member

variable {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
  {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}

/-- **The field readings at a MEMBER major** — the constructors' record
(`blockRuleFdomsAV_eq`) through `tgtMember_eq_block`. -/
theorem tgtHdF_member
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR j) (hms : (tgtMajor out j).member.isSome = true)
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) (ψ : Name → Nat) :
    ∀ (l : Nat) (x : Expr), (tgtFieldFvs pp.toBlockShape out j i)[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
        = some ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default) := by
  obtain ⟨ms, hmsA, hctA, -⟩ := recStage_ctorsAt (hm := hm) h hr
  have hmemk : pp.toBlockShape.recTgtAt j
      < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hmsA).1
  have hcj : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt j))[i]? = some cA := by
    show (ctorsAs.getD _ [])[i]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk i cA hcj
  have hcd := blockCtorData_of_core hcore hcj
  have hCf : cA.1.type.hasFvar = false := (mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)).1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  obtain ⟨-, -, hfv, -⟩ := tgtMember_eq_block R hr hcA hrhs hms
  intro l x hx
  rw [tgtFdomsAV_eq_block R hr hcA hrhs hms]
  rw [hfv] at hx
  exact (blockRuleFdomsAV_eq (hm := hm) h hr hcA hrhs hcd hCf TE.nP_le ψ).2 l x hx

/-- **The frame's grading at a MEMBER major** (`blockRuleHokPF_run`
through `tgtFdomsAV_eq_block`). -/
theorem tgtHokPF_member (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    (hS : BlockCtorsStage (V := V) μ F (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hmr : BlockMembersRun mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.toBlockShape cvTas)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR j) (hms : (tgtMajor out j).member.isSome = true)
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) (ψ : Name → Nat) :
    ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default) := by
  rw [tgtFdomsAV_eq_block R hr hcA hrhs hms]
  exact blockRuleHokPF_run hμ h ⟨pk, uOfD, ppsOf, rfl⟩ hS hcore hmr j r hm hr i cA hcA ψ

end Member

end AnyMajor

end ConLeche.Model
