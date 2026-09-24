module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetRowCertsRun
import ConLeche.Model.Inductives.BlockRuleCertsRun
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.StructBits
import ConLeche.Model.Capstone
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InstList

public section

/-!
# The certificates at the target data, at one rule (lane RECLIB, row certs)

`BlockRuleCerts.of_segments` at the target check's `(c, j)`-th rule:
the prefix and field openings are today's (the two checks open the
same stored types), the `ih` openers are the target run's `ih`
variables, opened off a generated tower over their types
(`ihTeleOf`), the residue and the conclusion are the target run's
(`TargetRuleRun.hty`/`hdeq` at `bodyO`/`concl`).  The frame's grading
is today's on the prefix and the fields (`blockRuleHokPF_of`) and, on
the `ih` block, each `ih` type's own inference at the frame
(`targetCall_ihTy_graded`), lifted past the earlier slots; the
conclusion is the recursor type's peel (`blockRuleCaAt_run`) at the
target width, graded as today's (`blockRuleConclFitW_run`,
`blockRuleConclArgsW_run`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts TargetMajor
  TargetIh)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

omit [SetTheory V] in
theorem ihDomsLifted_length (Ts : List AnnotTerm) : (ihDomsLifted Ts).length = Ts.length := by
  simp [ihDomsLifted]

omit [SetTheory V] in
theorem ihDomsLifted_getD {Ts : List AnnotTerm} {q : Nat} (hq : q < Ts.length) :
    (ihDomsLifted Ts).getD q default = (Ts.getD q default).liftN q 0 := by
  rw [ihDomsLifted, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]
  rfl

/-- An `ih` variable is a free variable at one of the `ih` types. -/
theorem mem_ihFvarsAt {B : Nat} {tys : List Expr} {x : Expr} (hx : x ∈ ihFvarsAt B tys) :
    ∃ i ty, x = Expr.fvar i ty ∧ ty ∈ tys := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have hr' : r < tys.length := List.mem_range.mp hr
  refine ⟨B + r, tys.getD r default, rfl, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', Option.getD_some]
  exact List.getElem_mem hr'

/-- **`hokA` from two segments**: the first graded as a whole, the
second under the first's values. -/
theorem hokA_of_two {PF I : List AnnotTerm}
    (hPF : ∀ l, l < PF.length → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ (PF.take l) ys → WellDenotedV V (consList ys σ) (PF.getD l default))
    (hI : ∀ q, q < I.length → ∀ (σ : Nat → V) (zs ys : List V),
      SpineFit σ PF zs → SpineFit (consList zs σ) (I.take q) ys →
      WellDenotedV V (consList ys (consList zs σ)) (I.getD q default)) :
    ∀ l, l < PF.length + I.length → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((PF ++ I).take l) ys →
      WellDenotedV V (consList ys σ) ((PF ++ I).getD l default) := by
  intro l hl σ ys hys
  rcases Nat.lt_or_ge l PF.length with hlP | hlP
  · rw [List.take_append_of_le_length (by omega)] at hys
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlP, ← List.getD_eq_getElem?_getD]
    exact hPF l hlP σ ys hys
  · rw [List.take_append, List.take_of_length_le (by omega)] at hys
    obtain ⟨zs, ws, rfl, hzs, hws⟩ := spineFit_append_inv hys
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hlP, ← List.getD_eq_getElem?_getD,
      consList_append]
    exact hI (l - PF.length) (by omega) σ zs ws hzs hws

section Rows

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {envI : Env}

set_option maxHeartbeats 4000000 in
/-- **The certificates at the target data, at one rule**, at the base
field domains. -/
theorem tgtRuleCertsW_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F fe.env pp cvTas ctorsAs (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTas ctorsAs out)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (ψ : Name → Nat) {c : Nat} (hc : c < (tgtRs out).length) {j : Nat}
    (hj : j < blockRecNCt (tgtRs out) c) :
    BlockRuleCerts V mpC F ψ (pp.toBlockShape.rulePrefixAt c)
      (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).length
      (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
        fe.env ψ c j).length
      (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c)
      (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j)
      (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
        fe.env ψ c j)
      (tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
        fe.env ψ c j)
      (tgtCaAV μ F fe (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env pp ψ c j) := by
  -- `hokC`'s fit and arguments, at the target `ih` block (only its length matters)
  have hdnP : d.nP = pp.nP := by obtain ⟨_, _, _, _, rfl⟩ := hdR; rfl
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r → d.ctorsM (pp.toBlockShape.recTgtAt c) = r.2.2.2 := by
    obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := recStage_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hfit := blockRuleConclFitW_run (mpC := mpC) hμ h hcore hmr hM hdnP hctM ψ hc hj (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j)
  have hargs := blockRuleConclArgsW_run hμ h hdR hS hcore hmr ψ hc hj (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j)
  -- the grading of the prefix and the fields
  have hPF := blockRuleHokPF_run hμ h hdR hS hcore hmr
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  have hjr : j < (tgtRs out)[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, (tgtRs out)[c].2.2.2[j]? = some cA :=
    ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, (tgtRs out)[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hjr)⟩
  have hmemk : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
    (blockRecMajor_run (V := V) hμ mpC h hmr hr (fun _ => 0)).2.1
  have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt c))[j]? = some cA := by rw [hctM c _ hr]; exact hcA
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hcd := blockCtorData_of_core hcore hcj
  have hcdP := hcd
  rw [show (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).nP = pp.nP
    from rfl] at hcdP
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hcbC : ConstsBound fe.env cA.1.type := constsBound_of_constsResolve _ hwfC.2.2.1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hnP := TE.nP_le
  -- the target rule's run
  obtain ⟨rc, rhs0, M, Q, hrP, hct, hds, hbf, hTf, hTb, hTc, hle, hRT3, hPrefEq, hFldEq, hB,
    hFrEq, hAbs, hnPc, hlvls⟩ := tgtRuleAt_facts_major h R hr hcA hrhs
  -- today's openings of the same stored types, and today's conclusion
  obtain ⟨o₁, cpref, rbs', body', ldoms, lrest, h₁, hinstC, h₂, -⟩ :=
    blockRuleData_run h hr hcA hrhs
  obtain ⟨concl0, hpr⟩ := blockRuleConcl_run h hr hcA hrhs
  obtain ⟨hw₁, hb₁⟩ := recStage_tyClosed h hr
  have hb₂ : (blockRuleCrest pp.toBlockShape (tgtRs out) c j).looseBVarsBounded 0 = true :=
    (instPisAt_bounded _ hinstC hCb
      (fun a ha => openPisAtFvars_fvars_closed h₁ a (List.mem_of_mem_take ha))).2
  have hw₂ := blockRuleHw2_of h₁ hw₁ hCf hinstC
  -- the target frame's facts
  have hCf' : (ConLeche.targetCtorAt M cA.1).hasFvar = false := by rw [hct]; exact hCf
  have hCb' : (ConLeche.targetCtorAt M cA.1).looseBVarsBounded 0 = true := by rw [hct]; exact hCb
  have hCc' : ConstsBound fe.env (ConLeche.targetCtorAt M cA.1) := by rw [hct]; exact hcbC
  obtain ⟨hFr, hlbFQ, hcbFQ, hherQ⟩ := targetFrame_facts Q.hpref Q.hcrest hds Q.hfld hTf hTb hTc
    hCf' hCb' hCc'
  have hformer : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
    exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1
  have hscope := fun ih (hih : ih ∈ Q.ihs.toList) =>
    targetIh_scope hμ Q mpC.base2.wf hle hbf hFr hherQ hcbFQ hformer (fun c' => (hRT3 c').1) hih
  have hwf : TargetIhWF (ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP
      Q.fvsPref Q.fvsF Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
        pp.toBlockShape.large))) (rc.rP + cA.2) Q.ihs :=
    (targetAbstract_acc 0 _ #[] _ _ Q.habs).2 (fun r hr => absurd hr (by simp))
  have hfvEq := ihs_fv_eq hwf
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  have hin := Rules.RulesInputs.ofSem mpC ψ
  -- the target data, named
  have hihL : tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j
      = Q.ihs.toList := by rw [tgtIhL, ← hAbs]
  have hBc : tgtB pp.toBlockShape (tgtRs out) c j = pp.toBlockShape.rulePrefixAt c + cA.2 :=
    tgtB_at hr hcA
  have hIdE : (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j) = ihDomsLifted (ihTyReads mpC.base2.acval fe.env ψ
      (pp.toBlockShape.rulePrefixAt c + cA.2) Q.ihs.toList) := by
    rw [tgtIhdomsAV, hBc, hihL]
  have hIlen : (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j).length = Q.ihs.size := by
    rw [hIdE, ihDomsLifted_length]; simp [ihTyReads]
  have hpl : (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c).length = pp.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j).length = cA.2 := blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ
  have hTyLen : (Q.ihs.toList.map (·.ty)).length = Q.ihs.size := by simp
  -- the conclusion: the run's is today's
  have hcrestQ : Q.crest = blockRuleCrest pp.toBlockShape (tgtRs out) c j := by
    have hc0 := Q.hcrest
    rw [hct, hds, instPisWith_eq_instPisAt, hPrefEq, hinstC] at hc0
    exact (Option.some.inj hc0).symm
  have hcbQ : Q.cbody = blockRuleCbody pp.toBlockShape (tgtRs out) c j := by
    have h2 : ConLeche.openPisAtFvars cA.2 (blockRuleCrest pp.toBlockShape (tgtRs out) c j)
        (pp.toBlockShape.rulePrefixAt c) = some (Q.fvsF, Q.cbody) := by
      rw [← hcrestQ, ← hrP]; exact Q.hfld
    rw [h₂] at h2
    exact (Prod.mk.inj (Option.some.inj h2)).2.symm
  have hQc : Q.concl = concl0 := by
    have h1 := Q.hconcl
    rw [hds, hnPc, hlvls, hcbQ, hPrefEq, hFldEq] at h1
    exact Option.some.inj (h1.symm.trans hpr)
  obtain ⟨hCaR, hcon⟩ := blockRuleCaAt_run hμ h hr hcA hrhs hcdP hCf hCb hfindC hlpsC hnP ψ
    Q.ihs.size
  have hCaEq : tgtCaAV μ F fe (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env pp ψ c j
      = (denoteMeta mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt c + cA.2 + Q.ihs.size)
          (blockRuleConclExpr pp (tgtRs out) c j)).getD default := by
    rw [tgtCaAV, hBc, hihL, Array.length_toList]
  obtain ⟨hbC, hleafC⟩ := blockRuleConclClosed_of h₁ h₂ hTf hCf hb₁ hb₂ hinstC hpr
  -- the residue: its reading and scoping
  obtain ⟨⟨Bv, hBv, -⟩, -, -, hlL, hbT⟩ := targetRule_reads hμ mpC.base2 ψ Q hle hbf hds hTf hTb
    hTc hCf' hCb' hCc' hformer hRT3
  -- the `ih` opening
  have hb₃ : ∀ t ∈ Q.ihs.toList.map (·.ty), t.looseBVarsBounded 0 = true := by
    intro t ht
    obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp ht
    exact (hscope ih hih).2.1
  have h₃ := openPisAtFvars_ihTeleOf hb₃ (pp.toBlockShape.rulePrefixAt c + cA.2)
  rw [hTyLen] at h₃
  have hBB : rc.rP + cA.2 = pp.toBlockShape.rulePrefixAt c + cA.2 := by rw [hrP]
  have hFr' : FvarList (pp.toBlockShape.rulePrefixAt c + cA.2) (Q.fvsPref ++ Q.fvsF).reverse := by
    rw [← hrP]; exact hFr
  have hfvEq' : Q.ihs.toList.map (·.fv)
      = ihFvarsAt (pp.toBlockShape.rulePrefixAt c + cA.2) (Q.ihs.toList.map (·.ty)) := by
    rw [hfvEq, hBB]
  -- the frame's readings and grading, at the target frame (`tgtRule_valid`'s)
  have hdF := (blockRuleFdomsAV_eq h hr hcA hrhs hcdP hCf hnP ψ).2
  have hokPF := hPF c _ hr j cA hcA ψ
  have hplQ : (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c).length = rc.rP := by rw [hpl, hrP]
  have hdoms : ∀ (q : Nat) (x : Expr), (Q.fvsPref ++ Q.fvsF)[q]? = some x →
      denoteMeta mpC.base2.acval fe.env ψ q (Expr.fvarTypeD x)
        = some (((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) ++ (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j)).reverse.getD (rc.rP + cA.2 - 1 - q) default) := by
    intro q x hx
    have hq := blockRuleHdoms_of (acval := mpC.base2.acval) (envT := fe.env)
      (ψ := ψ) (ihdoms := []) (fvsIh := []) hplQ hfl rfl
      (openPisAtFvars_length _ Q.hpref) (openPisAtFvars_length _ Q.hfld) rfl
      (blockRulePdomsAV_reads hμ mpC h hr _ (by rw [← hrP]; exact Q.hpref))
      (by rw [hFldEq, hrP]; exact hdF)
      (fun l x hx => nomatch hx) q x (by simpa using hx)
    simpa using hq
  have hokΔ : ∀ q, q < rc.rP + cA.2 → ∀ ρ' : Nat → V, Sat V ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) ++ (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j)).reverse ρ' →
      WellDenotedV V (fun l => ρ' (l + (rc.rP + cA.2 - 1 - q) + 1))
        (((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) ++ (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j)).reverse.getD (rc.rP + cA.2 - 1 - q) default) := by
    intro q hq ρ' hsat
    have hk := blockRuleHokΔ_of (V := V) (ihdoms := []) hplQ hfl rfl
      (fun l hl σ' ys hys => by
        have := hokPF l (by rw [← hrP]; omega) σ' ys (by simpa using hys)
        simpa using this) q (by simpa using hq) ρ' (by simpa using hsat)
    simpa using hk
  have h₃0 : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (rc.rP + cA.2)
      = some ([], Expr.sort .zero) := rfl
  -- an `ih` type's reading, named
  have hTs : ∀ q (hq : q < Q.ihs.size) (T : AnnotTerm),
      denoteMeta mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt c + cA.2) Q.ihs[q].ty
        = some T →
      (ihTyReads mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt c + cA.2)
        Q.ihs.toList).getD q default = T := by
    intro q hq T hT
    rw [ihTyReads, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
      Array.getElem?_eq_getElem hq]
    simp [hT]
  have hTsLen : (ihTyReads mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt c + cA.2)
      Q.ihs.toList).length = Q.ihs.size := by simp [ihTyReads]
  rw [hfl, hIlen]
  refine BlockRuleCerts.of_segments mpC h₁ h₂ h₃ hw₁ hw₂ ?_ ?_ ?_ ?_ hpl hfl hIlen
    (blockRulePdomsAV_reads hμ mpC h hr ψ h₁) (blockRuleFdomsAV_eq h hr hcA hrhs hcdP hCf hnP ψ).2
    ?_ ?_ (by rw [← hBB]; exact Q.hty) (by rw [← hBB]; exact Q.hdeq) hbT (by rw [hQc]; exact hbC)
    ?_ (by rw [hQc]; exact fun l hl => List.mem_append_left _ (hleafC l hl)) ?_ ?_ ?_
  · -- hw₃
    refine ihTeleOf_WScoped fun t ht => ?_
    obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp ht
    exact wscoped_of_leaves_mem hFr' _ (hscope ih hih).1
  · -- hlbF
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [← hPrefEq, ← hFldEq] at hx; exact hlbFQ x hx
    · obtain ⟨i, ty, rfl, hty⟩ := mem_ihFvarsAt hx
      obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp hty
      exact (hscope ih hih).2.1
  · -- hcbF
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [← hPrefEq, ← hFldEq] at hx; exact hcbFQ x hx
    · obtain ⟨i, ty, rfl, hty⟩ := mem_ihFvarsAt hx
      obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp hty
      simpa [ConstsBound] using (hscope ih hih).2.2.1
  · -- hclF
    intro x hx l hl
    rw [← hPrefEq, ← hFldEq]
    rcases List.mem_append.mp hx with hx | hx
    · rw [← hPrefEq, ← hFldEq] at hx
      exact List.mem_append_left _ (hherQ x hx l hl)
    · obtain ⟨i, ty, rfl, hty⟩ := mem_ihFvarsAt hx
      obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp hty
      exact List.mem_append_left _ (List.mem_reverse.mp ((hscope ih hih).1 l hl))
  · -- hI
    intro l x hx
    have hlen : l < (Q.ihs.toList.map (·.ty)).length := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      simpa [ihFvarsAt] using this
    have hl' : l < Q.ihs.size := by simpa using hlen
    have hx' : x = Expr.fvar (pp.toBlockShape.rulePrefixAt c + cA.2 + l) Q.ihs[l].ty := by
      simp only [ihFvarsAt, List.getElem?_map, List.getElem?_range hlen, Option.map_some,
        Option.some.injEq] at hx
      rw [← hx]
      simp [hl']
    subst hx'
    have hih : Q.ihs[l] ∈ Q.ihs.toList := Array.getElem_mem_toList hl'
    obtain ⟨C⟩ := Q.call hih
    obtain ⟨hlT, hbT', -, -, -, -⟩ := hscope _ hih
    obtain ⟨T, hT⟩ := targetCall_ihTy_reads mpC.base2 ψ C (wscoped_of_leaves_mem hFr _ hlT) hbT'
      (fun l hl => hlbFQ _ (List.mem_reverse.mp (hlT l hl)))
    rw [hBB] at hT
    have hd := denoteMeta_open_deepen (acval := mpC.base2.acval) (env := fe.env) (φ := ψ) hacl l
      (pp.toBlockShape.rulePrefixAt c + cA.2) Q.ihs[l].ty 0 [] [] (leaf_lt_of_mem hFr' hlT)
      (LocList.nil _) (LocList.nil _)
    simp only [ConLeche.Expr.instantiateList_nil, Nat.add_zero] at hd
    rw [hIdE, ihDomsLifted_getD (by rw [hTsLen]; exact hl'), hTs l hl' T hT]
    show denoteMeta _ _ _ _ Q.ihs[l].ty = _
    rw [hd, hT]
    rfl
  · -- hokA
    have hPFlen : ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) ++ (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j)).length = pp.toBlockShape.rulePrefixAt c + cA.2 := by
      rw [List.length_append, hpl, hfl]
    intro l hl σ ys hys
    refine hokA_of_two (fun l hl σ ys hys => hokPF l (by rw [hPFlen] at hl; exact hl) σ ys hys)
      (fun q hq σ zs ys hzs hys => ?_) l (by rw [hPFlen, hIlen]; exact hl) σ ys hys
    have hq' : q < Q.ihs.size := by rwa [hIlen] at hq
    have hyl : ys.length = q := by
      rw [hys.length_eq, List.length_take, hIlen]; omega
    have hih : Q.ihs[q] ∈ Q.ihs.toList := Array.getElem_mem_toList hq'
    obtain ⟨C⟩ := Q.call hih
    obtain ⟨hlT, hbT', -, -, -, -⟩ := hscope _ hih
    have hsp : SpineFit σ ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) ++ (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j)) (zs ++ []) := by rw [List.append_nil]; exact hzs
    have hW0 := walkCtx_blockFrame (V := V) (mT := mpC.base2) (ψ := ψ) (ihdoms := [])
      (ihvals := []) Q.hpref Q.hfld h₃0 hplQ hfl rfl
      (by simpa using hdoms) (by simpa using hokΔ)
      (by simpa using hlbFQ) (by simpa using hcbFQ) (by simpa using hherQ) hsp (by simp [SpineFit])
    simp only [List.append_nil, List.reverse_nil, List.nil_append, consList_nil,
      Nat.add_zero] at hW0
    obtain ⟨T, hT, hG⟩ := targetCall_ihTy_graded hμ hacl hin C hFr hW0 hlT hbT'
    rw [hBB] at hT
    rw [hIdE, ihDomsLifted_getD (by rw [hTsLen]; exact hq'), hTs q hq' T hT, WellDenotedV_liftN,
      ← hyl, shiftE_consList]
    exact hG _ hW0.2.1
  · -- hleafR
    intro l hl
    have hm := hlL l hl
    rw [targetFrameIh, List.mem_reverse, hfvEq', hPrefEq, hFldEq] at hm
    exact hm
  · -- hRb
    rw [tgtRbAV, ← hAbs, hB]
    simp only
    rw [← hBB, hBv, Option.getD_some]
  · -- hCa
    rw [hCaEq, hQc]
    exact hCaR concl0 hpr
  · -- hokC
    rw [hCaEq]
    rw [hpl, hfl, hIlen] at hfit hargs
    exact blockRuleHokC_of_run hμ mpC h hr ψ hcon hfit hargs

end Rows

end ConLeche.Model
