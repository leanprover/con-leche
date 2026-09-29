module

public import ConLeche.Model.Inductives.GenRecAssembly
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.BlockRecAssembly
import ConLeche.Model.Inductives.GenRecClasses
import ConLeche.Model.Inductives.GenRecPins
import ConLeche.Model.Inductives.GenRecStage
import ConLeche.Model.Inductives.GenRecRules
import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.GenClassNodes
import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.GenClsMinor
import ConLeche.Model.Inductives.GenClsRows
import ConLeche.Model.Inductives.GenClsFrame
import ConLeche.Verify.Inductives.GenRecScoped
import ConLeche.Verify.Inductives.NestNfScope

public section

/-!
# The generated recursor stage, assembled

`genRecStage` — the recursors' stage's obligation (`BlockRecStagedT`)
from the GENERATED stage's run, through the generic stage
(`blockRecStaged_dataR`) at the generated family's equation components
(`GenRecAssembly.lean`), its obligations discharged by the GENREC lanes:
the stage record (`recStage_of_gen`), the rule side (`GenRecRules.lean`),
the family premise (`genRecPre_run`) with its class side
(`genClsSem_run`, `genCls_minor`, `genClassInd`) and the rule frame's
grading (`genCls_frameV`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

set_option maxHeartbeats 4000000 in
/-- **THE GENERATED RECURSORS' STAGE**: the four cons-monotonicities at
the cons at the classes (`BlockRecStagedT`). -/
theorem genRecStage (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {mpC : EnvModelM V μ envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (hctx : GenRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      posR) :
    BlockRecStagedT (V := V) μ envC pp.toBlockShape out mpC := by
  have hctx0 := hctx
  obtain ⟨hPos, henvC, hnames, hndM, hN, hS, hcore, hctorsAs, hdR, hlfp, hcov, hmk, hover,
    ⟨R⟩, hheads⟩ := hctx0
  obtain ⟨pk, uOfD, ppsOf, hdRe⟩ := hdR
  -- the environments are well formed; the formers' and constructors' types closed
  have hwfC : ConLeche.EnvWF envC := mpC.base2.wf
  have hwfI : ConLeche.EnvWF envI := by
    obtain ⟨mk, -⟩ := hmk
    exact mk.base2.wf
  have hT : ∀ cv ∈ cvTasR, ConLeche.ScB 0 cv.type := by
    intro cv hcv
    obtain ⟨c, hc⟩ := List.getElem?_of_mem hcv
    have hf := (hcore.1 c cv hc).1
    have hw := hwfC _ (List.mem_of_find?_eq_some hf)
    exact ConLeche.ScB.of_closed hw.1 hw.2.2.2.1 0
  have hct : ∀ ctorsA ∈ ctorsAsR, ∀ c ∈ ctorsA, ConLeche.ScB 0 c.1.type := by
    intro ctorsA hA cA hcA
    obtain ⟨c, hc⟩ := List.getElem?_of_mem hA
    have hcl : c < ctorsAsR.length := (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    have hj' : (dR.ctorsM c)[j]? = some cA := by
      rw [← Option.some.inj ((hctorsAs c hcl).symm.trans hc)] at hj; exact hj
    have hck : c < dR.k := by rw [← hN.2.2]; exact hN.2.1 c j cA hj'
    have hf := (hcore.2.2.2 c hck j cA hj').1
    have hw := hwfC _ (List.mem_of_find?_eq_some hf)
    exact ConLeche.ScB.of_closed hw.1 hw.2.2.2.1 0
  have hpos := ConLeche.checkBlockPositivity_nfScoped hwfI hT hct hPos
  have hTlen : pp.toBlockShape.memberNames.length ≤ cvTasR.length := by
    rw [hN.2.2, hdRe]
    simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
      ConLeche.BlockShape.memberNames]
  have hg : ConLeche.ClassGenScoped R.g :=
    ConLeche.genScoped_of_run R hwfI hwfC hT hTlen hct hpos
  have hTbl := ConLeche.genRun_tbl_scoped R hwfI hwfC hT hct hpos
  have h : ConLeche.RecStageG μ F envC pp cvTasR ctorsAsR (tgtRs out) (fun _ => False) :=
    recStage_of_gen hμ R hg
  have hfind := genRecCtor_find (mpC := mpC) R hN hcore hctorsAs ⟨pk, uOfD, ppsOf, hdRe⟩ hcov
  obtain ⟨s, hsP, hTy⟩ := blockRecLevel_run (V := V) (mpC := mpC) hμ h
  obtain ⟨Dc, mc, cvc, hcls, hsel⟩ := genOutCls (mpC := mpC) R hcov dR.toLfp
  -- the open class-side rows
  have hcallTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < (tgtRs out).length →
      ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) →
      ∀ q ∈ genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j,
      ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs →
        q.1 < (tgtRs out).length ∧ xs.length = pp.toBlockShape.rulePrefixAt q.1 ∧
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ q.1).map
            (·.2.2))
          (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
            ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2])) := sorry
  have hargs : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < (tgtRs out).length →
      ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys →
      (∀ e ∈ tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j,
        WellDenotedV V (consList ys ρ) e) ∧
      WellDenotedV V (consList ys ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j) :=
    fun ψ ρ c hc j hj ys hys => genArgs_graded hμ R hg h mpC hfind ψ ρ hc hj ys hys
  have hrhs : ∀ (ψ : Name → Nat) (ρ : Nat → V) (rs : List V), rs.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys →
      (∀ v ∈ genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ c j,
        WellDenotedV V (consList ys (consList rs ρ)) v) ∧
      WellDenotedV V (consList ((genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd
          (genBit pp ψ) ψ c j).map (interp V (consList ys (consList rs ρ)))) (consList ys ρ))
        (genRbAV R.g R.rd c j) := sorry
  have hrowV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs →
        FieldsValid ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ∧
        ∀ ys : List V, SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape
            (tgtRs out) ψ c ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys →
          (∀ e ∈ tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j,
            AnnotValid V (consList ys ρ) e) ∧
          AnnotValid V (consList ys ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j) := by
    intro ψ ρ c r hr j cA rhs hcA _
    have hc : c < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
    have hj : j < blockRecNCt (tgtRs out) c :=
      Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hcA).1 (blockRecNCt_ge hr)
    refine ⟨fieldsValid_of_graded fun l hl zs hzs =>
      (genCls_frameV hμ R hg h mpC hfind ψ hc hj l hl ρ zs hzs).2, fun ys hys => ?_⟩
    obtain ⟨hE, hM⟩ := hargs ψ ρ c hc j hj ys hys
    exact ⟨fun e he => (hE e he).2, hM.2⟩
  have hihV : GenIhPiecesValid (V := V) (envC := envC) mpC.base2.acval out R.g R.rd
      (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
      (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ) := sorry
  have hrowP : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → ∀ (ψ₁ ψ₂ : Name → Nat),
      (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
            = tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i ∧
          tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
            = tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i ∧
          tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ₁ j i
            = tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ₂ j i := sorry
  have hrow3 : ∀ (φ : Name → Nat) (j : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      ConLeche.tgtFireOf (fun x => Expr.constsResolve envC x) pp.toBlockShape
          (ConLeche.tgtMajorsOf out) j r ≠ ConLeche.RecRuleFire.inert →
      BlockRuleRows3 (V := V) mpC pp (ConLeche.tgtMajorsOf out j).nPc (tgtRs out)
        (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
        (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
        (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
        (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
        (fun ψ => blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) φ j i r cA
        (ConLeche.recRuleBits envC.find? r.1.name
          { ctor := cA.1.name, nfields := cA.2, ctorParams := (ConLeche.tgtMajorsOf out j).nPc,
            fire := ConLeche.tgtFireOf (fun x => Expr.constsResolve envC x) pp.toBlockShape
              (ConLeche.tgtMajorsOf out) j r, rhs := rhs, paramsBlind := true }) := sorry
  -- the family premise
  have hsem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      GenPreSem pp out mpC dR Dc mc cvc R.g R.rd ψ ρ := by
    intro ψ ρ
    have hS4 := by
      subst hdRe
      exact genClsSem_run hμ R hg hcov h hN hS hcore hlfp hcls ψ ρ
    rw [← hdRe] at hS4
    exact ⟨hS4.1, hS4.2.1, hS4.2.2.1, hS4.2.2.2, hcallTy ψ ρ,
      genCls_minor hμ R hg h mpC hfind ψ ρ,
      genClassInd hμ hctx R hg hTbl hcls (fun c _ _ => hsel c) ψ ρ⟩
  have hframe : ∀ (ψ : Name → Nat), ∀ c, c < (tgtRs out).length →
      ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length →
      ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).take l) ys →
        WellDenoted V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).getD l default) :=
    fun ψ c hc j hj l hl σ ys hys =>
      (genCls_frameV hμ R hg h mpC hfind ψ hc hj l hl σ ys hys).1
  have hpre := genRecPre_run hμ R hg h hTy hdRe hlfp hN hS hcore hnames hcls hsem hframe hargs
    hrhs
  have heqB := genRecHeqB (mpC := mpC) hμ R hg h
  have heqV := genRecHeqV hμ R hg h hrowV hihV
  have heqP := genRecHeqP hμ R hg h hsP hrowP
  have hdataS := genRecHdataS hμ R hg h hndM heqB heqV heqP hpre hfind
    (genRulePrefRead hμ mpC R hg h) (genRuleFieldRead R hg mpC.base2.acval) hrow3
  unfold BlockRecStagedT
  rw [ConLeche.consBlockRecsT_eq_R]
  exact blockRecStaged_dataR (ctorTy := fun j i ψ =>
      blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) hμ mpC h
    (ConLeche.recStageG_nodup h hndM)
    (ConLeche.recRulesShape_tgt envC.find? (·.constsResolve envC) pp.toBlockShape out)
    (fun j r hr lvls pins hf => by
      obtain ⟨n1, n2, n3, n4⟩ := ConLeche.tgtFireOf_nested hf
      exact ⟨n1, n2, fun pin hpin => ⟨(n3 pin hpin).1, (n3 pin hpin).2.1,
        (n3 pin hpin).2.2.1, (n3 pin hpin).2.2.2,
        tgtFire_pinsNoProj h j r hr lvls pins hf pin hpin⟩, n4⟩)
    (genRecCtor_in R hN hcore hctorsAs ⟨pk, uOfD, ppsOf, hdRe⟩ hcov)
    (pdoms0 := fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (fdoms0 := fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
    (es0 := fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
    (ihs := fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
    (mk0 := fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
    (Rb0 := fun _ => genRbAV R.g R.rd) (s := s) (nCt := blockRecNCt (tgtRs out))
    heqB heqV heqP hpre
    (fun j r hr => blockRecNCt_ge hr)
    (fun ψ j r hr => blockRulePdomsAV_length hμ mpC h hr ψ)
    (genRecCtor_seam R hN hcore hctorsAs ⟨pk, uOfD, ppsOf, hdRe⟩ hcov) (genRecHtower R)
    (fun m₃ hac φ j r hr _ cA rhs _ _ => recStagePinsOk hμ mpC h m₃ hac φ j r hr cA rhs) hdataS
    (blockRecTyZ_run hμ mpC h) (genRecHRaZ R)

end ConLeche.Model
