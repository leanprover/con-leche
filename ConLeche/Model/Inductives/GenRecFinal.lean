module

public import ConLeche.Model.Inductives.GenRecAssembly
import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Inductives.GenOutKeyFit
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
import ConLeche.Model.Inductives.GenClsCall
import ConLeche.Model.Inductives.GenClsRhs
import ConLeche.Model.Inductives.GenClsData
import ConLeche.Model.Inductives.GenRecExtra
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

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockShape TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun)

universe w

variable {V : Type w} [SetTheory V]

set_option maxHeartbeats 4000000 in
/-- **THE GENERATED RECURSORS' STAGE**: the three cons-monotonicities at
the cons at the classes (`BlockRecStagedT`). -/
theorem genRecStage {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockShape}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {mpC : EnvModelM V envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → Term}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (hctx : GenRecCtx V F block envC envI pp out mpC dR isRecR A kindsR nfsR
      posR)
    -- the reserved names' check (`basisNamesOk`), at the block's recursors
    (hresR : ∀ rc ∈ pp.recs, ConLeche.reservedBasisNames.contains rc.cvR.name = false) :
    BlockRecStagedT (V := V) envC pp out mpC := by
  have hctx0 := hctx
  obtain ⟨hPos, henvC, hnames, hndM, hN, hS, hcore, hmemberCtors, hdR, hlfp, hcov, hmk, hover,
    ⟨R⟩, hheads⟩ := hctx0
  obtain ⟨pk, uOfD, ppsOf, hdRe⟩ := hdR
  -- the environments are well formed; the formers' and constructors' types closed
  have hwfC : ConLeche.EnvWF envC := mpC.base2.wf
  have hwfI : ConLeche.EnvWF envI := by
    obtain ⟨mk, -⟩ := hmk
    exact mk.base2.wf
  have hT : ∀ cv ∈ pp.formers, ConLeche.ScB 0 cv.type := by
    intro cv hcv
    obtain ⟨c, hc⟩ := List.getElem?_of_mem hcv
    obtain ⟨⟨_, -, hD⟩, -⟩ := hcore.1 c cv hc
    exact ConLeche.ScB.of_closed hD.readFvar hD.readBounded 0
  have hrd : ∀ F, FamilyRead mpC F := by
    obtain ⟨_, -, -, h, -⟩ := hmk
    exact h
  have hread : pp.members.map (·.cvT) = pp.formers := by
    rw [hdRe] at hN hS
    exact blockMembers_read hN hS.telescopeAt
  have hct : ∀ ctorList ∈ pp.memberCtors, ∀ c ∈ ctorList, ConLeche.ScB 0 c.1.type := by
    intro ctorList hA ctor hctor
    obtain ⟨c, hc⟩ := List.getElem?_of_mem hA
    have hcl : c < pp.memberCtors.length := (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hctor
    have hj' : (dR.ctorsM c)[j]? = some ctor := by
      rw [← Option.some.inj ((hmemberCtors c hcl).symm.trans hc)] at hj; exact hj
    have hck : c < dR.k := by rw [← hN.2.2]; exact hN.2.1 c j ctor hj'
    have hf := (hcore.2.2 c hck j ctor hj').1
    have hw := hwfC.consts _ (List.mem_of_find?_eq_some hf)
    exact ConLeche.ScB.of_closed hw.1 hw.2.2.2.1 0
  have hM : ∀ ms ∈ pp.members, ms.cvT.type.hasFvar = false := fun ms hms =>
    (hT _ (by rw [← hread]; exact List.mem_map_of_mem hms)).closed.1
  have hpos := ConLeche.checkBlockPositivity_nfScoped hwfI hM hT hct hPos
  have hTlen : pp.memberNames.length ≤ pp.formers.length := by
    rw [hN.2.2, hdRe]
    simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
      ConLeche.BlockShape.memberNames]
  have hg : ConLeche.ClassGenScoped R.g :=
    ConLeche.genScoped_of_run R hwfI hwfC hM hT hTlen hct hpos
  have hTbl := ConLeche.genRun_tbl_scoped R hwfI hwfC hM hT hct hpos
  have h : ConLeche.RecStageG .verified F envC pp (tgtRs out) :=
    recStage_of_gen R hg
  have hfind := genRecCtor_find (mpC := mpC) R hN hcore hmemberCtors ⟨pk, uOfD, ppsOf, hdRe⟩ hcov hrd
  obtain ⟨s, hsP, hTy⟩ := blockRecLevel_run (V := V) (mpC := mpC) h
  obtain ⟨Dc, mc, cvc, hcls, hsel⟩ := genOutCls (mpC := mpC) R hcov hrd dR.toLfp
  have hkf : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V),
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c) xs →
      ∀ dsa, DenoteSpine mpC.base2.acval envC ψ (tgtRP pp c) (tgtMajor out c).ds dsa →
      Sat V ((Dc c).params (Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls)).reverse
        (keyFrame dsa (tgtRP pp c) (consList xs ρ)) :=
    fun c hc hMo ψ ρ xs hfit _ hdsa =>
      genOut_keyFit hctx.base R hg h hc hMo (hcls c hc hMo) ψ ρ xs hfit hdsa
  -- the open class-side rows
  have hcallTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < (tgtRs out).length →
      ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c).length →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) (xs ++ fs) →
      ∀ q ∈ genIhdAV mpC.base2.acval envC R.g R.rd ψ c j,
      ∀ bs, SpineFit (consList (xs ++ fs) ρ) q.2.1 bs →
        q.1 < (tgtRs out).length ∧ xs.length = pp.rulePrefixAt q.1 ∧
        SpineFit ρ (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ q.1)
          (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
            ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2])) :=
    fun ψ ρ => genCallTy R hg h mpC hfind ψ ρ
  have hargs : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < (tgtRs out).length →
      ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) ys →
      (∀ e ∈ tgtEsAV pp out mpC.base2.acval envC ψ c j,
        WellDenoted V (consList ys ρ) e) ∧
      WellDenoted V (consList ys ρ) (tgtMkAV pp out mpC.base2.acval envC ψ c j) :=
    fun ψ ρ c hc j hj ys hys => genArgs_graded R hg h mpC hfind ψ ρ hc hj ys hys
  have hrhs : ∀ (ψ : Name → Nat) (ρ : Nat → V) (rs : List V), rs.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
        ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j) ys →
      (∀ v ∈ genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd ψ c j,
        WellDenoted V (consList ys (consList rs ρ)) v) ∧
      WellDenoted V (consList ((genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd ψ c j).map (interp V (consList ys (consList rs ρ)))) (consList ys ρ))
        (genRbAV R.g R.rd c j) :=
    fun ψ ρ rs hrl hty => genRhs R hg h mpC hfind ψ ρ rs hrl hty
  have hrowP : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some ctor → r.2.1[i]? = some rhs → ∀ (ψ₁ ψ₂ : Name → Nat),
      (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        tgtFdomsAV pp out mpC.base2.acval envC ψ₁ j i
            = tgtFdomsAV pp out mpC.base2.acval envC ψ₂ j i ∧
          tgtEsAV pp out mpC.base2.acval envC ψ₁ j i
            = tgtEsAV pp out mpC.base2.acval envC ψ₂ j i ∧
          tgtMkAV pp out mpC.base2.acval envC ψ₁ j i
            = tgtMkAV pp out mpC.base2.acval envC ψ₂ j i :=
    genRowParams R hg h mpC hfind
  -- the class side, both ways
  have hcsem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      GenClsSplit pp out mpC dR Dc mc cvc ψ ρ ∧ GenClsBack pp out mpC dR Dc mc cvc ψ ρ ∧
      GenClsDec pp out mpC dR Dc mc cvc ψ ρ ∧ GenClsDecInv pp out mpC dR Dc mc cvc ψ ρ := by
    intro ψ ρ
    subst hdRe
    exact genClsSem_run R hg hcov h hN hS hcore hlfp hcls hkf ψ ρ
  have hrdAll : ∀ c, c < (tgtRs out).length → pp.nP ≤ pp.rulePrefixAt c ∧
      ∃ cvI, GenClsRd mpC dR Dc mc cvc pp out c cvI := by
    intro c hc
    subst hdRe
    obtain ⟨hnP, cvI, Rd, -⟩ := genClsRd_all R hg hcov h hN hS hcore hlfp hcls hkf c hc
    exact ⟨hnP, cvI, Rd⟩
  -- the class's index count, read off its decoding at a fitting rule frame
  have hlenEs : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < (tgtRs out).length →
      ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs fs : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c) xs →
      SpineFit (consList xs ρ) (tgtFdomsAV pp out mpC.base2.acval envC ψ c j) fs →
      (tgtEsAV pp out mpC.base2.acval envC ψ c j).length = (tgtMajor out c).nIdx := by
    intro ψ ρ c hc j hj xs fs hxs hfs
    obtain ⟨-, cvI, Rd⟩ := hrdAll c hc
    obtain ⟨-, -, hret, -⟩ := (hcsem ψ ρ).2.2.1 c hc j hj xs fs hxs.length_eq
      (SpineFit.append hxs hfs)
    have hl := congrArg List.length hret
    rw [isOfW_length, List.length_map, Rd.hnIdx] at hl
    exact hl.symm
  have hrow3 : ∀ (φ : Name → Nat) (j : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some ctor → r.2.1[i]? = some rhs →
      BlockRuleRows3 (V := V) mpC pp (ConLeche.tgtMajorsOf out j).nPc (tgtRs out)
        (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ)
        (fun ψ => tgtFdomsAV pp out mpC.base2.acval envC ψ)
        (fun ψ => tgtEsAV pp out mpC.base2.acval envC ψ)
        (fun ψ => tgtMkAV pp out mpC.base2.acval envC ψ)
        (fun ψ => blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) φ j i r ctor
        ({ ctor := ctor.1.name, nfields := ctor.2, fire := ConLeche.tgtFireOf pp
              (ConLeche.tgtMajorsOf out) j r, rhs := rhs }) := by
    intro φ j r hr i ctor rhs hctor _
    have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
    obtain ⟨hnP, cvI, Rd⟩ := hrdAll j hj
    cases hmb : (tgtMajor out j).member with
    | none =>
      have hmb' : (ConLeche.tgtMajorsOf out j).member = none := hmb
      have hf := ConLeche.tgtFireOf_of_out (q := pp) r hmb'
      exact genRows3_out R hg hcov h (fun ψ ρ => (hcsem ψ ρ).1) (fun ψ ρ => (hcsem ψ ρ).2.2.1)
        (fun ψ ρ => (hcsem ψ ρ).2.2.2) hr hmb hctor Rd (hcls j hj hmb) hnP hf
        hf
    | some t =>
      have hmb' : (ConLeche.tgtMajorsOf out j).member = some t := hmb
      have hplain : ConLeche.tgtFireOf pp
          (ConLeche.tgtMajorsOf out) j r = .plain := by
        simp only [ConLeche.tgtFireOf, hmb']
      exact genRows3_mem R h hdRe hN hS hcore hlfp hnames (fun ψ ρ => (hcsem ψ ρ).1)
        (fun ψ ρ => (hcsem ψ ρ).2.2.1) (fun ψ ρ => (hcsem ψ ρ).2.2.2) hr hmb hctor
        hplain
  -- the family premise
  have hsem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      GenPreSem pp out mpC dR Dc mc cvc R.g R.rd ψ ρ := by
    intro ψ ρ
    have hS4 := hcsem ψ ρ
    exact ⟨hS4.1, hS4.2.1, hS4.2.2.1, hS4.2.2.2, hcallTy ψ ρ,
      genCls_minor R hg h mpC hfind ψ ρ,
      genClassInd hctx R hg hTbl hcls (fun c _ _ => hsel c) ψ ρ⟩
  have hframe : ∀ (ψ : Name → Nat), ∀ c, c < (tgtRs out).length →
      ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
          ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j).length →
      ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
          ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j).take l) ys →
        WellDenotedTy V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c
            ++ tgtFdomsAV pp out mpC.base2.acval envC ψ c j).getD l default) :=
    fun ψ c hc j hj l hl σ ys hys =>
      genCls_frameV R hg h mpC hfind ψ hc hj l hl σ ys hys
  have hpre := genRecPre_run R hg h hTy hdRe hlfp hN hS hcore hnames hcls hsem hframe hargs
    hrhs
  have heqB := genRecHeqB (mpC := mpC) R hg h
  have heqP := genRecHeqP R hg h hsP hrowP
  have hdataS := genRecHdataS R hg h hresR hndM heqB heqP hpre hfind
    (genRulePrefRead mpC R hg h) (genRuleFieldRead R hg mpC.base2.acval) hrow3
  -- the ι case split's facts (task #342 L10)
  have hseam := genRecCtor_seam R hN hcore hmemberCtors ⟨pk, uOfD, ppsOf, hdRe⟩ hcov hrd
  have hleaf := blockRecLeafOk_of mpC h heqB heqP hpre
  have hextra : ∀ (Rr : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) →
        Bool × List ConLeche.RecRule)
      (m₃ : EnvModel V (ConLeche.consBlockRecsR Rr pp 0 (tgtRs out) envC)),
      m₃.acval = blockRecAcv mpC.base2.acval envC (tgtRs out) s
        (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd ψ)
          (fun ψ => tgtMkAV pp out mpC.base2.acval envC ψ)
          (fun _ => genRbAV R.g R.rd)) →
      ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r →
      ∀ (i : Nat) (ctor : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some ctor → r.2.1[i]? = some rhs →
      RecRuleKWit m₃ φ r.1.name r.1 (pp.majorIdxAt j) (pp.rulePrefixAt j)
        (ConLeche.recKExpected pp (tgtMajor out j))
        ({ ctor := ctor.1.name, nfields := ctor.2, fire := ConLeche.tgtFireOf pp
              (ConLeche.tgtMajorsOf out) j r, rhs := rhs }) ∧
      RecRuleExtraNK m₃ φ r.1.name r.1 (pp.majorIdxAt j)
        (pp.rulePrefixAt j) (ConLeche.recKExpected pp (tgtMajor out j))
        ({ ctor := ctor.1.name, nfields := ctor.2, fire := ConLeche.tgtFireOf pp
              (ConLeche.tgtMajorsOf out) j r, rhs := rhs }) := by
    intro Rr m₃ hac φ j r hr i ctor rhs hctor hrhs
    have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
    obtain ⟨hnP, -⟩ := hrdAll j hj
    obtain ⟨-, -, hctorCB, hctorRd⟩ := hseam j r hr i ctor hctor
    cases hmb : (tgtMajor out j).member with
    | none =>
      obtain ⟨-, cvI, Rd⟩ := hrdAll j hj
      have hmb' : (ConLeche.tgtMajorsOf out j).member = none := hmb
      have hf := ConLeche.tgtFireOf_of_out (q := pp) r hmb'
      exact genOutExtra R hg hcov h (fun ψ ρ => (hcsem ψ ρ).1) hr hmb hctor Rd
        hnP hf hctorCB hctorRd hac φ rfl rfl
        hf
        (recStagePinsOk mpC h m₃ hac φ j r hr ctor rhs
          (fun _ _ hf' => R.fire_nestedRead hr hf'))
    | some t =>
      have hmb' : (ConLeche.tgtMajorsOf out j).member = some t := hmb
      have hplain : ConLeche.tgtFireOf pp
          (ConLeche.tgtMajorsOf out) j r = .plain := by
        simp only [ConLeche.tgtFireOf, hmb']
      obtain ⟨cvT, G⟩ := genMemAt_of R h hdRe hN hS hcore hlfp hnames hr hmb hctor
      exact genMemExtra h R (fun ψ ρ => (hcsem ψ ρ).1) G hr hmb hnP hctorCB hac φ rfl rfl
        hplain
  unfold BlockRecStagedT
  rw [ConLeche.consBlockRecsT_eq_R]
  exact blockRecStaged_dataR (ctorTy := fun j i ψ =>
      blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) mpC h hresR
    (ConLeche.recStageG_nodup h hndM)
    (ConLeche.recRulesShape_tgt pp out)
    (fun j r hr lvls pins hf => by
      have hread := R.fire_nestedRead hr hf
      obtain ⟨n1, n2, n3, pre, dom, body, D, e1, e2, e3, -⟩ := id hread
      exact ⟨n1, n2, n3, pre, dom, body, D, e1, e2, e3⟩)
    (genRecCtor_in R hN hcore hmemberCtors ⟨pk, uOfD, ppsOf, hdRe⟩ hcov hrd)
    (pdoms0 := fun ψ => blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ)
    (fdoms0 := fun ψ => tgtFdomsAV pp out mpC.base2.acval envC ψ)
    (es0 := fun ψ => tgtEsAV pp out mpC.base2.acval envC ψ)
    (ihs := fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd ψ)
    (mk0 := fun ψ => tgtMkAV pp out mpC.base2.acval envC ψ)
    (Rb0 := fun _ => genRbAV R.g R.rd) (s := s) (nCt := blockRecNCt (tgtRs out))
    heqB heqP hpre
    (fun j r hr => blockRecNCt_ge hr)
    (fun ψ j r hr => blockRulePdomsAV_length mpC h hr ψ)
    (genRecCtor_seam R hN hcore hmemberCtors ⟨pk, uOfD, ppsOf, hdRe⟩ hcov hrd) (genRecHtower R)
    (fun m₃ hac φ j r hr _ ctor rhs _ _ => recStagePinsOk mpC h m₃ hac φ j r hr ctor rhs
      (fun _ _ hf' => R.fire_nestedRead hr hf'))
    (fun m₃ hac => hextra _ m₃ hac) hdataS
    (genRecTyZ R hg h mpC)
    (fun _ _ hr _ _ _ hctor hrhs _ _ hRa hℓ ρ =>
      genRuleRaZ R hg h mpC hfind hlenEs hr hctor hrhs hRa hℓ ρ)

end ConLeche.Model
