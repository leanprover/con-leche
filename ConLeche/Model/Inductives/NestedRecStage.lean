module

public import ConLeche.Model.Inductives.DeclBlockNested
public import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Inductives.NestedRecPins
import ConLeche.Model.Inductives.NestedRecEqs
import ConLeche.Model.Inductives.NestedRecData
import ConLeche.Model.Inductives.TargetSeam
import ConLeche.Model.Inductives.TargetResidue

public section

/-!
# The recursors' stage at NESTED blocks, composed (lane NESTIND, session 14)

`NestedRecStageOwed` (`DeclBlockNested.lean`) from ONE named premise,
`NestedClassIndOwed` — the induction over the recursor CLASSES
(`TgtClassInd`, `tgtRecPre_clsI`'s `hind`), at every choice of the
outside classes' data.  This is what route A's positivity derivation
(lane POSDERIV) and the (D) typing are to supply (DESIGN F13).  Every
other fact the generic stage (`blockRecStaged_dataR`) asks of the
switch-on cons, at the TARGET rule data
(`tgtFdomsAV`/`tgtEsAV`/`tgtIhsAV`/`tgtMkAV`/`tgtRbAV`), is discharged
here (it was the bundle `NestedRecRestOwed` until lane RECREST emptied it).

What is DISCHARGED here: the stage record at any majors
(`recStage_of_targetG`), the switch-on cons as the generic one
(`consBlockRecsT_eq_R`) with its rules' shape (`recRulesShape_tgt`) and
the `.nested` firings' guards (`tgtFireOf_nested`), the per-recursor
bounds (`blockRecNCt_ge`, `blockRulePdomsAV_length`), the outside
classes' data (`tgtOutCls_of`, chosen), and the family premise's
CANDIDATE (`BlockRecPre.hCand`) from the class induction
(`tgtRecPre_clsI`) at the target equation list.

Discharged by lane RECREST (`NestedRecRest.lean` and the files named):
the family's names distinct (`recStageG_nodup`), the `.nested` pins free
of empty slots (`tgtFire_pinsNoProj`), the carried
constructors stored at the major's parameter count and read
(`tgtRecCtor_in`, `tgtRecCtor_seam`), the family's level and the type
half of the family premise (`blockRecLevel_run`, now over any majors;
chosen in the composition), the equations'
level-parametricity (`blockRecEqs_params_rows` over `tgtRow_params` and
`tgtRule_params`) and bound (`blockRecEqs_below_rows` over `tgtRowB`),
the rules' λ-tower (`tgtRuleTower_run`), the `ℓ = 0` arm
(`blockRecTyZ_run`, `tgtRuleRaZ_seam`), L6, the `.nested` pins' law
(`tgtRecPinsOk`, `NestedRecPins.lean`), and the family premise's
equation half and the equations' bit validity (`tgtRecEqs_hEqAny`,
`tgtRecEqs_validAny`, `NestedRecEqs.lean`), and L5/O12, the rule
contract at every fired pair (`tgtRecDataB`, `NestedRecData.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The nested stage's context**: `NestedRecStageOwed`'s run facts, as
one predicate (the two owed premises below quantify over it once). -/
@[expose] def NestedRecCtx (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) (envC envI : Env) (pp : BlockParts)
    (cvTasR : List ConstantVal) (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)) (nodesR : List ConLeche.NestKey) : Prop :=
  ConLeche.checkBlockRec (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC pp true
      (true && ConLeche.blockNestedBit pp.toBlockShape kindsR)
      (ConLeche.nestKindsFlat kindsR) nodesR block cvTasR ctorsAsR
      (ConLeche.blockNormalCtors pp.toBlockShape ctorsAsR nfsR) = .ok out ∧
  ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI
      envI.find? envI.consts pp cvTasR ctorsAsR true = .ok (kindsR, nfsR, nodesR) ∧
  envC = ConLeche.consBlockCtors pp.nP ctorsAsR envI ∧
  ctorsAsR.map (·.map (fun cA => (cA.1.name, cA.2)))
    = pp.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) ∧
  pp.toBlockShape.memberNames.Nodup ∧
  BlockNamesOk (V := V) dR cvTasR ∧
  BlockCtorsStage (V := V) μ F dR pp.lps cvTasR pp.toBlockShape isRecR A envI pp.ctorNamesAt ∧
  BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k ∧
  (∀ c, c < ctorsAsR.length → ctorsAsR[c]? = some (dR.ctorsM c)) ∧
  (∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
    dR = blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf) ∧
  dR.toLfp ∈ mpC.lfpBlocks ∧
  LfpCover mpC [] ∧
  FormersModelAt (V := V) envI pp.toBlockShape.memberNames mpC dR pp.lps cvTasR
    pp.toBlockShape isRecR ∧
  BlockOverEnv envC pp.toBlockShape.memberNames

/-- **OWED — the induction over the recursor classes** (route A + (D);
DESIGN F13): at every nested stage's context and every choice of the
outside classes' data, `TgtClassInd`. -/
@[expose] def NestedClassIndOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) : Prop :=
  ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)) (nodesR : List ConLeche.NestKey),
    NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR →
    ∀ (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal),
      (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c)) →
      (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind) →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        TgtClassInd μ F envC mpC.base2.acval pp.toBlockShape (cvTasR.map (·.type)) out
          dR Dc mc cvc ψ ρ

/-- **THE NESTED RECURSORS' STAGE, from the class induction** (lane
NESTIND, session 14; lane RECREST): `NestedRecStageOwed` reduces to
`NestedClassIndOwed`, the one premise route A + (D) supply; every other
fact the generic stage asks is discharged here. -/
theorem nestedRecStageOwed_of (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo}
    (hind : NestedClassIndOwed V μ F block) :
    NestedRecStageOwed V μ F block := by
  intro envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR hRec hPos henvC hnames
    hndM hN hS hcore hctorsAs hdR hlfp hcov hmk hover
  have hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A
      kindsR nfsR nodesR :=
    ⟨hRec, hPos, henvC, hnames, hndM, hN, hS, hcore, hctorsAs, hdR, hlfp, hcov, hmk, hover⟩
  have hind' := hind envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR hctx
  obtain ⟨R⟩ := ConLeche.targetRecCheck_run
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hRec))
  have h := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  -- the family's level, chosen by the check's inferred sorts
  obtain ⟨s, hsP, hTy⟩ := blockRecLevel_run (V := V) (mpC := mpC) hμ h
  -- the outside classes' data, chosen
  have hcls0 : ∀ c, ∃ t : Nat × ConstantVal,
      c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) (lfpSel mpC dR.toLfp (tgtMajor out c).ind) t.1 t.2 := by
    intro c
    by_cases hc : c < (tgtRs out).length
    · by_cases hm : (tgtMajor out c).member = none
      · obtain ⟨r, hr⟩ : ∃ r, (tgtRs out)[c]? = some r := ⟨_, List.getElem?_eq_getElem hc⟩
        obtain ⟨rc, cvRi, M, u, rhssA, -, -, ho, -, -, -, ⟨E⟩⟩ := ConLeche.targetRecRun_at R hr
        have hM : tgtMajor out c = M := by
          simp [tgtMajor, List.getD_eq_getElem?_getD, ho]
        rw [hM] at hm ⊢
        obtain ⟨mm, cvI, hD⟩ := tgtOutCls_sel hcov dR.toLfp E hm
        exact ⟨(mm, cvI), fun _ _ => hD⟩
      · exact ⟨(0, default), fun _ h' => absurd h' hm⟩
    · exact ⟨(0, default), fun h' => absurd h' hc⟩
  obtain ⟨tc, hcls⟩ := Classical.axiomOfChoice hcls0
  -- the family premise: its type and equation halves owed, its candidate
  -- from the class induction
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  -- the outside classes' blocks, canonically selected
  let DS : Nat → LfpDatum V := fun c =>
    lfpSel mpC (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).toLfp (tgtMajor out c).ind
  have hmr := blockMembersRun_seam hN hS hcore
  have hmemT : ∀ c, (tgtMajor out c).member.isSome = true → ConLeche.tgtMemAt out c := by
    intro c hc
    cases ho : out[c]? with
    | none => simp [ConLeche.tgtMemAt, ho]
    | some t =>
      simp only [tgtMajor, List.getD_eq_getElem?_getD, ho, Option.getD_some] at hc
      simp [ConLeche.tgtMemAt, ho, hc]
  have hM := blockModelAt_seam h hN hS hcore hlfp
  have hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ)
        (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ') ψ) ρ := by
    intro ψ ρ
    refine ⟨fun c hc => hTy ψ ρ c hc,
      tgtRecEqs_hEqAny hμ hcov h R (Dc := DS) (mc := fun c => (tc c).1)
        (cvc := fun c => (tc c).2) (fun c hc hm => hcls c hc hm) hN hS hcore hctorsAs hmr hM
        hmemT ψ ρ, ?_⟩
    obtain ⟨a, ha, hb⟩ := tgtRecPre_clsI hμ hcov h R
      (Dc := DS) (mc := fun c => (tc c).1) (cvc := fun c => (tc c).2)
      (fun c hc hm => hcls c hc hm) ⟨pk, uOfD, ppsOf, rfl⟩ hN hS hcore hmr hM hlfp hndM ψ ρ
      (hind' _ _ _ (fun c hc hm => hcls c hc hm) (fun _ _ _ => rfl) ψ ρ)
    refine ⟨a, ha, fun e he => hb e ?_⟩
    rw [tgtClsEqs_eq hμ h ψ]
    exact he
  unfold BlockRecStagedT
  rw [ConLeche.consBlockRecsT_eq_R]
  exact blockRecStaged_dataR hμ mpC h (ConLeche.recStageG_nodup h hndM)
    (ConLeche.recRulesShape_tgt envC.find? (·.constsResolve envC) pp.toBlockShape out)
    (fun j r hr lvls pins hf => by
      obtain ⟨n1, n2, n3, n4⟩ := ConLeche.tgtFireOf_nested hf
      exact ⟨n1, n2, fun pin hpin => ⟨(n3 pin hpin).1, (n3 pin hpin).2.1,
        (n3 pin hpin).2.2.1, (n3 pin hpin).2.2.2,
        tgtFire_pinsNoProj h j r hr lvls pins hf pin hpin⟩, n4⟩)
    (tgtRecCtor_in R hN hcore hctorsAs hcov)
    (blockRecEqs_below_rows hμ h (tgtRowB hμ R hN hcore hctorsAs hcov (tgtFormer_facts (fe := ConLeche.mkFEnv envC) hmr) h
      hmemT)) (tgtRecEqs_validAny hμ hcov h R hN hS hcore hctorsAs hmr hmemT)
    (fun i r hr ψ₁ ψ₂ hq => ⟨hsP i r hr ψ₁ ψ₂ hq,
      blockRecEqs_params_rows hμ h (fun c r hr j cA rhs hcA hrhs ψ₁ ψ₂ hq => by
        obtain ⟨e1, e2, e3⟩ := tgtRow_params hμ R hN hcore hctorsAs hcov h hr hcA hrhs hq
        obtain ⟨e4, e5⟩ := tgtRule_params (fe := ConLeche.mkFEnv envC) mpC.base2 h R hr hcA hrhs hq
        exact ⟨e1, e2, e4, e3, e5⟩) i r hr ψ₁ ψ₂ hq⟩) hpre
    (fun j r hr => blockRecNCt_ge hr)
    (fun ψ j r hr => blockRulePdomsAV_length hμ mpC h hr ψ)
    (tgtRecCtor_seam R hN hcore hctorsAs hcov)
    (fun j r hr i cA rhs hcA hrhs _ acv ψ Ra hRa =>
      tgtRuleTower_run R j r hr i cA rhs hcA hrhs acv _ ψ Ra hRa)
    (fun m₃ hac φ j r hr _ cA rhs _ _ => tgtRecPinsOk hμ mpC hcov h R m₃ hac φ j r hr cA rhs)
    (tgtRecDataB hμ hcov h R hndM hN hS hcore hctorsAs hlfp hmemT
      (blockRecEqs_below_rows hμ h (tgtRowB hμ R hN hcore hctorsAs hcov
        (tgtFormer_facts (fe := ConLeche.mkFEnv envC) hmr) h hmemT))
      (tgtRecEqs_validAny hμ hcov h R hN hS hcore hctorsAs hmr hmemT)
      (fun i r hr ψ₁ ψ₂ hq => ⟨hsP i r hr ψ₁ ψ₂ hq,
        blockRecEqs_params_rows hμ h (fun c r hr j cA rhs hcA hrhs ψ₁ ψ₂ hq => by
          obtain ⟨e1, e2, e3⟩ := tgtRow_params hμ R hN hcore hctorsAs hcov h hr hcA hrhs hq
          obtain ⟨e4, e5⟩ := tgtRule_params (fe := ConLeche.mkFEnv envC) mpC.base2 h R hr hcA
            hrhs hq
          exact ⟨e1, e2, e4, e3, e5⟩) i r hr ψ₁ ψ₂ hq⟩) hpre)
    (blockRecTyZ_run hμ mpC h)
    (fun j r hr i cA rhs hcA hrhs _ =>
      tgtRuleRaZ_seam (fe := ConLeche.mkFEnv envC) hμ h R hpre
        (tgtFdomsAV_length (fe := ConLeche.mkFEnv envC) h R _ _) j r hr i cA rhs hcA hrhs)

/-- **The uniform block step at nested blocks, at the two owed premises**:
`declBlock_nested` with `NestedRecStageOwed` from `nestedRecStageOwed_of`. -/
theorem declBlock_nested_of (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockParts}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env block p₀ env₂ true)
    (hind : NestedClassIndOwed V μ F block) :
    LfpCover mp [] → ∃ mp' : EnvModelM V μ env₂, LfpCover mp' [] :=
  declBlock_nested hμ mp hE hdp hrun (nestedRecStageOwed_of hμ hind)

end ConLeche.Model
