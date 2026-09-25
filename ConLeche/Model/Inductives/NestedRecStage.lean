module

public import ConLeche.Model.Inductives.DeclBlockNested
public import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.BlockRecData
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Inductives.NestedRecPins
import ConLeche.Model.Inductives.TargetSeam
import ConLeche.Model.Inductives.TargetResidue

public section

/-!
# The recursors' stage at NESTED blocks, composed (lane NESTIND, session 14)

`NestedRecStageOwed` (`DeclBlockNested.lean`) from TWO named premises:

* `NestedClassIndOwed` — the induction over the recursor CLASSES
  (`TgtClassInd`, `tgtRecPre_clsI`'s `hind`), at every choice of the
  outside classes' data.  This is what route A's positivity derivation
  (lane POSDERIV) and the (D) typing are to supply (DESIGN F13);
* `NestedRecRestOwed` — every other fact the generic stage
  (`blockRecStaged_dataR`) asks of the switch-on cons, at the TARGET rule
  data (`tgtFdomsAV`/`tgtEsAV`/`tgtIhsAV`/`tgtMkAV`/`tgtRbAV`), bundled as
  `NestedRecRest`'s named fields, each to be discharged at `outside`.

What is DISCHARGED here: the stage record at any majors
(`recStage_of_targetG`), the switch-on cons as the generic one
(`consBlockRecsT_eq_R`) with its rules' shape (`recRulesShape_tgt`) and
the `.nested` firings' guards (`tgtFireOf_nested`), the per-recursor
bounds (`blockRecNCt_ge`, `blockRulePdomsAV_length`), the outside
classes' data (`tgtOutCls_of`, chosen), and the family premise's
CANDIDATE (`BlockRecPre.hCand`) from the class induction
(`tgtRecPre_clsI`) at the target equation list.

Discharged by lane RECREST (`NestedRecRest.lean`, dropped from the owed
bundle): the family's names distinct (`recStageG_nodup`), the `.nested`
pins free of empty slots (`tgtFire_pinsNoProj`), the carried
constructors stored at the major's parameter count and read
(`tgtRecCtor_in`, `tgtRecCtor_seam`), the family's level and the type
half of the family premise (`blockRecLevel_run`, now over any majors;
`NestedRecRestOwed` quantifies over every such level), the equations'
level-parametricity (`blockRecEqs_params_rows` over `tgtRow_params` and
`tgtRule_params`) and bound (`blockRecEqs_below_rows` over `tgtRowB`),
the rules' λ-tower (`tgtRuleTower_run`), the `ℓ = 0` arm
(`blockRecTyZ_run`, `tgtRuleRaZ_seam`) and, L6, the `.nested` pins' law
(`tgtRecPinsOk`, `NestedRecPins.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **What the nested stage owes beyond the class induction**, at one
block's context and the family's level `s`, at the TARGET rule data. -/
structure NestedRecRest (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) (envC : Env)
    (pp : BlockParts) (cvTasR : List ConstantVal)
    (out : List (ConstantVal × TargetMajor × List Expr)) (mpC : EnvModelM V μ envC)
    (s : (Name → Nat) → Nat) : Prop where
  /-- the family premise's equation half (`BlockRecPre.hEq`) -/
  hEq : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = (tgtRs out).length →
    (∀ c, c < (tgtRs out).length → tup.getD c pt ∈ˢ interp V ρ ((blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ) c)) →
    ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') ψ),
      interp V (consList tup ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList tup ρ) e
  eqV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = (tgtRs out).length →
    (∀ mm, mm < (tgtRs out).length →
      tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ mm)) →
    ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') ψ), AnnotValid V (consList tup ρ) e
  /-- **L5 (O12)**: the rule data at every fired pair -/
  data : ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find? (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) pp.toBlockShape 0 (tgtRs out) envC),
    m₃.acval = (blockRecAcv mpC.base2.acval envC (tgtRs out) s
          (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out) (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ') (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ'))) →
    ∀ (φ : Name → Nat) (j : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), (tgtRs out)[j]? = some r →
    ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → (ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) j r ≠ .inert →
      BlockRuleDataB (V := V) mpC pp ((ConLeche.tgtMajorsOf out j).nPc) (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find? (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) pp.toBlockShape 0 (tgtRs out) envC) (tgtRs out) s (blockRecNCt (tgtRs out))
        (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ') (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ')
        (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i) φ j i r cA
        (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := (ConLeche.tgtMajorsOf out j).nPc,
              fire := (ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) j r, rhs := rhs, paramsBlind := true }) rhs


/-- **The nested stage's context**: `NestedRecStageOwed`'s run facts, as
one predicate (the two owed premises below quantify over it once). -/
@[expose] def NestedRecCtx (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) (envC envI : Env) (pp : BlockParts)
    (cvTasR : List ConstantVal) (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)) : Prop :=
  ConLeche.checkBlockRec (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC pp true
      (true && ConLeche.blockNestedBit pp.toBlockShape kindsR)
      (ConLeche.nestKindsFlat kindsR) block cvTasR ctorsAsR
      (ConLeche.blockNormalCtors pp.toBlockShape ctorsAsR nfsR) = .ok out ∧
  ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI
      envI.find? envI.consts pp cvTasR ctorsAsR true = .ok (kindsR, nfsR) ∧
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
  LfpCover mpC []

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
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)),
    NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR →
    ∀ (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal),
      (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c)) →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        TgtClassInd μ F envC mpC.base2.acval pp.toBlockShape (cvTasR.map (·.type)) out
          dR Dc mc cvc ψ ρ

/-- **OWED — the rest of the nested stage** (`NestedRecRest`'s fields), at
every nested stage's context and every family level `s` the check's
recursor types fit (`blockRecLevel_run`'s two facts: `s` reads only the
family's level parameters, and every recursor type lies in `univ (s ψ)`). -/
@[expose] def NestedRecRestOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) : Prop :=
  ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)),
    NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR →
    ∀ s : (Name → Nat) → Nat,
      (∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
        (tgtRs out)[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂) →
      (∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < (tgtRs out).length →
        interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c) ∈ˢ (univ (s ψ) : V) ∧
          WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      NestedRecRest V μ F envC pp cvTasR out mpC s

/-- The target equation list `tgtRecPre_clsI` concludes at IS the stage's
(`blockRecEqs` at the target rule data): the prefix domains are closed
(`blockRecPdomsK_run`), and the chain lifts keep the field domains'
lengths (`liftDomsK_length`). -/
theorem tgtClsEqs_eq {F : Nat} {envC : Env} {mpC : EnvModelM V μ envC} (hμ : μ.verifiedChecks = true)
    {pp : BlockParts} {cvTasR : List ConstantVal} {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTasR ctorsAsR (tgtRs out) memR) (ψ : Name → Nat) :
    iotaEqsAV (tgtRs out).length (blockRecNCt (tgtRs out))
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
        (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
        (fun c j => liftEsK (tgtRs out).length
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
          (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
        (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
        (tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out
          mpC.base2.acval envC ψ)
        (fun c j => (tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ c j).liftN (tgtRs out).length
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c
              j).length
            + (tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out
              mpC.base2.acval envC ψ c j).length))
      = blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ') ψ := by
  show _ = iotaEqsAV _ _ _ _ _ _ _ _
  refine iotaEqsAV_congr (fun c hc => ?_) (fun c _ j _ => ?_)
  · exact (blockRecPdomsK_run (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ _).symm
  · simp only [tgtFdomsK, liftDomsK_length]

/-- **THE NESTED RECURSORS' STAGE, from the class induction and the rest**
(lane NESTIND, session 14): `NestedRecStageOwed` reduces to
`NestedClassIndOwed` (the one premise route A + (D) supply) and
`NestedRecRestOwed` (the remaining named facts at the target rule data). -/
theorem nestedRecStageOwed_of (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo}
    (hind : NestedClassIndOwed V μ F block) (hrest : NestedRecRestOwed V μ F block) :
    NestedRecStageOwed V μ F block := by
  intro envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hRec hPos henvC hnames
    hndM hN hS hcore hctorsAs hdR hlfp hcov
  have hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A
      kindsR nfsR :=
    ⟨hRec, hPos, henvC, hnames, hndM, hN, hS, hcore, hctorsAs, hdR, hlfp, hcov⟩
  have hind' := hind envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hctx
  obtain ⟨R⟩ := ConLeche.targetRecCheck_run
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hRec))
  have h := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  -- the family's level, chosen by the check's inferred sorts
  obtain ⟨s, hsP, hTy⟩ := blockRecLevel_run (V := V) (mpC := mpC) hμ h
  have H := hrest envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hctx s hsP hTy
  -- the outside classes' data, chosen
  have hcls0 : ∀ c, ∃ t : LfpDatum V × Nat × ConstantVal,
      c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) t.1 t.2.1 t.2.2 := by
    intro c
    by_cases hc : c < (tgtRs out).length
    · by_cases hm : (tgtMajor out c).member = none
      · obtain ⟨r, hr⟩ : ∃ r, (tgtRs out)[c]? = some r := ⟨_, List.getElem?_eq_getElem hc⟩
        obtain ⟨rc, cvRi, M, u, rhssA, -, -, ho, -, -, -, ⟨E⟩⟩ := ConLeche.targetRecRun_at R hr
        have hM : tgtMajor out c = M := by
          simp [tgtMajor, List.getD_eq_getElem?_getD, ho]
        rw [hM] at hm ⊢
        obtain ⟨D, mm, cvI, hD⟩ := tgtOutCls_of hcov E hm
        exact ⟨(D, mm, cvI), fun _ _ => hD⟩
      · exact ⟨(dR.toLfp, 0, default), fun _ h' => absurd h' hm⟩
    · exact ⟨(dR.toLfp, 0, default), fun h' => absurd h' hc⟩
  obtain ⟨tc, hcls⟩ := Classical.axiomOfChoice hcls0
  -- the family premise: its type and equation halves owed, its candidate
  -- from the class induction
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
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
    refine ⟨fun c hc => hTy ψ ρ c hc, H.hEq ψ ρ, ?_⟩
    obtain ⟨a, ha, hb⟩ := tgtRecPre_clsI hμ hcov h R
      (Dc := fun c => (tc c).1) (mc := fun c => (tc c).2.1) (cvc := fun c => (tc c).2.2)
      (fun c hc hm => hcls c hc hm) ⟨pk, uOfD, ppsOf, rfl⟩ hN hS hcore hmr hM hlfp hndM ψ ρ
      (hind' _ _ _ (fun c hc hm => hcls c hc hm) ψ ρ)
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
      hmemT)) H.eqV
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
    H.data
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
    (hind : NestedClassIndOwed V μ F block) (hrest : NestedRecRestOwed V μ F block) :
    LfpCover mp [] → ∃ mp' : EnvModelM V μ env₂, LfpCover mp' [] :=
  declBlock_nested hμ mp hE hdp hrun (nestedRecStageOwed_of hμ hind hrest)

end ConLeche.Model
