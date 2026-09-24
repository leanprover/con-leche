module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetRowCertsW
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.StructRecKit2

public section

/-!
# The target recursor model's rows: the certificates and the conclusion `Ca` at the target data (lane RECLIB)

A row of `tgtRecPre_graph` (`TargetGraph.lean`), stated at the target
check's data (`TargetIhData.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Rows

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {envI : Env}

/-- **Row: the certificates at the target data** (B3 (e) 4–5). -/
theorem tgtRuleCerts_at (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape false nested blk cvTas ctorsAs out)
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) :
    ∀ (ψ : Name → Nat), ∀ c, c < (tgtRs out).length → memR c → ∀ j, j < blockRecNCt (tgtRs out) c →
      BlockRuleCerts V mpC F ψ (pp.toBlockShape.rulePrefixAt c)
        (blockRecFdomsK (tgtRs out).length mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c j).length (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j).length
        (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) (blockRecFdomsK (tgtRs out).length mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c j) (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j) (tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j) (tgtCaAV μ F fe (cvTas.map (·.type)) out mpC.base2.acval fe.env pp ψ c j) := by
  intro ψ c hc hm j hj
  have hW := tgtRuleCertsW_run hμ h R hdR hN hS hcore hmr hM ψ hm hc hj
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  -- the field domains' chain lift is the identity
  rw [blockRecFdomsK_eq_run hμ h hcore ψ hm hc hj (tgtRs out).length]
  exact hW

/-- `tgtRuleCerts_at` at every recursor (all majors members). -/
theorem tgtRuleCerts_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F fe.env pp cvTas ctorsAs (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape false nested blk cvTas ctorsAs out)
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) :
    ∀ (ψ : Name → Nat), ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      BlockRuleCerts V mpC F ψ (pp.toBlockShape.rulePrefixAt c)
        (blockRecFdomsK (tgtRs out).length mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c j).length (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j).length
        (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) (blockRecFdomsK (tgtRs out).length mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c j) (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j) (tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ c j) (tgtCaAV μ F fe (cvTas.map (·.type)) out mpC.base2.acval fe.env pp ψ c j) :=
  fun ψ c hc => tgtRuleCerts_at hμ h R hdR hN hS hcore hmr hM ψ c hc trivial

/-- **Row: the rule's conclusion at the rule's frame is the bound at
the constructed element** (B3 (e) 4). -/
theorem tgtKitCaB_at (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs (tgtRs out) memR)
    (_R : ConLeche.TargetRecRun μ F fe pp.toBlockShape false nested blk cvTas ctorsAs out)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hdnP : d.nP = pp.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      memR c → (tgtRs out)[c]? = some r → d.ctorsM (pp.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) {uX nIdxX : Nat → Nat} :
    ∀ c, c < (tgtRs out).length → memR c → uX c = d.uM (pp.toBlockShape.recTgtAt c) ψ →
      nIdxX c = d.nIdxAt (pp.toBlockShape.recTgtAt c) →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) xs →
      ∀ j, j < blockRecNCt (tgtRs out) c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (pp.toBlockShape.recTgtAt c) →
      blockHoleFitRel d ψ ρ pp.toBlockShape.recTgtAt xs c i j fs → ∀ g : V,
      interp V (consList (tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)) d ρ xs c j fs g) (consList (xs ++ fs) ρ)) (tgtCaAV μ F fe (cvTas.map (·.type)) out mpC.base2.acval fe.env pp ψ c j)
        = blockRecMot (tgtRs out).length (blockRecConclAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
          uX nIdxX ρ xs (tagged c i (d.inj ψ (pp.toBlockShape.recTgtAt c) j fs)) := by
  intro c hc hm huX hnX hps hpref j hj i fs hi hfit g
  obtain ⟨r, cA, rhs, ci, hr, hcA, hrhs, hfind, hlps, hnP, hcj, hjc, hes, hpl, hfl,
    -, hrds, hmemN⟩ := blockRuleCaAV_pair (hm := hm) hμ h hcore hmr hdnP hctM ψ hc hj
  obtain ⟨-, hmemk, -, -, -⟩ := blockRecMajor_run (hm := hm) (V := V) hμ mpC h hmr hr ψ
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  obtain ⟨-, -, hcd, -⟩ := hcore.2.2.1 _ j cA hcj
  -- the hole fit, as the stored fit (the override law at the carrier)
  have hfit' := (hM.carrier ψ _ (d.satOfSpine hps) _ hmemN i hi j fs).mp hfit
  -- `Ca` at the target width
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hcdP := hcd
  rw [hdnP] at hcdP
  obtain ⟨-, hcon⟩ := blockRuleCaAt_run (hm := hm) hμ h hr hcA hrhs hcdP hwfC.1 hwfC.2.2.2.1 hfindC hlpsC
    hnP ψ (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).length
  have hCaEq : tgtCaAV μ F fe (cvTas.map (·.type)) out mpC.base2.acval fe.env pp ψ c j
      = (denoteMeta mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt c + cA.2
          + (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).length)
          (blockRuleConclExpr pp (tgtRs out) c j)).getD default := by
    rw [tgtCaAV, tgtB_at hr hcA]
  rw [hCaEq]
  have hihl : (tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
      fe.env ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
        pp.toBlockShape.large)) d ρ xs c j fs g).length
      = (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).length := by
    rw [tgtIhv, blockRecIhvAt_length, tgtKeys, List.length_map, List.length_range]
  -- the tuple is an index spine's
  obtain ⟨is, hIs, rfl⟩ := mem_idxSet_elim hi
  -- the field spine fits the constructor's own field domains
  have hxs : xs.length = pp.toBlockShape.rulePrefixAt c := by rw [hpref.length_eq, hpl]
  have hfd := blockRuleFdomsAV_datum (hm := hm) h hr hcA hrhs hcore hmemk hcj hnP hdnP ψ
  have hq := blockRecSpF_base (mem := pp.toBlockShape.recTgtAt) hμ h hr hfd hxs hpref hfit'.2.1
  obtain ⟨xs', fs', heq, hxs', hfs'⟩ := spineFit_append_inv hq
  obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hxs'.length_eq, hpref.length_eq])
  have hod : (xs.drop d.nP).length = pp.toBlockShape.rulePrefixAt c - d.nP := by
    rw [List.length_drop, hxs]
  have hsf : SpineFit (consList (xs.take d.nP) ρ)
      ((d.Fss (pp.toBlockShape.recTgtAt c) ψ).getD j []) fs := by
    have hq' := (spineFit_liftDomsK_insert (us := xs.drop d.nP)
      (ρ := consList (xs.take d.nP) ρ) ((d.Fss (pp.toBlockShape.recTgtAt c) ψ).getD j []) [] fs)
    rw [List.length_nil, hod, consList_nil, consList_nil, ← consList_append,
      List.take_append_drop, ← hfd] at hq'
    exact hq'.mp hfs'
  have hfsl : fs.length = cA.2 := by rw [hfs'.length_eq, hfl]
  -- the conclusion, evaluated (§29b)
  have hCaE := blockIndCaE_of_run (hm := hm) hμ hM h hr hcA hrhs hfind hlps hnP hdnP hmemN hcj hjc ψ
    hcon rfl rfl hes hpl hfl hrds rfl hxs hfsl hihl hps hsf hIs hfit' rfl
  rw [hCaE, blockRecMot_tagged hc, huX, hnX]
  have hIdx := hM.idxOk ψ _ (d.satOfSpine hps) _ hmemN
  have hret : isOfW (d.uM (pp.toBlockShape.recTgtAt c) ψ)
      (d.nIdxAt (pp.toBlockShape.recTgtAt c))
      (tupW (d.uM (pp.toBlockShape.recTgtAt c) ψ) is) = is := by
    rw [← blockMembers_IdsM_length hmr hmemk ψ]
    exact isOfW_tupW hIdx hIs
  rw [hret, List.append_assoc]

/-- `tgtKitCaB_at` at every recursor (all majors members). -/
theorem tgtKitCaB_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F fe.env pp cvTas ctorsAs (tgtRs out))
    (_R : ConLeche.TargetRecRun μ F fe pp.toBlockShape false nested blk cvTas ctorsAs out)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hdnP : d.nP = pp.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r → d.ctorsM (pp.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    ∀ c, c < (tgtRs out).length →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) xs →
      ∀ j, j < blockRecNCt (tgtRs out) c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (pp.toBlockShape.recTgtAt c) →
      blockHoleFitRel d ψ ρ pp.toBlockShape.recTgtAt xs c i j fs → ∀ g : V,
      interp V (consList (tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)) d ρ xs c j fs g) (consList (xs ++ fs) ρ)) (tgtCaAV μ F fe (cvTas.map (·.type)) out mpC.base2.acval fe.env pp ψ c j)
        = blockRecMot (tgtRs out).length (blockRecConclAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
          (fun c' => d.uM (pp.toBlockShape.recTgtAt c') ψ) (fun c' => d.nIdxAt (pp.toBlockShape.recTgtAt c')) ρ xs (tagged c i (d.inj ψ (pp.toBlockShape.recTgtAt c) j fs)) :=
  fun c hc => tgtKitCaB_at hμ h _R hcore hmr hM hdnP (fun c r _ hr => hctM c r hr) ψ ρ xs c hc trivial
    rfl rfl

end Rows

end ConLeche.Model
