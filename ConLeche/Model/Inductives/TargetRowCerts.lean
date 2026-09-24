module

public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.BlockDeclRun

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
  {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}

/-- **Row: the certificates at the target data** (B3 (e) 4–5). -/
theorem tgtRuleCerts_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTas ctorsAs out)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A fssZ envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) :
    ∀ (ψ : Name → Nat), ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      BlockRuleCerts V mpC F ψ (pp.toBlockShape.rulePrefixAt c)
        (blockRecFdomsK (tgtRs out).length mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c j).length (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j).length
        (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) (blockRecFdomsK (tgtRs out).length mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c j) (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j) (tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j) (tgtCaAV μ F fe (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env pp ψ c j) := by
  sorry

/-- **Row: the rule's conclusion at the rule's frame is the bound at
the constructed element** (B3 (e) 4). -/
theorem tgtKitCaB_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTas ctorsAs out)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (hN : BlockNamesOk (V := V) d cvTas)
    (hdnP : d.nP = pp.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r → d.ctorsM (pp.toBlockShape.recTgtAt c) = r.2.2.2)
    (hC : LfpClause mpC.base2.acval d.toLfp)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    ∀ c, c < (tgtRs out).length →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) xs →
      ∀ j, j < blockRecNCt (tgtRs out) c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (pp.toBlockShape.recTgtAt c) →
      blockHoleFitRel d ψ ρ pp.toBlockShape.recTgtAt xs c i j fs → ∀ g : V,
      interp V (consList (tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)) d ρ xs c j fs g) (consList (xs ++ fs) ρ)) (tgtCaAV μ F fe (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env pp ψ c j)
        = blockRecMot (tgtRs out).length (blockRecConclAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
          (fun c' => d.uM (pp.toBlockShape.recTgtAt c') ψ) (fun c' => d.nIdxAt (pp.toBlockShape.recTgtAt c')) ρ xs (tagged c i (d.inj ψ (pp.toBlockShape.recTgtAt c) j fs)) := by
  sorry

end Rows

end ConLeche.Model
