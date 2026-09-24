module

public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.BlockDeclRun

public section

/-!
# The target recursor model's rows: the graph-built `ih` values: their fit and the `ih` chain (lane RECLIB)

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

/-- **Row: the graph-built `ih` values fit the `ih` domains** (B3 (e)
6), given the graph is bound-valued at the predecessors. -/
theorem tgtGraphIhF_run (hμ : μ.verifiedChecks = true)
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
    (hM : BlockModelAt mpC.base2 names d)
    (hC : LfpClause mpC.base2.acval d.toLfp)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    ∀ c, c < (tgtRs out).length →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) xs →
      ∀ j, j < blockRecNCt (tgtRs out) c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (pp.toBlockShape.recTgtAt c) →
      blockHoleFitRel d ψ ρ pp.toBlockShape.recTgtAt xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ blockGraphPred d ψ ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ) pp.toBlockShape.recTgtAt (tgtRs out).length (tgtCall μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ d ρ) xs (c, j, fs) →
        app g v ∈ˢ blockRecMot (tgtRs out).length (blockRecConclAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
          (fun c' => d.uM (pp.toBlockShape.recTgtAt c') ψ) (fun c' => d.nIdxAt (pp.toBlockShape.recTgtAt c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j) (tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)) d ρ xs c j fs g) := by
  sorry

/-- **Row: the `ih` chain** (B3 (e) 7) — the graph-built `ih` values,
read off any recursor `r` over the rule's predecessors, ARE the target
`ih` terms' readings at the chain frame of any candidate `a` whose fold
along a callee's spine is `r` at the tagged call. -/
theorem tgtGraphIhChain_run (hμ : μ.verifiedChecks = true)
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
    (hM : BlockModelAt mpC.base2 names d)
    (hC : LfpClause mpC.base2.acval d.toLfp)
    (ψ : Name → Nat) (ρ : Nat → V) (a : Nat → V) (xs : List V) (r : V → V)
    (hfold : ∀ c', c' < (tgtRs out).length → ∀ (is : List V) (x : V),
      xs.length = pp.toBlockShape.rulePrefixAt c' →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c').map
        (·.2.2)) (xs ++ (is ++ [x])) →
      r (tagged c' (d.tup ψ (pp.toBlockShape.recTgtAt c') is) x) = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit (chainFrame (tgtRs out).length a ρ) (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c ++ blockRecFdomsK (tgtRs out).length mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c j) (xs ++ fs) →
      tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)) d ρ xs c j fs
          (graph r (blockGraphPred d ψ ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ) pp.toBlockShape.recTgtAt (tgtRs out).length (tgtCall μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ d ρ) xs (c, j, fs)))
        = (tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j).map (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))) := by
  sorry

end Rows

end ConLeche.Model
