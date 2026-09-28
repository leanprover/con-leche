module

public import ConLeche.Model.Inductives.DeclBlock
public import ConLeche.Verify.Inductives.RecCheckRun

public section

/-!
# The recursors' stage's context on the old route

`NestedRecCtx`: the recursors' stage's run (the positivity check fused
with the target check, then the reject-only conformance check) and what
the uniform block step (`DeclBlockStep.lean`) reads of it, with the
target check's hook at a family (`recHookOf`).  It reads the target
check's run record (`TargetRecRun`) and goes with that check at the
class check's flip.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BlockShape BlockParts MemberShape BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The recursor check's hook at a family** `tys` (`targetHook`, the
fused traversal's per-constructor rules, at the fueled operations): the
predicate the positivity run's walked constructors satisfy
(`ConLeche.HookOk`). -/
@[expose] def recHookOf (μ : CheckMode) (F : Nat) (envC : Env) (q : BlockShape)
    (cvTas : List ConstantVal) (tys : List (ConstantVal × ConLeche.TargetMajor × Level)) :
    ConLeche.NestHook ConLeche.CheckM :=
  ConLeche.targetHook (ConLeche.ShadowOps.fueled μ F) (ConLeche.mkFEnv envC)
    (ConLeche.consBlockRecsBareF q 0 (tys.map fun t => (t.1, t.2.1.nIdx)) (ConLeche.mkFEnv envC))
    q (cvTas.map (·.type)) (ConLeche.targetFamilyOf q tys) q.recs tys

/-- **The recursors' stage's context** (`nestedRecStage`,
`DeclBlockStep.lean`): the stage's own run (the positivity check fused
with the target check, then the reject-only conformance check), and in it
the block's POSITIVITY run at the formers' environment `envI` — its hook
the recursor check's at the check's record `R` — whose constructors' cons
is `envC` (the recursor stage may read it), the stored
constructors the recogniser's, the block's representation at the
constructors' environment (the three records `blockModelAt_of_stages`
consumes, the run's own record), its lfp clause recorded in a covered
carrier, the positivity model at the formers' environment, and the block
over the input environment. -/
@[expose] def NestedRecCtx (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) (envC envI : Env) (pp : BlockParts)
    (cvTasR : List ConstantVal) (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr))
    (keysR : List ConLeche.NestKey) : Prop :=
  ConLeche.checkBlockRec (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC envI pp block
      cvTasR ctorsAsR = .ok out ∧
  (∃ R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape
      (ConLeche.blockNestedBit pp.toBlockShape kindsR) block cvTasR ctorsAsR out,
    R.keys = keysR ∧
    ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI
      envI.find? envI.consts pp cvTasR ctorsAsR
      (recHookOf μ F envC pp.toBlockShape cvTasR R.tys) = .ok (kindsR, nfsR, keysR, R.done)) ∧
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

end ConLeche.Model
