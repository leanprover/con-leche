module

public import ConLeche.Model.Inductives.TargetOutGrade
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.TargetOutCa
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.TargetOutConcl
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetRowCertsW
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.FixKit
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetRowCertsRun
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.TargetRecRead
import ConLeche.Model.Inductives.TargetIhSlot
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Capstone
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Verify.Inductives.RecCheckRun

public section

/-!
# The rule certificates at an OUTSIDE class

`graphRecPre_core`'s `hcerts` at a recursor whose major is an outside
container: `BlockRuleCerts` at the target check's rule data
(`tgtFdomsAV`, `tgtIhdomsAV`, `tgtRbAV`, `tgtCaAV`).  The member row is
`tgtRuleCertsW_run` (`TargetRowCertsW.lean`); the frame-level facts are
shared (`targetFrame_facts`, `targetRule_reads`, `targetIh_scope`, over
the major's parameters scoped at the prefix, `TgtDsOk`); what differs
at an outside class is

* `tgtOutDsOk` — the major's parameters are the arguments of the
  recursor type's major domain: scoped at the prefix, naming stored
  constants, drawing their leaves from the prefix openers;
* the fields' readings and grading — the instantiated constructor's
  (`tgtOutOpen`, `tgtOutCrestWd`);
* the conclusion `Ca` — its peel at the target spellings (`tgtOutCaAt`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Certs

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {nested : Bool} {block : List ConstantInfo}

end Certs

end ConLeche.Model
