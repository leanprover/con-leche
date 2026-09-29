module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Model.Inductives.BlockRuleCertsRun
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetSeam
import ConLeche.Model.Inductives.TargetRowCertsW
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutGrade
import ConLeche.Model.Inductives.TargetOutCerts
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockHoleGrade
import ConLeche.Semantics.Tower.BlockRecTower

public section

/-!
# The nested recursors' stage: the ι equations' validity and grading

`blockRecStaged_dataR`'s `heqV` (bit validity) and `BlockRecPre.hEq`
(truth values and grading), at the target check's
rule data at EVERY major — the same row split as `eqB` (`tgtRowB`):

* the frame's grading on the prefix and the fields (`tgtHokPF`): a
  member's by the constructors' record (`blockRuleHokPF_run`), a
  container's off the recursor type's prefix and the instantiated
  constructor (`tgtOutCrestWd`, `tgtOutOpen`);
* the field readings (`tgtHdF`): `blockRuleHdF_seam` / `tgtOutOpen`;
* the conclusion's arguments graded (`tgtConclArgsW`):
  `blockRuleConclArgsW_run` / `tgtOutConclArgs`;
* the `ih` terms and the residue graded (`tgtRule_wdVG`, any major);
* for `hEq`'s left-hand side, the rule's spine fitting the recursor's
  binder data at every class (`tgtCls_hrule`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Rows

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
  {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}

end Rows

end ConLeche.Model
