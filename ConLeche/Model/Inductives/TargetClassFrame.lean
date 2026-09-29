module

import ConLeche.Model.Inductives.TargetClasses
public import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutCerts
import ConLeche.Model.Inductives.TargetOutGrade
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetRowCertsW
import ConLeche.Model.Inductives.TargetResidue
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.Inductives.RecStage

public section

/-!
# A target rule's FRAME at every class

The `(c, j)`-th rule of a target check at ANY major — a member of the
block or an outside container (`TgtOutCls`) — opens one frame: the
recursor's prefix, then the constructor's fields at the major's
instantiation.  The facts every call row reads off that frame are the
same at both kinds; only their SOURCES differ (a member constructor's
record `hcore`, the member rows' readings; a container constructor's
environment entry, the instantiated constructor's reading `tgtOutOpen`
and grading `tgtOutCrestWd`).  `tgtFrame_cls` states them once, at the
target spellings (`tgtFdomsAV` for the fields), so the call rows over
the classes read no member-only lemma.

* `tgtFrame_cls` — the package (one case split on the member bit);
* `tgtFrame_walk` — the frame's walk context at any spine fitting the
  prefix and field domains (no case split).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor RecShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Frame

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

end Frame

end ConLeche.Model
