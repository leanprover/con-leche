module

import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetIhSlot
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetClassFrame
import ConLeche.Verify.Inductives.NestCallRun
public import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetIhData

public section

/-!
# A call's data, off the target check's run

A call target of the graph recursor (`tgtCall`) at the `(c, j)`-th rule is
one of the rule's `ih` keys: an `ih` entry of the abstraction, whose call
typing ran (`TargetCallRun`, and K.53′), a spine `bs` fitting the call's
telescope read at the rule's frame, the target the callee's index tuple of
the call's index readings, and the value the called field applied to
`bs` (`tgtCall_data`).
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

section Data

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

end Data

end ConLeche.Model
