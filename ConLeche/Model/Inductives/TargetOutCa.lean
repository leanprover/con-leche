module

public import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutConcl
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.BlockRuleCaRun
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InstLevels
import ConLeche.Semantics.Tower.FixTower

public section

/-!
# The rule's conclusion `Ca` at an OUTSIDE class — `hCaB`

The graph producer's `hCaB` (`graphRecPre_core`) reads the rule's
conclusion `Ca` (`tgtCaAV`: the recursor type instantiated at the rule's
prefix, the constructor's index expressions and the fired constructor,
read past the `ih` openers) at a decoding of the class, and asks it to
be the motive at the tagged element.  At a member class that is
`tgtKitCaB_at` (`TargetRowCerts.lean`); here it is stated at an outside
class — the major a container `C.{us} ds`, the class the recorded block
`D` holding `C` (`TgtOutCls`):

* `tgtOutCaAt` — the peel (`BlockRuleConclAt`) at the TARGET spellings:
  the prefix openers read to `paramBvarsAt`, the constructor's index
  arguments to `tgtEsAV`, the fired spine to `tgtMkAV`, each lifted past
  the `ih` openers;
* `tgtOutCaB` — `hCaB`: the index values at a hole fit of `D`'s
  constructor at the tuple `t` are `t`'s components (the fit's result
  indices, against the rule's own decoding `tgtOutDec`), the fired spine
  reads to the injection, and `blockRecCa_run` evaluates the peel.

The `ih` values enter only through their number: the `ih` block sits
above the conclusion's frame.
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

section Ca

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {nested : Bool} {block : List ConstantInfo}

/-- The recomputed recursor type is the stored one. -/
theorem tgtRecTy_at {out : List (ConstantVal × TargetMajor × List Expr)} {j : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) : tgtRecTy out j = r.1.type := by
  simp only [tgtRs, List.getElem?_map] at hr
  cases ho : out[j]? with
  | none => rw [ho] at hr; exact nomatch hr
  | some t =>
    rw [ho] at hr
    obtain rfl := Option.some.inj hr
    simp only [tgtRecTy, List.getD_eq_getElem?_getD, ho, Option.getD_some]

end Ca

end ConLeche.Model
