module

public import ConLeche.Semantics.Inductives.DeclNested
public import ConLeche.Model.Inductives.NestedPins
public import ConLeche.Model.Inductives.NestedCopyIdx
public import ConLeche.Model.Inductives.NestedCopyInst
public import ConLeche.Model.Inductives.NestedPinLeafAll
import ConLeche.Model.Inductives.NestedStoreRun
import ConLeche.Model.Inductives.NestedReadLaw
public section

/-!
# The nested route's model chain, composed (task #315)

Nothing new is proved here.  This file exists so that the ELABORATOR,
and not a reading of seven statements in seven files, is what certifies
that the nested route's model side composes: the links

* `nestedPinsShape_of`     (`NestedCopyInst.lean`),
* `nestedPinsEntry_of_le_all` (`NestedPinLeafAll.lean`),
* `nestedPinsIdent_of`     (`NestedCopyIdx.lean`),
* `nestedPinsStaged_of`    (`NestedPins.lean`),
* `nestedCtorsStaged_of_pins` (`NestedReadLaw.lean`),
* `nestedCoreModeled_of`   (`DeclNestedCore.lean`),
* `nestedTailModeled`      (`NestedStoreRun.lean`, K.36 discharged), and
* `declNested_of`          (`DeclNestedCore.lean`)

meet at their ends, and that what is left over when they do is EXACTLY
three open hypotheses.  An edit that breaks the composition fails here
rather than in someone's reading of the tree.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche (Env CheckMode NestedParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {F : Nat} {env envOut : Env}
  {p : NestedParts}

/-- **WHAT REMAINS ON THE MODEL SIDE OF THE NESTED ROUTE**: a nested
block's install carries the environment's model across, from THREE open
hypotheses and nothing else —

* `NestedPinsShapeOrdRight` and `NestedPinsShapePinF`
  (`NestedCopyInst.lean`): the two halves of a copied constructor's
  field shape that wait on the same kernel record;
* `NestedPinsLe` (`NestedPinLeafAll.lean`): the pins' rank order.

Everything else the chain needs is a theorem in this tree: the tail's
last model face K.36 is the run's own `nestedContainersOk` Bool
(`nestedCtorPinNamesOf_of_containersOk`, K.53), and the core's stages
come out of the three residuals by `nestedPinsShape_of`,
`nestedPinsEntry_of_le_all`, `nestedPinsIdent_of`,
`nestedPinsStaged_of`, `nestedCtorsStaged_of_pins` and
`nestedCoreModeled_of`.

Stated as the composition itself, so that the residual count is
elaborator-checked (this project's `consumer-first-hypotheses` rule
applied to the route as a whole): if a link's statement drifts, this
theorem stops compiling. -/
theorem nestedModeled_of_three
    (hOrd : NestedPinsShapeOrdRight V μ F) (hPin : NestedPinsShapePinF V μ F)
    (hLe : NestedPinsLe V μ F)
    (hμ : μ.verifiedChecks = true) (mp : EnvModelB V μ env)
    (hE : ConLeche.EtaFamiliesClosed env)
    (h : ConLeche.Semantics.DeclNestedRun μ F env p envOut) :
    Nonempty (EnvModelB V μ envOut) :=
  declNested_of hμ mp hE
    (nestedCoreModeled_of (nestedCtorsStaged_of_pins (nestedPinsStaged_of
      (nestedPinsIdent_of (nestedPinsShape_of hOrd hPin)
        (nestedPinsEntry_of_le_all (nestedPinsShape_of hOrd hPin) hLe)))))
    nestedTailModeled h

end ConLeche.Model
