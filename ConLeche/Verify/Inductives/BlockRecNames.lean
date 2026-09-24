module

public import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Verify.ProjSlots
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.Extend.Inversions

public section

/-!
# The recursor CHECK at k members, inverted at the NAMES

Two kernel-inversion facts about `checkBlockRecK`
(`ConLeche/Kernel/Inductives/BlockInstall.lean`), MODEL-FREE: what the
stage stores, per recursor record, and what its `checkConstantVal` run
says about the stored constant.

* `checkBlockRecK_recNames`: the name-set check ran, there is one
  stored recursor per record, and each is that record's constant
  CHECKED at the constructors' environment;
* `checkBlockRecK_cvFacts`: every stored recursor's name is fresh at
  that environment, passes the two name guards, and its (annotated)
  type mentions no empty projection slot.

They live here, below both consumers: the model tier's recursor-stage
assembly (`Model/Inductives/BlockRecAssembly.lean`) and the η-closure's
recursor freshness (`checkBlockRec_fresh`,
`Semantics/Inductives/DeclBlockEta.lean`), which may not import Model.
-/

