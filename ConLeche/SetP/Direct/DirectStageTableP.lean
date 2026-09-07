import ConLeche.SetP.Direct.DirectBodyFramesP
import ConLeche.Verify.Direct.DirectPartsInv

/-!
# The projection table's cons (task #175 S1)

`stageTable`: the P step at the direct install's last stage — the
structure's projection **table**, one constant holding every field's
body (`checkDirectProjTable`).  The table's leaf is `Sort 0` (a
member of its dummy type's reading; a table is not a term), and what
the cons owes is the tower law at every field
(`declStepPM_of_tower_cons`):

* **(A)** the typing law reads body `i` through the dummy telescope
  (`denoteP_projTele_zero`); the opened body is the constructor's
  field domain at the variables (`directProjBody_open`), whose frame
  facts are `bodyFrames`, and `entryTypingCore` closes;
* **(B)** the iota law and **(C)** the η law are the block's own
  (`entryIotaCore`/`entryIotaCoreZero`, `entryEtaCore`), as before.

The squash regime's guard content (`directProjGuards_getD` over the
field-sort run) and the unused earlier fields' invariance
(`openPisAtFvars_leaf_free`) are derived here per field, as the
retired per-slot fold derived them per slot.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AVExpr)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta ProjEntry ProjTable projTableName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- The table name has the reserved shape. -/
theorem projTableName_isProjFnShape (T : Name) :
    (projTableName T).isProjFnShape = true := rfl

end ConLeche.SetP
