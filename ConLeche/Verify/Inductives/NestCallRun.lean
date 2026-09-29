module

public import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.ExceptBind

public section

/-!
# The calls' run facts at a nested stage

The run facts the calls' landing reads off the install, beside
`RecCheckRun.lean` and `PositivityInv.lean`:

* every checked major records the walk's normal forms its class matches
  (`TargetRecRun.nfsRun`: `targetMajorNfs … = .ok TargetMajor.nfs`);
* every call's typing ran (`targetCallsOk_each`).

The members' own entries are the root frame's, recorded like every
frame's (`CtorsRecRoot`, `checkBlockPositivity_deriv`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## A checked major's recorded normal forms -/

/-! ## Every call's typing ran -/

end ConLeche
