module

public import ConLeche.Cached.CheckerC
public import ConLeche.Kernel.Inductives.TargetInstall

@[expose] public section

/-!
# The target shadow through the index (lane TSHADOW)

The cached instantiation of `targetShadow`
(`ConLeche/Kernel/Inductives/TargetInstall.lean`): the index-bound
operations `sharedOpsC`, the rule variant `sharedOpsRuleR` (a flush at
each of a rule's two environment transitions), `flushC` at every
environment change, and the memoised walkers.  `--target-shadow`
(`Main.lean`) runs it beside the install on the pre-block index and
state, and discards the state: nothing of it reaches the fold.
-/

namespace ConLeche.Cached

variable (mode : CheckMode)

/-- The cached shadow operations. -/
def shadowOpsC : ShadowOps CheckCM :=
  ⟨sharedOpsC mode, sharedOpsRuleR mode, flushC, structWalkersC⟩

/-- **The target shadow through the index.** -/
def targetShadowS (fe : FEnv) (nPd : Nat) (block : List ConstantInfo) :
    CheckCM TargetShadowReport :=
  targetShadow (shadowOpsC mode) fe nPd block

end ConLeche.Cached
