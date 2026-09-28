module

public import ConLeche.Kernel.Inductives.ClassCheck
public import ConLeche.Cached.CheckerC

@[expose] public section

/-!
# The class checker through the index (EXPERIMENTAL, not the default)

`checkBlockKS` (`CheckerC.lean`) with the class check
(`classRecCheck`, `ConLeche/Kernel/Inductives/ClassCheck.lean`) in place
of today's recursor check and conformance check: the same formers'
and constructors' pass, the same tail around it.  Nothing in the fold
calls it; the sweep driver `tests/ClassSweep.lean` does.
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-- `checkBlockTailS` on the class check. -/
def checkBlockTailClassS (block : List ConstantInfo) (q : BlockPass FEnv) : CheckCM FEnv := do
  let p := q.p
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.k ∨ 2 ≤ p.numCtors) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  let _isorts ← checkBlockIdxSortsF (sharedOpsC mode q.env₁) q.env₁ p.toBlockShape
    (p.members.zip q.cvTas)
  let vis₁ := q.env₁.visibleBelow
  let env₁ := q.env₁.env
  let fe₂ := consBlockCtorsF p.nP q.ctorsAs q.env₁
  flushC
  let (out, _) ← classRecCheck (shadowOpsC mode) (fe₂.restrictTo vis₁) env₁ fe₂ p block q.cvTas
    q.ctorsAs
  flushC
  let fe₃ := consBlockRecsTF fe₂.find? (·.constsResolveF fe₂) p.toBlockShape 0 out fe₂
  checkBlockTablesF (m := CheckCM) structWalkersC p.toBlockShape
    (p.members.zip (q.ctorsAs.zip q.sortsss)) fe₃

/-- `checkBlockKS` on the class check. -/
def checkBlockClassKS (fe : FEnv) (block : List ConstantInfo) (p₀ : BlockParts) :
    CheckCM FEnv := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  flushC
  let q ← checkBlockPassS mode fe p₀ (blockRawRec p₀)
  checkBlockTailClassS mode block q

end ConLeche.Cached
