import Setlec.SetBase.Bridge.EtaCerts

/-!
# `DefEqClaimsR` at `fuel + 1`, closed (task #148, T3, batch d)

Every obligation of the defeq quarter is discharged: `stuckIrrel`'s
cascade is unconditional (`stuckIrrel_stepR` + the two eta
certificates + `structUnitCert_stepR` + `proofIrrel_stepR`), the stuck
block is `defeqStuck_stepR`, the spine short-circuit is
`defeqSpine_stepR`, and the literal acceleration is `reduceNat_stepR`.

So the third quarter of `CheckStepR` stands with **no outstanding
step** — as does the second (`whnf_claimsR_closed`).  What remains of
`CheckStepR` is the projection clauses (batch e) and the iota clause
(batch g).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-- **`StuckIrrelStepR`, proved.** -/
theorem stuckIrrel_stepR_closed {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hg : mode.betaGate = false)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsR mode m φ fuel) (ihd : DefEqClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel) :
    StuckIrrelStepR (mode := mode) m φ fuel :=
  stuckIrrel_stepR m φ hg hcl ihw ihd ihi
    (pairEtaCert_stepR m φ hg ihw ihd ihi)
    (structEtaCert_stepR m φ hg hcl ihw ihd ihi)

/-- **`DefEqClaimsR` at `fuel + 1`, with no outstanding obligation.** -/
theorem defeq_claimsR_full {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hg : mode.betaGate = false)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsR mode m φ fuel) (ihw : WhnfClaimsR mode m φ fuel)
    (ihd : DefEqClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel) :
    DefEqClaimsR mode m φ (fuel + 1) :=
  defeq_claimsR_closed m φ hcl ihwc (reduceNat_stepR m φ hcl ihw)
    (propIrrel_stepR hg m φ ihw ihi)
    (defeqStuck_stepR m φ hg hcl ihw ihd ihi
      (stuckIrrel_stepR_closed m φ hg hcl ihw ihd ihi))
    (defeqSpine_stepR m φ ihd)

end Setlec.SetR
