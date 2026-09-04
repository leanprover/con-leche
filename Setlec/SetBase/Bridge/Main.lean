import Setlec.SetBase.Bridge.Iota

/-!
# `CheckStepR`, closed (task #148, T3)

The bridge's fuel-induction step, with **no outstanding obligation**:
a successful `--set-model` checker run yields a derivation of the
relation family of `Setlec/SetR/Rel.lean`.

| quarter | closed by |
|---|---|
| `WhnfCoreClaimsR` | `whnfCore_claimsR`, with `iota_stepR` (batch g) and `proj_stepR` (batch e) |
| `WhnfClaimsR` | `whnf_claimsR_closed` (batch f) |
| `DefEqClaimsR` | `defeq_claimsR_full` (batch d) |
| `InferClaimsR` | `infer_claimsR`, with the five structural clauses (batches a-rest/b) and `inferProj_stepR` (batch e) |

`checkSoundR` (`Bridge/Claims.lean`) turns the step into the four claims
at every fuel, and the three wrappers (`inferTypeCore_bridge`,
`isDefEqCore_bridge`, `whnf_bridge`) are the forms every consumer uses.

**What the bridge is conditional on** is exactly `EnvR` — seven V-free
environment facts (`Bridge/Env.lean`), every one of them either a field
of `EnvTT`/`EnvS` or an immediate consequence.  There is no semantic
content anywhere in this tier: no `SetTheory`, no membership, no
interpretation.  That is the factoring the campaign was for.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode}

/-- **`CheckStepR`, proved.**  The bridge half of task #148. -/
theorem checkStepR (hg : mode.betaGate = false) : CheckStepR mode := by
  intro env m φ fuel ihwc ihw ihd ihi
  have hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ) := m.cval_closed
  exact ⟨whnfCore_claimsR m φ hg hcl
      (iota_stepR m φ hcl ihw ihd ihi) (proj_stepR m φ hcl ihwc ihw ihd ihi)
      ihwc ihw ihd ihi,
    whnf_claimsR_closed m φ hcl ihwc ihw,
    defeq_claimsR_full m φ hcl ihwc ihw ihd ihi,
    infer_claimsR m φ hcl
      (inferPi_stepR m φ hcl ihw ihi) (inferLam_stepR m φ hcl ihw ihi)
      (inferApp_stepR m φ hcl ihw ihd ihi) (inferLet_stepR m φ hcl ihw ihd ihi)
      (inferProj_stepR m φ hcl ihw ihi)⟩

/-- **The bridge, at every fuel.**  Successful inference yields an
`Infer` derivation up to `DefEq`; a positive defeq verdict yields a
`DefEq`; reduction yields a `Red`. -/
theorem checkBridge {env : Env} (hg : mode.betaGate = false)
    (m : EnvR env) (φ : Name → Nat) :
    ∀ fuel : Nat, WhnfCoreClaimsR mode m φ fuel ∧ WhnfClaimsR mode m φ fuel ∧
      DefEqClaimsR mode m φ fuel ∧ InferClaimsR mode m φ fuel :=
  checkSoundR (checkStepR hg) m φ

end Setlec.SetR
