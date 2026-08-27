import Setlec.SetR.Bridge.ReduceNat

/-!
# `CheckStepR`, assembled (task #148, T3)

The four quarters, put together: `whnfCore_claimsR`,
`whnf_claimsR_closed` (no obligation — batch (f) is discharged),
`defeq_claimsR_closed` and `infer_claimsR`.  Everything structural is
proved; everything else is one of the named `Prop`s below, each stated
at a checker function boundary or a checker configuration, so that every
consumer of an unproved step is visible in the source.

The bundle deliberately does **not** carry `ReduceNatStepR`: it is
proved (`reduceNat_stepR`, batch f), and a discharged obligation has no
business in an obligation record.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode}

/-- The outstanding clause obligations of `CheckStepR`.

Five of the eight (`InferPi/Lam/App/Let/ProjStepR`) sit downstream of
the `Red`-at-an-inferred-type finding recorded in
`Setlec/SetR/DESIGN.md`, and so does part of `IotaStepR` (its R12–R14
rescues) and of `DefEqStuckStepR` (its `stuckIrrel` dispatch); the rule
shapes those need are under decision.  `ProjStepR` and the congruence
part of `DefEqStuckStepR` are the pieces that are only partly
affected. -/
structure StepObligationsR (mode : CheckMode) {env : Env} (m : EnvR env)
    (φ : Name → Nat) (fuel : Nat) : Prop where
  /-- The ι clause (R11 + the R12–R14 rescues), at `iotaRecP`. -/
  iota : IotaStepR (mode := mode) m φ fuel
  /-- The `.proj` reduction clause (R6, R7), at `whnfCore`'s `.proj` case. -/
  proj : ProjStepR (mode := mode) m φ fuel
  /-- I6. -/
  inferPi : InferPiStepR (mode := mode) m φ fuel
  /-- I7. -/
  inferLam : InferLamStepR (mode := mode) m φ fuel
  /-- I8. -/
  inferApp : InferAppStepR (mode := mode) m φ fuel
  /-- I10. -/
  inferLet : InferLetStepR (mode := mode) m φ fuel
  /-- I9. -/
  inferProj : InferProjStepR (mode := mode) m φ fuel
  /-- D8/D9, at `proofIrrelP`. -/
  proofIrrel : ProofIrrelStepR (mode := mode) m φ fuel
  /-- D5–D7, D10–D14, at `defeqStep`'s stuck configuration. -/
  defeqStuck : DefEqStuckStepR (mode := mode) m φ fuel
  /-- D7's second entry point, at `defeqSpineP`. -/
  defeqSpine : DefEqSpineStepR (mode := mode) m φ fuel

/-- **`CheckStepR` from the clause obligations.**  The obligations are
supplied per knot level, with the four induction hypotheses in scope —
several of them (the stuck cascade, the ι clause) consume the claims at
`fuel` exactly as the proved quarters do. -/
theorem checkStepR_of
    (hob : ∀ (env : Env) (m : EnvR env) (φ : Name → Nat) (fuel : Nat),
      (∀ n ψ, VExpr.Closed (m.cval n ψ)) →
      WhnfCoreClaimsR mode m φ fuel → WhnfClaimsR mode m φ fuel →
      DefEqClaimsR mode m φ fuel → InferClaimsR mode m φ fuel →
      StepObligationsR mode m φ fuel) :
    CheckStepR mode := by
  intro env m φ fuel ihwc ihw ihd ihi
  have hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ) := m.cval_closed
  obtain ⟨hiota, hproj, hpi, hlam, happ, hlet, hiproj, hirr, hstk, hspine⟩ :=
    hob env m φ fuel hcl ihwc ihw ihd ihi
  exact ⟨whnfCore_claimsR m φ hcl hiota hproj ihwc ihw ihd ihi,
    whnf_claimsR_closed m φ hcl ihwc ihw,
    defeq_claimsR_closed m φ hcl ihwc (reduceNat_stepR m φ hcl ihw) hirr
      hstk hspine,
    infer_claimsR m φ hcl hpi hlam happ hlet hiproj⟩

end Setlec.SetR
