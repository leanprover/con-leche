import Setlec.SetR.Interp2.Step2.InferQ
import Setlec.SetR.Interp2.Step2.Whnf
import Setlec.SetR.Interp2.Step2.DefEqRun

/-!
# `CheckStep2B`, assembled — migration step 3's capstone

The four quarters, joined.  Every hypothesis below is a **named routed
residue** owned by one quarter; none is a claim about the checker's
runs, and none is discharged here.  What this file establishes is that
the *decomposition closes*: the corrected statement follows from the
residues and nothing else, so the remaining work is a finite list of
named obligations rather than an open question about the shape of the
induction.

Three generations of the statement were needed to get here
(`Claims2` → `Claims2A` → `Claims2B`), and the two discarded ones are
kept with their refutations.  The lineage is the point: each
generation was refuted by a *consumer*, not by inspection, and the
consumers were the four quarters running in parallel against it.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec (CheckMode Env Name)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The step, from the four quarters' routed residues.** -/
theorem checkStep2B_of_quarters
    (hwc : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat),
      Denote2Inst1B μ m.acval env φ)
    (hbc : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), BetaCert2 μ m φ fuel)
    (hio : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), IotaStep2B μ m φ fuel)
    (hpj : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), ProjStep2B μ m φ fuel)
    (hrn : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNatStep2 μ m φ fuel)
    (hdl : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat),
      Delta2B μ m φ)
    (hd : DefEqStep2BP μ V) (hi : InferInputs2A V μ) :
    CheckStep2B μ V :=
  checkStep2B_of (whnfCoreStep2B_of hwc hbc hio hpj)
    (whnfStep2B_of hrn hdl) (defEqStep2B_of hd) (inferStep2B_of hi)

/-- **The induction, from the same.**  `checkSound2B` applied to the
assembly: at every fuel, all four claims. -/
theorem checkSound2B_of_quarters {env : Env}
    (hwc : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat),
      Denote2Inst1B μ m.acval env φ)
    (hbc : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), BetaCert2 μ m φ fuel)
    (hio : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), IotaStep2B μ m φ fuel)
    (hpj : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), ProjStep2B μ m φ fuel)
    (hrn : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat)
      (fuel : Nat), ReduceNatStep2 μ m φ fuel)
    (hdl : ∀ (env : Env) (m : EnvS2 V env) (φ : Name → Nat),
      Delta2B μ m φ)
    (hd : DefEqStep2BP μ V) (hi : InferInputs2A V μ)
    (m : EnvS2 V env) (φ : Name → Nat) (fuel : Nat) :
    WhnfCoreClaims2B μ m φ fuel ∧ WhnfClaims2B μ m φ fuel ∧
      DefEqClaims2B μ m φ fuel ∧ InferClaims2A μ m φ fuel :=
  checkSound2B
    (checkStep2B_of_quarters hwc hbc hio hpj hrn hdl hd hi) m φ fuel

end Setlec.SetR.Interp2
