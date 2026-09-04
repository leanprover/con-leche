import Setlec.SetR.Interp2.Step2.InferQ
import Setlec.SetR.Interp2.Step2.DefEqRun

/-!
# `CheckStep2C`, assembled — generation four's capstone

The four quarters of statement generation four, joined.  Every
hypothesis is a **named routed residue**; none is discharged here.
As at `Capstone.lean`, what this establishes is that the decomposition
*closes* — the remainder is a finite list of named obligations.

Generation four's own purpose is separately established: the `∀`/`λ`
congruences can now discharge `CtxOk2.openCong`, which
`not_openCongLocal` proves no ρ-local claim could supply.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec (CheckMode Env Name)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The generation-four step, from the quarters' routed residues.** -/
theorem checkStep2C_of_quarters (hgOff : μ.betaGate = false)
    (hwc : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat),
      Denote2Inst1B μ m.acval env φ)
    (hbc : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), BetaCert2 μ m φ fuel)
    (hio : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), IotaStep2C μ m φ fuel)
    (hpj : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), ProjStep2C μ m φ fuel)
    (hrn : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), ReduceNatStep2C μ m φ fuel)
    (hdl : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat),
      Delta2B μ m φ)
    (hdd : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat),
      Denote2Delta2A μ m φ)
    (hrn2 : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2C μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2C μ m φ fuel)
    (hsp : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2C μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2C μ m φ fuel)
    (hsl : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat),
      Denote2StrLit2A μ m φ)
    (hap : ∀ (env : Env) (m : EnvS2UM V μ env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel F : Nat),
      BinderSortAgree2A μ env φ fuel F)
    (hac : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2C μ m φ fuel)
    (het : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), EtaCert2C μ m φ fuel)
    (hi : InferInputs2C V μ) :
    CheckStep2C μ V :=
  checkStep2C_of (whnfCoreStep2C_of hgOff hwc hbc hio hpj)
    (whnfStep2C_of hrn hdl)
    (defEqStep2C_of hgOff hdd hrn2 hpi hsp hsi hsl hap hbs hac het)
    (inferStep2C_of hi)

end Setlec.SetR.Interp2
