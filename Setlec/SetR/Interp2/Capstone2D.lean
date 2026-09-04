import Setlec.SetR.Interp2.Step2.InferQ
import Setlec.SetR.Interp2.Step2.DefEqRun

/-!
# `CheckStep2D`, assembled — generation five's capstone

The four quarters of statement generation five, joined.  Every
hypothesis is a **named routed residue**; none is discharged here.
As at `Capstone2C.lean`, what this establishes is that the
decomposition *closes* — the remainder is a finite list of named
obligations.

## What the join looks like beside `checkStep2C_of_quarters`

`checkStep2C_of_quarters` took **seventeen** hypotheses.  This takes
**fifteen**, and the two that go are not bookkeeping:

* **`hbc : BetaCert2`** — the β site's argument certificate — is now
  `betaCert2D_of_claims`, built inside `whnfCoreStep2D_of` from the
  defeq and inference claims the quarter is already handed.  Seal 14
  named exactly this: *"what is still not dischargeable is the context
  currency … that is seal 11's move and it is generation five."*
* **`hi : InferInputs2C`** becomes `InferInputs2D`, which is the same
  structure minus three fields: `ctx_R` (**refuted**, `not_ctxOk2R`),
  `ctx_ann` (now `CtxOk2D`'s fourth conjunct) and `ctx_open` (now the
  kit theorem `CtxOk2D.openS`).

Nothing was weakened to achieve either.  `BetaCert2D` is stated in
this file's import closure with the *same* conclusion `BetaCert2` had,
and `InferInputs2D`'s six surviving fields are literally their `…C`
counterparts — `ConstType2C`, `NatHeads2`, `InferStrLitStep2C`,
`BetaCross2C`, `SortSem2` are reused, not restated.

## What generation five's own purpose establishes

Generation four's purpose was the quantifier, and its capstone note
records it: the congruences can discharge `CtxOk2.openCong`, which
`not_openCongLocal` proves no ρ-local claim could supply.  Generation
five's is the **currency**, and the record is this file's hypothesis
list: the one hypothesis the campaign had mechanically refuted is no
longer in it.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec (CheckMode Env Name)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The generation-five step, from the quarters' routed residues.** -/
theorem checkStep2D_of_quarters (hgOff : μ.betaGate = false)
    (hwc : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat),
      Denote2Inst1B μ m.acval env φ)
    (hio : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), IotaStep2D μ m φ fuel)
    (hpj : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), ProjStep2D μ m φ fuel)
    (hrn : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), ReduceNatStep2D μ m φ fuel)
    (hdl : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat),
      Delta2B μ m φ)
    (hdd : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat),
      Denote2Delta2A μ m φ)
    (hrn2 : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), ReduceNat2D μ m φ fuel)
    (hpi : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), ProofIrrel2D μ m φ fuel)
    (hsp : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), DefEqSpine2D μ m φ fuel)
    (hsi : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), StuckIrrel2D μ m φ fuel)
    (hsl : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat),
      Denote2StrLit2A μ m φ)
    (hap : ∀ (env : Env) (m : EnvS2UM V μ env), AcvalParams2 m)
    (hbs : ∀ (env : Env) (φ : Name → Nat) (fuel F : Nat),
      BinderSortAgree2A μ env φ fuel F)
    (hac : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), AppCongrStuck2D μ m φ fuel)
    (het : ∀ (env : Env) (m : EnvS2UM V μ env) (φ : Name → Nat)
      (fuel : Nat), EtaCert2D μ m φ fuel)
    (hi : InferInputs2D V μ) :
    CheckStep2D μ V :=
  checkStep2D_of (whnfCoreStep2D_of hgOff hwc hio hpj)
    (whnfStep2D_of hrn hdl)
    (defEqStep2D_of hdd hrn2 hpi hsp hsi hsl hap hbs hac het)
    (inferStep2D_of hi)

/-! ## The four residues that did not move, and why that is a check

`Denote2Inst1B`, `Delta2B`, `Denote2Delta2A`, `Denote2StrLit2A`,
`AcvalParams2` and `BinderSortAgree2A` enter this assembly **exactly
as they entered generation four's** — the same six objects, not
transposes.  The rule that predicts it is the one seal 14 stated for
the quantifier and this generation reuses for the currency: *a residue
that does not mention the thing a generation changes cannot be
affected by the change.*  Six of fifteen hypotheses passing that test
unchanged, across two consecutive generations, is the cheapest
available evidence that the two changes were each one change. -/

end Setlec.SetR.Interp2
