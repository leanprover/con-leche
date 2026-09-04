import Setlec.SetP.Step2.InferP
import Setlec.SetP.Step2.InferIOP
import Setlec.SetP.Step2.WhnfP
import Setlec.SetP.Step2.DefEqP

/-!
# The P-tier step, assembled (task #161, P3.6)

The four quarters composed into `CheckStep2P`, and the induction
closed: the four soundness claims hold at **every** fuel, over the
validated-annotation reading, conditional on exactly three routed
input bundles and the validating mode.

Compare the canonical lane's frontier (`Capstone2E.lean`,
`checkStep2E_of_quarters`): **fifteen** residues, among them the
Θ-frozen sort-stability family (`BinderSortAgree2`, `LamCodSort2`,
`SortOfE/LamSortEInstLevels`, `SortAgree`, `EnvExtendStable`) — all of
which are *gone* here, dissolved into the P2 validation sites' own run
certificates, the bit laws, and the proved crossings
(`denotePInstLevels`, `deltaP_of`, `denoteP_beta`).  What remains
routed is of two kinds only:

* **install-tier obligations** — the environment's own facts
  (`ConstTypeP`, `AcvalValidP`, `AcvalDefnInstP`, `NatHeads2`), to be
  discharged when `EnvS2PM` lands (the P4 design note in DESIGN.md).
  `SortSem2`'s successor is *not* here: `sortSemAtP_of_claims`
  derives it from the claims one fuel down — with the annotation fuel
  gone its uses are induction-bounded, and one more of
  `Capstone2E`'s fifteen dissolves;
* **totality factors** — `denoteP` successes the dual-success claims
  cannot produce themselves (`WhnfCoreExistsP`, `InferExistsP`,
  `InferReadsP`, `WhnfReadsP`, `WhnfCoreReductExistsP`,
  `DenotePDeltaP`, and the routed clause residues
  `InferStrLitStepP`/`InferProjStepP`/`IotaStepP`/`ProjStepP`/
  `ReduceNatStepP`).  These overlap heavily and are the designated
  target of a consolidation seal: `denoteP` fails only out of
  fragment, and checker outputs stay in fragment — the upgrade path
  `Claims2P.lean`'s docstring names.

The mode hypothesis `μ.verified = true` is load-bearing exactly once
(the defeq binder arms' certificate extraction) and threaded uniformly.
-/

namespace Setlec.SetR.Interp2

open Setlec (CheckMode Env Name)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The P-generation step, from the quarters.** -/
theorem checkStep2P_of_quarters (hμ : μ.verified = true)
    (hwin : WhnfInputsP V μ) (hdin : DefEqInputsP μ V)
    (hiin : InferInputsP V μ) : CheckStep2P μ V :=
  fun env m φ fuel h1 h2 h3 h4 =>
    ⟨whnfCoreStepP_of hμ hwin env m φ fuel h1 h2 h3 h4,
     whnfStepP_of hμ hwin env m φ fuel h1 h2 h3 h4,
     defEqStepP_of hμ hdin env m φ fuel h1 h2 h3 h4,
     inferStepP_of hiin hμ env m φ fuel hμ h1 h2 h3 h4⟩

/-- **The P-tier soundness ladder, closed over fuel**: at a validating
mode, given the three input bundles, the four claims hold at every
fuel — the checker's runs are sound for the collapse-free
interpretation of the validated annotations. -/
theorem checkSoundP_of_inputs (hμ : μ.verified = true)
    (hwin : WhnfInputsP V μ) (hdin : DefEqInputsP μ V)
    (hiin : InferInputsP V μ) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2P μ m φ fuel ∧ WhnfClaims2P μ m φ fuel ∧
        DefEqClaims2P μ m φ fuel ∧ InferClaims2P μ m φ fuel :=
  checkSound2P (checkStep2P_of_quarters hμ hwin hdin hiin) m φ

/-! ## The five-way assembly (the io-license batch)

`Claims2PIO.lean` froze `CheckStep2P5` as "the campaign's remaining
bill"; with the io quarter's eleven arms closed
(`inferStepIOP_of`, `Step2/InferIOP.lean`) the bill is paid by
composition: the io slot consumes the same four steps plus the io
step, and the sealed four never mention the io claim (the knot
boundary — no full-lane claim is discharged from an io claim, by
construction). -/

/-- **The five-way step, from the quarters.** -/
theorem checkStep2P5_of_quarters (hμ : μ.verified = true)
    (hwin : WhnfInputsP V μ) (hdin : DefEqInputsP μ V)
    (hiin : InferInputsIOP V μ) : CheckStep2P5 μ V :=
  fun env m φ fuel h1 h2 h3 h4 h5 =>
    ⟨whnfCoreStepP_of hμ hwin env m φ fuel h1 h2 h3 h4,
     whnfStepP_of hμ hwin env m φ fuel h1 h2 h3 h4,
     defEqStepP_of hμ hdin env m φ fuel h1 h2 h3 h4,
     inferStepP_of hiin.base hμ env m φ fuel hμ h1 h2 h3 h4,
     inferStepIOP_of hiin hμ env m φ fuel hμ h1 h2 h3 h4 h5⟩

/-- **The five-way ladder, closed over fuel**: the four sealed claims
and the io claim hold at every fuel, at a validating mode, given the
routed input bundles.  This is what B4's driver-side skip baking
consumes at each io call site. -/
theorem checkSoundP5_of_inputs (hμ : μ.verified = true)
    (hwin : WhnfInputsP V μ) (hdin : DefEqInputsP μ V)
    (hiin : InferInputsIOP V μ) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) :
    ∀ fuel : Nat,
      WhnfCoreClaims2P μ m φ fuel ∧ WhnfClaims2P μ m φ fuel ∧
        DefEqClaims2P μ m φ fuel ∧ InferClaims2P μ m φ fuel ∧
          InferClaimsIO2P μ m φ fuel :=
  checkSound2P5 (checkStep2P5_of_quarters hμ hwin hdin hiin) m φ

end Setlec.SetR.Interp2
