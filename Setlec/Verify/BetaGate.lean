import Setlec.Kernel.Core

/-!
# The β gate's dead-branch collapse (task #161, S13a)

`betaGateFires` (`Setlec/Kernel/Core.lean`) is the *one* β-certificate
gate predicate, shared by every β-cert lane (the pure body, the cached
`whnfAppI`/`betaPeelI` twins, and the pure mirror in
`Verify/BetaSpine.lean`).  This module is its whole proof
interface, and it is deliberately small:

* **`betaGateFires_off` — THE DEAD-BRANCH COLLAPSE.**  At a mode whose
  gate is off the predicate is `false`, so the gated `if` takes its
  `else` arm — which is the pre-gate clause *byte-for-byte*.  Every
  pre-gate proof of every non-gated mode is therefore one `simp only`
  from its old form, and that rewrite is the same lemma at every site.
  This is the *whole* reason the gate is a pure early return rather
  than a wrapper around the certificate's `Bool`;
* **`isNever_of_betaGateFires`** — a fired gate's datum is `.never`,
  which is what the P tier's licensing composition
  (`AnnotOkP_beta_gate`, `SetP/Step2/GateP.lean`, via
  `pwBit_ne_zero_of_isNever`) consumes.  No certificate appears in it;
* **`verified_isNever_of_betaGateFires`** — a fired gate is a verified
  mode's gate, which is the pair the P tier's licensing theorem is
  stated against.  (The mode-level coverage certificates that used to
  sit here retired with the mode set they partitioned; see below.)

The module imports `Kernel.Core` and nothing else: it is base-tier.
-/

namespace Setlec

variable {mode : CheckMode} {pw : PropWhen}

/-- **THE DEAD-BRANCH COLLAPSE.**  At `betaGate = false` the gate never
fires, so the gated `if`'s `else` arm — the pre-gate clause, verbatim
— is the one taken. -/
@[simp] theorem betaGateFires_off (h : mode.betaGate = false) :
    betaGateFires mode pw = false := by
  simp [betaGateFires, h]

/-- The gate is off at `.noModel`. -/
@[simp] theorem betaGate_off_noModel :
    CheckMode.betaGate .noModel = false := rfl

/-- The gate is on at `.setModel` — the one verified mode. -/
@[simp] theorem betaGate_on_setModel :
    CheckMode.betaGate .setModel = true := rfl

/-! ## The coverage certificates, RETIRED (2026-09-05)

`CheckMode.verified_of_betaGate` (a gated mode is a verified mode) and
`CheckMode.betaGate_off_or_verified` (every mode is ungated or
verified) were a **partition of the capstone families**: ungated modes
were the R letters', verified modes the P letters'.  With one verified
mode and one unverified one there is no partition to certify — the
statements would be true and empty.  The user's ruling at the SetR
removal is that they go, not that they be restated one-sided:
*coverage certificates were the pathology.*  What the fence actually
needs is stated where it is consumed (`AnnotOkP_beta_gate`,
`SetP/Step2/GateP.lean`), against the datum, not against the mode
set. -/

/-- A fired gate's datum is `.never`. -/
theorem isNever_of_betaGateFires (h : betaGateFires mode pw = true) :
    pw.isNever = true :=
  (Bool.and_eq_true .. |>.mp h).2

/-- A fired gate is a verified mode's gate: the pair the P tier's
licensing theorem (`AnnotOkP_beta_gate`) is stated against. -/
theorem verified_isNever_of_betaGateFires
    (h : betaGateFires mode pw = true) :
    (mode.verified && pw.isNever) = true := by
  rcases Bool.and_eq_true .. |>.mp h with ⟨hg, hn⟩
  cases mode <;> simp_all [CheckMode.betaGate, CheckMode.verified]

/-! ## The template bridge (task #172, batch B2)

`CoreCfg` (`Setlec/Kernel/CoreCfg.lean`) replaces the mode flag as the
body template's parameter.  These three are the whole bridge, and all
three are `rfl`: `cfgOf`'s fields are *projections of a literal
constructor*, so a config read is the old accessor definitionally even
at a **variable** mode.  That is what let the template be introduced
without disturbing a landed statement. -/

/-- The template's β field at `cfgOf mode` **is** the gate predicate. -/
@[simp] theorem cfgOf_betaSkip :
    (cfgOf mode).betaSkip pw = betaGateFires mode pw := rfl

/-- The template's verified field at `cfgOf mode` **is** the accessor. -/
@[simp] theorem cfgOf_verified :
    (cfgOf mode).verified = mode.verified := rfl

/-- The transitional ι-cone field at `cfgOf mode` **is** the mode. -/
@[simp] theorem cfgOf_iotaMode : (cfgOf mode).iotaMode = mode := rfl

/-- **The P core's β branch reads the datum, not a flag**: at `cfgP`
the skip predicate is the redex's own validated annotation. -/
theorem cfgP_betaSkip_eq_setModel (pw : PropWhen) :
    cfgP.betaSkip pw = betaGateFires .setModel pw := rfl

end Setlec
