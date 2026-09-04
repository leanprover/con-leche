import Setlec.Kernel.Core

/-!
# The β gate's dead-branch collapse (task #161, S13a)

`betaGateFires` (`Setlec/Kernel/Core.lean`) is the *one* β-certificate
gate predicate, shared by all four β-cert lanes (the pure body, the
interned `whnfAppI`/`betaPeelI`, their cached twins, and the pure
mirror in `Verify/BetaSpine.lean`).  This module is its whole proof
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
* **`CheckMode.verified_of_betaGate`** — the gate refines `verified`:
  the gate reads a *validated* annotation, so a gated mode is a
  verified mode.  This is the asymmetry fence at the mode level, and
  it is what lets the P capstone's existing `μ.verified = true` letter
  cover the gated mode with no new hypothesis.

The module imports `Kernel.Core` and nothing else: it is base-tier,
consumed by the R lane and the P lane alike.
-/

namespace Setlec

variable {mode : CheckMode} {pw : PropWhen}

/-- **THE DEAD-BRANCH COLLAPSE.**  At `betaGate = false` the gate never
fires, so the gated `if`'s `else` arm — the pre-gate clause, verbatim
— is the one taken. -/
@[simp] theorem betaGateFires_off (h : mode.betaGate = false) :
    betaGateFires mode pw = false := by
  simp [betaGateFires, h]

/-- The gate is off at `.setModel`. -/
@[simp] theorem betaGate_off_setModel :
    CheckMode.betaGate .setModel = false := rfl

/-- The gate is off at `.noModel`. -/
@[simp] theorem betaGate_off_noModel :
    CheckMode.betaGate .noModel = false := rfl

/-- The gate is on at `.setModelP`, and there only. -/
@[simp] theorem betaGate_on_setModelP :
    CheckMode.betaGate .setModelP = true := rfl

/-- A gated mode is a verified mode: the gate reads a *validated*
annotation, so `betaGate` refines `verified` — the asymmetry fence at
the mode level, and the reason the P capstone's `μ.verified = true`
letter already covers the gated mode. -/
theorem CheckMode.verified_of_betaGate (h : mode.betaGate = true) :
    mode.verified = true := by
  cases mode <;> simp_all [CheckMode.betaGate, CheckMode.verified]

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
  simp [CheckMode.verified_of_betaGate hg, hn]

end Setlec
