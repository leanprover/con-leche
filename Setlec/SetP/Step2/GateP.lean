import Setlec.SetP.Step2.WhnfP

/-!
# The β-gate's license, at the P currency (task #161, S12)

`Setlec/Kernel/CoreP.lean`'s gate skips the per-redex β certificate at
a λ whose validated datum is `.never`, under `mode.verified`.  S9
sealed *that* the gate is licensed — the claim's positive branch
consumes nothing — and pinned the gate LIVE with five `#guard`s.  This
module is the license as a **theorem**: the two facts a transposed β
clause needs where the ungated clause reads a certificate, and the
asymmetry fence stated so that a violation is a type error rather than
a review question.

Three statements, and the third is the fence:

* `gate_pwBit_ne_zero` — a fired gate's datum is positive at **every**
  valuation.  This is `pwBit_ne_zero_of_isNever` with the mode
  conjunct dropped, i.e. the sound half of
  `isNever_iff_forall_pwBit_ne_zero` read at the kernel's own gate
  expression;
* `AnnotOkP_beta_gate` — **the license**: at a fired gate the β step's
  interpretation equality and the reduct's truthfulness follow from
  the redex's own `AnnotOkP` slot, with no certificate premise of any
  kind.  Its proof is `AnnotOkP_beta_pos ∘ gate_pwBit_ne_zero`: one
  composition, which is exactly the S9 seal's "the positive branch
  already consumes nothing" made into a term;
* `gate_zero_kind_unreachable` — **the asymmetry fence.**  A fired
  gate and a zero-kind datum are contradictory, so the arm that
  consumes a certificate (`AnnotOkP_beta_zero`, whose `hmem` premise
  is the certificate's product) is unreachable under the gate.  A
  transposed obligation that reached for a certificate the gate
  skipped would have to inhabit this branch; it cannot.

The fence is one-directional by design and stays that way: the
**projection** certificate is not gated (`Kernel/CoreP.lean`), and the
zero-kind β certificate is not gated either — the gate's condition is
`isNever`, and `isNever_iff_forall_pwBit_ne_zero`'s *completeness* half
says no other datum is positive at every valuation.  The establishment
side of the asymmetry (`io_membership_fails_at_squash`) is untouched
here and by construction cannot be reached from these three.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Name BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V]

/-- **The gate's condition, read at the claims' split.**  The kernel
tests `mode.verified && mb.pw.isNever`; the claims split on
`pwBit φ mb.pw = 0` at the ambient valuation.  A fired gate puts the
datum on the positive side at *every* `φ` — the ∀-`φ` uniform form of
the split, and the sound half of `isNever_iff_forall_pwBit_ne_zero`. -/
theorem gate_pwBit_ne_zero {mode : CheckMode} {mb : BinderMeta}
    (hg : (mode.verified && mb.pw.isNever) = true) (φ : Name → Nat) :
    pwBit φ mb.pw ≠ 0 :=
  pwBit_ne_zero_of_isNever (by
    rcases Bool.and_eq_true .. |>.mp hg with ⟨-, h⟩; exact h) φ

/-- **THE β-GATE'S LICENSE.**  At a fired gate the β step's two
obligations — the interpretation equality and the reduct's
truthfulness — are discharged from the redex's own `AnnotOkP` slot.

**No certificate appears in this statement or in its proof.**  That is
the whole content of the gate: the run the kernel deletes
(`infer a` followed by `defeq ta ty`) supplies `AnnotOkP_beta_zero`'s
`hmem`, and at a `.never` datum `AnnotOkP_beta_zero` is not the arm
taken. -/
theorem AnnotOkP_beta_gate {mode : CheckMode} {mb : BinderMeta}
    (hg : (mode.verified && mb.pw.isNever) = true)
    {A b a : AVExpr} {φ : Name → Nat} {ρ : Nat → V}
    (h : AnnotOkP V ρ (.app (.lam (pwBit φ mb.pw) A b) a)) :
    interp2 V ρ (.app (.lam (pwBit φ mb.pw) A b) a)
        = interp2 V ρ (b.inst a) ∧
      AnnotOkP V ρ (b.inst a) :=
  AnnotOkP_beta_pos (gate_pwBit_ne_zero hg φ) h

/-- **THE ASYMMETRY FENCE.**  A fired gate and a zero-kind datum
cannot coexist.  The certificate-consuming arm of the β split
(`AnnotOkP_beta_zero`) is guarded by `pwBit φ mb.pw = 0`, so under the
gate that arm is *unreachable*: no transposed obligation can reach for
a certificate the gate skipped, and the establishment/consumption
asymmetry survives the transposition intact. -/
theorem gate_zero_kind_unreachable {mode : CheckMode} {mb : BinderMeta}
    (hg : (mode.verified && mb.pw.isNever) = true) {φ : Name → Nat}
    (hz : pwBit φ mb.pw = 0) : False :=
  gate_pwBit_ne_zero hg φ hz

end Setlec.SetR.Interp2
