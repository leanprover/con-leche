import Setlec.TT.Nat.Numeral

/-!
# The structural `Nat` operations on numerals

One lemma family per operation with a certified structural fast path
(`natOpNames`: `pred`, `add`, `sub`, `mul`, `pow`, `beq`, `ble`).  Each
is **hypothetical over an arbitrary term `f`**: given that `f` satisfies
the operation's defining recurrences *at numerals*, `f` computes that
operation on numerals.  Nothing here names a constant, so the layer
stays free of any commitment about how the checker's `Nat.add` is
stored — built-in or unfolded stream definition, the lemma is the same.

## Where the shapes come from

The hypotheses are the checker's own certified recurrences
(`Setlec/Kernel/Core.lean`, `natOpEquations`) with the equations' two
free variables instantiated at numerals, and the proofs are the
meta-level literal inductions of `Setlec/Model/NatOps.lean`
(`natLit_add`, `natLit_sub`, …) transposed from value equality to
`Deq`.  Both correspondences are deliberate: the model-side proof is
the induction skeleton, and the certificate-side shape is what makes
the bridge's discharge of these hypotheses mechanical.

**The hypotheses are instantiated at numerals only** — weaker than the
model's "for all members of the `Nat` value", and all the induction
needs.  Every strengthening here would be an obligation for the bridge
to discharge, so there is none: not even a `HasType` premise survives.
-/

namespace Setlec.TT

variable {Γ : List VExpr}

/-- `Nat.pred` on numerals. -/
theorem numeral_pred {p : VExpr}
    (h0 : Deq Γ (.app p natZeroT) natZeroT)
    (hS : ∀ a, Deq Γ (.app p (natSuccT (numeral a))) (numeral a)) :
    ∀ a, Deq Γ (.app p (numeral a)) (numeral (a - 1))
  | 0 => h0
  | a + 1 => hS a

/-- `Nat.add` on numerals. -/
theorem numeral_add {f : VExpr}
    (h0 : ∀ a, Deq Γ (ap2 f (numeral a) natZeroT) (numeral a))
    (hS : ∀ a b, Deq Γ (ap2 f (numeral a) (natSuccT (numeral b)))
      (natSuccT (ap2 f (numeral a) (numeral b)))) :
    ∀ a b, Deq Γ (ap2 f (numeral a) (numeral b)) (numeral (a + b))
  | a, 0 => h0 a
  | a, b + 1 => (hS a b).trans (Deq.appArg (numeral_add h0 hS a b))

/-- `Nat.sub` on numerals (`pred` already computed). -/
theorem numeral_sub {f p : VExpr}
    (hpred : ∀ a, Deq Γ (.app p (numeral a)) (numeral (a - 1)))
    (h0 : ∀ a, Deq Γ (ap2 f (numeral a) natZeroT) (numeral a))
    (hS : ∀ a b, Deq Γ (ap2 f (numeral a) (natSuccT (numeral b)))
      (.app p (ap2 f (numeral a) (numeral b)))) :
    ∀ a b, Deq Γ (ap2 f (numeral a) (numeral b)) (numeral (a - b))
  | a, 0 => h0 a
  | a, b + 1 => by
    rw [show a - (b + 1) = a - b - 1 from by omega]
    exact ((hS a b).trans (Deq.appArg (numeral_sub hpred h0 hS a b))).trans
      (hpred (a - b))

/-- `Nat.mul` on numerals (`add` already computed). -/
theorem numeral_mul {f g : VExpr}
    (hadd : ∀ a b, Deq Γ (ap2 g (numeral a) (numeral b)) (numeral (a + b)))
    (h0 : ∀ a, Deq Γ (ap2 f (numeral a) natZeroT) natZeroT)
    (hS : ∀ a b, Deq Γ (ap2 f (numeral a) (natSuccT (numeral b)))
      (ap2 g (ap2 f (numeral a) (numeral b)) (numeral a))) :
    ∀ a b, Deq Γ (ap2 f (numeral a) (numeral b)) (numeral (a * b))
  | a, 0 => h0 a
  | a, b + 1 => by
    rw [show a * (b + 1) = a * b + a from Nat.mul_succ a b]
    exact ((hS a b).trans
      (Deq.ap2 (numeral_mul hadd h0 hS a b) Deq.refl)).trans (hadd (a * b) a)

/-- `Nat.pow` on numerals (`mul` already computed). -/
theorem numeral_pow {f g : VExpr}
    (hmul : ∀ a b, Deq Γ (ap2 g (numeral a) (numeral b)) (numeral (a * b)))
    (h0 : ∀ a, Deq Γ (ap2 f (numeral a) natZeroT) (natSuccT natZeroT))
    (hS : ∀ a b, Deq Γ (ap2 f (numeral a) (natSuccT (numeral b)))
      (ap2 g (ap2 f (numeral a) (numeral b)) (numeral a))) :
    ∀ a b, Deq Γ (ap2 f (numeral a) (numeral b)) (numeral (a ^ b))
  | a, 0 => h0 a
  | a, b + 1 => by
    rw [show a ^ (b + 1) = a ^ b * a from Nat.pow_succ a b]
    exact ((hS a b).trans
      (Deq.ap2 (numeral_pow hmul h0 hS a b) Deq.refl)).trans (hmul (a ^ b) a)

/-- `Nat.beq` on numerals.  `tv`/`fv` are the `Bool` constructor terms;
the layer never needs them to be distinct. -/
theorem numeral_beq {f tv fv : VExpr}
    (h00 : Deq Γ (ap2 f natZeroT natZeroT) tv)
    (h0S : ∀ b, Deq Γ (ap2 f natZeroT (natSuccT (numeral b))) fv)
    (hS0 : ∀ a, Deq Γ (ap2 f (natSuccT (numeral a)) natZeroT) fv)
    (hSS : ∀ a b, Deq Γ (ap2 f (natSuccT (numeral a)) (natSuccT (numeral b)))
      (ap2 f (numeral a) (numeral b))) :
    ∀ a b, Deq Γ (ap2 f (numeral a) (numeral b)) (if a = b then tv else fv)
  | 0, 0 => by rw [if_pos rfl]; exact h00
  | 0, b + 1 => by rw [if_neg (by omega)]; exact h0S b
  | a + 1, 0 => by rw [if_neg (by omega)]; exact hS0 a
  | a + 1, b + 1 => by
    refine (hSS a b).trans ?_
    have ih := numeral_beq h00 h0S hS0 hSS a b
    by_cases hab : a = b
    · rw [if_pos (by omega)]
      rwa [if_pos hab] at ih
    · rw [if_neg (by omega)]
      rwa [if_neg hab] at ih

/-- `Nat.ble` on numerals — the guard the WF-recursive operations'
recurrences are stated with (`Setlec/TT/Nat/WfOps.lean`). -/
theorem numeral_ble {f tv fv : VExpr}
    (h0 : ∀ b, Deq Γ (ap2 f natZeroT (numeral b)) tv)
    (hS0 : ∀ a, Deq Γ (ap2 f (natSuccT (numeral a)) natZeroT) fv)
    (hSS : ∀ a b, Deq Γ (ap2 f (natSuccT (numeral a)) (natSuccT (numeral b)))
      (ap2 f (numeral a) (numeral b))) :
    ∀ a b, Deq Γ (ap2 f (numeral a) (numeral b)) (if a ≤ b then tv else fv)
  | 0, b => by rw [if_pos (by omega)]; exact h0 b
  | a + 1, 0 => by rw [if_neg (by omega)]; exact hS0 a
  | a + 1, b + 1 => by
    refine (hSS a b).trans ?_
    have ih := numeral_ble h0 hS0 hSS a b
    by_cases hab : a ≤ b
    · rw [if_pos (by omega)]
      rwa [if_pos hab] at ih
    · rw [if_neg (by omega)]
      rwa [if_neg hab] at ih

end Setlec.TT
