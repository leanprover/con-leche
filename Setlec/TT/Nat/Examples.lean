import Setlec.TT.Nat.WfOps

/-!
# Worked instantiations

Regression tests for the interface of `Setlec/TT/Nat/*`: the lemma
families are hypothetical over an arbitrary term, so "the checker
accepted `Nat.add 12345 67890 = 80235`" becomes a derivation by
*instantiating* the family at `12345` and `67890`.  The point of these
examples is that the instantiation is immediate — the elaborator
computes `12345 + 67890` in the metalanguage and never unfolds
`numeral` at either literal.

The `Deq → HasType` step at the end shows the type slot is free: the
same `Deq` yields a derivation at `natT`, or at any other slot.
-/

namespace Setlec.TT
namespace NatExamples

variable {Γ : List VExpr}

/-- **The headline.**  Any `f` satisfying `Nat.add`'s certified
recurrences at numerals derives `f 12345 67890 ≡ 80235`, at the type
slot `Nat`. -/
example {f : VExpr}
    (h0 : ∀ a, Deq Γ (ap2 f (numeral a) natZeroT) (numeral a))
    (hS : ∀ a b, Deq Γ (ap2 f (numeral a) (natSuccT (numeral b)))
      (natSuccT (ap2 f (numeral a) (numeral b)))) :
    HasType Γ .prf
      (.eqE natT (ap2 f (numeral 12345) (numeral 67890)) (numeral 80235)) :=
  (numeral_add h0 hS 12345 67890).toHasType natT

/-- The same, read back at a different (inert) type slot. -/
example {f : VExpr}
    (h0 : ∀ a, Deq Γ (ap2 f (numeral a) natZeroT) (numeral a))
    (hS : ∀ a b, Deq Γ (ap2 f (numeral a) (natSuccT (numeral b)))
      (natSuccT (ap2 f (numeral a) (numeral b)))) :
    HasType Γ .prf
      (.eqE (.sort 37) (ap2 f (numeral 12345) (numeral 67890))
        (numeral 80235)) :=
  (numeral_add h0 hS 12345 67890).toHasType _

/-- A guarded operation: `Nat.div`, with its `Nat.ble` guard supplied
by `numeral_ble` — the composition the bridge will perform. -/
example {dv sb bl tv fv : VExpr}
    (hb0 : ∀ b, Deq Γ (ap2 bl natZeroT (numeral b)) tv)
    (hbS0 : ∀ a, Deq Γ (ap2 bl (natSuccT (numeral a)) natZeroT) fv)
    (hbSS : ∀ a b, Deq Γ (ap2 bl (natSuccT (numeral a)) (natSuccT (numeral b)))
      (ap2 bl (numeral a) (numeral b)))
    (hsub : ∀ a b, Deq Γ (ap2 sb (numeral a) (numeral b)) (numeral (a - b)))
    (hrec : ∀ a b, Deq Γ (ap2 bl (numeral b) (numeral a)) tv →
      Deq Γ (ap2 bl (numeral 1) (numeral b)) tv →
      Deq Γ (ap2 dv (numeral a) (numeral b))
        (natSuccT (ap2 dv (ap2 sb (numeral a) (numeral b)) (numeral b))))
    (hgt : ∀ a b, Deq Γ (ap2 bl (numeral b) (numeral a)) fv →
      Deq Γ (ap2 dv (numeral a) (numeral b)) natZeroT)
    (hzero : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral b)) fv →
      Deq Γ (ap2 dv (numeral a) (numeral b)) natZeroT) :
    Deq Γ (ap2 dv (numeral 80235) (numeral 12345)) (numeral 6) :=
  numeral_div (numeral_ble hb0 hbS0 hbSS) hsub hrec hgt hzero 80235 12345

/-- Numerals are `Nat`s — the typing correspondence, at a literal. -/
example : HasType [] (numeral 12345) natT := hasType_numeral 12345

end NatExamples
end Setlec.TT
