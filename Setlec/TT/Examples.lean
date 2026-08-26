import Setlec.TT.Judgment

/-!
# Worked derivations

Regression tests for the rule shapes and — more importantly — for the
de Bruijn conventions of `Setlec/TT/Const.lean` and
`Setlec/TT/Judgment.lean`.  An off-by-one in a rule's `liftN`/`inst`
makes these fail to elaborate.

Note the explicit `(T := …)` annotations: the type slot of `eqE` is
semantically inert, so the equational rules leave it unconstrained.
That is deliberate — the eventual denotation function always has a
concrete type to hand and an unconstrained slot is one obligation
fewer — but it does mean hand-written derivations must say which one
they mean.
-/

namespace Setlec.TT
namespace Examples

/-- The identity on `Prop`, as a function `Sort 0 → Sort 0`. -/
example : HasType [] (.lam (.sort 0) (.bvar 0)) (.pi (.sort 0) (.sort 0)) :=
  .lam (.bvar (A := .sort 0) rfl)

/-- The *dependent* identity at level 0: `fun (A : Prop) (x : A) => x`.
This is the index test — the body's `bvar 0` must be typed at
`bvar 1`. -/
example :
    HasType [] (.lam (.sort 0) (.lam (.bvar 0) (.bvar 0)))
      (.pi (.sort 0) (.pi (.bvar 0) (.bvar 1))) :=
  .lam (.lam (.bvar (A := .bvar 0) rfl))

/-- `Nat.succ Nat.zero : Nat` — the `app` rule's `B.inst a` on a
non-dependent codomain. -/
example : HasType [] (natSuccT natZeroT) natT :=
  .app (A := natT) (B := natT) .const .const

/-- β, on the identity applied to zero. -/
example :
    HasType [] .prf
      (.eqE natT (.app (.lam natT (.bvar 0)) natZeroT) natZeroT) :=
  .beta (A := natT) .const

/-- ζ: `let n : Nat := 0; n` types at `Nat`, with the value
substituted into the body. -/
example : HasType [] (.letE natT natZeroT (.bvar 0)) natT :=
  .letE .const .const .const

/-- …and the corresponding zeta equation. -/
example :
    HasType [] .prf (.eqE natT (.letE natT natZeroT (.bvar 0)) natZeroT) :=
  .zeta

/-- Proof irrelevance at a concrete `Prop`: any two proofs of an
equation are equal. -/
example :
    HasType [] .prf (.eqE (.eqE natT natZeroT natZeroT) .prf .prf) :=
  .proofIrrel .eqType .refl .refl

/-- Conversion by an object-level equation: `0` also has type
`(fun _ : Nat => Nat) 0`, after converting along β. -/
example : HasType [] natZeroT (.app (.lam natT natT) natZeroT) :=
  .conv .const (.symm (T := natT) (T' := .sort 1) (.beta (T := natT) .const))

/-- η for functions, at `Nat → Nat`. -/
example :
    HasType [] .prf
      (.eqE (arrow natT natT)
        (.lam natT (.app (.const .natSucc []) (.bvar 0)))
        (.const .natSucc [])) :=
  .eta (T := arrow natT natT) (A := natT) (B := natT)
    (f := .const .natSucc []) .const

/-- Structure η for the basis pair, at `Prop × Prop`. -/
example (A B : VExpr) (hA : HasType [] A (.sort 0))
    (hB : HasType [] B (arrow A (.sort 0)))
    (p : VExpr) (hp : HasType [] p (psigmaT 0 0 A B)) :
    HasType [] .prf
      (.eqE (psigmaT 0 0 A B) p
        (psigmaMkT 0 0 A B (psigmaFstT 0 0 A B p) (psigmaSndT 0 0 A B p))) :=
  .psigmaEta hA hB hp

/-- Unit-like η for the basis unit. -/
example (x y : VExpr) (hx : HasType [] x (punitT 3))
    (hy : HasType [] y (punitT 3)) :
    HasType [] .prf (.eqE (punitT 3) x y) :=
  .punitEta hx hy

end Examples
end Setlec.TT
