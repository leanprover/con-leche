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
        (psigmaMkT 0 0 A B (pfstT p) (psndT p))) :=
  .psigmaEta hA hB hp

/-- Unit-like η for the basis unit. -/
example (x y : VExpr) (hx : HasType [] x (punitT 3))
    (hy : HasType [] y (punitT 3)) :
    HasType [] .prf (.eqE (punitT 3) x y) :=
  .punitEta hx hy

/-- The first projection of a pair, typed from its subject alone: the
rule reads `A` and `B` off the premise, and the *term* `p.1` mentions
neither. -/
example (A B : VExpr) (hA : HasType [] A (.sort 3))
    (hB : HasType [] B (arrow A (.sort 5)))
    (p : VExpr) (hp : HasType [] p (psigmaT 3 5 A B)) :
    HasType [] (pfstT p) A :=
  .projFst hA hB hp

/-- …and the second, dependent on the first. -/
example (A B : VExpr) (hA : HasType [] A (.sort 3))
    (hB : HasType [] B (arrow A (.sort 5)))
    (p : VExpr) (hp : HasType [] p (psigmaT 3 5 A B)) :
    HasType [] (psndT p) (.app B (pfstT p)) :=
  .projSnd hA hB hp

/-- ι for the first projection: `(mk a b).1 ≡ a`. -/
example (A B a b : VExpr) (hA : HasType [] A (.sort 3))
    (hB : HasType [] B (arrow A (.sort 5)))
    (ha : HasType [] a A) (hb : HasType [] b (.app B a)) :
    HasType [] .prf (.eqE A (pfstT (psigmaMkT 3 5 A B a b)) a) :=
  .projFstMk hA hB ha hb

/-- Projection congruence: equal subjects have equal fields.  This is
the rule the checker's `.proj`-vs-`.proj` comparison needs, and it is
*not* derivable from the other congruences — `proj` is not an
application. -/
example (a b : VExpr) (T : VExpr) (h : HasType [] .prf (.eqE T a b)) :
    HasType [] .prf (.eqE T (pfstT a) (pfstT b)) :=
  .congrProj h

/-! ## Four basis constants the layer does *not* need

`Eq.rec`, `PSigma'.rec`, `PSigma'.fst` and `PSigma'.snd` are absent
from `BConst` because they are derivable.  All four derivations are
mechanized below, and each removes an index-heavy dependent type from
`Setlec/TT/Const.lean`.

The two projections are worth a word: they are derivable *because*
`proj` is a former whose typing rule reads the pair's type arguments
off its premise.  A layer that took the projections as constants and
no former could not go the other way — that is the asymmetry which
made the former the right primitive (task #119; see
`Setlec/TT/Syntax.lean`). -/

/-- **`PSigma'.fst` is derivable**: `fun A B p => p.1` has the
constant's old type. -/
theorem psigmaFst_derivable {u v : Nat} :
    HasType []
      (.lam (.sort u) (.lam (arrow (.bvar 0) (.sort v))
        (.lam (psigmaT u v (.bvar 1) (.bvar 0)) (pfstT (.bvar 0)))))
      (.pi (.sort u) (.pi (arrow (.bvar 0) (.sort v))
        (.pi (psigmaT u v (.bvar 1) (.bvar 0)) (.bvar 2)))) :=
  .lam (.lam (.lam (.projFst
    (.bvar (A := .sort u) rfl)
    (.bvar (A := arrow (.bvar 0) (.sort v)) rfl)
    (.bvar (A := psigmaT u v (.bvar 1) (.bvar 0)) rfl))))

/-- **`PSigma'.snd` is derivable**: `fun A B p => p.2`, at the
dependent codomain the constant used to spell with `PSigma'.fst`. -/
theorem psigmaSnd_derivable {u v : Nat} :
    HasType []
      (.lam (.sort u) (.lam (arrow (.bvar 0) (.sort v))
        (.lam (psigmaT u v (.bvar 1) (.bvar 0)) (psndT (.bvar 0)))))
      (.pi (.sort u) (.pi (arrow (.bvar 0) (.sort v))
        (.pi (psigmaT u v (.bvar 1) (.bvar 0))
          (.app (.bvar 1) (pfstT (.bvar 0)))))) :=
  .lam (.lam (.lam (.projSnd
    (.bvar (A := .sort u) rfl)
    (.bvar (A := arrow (.bvar 0) (.sort v)) rfl)
    (.bvar (A := psigmaT u v (.bvar 1) (.bvar 0)) rfl))))

/-- **`Eq.rec` is derivable**: once equality is reflected, transport is
the identity, so `fun A a M m b h => m` has the recursor's type.  The
step that makes it work is `congrEq`: it retypes the canonical proof
`prf : a = a` as a proof of `a = b`, after which proof irrelevance
identifies it with `h` and two `congrApp`s move the motive. -/
theorem eqRec_derivable {Γ : List VExpr} {A a b M m h : VExpr}
    (hh : HasType Γ h (.eqE A a b))
    (hm : HasType Γ m (.app (.app M a) .prf)) :
    HasType Γ m (.app (.app M b) h) := by
  -- the canonical proof, retyped from `a = a` to `a = b`
  have hprf : HasType Γ .prf (.eqE A a b) :=
    .conv (A := .eqE A a a) (T := .sort 0) (.refl (T := A))
      (.congrEq (T := A) (T' := A) (T'' := .sort 0) (S := A) (S' := A)
        (a := a) (a' := a) (b := a) (b' := b) (.refl (T := A)) hh)
  -- …hence indistinguishable from `h`
  have hirr : HasType Γ .prf (.eqE (.eqE A a b) .prf h) :=
    .proofIrrel .eqType hprf hh
  -- move the motive along both arguments
  exact .conv (T := .sort 0) hm
    (.congrApp (T := .sort 0) (T' := .eqE A a b) (T'' := .sort 0)
      (.congrApp (T := .sort 0) (T' := A) (T'' := .sort 0)
        (.refl (T := .sort 0)) hh)
      hirr)

/-- **`PSigma'.rec` is derivable**: the minor premise applied to the two
projections has the right type once the subject is converted along
structure η. -/
theorem psigmaRec_derivable {Γ : List VExpr} {u v : Nat}
    {A B M f p : VExpr}
    (hA : HasType Γ A (.sort u)) (hB : HasType Γ B (arrow A (.sort v)))
    (hp : HasType Γ p (psigmaT u v A B))
    (hf : HasType Γ (.app (.app f (pfstT p)) (psndT p))
      (.app M (psigmaMkT u v A B (pfstT p) (psndT p)))) :
    HasType Γ (.app (.app f (pfstT p)) (psndT p)) (.app M p) :=
  .conv (T := .sort 0) hf
    (.congrApp (T := .sort 0) (T' := psigmaT u v A B) (T'' := .sort 0)
      (.refl (T := .sort 0))
      (.symm (T' := psigmaT u v A B) (.psigmaEta hA hB hp)))

end Examples
end Setlec.TT
