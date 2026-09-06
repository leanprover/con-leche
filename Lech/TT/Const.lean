import Lech.TT.Subst

/-!
# Types of the built-in constants

`BConst.type c us` is the (closed) type of the constant `c` at the
level instantiation `us`.  Level lists shorter than `c.numLevels` read
`0` for the missing entries, so `BConst.type` is total and the `const`
typing rule needs no arity side condition.

The smart constructors below (`natT`, `psigmaT`, …) are also what the
equational rules of `Lech/TT/Judgment.lean` are written with, and
what the eventual denotation function will emit.
-/

namespace Lech.TT

open VExpr

/-- Level lookup with a `0` default. -/
def lv (us : List Nat) (i : Nat) : Nat := us.getD i 0

/-! ## Smart constructors -/

/-- `Nat` -/
def natT : VExpr := .const .nat []
/-- `Nat.zero` -/
def natZeroT : VExpr := .const .natZero []
/-- `Nat.succ e` -/
def natSuccT (e : VExpr) : VExpr := .app (.const .natSucc []) e
/-- `@Nat.rec.{u} M z s t` -/
def natRecT (u : Nat) (M z s t : VExpr) : VExpr :=
  mkAppN (.const .natRec [u]) [M, z, s, t]

/-- `PUnit.{u}` -/
def punitT (u : Nat) : VExpr := .const .punit [u]
/-- `PUnit.unit.{u}` -/
def punitUnitT (u : Nat) : VExpr := .const .punitUnit [u]
/-- `@PUnit.rec.{u,v} M m t` -/
def punitRecT (u v : Nat) (M m t : VExpr) : VExpr :=
  mkAppN (.const .punitRec [u, v]) [M, m, t]

/-- `@PSigma'.{u,v} A B` -/
def psigmaT (u v : Nat) (A B : VExpr) : VExpr :=
  mkAppN (.const .psigma [u, v]) [A, B]
/-- `@PSigma'.mk.{u,v} A B a b` -/
def psigmaMkT (u v : Nat) (A B a b : VExpr) : VExpr :=
  mkAppN (.const .psigmaMk [u, v]) [A, B, a, b]
/-- `p.1` — field `0` of a pair.  A *former*, so it needs neither the
pair's type arguments nor its levels: the typing rule reads them off
the premise (`Lech/TT/Syntax.lean`). -/
def pfstT (p : VExpr) : VExpr := .proj 0 p
/-- `p.2` — field `1` of a pair. -/
def psndT (p : VExpr) : VExpr := .proj 1 p

/-- `Empty.{u}` (level-polymorphic: `Empty.{0}` is `False`) -/
def emptyT (u : Nat) : VExpr := .const .empty [u]
/-- `¬ A`, i.e. `A → False` -/
def negT (A : VExpr) : VExpr := arrow A (emptyT 0)

/-- `@Quot.{u} A r` -/
def quotT (u : Nat) (A r : VExpr) : VExpr :=
  mkAppN (.const .quot [u]) [A, r]
/-- `@Quot.mk.{u} A r a` -/
def quotMkT (u : Nat) (A r a : VExpr) : VExpr :=
  mkAppN (.const .quotMk [u]) [A, r, a]
/-- `@Quot.lift.{u,v} A r B f h q` -/
def quotLiftT (u v : Nat) (A r B f h q : VExpr) : VExpr :=
  mkAppN (.const .quotLift [u, v]) [A, r, B, f, h, q]

/-- The type of a relation on `A`, where `A` is the term `a` in the
ambient context: `A → A → Prop`.  (Written out rather than built from
`arrow`, because the second domain sits under one extra binder.) -/
def relT (A : VExpr) : VExpr := .pi A (.pi A.lift (.sort 0))

/-! ## The type assignment -/

/-- The type of each built-in constant. -/
def BConst.type : BConst → List Nat → VExpr
  | .nat, _ => .sort 1
  | .natZero, _ => natT
  | .natSucc, _ => arrow natT natT
  | .natRec, us =>
    let u := lv us 0
    -- `∀ (M : Nat → Sort u), M 0 → (∀ n, M n → M (n+1)) → ∀ t, M t`
    .pi (arrow natT (.sort u)) <|
    .pi (.app (.bvar 0) natZeroT) <|
    .pi (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (natSuccT (.bvar 1))))) <|
    .pi natT <|
    .app (.bvar 3) (.bvar 0)
  | .punit, us => .sort (lv us 0)
  | .punitUnit, us => punitT (lv us 0)
  | .punitRec, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ (M : PUnit.{u} → Sort v), M unit → ∀ t, M t`
    .pi (arrow (punitT u) (.sort v)) <|
    .pi (.app (.bvar 0) (punitUnitT u)) <|
    .pi (punitT u) <|
    .app (.bvar 2) (.bvar 0)
  | .psigma, us =>
    let u := lv us 0; let v := lv us 1
    .pi (.sort u) <| .pi (arrow (.bvar 0) (.sort v)) <| .sort (Nat.max u v)
  | .psigmaMk, us =>
    let u := lv us 0; let v := lv us 1
    .pi (.sort u) <|
    .pi (arrow (.bvar 0) (.sort v)) <|
    .pi (.bvar 1) <|
    .pi (.app (.bvar 1) (.bvar 0)) <|
    psigmaT u v (.bvar 3) (.bvar 2)
  | .empty, us => .sort (lv us 0)
  | .emptyRec, us =>
    let u := lv us 0; let v := lv us 1
    .pi (arrow (emptyT u) (.sort v)) <| .pi (emptyT u) <| .app (.bvar 1) (.bvar 0)
  | .quot, us =>
    let u := lv us 0
    .pi (.sort u) <| .pi (relT (.bvar 0)) <| .sort u
  | .quotMk, us =>
    let u := lv us 0
    .pi (.sort u) <| .pi (relT (.bvar 0)) <| .pi (.bvar 1) <|
      quotT u (.bvar 2) (.bvar 1)
  | .quotLift, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ A r B (f : A → B), (∀ a b, r a b → f a = f b) → Quot A r → B`
    .pi (.sort u) <|
    .pi (relT (.bvar 0)) <|
    .pi (.sort v) <|
    .pi (.pi (.bvar 2) (.bvar 1)) <|
    .pi (.pi (.bvar 3) (.pi (.bvar 4)
          (.pi (mkAppN (.bvar 4) [.bvar 1, .bvar 0])
            (.eqE (.bvar 4) (.app (.bvar 3) (.bvar 2))
              (.app (.bvar 3) (.bvar 1)))))) <|
    .pi (quotT u (.bvar 4) (.bvar 3)) <|
    .bvar 3
  | .quotInd, us =>
    let u := lv us 0
    .pi (.sort u) <|
    .pi (relT (.bvar 0)) <|
    .pi (.pi (quotT u (.bvar 1) (.bvar 0)) (.sort 0)) <|
    .pi (.pi (.bvar 2) (.app (.bvar 1) (quotMkT u (.bvar 3) (.bvar 2) (.bvar 0)))) <|
    .pi (quotT u (.bvar 3) (.bvar 2)) <|
    .app (.bvar 2) (.bvar 0)
  | .quotSound, us =>
    let u := lv us 0
    .pi (.sort u) <|
    .pi (relT (.bvar 0)) <|
    .pi (.bvar 1) <|
    .pi (.bvar 2) <|
    .pi (mkAppN (.bvar 2) [.bvar 1, .bvar 0]) <|
    .eqE (quotT u (.bvar 4) (.bvar 3))
      (quotMkT u (.bvar 4) (.bvar 3) (.bvar 2))
      (quotMkT u (.bvar 4) (.bvar 3) (.bvar 1))
  | .propext, _ =>
    -- `∀ (A B : Prop), (A → B) → (B → A) → A = B`
    .pi (.sort 0) <| .pi (.sort 0) <|
    .pi (.pi (.bvar 1) (.bvar 1)) <|
    .pi (.pi (.bvar 1) (.bvar 3)) <|
    .eqE (.sort 0) (.bvar 3) (.bvar 2)
  | .choice, us =>
    let u := lv us 0
    -- `∀ (A : Sort u), ¬¬A → A`
    .pi (.sort u) <| .pi (negT (negT (.bvar 0))) <| .bvar 1
  | .lfp, us =>
    let u := lv us 0
    -- `(Sort u → Sort u) → Sort u` (task #188)
    .pi (arrow (.sort u) (.sort u)) (.sort u)
  | .lfpFam, us =>
    let u := lv us 0; let w := lv us 1
    -- `Π (I : Sort u), ((I → Sort w) → (I → Sort w)) → I → Sort w` (task #188, indexed)
    .pi (.sort u) <|
    .pi (arrow (arrow (.bvar 0) (.sort w)) (arrow (.bvar 0) (.sort w))) <|
    .pi (.bvar 1) (.sort w)

end Lech.TT
