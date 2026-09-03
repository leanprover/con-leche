import Setlec.SetBase.Syntax
import Setlec.TT.Const

/-!
# `BConst.type2` — the annotated basis-constant types (#151, step 2)

*(Re-based to `Setlec/SetBase/*` at THE SEPARATION's S2, task #161: the
module already imported nothing but `SetBase/Syntax` and `TT/Const` —
it is the basis constants' *annotated types*, pure syntax — and the
graded lane's `Interp2/BasisTypeOk` was reaching it through the 2U
`Interp2/BasisOk`.  Path and module name changed; namespaces,
statements and proofs verbatim.)*


The first of the two suppliers the skeleton's `const` row waits on
(`Interp2/Skeleton.lean`): the annotated mirror of
`Setlec/TT/Const.lean`'s `BConst.type`, so that a built-in constant's
type can be *written* as an `AVExpr` at all.  `denote2` cannot produce
it — `BConst.type` yields a `VExpr` and `denote2` maps `Expr → AVExpr`
— which is why the former has to exist on its own.

## The annotation convention, inherited not invented

`Interp2/Value.lean` fixed it for the value side, and this file mirrors
it exactly, because the two must agree for the capstone
(`bval2_mem_type`) to typecheck at all:

* **every binder's codomain slot carries the tower's result sort `r`**,
  not the exact `imax` fold.  Sound because `piR`/`lamR` read the
  numeral only through `v = 0`, and `imax x y = 0 ↔ y = 0`
  (`imax_eq_zero_iff`);
* **every binder's domain slot carries the domain's exact sort**,
  because those are what the consumers' membership hypotheses are
  stated with — `AnnotOk2`'s binder clauses and `Skeleton.sound_pi`
  both read the domain numeral.

So `.pi u' r A B` throughout, with `u'` exact.  The `v'`-for-a-`Sort`
trap is worth naming once: a codomain slot holds the sort of `B` **as
a type**, so a codomain `.sort k` gets `k + 1`, never `k`.  That is why
`A → Prop` annotates as `.pi u 1 A (.sort 0)` and is a *type*
(`Sort (max u 1)`), not a proposition.

## The result sorts, read off the towers

| constant | `r` | tower |
|---|---|---|
| the five atomic types | — | no binder |
| `natSucc` | `1` | `lamR 1 omega natsucc` |
| `natRec` | `u` | `natRecV2` |
| `punitRec` | `v` | `punitRecV2` |
| `psigma` | `max u v + 1` | `psigmaV2` (a type former) |
| `psigmaMk` | `max u v` | `psigmaMkV2` |
| `emptyRec` | `v` | `emptyRecV2` |
| `quot` | `u + 1` | `quotV2` (a type former) |
| `quotMk` | `u` | `quotMkV2` |
| `quotLift` | `v` | `quotLiftV2` |
| `quotInd`/`quotSound`/`propext` | `0` | `pt`: the types are `Prop` |
| `choice` | `u` | `choiceV2` |

The faithfulness check is `type2_erase` below: erasure returns
`BConst.type` on the nose, so the former adds annotations and nothing
else.  It is the analogue of `denote2_erase`, and it is what makes a
numeral error the *only* thing that can go wrong here — a structural
error cannot survive it.
-/

namespace Setlec.SetR.Interp2

open Setlec.SetR (AVExpr)
open Setlec.TT (BConst lv)

/-! ## Annotated smart constructors

Mirrors of `Setlec/TT/Const.lean`'s, one per former the basis types
mention.  Each carries the numerals its own shape fixes. -/

/-- `Nat` -/
def natT2 : AVExpr := .const .nat []
/-- `Nat.zero` -/
def natZeroT2 : AVExpr := .const .natZero []
/-- `Nat.succ e` -/
def natSuccT2 (e : AVExpr) : AVExpr := .app (.const .natSucc []) e
/-- `PUnit.{u}` -/
def punitT2 (u : Nat) : AVExpr := .const .punit [u]
/-- `PUnit.unit.{u}` -/
def punitUnitT2 (u : Nat) : AVExpr := .const .punitUnit [u]
/-- `Empty.{u}` -/
def emptyT2 (u : Nat) : AVExpr := .const .empty [u]
/-- `@PSigma'.{u,v} A B` -/
def psigmaT2 (u v : Nat) (A B : AVExpr) : AVExpr :=
  AVExpr.mkAppN (.const .psigma [u, v]) [A, B]
/-- `@Quot.{u} A r` -/
def quotT2 (u : Nat) (A r : AVExpr) : AVExpr :=
  AVExpr.mkAppN (.const .quot [u]) [A, r]
/-- `@Quot.mk.{u} A r a` -/
def quotMkT2 (u : Nat) (A r a : AVExpr) : AVExpr :=
  AVExpr.mkAppN (.const .quotMk [u]) [A, r, a]

/-- `A → B`, at the domain's sort `u` and the codomain's sort `v`. -/
def arrowA (u v : Nat) (A B : AVExpr) : AVExpr := .pi u v A B.lift

/-- `A → A → Prop`, the relation type at `A : Sort u`.  Its own sort is
`max u 1` — a *type*, because `Prop` lives in `Sort 1`.  Matches
`relSpace2`. -/
def relT2 (u : Nat) (A : AVExpr) : AVExpr :=
  .pi u (Nat.max u 1) A (.pi u 1 A.lift (.sort 0))

/-- `¬ A`, i.e. `A → False`: a proposition, so the codomain slot is
`0`. -/
def negT2 (u : Nat) (A : AVExpr) : AVExpr := arrowA u 0 A (emptyT2 0)

/-! ## The annotated type assignment -/

/-- The annotated type of each built-in constant — `BConst.type` with
every binder's two numerals supplied (see the module docstring). -/
def BConst.type2 : BConst → List Nat → AVExpr
  | .nat, _ => .sort 1
  | .natZero, _ => natT2
  | .natSucc, _ => arrowA 1 1 natT2 natT2
  | .natRec, us =>
    let u := lv us 0
    -- `∀ (M : Nat → Sort u), M 0 → (∀ n, M n → M (n+1)) → ∀ t, M t`
    .pi (u + 1) u (arrowA 1 (u + 1) natT2 (.sort u)) <|
    .pi u u (.app (.bvar 0) natZeroT2) <|
    .pi u u (.pi 1 u natT2 (.pi u u (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (natSuccT2 (.bvar 1))))) <|
    .pi 1 u natT2 <|
    .app (.bvar 3) (.bvar 0)
  | .punit, us => .sort (lv us 0)
  | .punitUnit, us => punitT2 (lv us 0)
  | .punitRec, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ (M : PUnit.{u} → Sort v), M unit → ∀ t, M t`
    .pi (Nat.max u (v + 1)) v
      (arrowA u (v + 1) (punitT2 u) (.sort v)) <|
    .pi v v (.app (.bvar 0) (punitUnitT2 u)) <|
    .pi u v (punitT2 u) <|
    .app (.bvar 2) (.bvar 0)
  | .psigma, us =>
    let u := lv us 0; let v := lv us 1
    let r := Nat.max u v + 1
    .pi (u + 1) r (.sort u) <|
    .pi (Nat.max u (v + 1)) r
      (arrowA u (v + 1) (.bvar 0) (.sort v)) <|
    .sort (Nat.max u v)
  | .psigmaMk, us =>
    let u := lv us 0; let v := lv us 1
    let r := Nat.max u v
    .pi (u + 1) r (.sort u) <|
    .pi (Nat.max u (v + 1)) r
      (arrowA u (v + 1) (.bvar 0) (.sort v)) <|
    .pi u r (.bvar 1) <|
    .pi v r (.app (.bvar 1) (.bvar 0)) <|
    psigmaT2 u v (.bvar 3) (.bvar 2)
  | .empty, us => .sort (lv us 0)
  | .emptyRec, us =>
    let u := lv us 0; let v := lv us 1
    .pi (Nat.max u (v + 1)) v
      (arrowA u (v + 1) (emptyT2 u) (.sort v)) <|
    .pi u v (emptyT2 u) <|
    .app (.bvar 1) (.bvar 0)
  | .quot, us =>
    let u := lv us 0
    .pi (u + 1) (u + 1) (.sort u) <|
    .pi (Nat.max u 1) (u + 1) (relT2 u (.bvar 0)) <|
    .sort u
  | .quotMk, us =>
    let u := lv us 0
    .pi (u + 1) u (.sort u) <|
    .pi (Nat.max u 1) u (relT2 u (.bvar 0)) <|
    .pi u u (.bvar 1) <|
    quotT2 u (.bvar 2) (.bvar 1)
  | .quotLift, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ A r B (f : A → B), (∀ a b, r a b → f a = f b) → Quot A r → B`
    .pi (u + 1) v (.sort u) <|
    .pi (Nat.max u 1) v (relT2 u (.bvar 0)) <|
    .pi (v + 1) v (.sort v) <|
    .pi (Setlec.TT.imax u v) v (.pi u v (.bvar 2) (.bvar 1)) <|
    .pi 0 v (.pi u 0 (.bvar 3) (.pi u 0 (.bvar 4)
          (.pi 0 0 (AVExpr.mkAppN (.bvar 4) [.bvar 1, .bvar 0])
            (.eqE (.bvar 4) (.app (.bvar 3) (.bvar 2))
              (.app (.bvar 3) (.bvar 1)))))) <|
    .pi u v (quotT2 u (.bvar 4) (.bvar 3)) <|
    .bvar 3
  | .quotInd, us =>
    let u := lv us 0
    .pi (u + 1) 0 (.sort u) <|
    .pi (Nat.max u 1) 0 (relT2 u (.bvar 0)) <|
    .pi (Nat.max u 1) 0
      (.pi u 1 (quotT2 u (.bvar 1) (.bvar 0)) (.sort 0)) <|
    .pi 0 0 (.pi u 0 (.bvar 2)
      (.app (.bvar 1) (quotMkT2 u (.bvar 3) (.bvar 2) (.bvar 0)))) <|
    .pi u 0 (quotT2 u (.bvar 3) (.bvar 2)) <|
    .app (.bvar 2) (.bvar 0)
  | .quotSound, us =>
    let u := lv us 0
    .pi (u + 1) 0 (.sort u) <|
    .pi (Nat.max u 1) 0 (relT2 u (.bvar 0)) <|
    .pi u 0 (.bvar 1) <|
    .pi u 0 (.bvar 2) <|
    .pi 0 0 (AVExpr.mkAppN (.bvar 2) [.bvar 1, .bvar 0]) <|
    .eqE (quotT2 u (.bvar 4) (.bvar 3))
      (quotMkT2 u (.bvar 4) (.bvar 3) (.bvar 2))
      (quotMkT2 u (.bvar 4) (.bvar 3) (.bvar 1))
  | .propext, _ =>
    -- `∀ (A B : Prop), (A → B) → (B → A) → A = B`
    .pi 1 0 (.sort 0) <| .pi 1 0 (.sort 0) <|
    .pi 0 0 (.pi 0 0 (.bvar 1) (.bvar 1)) <|
    .pi 0 0 (.pi 0 0 (.bvar 1) (.bvar 3)) <|
    .eqE (.sort 0) (.bvar 3) (.bvar 2)
  | .choice, us =>
    let u := lv us 0
    -- `∀ (A : Sort u), ¬¬A → A`
    .pi (u + 1) u (.sort u) <|
    .pi 0 u (negT2 0 (negT2 u (.bvar 0))) <|
    .bvar 1

/-! ## Faithfulness

The former adds annotations and nothing else — so a *numeral* error is
the only thing this file can get wrong, and the capstone
(`bval2_mem_type`) is what tests those. -/

/-- **The erasure law**: `type2` erases to `BConst.type` on the nose. -/
theorem type2_erase (c : BConst) (us : List Nat) :
    (BConst.type2 c us).erase = BConst.type c us := by
  cases c <;>
    simp [BConst.type2, Setlec.TT.BConst.type, natT2, natZeroT2,
      natSuccT2, punitT2, punitUnitT2, emptyT2, psigmaT2, quotT2,
      quotMkT2, arrowA, relT2, negT2, Setlec.TT.natT,
      Setlec.TT.natZeroT,
      Setlec.TT.natSuccT, Setlec.TT.punitT, Setlec.TT.punitUnitT,
      Setlec.TT.emptyT, Setlec.TT.psigmaT, Setlec.TT.quotT,
      Setlec.TT.quotMkT, Setlec.TT.arrow, Setlec.TT.relT,
      Setlec.TT.negT, AVExpr.mkAppN, Setlec.TT.VExpr.mkAppN]

end Setlec.SetR.Interp2
