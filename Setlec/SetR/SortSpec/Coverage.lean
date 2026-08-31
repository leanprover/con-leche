import Setlec.SetR.SortSpec.Agree
import Setlec.Kernel.Basis
import Setlec.Kernel.StdAxioms

/-!
# Coverage — how much of a real environment `sortSpec` can answer

Seal 2 owes the verdict memo a *number*, not an impression.  This
file measures `sortSpec`'s reach on the one environment fragment that
is in the tree as data: the eight pinned basis families
(`Kernel/Basis/*`, `Kernel/StdAxioms.lean`), 26 stored constants.

The metric is the honest one: a constant `c` is **answerable** when
`piCod` reaches a syntactic sort after stripping its declared type's
full `∀`-telescope — i.e. when `sortSpec` can give a sort for `c`
applied to all of its arguments.  Everything below is checked by
`decide`, so it is a regression test rather than a claim, and it adds
no axiom.

## The result, exactly

    answerable c  ↔  c is an inductive type former

on all 26 constants (`answerable_iff_indInfo`).  Broken out:

| class | count | `sortSpec` | verdict |
|---|---|---|---|
| type formers (`indInfo`) | 8 | answers | **complete** |
| constructors + `Quot.sound` | 9 | declines | **correct** |
| recursors (`recInfo`) | 9 | declines | the **ι wall** |

* **8 / 8 type formers answered.**  Every constant that can appear as
  a binder type in this fragment gets a sort.  On the class that
  matters for binder sorts, coverage is total.
* **9 / 9 terms declined, correctly.**  `Nat.zero`, `Nat.succ`,
  `Eq.refl`, `Quot.mk`, `Quot.sound`, … are terms; a term is never a
  type, so `none` is the right answer and the checker's `sortOfE`
  fails on them too.  (Seal 1 shipped a `.lit` clause that got this
  class wrong for literals; seal 2 fixed it.)
* **9 / 26 (35%) declined at the ι wall.**  The recursors — including
  `Quot.lift` and `Quot.ind`, which are stored as `recInfo`.  Their
  declared codomain is a motive application, not a syntactic sort, so
  `piCod` stops; and under large elimination a recursor application
  *is* a type with a real sort.  This is seal 1's ι finding, priced.

That the two predicates coincide is not a coincidence: an `indInfo`'s
declared type is a `∀`-telescope ending in the family's sort, which is
precisely `piCod`'s success condition, and nothing else in a basis
environment has that shape.
-/

namespace Setlec.SetR.SortSpec

open Setlec (Expr Level ConstantInfo)

/-- The number of leading `∀` binders of a declared type. -/
def piArity : Expr → Nat
  | .forallE _ _ b _ => piArity b + 1
  | _ => 0

/-- The 26 pinned basis constants, in install order. -/
def basisAll : List ConstantInfo :=
  Setlec.emptyBasis ++ Setlec.punitBasis ++ Setlec.psigmaBasis ++
    Setlec.natBasis ++ Setlec.quotBasis ++ Setlec.eqBasis ++
    Setlec.iffFamily ++ Setlec.nonemptyFamily

/-- Can `sortSpec` sort `c` applied to all of its arguments? -/
def answerable (c : ConstantInfo) : Bool :=
  (piCod c.toConstantVal.type
    (piArity c.toConstantVal.type)).isSome

def isInd : ConstantInfo → Bool
  | .indInfo _ _ => true
  | _ => false

def isRec : ConstantInfo → Bool
  | .recInfo _ _ _ _ => true
  | _ => false

/-- The pinned environment has 26 constants. -/
example : basisAll.length = 26 := by decide

/-- **The characterization**: on this environment `sortSpec` answers
for a constant exactly when that constant is an inductive type
former. -/
theorem answerable_iff_indInfo :
    basisAll.all (fun c => answerable c == isInd c) = true := by
  decide

/-- Eight answered. -/
example : (basisAll.filter answerable).length = 8 := by decide

/-- Eighteen declined. -/
example :
    (basisAll.filter (fun c => !answerable c)).length = 18 := by
  decide

/-- **The ι wall, counted**: nine recursors, 35% of the environment,
every one of them declined. -/
example : (basisAll.filter isRec).length = 9 := by decide

example :
    (basisAll.filter
      (fun c => isRec c && !answerable c)).length = 9 := by
  decide

/-- The remaining nine declines are constructors and `Quot.sound` —
terms, for which `none` is the correct answer. -/
example :
    (basisAll.filter
      (fun c => !answerable c && !isRec c)).length = 9 := by
  decide

end Setlec.SetR.SortSpec
