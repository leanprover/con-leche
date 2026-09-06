import Setlec.Kernel.Env

/-!
# Basis names

The reserved names of the pinned basis blocks (see `Setlec.Kernel.Basis`).
-/

namespace Setlec

open Name (anonymous)

/-- The name of the basis equality type. -/
def eqName : Name := anonymous |>.str "Eq"

/-- The name of the basis equality constructor. -/
def eqReflName : Name := eqName |>.str "refl"

/-- The name of the basis unit type. -/
def punitName : Name := anonymous |>.str "PUnit"

/-- The name of the basis unit type's recursor.  A top-level constant
so the unit-like head test (`isUnitLikeTy`, task #161 item C1) does not
rebuild it on every proof-irrelevance attempt. -/
def punitRecName : Name := punitName |>.str "rec"

/-- The name `Nat`. -/
def natName : Name := anonymous |>.str "Nat"

/-- The name `Nat.zero`. -/
def natZeroName : Name := natName |>.str "zero"

/-- The name `Nat.succ`. -/
def natSuccName : Name := natName |>.str "succ"

/-- The name of the basis unit constructor. -/
def punitUnitName : Name := punitName |>.str "unit"

def emptyName : Name := anonymous |>.str "Empty"

/-- The name of the basis quotient type. -/
def quotName : Name := anonymous |>.str "Quot"

/-- The name of the basis quotient constructor. -/
def quotMkName : Name := quotName |>.str "mk"

/-- The name of the basis quotient lift eliminator. -/
def quotLiftName : Name := quotName |>.str "lift"

/-- The name of the basis quotient induction eliminator. -/
def quotIndName : Name := quotName |>.str "ind"

/-- The name of the basis quotient soundness axiom. -/
def quotSoundName : Name := quotName |>.str "sound"

/-! The names of the string-literal support constants (see
`strLitSupported` in `Setlec.Kernel.Core`).  These are *not* basis
names — the constants are ordinary stream-installed declarations
(preprocessor-modeled inductives and plain definitions); the names are
pinned only so that a string literal knows what it unfolds to
(`strLitToConstructor`), exactly like the `Nat` literal names above. -/

/-- The name `String`. -/
def stringName : Name := anonymous |>.str "String"

/-- The name `String.ofList`. -/
def stringOfListName : Name := stringName.str "ofList"

/-- The name `List`. -/
def listName : Name := anonymous |>.str "List"

/-- The name `List.nil`. -/
def listNilName : Name := listName.str "nil"

/-- The name `List.cons`. -/
def listConsName : Name := listName.str "cons"

/-- The name `Char`. -/
def charName : Name := anonymous |>.str "Char"

/-- The name `Char.ofNat`. -/
def charOfNatName : Name := charName.str "ofNat"

/-- Names reserved for the pinned basis blocks; no other declaration
may use them.  `PSigma'` is not among them (task #175 W6): the
preprocessor's tight pair installs through the direct simple-structure
path as an ordinary two-field structure. -/
def reservedBasisNames : List Name :=
  [eqName, eqReflName, eqName.str "rec",
   natName, natZeroName, natSuccName, natName.str "rec",
   punitName, punitUnitName, punitName.str "rec",
   emptyName, emptyName.str "rec",
   quotName, quotMkName, quotLiftName, quotIndName, quotSoundName]

end Setlec
