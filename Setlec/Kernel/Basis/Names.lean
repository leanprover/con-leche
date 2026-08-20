import Setlec.Kernel.Env

/-!
# Basis names

The reserved names of the pinned basis blocks (see `Setlec.Kernel.Basis`).
-/

namespace Setlec

open Name (anonymous)


open Name (anonymous)

/-- The name of the basis dependent-pair type. -/
def psigmaName : Name := anonymous |>.str "PSigma'"

/-- The name of the basis dependent-pair constructor. -/
def psigmaMkName : Name := psigmaName |>.str "mk"

/-- The name of the basis equality type. -/
def eqName : Name := anonymous |>.str "Eq"

/-- The name of the basis equality constructor. -/
def eqReflName : Name := eqName |>.str "refl"

/-- The name of the basis unit type. -/
def punitName : Name := anonymous |>.str "PUnit"

/-- The name `Nat`. -/
def natName : Name := anonymous |>.str "Nat"

/-- The name `Nat.zero`. -/
def natZeroName : Name := natName |>.str "zero"

/-- The name `Nat.succ`. -/
def natSuccName : Name := natName |>.str "succ"

/-- The name of the basis unit constructor. -/
def punitUnitName : Name := punitName |>.str "unit"

def emptyName : Name := anonymous |>.str "Empty"

/-- Names reserved for the pinned basis blocks; no other declaration
may use them. -/
def reservedBasisNames : List Name :=
  [eqName, eqReflName, eqName.str "rec",
   natName, natZeroName, natSuccName, natName.str "rec",
   psigmaName, psigmaMkName, psigmaName.str "rec",
   punitName, punitUnitName, punitName.str "rec",
   emptyName, emptyName.str "rec"]

end Setlec
