import Setlec.Kernel.Basis.Names
import Setlec.Kernel.Basis.Eq
import Setlec.Kernel.Basis.Nat
import Setlec.Kernel.Basis.PUnit
import Setlec.Kernel.Basis.Empty
import Setlec.Kernel.Basis.Quot

/-!
# The pinned basis inductives

The lean-inductive-models preprocessor reduces every supported inductive
to the five-member basis `Eq`, `Nat`, `PSigma'`, `PUnit`, `Quot` (plus
standard axioms); of these the checker pins `Eq`, `Nat`, `PUnit`, `Quot`
(and `Empty`) natively (hand-written set models).  `PSigma'` is NOT
pinned (task #175 W6, 2026-09-05): the preprocessor's tight pair is an
ordinary two-field simple structure and installs through the direct
path (`Setlec/Kernel/Direct.lean`, tower projection entries) like any
other.  The pinned declarations match exactly what the preprocessor
emits — the frontend compares incoming records against these and
declines anything else.  One module per basis type under
`Setlec/Kernel/Basis/`; the expressions are generated from the
preprocessor's own emission (see DESIGN.md); do not edit them by hand.
-/

namespace Setlec

/-- The constants of one basis block, in dependency order. -/
def BasisKind.decls : BasisKind → List ConstantInfo
  | .eqK => eqBasis
  | .natK => natBasis
  | .punitK => punitBasis
  | .emptyK => emptyBasis
  | .quotK => quotBasis

/-- The annotated constants of one basis block, in dependency order. -/
def BasisKind.declsA : BasisKind → List ConstantInfo
  | .eqK => [eqA, eqReflA, eqRecA]
  | .natK => [natA, natZeroA, natSuccA, natRecA]
  | .punitK => [punitA, punitUnitA, punitRecA]
  | .emptyK => [emptyA, emptyRecA]
  | .quotK => [quotA, quotMkA, quotLiftA, quotIndA, quotSoundA]

-- placeholder annotated Empty declarations; regenerated below
end Setlec
