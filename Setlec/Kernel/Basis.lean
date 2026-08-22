import Setlec.Kernel.Basis.Names
import Setlec.Kernel.Basis.Eq
import Setlec.Kernel.Basis.Nat
import Setlec.Kernel.Basis.PSigma
import Setlec.Kernel.Basis.PUnit
import Setlec.Kernel.Basis.Empty
import Setlec.Kernel.Basis.Quot

/-!
# The pinned basis inductives

The lean-inductive-models preprocessor reduces every supported inductive
to the five-member basis `Eq`, `Nat`, `PSigma'`, `PUnit`, `Quot` (plus
standard axioms); these are the only inductives the checker implements
natively (hand-written set models).  The declarations are pinned to
exactly what the preprocessor emits — the frontend compares incoming
records against these and declines anything else.  One module per basis
type under `Setlec/Kernel/Basis/`; the expressions are generated from
the preprocessor's own emission (see DESIGN.md); do not edit them by
hand.
-/

namespace Setlec

/-- The constants of one basis block, in dependency order. -/
def BasisKind.decls : BasisKind → List ConstantInfo
  | .eqK => eqBasis
  | .natK => natBasis
  | .psigmaK => psigmaBasis
  | .punitK => punitBasis
  | .emptyK => emptyBasis
  | .quotK => quotBasis

/-- The annotated constants of one basis block, in dependency order. -/
def BasisKind.declsA : BasisKind → List ConstantInfo
  | .eqK => [eqA, eqReflA, eqRecA]
  | .natK => [natA, natZeroA, natSuccA, natRecA]
  | .psigmaK => [psigmaA, psigmaMkA, psigmaRecA, pairFstA, pairSndA]
  | .punitK => [punitA, punitUnitA, punitRecA]
  | .emptyK => [emptyA, emptyRecA]
  | .quotK => [quotA, quotMkA, quotLiftA, quotIndA, quotSoundA]

-- placeholder annotated Empty declarations; regenerated below
end Setlec
