import Setlec.Kernel.Basis.Names
import Setlec.Kernel.Basis.Builder
import Setlec.Kernel.Basis.Eq
import Setlec.Kernel.Basis.Nat
import Setlec.Kernel.Basis.PUnit
import Setlec.Kernel.Basis.Empty
import Setlec.Kernel.Basis.False
import Setlec.Kernel.Basis.Quot

/-!
# The pinned basis inductives

The lean-inductive-models preprocessor reduces every supported inductive
to the five-member basis `Eq`, `Nat`, `PSigma'`, `PUnit`, `Quot` (plus
standard axioms); of these the checker pins `Eq`, `Nat`, `PUnit`, `Quot`
(and `Empty`, `False`) natively (hand-written set models).  `PSigma'` is NOT
pinned (task #175 W6, 2026-09-05): the preprocessor's tight pair is an
ordinary two-field simple structure and installs through the direct
path (`Setlec/Kernel/Direct.lean`, tower projection entries) like any
other.  The pinned declarations match exactly what the preprocessor
emits — the frontend compares incoming records against these and
declines anything else.  One module per basis type under
`Setlec/Kernel/Basis/`, hand-written against the toolchain's
`Init.Prelude` through the small builder in `Basis/Builder.lean`.

**Raw only.**  The *annotated* forms — what the installation actually
stores — are computed from these by the checker's own annotation pass
in `Setlec/Kernel/BasisA.lean`, which therefore sits above
`Setlec.Kernel.TypeChecker`.  This module sits below it: the kernel
core needs the raw pins (the frontend matches incoming records against
them) and nothing else.
-/

namespace Setlec

/-- The constants of one basis block, in dependency order. -/
def BasisKind.decls : BasisKind → List ConstantInfo
  | .eqK => eqBasis
  | .natK => natBasis
  | .punitK => punitBasis
  | .emptyK => emptyBasis
  | .falseK => falseBasis
  | .quotK => quotBasis

end Setlec
