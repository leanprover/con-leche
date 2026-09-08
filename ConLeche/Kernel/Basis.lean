module

public import ConLeche.Kernel.Basis.Names
public import ConLeche.Kernel.Basis.Builder
public import ConLeche.Kernel.Basis.Eq
public import ConLeche.Kernel.Basis.Nat
public import ConLeche.Kernel.Basis.PUnit
public import ConLeche.Kernel.Basis.Empty
public import ConLeche.Kernel.Basis.False
public import ConLeche.Kernel.Basis.Quot

@[expose] public section

/-!
# The pinned basis inductives

A modelled inductive block is reduced to the five-member basis `Eq`,
`Nat`, `PSigma'`, `PUnit`, `Quot` (plus standard axioms); of these the
checker pins `Eq`, `Nat`, `PUnit`, `Quot` (and `Empty`, `False`)
natively (hand-written set models).  `PSigma'` is NOT pinned (task
#175 W6, 2026-09-05): the tight pair is an ordinary two-field simple
structure and installs through the direct path
(`ConLeche/Kernel/Direct.lean`, tower projection entries) like any
other.  The pinned declarations are the toolchain's own — the frontend
compares incoming records against these and declines anything else.  One module per basis type under
`ConLeche/Kernel/Basis/`, hand-written against the toolchain's
`Init.Prelude` through the small builder in `Basis/Builder.lean`.

**Raw only.**  The *annotated* forms — what the installation actually
stores — are computed from these by the checker's own annotation pass
in `ConLeche/Kernel/BasisA.lean`, which therefore sits above
`ConLeche.Kernel.TypeChecker`.  This module sits below it: the kernel
core needs the raw pins (the frontend matches incoming records against
them) and nothing else.
-/

namespace ConLeche

/-- The constants of one basis block, in dependency order. -/
def BasisKind.decls : BasisKind → List ConstantInfo
  | .eqK => eqBasis
  | .natK => natBasis
  | .punitK => punitBasis
  | .emptyK => emptyBasis
  | .falseK => falseBasis
  | .quotK => quotBasis

end ConLeche
