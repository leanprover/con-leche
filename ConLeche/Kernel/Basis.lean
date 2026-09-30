module

public import ConLeche.Kernel.Basis.Names
public import ConLeche.Kernel.Basis.Builder
public import ConLeche.Kernel.Basis.Eq
public import ConLeche.Kernel.Basis.Nat
public import ConLeche.Kernel.Basis.Empty
public import ConLeche.Kernel.Basis.False
public import ConLeche.Kernel.Basis.Quot
public import ConLeche.Kernel.Basis.And
public import ConLeche.Kernel.Canon

@[expose] public section

/-!
# The pinned basis inductives

The checker pins `Eq`, `Nat`, `Quot`, `Empty` and `False`
natively (hand-written set models), and pins `And` by recognition
alone (below).  The pinned declarations are the toolchain's own — the
fold compares incoming records against these (a differing block under
a pinned name is rejected, a differing quotient record declined).  One
module per pinned type under `ConLeche/Kernel/Basis/`, hand-written
against the toolchain's `Init.Prelude` through the small builder in
`Basis/Builder.lean`.

**Raw only.**  The *annotated* forms — what the installation actually
stores — are computed from these by the checker's own annotation pass
in `ConLeche/Kernel/BasisA.lean`, which therefore sits above
`ConLeche.Kernel.TypeChecker`.  This module sits below it: the kernel
core needs the raw pins (the fold matches incoming records against
them) and nothing else.
-/

namespace ConLeche

/-- The constants of one basis block, in dependency order. -/
def BasisKind.decls : BasisKind → List ConstantInfo
  | .eqK => eqBasis
  | .natK => natBasis
  | .emptyK => emptyBasis
  | .falseK => falseBasis
  | .quotK => quotBasis

/-! ## Recognising a pinned block in a stream record (task #293)

The decoder emits the file's records and nothing else, and
`preparePrelude` only reorders them, so a stream's `Nat` block reaches
`checkDecl` as an ordinary `indDecl`.  These are the two tests that
recognise it as the pinned block — the matching the parser used to do,
where it belongs.  A block under a pinned name that does NOT match is
left to the ordinary route, where the reserved-name check rejects it
(a basis redefinition is invalid input); a quotient record that does
not match its pin is a decline. -/

/-- **The basis-pin match**, with task #215's NAME pre-filter.
`ConstantInfo.canon` rebuilds the whole block as an unshared tree — on
a heavily DAG-shared block that was the frontend's single largest cost
— so a block that is not one of the four pinned ones must not reach it.
`canon` renames only *level parameters*, leaving every constant name
alone, so a block can match a pin only when its members' names are the
pin's, member for member, and that test is a handful of `Name`
comparisons. -/
def basisPinHit (block : List ConstantInfo) : Option BasisKind :=
  ([BasisKind.eqK, .natK, .emptyK, .falseK].find? fun k =>
      k.decls.map (·.name) == block.map (·.name)).filter fun k =>
    canonEqList block k.decls

/-- **The quotient-pin match**: the record is the pinned package's
constant at the slot it declares itself at.  The two are compared at
`toConstantVal`. -/
def quotPinHit (k : QuotKind) (cv : ConstantVal) : Bool :=
  ConstantVal.canonEq cv (BasisKind.quotK.decls.getD k.slot (.axiomInfo default)).toConstantVal

/-! ## The pinned `And`

`And` is recognised, not installed from literals
(`ConLeche/Kernel/Basis/And.lean`): the block that matches the pin goes
through the ordinary inductive installer.  What the pin adds is a
REJECT — a record that declares `And`, `And.intro` or `And.rec` and is
not the pinned block is invalid input, as a basis redefinition is — so
that in every accepted environment the name `And` is the toolchain's
`And` and the stuck-proof rescue that serves it (`majorToCtor`'s `And`
branch) is available.  The fold asks this of every record before its
dispatch (`annotDeclStep`, `ConLeche/Cached/Installed.lean`). -/

/-- **The `And` pin's test**: the record declares none of the pinned
`And` block's names, or it IS that block — two parameters, and equal
to `andPin` up to `ConstantInfo.canon`. -/
def andPinOk : Declaration → Bool
  | .indDecl block nP =>
    !(block.any fun c => andPinNames.contains c.name) ||
      (nP == 2 && canonEqList block andPin)
  | .axiomDecl cv | .defnDecl cv .. | .thmDecl cv .. | .opaqueDecl cv ..
  | .quotDecl _ cv => !andPinNames.contains cv.name
  | .basisDecl _ => true

end ConLeche
