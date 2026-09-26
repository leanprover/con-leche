module

public import ConLeche.Kernel.Inductives.StructParts

@[expose] public section

/-!
# The one-member shape record (task #175)

`InductiveShape` is a block member read as one inductive (the uniform
route's `BlockShape.toInductive`; the conformance check's
`NativeParts`, `ConLeche/Conformance/RecGen.lean`, extends it with the
fields' kinds).  Its recursor has `numIndices` indices, one motive,
one minor per constructor (`rulePrefix = numParams + 1 + n`,
`majorIdx = rulePrefix + numIndices`) and one rule per constructor in
constructor order (lean4lean `Lean4Lean/Inductive/Add.lean`, the
official `inductive.cpp`); the large eliminator carries a fresh
elimination level parameter in front of the block's, the small one
the block's own.

**The elimination restriction** (official `elim_only_at_universe_zero`,
enforced by `checkBlockTail` and `checkStructFieldSortsI`): an
inductive whose result sort is not provably nonzero
(`Level.isNeverZero`) and which has two or more constructors
eliminates into `Prop` only; with ONE constructor every field that is
not a proposition must be one of the residual's index expressions
(`Eq`'s rule).  This is the rule that keeps the model's iota law
consistent: at a squash instantiation every constructor value is the
proof point, and two rules firing to two different minors on the same
value would contradict each other; with one constructor the recursor
reads the data fields off the index arguments instead of the
(squashed) value.
-/

namespace ConLeche

/-- A block member's pieces, read as one inductive. -/
structure InductiveShape where
  /-- the type former -/
  cvT : ConstantVal
  /-- the constructors in declaration order, each with its field count -/
  ctors : List (ConstantVal × Nat)
  /-- parameter count -/
  nP : Nat
  /-- index count -/
  nIdx : Nat
  /-- the recursor -/
  cvR : ConstantVal
  /-- the recursor's fresh elimination level parameter (`large` only;
  `.anonymous` for a small eliminator) -/
  elim : Name
  /-- the result sort -/
  resSort : Level
  /-- the rules' right-hand sides as exported, in constructor order -/
  rhss : List Expr
  /-- large eliminator (a fresh elimination level parameter in front) -/
  large : Bool
  /-- the result sort is provably `Prop` -/
  isProp : Bool
  deriving Repr

/-- The record completed with the former's result sort (task #195):
the install stage reads the sort off the checked telescope — the
declared one, or official's whnf'd one — and every later stage runs
on this record.  `isProp` is recomputed so that the
invariant `isProp = (isEquiv resSort zero == some true)` holds by
definition. -/
def InductiveShape.withSort (p : InductiveShape) (s : Level) : InductiveShape :=
  { p with resSort := s, isProp := Level.isEquiv s .zero == some true }

end ConLeche
