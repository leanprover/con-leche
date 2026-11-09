module

public import ConLeche.Kernel.DeclCheck

@[expose] public section

/-!
# The projection table's checks, through the index

`ConLeche/Kernel/Inductives/StructInstall.lean`'s survivors over an `FEnv` (the
mirrors the cached drivers run) and the `StructWalkers` record the
block installer takes its constant walks from (task #214 P3).
-/

namespace ConLeche

variable (mode : CheckMode)

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ### The binder-domain walk, through the index -/

/-- `checkStructDomsAt` through the index. -/
def checkStructDomsAtF (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkStructDomsAtF ops fe off fvs doms j

/-- `checkStructDomsAtF` over arrays.  Equal to it at `List.toArray`:
`checkStructDomsAtFA_eq`. -/
def checkStructDomsAtFA (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : Array Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkStructDomsAtFA ops fe off fvs doms j

/-- **The tree walker an index-side installer takes from its driver**
(task #214, after the JZero audit): the constant-resolution gate over
constructor binder domains is a whole-tree traversal of the block
install, and on a heavily DAG-shared block (Mathlib's
`ModularCurve.JZeroGoodReductionSpecialization_alt`: a 3.3 k-node DAG
unfolding to 19.6 M nodes) it must not walk the tree.  The cached
driver supplies its memoised twin (`ConLeche.Cached.structWalkersC`:
`constsResolveFC`); the specification is `StructWalkers.plain`, to
which the driver's record is equal (`structWalkersC_eq_plain`,
`ConLeche/Verify/Cached/WalkersC.lean`).  The projection-body builder
(`structProjBodies`) is the same function in both: its substitution
`Expr.instantiateLift` executes as a memoized DAG walk.  The pure
installers never see this record. -/
structure StructWalkers where
  /-- `Expr.constsResolveF` or its memoised twin -/
  resolve : FEnv → Expr → Bool

/-- The plain walkers: the specification. -/
def StructWalkers.plain : StructWalkers :=
  ⟨fun fe e => e.constsResolveF fe⟩

/-- `checkStructProjTable` through the index (task #175 S1). -/
def checkStructProjTableF (w : StructWalkers) (t : ProjTable) (fe : FEnv) : m Unit := do
  -- the bodies' scoping, validated once at insertion (the stage's own
  -- guard, what `EnvWF`'s table clause records): fvar-free, level
  -- parameters within the structure's, resolving, scoped at the
  -- parameters and the subject; one per field
  unless t.bodies.size = t.numFields ∧ t.bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined t.levelParams && w.resolve fe b &&
      b.looseBVarsBounded (t.numParams + 1)) do
    throw (.internal "direct structure: projection body scoping")
  -- the table follows its structure (declared by the same block):
  -- `EnvWF`'s table clause records it
  unless (fe.find? t.structName).isSome do
    throw (.internal "direct structure: projection table before its structure")
  unless (fe.findTable? t.structName).isNone do
    throw (.invalid "projection table taken")

end Mirrors
