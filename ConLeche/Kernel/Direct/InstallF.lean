import ConLeche.Kernel.DeclCheck

/-!
# The direct simple-structure install, through the index

`checkDirectStruct`'s stages (`ConLeche/Kernel/Direct/Install.lean`)
over an `FEnv`, the mirrors the cached drivers run.  Extracted verbatim
from the tail of `ConLeche/Kernel/DeclCheck.lean` (its `Mirrors`
section) on 2026-09-06 (cleanup pass A).
-/

namespace ConLeche

variable (mode : CheckMode)

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ### The direct simple-structure path, through the index -/

/-- `checkDirectDomsAt` through the index. -/
def checkDirectDomsAtF (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkDirectDomsAtF ops fe off fvs doms j

/-- `checkDirectDomsAtF` over arrays (see `checkDirectFieldUnivFA`).
Equal to it at `List.toArray`: `checkDirectDomsAtFA_eq`. -/
def checkDirectDomsAtFA (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : Array Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkDirectDomsAtFA ops fe off fvs doms j

/-- **The tree walkers an index-side installer takes from its
driver** (task #214, after the JZero audit): the constant-resolution
gate over constructor binder domains and the projection-body builder
over the constructor telescope are the two whole-tree traversals of
the direct install, and on a heavily DAG-shared block (Mathlib's
`ModularCurve.JZeroGoodReductionSpecialization_alt`: a 3.3 k-node DAG
unfolding to 19.6 M nodes) they are what the tree-size budget exists
for.  The cached driver supplies its memoised twins
(`ConLeche.Cached.directWalkersC`: `constsResolveFC`,
`directProjBodiesC`); the specification is `DirectWalkers.plain`, to
which the driver's record is equal (`directWalkersC_eq_plain`,
`ConLeche/Verify/Cached/WalkersC.lean`).  The pure installers never see
this record. -/
structure DirectWalkers where
  /-- `Expr.constsResolveF` or its memoised twin -/
  resolve : FEnv → Expr → Bool
  /-- `directProjBodies` or its memoised twin -/
  projBodies : Name → Nat → Nat → Expr → Option (Array Expr)

/-- The plain walkers: the specification. -/
def DirectWalkers.plain : DirectWalkers :=
  ⟨fun fe e => e.constsResolveF fe, directProjBodies⟩

/-- `checkDirectProjTable` through the index (task #175 S1). -/
def checkDirectProjTableF (w : DirectWalkers) (T C : Name) (lps : List Name) (nP nF : Nat)
    (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) (fe : FEnv) :
    m FEnv := do
  let bodies ← unwrapOr (w.projBodies T nP nF cvCa.type)
    (.internal "direct structure: projection bodies")
  -- the bodies' scoping, validated once at insertion (the stage's own
  -- guard, what `EnvWF`'s table clause records): fvar-free, level
  -- parameters within the structure's, resolving, scoped at the
  -- parameters and the subject; one per field
  unless bodies.size = nF ∧ bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined lps && w.resolve fe b &&
      b.looseBVarsBounded (nP + 1)) do
    throw (.internal "direct structure: projection body scoping")
  -- the projection-function name family (the modeled route's, the key
  -- of its η-family predicate) must be free too: a direct family has
  -- no projection functions, and the model's η law for the block is
  -- discharged by the tower, never by `EtaFamilyStored`
  unless (List.range nF).all (fun j => (fe.find? (projFnName T j)).isNone) do
    throw (.invalid "projection name family taken")
  unless (fe.find? (projTableName T)).isNone do
    throw (.invalid "projection table taken")
  pure (fe.push (.projInfo ⟨T, lps, nP, C, nF, resSort, bodies, guards, off⟩))

end Mirrors
