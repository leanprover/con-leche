module

public import ConLeche.Kernel.DeclCheck

@[expose] public section

/-!
# The projection table's checks, through the index

`ConLeche/Kernel/Inductives/StructInstall.lean`'s survivors over an `FEnv`
(task #214 P3); the cached driver runs their twins (`ConLeche/Cached/IndTail.lean`).
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

/-- `checkStructProjTable` through the index (task #175 S1). -/
def checkStructProjTableF (t : ProjTable) (fe : FEnv) : m Unit := do
  -- the bodies' scoping, validated once at insertion (the stage's own
  -- guard, what `EnvWF`'s table clause records): fvar-free, level
  -- parameters within the structure's, resolving, scoped at the
  -- parameters and the subject; one per field
  unless t.bodies.size = t.numFields ∧ t.bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined t.levelParams && b.constsResolveF fe &&
      b.looseBVarsBounded (t.numParams + 1)) do
    throw (.internal "direct structure: projection body scoping")
  -- the table follows its structure (declared by the same block):
  -- `EnvWF`'s table clause records it
  unless (fe.find? t.structName).isSome do
    throw (.internal "direct structure: projection table before its structure")
  unless (fe.findTable? t.structName).isNone do
    throw (.invalid "projection table taken")

end Mirrors
