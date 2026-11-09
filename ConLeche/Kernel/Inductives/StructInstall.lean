module

public import ConLeche.Kernel.CheckerBase
public import ConLeche.Kernel.TrustAxioms

@[expose] public section

/-!
# The projection table's checks (pure fueled checker)

The binder-domain walk and the checks of the projection TABLE the block install
stores at a structure-like member (`checkStructProjTable`,
run per table by `checkBlockTables`,
`ConLeche/Kernel/Inductives/BlockTail.lean`).  The index-threaded twins
are `ConLeche/Kernel/Inductives/StructInstallF.lean`.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-! ## The structure-shaped block's reference checks

What this layer contributes at a structure-shaped block are the
reference checks that need inference and definitional equality — the
per-field universe bound and the definitional pins of the recursor's
binder domains against the constructor's.
-/

/-- The reference kernels' binder-domain comparisons, run binder by
binder **at its own frame**: the `j`-th opened variable's annotation
against the `j`-th expected domain, at frame `off + j`.

Domain `j` is scoped at `off + j` — it mentions the binders before it
and nothing else — so that frame is exactly the context the references
compare it in, with those binders in scope and no more.  Because each
telescope is opened at its **own** variables, neither side's
annotations are borrowed from the other, which is what lets the model's
walks carry their own frame conditions at every stage.  Walks from the
last binder to the first. -/
def checkStructDomsAt (ops : CheckerOps m) (env : Env) (off : Nat)
    (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkStructDomsAt ops env off fvs doms j

/-- Stage 5: **the projection table's checks** (task #175 S1).  One table per
structure, in the environment's table component (task #362), read off the block by `blockTables`
(`ConLeche/Kernel/Install.lean`): the fields' result-type bodies read off the stored constructor
type by substitution alone (`structProjBodies`), the constructor and the counts.  This checks that
table, as it will be installed.  Nothing is inferred or pinned here — a `.proj T i e` use
instantiates `bodies[i]` at its own arguments (`ProjEntry.typeAt`) after the official `infer_proj`
guard (`checkProjGuard`, at the use), and a slot with no legal instantiation (a used-later data
field of a `Prop` structure) simply fails that guard at every use (`invalid`, as official). -/
def checkStructProjTable (t : ProjTable) (env : Env) : m Unit := do
  -- the bodies' scoping, validated once at insertion (the stage's own
  -- guard, what `EnvWF`'s table clause records): fvar-free, level
  -- parameters within the structure's, resolving, scoped at the
  -- parameters and the subject; one per field
  unless t.bodies.size = t.numFields ∧ t.bodies.all (fun b => !b.hasFvar &&
      b.allLevelParamsDefined t.levelParams && b.constsResolve env &&
      b.looseBVarsBounded (t.numParams + 1)) do
    throw (.internal "direct structure: projection body scoping")
  -- the table follows its structure (declared by the same block):
  -- `EnvWF`'s table clause records it
  unless (env.find? t.structName).isSome do
    throw (.internal "direct structure: projection table before its structure")
  unless (env.findTable? t.structName).isNone do
    throw (.invalid "projection table taken")

end ConLeche
