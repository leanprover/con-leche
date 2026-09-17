module

public import ConLeche.Model.Inductives.NestedRecCtor
public import ConLeche.Model.Inductives.NestedRecTypes
import ConLeche.Model.Inductives.NestedRecFibre
public section

/-!
# The restored recursor types' frames, by transfer (task #315, M7-2, PLAN-M7 §1e)

The thirteen bookkeeping clauses of `NestedRecReadings` are
`NestedTailIn.readings`' (`NestedRecTypes.lean`); its fourteenth,
`frames = ReadingFramesT`, is this file's — by TRANSFER along the
restore walk's reading law (`denoteMeta_restoreWalk`,
`NestedRecWalk.lean`): a spine fitting the RESTORED recursor type's
reading fits the SCRATCH one's, whose frame inversion is the MUTUAL
`IsBlockModels.spineFit_recData_inv` at the auxiliary block's own
block model, and the frame's semantic clauses transfer back through
the fibre kit (`NestedRecFibre.lean`).

* B1 `NestedRecTysAuxOk` — the walk's shape precondition at the run
  (K.35's model face: every read-back recursor type, below its
  parameter prefix, is `AuxAppsOk` at the restore table);
* B2 `NestedTailIn.restoreAgree` — `RestoreAgree` instantiated at the
  tail, with T2's `NestedTailIn.ctorArm` as its `ctor` field.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  AuxType ContainerInfo ContainerMember ContainerCtor fueledOps BinderMeta PropWhen RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## B1 — the walk's precondition at the run -/

/-- **K.35's model face** (PLAN-M7 §1a, provisional until the kernel
record lands): every read-back recursor type, below its parameter
prefix of `b.nP` binders, has the shape the restore walk relies on —
every application headed by a restore-table key carries the block's
parameter variables in its first `nP` arguments and the key's arity
(`nestedArity`) in all — stated at depth `0` below the prefix. -/
@[expose] def NestedRecTysAuxOk (p : NestedParts) (st : ElimState) (b : MutualBlock)
    (stored : List AuxStored) (pinsS : List PinSyn) : Prop :=
  ∀ (c : Nat) (a : AuxStored), stored[c]? = some a →
    ∃ (pbs : List (Expr × BinderMeta)) (body : Expr),
      a.cvRa.type.stripPis b.nP = some (pbs, body) ∧
      AuxAppsOk (ConLeche.restoreTbl p st) b.lps (nestedArity p st pinsS) 0 body

end ConLeche.Model
