module

import ConLeche.Model.Inductives.SumRecRead
public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Semantics.Tower.FixSquashI
public section

/-!
# The generated recursive recursor's readings: the targets (task #188)

The binder data the generated recursor type `structRecTyR`
(`ConLeche/Conformance/RecGen.lean`) reads to, and the rules' λ-data
and cores — the indexed sum route's (`SumRecReadP.lean`) with the
**inductive-hypothesis binders** in the minors (`ihPisAV`: for each
recursive field `i`, at ih position `l`, `motive e⃗_i f_i` with the
field's index readings moved to the binder's frame, `ihIdxAt`) and
the ih applications in the rules (`ihAppAV`: the recursor's leaf at
the block's variables, the field's index readings and the field).  The
reading theorems (`FixRecReadP.lean`) prove the kernel's generators
read to exactly these.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The ih binders -/

/-- A recursive constructor datum: name, field count, field data,
index readings, recursive positions, per-field index-expression
readings, per-field telescopes (empty at a finitary field; task
#202). -/
abbrev CtorDatumR :=
  Name × Nat × List (Nat × Nat × AnnotTerm) × List AnnotTerm × List Nat × List (List AnnotTerm) ×
    List (List (Nat × Nat × AnnotTerm))

/-! ## The telescope toolkit (task #202)

The kernel spells a reflexive field's own telescope with
`Expr.piBinders` (`structFieldTeleOf`); the readings need its
elementary laws — the round trip, its stability under the frame's
instantiation (whose arguments are free variables), and the openers'
count. -/

end ConLeche.Model
