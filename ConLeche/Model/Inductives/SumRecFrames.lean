module

public import ConLeche.Model.Inductives.SumRecData
public import ConLeche.Model.Inductives.SumStageCtor
import ConLeche.Model.Inductives.StructRecRead
public section

/-!
# The sum recursor's frames (task #175 sum-types, indexed)

`sumRecFrames`: at a parameter frame, the generated sum recursor's
entries read to the recursor leaf's premise `RecBaseS` — the motive
entry to the nested product over the former's index telescope into
the family at each index tuple, minor entry `j` (at the frame under
the motive and the earlier minors) to constructor `j`'s minor space
`minorSpI` (its conclusion at the constructor's own index values),
the index entries to the former's index telescope, the major entry
to the family at the frame's index tuple — and the K-frame's two
hypothesis records (`RecHypS`, `SqHypS`).  The walk: down the minor
chain (`sumMinorsTail`), then down the index chain (`sumIdxTail`),
the frame kept as an explicit `consList`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The chains of a data list -/

/-- The field chains of the constructor data (at the parameter
frame). -/
@[expose] def fssOf (nP : Nat) (cds : List CtorDatum) : List (List AnnotTerm) :=
  cds.map fun cd => (cd.2.2.1.drop nP).map (·.2.2)

/-- The index readings of the constructor data. -/
@[expose] def essOf (cds : List CtorDatum) : List (List AnnotTerm) :=
  cds.map fun cd => cd.2.2.2

theorem fssOf_getElem? (nP : Nat) (cds : List CtorDatum) (j : Nat) :
    (fssOf nP cds)[j]? = cds[j]?.map fun cd => (cd.2.2.1.drop nP).map (·.2.2) := by
  simp [fssOf]

theorem essOf_getElem? (cds : List CtorDatum) (j : Nat) :
    (essOf cds)[j]? = cds[j]?.map fun cd => cd.2.2.2 := by
  simp [essOf]

/-! ## The nested product over a telescope, read -/


end ConLeche.Model
