import Setlec.Kernel.Env
import Setlec.Kernel.IExpr

/-!
# Parsed declarations with interned expressions (task #78)

The frontend parses the export tables *directly into an `EStore`*: each
expression-table entry is interned once, children resolved to
already-interned indices, so the export format's structural sharing is
preserved end to end.  Declarations then reference expressions by arena
index (`DeclP`), and the checker's shared-state drivers consume the
indices without ever materializing a tree.

Exceptions carrying `Expr` trees remain where a genuinely bounded
consumer needs them (see DESIGN.md, "Parse-time interning"): inductive
blocks (`indDecl` carries `ConstantInfo`s read back at parse under the
tree-size budget — the install pipeline compares member types against
`_model` artifacts with tree traversals) and the pinned basis blocks.

`DeclP.readback` recovers the spec-level `Declaration` — the object the
consistency statements quantify over; `Setlec/Model/ConsistencyP.lean`
identifies the executable run on indices with the spec run on the
read-back declarations.
-/

namespace Setlec

/-- `ConstantVal` with the type as an arena index. -/
structure ConstantValP where
  name : Name
  levelParams : List Name
  type : EIdx
  deriving Repr, Inhabited

/-- A parsed declaration: expression fields are arena indices into the
parse store, except for inductive blocks (read back at parse, tree-size
budgeted) and basis blocks (pinned). -/
inductive DeclP where
  | axiomDecl (val : ConstantValP)
  | defnDecl (val : ConstantValP) (value : EIdx) (hint : ReducibilityHint)
  | thmDecl (val : ConstantValP) (value : EIdx)
  | opaqueDecl (val : ConstantValP) (value : EIdx)
  | basisDecl (kind : BasisKind)
  | indDecl (block : List ConstantInfo)
  deriving Repr, Inhabited

namespace DeclP

/-- The name of a non-block declaration (mirrors `Declaration.name`). -/
def name : DeclP → Name
  | .axiomDecl v | .defnDecl v _ _ | .thmDecl v _ | .opaqueDecl v _ => v.name
  | .basisDecl _ | .indDecl _ => .anonymous

/-- A parsed index reference is a tier-one (even) index below the
encoded bound (task #64: `EIdx` is `2 * position + tier`; parser
indices are always even, so the parity conjunct never fails on real
streams). -/
@[inline] def inRange1 (n0 : Nat) (e : EIdx) : Bool :=
  etier e == 0 && e < n0

/-- All expression indices are in the parse store's range (checked once
per declaration at the checker seam; `O(1)` — under `EStore.WF`,
in-range tier-one indices have total denotations). -/
def inRangeB (n0 : Nat) : DeclP → Bool
  | .axiomDecl v => inRange1 n0 v.type
  | .defnDecl v value _ => inRange1 n0 v.type && inRange1 n0 value
  | .thmDecl v value | .opaqueDecl v value =>
    inRange1 n0 v.type && inRange1 n0 value
  | .basisDecl _ | .indDecl _ => true

end DeclP

namespace EStore

/-- Read back a parsed `ConstantValP` (memoized DAG readback). -/
def readbackCV (st : EStore) (cv : ConstantValP) : Option ConstantVal :=
  (st.readbackI cv.type).map fun ty => ⟨cv.name, cv.levelParams, ty⟩

/-- Read back a parsed declaration to the spec-level `Declaration`
(`Setlec/Verify/IExprOps.lean` identifies this with the structural
denotation on well-formed stores). -/
def readbackDecl (st : EStore) : DeclP → Option Declaration
  | .axiomDecl v => (st.readbackCV v).map .axiomDecl
  | .defnDecl v value hint =>
    (st.readbackCV v).bind fun cv =>
      (st.readbackI value).map fun ve => .defnDecl cv ve hint
  | .thmDecl v value =>
    (st.readbackCV v).bind fun cv =>
      (st.readbackI value).map fun ve => .thmDecl cv ve
  | .opaqueDecl v value =>
    (st.readbackCV v).bind fun cv =>
      (st.readbackI value).map fun ve => .opaqueDecl cv ve
  | .basisDecl kind => some (.basisDecl kind)
  | .indDecl block => some (.indDecl block)

end EStore

end Setlec
