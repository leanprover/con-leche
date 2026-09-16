module

public import ConLeche.Frontend.InModel.Kit
public import ConLeche.Frontend.ProjRec

@[expose] public section

/-!
# The parsed inductive block, as the in-process modeller reads it (task #200)

The records the frontend hands the nested rung
(`ConLeche/Frontend/InModel/Nested.lean`): one inductive type, one
constructor and one recursor of a parsed block with the export's shape
data, the block, and the declaration table the generator reads beside
it.  They lived in the mutual rung's module until task #278 moved the
mutual reduction into the kernel (`ConLeche/Kernel/Inductives/MutualInstall.lean`)
and deleted that rung.
-/

namespace ConLeche.Frontend.InModel

open ConLeche

/-- One inductive type of a parsed block, with the export's shape data. -/
structure IndTypeRec where
  cv : ConstantVal
  nP : Nat
  nIdx : Nat
  ctors : List Name
  isRec : Bool
  isReflexive : Bool
  numNested : Nat
  deriving Repr, Inhabited

/-- One constructor of a parsed block. -/
structure IndCtorRec where
  cv : ConstantVal
  nP : Nat
  nF : Nat
  deriving Repr, Inhabited

/-- One recursor of a parsed block (`numParams`, `numMotives`,
`numMinors`, `numIndices` as exported). -/
structure IndRecRec where
  cv : ConstantVal
  nP : Nat
  nM : Nat
  nm : Nat
  nI : Nat
  rules : List RecRule
  deriving Repr, Inhabited

/-- A parsed inductive block. -/
structure BlockRec where
  types : List IndTypeRec
  ctors : List IndCtorRec
  recs : List IndRecRec
  deriving Repr, Inhabited

/-- What the generator reads besides the block: the declared types of
the constants so far, and the definitional heights. -/
structure Ctx where
  tbl : ConstTable
  heights : Name → Nat
  /-- the parsed inductive blocks so far, by member type name (the
  nested rung reads a container's shape off it) -/
  blocks : Name → Option BlockRec := fun _ => none

/-- Unwrap a generator step that cannot fail on a well-formed block. -/
def need (what : String) : Option α → Except String α
  | some a => pure a
  | none => throw s!"internal shape failure: {what}"

end ConLeche.Frontend.InModel
