module

public import ConLeche.Frontend.Olean.Sparse

@[expose] public section

/-!
# Reading `.olean` files: the reads of a part of a full parse

These take less of a region and root than the full parse (`parseFull`,
`ConLeche/Frontend/Olean/Fast.lean`):

| read | what it returns |
|---|---|
| `readNamePositions` | the header, and per constant its location, name, kind and whether the checker skips it |
| `readEntry` | the constant at a location, with a memo of its own |
| `readStmts` | the statements of the constants at some locations |

Each is proved to be a projection of the full parse: **where the full parse
succeeds, the read succeeds, and returns that**
(`ConLeche/Verify/Frontend/Olean/Reads.lean`).  The converse does not hold, on
purpose: a read looks only at what it needs, so it can succeed on a file whose
full parse fails on an object the read never visits.  A reader may rely on a
file only through a full parse of it (at the module's home); the reads then
cannot fail or disagree.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- lean4export's filter (`dumpConstant`): unsafe and partial constants
are not exported. -/
def CKindF.skipped {N E : Type} (k : CKindF N E) : Bool :=
  match k with
  | .ax u | .opaq _ u | .induct _ _ _ _ _ _ u _ | .ctor _ _ _ _ u | .recur _ _ _ _ _ _ _ u => u
  | .defn _ _ s => s != "safe"
  | .thm .. | .quot _ => false

/-- The constructor of a stored constant's kind, as `ConstantInfo` numbers
them. -/
def CKindF.tag {N E : Type} : CKindF N E → Nat
  | .ax _ => 0
  | .defn .. => 1
  | .thm .. => 2
  | .opaq .. => 3
  | .quot _ => 4
  | .induct .. => 5
  | .ctor .. => 6
  | .recur .. => 7

/-- **No two the same**: the list's elements are distinct (`s` the ones
before). -/
def distinctGo {α : Type} [BEq α] [Hashable α] : List α → Std.HashSet α → Bool
  | [], _ => true
  | x :: xs, s =>
    -- (one lookup per element)
    let (b, s) := s.containsThenInsert x
    !b && distinctGo xs s

/-! ## The reads of a part of it -/

/-- A module's flag and imports. -/
structure ModHeader where
  isModule : Bool
  imports : Array ImportRec
  deriving Inhabited, BEq

/-- What `readNamePositions` takes of one stored constant. -/
structure NamePosition where
  /-- its location in the region (`readEntry`) -/
  loc : Nat
  name : Name
  /-- the constructor of its kind (`CKindF.tag`) -/
  tag : Nat
  /-- `CKindF.skipped` of its kind -/
  skipped : Bool

/-- **The name positions** of a module: its header, and per stored constant,
in the part's order, what `NamePosition` holds. -/
structure NamePositions where
  header : ModHeader
  consts : Array NamePosition

/-- One constant's position and name. -/
def namePosition (r : Region) (c : Nat) : Option NamePosition := do
  let s ← constSkel r c
  pure ⟨c, ← nameP r s.name, s.kind.tag, s.kind.skipped⟩

/-- **The name positions**: no expression of the module is read.  A name two
constants bear fails it: `constNamesOk`'s rule, the part of the name table
check this read can make. -/
def readNamePositions (r : Region) (root : UInt64) : Option NamePositions := do
  let sk ← moduleSkel r root
  let imports ← sk.imports.mapM (ImportF.mapM (nameP r))
  let cs ← sk.consts.mapM (namePosition r)
  unless distinctGo (cs.map (·.name)) (Std.HashSet.emptyWithCapacity cs.length) do none
  pure ⟨⟨sk.isModule, imports.toArray⟩, cs.toArray⟩

/-- **The constant at location `c`**, read with a memo of its own. -/
def readEntry (r : Region) (c : Nat) : Option (CEntryF Name Expr) :=
  constSkel r c >>= sparseEntry r

/-- **The statements of the constants at some locations**, read together. -/
def readStmts (r : Region) (cs : List Nat) : Option (List ConstantVal) :=
  cs.mapM (constSkel r) >>= stmtsFast r

end ConLeche.Frontend.Olean
