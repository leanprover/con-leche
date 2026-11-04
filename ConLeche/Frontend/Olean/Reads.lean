module

public import ConLeche.Frontend.Olean.Sparse
public import Std.Data.HashSet.Basic

@[expose] public section

/-!
# Reading `.olean` files: the full parse, and the reads of a part of it

**The full parse** of a module's root in a region is `parseFull`: its name
table checked (`constNamesOk`), then every constant decoded by the fast
decoder, which is the specification (`decodeModuleFast_eq`,
`parseFull_eq_spec`), so the fast and the specified parse succeed on the
same files.

**The other reads** take less from the same region and root:

| read | what it returns |
|---|---|
| `readHeader` | the module's flag and imports |
| `readLight` | per constant: its location, name, kind and whether the checker skips it |
| `readEntry` | the constant at a location, with a memo of its own |
| `readStmts` | the statements of the constants at some locations |

(and `importsPre`, `ConLeche/Frontend/Olean/Header.lean`: the imports from
a prefix of the file's bytes).  Each is proved to be a projection of the
full parse: **where the full parse succeeds, the read succeeds, and returns
that** (`ConLeche/Verify/Frontend/Olean/Reads.lean`).  The converse does not
hold, on purpose: a read looks only at what it needs, so it can succeed on
a file whose full parse fails on an object the read never visits.  A
reader may rely on a file only through a full parse of it (at the module's
home); the reads then cannot fail or disagree.
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

/-- **A part's name table agrees with its constants** (task #383):
`ModuleData.constNames`, the keys Lean's `finalizeImport` stores the
constants under (it zips the two arrays, never comparing the two names), has as many entries as
`ModuleData.constants`, entry `i` the name of constant `i` (the same
object, or the same name decoded), and no name twice.  The decoder reads
the constants alone, so a table that names them differently would make
the checked constants differ from the ones Lean loads under those names;
and a name stored twice in one part is disambiguated by Lean's loader
(`subsumesInfo`, or "already contains") in a way no other tool need
share. -/
def constNamesOk (r : Region) (root : UInt64) : Bool := Id.run do
  let some g := r.loc root | return false
  unless r.isCtor g 0 5 do return false
  let some ns := r.objArray g (r.fld g 1) | return false
  let some cs := r.objArray g (r.fld g 2) | return false
  unless ns.size == cs.size do return false
  let mut seen : Std.HashSet Name := Std.HashSet.emptyWithCapacity ns.size
  for h : i in [0:ns.size] do
    let some sk := (cs[i]?).bind (constSkel r) | return false
    let some a := nameAt r ns[i] | return false
    unless r.loc sk.name == some ns[i] do
      match nameP r sk.name with
      | some b => unless a == b do return false
      | none => return false
    if seen.contains a then return false
    seen := seen.insert a
  return true

/-- **No two the same**: the list's elements are distinct (`s` the ones
before). -/
def distinctGo {α : Type} [BEq α] [Hashable α] : List α → Std.HashSet α → Bool
  | [], _ => true
  | x :: xs, s =>
    -- (one lookup per element)
    let (b, s) := s.containsThenInsert x
    !b && distinctGo xs s

/-! ## The full parse -/

/-- **The full parse** of the module at `root`: its name table agrees with
its constants, and all of them decode. -/
def parseFull (r : Region) (root : UInt64) : Option ModDecoded := do
  unless constNamesOk r root do none
  decodeModuleFast r root

/-! ## The reads of a part of it -/

/-- A module's flag and imports. -/
structure ModHeader where
  isModule : Bool
  imports : Array ImportRec
  deriving Inhabited, BEq

/-- **The module's flag and imports**, its constants not looked at. -/
def readHeader (r : Region) (root : UInt64) : Option ModHeader := do
  let sk ← moduleSkel r root
  let imports ← sk.imports.mapM (ImportF.mapM (nameP r))
  pure ⟨sk.isModule, imports.toArray⟩

/-- What a light read takes of one stored constant. -/
structure LightConst where
  /-- its location in the region (`readEntry`) -/
  loc : Nat
  name : Name
  /-- the constructor of its kind (`CKindF.tag`) -/
  tag : Nat
  /-- `CKindF.skipped` of its kind -/
  skipped : Bool

/-- **The light read** of a module: its header, and per stored constant,
in the part's order, what `LightConst` holds. -/
structure LightPart where
  header : ModHeader
  consts : Array LightConst

/-- One constant's light read. -/
def lightConst (r : Region) (c : Nat) : Option LightConst := do
  let s ← constSkel r c
  pure ⟨c, ← nameP r s.name, s.kind.tag, s.kind.skipped⟩

/-- **The light read**: no expression of the module is read.  A name two
constants bear fails it: `constNamesOk`'s rule, the part of the name table
check a light read can make. -/
def readLight (r : Region) (root : UInt64) : Option LightPart := do
  let sk ← moduleSkel r root
  let imports ← sk.imports.mapM (ImportF.mapM (nameP r))
  let cs ← sk.consts.mapM (lightConst r)
  unless distinctGo (cs.map (·.name)) (Std.HashSet.emptyWithCapacity cs.length) do none
  pure ⟨⟨sk.isModule, imports.toArray⟩, cs.toArray⟩

/-- **The constant at location `c`**, read with a memo of its own. -/
def readEntry (r : Region) (c : Nat) : Option (CEntryF Name Expr) :=
  constSkel r c >>= sparseEntry r

/-- **The statements of the constants at some locations**, read together. -/
def readStmts (r : Region) (cs : List Nat) : Option (List ConstantVal) :=
  cs.mapM (constSkel r) >>= stmtsFast r

end ConLeche.Frontend.Olean
