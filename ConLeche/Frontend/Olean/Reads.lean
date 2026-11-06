module

public import ConLeche.Frontend.Olean.Sparse

@[expose] public section

/-!
# Reading `.olean` files: taking less of a region

The reads of a part of a `ModuleData`, at a region and an address: what the
interface's reads at a level (`ConLeche/Frontend/Olean/View.lean`) are made of.
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

/-- What `namePositionsAt` takes of one stored constant. -/
structure NamePosition where
  /-- its location in the region (`entryAt`) -/
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
def namePositionsAt (r : Region) (root : UInt64) : Option NamePositions := do
  let sk ← moduleSkel r root
  let imports ← sk.imports.mapM (ImportF.mapM (nameP r))
  let cs ← sk.consts.mapM (namePosition r)
  unless distinctGo (cs.map (·.name)) (Std.HashSet.emptyWithCapacity cs.length) do none
  pure ⟨⟨sk.isModule, imports.toArray⟩, cs.toArray⟩

/-- **The constant at location `c`**, read with a memo of its own. -/
def entryAt (r : Region) (c : Nat) : Option (CEntryF Name Expr) :=
  constSkel r c >>= sparseEntry r

/-- **The statements of the constants at some locations**, read together. -/
def stmtsAt (r : Region) (cs : List Nat) : Option (List ConstantVal) :=
  cs.mapM (constSkel r) >>= stmtsFast r

/-! ### Several constants, one memo -/

/-- One root read into a memo shared by several constants (`sGo`, no frontier); a root
that does not read leaves the memo as it was, and the build reads it again on its own. -/
def memoAdd (r : Region) (k : UInt8) (st : SM) (v : UInt64) : SM :=
  match r.loc v with
  | some c => (sGo r {} k c st).getD st
  | none => st

/-- The roots of a constant's skeleton into the memo: its names, then its expressions. -/
def memoRoots (r : Region) (st : SM) (sk : CEntryF UInt64 UInt64) : SM :=
  sk.exprs.foldl (memoAdd r kExpr) (sk.names.foldl (memoAdd r kName) st)

/-- A name pointer by the memo, else read on its own (`sparseNameP`). -/
def memoName (r : Region) (st : SM) (v : UInt64) : Option Name :=
  if v == 1 then some .anonymous
  else match r.loc v with
    | some c =>
      match st.names[c]? with
      | some n => some n
      | none => sparseNameP r v
    | none => none

/-- An expression pointer by the memo, else read on its own (`sparseExprP`). -/
def memoExpr (r : Region) (st : SM) (v : UInt64) : Option Expr :=
  match r.loc v with
  | some c =>
    match st.exprs[c]? with
    | some e => some e
    | none => sparseExprP r v
  | none => none

/-- **The constants at some locations, read with one memo**: every root of every
constant into the memo first (`memoRoots`), then each constant built from it.  What the
constants share is read once, and shared in the values. -/
def entriesAt (r : Region) (cs : List Nat) : Option (List (CEntryF Name Expr)) := do
  let sks ← cs.mapM (constSkel r)
  let st := sks.foldl (memoRoots r) {}
  sks.mapM (CEntryF.mapM (memoName r st) (memoExpr r st))

/-- **The kind of the constant at location `c`, its expressions left out**: what Lean's
`subsumesInfo` reads of a kind beside the statement (a theorem's `all`, an axiom's
`isUnsafe`). -/
def kindNamesAt (r : Region) (c : Nat) : Option (CKindF Name Unit) := do
  let s ← constSkel r c
  s.kind.mapM (sparseNameP r) (fun _ => some ())

end ConLeche.Frontend.Olean
