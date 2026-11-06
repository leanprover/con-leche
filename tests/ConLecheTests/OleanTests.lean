module

public import ConLeche.Frontend.Olean
public import ConLeche.Verify.Frontend.Olean.Files
public import ConLeche.Verify.Frontend.Olean.View
public import ConLecheTests.ScanTests
/- The checks below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Frontend.Olean
meta import ConLecheTests.ScanTests

public section

/-!
# The olean reader, evaluated

The theorems say the fast decoder is the specification and every partial
read is a projection of the full parse, on every input.  The first check
below evaluates the second on the committed fixtures (`tests/olean/lib`, the
module-system modules at their private and exported levels, the classic
module), and that the result is not empty.  The specification is not
executable.  The second compares what the full parse reads off the small
fixtures with facts
written down by hand from their sources (`tests/olean/src`): the imports,
the names stored, and the kind, fields and values of a few constants at each
level; and every part's name table (`constNamesOk`) lists its constants.
The third checks the emission's input validation on a hand-made constant.
The first also evaluates the load: with each theorem's value read over the
module's frontier, it is the private view.
-/

namespace ConLecheTests

open ConLeche ConLeche.Frontend.Olean

-- `HintsRec`'s instance is `ScanTests`'s.
deriving instance DecidableEq for CKindF, CEntryF

/-- A view's imports and constants. -/
def pairOf (d : ModDecoded) : Array ImportRec × Array (CEntryF Name Expr) :=
  (d.imports, d.constants)

def fastDecode (f : ModFiles) (level : OLeanLevel) :
    Option (Array ImportRec × Array (CEntryF Name Expr)) :=
  (parseView f level).map pairOf

def readPartOrFail (p : String) : IO Part := do
  match Part.ofBytes p (← IO.FS.readBinFile p) with
  | .ok x => pure x
  | .error e => throw (IO.userError s!"{p}: {repr e}")

/-- A view reads something, and every read of a part of it is its part. -/
def agree (what : String) (f : ModFiles) (level : OLeanLevel) : IO Unit := do
  let some d := parseView f level | throw (IO.userError s!"{what}: it does not read")
  if d.constants.isEmpty then throw (IO.userError s!"{what}: no constants read")
  let some l := readNamePositions f level | throw (IO.userError s!"{what}: no name positions")
  unless l.header.imports == d.imports && l.consts.map (·.name) == d.constants.map (·.name) do
    throw (IO.userError s!"{what}: the name positions differ")
  unless l.consts.toList.mapM (readEntry f level ·.loc) == some d.constants.toList do
    throw (IO.userError s!"{what}: the entry reads differ")
  unless readStmts f level (l.consts.toList.map (·.loc)) == some (d.constants.toList.map CEntryF.stmt) do
    throw (IO.userError s!"{what}: the statements read differ")
  -- with one memo, all at once and in another order
  unless readEntries f level (l.consts.toList.map (·.loc)) == some d.constants.toList do
    throw (IO.userError s!"{what}: the entries read with one memo differ")
  unless readEntries f level (l.consts.toList.reverse.map (·.loc)) == some d.constants.toList.reverse do
    throw (IO.userError s!"{what}: the entries read with one memo, reversed, differ")

/-- **A module's load, each theorem's value read over its frontier, is the private view**:
`loadAt_spec`, `lazyEntry_of_spec`, `frontierExpr_eq` on the fixtures.  What a constant
mentions is compared with what the full parse says, as the walk over the file's objects has
no theorem. -/
def loadAgrees (what : String) (i : Nat) (f : ModFiles) : IO Unit := do
  let some d := parseView f .private | throw (IO.userError s!"{what}: it does not read")
  let some l := loadAt i (.str .anonymous what) f | throw (IO.userError s!"{what}: the load fails")
  let some (r, _) := f.viewRegion .private | throw (IO.userError s!"{what}: no region")
  unless l.constants.size == d.constants.size do
    throw (IO.userError s!"{what}: a constant more or less")
  for e in l.constants, c in d.constants do
    match e.kind, c.kind with
    | .thm (.bvar code) all, .thm v all' =>
      unless refModule code == i && all == all' do
        throw (IO.userError s!"{what}: {c.name}: the reference's module or the block")
      unless frontierExpr r l.frontier (refLoc code) == some v do
        throw (IO.userError s!"{what}: {c.name}: its value over the frontier")
      unless frontierExpr r {} (refLoc code) == some v do
        throw (IO.userError s!"{what}: {c.name}: its value with no frontier")
      unless e.name == c.name && e.levelParams == c.levelParams && e.type == c.type do
        throw (IO.userError s!"{what}: {c.name}: its statement")
    | .thm .., _ | _, .thm .. => throw (IO.userError s!"{what}: {c.name}: its kind")
    | _, _ =>
      unless e.toCEntryF == c do
        throw (IO.userError s!"{what}: {c.name} differs")

/-- A module's files. -/
def filesOf (lib m : String) : IO ModFiles := do
  let ex ← readPartOrFail s!"{lib}{m}.olean"
  if ← System.FilePath.pathExists s!"{lib}{m}.olean.private" then
    pure { exported := ex, server := some (← readPartOrFail s!"{lib}{m}.olean.server"),
           «private» := some (← readPartOrFail s!"{lib}{m}.olean.private") }
  else pure { exported := ex }

#eval show IO Unit from do
  let lib := "tests/olean/lib/"
  for m in ["Tiny", "TinyUse", "ClashA", "ClashB", "TinyClassic"] do
    let f ← filesOf lib m
    for level in [OLeanLevel.exported, .server, .private] do
      agree s!"{m} ({repr level})" f level
    let some v := parseAllViews f | throw (IO.userError s!"{m}: all views")
    for level in [OLeanLevel.exported, .server, .private] do
      unless fastDecode f level == some (pairOf (v.at level)) do
        throw (IO.userError s!"{m} ({repr level}): differs from the one-memo read")
    -- an importer holding M.olean alone reads the home's exported view
    unless fastDecode { exported := f.exported } .exported == some (pairOf v.exported) do
      throw (IO.userError s!"{m}: the exported file alone")
    let some ld := loadAt 0 (.str .anonymous m) f | throw (IO.userError s!"{m}: the load")
    match checkViews (.str .anonymous m) f ld with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"{m}: {e}")
    loadAgrees m 7 f
    -- the imports off every prefix the walk does not run off, up to the file
    let bytes := f.exported.bytes
    for k in [0:bytes.size / 512 + 1] do
      let pre := bytes.extract 0 (k * 512)
      if !(hdrWalk pre dataStart == .short) then
        unless importsPre pre == some v.exported.imports do
          throw (IO.userError s!"{m}: the imports off a prefix of {k * 512} bytes")

/-! ## Facts from the sources  -/

/-- A name from its dotted spelling. -/
def nm (s : String) : Name := mkN (s.splitOn ".")

def decodeOf (what : String) (f : ModFiles) (level : OLeanLevel) :
    IO (Array ImportRec × Array (CEntryF Name Expr)) := do
  match fastDecode f level with
  | some x => pure x
  | none => throw (IO.userError s!"{what}: the full parse does not read it")

def expect (what : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"fixture fact failed: {what}")

/-- The constant of a name, by the decoded entries. -/
def entry (cs : Array (CEntryF Name Expr)) (n : String) : Option (CEntryF Name Expr) :=
  cs.find? (·.name == nm n)

def kindIs (cs : Array (CEntryF Name Expr)) (n : String) (p : CKind → Bool) : Bool :=
  match entry cs n with
  | some c => p c.kind
  | none => false

def cT : Expr := .const (nm "T") []

def sortN (xs : Array Name) : Array Name := xs.qsort fun a b => toString a < toString b

#eval show IO Unit from do
  let lib := "tests/olean/lib/"
  let f ← filesOf lib "Tiny"
  -- Tiny.lean: `prelude`, no imports; `inductive T | a | b`,
  -- `def idT (x : T) : T := x`, `inductive Yes : Prop | intro`,
  -- `theorem yes : Yes := Yes.intro`, all in a public section
  let (imps, cs) ← decodeOf "Tiny (private)" f .private
  expect "Tiny imports nothing" imps.isEmpty
  for n in ["T", "T.a", "T.b", "T.rec", "idT", "Yes", "Yes.intro", "Yes.rec", "yes"] do
    expect s!"Tiny stores {n}" (entry cs n).isSome
  expect "T is a type of two constructors, no parameters or indices" <| kindIs cs "T" fun
    | .induct 0 0 [a] [c₁, c₂] 0 false false false => a == nm "T" && c₁ == nm "T.a" && c₂ == nm "T.b"
    | _ => false
  expect "T : Type" ((entry cs "T").map (·.type) == some (.sort (.succ .zero)))
  expect "T.b is T's constructor 1, no fields" <| kindIs cs "T.b" fun
    | .ctor i 1 0 0 false => i == nm "T"
    | _ => false
  expect "T.b : T" ((entry cs "T.b").map (·.type) == some cT)
  expect "idT : T → T := fun x => x" <| (entry cs "idT").any fun c =>
    c.type == .forallE cT cT && match c.kind with
      | .defn v _ "safe" => v == .lam cT (.bvar 0)
      | _ => false
  expect "yes : Yes := Yes.intro" <| (entry cs "yes").any fun c =>
    c.type == .const (nm "Yes") [] && match c.kind with
      | .thm v [a] => v == .const (nm "Yes.intro") [] && a == nm "yes"
      | _ => false
  expect "Yes : Prop" ((entry cs "Yes").map (·.type) == some (.sort .zero))
  -- the exported level: the theorem and the unexposed definition as
  -- axioms of their statements, the inductive types as they are
  let (impsE, csE) ← decodeOf "Tiny (exported)" f .exported
  expect "Tiny's exported part imports nothing" impsE.isEmpty
  expect "yes is exported as an axiom" (kindIs csE "yes" fun | .ax false => true | _ => false)
  expect "idT is exported as an axiom of its type" <| (entry csE "idT").any fun c =>
    c.type == .forallE cT cT && c.kind matches .ax false
  expect "T is exported as it is" (kindIs csE "T" fun | .induct .. => true | _ => false)
  -- TinyUse.lean: `public import Tiny`; `def twice (x : T) : T := idT (idT x)`
  let f ← filesOf lib "TinyUse"
  let (imps, cs) ← decodeOf "TinyUse (private)" f .private
  expect "TinyUse imports Tiny" (imps.map (·.module) == #[nm "Tiny"])
  expect "…publicly" (imps.all (·.isExported))
  expect "TinyUse stores twice and yes'" (sortN (cs.map (·.name)) == #[nm "twice", nm "yes'"])
  let idT : Expr := .const (nm "idT") []
  expect "twice := fun x => idT (idT x)" <| kindIs cs "twice" fun
    | .defn v _ _ => v == .lam cT (.app idT (.app idT (.bvar 0)))
    | _ => false
  -- TinyClassic.lean: no `module`; `inductive U | c`, `def idU (x : U) : U := x`
  let f ← filesOf lib "TinyClassic"
  let (imps, cs) ← decodeOf "TinyClassic" f .private
  expect "TinyClassic imports nothing" imps.isEmpty
  expect "TinyClassic stores U, U.c, U.rec, U.recOn, idU" (sortN (cs.map (·.name)) ==
    sortN #[nm "U", nm "U.c", nm "U.rec", nm "U.recOn", nm "idU"])
  expect "U has the one constructor U.c" <| kindIs cs "U" fun
    | .induct 0 0 _ [c] 0 false false false => c == nm "U.c"
    | _ => false
  let cU : Expr := .const (nm "U") []
  expect "idU := fun x => x" <| kindIs cs "idU" fun
    | .defn v _ _ => v == .lam cU (.bvar 0)
    | _ => false

/-! ## The module emission's validation  -/

def ty0 : Expr := .sort (.succ .zero)

def ent (n : String) (type : Expr) (kind : CKind) : CEntry :=
  { name := nm n, levelParams := [], type, kind }

-- A constructor its inductive type does not list is malformed input (it
-- would be dropped without a word).
def orphanMerged : Merged :=
  let cs := #[ent "I" ty0 (.induct 0 0 [nm "I"] [] 0 false false false),
    ent "I.c" (.const (nm "I") []) (.ctor (nm "I") 0 0 0 false)]
  match mergeAll #[⟨nm "M", cs, {}⟩] with
  | .ok mg => mg
  | .error _ => {}

#guard (blocksOk orphanMerged) matches .error (.internal _)

/-- The merge of some constants; a merge that fails is the empty one, on which the guards below
would fail. -/
def mergedOf (cs : Array CEntry) : Merged :=
  match mergeAll #[⟨nm "M", cs, {}⟩] with
  | .ok mg => mg
  | .error _ => {}

def indI (all cs : List Name) (u : Bool := false) : CEntry :=
  ent "I" ty0 (.induct 0 0 all cs 0 false u false)

def ctorIc (ind : String := "I") (u : Bool := false) : CEntry :=
  ent "I.c" (.const (nm "I") []) (.ctor (nm ind) 0 0 0 u)

def recI (all : List Name) (u : Bool := false) : CEntry :=
  ent "I.rec" ty0 (.recur all 0 0 0 0 [] false u)

def isBlocksError (cs : Array CEntry) : Bool :=
  (mergedOf cs).order.size == cs.size &&
    match blocksOk (mergedOf cs) with
    | .error (.internal _) => true
    | _ => false

-- A block in order.
#guard (blocksOk (mergedOf #[indI [nm "I"] [nm "I.c"], ctorIc, recI [nm "I"]])) matches .ok ()
-- The same block filtered out, as a whole.
#guard (blocksOk (mergedOf #[indI [nm "I"] [nm "I.c"] true, ctorIc "I" true, recI [nm "I"] true]))
  matches .ok ()
-- A block's `all` that names a theorem: the walk would mark the theorem visited and the block's
-- record would leave it out, so that it is never checked.
#guard isBlocksError #[indI [nm "I", nm "bad"] [], ent "bad" ty0 (.thm (.sort .zero) [nm "bad"])]
-- A block that does not list its own type, or names one that is not stored.
#guard isBlocksError #[indI [] []]
#guard isBlocksError #[indI [nm "I", nm "J"] []]
-- Two types that disagree on the block.
#guard isBlocksError #[indI [nm "I", nm "J"] [],
  ent "J" ty0 (.induct 0 0 [nm "J"] [] 0 false false false)]
-- A listed constructor that is not stored, is no constructor, or names another type.
#guard isBlocksError #[indI [nm "I"] [nm "I.c"]]
#guard isBlocksError #[indI [nm "I"] [nm "I.c"], ent "I.c" ty0 (.ax false)]
#guard isBlocksError #[indI [nm "I"] [nm "I.c"], ctorIc "J",
  ent "J" ty0 (.induct 0 0 [nm "J"] [nm "I.c"] 0 false false false)]
-- A constructor whose type is not stored, or is no inductive type.
#guard isBlocksError #[ctorIc]
#guard isBlocksError #[ent "I" ty0 (.ax false), ctorIc]
-- A recursor of no block, of a block not stored, of no inductive type, or not its member's.
#guard isBlocksError #[recI []]
#guard isBlocksError #[recI [nm "I"]]
#guard isBlocksError #[ent "I" ty0 (.ax false), recI [nm "I"]]
#guard isBlocksError #[indI [nm "I"] [], recI [nm "I", nm "J"]]
-- Parts of a block of which some are filtered out: the walk would not reach the safe ones'
-- record through the unsafe type.
#guard isBlocksError #[indI [nm "I"] [nm "I.c"] true, ctorIc]
#guard isBlocksError #[indI [nm "I"] [nm "I.c"], ctorIc "I" true]
#guard isBlocksError #[indI [nm "I"] [] true, recI [nm "I"]]
-- A quotient constant outside the package, and a package holding another kind.
#guard isBlocksError #[ent "Q" ty0 (.quot "type")]
#guard isBlocksError #[ent "Quot" ty0 (.quot "type"), ent "Quot.mk" ty0 (.ax false)]
#guard (blocksOk (mergedOf #[ent "Quot" ty0 (.quot "type"), ent "Quot.mk" ty0 (.quot "ctor")]))
  matches .ok ()

/-! ## One group's record -/

-- A group validated alone, as `blocksOk` validates a merged block: in order; a listed
-- constructor not stored; a member of another block; a recursor of another block.
#guard (groupRecord (mergedOf #[indI [nm "I"] [nm "I.c"], ctorIc]) (nm "I")) matches
  .ok (.indDecl [.indInfo .., .ctorInfo ..] 0)
-- (a recursor of no motive: the record builder's verdict, as for a merged block)
#guard (groupRecord (mergedOf #[indI [nm "I"] [nm "I.c"], ctorIc, recI [nm "I"]]) (nm "I")) matches
  .error (.invalid _)
#guard (groupRecord (mergedOf #[indI [nm "I"] [nm "I.c"]]) (nm "I")) matches .error (.internal _)
#guard (groupRecord (mergedOf #[indI [nm "I", nm "J"] [],
  ent "J" ty0 (.induct 0 0 [nm "J"] [] 0 false false false)]) (nm "I")) matches .error (.internal _)
#guard (groupRecord (mergedOf #[indI [nm "I"] [], recI [nm "I", nm "J"]]) (nm "I"))
  matches .error (.internal _)
-- a name that is no inductive type
#guard (groupRecord (mergedOf #[ent "I" ty0 (.ax false)]) (nm "I")) matches .error (.internal _)

/-- A block's recursors by name: the exported part lists its constants sorted by name, the
private part in the order they were declared. -/
def recsSorted : Declaration → Declaration
  | .indDecl block np =>
    let isRec : ConstantInfo → Bool := fun | .recInfo .. => true | _ => false
    .indDecl (block.filter (!isRec ·) ++
      ((block.filter isRec).toArray.qsort (toString ·.name < toString ·.name)).toList) np
  | d => d

/-- **A group's record read from one part is the emission's**: every inductive type of the
fixture's private and exported parts, `readGroup` then `groupRecord`, against the record
the merged emission of the module's load builds for it (at the exported part, up to the
order of the recursors). -/
def groupAgrees (lib m : String) : IO Unit := do
  let f ← filesOf lib m
  let some ld := loadAt 0 (nm m) f | throw (IO.userError s!"{m}: the load")
  let .ok mg := mergeAll #[ld] | throw (IO.userError s!"{m}: the merge")
  for level in [OLeanLevel.private, .exported] do
    let some ps := readNamePositions f level | throw (IO.userError s!"{m}: the names")
    let locs : Std.HashMap Name Nat := ps.consts.foldl (fun m q => m.insert q.name q.loc) {}
    let recs := (ps.consts.filter (·.tag == 7)).toList.map (·.loc)
    for q in ps.consts do
      if q.tag != 5 then continue
      let some g := readGroup f level (locs[·]?) recs q.name | throw (IO.userError s!"{q.name}: read")
      let .ok d := groupRecord g q.name | throw (IO.userError s!"{q.name}: the record")
      let .ok ds := declsOf (emitAll mg #[q.name]) | throw (IO.userError s!"{q.name}: the emission")
      unless ds.any (fun e => if level == .private then e == d else recsSorted e == recsSorted d) do
        throw (IO.userError s!"{m} ({repr level}): {q.name}'s record is not the emission's")

#eval show IO Unit from do
  groupAgrees "tests/olean/lib/" "GrN"
  groupAgrees "tests/olean/lib/" "Tiny"
  groupAgrees "tests/olean/lib/" "TinyClassic"

/-! ## The header fixpoint -/

/-- The modules a fixture's header loads, with the part of each, in the order. -/
def loadsOf (m : String) : IO (List (String × Bool × Bool)) := do
  let sp : SearchPath := ["tests/olean/lib"]
  let f ← filesOf "tests/olean/lib/" m
  let some ps := readNamePositions f .private | throw (IO.userError s!"{m}: the names")
  match ← (headerFixpoint sp ps.header.isModule ps.header.imports : IO _) with
  | .ok ld => pure ((ld.order.zip ld.flags).toList.map fun (n, fl) => (toString n, fl.importAll, fl.isExported))
  | .error e => throw (IO.userError s!"{m}: {e}")

-- (compared by hand with Lean's own `importModules` of the headers, `env.header.modules`)
#eval show IO Unit from do
  -- `import all LvA`: LvA whole, its plain import LvB's exported part, LvB's `import all LvC`
  -- not followed (LvB is not loaded whole)
  unless (← loadsOf "LvM") == [("LvB", false, false), ("LvA", true, false)] do
    throw (IO.userError "LvM's loads")
  -- `public import LvA` (its plain import of LvB not followed), `import all LvB` (so LvC whole)
  unless (← loadsOf "LvN") == [("LvA", false, true), ("LvC", true, false), ("LvB", true, false)] do
    throw (IO.userError "LvN's loads")
  -- a module outside the module system loads everything whole
  unless (← loadsOf "TinyUse") == [("Tiny", false, true)] do throw (IO.userError "TinyUse's loads")

-- Module names on the command line (upstream's
-- challenge-numeric-namespace): `«»` escapes taken literally, dots
-- included; empty components and unclosed escapes refused.
#guard parseModName "Challenge.«12.34».«5»" ==
  some ((((Name.anonymous.str "Challenge").str "12.34").str "5"))
#guard parseModName "Init.Data.Nat" == some (((Name.anonymous.str "Init").str "Data").str "Nat")
#guard parseModName "«a.b»" == some (Name.anonymous.str "a.b")
#guard parseConstName "_private.M.0.foo" ==
  some ((((Name.anonymous.str "_private").str "M").num 0).str "foo")
#guard parseConstName "«0».x" == some ((Name.anonymous.str "0").str "x")
#guard parseModName "123" == some (Name.anonymous.str "123")
#guard ["", "A.", ".A", "A..B", "«A", "«A»B", "A.«B", "«»", "A.«»"].all (parseModName · |>.isNone)
#guard (modFile "d" ((((Name.anonymous.str "Challenge").str "12.34").str "5")) "olean").toString
  == "d/Challenge/12.34/5.olean"

-- A bignum's limbs by halves (task #395): the halving agrees with the
-- plain fold, and a literal of a million limbs (all ones: `2^(64·n) - 1`)
-- decodes at once — the fold alone is quadratic, minutes at that size.
def limbBytes : ByteArray := ⟨(Array.range 800).map fun i => (i * 37 + 11).toUInt8⟩
#guard [0, 1, 15, 16, 17, 33, 64, 99, 100].all fun n => limbs limbBytes 0 n == limbsFold limbBytes 0 n 0
#guard limbs limbBytes 8 91 == limbsFold limbBytes 8 91 0
def onesBytes (n : Nat) : ByteArray := ⟨Array.replicate (8 * n) 255⟩
#guard limbs (onesBytes 1000000) 0 1000000 + 1 == 1 <<< (64 * 1000000)

-- The equality's footprint: the standard three, nothing else.
/--
info: 'ConLeche.Frontend.Olean.parseView_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parseView_eq_spec

/-! ### As statements -/

example (f : ModFiles) (level : OLeanLevel) : parseView f level = decodeModuleSpec f level :=
  parseView_eq_spec f level

end ConLecheTests
