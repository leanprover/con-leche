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
    match checkViews (.str .anonymous m) f v with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"{m}: {e}")
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
  { name := nm n, levelParams := [], type, kind, uses := constsOf [type] }

-- A constructor its inductive type does not list is malformed input (it
-- would be dropped without a word): the merged closure's walk finds it.
def orphanMerged : Merged :=
  let cs := #[ent "I" ty0 (.induct 0 0 [nm "I"] [] 0 false false false),
    ent "I.c" (.const (nm "I") []) (.ctor (nm "I") 0 0 0 false)]
  match mergeAll #[⟨nm "M", cs⟩] with
  | .ok mg => mg
  | .error _ => {}

#guard (coverageOk orphanMerged (emitAll orphanMerged orphanMerged.order)) matches .error (.internal _)

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
