module

public import ConLeche.Frontend.Olean.Records
public import ConLeche.Verify.Frontend.Olean.Equiv
public import ConLeche.Verify.Frontend.Olean.Reads
public import ConLeche.Verify.Frontend.Olean.Files
public import ConLecheTests.ScanTests
/- The checks below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Frontend.Olean.Records
meta import ConLecheTests.ScanTests

public section

/-!
# The olean reader, evaluated

The theorems say the fast decoder is the specification and every partial
read is a projection of the full parse, on every input.  The first check
below evaluates them on the committed fixtures (`tests/olean/lib`, the
module-system modules at their private and exported levels, the classic
module), and that the result is not empty.  That catches a slip in either
implementation, but not one in the layout functions they share.  The second
compares what the specification reads off the small fixtures with facts
written down by hand from their sources (`tests/olean/src`): the imports,
the names stored, and the kind, fields and values of a few constants at each
level; and every part's name table (`constNamesOk`) lists its constants.
The third checks the emission's input validation on a hand-made constant.
-/

namespace ConLecheTests

open ConLeche ConLeche.Frontend.Olean

-- `HintsRec`'s instance is `ScanTests`'s.
deriving instance DecidableEq for CKindF, CEntryF

def specDecode (r : Region) (root : UInt64) : Option (Array ImportRec × Array (CEntryF Name Expr)) :=
  (decodeModuleSpec r root).map fun d => (d.imports, d.constants)

def fastDecode (r : Region) (root : UInt64) : Option (Array ImportRec × Array (CEntryF Name Expr)) :=
  (parseFull r root).map fun d => (d.imports, d.constants)

def readPartOrFail (p : String) : IO Part := do
  match Part.ofBytes p (← IO.FS.readBinFile p) with
  | .ok x => pure x
  | .error e => throw (IO.userError s!"{p}: {repr e}")

/-- The decoders agree on one region, read something, and every partial read
is the full parse's part. -/
def agree (what : String) (r : Region) (root : UInt64) : IO Unit := do
  let s := specDecode r root
  unless s == fastDecode r root do throw (IO.userError s!"{what}: the decoders disagree")
  let some (imps, cs) := s | throw (IO.userError s!"{what}: the specification does not read it")
  if cs.isEmpty then throw (IO.userError s!"{what}: no constants read")
  let some sk := moduleSkel r root | throw (IO.userError s!"{what}: no skeleton")
  unless (readHeader r root).map (·.imports) == some imps do
    throw (IO.userError s!"{what}: the header read differs")
  let some l := readLight r root | throw (IO.userError s!"{what}: the light read fails")
  unless l.header.imports == imps && l.consts.map (·.name) == cs.map (·.name) &&
      l.consts.map (·.loc) == sk.consts.toArray do
    throw (IO.userError s!"{what}: the light read differs")
  unless sk.consts.mapM (readEntry r) == some cs.toList do
    throw (IO.userError s!"{what}: the entry reads differ")
  unless readStmts r sk.consts == some (cs.toList.map CEntryF.stmt) do
    throw (IO.userError s!"{what}: the statements read differ")

#eval show IO Unit from do
  let lib := "tests/olean/lib/"
  for m in ["Tiny", "TinyUse", "ClashA", "ClashB"] do
    let ex ← readPartOrFail s!"{lib}{m}.olean"
    let sv ← readPartOrFail s!"{lib}{m}.olean.server"
    let pv ← readPartOrFail s!"{lib}{m}.olean.private"
    let .ok r := Region.ofParts #[ex, sv, pv] | throw (IO.userError s!"{m}: region")
    agree s!"{m} (private level)" r pv.root
    agree s!"{m} (server level)" r sv.root
    agree s!"{m} (exported level)" (Region.single ex) ex.root
    let .ok er := parseExported (.str .anonymous m) ex | throw (IO.userError s!"{m}: exported")
    let .ok mr := parseModule (.str .anonymous m) er ex sv pv | throw (IO.userError s!"{m}: module")
    unless mr.isModule && mr.imports == er.imports && mr.exported.size == er.constants.size do
      throw (IO.userError s!"{m}: the module read")
    -- the imports off every prefix the walk does not run off, up to the file
    for k in [0:ex.bytes.size / 512 + 1] do
      let pre := ex.bytes.extract 0 (k * 512)
      if !(hdrWalk pre dataStart == .short) then
        unless importsPre pre == some er.imports do
          throw (IO.userError s!"{m}: the imports off a prefix of {k * 512} bytes")
  let cl ← readPartOrFail s!"{lib}TinyClassic.olean"
  agree "TinyClassic" (Region.single cl) cl.root

/-! ## Facts from the sources  -/

/-- A name from its dotted spelling. -/
def nm (s : String) : Name := mkN (s.splitOn ".")

def decodeAt (what : String) (r : Region) (root : UInt64) :
    IO (Array ImportRec × Array (CEntryF Name Expr)) := do
  match specDecode r root with
  | some x => pure x
  | none => throw (IO.userError s!"{what}: the specification does not read it")

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
  let ex ← readPartOrFail s!"{lib}Tiny.olean"
  let sv ← readPartOrFail s!"{lib}Tiny.olean.server"
  let pv ← readPartOrFail s!"{lib}Tiny.olean.private"
  let .ok r := Region.ofParts #[ex, sv, pv] | throw (IO.userError "Tiny: region")
  -- Tiny.lean: `prelude`, no imports; `inductive T | a | b`,
  -- `def idT (x : T) : T := x`, `inductive Yes : Prop | intro`,
  -- `theorem yes : Yes := Yes.intro`, all in a public section
  let (imps, cs) ← decodeAt "Tiny (private)" r pv.root
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
  let (impsE, csE) ← decodeAt "Tiny (exported)" (Region.single ex) ex.root
  expect "Tiny's exported part imports nothing" impsE.isEmpty
  expect "yes is exported as an axiom" (kindIs csE "yes" fun | .ax false => true | _ => false)
  expect "idT is exported as an axiom of its type" <| (entry csE "idT").any fun c =>
    c.type == .forallE cT cT && c.kind matches .ax false
  expect "T is exported as it is" (kindIs csE "T" fun | .induct .. => true | _ => false)
  expect "Tiny's name tables" (constNamesOk (Region.single ex) ex.root && constNamesOk r pv.root &&
    constNamesOk r sv.root)
  -- TinyUse.lean: `public import Tiny`; `def twice (x : T) : T := idT (idT x)`
  let ex ← readPartOrFail s!"{lib}TinyUse.olean"
  let sv ← readPartOrFail s!"{lib}TinyUse.olean.server"
  let pv ← readPartOrFail s!"{lib}TinyUse.olean.private"
  let .ok r := Region.ofParts #[ex, sv, pv] | throw (IO.userError "TinyUse: region")
  let (imps, cs) ← decodeAt "TinyUse (private)" r pv.root
  expect "TinyUse imports Tiny" (imps.map (·.module) == #[nm "Tiny"])
  expect "…publicly" (imps.all (·.isExported))
  expect "TinyUse stores twice and yes'" (sortN (cs.map (·.name)) == #[nm "twice", nm "yes'"])
  let idT : Expr := .const (nm "idT") []
  expect "twice := fun x => idT (idT x)" <| kindIs cs "twice" fun
    | .defn v _ _ => v == .lam cT (.app idT (.app idT (.bvar 0)))
    | _ => false
  -- TinyClassic.lean: no `module`; `inductive U | c`, `def idU (x : U) : U := x`
  let cl ← readPartOrFail s!"{lib}TinyClassic.olean"
  let (imps, cs) ← decodeAt "TinyClassic" (Region.single cl) cl.root
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
  expect "TinyClassic's name table" (constNamesOk (Region.single cl) cl.root)

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

#guard (coverageOk orphanMerged (emitAll orphanMerged)) matches .error (.internal _)

-- Module names on the command line (upstream's
-- challenge-numeric-namespace): `«»` escapes taken literally, dots
-- included; empty components and unclosed escapes refused.
#guard parseModName "Challenge.«12.34».«5»" ==
  some ((((Name.anonymous.str "Challenge").str "12.34").str "5"))
#guard parseModName "Init.Data.Nat" == some (((Name.anonymous.str "Init").str "Data").str "Nat")
#guard parseModName "«a.b»" == some (Name.anonymous.str "a.b")
#guard parseModName "123" == some (Name.anonymous.str "123")
#guard ["", "A.", ".A", "A..B", "«A", "«A»B", "A.«B"].all (parseModName · |>.isNone)
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
info: 'ConLeche.Frontend.Olean.decodeModuleFast_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms decodeModuleFast_eq

/-! ### The reads of a parsed module, as statements -/

example (r : Region) (c : Nat) : readEntry r c = constSpec r c := readEntry_eq r c
example (r : Region) (root : UInt64) (d : ModDecoded) (h : parseFull r root = some d) :
    readHeader r root = some ⟨d.isModule, d.imports⟩ := readHeader_of_full h

end ConLecheTests
