module

public import ConLeche.Frontend.Olean.Load
public import ConLeche.Verify.Frontend.Olean.Equiv
public import ConLecheTests.ScanTests
public import ConLeche.Frontend.Olean.Modules
public import ConLeche.Driver.Modular
/- The checks below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Frontend.Olean.Load
meta import ConLeche.Frontend.Olean.Fast
meta import ConLecheTests.ScanTests
meta import ConLeche.Frontend.Olean.Modules
meta import ConLeche.Driver.Modular

public section

/-!
# The olean reader's specification, evaluated (task #371)

The theorem `decodeModuleSpec_eq_fast` says the fast decoder IS the
specification on every input.  The first check below evaluates the two
against each other: on the committed fixtures (`tests/olean/lib`, the
module-system modules at their private level and their exported level,
the classic module) the specification — spelled out below, since
`decodeModuleSpec` itself is compiled as the fast decoder (`@[csimp]`) —
evaluates to the fast decoder's result, and the result is not empty.
That catches a slip in either implementation, but not one in the layout
functions both share.  The second check (task #383) compares what the
specification reads off the small fixtures with facts written down by
hand from their sources (`tests/olean/src`): the imports, the names
stored, and the kind, fields and values of a few constants at each
level; and every part's name table (`constNamesOk`) lists its
constants.  The third checks the emission's input validation on
hand-made constants (a constructor its type does not list, block data
that disagree on which constants form the block).
-/

namespace ConLecheTests

open ConLeche ConLeche.Frontend.Olean

-- `HintsRec`'s instance is `ScanTests`'s.
deriving instance DecidableEq for CKindF, CEntryF

/-- `decodeModuleSpec`, spelled out: its constants are `constSpec`, whose
`nameP`/`exprP` are compiled as written. -/
def specDecode (r : Region) (root : UInt64) : Option (Array Name × Array (CEntryF Name Expr)) := do
  let sk ← moduleSkel r root
  let imports ← sk.imports.mapM (nameP r)
  let constants ← sk.consts.mapM (constSpec r)
  pure (imports.toArray, constants.toArray)

def fastDecode (r : Region) (root : UInt64) : Option (Array Name × Array (CEntryF Name Expr)) :=
  (decodeModuleFast r root true).map fun d => (d.imports, d.constants)

def readPartOrFail (p : String) : IO Part := do
  match Part.ofBytes p (← IO.FS.readBinFile p) with
  | .ok x => pure x
  | .error e => throw (IO.userError s!"{p}: {repr e}")

/-- Spec and fast decoder agree on one region, and read something. -/
def agree (what : String) (r : Region) (root : UInt64) : IO Unit := do
  let s := specDecode r root
  unless s == fastDecode r root do throw (IO.userError s!"{what}: the decoders disagree")
  match s with
  | some (_, cs) =>
    if cs.isEmpty then throw (IO.userError s!"{what}: no constants read")
  | none => throw (IO.userError s!"{what}: the specification does not read it")

#eval show IO Unit from do
  let lib := "tests/olean/lib/"
  for m in ["Tiny", "TinyUse", "ClashA", "ClashB"] do
    let ex ← readPartOrFail s!"{lib}{m}.olean"
    let sv ← readPartOrFail s!"{lib}{m}.olean.server"
    let pv ← readPartOrFail s!"{lib}{m}.olean.private"
    let .ok r := Region.ofParts #[ex, sv, pv] | throw (IO.userError s!"{m}: region")
    agree s!"{m} (private level)" r pv.root
    agree s!"{m} (exported level)" (Region.single ex) ex.root
  let cl ← readPartOrFail s!"{lib}TinyClassic.olean"
  agree "TinyClassic" (Region.single cl) cl.root

/-! ## Facts from the sources (task #383) -/

/-- A name from its dotted spelling. -/
def nm (s : String) : Name := mkN (s.splitOn ".")

def decodeAt (what : String) (r : Region) (root : UInt64) :
    IO (Array Name × Array (CEntryF Name Expr)) := do
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
  expect "TinyUse imports Tiny" (imps == #[nm "Tiny"])
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

/-! ## The module emission's validation (task #383) -/

def ty0 : Expr := .sort (.succ .zero)

def ent (n : String) (type : Expr) (kind : CKind) : CEntry :=
  { name := nm n, levelParams := [], type, kind, uses := constsOf [type] }

-- A constructor its inductive type does not list is malformed input (it
-- was dropped without a word); so in the merged closure's walk.
#guard match moduleDecls #[ent "I" ty0 (.induct 0 0 [nm "I"] [] 0 false false false),
    ent "I.c" (.const (nm "I") []) (.ctor (nm "I") 0 0 0 false)] with
  | .error (.internal m, _) => m.startsWith "the constant I.c is in no emitted record"
  | _ => false

def orphanMerged : Merged :=
  let cs := #[ent "I" ty0 (.induct 0 0 [nm "I"] [] 0 false false false),
    ent "I.c" (.const (nm "I") []) (.ctor (nm "I") 0 0 0 false)]
  match mergeAll #[⟨nm "M", #[], cs⟩] with
  | .ok mg => mg
  | .error _ => {}

#guard (coverageOk orphanMerged (emitAll orphanMerged)) matches .error (.internal _)

-- An inductive type naming a constructor that is not stored.
#guard match moduleDecls #[ent "I" ty0 (.induct 0 0 [nm "I"] [nm "I.c"] 0 false false false)] with
  | .error (.internal m, _) => m.startsWith "the inductive data of I: its constructor I.c is not stored"
  | _ => false

/-! ## The modular driver's verdict under `--keep-going` (task #383) -/

-- the most severe failure decides: an internal error or malformed input
-- (3) over a rejection (1) over a decline (2) over an accept (0)
#guard [(0, 2, 2), (2, 1, 1), (1, 2, 1), (1, 3, 3), (3, 1, 3), (2, 3, 3), (0, 0, 0)].all
  fun (a, b, c) => Driver.Modular.worseExit a b == c

-- holes: a definition and an opaque hole are installed by their
-- statements (theorem records), each remembering the kind that fills it
#guard
  let cv : ConstantVal := ⟨nm "h", [], .const (nm "Nat") []⟩
  let v : Expr := .app (.app (.const sorryAxName [.zero]) (.const (nm "Nat") [])) (.const (nm "Bool.false") [])
  let ds := #[Declaration.defnDecl cv v (.regular 0), .opaqueDecl cv v, .thmDecl cv v]
  (Driver.Modular.assumeHoles ds).all (· matches .thmDecl ..) &&
    (ds.map fun d => (Driver.Modular.holesOf #[d])[nm "h"]?) == #[some 1, some 0, some 2]

-- A constructor naming another type than the one listing it.
#guard match moduleDecls #[ent "I" ty0 (.induct 0 0 [nm "I", nm "J"] [nm "I.c"] 0 false false false),
    ent "J" ty0 (.induct 0 0 [nm "I", nm "J"] [] 0 false false false),
    ent "I.c" (.const (nm "I") []) (.ctor (nm "J") 0 0 0 false)] with
  | .error (.internal m, _) => m.startsWith "the inductive data of I: its constructor I.c names"
  | _ => false

-- Two block members that name different blocks.
#guard match moduleDecls #[ent "I" ty0 (.induct 0 0 [nm "I", nm "J"] [] 0 false false false),
    ent "J" ty0 (.induct 0 0 [nm "J"] [] 0 false false false)] with
  | .error (.internal m, _) => m.startsWith "the inductive data of I: its block member J"
  | _ => false

-- Module names on the command line (task #384, upstream's
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

-- The equality's footprint: the standard three, nothing else.
/--
info: 'ConLeche.Frontend.Olean.decodeModuleSpec_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms decodeModuleSpec_eq_fast

end ConLecheTests
