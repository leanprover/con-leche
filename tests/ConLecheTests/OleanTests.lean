module

public import ConLeche.Frontend.Olean.Load
public import ConLeche.Verify.Frontend.Olean.Equiv
public import ConLecheTests.ScanTests
/- The checks below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Frontend.Olean.Load
meta import ConLeche.Frontend.Olean.Fast
meta import ConLecheTests.ScanTests

public section

/-!
# The olean reader's specification, evaluated (task #371)

The theorem `decodeModuleSpec_eq_fast` says the fast decoder IS the
specification on every input; these checks are what catches a slip in
the specification's fidelity to the format, which the theorem, being
about two Lean functions, cannot.  On the committed fixtures
(`tests/olean/lib`, the module-system modules at their private level and
their exported level, the classic module) the specification —
spelled out below, since `decodeModuleSpec` itself is compiled as the
fast decoder (`@[csimp]`) — evaluates to the fast decoder's result, and
the result is not empty.
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

-- The equality's footprint: the standard three, nothing else.
/--
info: 'ConLeche.Frontend.Olean.decodeModuleSpec_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms decodeModuleSpec_eq_fast

end ConLecheTests
