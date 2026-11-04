module

public import ConLeche.Frontend.Olean.Header
public import ConLeche.Frontend.Olean.Reads
public import Std.Data.HashMap.Basic

@[expose] public section

/-!
# Reading `.olean` files: one module's parts

A module of the module system has three files, `M.olean` (the exported
level), `M.olean.server` and `M.olean.private`, one address space
(`Region.ofParts`); a classic module has its `M.olean` alone.

**The exported part is read alone** (`parseExported`), in the region of
that one file, as an importer reads it, and **the module's full read**
(`parseModule`) starts from that, so that a home and an importer of one
file take its exported constants from one function of its bytes.  Every
check that the parts' redundant data agree is the full read's (a mismatch
is malformed input, `.internal`, exit 3):

* every part's name table lists its constants, each name once
  (`constNamesOk`: the exported, server and private part);
* the imports the prefix of the exported file holds are its root's
  (`importsPre`);
* the server and private parts' headers are the exported part's: a
  module of the module system, the same imports with the same flags;
* every constant of the exported part, and of the server part, is the
  private part's constant of its name or that constant with its value
  hidden (`expoOfParts`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- The module's files do not decode. -/
def undecodable (m : Name) : CheckError :=
  .internal s!"module {m}: malformed .olean data (an object of the wrong shape, or a \
    pointer that does not point below its object)"

/-- The malformed name table's error. -/
def badConstNames (m : Name) (part : String) : CheckError :=
  .internal s!"module {m}: the {part} part's name table (constNames) does not list its \
    constants' names, each once"

/-- `parseFull`, with the module's error. -/
def parseFullE (m : Name) (part : String) (r : Region) (root : UInt64) :
    Except CheckError ModDecoded :=
  match parseFull r root with
  | some d => .ok d
  | none => .error (if constNamesOk r root then undecodable m else badConstNames m part)

/-! ## The exported part -/

/-- **A module's exported part, read in full and alone**: what an importer
at the exported level sees of it. -/
def parseExported (m : Name) (ex : Part) : Except CheckError ModDecoded := do
  let d ← parseFullE m "exported" (Region.single ex) ex.root
  unless importsPre ex.bytes == some d.imports do .error (undecodable m)
  pure d

/-! ## The levels of a module's constants -/

/-- **A private constant at the exported level.** -/
inductive Expo where
  /-- the exported part stores the same constant -/
  | same
  /-- the exported part stores it as an axiom of the same name, level
  parameters and type: its value is hidden -/
  | hidden
  /-- the exported part does not store it -/
  | absent
  deriving Inhabited, DecidableEq, Repr

def hintsEq : HintsRec → HintsRec → Bool
  | .abbrev, .abbrev | .opaque, .opaque => true
  | .regular a, .regular b => a == b
  | _, _ => false

def rulesEq : List (Name × Nat × Expr) → List (Name × Nat × Expr) → Bool
  | [], [] => true
  | (a, b, c) :: xs, (a', b', c') :: ys => a == a' && b == b' && c == c' && rulesEq xs ys
  | _, _ => false

/-- Structural equality of two stored constants (expressions by the
checker's equality, pointer-equal first). -/
def entrySame (a b : CEntryF Name Expr) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
  match a.kind, b.kind with
  | .ax u, .ax u' => u == u'
  | .defn v h s, .defn v' h' s' => v == v' && hintsEq h h' && s == s'
  | .thm v al, .thm v' al' => v == v' && al == al'
  | .opaq v u, .opaq v' u' => v == v' && u == u'
  | .quot k, .quot k' => k == k'
  | .induct a b c d e f g h, .induct a' b' c' d' e' f' g' h' =>
    a == a' && b == b' && c == c' && d == d' && e == e' && f == f' && g == g' && h == h'
  | .ctor a b c d e, .ctor a' b' c' d' e' =>
    a == a' && b == b' && c == c' && d == d' && e == e'
  | .recur a b c d e f g h, .recur a' b' c' d' e' f' g' h' =>
    a == a' && b == b' && c == c' && d == d' && e == e' && rulesEq f f' && g == g' && h == h'
  | _, _ => false

/-- A stored constant's kind, for messages. -/
def kindWord : CKind → String
  | .ax u => s!"axiom{if u then " (unsafe)" else ""}"
  | .defn _ _ s => s!"definition ({s})"
  | .thm .. => "theorem"
  | .opaq _ u => s!"opaque{if u then " (unsafe)" else ""}"
  | .quot _ => "quotient"
  | .induct .. => "inductive"
  | .ctor .. => "constructor"
  | .recur .. => "recursor"

/-- **The exported level of one private constant**, given the exported
part's constant of that name: the same constant, or the private one
with its value hidden; `none` is a constant the exported part does not
refine. -/
def expoOf (priv ex : CEntryF Name Expr) : Option Expo :=
  if entrySame priv ex then some .same
  else if priv.name == ex.name && priv.levelParams == ex.levelParams && priv.type == ex.type then
    -- the axiom Lean exports in its place (`addDeclCore`): unsafe exactly
    -- when the definition is not safe or the opaque constant is unsafe
    match priv.kind, ex.kind with
    | .defn _ _ s, .ax u => if u == (s != "safe") then some .hidden else none
    | .thm .., .ax u => if !u then some .hidden else none
    | .opaq _ u', .ax u => if u == u' then some .hidden else none
    | _, _ => none
  else none

/-- **The exported level of a module's private constants**: for each
exported constant, the private constant it stands for — the same object
(the private part points into the exported part), the same skeleton
(names and expressions as pointers), the same constant decoded, or an
axiom of the same name, level parameters and type (by pointer, else
decoded) where the private one is a definition, theorem or opaque
constant.  `none` with the reason: an exported view that is not a
refinement of the private one. -/
def expoOfParts (r : Region) (privRoot expRoot : UInt64) (cs : Array (CEntryF Name Expr)) :
    Except String (Array Expo) := do
  let some skP := moduleSkel r privRoot | throw "malformed private part"
  let some skE := moduleSkel r expRoot | throw "malformed exported part"
  let privLoc : Std.HashMap Nat Nat :=
    skP.consts.foldl (fun (m, i) c => (m.insert c i, i + 1)) ({}, 0) |>.1
  let privLocs := skP.consts.toArray
  let privIdx : Std.HashMap Name Nat :=
    cs.size.fold (init := {}) fun i _ acc => acc.insert cs[i].name i
  let mut expo : Array Expo := cs.map fun _ => .absent
  for c in skE.consts do
    if let some i := privLoc[c]? then
      expo := expo.set! i .same
    else
      let some se := constSkel r c | throw "malformed exported constant"
      let some en := nameP r se.name | throw "malformed exported constant"
      let some i := privIdx[en]? | throw s!"the exported constant {en} is not stored at the private level"
      let some sp := (privLocs[i]?).bind (constSkel r) | throw "malformed private constant"
      let samePtrs : Bool := se.type == sp.type && se.levelParams == sp.levelParams
      let hiddenKind : Bool := match se.kind, sp.kind with
        | .ax u, .defn _ _ s => u == (s != "safe")
        | .ax u, .thm .. => !u
        | .ax u, .opaq _ u' => u == u'
        | _, _ => false
      if hiddenKind && samePtrs then expo := expo.set! i .hidden
      else
        -- the fallback: decode the exported constant
        let some e := constSpec r c | throw "malformed exported constant"
        match expoOf cs[i]! e with
        | some x => expo := expo.set! i x
        | none => throw s!"the exported view of {en} is not a refinement of its private \
            constant ({kindWord cs[i]!.kind} / {kindWord e.kind})"
  return expo

/-! ## The whole module -/

/-- **One module, read in full**: its flag and imports, its constants at
the private level and each one's exported level, and the exported part's
constants as `parseExported` read them. -/
structure ModRead where
  name : Name
  isModule : Bool
  imports : Array ImportRec
  constants : Array (CEntryF Name Expr)
  expo : Array Expo
  exported : Array (CEntryF Name Expr)

/-- **A classic module, read in full**: its one part. -/
def classicModule (m : Name) (er : ModDecoded) : ModRead :=
  { name := m, isModule := false, imports := er.imports, constants := er.constants,
    expo := er.constants.map fun _ => .same, exported := er.constants }

/-- **A module of the module system, read in full**: `er` its exported
part's read (`parseExported`), `ex`, `s`, `p` its three files. -/
def parseModule (m : Name) (er : ModDecoded) (ex s p : Part) : Except CheckError ModRead := do
  let bad (what : String) : CheckError := .internal s!"module {m}: {what}"
  let r ← Region.ofParts #[ex, s, p]
  let check (part : String) (root : UInt64) : Except CheckError ModDecoded := do
    let d ← parseFullE m part r root
    unless d.isModule do
      .error (bad s!"the {part} part is not of a module of the module system, the \
        exported part is")
    unless d.imports == er.imports do
      .error (bad s!"the {part} part's imports are not the exported part's")
    pure d
  let _ ← check "server" s.root
  let d ← check "private" p.root
  match expoOfParts r p.root ex.root d.constants, expoOfParts r p.root s.root d.constants with
  | .ok expo, .ok _ =>
    pure { name := m, isModule := true, imports := er.imports, constants := d.constants, expo,
           exported := er.constants }
  | .error msg, _ => .error (bad s!"the exported part: {msg}")
  | _, .error msg => .error (bad s!"the server part: {msg}")

end ConLeche.Frontend.Olean
