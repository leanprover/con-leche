module

public import ConLeche.Frontend.Olean.Spec
public import ConLeche.Frontend.ExportC
public import Std.Data.HashSet.Basic

@[expose] public section

/-!
# Reading `.olean` files: the import closure as one record stream (task #369)

`con-leche --olean M₁ … Mₙ` checks the modules `Mᵢ` and everything they
import, read from their `.olean` files.  This file turns the import
closure into the same `Declaration` records the lean4export reader
produces (`ConLeche/Frontend/ExportC.lean`), so that everything after
the parse — the prelude preparation, the install and the check, and the
main theorem about them — is the stream path's, unchanged.

**What is merged is what lean4export exports**: the closure loaded at
the PRIVATE level (each module-system module's `.olean.private`, whose
`ModuleData` holds the full constants — theorems with their proofs,
definitions with their bodies; a module outside the module system has
only its `.olean`), merged as Lean's own `finalizeImport` merges them,
and exported in lean4export's order:

1. **Loading** (`loadClosure`): the modules in import order, each
   module after its imports (a depth-first post-order from the roots, as
   `importModules` builds its module array), each module's files read,
   validated and decoded once by the decoder the caller passes — the
   driver passes the specification `decodeModuleSpec`
   (`ConLeche/Frontend/Olean/Spec.lean`), which the compiler replaces by
   the fast decoder.
2. **Merging** (`mergeEntry`): a name stored by two modules is kept once,
   by `subsumesInfo`'s rule (`Lean/Environment.lean`): the later copy
   replaces the earlier one when it subsumes it, the earlier one stays
   when it subsumes the later, and otherwise the closure is invalid —
   Lean's own import refuses it ("environment already contains").
3. **Emitting** (`emitAll`): lean4export's `dumpConstant` walk — every
   constant whose name is not internal is a root, every constant is
   emitted after the constants its type and value mention, an inductive
   block as one record with its constructors and recursors, the quotient
   package as its four records after `Eq`, unsafe and partial constants
   left out.  The walk is iterative (`Work` items on an explicit stack).
4. **Building** (`declsOf`): each emitted record becomes a `Declaration`
   through the stream reader's own builder `declOfF`, so the validation
   of inductive records (`validateIndF`) and every decline are the
   stream path's.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## Files -/

/-- The search path: the directories holding `.olean` trees, as
`LEAN_PATH` lists them. -/
abbrev SearchPath := List System.FilePath

/-- The file a module's level is stored in. -/
def modFile (dir : System.FilePath) (m : Name) (ext : String) : System.FilePath :=
  let rec comps : Name → List String
    | .anonymous => []
    | .str p s => comps p ++ [s]
    | .num p n => comps p ++ [toString n]
  (comps m).foldl (· / ·) dir |>.addExtension ext

/-- The first search-path directory holding the module's `.olean`. -/
def findModule (sp : SearchPath) (m : Name) : IO (Option System.FilePath) := do
  for d in sp do
    if ← (modFile d m "olean").pathExists then return some d
  return none

/-- Read and validate one file. -/
def readPart (p : System.FilePath) : IO (Except CheckError Part) := do
  let b ← IO.FS.readBinFile p
  pure (Part.ofBytes p.toString b)

/-! ## Dependencies -/

/-- A name from its components. -/
def mkN (cs : List String) : Name := cs.foldl .str .anonymous

/-- The DAG walk of `constsOf`.  A name is added by `addN`, written out
at each leaf so that no pair is allocated per node. -/
partial def constsGo (stack : List Expr) (seen : Std.HashSet Expr) (seenN : Std.HashSet Name)
    (out : Array Name) : Array Name :=
  match stack with
  | [] => out
  | e :: rest =>
    -- leaves need no visited entry: only compound nodes are shared work
    match e with
    | .const n _ =>
      if seenN.contains n then constsGo rest seen seenN out
      else constsGo rest seen (seenN.insert n) (out.push n)
    | .lit (.natVal _) =>
      let n := mkN ["Nat"]
      if seenN.contains n then constsGo rest seen seenN out
      else constsGo rest seen (seenN.insert n) (out.push n)
    | .lit (.strVal _) =>
      let n₁ := mkN ["Char", "ofNat"]
      let n₂ := mkN ["String", "ofList"]
      if seenN.contains n₁ && seenN.contains n₂ then constsGo rest seen seenN out
      else
        let (seenN, out) := if seenN.contains n₁ then (seenN, out)
          else (seenN.insert n₁, out.push n₁)
        let (seenN, out) := if seenN.contains n₂ then (seenN, out)
          else (seenN.insert n₂, out.push n₂)
        constsGo rest seen seenN out
    | .bvar _ | .sort _ => constsGo rest seen seenN out
    | _ =>
      if seen.contains e then constsGo rest seen seenN out
      else
        let seen := seen.insert e
        match e with
        | .app f a => constsGo (f :: a :: rest) seen seenN out
        | .lam t b | .forallE t b => constsGo (t :: b :: rest) seen seenN out
        | .letE t v b => constsGo (t :: v :: b :: rest) seen seenN out
        | .proj _ _ x => constsGo (x :: rest) seen seenN out
        | .fvar _ t => constsGo (t :: rest) seen seenN out
        | _ => constsGo rest seen seenN out

/-- **The constants an expression mentions**, in first-visit order, and
the literal dependencies lean4export adds (`dumpNatDeps`,
`dumpStrDeps`): `Nat` for a numeral, `Char.ofNat` and `String.ofList`
for a string.  An iterative walk over the DAG, each node once. -/
def constsOf (es : List Expr) : Array Name :=
  constsGo es (Std.HashSet.emptyWithCapacity 256) (Std.HashSet.emptyWithCapacity 64) #[]

/-! ## One module -/

/-- **One stored constant**, as the merge and the emitter need it: the
decoded `ConstantInfo` and the constants its type and values mention,
in first-visit order (`constsOf`, computed by the module's decode
worker). -/
structure CEntry extends CEntryF Name Expr where
  uses : Array Name := #[]

/-- lean4export's filter (`dumpConstant`): unsafe and partial constants
are not exported. -/
def CEntry.skipped (c : CEntry) : Bool :=
  match c.kind with
  | .ax u | .opaq _ u | .induct _ _ _ _ _ _ u _ | .ctor _ _ _ _ u | .recur _ _ _ _ _ _ _ u => u
  | .defn _ _ s => s != "safe"
  | .thm .. | .quot _ => false

/-- The constants a record depends on. -/
def CEntry.deps (c : CEntry) : List Expr :=
  match c.kind with
  | .defn v .. | .thm v _ | .opaq v _ => [c.type, v]
  | .recur _ _ _ _ _ rules _ _ => c.type :: rules.map (·.2.2)
  | _ => [c.type]

/-- A module decoder: the module stored in a region from its root
pointer, with its constants or its imports alone
(`decodeModuleSpec`). -/
abbrev Decoder := Region → UInt64 → Bool → Option ModDecoded

/-- A loaded module: its imports and its decoded constants. -/
structure Loaded where
  name : Name
  imports : Array Name
  constants : Array CEntry

/-- The module's files do not decode. -/
def undecodable (m : Name) : CheckError :=
  .internal s!"module {m}: malformed .olean data (an object of the wrong shape, or a \
    pointer that does not point below its object)"

/-- **A part's name table agrees with its constants** (task #383):
`ModuleData.constNames`, the keys Lean's `finalizeImport` stores the
constants under (it zips the two arrays), has as many entries as
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

/-- The malformed name table's error. -/
def badConstNames (m : Name) (part : String) : CheckError :=
  .internal s!"module {m}: the {part} part's name table (constNames) does not list its \
    constants' names, each once"

/-! ## The imports -/

/-- One `import` of a module, with Lean's flags (`Lean.Import`). -/
structure ImportRec where
  module : Name
  /-- `import all` -/
  importAll : Bool
  /-- `public import` (re-exported to the importer's importers) -/
  isExported : Bool
  /-- `meta import` (IR only; irrelevant to the kernel) -/
  isMeta : Bool
  deriving Inhabited, Repr, BEq

/-- The root `ModuleData`'s imports with their flags (the `Import`
structure: the module's name, then three one-byte scalars in declaration
order). -/
def importsAt (r : Region) (root : UInt64) : Option (Array ImportRec) := do
  let g ← r.loc root
  unless r.isCtor g 0 5 do none
  let imps ← r.objArray g (r.fld g 0)
  imps.mapM fun i => do
    unless r.isCtor i 0 1 do none
    let m ← nameP r (← r.ptrFld i 0)
    pure { module := m, importAll := ← r.bool i 0, isExported := ← r.bool i 1,
           isMeta := ← r.bool i 2 }

/-! ## The exported level -/

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

/-! ## One module -/

instance : Inhabited CEntry :=
  ⟨{ name := .anonymous, levelParams := [], type := .bvar 0, kind := .ax false }⟩


/-- **One module, read**: its imports with their flags, whether it is a
module of the module system, its private-level constants and each
one's exported level. -/
structure ModRead where
  name : Name
  isModule : Bool
  imports : Array ImportRec
  constants : Array CEntry
  expo : Array Expo
  deriving Inhabited

/-- **The exported level of a module's private constants**: for each
exported constant, the private constant it stands for — the same object
(the private part points into the exported part), the same skeleton
(names and expressions as pointers), the same constant decoded, or an
axiom of the same name, level parameters and type (by pointer, else
decoded) where the private one is a definition, theorem or opaque
constant.  `none` with the reason: an exported view that is not a
refinement of the private one. -/
def expoOfParts (r : Region) (privRoot expRoot : UInt64) (cs : Array CEntry) :
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
        match expoOf cs[i]!.toCEntryF e with
        | some x => expo := expo.set! i x
        | none => throw s!"the exported view of {en} is not a refinement of its private \
            constant ({kindWord cs[i]!.kind} / {kindWord e.kind})"
  return expo

/-- **Read one module**: its imports with their flags, its private-level
constants, and for a module of the module system each one's exported
level — with every check that the parts' redundant data agree (task
#383; a mismatch is malformed input, `.internal`, exit 3):

* every part's name table lists its constants, each name once
  (`constNamesOk`: the exported, server and private part);
* the server and private parts' headers are the exported part's: a
  module of the module system, the same imports with the same flags
  (closure discovery reads the exported part's, the module's check the
  private part's);
* every constant of the exported part, and of the server part, is the
  private part's constant of its name or that constant with its value
  hidden (`expoOfParts`). -/
def readModule (dec : Decoder) (sp : SearchPath) (m : Name) : IO (Except CheckError ModRead) := do
  let some dir ← findModule sp m
    | return .error (.internal s!"module {m}: no .olean on the search path")
  let ex ← match ← readPart (modFile dir m "olean") with
    | .ok p => pure p
    | .error e => return .error e
  let bad (what : String) : CheckError := .internal s!"module {m}: {what}"
  let rE := Region.single ex
  let some sk := moduleSkel rE ex.root | return .error (undecodable m)
  let some impE := importsAt rE ex.root | return .error (undecodable m)
  -- a module imported twice (`public import A` beside `import all A`) is
  -- Lean's own case, merged by its level fixpoint (`importModulesCore`,
  -- here `levelsOf`); a module importing itself is a cycle, which the
  -- closure's walk rejects before any module is read (`closureGo`)
  unless constNamesOk rE ex.root do return .error (badConstNames m "exported")
  let mkCs (d : ModDecoded) : Array CEntry := d.constants.map fun c =>
    let c : CEntry := { toCEntryF := c }
    { c with uses := constsOf c.deps }
  if !sk.isModule then
    let some d := dec rE ex.root true | return .error (undecodable m)
    let cs := mkCs d
    return .ok ⟨m, false, impE, cs, cs.map fun _ => .same⟩
  let sv ← readPart (modFile dir m "olean.server")
  let pv ← readPart (modFile dir m "olean.private")
  let (s, p) ← match sv, pv with
    | .ok s, .ok p => pure (s, p)
    | .error e, _ | _, .error e => return .error e
  let r ← match Region.ofParts #[ex, s, p] with
    | .ok r => pure r
    | .error e => return .error e
  for (part, root) in [("server", s.root), ("private", p.root)] do
    let some skP := moduleSkel r root | return .error (undecodable m)
    unless skP.isModule do
      return .error (bad s!"the {part} part is not of a module of the module system, the \
        exported part is")
    let some impP := importsAt r root | return .error (undecodable m)
    unless impP == impE do
      return .error (bad s!"the {part} part's imports are not the exported part's")
    unless constNamesOk r root do return .error (badConstNames m part)
  let some d := dec r p.root true | return .error (undecodable m)
  let cs := mkCs d
  match expoOfParts r p.root ex.root cs, expoOfParts r p.root s.root cs with
  | .ok expo, .ok _ => return .ok ⟨m, true, impE, cs, expo⟩
  | .error msg, _ => return .error (bad s!"the exported part: {msg}")
  | _, .error msg => return .error (bad s!"the server part: {msg}")

/-- **Load one module** for the merge: `readModule`'s read, with every
validation of the module's parts, its private-level constants kept. -/
def loadModule (dec : Decoder) (sp : SearchPath) (m : Name) :
    IO (Except CheckError Loaded) := do
  match ← readModule dec sp m with
  | .ok r => pure (.ok ⟨m, r.imports.map (·.module), r.constants⟩)
  | .error e => pure (.error e)

/-! ## The closure -/

/-- A module's imports, read off its exported `.olean` alone. -/
def moduleImports (dec : Decoder) (sp : SearchPath) (m : Name) :
    IO (Except CheckError (Array Name)) := do
  let some dir ← findModule sp m
    | return .error (.internal s!"module {m}: no .olean on the search path")
  match ← readPart (modFile dir m "olean") with
  | .error e => pure (.error e)
  | .ok ex =>
    match dec (Region.single ex) ex.root false with
    | some d => pure (.ok d.imports)
    | none => pure (.error (undecodable m))

/-- **The import closure, in Lean's module order**: a module after
everything it imports, the roots and each module's imports in their
order (a depth-first post-order, as `importModules` builds its module
array).  An explicit stack (`(module, imports expanded?)`) instead of
recursion.  A module whose imports are being expanded (`seen`, not yet
`done`) is on the walk's current path, so an import of it is an import
cycle: malformed input (task #383; Lean's own import refuses a cycle). -/
partial def closureGo (dec : Decoder) (sp : SearchPath) (stack : List (Name × Bool))
    (seen done : Std.HashSet Name) (out : Array Name) : IO (Except CheckError (Array Name)) := do
  match stack with
  | [] => pure (.ok out)
  | (m, true) :: rest => closureGo dec sp rest seen (done.insert m) (out.push m)
  | (m, false) :: rest =>
    if seen.contains m then closureGo dec sp rest seen done out
    else
      match ← moduleImports dec sp m with
      | .error e => pure (.error e)
      | .ok imps =>
        let seen := seen.insert m
        if let some c := imps.find? fun i => seen.contains i && !done.contains i then
          return .error (.internal s!"import cycle: {m} imports {c}")
        let kids := imps.toList.filter (!seen.contains ·) |>.map (·, false)
        closureGo dec sp (kids ++ (m, true) :: rest) seen done out

def closureOrder (dec : Decoder) (sp : SearchPath) (roots : Array Name) :
    IO (Except CheckError (Array Name)) :=
  closureGo dec sp (roots.toList.map (·, false)) {} {} #[]

/-- The modules decoded one after the other. -/
partial def loadSerial (dec : Decoder) (sp : SearchPath) (ms : List Name) (out : Array Loaded) :
    IO (Except CheckError (Array Loaded)) := do
  match ms with
  | [] => pure (.ok out)
  | m :: rest =>
    match ← loadModule dec sp m with
    | .error e => pure (.error e)
    | .ok l => loadSerial dec sp rest (out.push l)

/-- **The closure, loaded**: its modules in Lean's order, decoded.  The
decode of a module needs nothing of any other module, so above one
worker the modules are dealt round-robin to `jobs` workers, each
decoding its share one after the other (so at most `jobs` modules are
in flight, and their memos are the only per-module memory alive), and
the results are put back in module order; the first failure in that
order is the one reported. -/
def loadClosure (dec : Decoder) (sp : SearchPath) (roots : Array Name) (jobs : Nat := 1) :
    IO (Except CheckError (Array Loaded)) := do
  match ← closureOrder dec sp roots with
  | .error e => pure (.error e)
  | .ok order =>
    if jobs ≤ 1 then loadSerial dec sp order.toList #[]
    else
      let w := min jobs order.size
      let shares := (List.range w).map fun k =>
        (List.range order.size).filter (· % w == k) |>.filterMap (order[·]?)
      let tasks ← shares.toArray.mapM fun ms =>
        IO.asTask (prio := .dedicated) (loadSerial dec sp ms #[])
      let mut parts : Array (Array Loaded) := #[]
      for t in tasks do
        match ← IO.wait t with
        | .ok (.ok ls) => parts := parts.push ls
        | .ok (.error e) => return .error e
        | .error ioe => return .error (.internal s!"reading the oleans: {ioe}")
      -- module `i` is element `i / w` of share `i % w`
      let out := (List.range order.size).filterMap fun i =>
        (parts[i % w]?).bind (·[i / w]?)
      pure (.ok out.toArray)

/-! ## The merge -/

/-- Lean's `isPropCheap`: the statement is a telescope over a constant
applied to as many arguments as its own type has binders before a
`Prop` result. -/
def isPropCheap (m : Std.HashMap Name CEntry) (ty : Expr) : Bool :=
  let rec body : Expr → Expr
    | .forallE _ b => body b
    | e => e
  let rec head : Expr → Nat → Option (Name × Nat)
    | .app f _, k => head f (k + 1)
    | .const n _, k => some (n, k)
    | _, _ => none
  let rec drop : Expr → Nat → Option Expr
    | e, 0 => some e
    | .forallE _ b, k + 1 => drop b k
    | _, _ => none
  match head (body ty) 0 with
  | some (n, k) =>
    match m[n]? with
    | some d => match drop d.type k with
      | some (.sort .zero) => true
      | _ => false
    | none => false
  | none => false

/-- `subsumesInfo` (`Lean/Environment.lean`): may `c₁` stand for `c₂`? -/
def subsumes (m : Std.HashMap Name CEntry) (c₁ c₂ : CEntry) : Bool :=
  c₁.name == c₂.name && c₁.type == c₂.type && c₁.levelParams == c₂.levelParams &&
  match c₁.kind, c₂.kind with
  | .thm _ a₁, .thm _ a₂ => a₁ == a₂
  | .thm _ a₁, .ax u₂ => a₁ == [c₂.name] && !u₂
  | .ax u₁, .ax u₂ => u₁ == u₂ && isPropCheap m c₁.type
  | _, _ => false

/-- The merged constants and the order they were first stored in. -/
structure Merged where
  map : Std.HashMap Name CEntry := {}
  order : Array Name := #[]

/-- **Merge one constant** (`finalizeImport`'s rule). -/
def mergeEntry (mg : Merged) (c : CEntry) : Except CheckError Merged :=
  match mg.map[c.name]? with
  | none =>
    let { map, order } := mg
    pure { map := map.insert c.name c, order := order.push c.name }
  | some prev =>
    if subsumes mg.map c prev then
      let { map, order } := mg
      pure { map := map.insert c.name c, order }
    else if subsumes mg.map prev c then pure mg
    else throw (.invalid s!"two modules store different constants named {c.name}")

def mergeAll (ls : Array Loaded) : Except CheckError Merged :=
  ls.foldlM (fun mg l => l.constants.foldlM mergeEntry mg) {}

/-! ## The emission order -/

/-- Lean's `Name.isInternal`: some component starts with `_`. -/
def Name.isInternal : Name → Bool
  | .str p s => s.front == '_' || Name.isInternal p
  | .num p _ => Name.isInternal p
  | .anonymous => false

/-- One step of the emission walk. -/
inductive Work where
  | visit (n : Name)
  | one (c : CEntry)
  | quot (cs : List CEntry)
  | block (tys ctors recs : List CEntry)

/-- The emitter's output: the record stream in the stream reader's
syntax (`DeclRec`, indices into the two tables). -/
structure Emit where
  visited : Std.HashSet Name := {}
  names : Array Name := #[]
  exprs : Array Expr := #[]
  out : Array DeclRec := #[]

/-! The updates below take the field out of the record before changing
it, so that the array or set is changed at reference count 1 (the
`DS.mark` in `ConLeche/Frontend/Olean/Fast.lean` says why). -/

def Emit.name (st : Emit) (n : Name) : Emit × Nat :=
  let { visited, names, exprs, out } := st
  let i := names.size
  ({ visited, names := names.push n, exprs, out }, i)

def Emit.expr (st : Emit) (e : Expr) : Emit × Nat :=
  let { visited, names, exprs, out } := st
  let i := exprs.size
  ({ visited, names, exprs := exprs.push e, out }, i)

def Emit.push (st : Emit) (d : DeclRec) : Emit :=
  let { visited, names, exprs, out } := st
  { visited, names, exprs, out := out.push d }

def Emit.mark (st : Emit) (n : Name) : Emit :=
  let { visited, names, exprs, out } := st
  { visited := visited.insert n, names, exprs, out }

def Emit.cv (st : Emit) (c : CEntry) : Emit × CVRec :=
  let (st, n) := st.name c.name
  let (st, lps) := c.levelParams.foldl (fun (st, acc) p =>
    let (st, i) := st.name p; (st, acc.push i)) (st, #[])
  let (st, t) := st.expr c.type
  (st, ⟨n, lps.toList, t⟩)

def Emit.names' (st : Emit) (ns : List Name) : Emit × List Nat :=
  let (st, acc) := ns.foldl (fun (st, acc) p =>
    let (st, i) := st.name p; (st, acc.push i)) (st, #[])
  (st, acc.toList)

/-- **One constant's record.** -/
def Emit.one (st : Emit) (c : CEntry) : Emit :=
  let (st, cv) := st.cv c
  let (st, d) : Emit × Option DeclRec := match c.kind with
    | .ax u => (st, some (.ax cv u))
    | .defn v h s => let (st, i) := st.expr v; (st, some (.defn cv i h s))
    | .thm v _ => let (st, i) := st.expr v; (st, some (.thm cv i))
    | .opaq v u => let (st, i) := st.expr v; (st, some (.opaq cv i u))
    | .quot k => (st, some (.quot cv k))
    | _ => (st, none)
  match d with
  | some d => st.push d
  | none => st

/-- **An inductive block's record**: lean4export's `inductive` object. -/
def Emit.block (st : Emit) (tys ctors recs : List CEntry) : Emit :=
  let (st, ts) := tys.foldl (fun (st, acc) c =>
    match c.kind with
    | .induct np ni _ cs nn ir iu irf =>
      let (st, cv) := st.cv c
      let (st, cs) := st.names' cs
      (st, acc.push { cv, ctors := cs, isRec := ir, isReflexive := irf, isUnsafe := iu,
                      numIndices := ni, numNested := nn, numParams := np : IndTypeRec })
    | _ => (st, acc)) (st, #[])
  let (st, cts) := ctors.foldl (fun (st, acc) c =>
    match c.kind with
    | .ctor ind cidx np nf iu =>
      let (st, cv) := st.cv c
      let (st, ii) := st.name ind
      (st, acc.push { cv, isUnsafe := iu, numFields := nf, numParams := np,
                      cidx := some cidx, induct := some ii : IndCtorRec })
    | _ => (st, acc)) (st, #[])
  let (st, rs) := recs.foldl (fun (st, acc) c =>
    match c.kind with
    | .recur _ np ni nmo nmi rules k iu =>
      let (st, cv) := st.cv c
      let (st, rr) := rules.foldl (fun (st, acc) (cn, nf, rhs) =>
        let (st, ci) := st.name cn
        let (st, ri) := st.expr rhs
        (st, acc.push ({ ctor := ci, nfields := nf, rhs := ri } : RuleRec))) (st, #[])
      (st, acc.push { cv, isUnsafe := iu, k, numIndices := ni, numMinors := nmi,
                      numMotives := nmo, numParams := np, rules := rr.toList : IndRecRec })
    | _ => (st, acc)) (st, #[])
  st.push (.ind ts.toList cts.toList rs.toList)

/-- **The emission walk** (lean4export's `dumpConstant`, iterative):
`visit n` emits `n`'s record after its dependencies. -/
partial def emitLoop (mg : Merged) (recMap : Std.HashMap Name (Array Name))
    (stack : List Work) (st : Emit) : Emit :=
  match stack with
  | [] => st
  | .one c :: rest => emitLoop mg recMap rest (st.one c)
  | .quot cs :: rest => emitLoop mg recMap rest (cs.foldl Emit.one st)
  | .block ts cs rs :: rest => emitLoop mg recMap rest (st.block ts cs rs)
  | .visit n :: rest =>
    if st.visited.contains n then emitLoop mg recMap rest st else
    match mg.map[n]? with
    | none => emitLoop mg recMap rest st
    | some c =>
      if c.skipped then emitLoop mg recMap rest st else
      let st := st.mark n
      let visits (cs : List CEntry) : List Work :=
        cs.flatMap fun c => c.uses.toList.map Work.visit
      match c.kind with
      | .ax _ | .defn .. | .thm .. | .opaq .. =>
        emitLoop mg recMap (visits [c] ++ Work.one c :: rest) st
      | .quot _ =>
        let qs := [mkN ["Quot"], mkN ["Quot", "mk"], mkN ["Quot", "lift"], mkN ["Quot", "ind"]].filterMap (mg.map[·]?)
        let st := qs.foldl (fun st q => st.mark q.name) st
        emitLoop mg recMap (Work.visit (mkN ["Eq"]) :: Work.quot qs :: rest) st
      | .ctor ind .. => emitLoop mg recMap (Work.visit ind :: rest) st
      | .recur all .. => emitLoop mg recMap (all.map Work.visit ++ rest) st
      | .induct _ _ all _ _ _ _ _ =>
        let tys : List CEntry := all.filterMap (mg.map[·]?)
        let ctors := tys.flatMap fun t => match t.kind with
          | .induct _ _ _ cs _ _ _ _ => cs.filterMap (mg.map[·]?)
          | _ => []
        let recs : List CEntry := ((recMap[n]?).getD #[]).toList.filterMap (mg.map[·]?)
        let st := (tys ++ ctors ++ recs).foldl
          (fun st x => st.mark x.name) st
        emitLoop mg recMap (visits (tys ++ ctors ++ recs) ++ Work.block tys ctors recs :: rest) st

/-- **The record stream of the merged closure.** -/
def emitAll (mg : Merged) : Emit :=
  let recMap := mg.order.foldl (fun (m : Std.HashMap Name (Array Name)) n =>
    match (mg.map[n]?).map (·.kind) with
    | some (CKindF.recur all ..) =>
      all.foldl (fun m i => m.alter i fun
        | none => some #[n]
        | some a => some (if a.contains n then a else a.push n)) m
    | _ => m) {}
  let roots := mg.order.filter (!Name.isInternal ·)
  emitLoop mg recMap (roots.toList.map .visit) {}

/-! ## The coverage of the emission -/

/-- The names an emitted record declares. -/
def Emit.declared (em : Emit) : Std.HashSet Name :=
  let nm (cv : CVRec) (s : Std.HashSet Name) : Std.HashSet Name :=
    match em.names[cv.name]? with
    | some n => s.insert n
    | none => s
  em.out.foldl (init := {}) fun s d => match d with
    | .ax cv _ | .defn cv .. | .thm cv _ | .opaq cv .. | .quot cv _ => nm cv s
    | .ind ts cs rs =>
      let s := ts.foldl (fun s t => nm t.cv s) s
      let s := cs.foldl (fun s c => nm c.cv s) s
      rs.foldl (fun s r => nm r.cv s) s

/-- **Every constant the walk reached is in an emitted record**
(task #383): the walk's `visit` of a constructor or recursor emits its
inductive block, and a block takes its members, constructors and
recursors from the constants by name; a constructor its block does not
list, a recursor no member of its block finds, or a block naming a
member or constructor that is not stored would otherwise be dropped
without a word.  Every constant the walk reached and did not skip
(`CEntry.skipped`) must be declared by an emitted record, and every
inductive type's block members and constructors must be stored, the
members must agree on the block and the constructors name their type,
and a recursor's block must be its first member's; a violation is
malformed input. -/
def coverageOk (mg : Merged) (em : Emit) : Except CheckError Unit := do
  let decl := em.declared
  for n in mg.order do
    if let some c := mg.map[n]? then
      if !c.skipped && em.visited.contains n then
        unless decl.contains n do
          throw (.internal s!"the constant {n} is in no emitted record (a constructor or \
            recursor its inductive block does not have)")
        -- the data that decides which constants form one block (task
        -- #383), which a reader could take from `all`, from `ctors` or
        -- from a constructor's `induct`: they must agree.  The other
        -- fields are the record builder's (`validateIndF`) and the
        -- installer's.
        let bad (what : String) : CheckError := .internal s!"the inductive data of {n}: {what}"
        match c.kind with
        | .induct _ _ all cs _ _ _ _ =>
          unless all.contains n do throw (bad "its block does not list it")
          for x in all do
            match ((mg.map[x]?).map (·.kind) : Option CKind) with
            | some (.induct _ _ all' ..) =>
              unless all' == all do throw (bad s!"its block member {x} names another block")
            | some _ => throw (bad s!"its block member {x} is not an inductive type")
            | none => throw (bad s!"its block member {x} is not stored")
          for x in cs do
            match ((mg.map[x]?).map (·.kind) : Option CKind) with
            | some (.ctor ind ..) =>
              unless ind == n do throw (bad s!"its constructor {x} names another type")
            | some _ => throw (bad s!"its constructor {x} is not a constructor")
            | none => throw (bad s!"its constructor {x} is not stored")
        | .recur all .. =>
          match all.head? with
          | none => throw (bad "the recursor names no block")
          | some t =>
            match ((mg.map[t]?).map (·.kind) : Option CKind) with
            | some (.induct _ _ all' ..) =>
              unless all' == all do throw (bad s!"the recursor's block is not {t}'s")
            | _ => throw (bad s!"the recursor's block member {t} is not a stored inductive type")
        | _ => pure ()

/-! ## The records -/

/-- **The `Declaration` records**, through the stream reader's builder.
A record's verdict (a decline, a contradiction between its fields) is
the stream path's, at the record's position. -/
def declsOf (em : Emit) : Except (CheckError × Nat) (Array Declaration) :=
  let nm (i : Nat) : M Name := match em.names[i]? with
    | some n => pure n | none => throw s!"undefined name index {i}"
  let lv (_ : Nat) : M Level := throw "no level table"
  let ex (i : Nat) : M Expr := match em.exprs[i]? with
    | some e => pure e | none => throw s!"undefined expr index {i}"
  em.out.size.fold (init := .ok #[]) fun k _ acc => do
    let ds ← acc
    match declOfF nm lv ex em.out[k] with
    | .ok (.inl d) => pure (ds.push d)
    | .ok (.inr v) => throw (v.toError, k)
    | .error msg => throw (.internal msg, k)

/-- **The whole read**: load, merge, emit, build. -/
def readOleans (dec : Decoder) (sp : SearchPath) (roots : Array Name) (jobs : Nat := 1) :
    IO (Except (CheckError × Nat) (Array Declaration)) := do
  match ← loadClosure dec sp roots jobs with
  | .error e => pure (.error (e, 0))
  | .ok ls =>
    match mergeAll ls with
    | .error e => pure (.error (e, 0))
    | .ok mg =>
      let em := emitAll mg
      match coverageOk mg em with
      | .error e => pure (.error (e, 0))
      | .ok () => pure (declsOf em)

end ConLeche.Frontend.Olean
