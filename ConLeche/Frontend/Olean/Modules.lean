module

public import ConLeche.Frontend.Olean.Load
public import ConLeche.Frontend.Prepare

@[expose] public section

/-!
# Reading `.olean` files module by module (task #370)

`con-leche --olean --modular M₁ … Mₙ` checks every module of the import
closure of the `Mᵢ` on its own, against the context Lean elaborated it
in.  This file reads what that needs, per module, with the decoder of
`ConLeche/Frontend/Olean/{Region,Decode}.lean` and the emission walk of
`Load.lean`:

* **the imports with Lean's flags** (`import all`, `public`, `meta`:
  the `Import` structure's three scalar bytes, in declaration order);
* **the private level**: the module's constants as the `.olean.private`
  part stores them (a module outside the module system has only its
  `.olean`, which stores everything);
* **the exported level**, per constant (`Expo`): the `.olean` part of a
  module of the module system, compared constant by constant with the
  private one — the same constant, the same constant with its value
  hidden (an axiom of the same name, level parameters and type, where
  the private one is a definition, theorem or opaque constant), or
  absent.  Anything else is an exported view that is not a refinement
  of the private one, and the module is rejected (`.invalid`, exit 1).
  A constant the private part shares with the exported one (the same
  object: the private part points into the exported part) is compared
  by address, without decoding it twice;
* **the module's records in a dependency order** (`moduleDecls`):
  lean4export's `dumpConstant` walk (`emitLoop`) restricted to the
  module's own constants — an imported constant is outside the walk —
  with every own constant a root (the non-internal names first, in the
  module's order, then the internal ones, so that an internal constant
  another module uses is installed even when nothing of its own module
  mentions it), built into `Declaration`s by the stream reader's
  builder; then `prepareModule`: the module's own copies of the built-in
  prelude's declarations moved to its front and the pinned `Nat`
  operations' ground hoisted, as `preparePrelude` does for a whole
  stream, but nothing synthesised — a module's context is what Lean
  elaborated it in, and a prelude declaration the module does not
  store is not its own.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

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
  deriving Inhabited, Repr

/-- The root `ModuleData`'s imports with their flags. -/
def importsAt (r : @& Region) (v : UInt64) : DM (Array ImportRec) := do
  let x ← liftE (r.obj v)
  liftE (x.expect 0 5 "ModuleData")
  let imps ← liftE (r.array (← liftE (x.field 0)))
  imps.mapM fun i => do
    let y ← liftE (r.obj i)
    liftE (y.expect 0 1 "Import")
    let m ← nameAt r (← liftE (y.field 0)) shallowFuel
    pure { module := m, importAll := ← liftE (boolAt y 0), isExported := ← liftE (boolAt y 1),
           isMeta := ← liftE (boolAt y 2) }

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
def CEntry.same (a b : CEntry) : Bool :=
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
def expoOf (priv ex : CEntry) : Option Expo :=
  if priv.same ex then some .same
  else if priv.name == ex.name && priv.levelParams == ex.levelParams && priv.type == ex.type then
    match priv.kind, ex.kind with
    | .defn .., .ax _ | .thm .., .ax _ | .opaq .., .ax _ => some .hidden
    | _, _ => none
  else none

/-! ## One module -/

instance : Inhabited CEntry := ⟨{ name := .anonymous, levelParams := [], type := .bvar 0, kind := .ax false }⟩

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

/-- **Read one module**: the private level as `loadModule` reads it, the
imports with their flags, and for a module of the module system the
exported part's constants compared with the private ones. -/
def readModule (sp : SearchPath) (m : Name) (ds : DS) :
    IO (Except CheckError (ModRead × DS)) := do
  let some dir ← findModule sp m
    | return .error (.internal s!"module {m}: no .olean on the search path")
  let ex ← match ← readPart (modFile dir m "olean") with
    | .ok p => pure p
    | .error e => return .error e
  let r0 := Region.single ex
  let isModule ← match (do
      let x ← r0.obj ex.root
      x.expect 0 5 "ModuleData"
      boolAt x 0 : Except String Bool) with
    | .ok b => pure b
    | .error e => return .error (.internal s!"module {m}: {e}")
  let (r, root) ← if isModule then do
      let sv ← readPart (modFile dir m "olean.server")
      let pv ← readPart (modFile dir m "olean.private")
      match sv, pv with
      | .ok s, .ok p =>
        match Region.ofParts #[ex, s, p] with
        | .ok r => pure (r, p.root)
        | .error e => return .error e
      | .error e, _ | _, .error e => return .error e
    else pure (r0, ex.root)
  let ds := ds.fresh r.words
  let act : DM (ModRead × Option String) := do
    let info ← moduleAt r root
    let imports ← importsAt r root
    let cs ← info.constants.mapM (constAt r)
    let cs := cs.map fun c => { c with uses := constsOf c.deps }
    if !isModule then
      return (⟨m, false, imports, cs, cs.map fun _ => .same⟩, none)
    -- the exported part: its constants by name, compared with the
    -- private ones (by address first)
    let einfo ← moduleAt r ex.root
    let privIdx : Std.HashMap Name Nat :=
      cs.size.fold (init := {}) fun i _ acc => acc.insert cs[i].name i
    let privAddr : Std.HashMap UInt64 Nat :=
      info.constants.size.fold (init := {}) fun i _ acc => acc.insert info.constants[i] i
    let mut expo : Array Expo := cs.map fun _ => .absent
    for a in einfo.constants do
      if let some i := privAddr[a]? then
        -- the same object as private constant `i`
        expo := expo.set! i .same
      else
        let e ← constAt r a
        match privIdx[e.name]? with
        | none => return (default, some s!"the exported constant {e.name} is not stored at the private level")
        | some i =>
          match expoOf cs[i]! e with
          | some x => expo := expo.set! i x
          | none => return (default, some s!"the exported view of {e.name} is not a refinement of its private constant ({kindWord cs[i]!.kind} / {kindWord e.kind})")
    pure (⟨m, true, imports, cs, expo⟩, none)
  match act.run ds with
  | .ok ((l, none), ds) => pure (.ok (l, ds))
  | .ok ((_, some msg), _) => pure (.error (.invalid s!"module {m}: {msg}"))
  | .error e => pure (.error (.internal s!"module {m}: {e}"))

/-- The modules read one after the other, the hash-cons tables
threaded through. -/
partial def readSerial (sp : SearchPath) (ms : List Name) (ds : DS) (out : Array ModRead) :
    IO (Except CheckError (Array ModRead)) := do
  match ms with
  | [] => pure (.ok out)
  | m :: rest =>
    match ← readModule sp m ds with
    | .error e => pure (.error e)
    | .ok (l, ds) => readSerial sp rest ds (out.push l)

/-- **The closure, read module by module**, in Lean's module order,
on `jobs` workers (round-robin shares, as `loadClosure`). -/
def readClosure (sp : SearchPath) (roots : Array Name) (jobs : Nat := 1) :
    IO (Except CheckError (Array ModRead)) := do
  match ← closureOrder sp roots with
  | .error e => pure (.error e)
  | .ok order =>
    if jobs ≤ 1 then readSerial sp order.toList {} #[]
    else
      let w := min jobs order.size
      let shares := (List.range w).map fun k =>
        (List.range order.size).filter (· % w == k) |>.filterMap (order[·]?)
      let tasks ← shares.toArray.mapM fun ms =>
        IO.asTask (prio := .dedicated) (readSerial sp ms {} #[])
      let mut parts : Array (Array ModRead) := #[]
      for t in tasks do
        match ← IO.wait t with
        | .ok (.ok ls) => parts := parts.push ls
        | .ok (.error e) => return .error e
        | .error ioe => return .error (.internal s!"reading the oleans: {ioe}")
      let out := (List.range order.size).filterMap fun i =>
        (parts[i % w]?).bind (·[i / w]?)
      pure (.ok out.toArray)

/-! ## One module's records -/

/-- **A module's own record stream**: lean4export's walk over the
module's own constants, every own constant a root (non-internal names
first), and the records built by the stream reader's builder. -/
def moduleDecls (cs : Array CEntry) : Except (CheckError × Nat) (Array Declaration) :=
  let mg : Merged := cs.foldl (fun mg c =>
    let { map, order } := mg
    { map := map.insert c.name c, order := order.push c.name }) {}
  let recMap := mg.order.foldl (fun (m : Std.HashMap Name (Array Name)) n =>
    match (mg.map[n]?).map CEntry.kind with
    | some (CKind.recur all ..) =>
      all.foldl (fun m i => m.alter i fun
        | none => some #[n]
        | some a => some (if a.contains n then a else a.push n)) m
    | _ => m) {}
  let roots := mg.order.filter (!Name.isInternal ·) ++ mg.order.filter (Name.isInternal ·)
  declsOf (emitLoop mg recMap (roots.toList.map .visit) {})

/-- The module's own copies of the prelude's declarations, moved to the
front in the prelude's order; nothing synthesised. -/
def frontOwn (acc : Array Declaration) :
    List Declaration → Array Declaration → Array Declaration × Array Declaration
  | [], ds => (acc, ds)
  | p :: ps, ds =>
    match pick (preludeKey p) ds with
    | (some d, ds') => frontOwn (acc.push d) ps ds'
    | (none, ds') => frontOwn acc ps ds'

/-- **A module's records, prepared**: its own prelude declarations
first, the pinned `Nat` operations' ground hoisted. -/
def prepareModule (pre : PreludeIx) (ds : Array Declaration) : Array Declaration :=
  let (front, rest) := frontOwn #[] pre.decls.toList ds
  (hoistNatOpGround (front ++ rest)).1

end ConLeche.Frontend.Olean
