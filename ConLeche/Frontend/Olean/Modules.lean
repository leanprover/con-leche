module

public import ConLeche.Frontend.Olean.Load
public import ConLeche.Frontend.Prepare

@[expose] public section

/-!
# Reading `.olean` files module by module (task #370)

`con-leche --olean --modular M₁ … Mₙ` checks every module of the import
closure of the `Mᵢ` on its own, against a context built by Lean's
loading rules.  Each module is read by `readModule`
(`ConLeche/Frontend/Olean/Load.lean`, shared with the merged read): the
imports with Lean's flags (`import all`, `public`, `meta`), the private
level (the `.olean.private` part's constants; a module outside the
module system has only its `.olean`), and the exported level per
constant (`Expo`: the same constant, the same constant with its value
hidden, or absent), every redundant piece of the parts checked to agree
(task #383; a mismatch is malformed input, exit 3).  This file reads the
closure module by module and builds each module's records:

* **the module's records in a dependency order** (`moduleDecls`):
  lean4export's `dumpConstant` walk (`emitLoop`) restricted to the
  module's own constants — an imported constant is outside the walk —
  with every own constant a root (the non-internal names first, in the
  module's order, then the internal ones, so that an internal constant
  another module uses is installed even when nothing of its own module
  mentions it), every constant it reaches in an emitted record
  (`coverageOk`), built into `Declaration`s by the stream reader's
  builder; then `prepareModule`: the module's own copies of the built-in
  prelude's declarations moved to its front and the pinned `Nat`
  operations' ground hoisted, as `preparePrelude` does for a whole
  stream, but nothing synthesised — a module's context comes from its
  imports, and a prelude declaration the module does not store is not
  its own.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- The modules read one after the other. -/
partial def readSerial (dec : Decoder) (sp : SearchPath) (ms : List Name) (out : Array ModRead) :
    IO (Except CheckError (Array ModRead)) := do
  match ms with
  | [] => pure (.ok out)
  | m :: rest =>
    match ← readModule dec sp m with
    | .error e => pure (.error e)
    | .ok l => readSerial dec sp rest (out.push l)

/-- **The closure, read module by module**, in Lean's module order,
on `jobs` workers (round-robin shares, as `loadClosure`). -/
def readClosure (dec : Decoder) (sp : SearchPath) (roots : Array Name) (jobs : Nat := 1) :
    IO (Except CheckError (Array ModRead)) := do
  match ← closureOrder dec sp roots with
  | .error e => pure (.error e)
  | .ok order =>
    if jobs ≤ 1 then readSerial dec sp order.toList #[]
    else
      let w := min jobs order.size
      let shares := (List.range w).map fun k =>
        (List.range order.size).filter (· % w == k) |>.filterMap (order[·]?)
      let tasks ← shares.toArray.mapM fun ms =>
        IO.asTask (prio := .dedicated) (readSerial dec sp ms #[])
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
def moduleDecls (cs : Array CEntry) : Except (CheckError × Nat) (Array Declaration) := do
  -- no name twice: `readModule` rejects a part that stores one twice
  -- (`constNamesOk`)
  let mg : Merged := cs.foldl (fun mg c =>
    let { map, order } := mg
    { map := map.insert c.name c, order := order.push c.name }) {}
  let recMap := mg.order.foldl (fun (m : Std.HashMap Name (Array Name)) n =>
    match (mg.map[n]?).map (·.kind) with
    | some (CKindF.recur all ..) =>
      all.foldl (fun m i => m.alter i fun
        | none => some #[n]
        | some a => some (if a.contains n then a else a.push n)) m
    | _ => m) {}
  let roots := mg.order.filter (!Name.isInternal ·) ++ mg.order.filter (Name.isInternal ·)
  let em := emitLoop mg recMap (roots.toList.map .visit) {}
  match coverageOk mg em with
  | .error e => throw (e, 0)
  | .ok () => declsOf em

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
