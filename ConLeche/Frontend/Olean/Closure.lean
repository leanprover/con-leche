module

public import ConLeche.Frontend.Olean.Files
public import ConLeche.Frontend.Olean.Lazy
public import ConLeche.Frontend.Olean.Progress

@[expose] public section

/-!
# Reading `.olean` files: the import closure

The closure's module order from the headers alone (the imports at the start
of each exported file, `readImportsAt`), then every module of it loaded
(`ConLeche/Frontend/Olean/Lazy.lean`), in parallel (`CheckerIO.parMapExcept`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## The module order -/

/-- **The import closure, in Lean's module order**: a module after
everything it imports, the roots and each module's imports in their
order (a depth-first post-order, as `importModules` builds its module
array).  An explicit stack (`(module, imports expanded?)`) instead of
recursion.  A module whose imports are being expanded (`seen`, not yet
`done`) is on the walk's current path, so an import of it is an import
cycle: malformed input (task #383; Lean's own import refuses a cycle).
`fuel` bounds the steps (each pops one entry: a module's end, an import of
a module seen, or a module's expansion), an internal error when spent. -/
def closureGo {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) :
    Nat → List (Name × Bool) → Std.HashSet Name → Std.HashSet Name → Array Name →
      μ (Except CheckError (Array Name))
  | _, [], _, _, out => pure (.ok out)
  | 0, _ :: _, _, _, _ => pure (.error (.internal "the import closure's walk ran out of steps"))
  | fuel + 1, (m, true) :: rest, seen, done, out =>
    closureGo sp fuel rest seen (done.insert m) (out.push m)
  | fuel + 1, (m, false) :: rest, seen, done, out =>
    if seen.contains m then closureGo sp fuel rest seen done out
    else do
      match ← moduleImports sp m with
      | .error e => pure (.error e)
      | .ok imps =>
        let imps := imps.map (·.module)
        let seen := seen.insert m
        if let some c := imps.find? fun i => seen.contains i && !done.contains i then
          return .error (.internal s!"import cycle: {m} imports {c}")
        let kids := imps.toList.filter (!seen.contains ·) |>.map (·, false)
        closureGo sp fuel (kids ++ (m, true) :: rest) seen done out

/-- The walk's step bound: far beyond any closure (each module and each
import edge is a step or two). -/
def closureFuel : Nat := 1 <<< 40

def closureOrder {μ : Type → Type} [CheckerIO μ] (sp : SearchPath)
    (roots : Array Name) : μ (Except CheckError (Array Name)) :=
  closureGo sp closureFuel (roots.toList.map (·, false)) {} {} #[]

/-! ## The load -/

/-- **Load one module** for the merge, what it is in the closure's order: its private
view, what Lean's own import outside the module system and lean4export load, its
theorems' values left in the file (`loadView`). -/
def loadModule {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (n : ReadNotes) (total : Nat)
    (x : Name × Nat) : μ (Except CheckError Loaded) := do
  match ← readFiles sp x.1 .private with
  | .ok f =>
    let r := loadView x.2 x.1 f
    CheckerIO.liftIO (n.moduleLoaded total)
    pure r
  | .error e => pure (.error e)

/-- **The closure, loaded**: its modules in Lean's order.  The load of a module needs
nothing of any other module, so the modules are loaded by the parallel map with a stop
(`CheckerIO.parMapExcept`: at most `jobs` modules in flight); the result is the sequential
map's, the first failure in module order the one reported. -/
def loadClosure {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (n : ReadNotes)
    (roots : Array Name) (jobs : Nat := 1) : μ (Except CheckError (Array Loaded)) := do
  CheckerIO.liftIO (n.say "tracing the import closure")
  match ← closureOrder sp roots with
  | .error e => pure (.error e)
  | .ok order =>
    CheckerIO.liftIO (n.say s!"loading {order.size} modules")
    return (← CheckerIO.parMapExcept jobs (loadModule sp n order.size)
      order.toList.zipIdx).map List.toArray

end ConLeche.Frontend.Olean
