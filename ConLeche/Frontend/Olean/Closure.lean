module

public import ConLeche.Frontend.Olean.Files
public import Std.Data.HashSet.Basic

@[expose] public section

/-!
# Reading `.olean` files: the import closure

The closure's module order from the headers alone (the imports at the start
of each exported file, `readImportsAt`), then every module of it read in
full, in parallel (`CheckerIO.parMapExcept`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## The constants a constant mentions -/

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

/-- **One stored constant**, as the merge and the emitter need it: the
decoded constant and the constants its type and values mention, in
first-visit order (`constsOf`, computed by the module's load). -/
structure CEntry extends CEntryF Name Expr where
  uses : Array Name := #[]

instance : Inhabited CEntry := ⟨{ toCEntryF := default }⟩

/-- `CKindF.skipped` of a stored constant. -/
def CEntry.skipped (c : CEntry) : Bool := c.kind.skipped

/-- The expressions a record depends on. -/
def CEntry.deps (c : CEntry) : List Expr :=
  match c.kind with
  | .defn v .. | .thm v _ | .opaq v _ => [c.type, v]
  | .recur _ _ _ _ _ rules _ _ => c.type :: rules.map (·.2.2)
  | _ => [c.type]

/-- A constant with what it mentions. -/
def CEntry.ofRead (c : CEntryF Name Expr) : CEntry :=
  let c : CEntry := { toCEntryF := c }
  { c with uses := constsOf c.deps }

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

/-- A loaded module: its constants at the private level. -/
structure Loaded where
  name : Name
  constants : Array CEntry

/-- **Load one module** for the merge: its private view, what Lean's own import
outside the module system and lean4export load. -/
def loadModule {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) :
    μ (Except CheckError Loaded) := do
  match ← readView sp m .private with
  | .ok d => pure (.ok ⟨m, d.constants.map CEntry.ofRead⟩)
  | .error e => pure (.error e)

/-- **The closure, loaded**: its modules in Lean's order, decoded.  The
decode of a module needs nothing of any other module, so the modules are
loaded by the parallel map with a stop (`CheckerIO.parMapExcept`: at most
`jobs` modules in flight); the result is the sequential map's, the first
failure in module order the one reported. -/
def loadClosure {μ : Type → Type} [CheckerIO μ] (sp : SearchPath)
    (roots : Array Name) (jobs : Nat := 1) : μ (Except CheckError (Array Loaded)) := do
  match ← closureOrder sp roots with
  | .error e => pure (.error e)
  | .ok order =>
    return (← CheckerIO.parMapExcept jobs (loadModule sp) order.toList).map List.toArray

end ConLeche.Frontend.Olean
