module

public import ConLeche.Driver.CheckMain

/-!
# The import graph of a closure, checked (task #467)

`con-leche --check-graph --search-path=DIRS -- ROOT…` reads the header of every module of the
roots' import closure (`moduleImports`: the imports at the start of each exported `.olean`, the
read every reader of the module makes) and checks that the graph is **acyclic** and that every
import resolves.  No numbering is an input: the check computes one (Kahn's worklist over the
closure, `kahn`) and validates it (`verdict`): every module of the closure has a rank, no two the
same, and every import edge goes to a smaller rank.  What is proved is the validation, not the
algorithm (`ConLeche/Verify/Driver/Graph.lean`, `checkGraphG_ok`).

**The closure and its edges** are every import of every kind: public, private, `import all`,
`meta`.  A module's per-module check (the worker) may take a completion's copy from a module only
a private import reaches, so the numbering the modular theorem is stated at must order those
edges too; and Lean's own import refuses a cycle through any of them.

**Exit codes**: 0 the graph is acyclic; 1 an import cycle (the cycle is printed), or a module of
the closure that is on no directory of the search path; 3 an unreadable or malformed header, or
a module's files laid out as `findModule` refuses; 2 where the header read declines (a file of
another toolchain).
-/

@[expose] public section

namespace ConLeche.Driver.Graph

open ConLeche ConLeche.Frontend.Olean

/-- A module of the closure: its name and its imports, off its header. -/
abbrev Node := Name × Array ImportRec

/-! ## The closure -/

/-- Whether no directory of the search path holds any of `m`'s files (an exception while
looking is not that). -/
def missingOn {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) : μ Bool :=
  tryCatchThe IO.Error (do return (← locateHits sp m).isEmpty) fun _ => pure false

/-- **A module's imports**, read off its header (`moduleImports`); a module on no directory of
the search path is invalid input (an import that does not resolve). -/
def hdrOf {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) :
    μ (Except CheckError Node) := do
  match ← moduleImports sp m with
  | .ok imps => pure (.ok (m, imps))
  | .error e =>
    if ← missingOn sp m then
      pure (.error (.invalid s!"module {m}: no .olean on the search path"))
    else pure (.error e)

/-- One level of the walk: the modules read, in order, and the imports not yet seen, the next
level. -/
def expand (seen : Std.HashSet Name) (out : Array Node) (next : Array Name) :
    List Node → Std.HashSet Name × Array Node × Array Name
  | [] => (seen, out, next)
  | (m, imps) :: rest =>
    let (seen, next) := imps.foldl (fun (s, nx) i =>
      if s.contains i.module then (s, nx) else (s.insert i.module, nx.push i.module)) (seen, next)
    expand seen (out.push (m, imps)) next rest

/-- **The closure, level by level**: the headers of a level read on `jobs` threads
(`CheckerIO.parMapExcept`, the sequential map in meaning), the modules first met there the next
level.  `fuel` bounds the levels, an internal error when spent. -/
def closureLevels {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (jobs : Nat) :
    Nat → List Name → Std.HashSet Name → Array Node → μ (Except CheckError (Array Node))
  | _, [], _, out => pure (.ok out)
  | 0, _ :: _, _, _ => pure (.error (.internal "the closure's walk ran out of steps"))
  | fuel + 1, lvl@(_ :: _), seen, out => do
    match ← CheckerIO.parMapExcept jobs (hdrOf sp) lvl with
    | .error e => pure (.error e)
    | .ok rs =>
      let (seen, out, next) := expand seen out #[] rs
      closureLevels sp jobs fuel next.toList seen out

/-- The walk's level bound: far beyond any closure. -/
def levelFuel : Nat := 1 <<< 40

/-- The roots, each once, in order, and the set of them. -/
def dedup (xs : List Name) : List Name × Std.HashSet Name :=
  let (s, acc) := xs.foldl (fun (s, acc) x =>
    if s.contains x then (s, acc) else (s.insert x, acc.push x)) (({} : Std.HashSet Name), #[])
  (acc.toList, s)

/-! ## The order -/

/-- Each module's position in the closure. -/
def indexOf (C : Array Node) : Std.HashMap Name Nat := Id.run do
  let mut idx : Std.HashMap Name Nat := {}
  for h : k in [0:C.size] do
    idx := idx.insert C[k].1 k
  return idx

/-- Each module's imports, by position (an import outside the closure left out: the walk puts
every import in, and the validation checks it). -/
def depsOf (idx : Std.HashMap Name Nat) (C : Array Node) : Array (Array Nat) :=
  C.map fun e => e.2.filterMap fun i => idx[i.module]?

/-- **Kahn's worklist**: the positions in an order where each comes after everything it
imports; on a cyclic graph, the part of it that waits on no cycle.  `wait` is each module's
number of import edges not yet released (an import listed twice is two edges, and releases
twice). -/
def kahn (deps : Array (Array Nat)) : Array Nat := Id.run do
  let n := deps.size
  let mut users : Array (Array Nat) := Array.replicate n #[]
  for h : k in [0:n] do
    for j in deps[k] do
      users := users.modify j (·.push k)
  let mut wait : Array Nat := deps.map (·.size)
  let mut q : Array Nat := #[]
  for h : k in [0:n] do
    if deps[k].isEmpty then q := q.push k
  let mut i := 0
  for _ in [0:n] do
    if h : i < q.size then
      let x := q[i]
      for y in users[x]! do
        let w := wait[y]!
        wait := wait.set! y (w - 1)
        if w == 1 then q := q.push y
      i := i + 1
    else break
  return q

/-- **The ranks**: a position's place in the order, `none` for a position the order lacks. -/
def ranksOf (n : Nat) (ord : Array Nat) : Array (Option Nat) := Id.run do
  let mut rank : Array (Option Nat) := Array.replicate n none
  for h : t in [0:ord.size] do
    rank := rank.set! ord[t] (some t)
  return rank

/-- A module's rank, by name. -/
def rankOf (idx : Std.HashMap Name Nat) (rank : Array (Option Nat)) (m : Name) : Option Nat :=
  (idx[m]?).bind fun k => (rank[k]?).join

/-- **A cycle**, given the order (the part of the graph waiting on no cycle): from the first
module outside it, an import outside it, until a module repeats; the modules from its first
visit on, in import order.  Every module outside the order has an import outside it (else Kahn's
worklist would have released it), so the walk ends on a repeat. -/
def cycleOf (deps : Array (Array Nat)) (ord : Array Nat) : Option (List Nat) := Id.run do
  let n := deps.size
  let mut done : Array Bool := Array.replicate n false
  for k in ord do
    done := done.set! k true
  let some s := (List.range n).find? (!done[·]!) | return none
  let mut path : Array Nat := #[]
  let mut at? : Array (Option Nat) := Array.replicate n none
  let mut x := s
  for _ in [0:n + 1] do
    if let some p := at?[x]! then
      return some (path.extract p path.size).toList
    at? := at?.set! x (some path.size)
    path := path.push x
    match deps[x]!.find? (!done[·]!) with
    | some y => x := y
    | none => return some path.toList
  return some path.toList

/-! ## The validation -/

/-- The closure's names. -/
def namesOf (C : List Node) : Std.HashSet Name :=
  C.foldl (fun s e => s.insert e.1) {}

/-- `a` and `b` are ranks, `a` below `b`. -/
def rankLt : Option Nat → Option Nat → Bool
  | some a, some b => a < b
  | _, _ => false

/-- An import of `m` goes to a module of the closure of a smaller rank. -/
def edgeOk (pos : Std.HashSet Name) (rk : Name → Option Nat) (m : Name) (i : ImportRec) : Bool :=
  pos.contains i.module && rankLt (rk i.module) (rk m)

/-- **The verdict on a closure and a numbering**: `none` when every root is in the closure,
every module of it has a rank, no two the same, and every import edge goes to a module of the
closure of a smaller rank; else the first thing wrong. -/
def verdict (roots : List Name) (C : List Node) (rk : Name → Option Nat) : Option CheckError :=
  let pos := namesOf C
  if let some r := roots.find? (!pos.contains ·) then
    some (.internal s!"the root {r} is not in the closure")
  else if let some (m, _) := C.find? (fun e => (rk e.1).isNone) then
    some (.internal s!"the module {m} of the closure has no rank")
  else if !distinctGo (C.map fun e => rk e.1) {} then
    some (.internal "two modules of the closure have the same rank")
  else if let some (m, imps) := C.find? (fun e => !e.2.all (edgeOk pos rk e.1)) then
    let i := (imps.find? (!edgeOk pos rk m ·)).map (·.module)
    some (.invalid s!"the import {m} → {i.getD .anonymous} does not go to a smaller rank")
  else none

/-! ## The check -/

/-- A cycle's message: its modules in import order, the first repeated at the end. -/
def cycleMsg (C : Array Node) (cyc : List Nat) : String :=
  let names := cyc.map fun k => toString (C[k]?.map (·.1) |>.getD .anonymous)
  " → ".intercalate (names ++ names.take 1)

/-- **The graph check**, generic in the IO class: walk the closure's headers, compute an order,
validate it; the exit code. -/
def checkGraphG {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (roots : List Name)
    (jobs : Nat) : μ UInt8 := do
  let (lvl, seen) := dedup roots
  match ← closureLevels sp jobs levelFuel lvl seen #[] with
  | .error e =>
    diagLine s!"con-leche: graph: {e}"
    return e.exitCode
  | .ok C =>
    let idx := indexOf C
    let deps := depsOf idx C
    let ord := kahn deps
    if let some cyc := cycleOf deps ord then
      let e : CheckError := .invalid s!"import cycle: {cycleMsg C cyc}"
      diagLine s!"con-leche: graph: {e}"
      return e.exitCode
    match verdict roots C.toList (rankOf idx (ranksOf C.size ord)) with
    | some e =>
      diagLine s!"con-leche: graph: {e}"
      return e.exitCode
    | none =>
      outLine s!"con-leche: graph: acyclic: {C.size} modules, \
        {C.foldl (· + ·.2.size) 0} import edges"
      return 0

end ConLeche.Driver.Graph
