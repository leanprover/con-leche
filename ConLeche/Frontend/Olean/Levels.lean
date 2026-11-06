module

public import ConLeche.Frontend.Olean.Closure

@[expose] public section

/-!
# Reading `.olean` files: what Lean loads for a module, from the headers

A module `M` is compiled in the environment Lean's `importModulesCore`
(`Lean/Environment.lean`, v4.35.0) builds from `M`'s header: every module its
imports reach, each at a level.  The levels are the least fixpoint of the rules
of `importModulesCore`'s lattice comment, over two flags per module:

* `importAll`: the module's private part is loaded (Lean's `privateAll` or `all`);
  else its exported part;
* `isExported`: it is in the root's public scope (`public` or `all`).

Every module of a non-`module` root is loaded at its private part (the global
level `.private`); a `module` root's global level is `.exported`.  A module whose
data no rule asks for (a plain `import` of a module loaded without `import all`)
is not loaded at all.  Lean's kernel environment is the merge of the loaded parts,
in its module order (`finalizeImport`'s `moduleData`); the name index of those
parts is `ConLeche/Frontend/Olean/Index.lean`.

This reads each module's header once (`moduleImports`) and nothing else of the
files.  Nothing about soundness rests on it: any presentation of a module's
interface is sound, the levels decide only whether a verdict is Lean's
(DESIGN #460 §3).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- **A loaded module's two flags** in `importModulesCore`'s lattice. -/
structure LoadFlags where
  /-- its private part is loaded (`import all`, or a root outside the module system) -/
  importAll : Bool
  /-- it is in the root's public scope -/
  isExported : Bool
  deriving Inhabited, BEq, Repr

/-- The part of a module the fixpoint loads. -/
def LoadFlags.level (l : LoadFlags) : OLeanLevel := if l.importAll then .private else .exported

/-- One step of the fixpoint's worklist. -/
inductive LvWork where
  /-- an import `i` of a module at flags `pf` -/
  | imp (pf : LoadFlags) (i : ImportRec)
  /-- a newly met module's imports are done: it takes its place in the order -/
  | done (m : Name) (fl : LoadFlags)

/-- The fixpoint's state. -/
structure LvState where
  /-- the flags of every module that has its place -/
  flags : Std.HashMap Name LoadFlags := {}
  /-- the modules met but not yet placed: their imports are being expanded -/
  open_ : Std.HashSet Name := {}
  /-- the modules in Lean's order (`moduleNames`) -/
  order : Array Name := #[]
  /-- every met module's imports, read once -/
  imports : Std.HashMap Name (Array ImportRec) := {}

/-- A module's imports at its flags, as work, in their order. -/
def LvWork.ofImports (fl : LoadFlags) (imps : Array ImportRec) : List LvWork :=
  imps.toList.map (.imp fl)

/-- **The fixpoint's worklist** (`importModulesCore.go`, iterative).  At `imp pf i`:
the import is followed if the importer's data is loaded and the import is public or
the importer is loaded whole (`needsData`); its flags are `importAll := gPriv ||
pf.importAll && i.importAll`, `isExported := pf.isExported && i.isExported`.  A module
with its place already has its flags joined with these; where they grow, its imports
are expanded again at the joined flags (Lean's "bump entire closure").  A module met
for the first time has its imports expanded at its flags, and takes its place in the
order after them (`done`), as Lean pushes it to `moduleNames` after its recursion.
A module met again while its own imports are expanded is an import cycle.  Each
module's imports are expanded at most three times (the flags only grow), so the
steps are at most three per import edge and two per module; `fuel` bounds them.
`meta` imports load the same data as plain ones here: what `meta` adds is IR, which
holds no constants (`mkIRData`). -/
def levelsGo {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (gPriv : Bool) :
    Nat → List LvWork → LvState → μ (Except CheckError LvState)
  | _, [], st => pure (.ok st)
  | 0, _ :: _, _ => pure (.error (.internal "the header fixpoint ran out of steps"))
  | fuel + 1, .done m fl :: rest, st =>
    let { flags, open_, order, imports } := st
    levelsGo sp gPriv fuel rest
      { flags := flags.insert m fl, open_ := open_.erase m, order := order.push m, imports }
  | fuel + 1, .imp pf i :: rest, st =>
    if !(i.isExported || pf.importAll) then levelsGo sp gPriv fuel rest st else
    let fl : LoadFlags := { importAll := gPriv || (pf.importAll && i.importAll),
                            isExported := pf.isExported && i.isExported }
    let m := i.module
    match st.flags[m]? with
    | some old =>
      let fl' : LoadFlags := { importAll := fl.importAll || old.importAll,
                               isExported := fl.isExported || old.isExported }
      if fl' == old then levelsGo sp gPriv fuel rest st else
      let imps := (st.imports[m]?).getD #[]
      levelsGo sp gPriv fuel (LvWork.ofImports fl' imps ++ rest) { st with flags := st.flags.insert m fl' }
    | none =>
      if st.open_.contains m then
        pure (.error (.internal s!"import cycle: a module importing {m} is imported by it"))
      else do
        match ← moduleImports sp m with
        | .error e => pure (.error e)
        | .ok imps =>
          levelsGo sp gPriv fuel (LvWork.ofImports fl imps ++ .done m fl :: rest)
            { st with open_ := st.open_.insert m, imports := st.imports.insert m imps }

/-- **What Lean loads for a module**: its header's fixpoint, in Lean's module order. -/
structure Loads where
  /-- the loaded modules, in Lean's order (`moduleNames` of those with data) -/
  order : Array Name
  /-- by position in `order`: the module's flags -/
  flags : Array LoadFlags
  /-- by position in `order`: the module's imports, off the start of its `M.olean` -/
  imports : Array (Array ImportRec)
  /-- a module's position in `order` -/
  index : Std.HashMap Name Nat

/-- **The header fixpoint** of a module whose header says `isModule` and `imports`:
every module Lean's `importModulesCore` loads for it (the global level `.exported` for
a module of the module system, `.private` otherwise), in Lean's module order, with
the part it loads of each (`LoadFlags.level`).  The flags are the least fixpoint of
the lattice's rules:

* the root's imports start at `importAll`, and `isExported` exactly when the root is
  of the module system;
* `A importAll ∧ A import all B → B importAll`; under the global level `.private`
  every loaded module is `importAll`;
* `A isExported ∧ A public import B → B isExported`;
* a module is loaded when an importer is `importAll` or imports it publicly.

The order is Lean's `moduleNames` restricted to the modules with data, up to one
case: a module Lean meets first through a `meta` import of a module loaded without
its data (for its IR only), and loads later, has its place at that first meeting in
Lean's order and at the later one here.  The order decides nothing but which copy of
a name comes first in the index (`ConLeche/Frontend/Olean/Index.lean`). -/
def headerFixpoint {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (isModule : Bool)
    (imports : Array ImportRec) : μ (Except CheckError Loads) := do
  let root : LoadFlags := { importAll := true, isExported := isModule }
  match ← levelsGo sp (!isModule) closureFuel (LvWork.ofImports root imports) {} with
  | .error e => pure (.error e)
  | .ok st =>
    let flags := st.order.map fun m => (st.flags[m]?).getD default
    let imps := st.order.map fun m => (st.imports[m]?).getD #[]
    let index := st.order.foldl (fun (acc : Std.HashMap Name Nat × Nat) m =>
      (acc.1.insert m acc.2, acc.2 + 1)) ({}, 0) |>.1
    pure (.ok { order := st.order, flags, imports := imps, index })

/-! ## The public-import closures -/

/-- A set of positions in the load order, as bits. -/
abbrev ModSet := ByteArray

/-- The empty set over `n` modules. -/
def ModSet.empty (n : Nat) : ModSet := ⟨Array.replicate ((n + 7) / 8) 0⟩

/-- Is position `i` in the set. -/
def ModSet.has (s : ModSet) (i : Nat) : Bool :=
  (s.get! (i / 8) >>> (i % 8).toUInt8) &&& 1 == 1

/-- The set with position `i` added. -/
def ModSet.add (s : ModSet) (i : Nat) : ModSet :=
  if i / 8 < s.size then s.set! (i / 8) (s.get! (i / 8) ||| ((1 : UInt8) <<< (i % 8).toUInt8)) else s

/-- The union of two sets of one size. -/
def ModSet.union (s t : ModSet) : ModSet :=
  t.size.fold (fun k _ s => s.set! k (s.get! k ||| t.get! k)) s

/-- The number of positions in the set. -/
def ModSet.card (s : ModSet) : Nat :=
  s.foldl (fun n b => n + (8 : Nat).fold (fun j _ c => c + ((b >>> j.toUInt8) &&& 1).toNat) 0) 0

/-- **Each loaded module's public-import closure**: the modules a path of `public
import`s leads to from it, itself included, by position in the load order.  These
are loaded wherever that module is (the rule `isExported`/`needsData` follows a public
import from every module with data), so the importer's copy of a name of their
exported parts is the module's own.  A public import of a loaded module is placed
before it (it is met during that module's first expansion), so one pass in order. -/
def pubClosures (ld : Loads) : Array ModSet :=
  let n := ld.order.size
  (List.range n).foldl (fun (acc : Array ModSet) i =>
    let s := ((ld.imports[i]?).getD #[]).foldl (fun s imp =>
      if !imp.isExported then s else
      match ld.index[imp.module]? with
      | some j => if j < acc.size then s.union acc[j]! else s.add j
      | none => s) ((ModSet.empty n).add i)
    acc.push s) (Array.mkEmpty n)

end ConLeche.Frontend.Olean
