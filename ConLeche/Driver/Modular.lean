module

public import ConLeche.Driver.ParInstall
public import ConLeche.Driver.CheckPool
public import ConLeche.Driver.OwnerParse
public import ConLeche.Frontend.Olean.Modules
public import Std.Data.TreeSet.Basic

/-!
# The modular driver: module by module, over one store (task #370)

`con-leche --olean --modular --search-path=… MODULE…` checks every
module of the import closure on its own: its records installed and
checked at a **view** of the store that presents exactly the module's
context — the constants Lean elaborated it against — and the local
checks that tie the module's context to its imports.

**The store** is partitioned by home module: module `h`'s unit
(`ModSlot`) is the constants its install pushed, in push order, each
with its exported variant, and its projection tables.  A view
(`viewOf`) has no constants of its own at the start; its base layer is
the store (`MBase`): a name index over every module's predicted
constants (`buildIdx`; a name stored by several modules has several
alternates), the units, and the viewing module's **level** of every
module (`levelsOf`: `0` not loaded, `1` its exported part, `2` its
private part), computed by Lean's own rules (`importModulesCore`).  A
view gates by module, never by a position in some global order.

**The install** of module `M` is the serial fold's phase A
(`installLoop`) at `M`'s view: it waits for the units of the modules it
imports and nothing else (a module is installed after its direct
imports, each of which was installed after its own: the closure is
complete).  Independent modules install in parallel (`installAll`, a
ready queue over the import graph on `jobs` worker threads).  Its unit
is published when it is done.  **The checks** of every recorded
declaration of every module run in one pool afterwards, each at its
module's final view, restricted to its prefix as usual.
-/

@[expose] public section

namespace ConLeche.Driver.Modular

open ConLeche ConLeche.Cached ConLeche.Frontend ConLeche.Frontend.Olean

/-! ## The module graph -/

/-- **A module, as the driver checks it**: its imports (indices of
earlier modules) with their flags, its prepared records, and its
constants' exported levels by name. -/
structure ModIn where
  name : Name
  isModule : Bool
  imports : Array (Nat × ImportRec)
  decls : Array Declaration
  expo : Std.HashMap Name Expo
  deriving Inhabited

/-- **The graph**: the modules in Lean's module order, each one's
imports resolved to earlier modules (a later or missing one is an
import cycle or an unread module: malformed input), each one's records
emitted and prepared. -/
def buildGraph (pre : PreludeIx) (rs : Array ModRead) :
    Except (CheckError × Name) (Array ModIn) := do
  let pos : Std.HashMap Name Nat := rs.size.fold (init := {}) fun i _ m => m.insert rs[i].name i
  let mut out : Array ModIn := Array.mkEmpty rs.size
  for h : i in [0:rs.size] do
    let r := rs[i]
    let mut imps : Array (Nat × ImportRec) := #[]
    for im in r.imports do
      match pos[im.module]? with
      | some j =>
        if j < i then imps := imps.push (j, im)
        else throw (.invalid s!"import cycle: {r.name} imports {im.module}", r.name)
      | none => throw (.internal s!"{r.name} imports {im.module}, which was not read", r.name)
    let ds ← match moduleDecls r.constants with
      | .ok ds => pure ds
      | .error (e, _) => throw (e, r.name)
    let expo : Std.HashMap Name Expo := r.constants.size.fold (init := {}) fun k _ m =>
      m.insert r.constants[k]!.name (r.expo[k]?.getD .absent)
    out := out.push ⟨r.name, r.isModule, imps, prepareModule pre ds, expo⟩
  return out

/-! ## The levels -/

/-- **The level of every module in `m`'s context** (Lean's
`importModulesCore`, the data part): the least fixed point of

* `m`'s direct import `i` is loaded, with `importAll := G ∨ i.importAll`
  and `isExported := E₀ ∧ i.isExported`,
* a loaded `A` with flags `(iA, iE)` loads its import `i` when
  `i.isExported ∨ iA`, with `importAll := G ∨ (iA ∧ i.importAll)` and
  `isExported := iE ∧ i.isExported`,

where `G` (every import at the private level) holds for a module
outside the module system, and `E₀` for one inside it.  A loaded
module's level is `2` (private) under `importAll`, `1` (exported)
otherwise; `0` is not loaded.  The state of a module only grows (two
flags), so the worklist is bounded by four visits per module. -/
def levelsOf (g : Array ModIn) (m : Nat) : ByteArray := Id.run do
  let G := match g[m]? with
    | some x => !x.isModule
    | none => true
  -- state bits: 1 loaded, 2 importAll, 4 isExported
  let mut st : Std.HashMap Nat UInt8 := {}
  let mut work : Array (Nat × Bool × Bool) := #[]
  for (j, im) in (g[m]?.map (·.imports)).getD #[] do
    work := work.push (j, G || im.importAll, !G && im.isExported)
  let mut fuel := 4 * g.size + 4 * (g.foldl (· + ·.imports.size) 0) + 4
  while fuel > 0 do
    fuel := fuel - 1
    match work.back? with
    | none => fuel := 0
    | some (b, iA, iE) =>
      work := work.pop
      let cur := st.getD b 0
      let new : UInt8 := cur ||| 1 ||| (if iA then 2 else 0) ||| (if iE then 4 else 0)
      if new != cur then
        st := st.insert b new
        let iA' := new &&& 2 != 0
        let iE' := new &&& 4 != 0
        for (j, im) in (g[b]?.map (·.imports)).getD #[] do
          if im.isExported || iA' then
            work := work.push (j, G || (iA' && im.importAll), iE' && im.isExported)
  let mut lvl := ByteArray.mk (Array.replicate g.size 0)
  for (b, s) in st.toList do
    if b < lvl.size then
      lvl := lvl.set! b (if s &&& 2 != 0 then 2 else 1)
  return lvl

/-! ## The store -/

/-- The number of shards of the store's name index. -/
def nShards : Nat := 256

/-- **The store's name index**: every name a module's records will
install (`predictSlots`), with the module and its position among the
module's installed constants; a name several modules store has an
alternate for each, in module order.  Also the names with more than one
alternate. -/
def buildIdx (g : Array ModIn) : Array (Std.HashMap Name (List (Nat × Nat))) × Array Name := Id.run do
  let mut sh : Array (Std.HashMap Name (List (Nat × Nat))) := Array.replicate nShards {}
  let mut dups : Std.HashSet Name := {}
  for h : i in [0:g.size] do
    let mut j := 0
    for pd in g[i].decls do
      for n in predictSlots pd do
        let s := baseShard n nShards
        let m := sh[s]!
        let sh' := sh.set! s {}
        let (old, m) := m.getThenInsertIfNew? n [(i, j)]
        let m := match old with
          | some l => m.insert n (l ++ [(i, j)])
          | none => m
        if old.isSome then dups := dups.insert n
        sh := sh'.set! s m
        j := j + 1
  return (sh, dups.toArray)

/-- **A module's view**: no constants of its own yet, the store at the
module's levels below. -/
def viewOf (idx : Array (Std.HashMap Name (List (Nat × Nat)))) (slots : Array (Thunk ModSlot))
    (lvl : ByteArray) : FEnv :=
  ⟨⟨[], []⟩, {}, 0, { mb := some ⟨idx, slots, lvl⟩ }, [], {}⟩

/-- The exported variant of an installed constant: the same constant,
the constant with its value hidden (a definition becomes an axiom of
its statement; a theorem and an opaque constant are value-free
already), or nothing when the exported part does not store it. -/
def variantOf (ex : Option Expo) (ci : ConstantInfo) : Option ConstantInfo :=
  match ex with
  | some .same => some ci
  | some .hidden =>
    match ci with
    | .defnInfo cv _ _ => some (.axiomInfo cv)
    | ci => some ci
  | _ => none

/-- **A module's unit**: its installed constants in push order, their
exported variants, its tables. -/
def unitOf (m : ModIn) (fe : FEnv) : ModSlot :=
  let priv := fe.env.consts.reverse.toArray
  { priv, pub := priv.map fun ci => variantOf m.expo[ci.name]? ci, tbls := fe.tbls }

/-! ## The install -/

/-- **One module installed**: the fold's phase A over its records from
its view `fe₀`, with the accepting run. -/
structure ModInstalled (mode : CheckMode) (ds : Array Declaration) (fe₀ : FEnv) where
  fe : FEnv
  pend : Array PendingCheck
  run : ∃ n, InstallRun mode natOpPinSets ds.toList (0, fe₀, #[]) (n, fe, pend)

/-- Install module `i` at its view. -/
def installModule (mode : CheckMode) (err : IO.FS.Stream) (ds : Array Declaration) (fe₀ : FEnv) :
    IO (Except (CheckError × Nat) (ModInstalled mode ds fe₀)) := do
  let st ← IO.mkRef ({} : WStats)
  let p₀ : Nat × FEnv × Array PendingCheck := (0, fe₀.markLinear, #[])
  match ← installLoop mode err 0 ds.size 0 st ds p₀ 0 p₀ (by
      rw [List.take_zero]; exact .nil _) with
  | .error e => return .error e
  | .ok ⟨(n, fe, pend), ⟨r⟩⟩ => return .ok ⟨fe, pend, ⟨n, FEnv.markLinear_eq fe₀ ▸ r⟩⟩

/-- The ready queue of the install: the modules whose imports are all
installed, lowest index first; and the count of unfinished imports of
every module. -/
structure Sched where
  counts : Array (IO.Ref Nat)
  dependents : Array (Array Nat)
  ready : IO.Ref (Std.TreeSet Nat compare)
  remaining : IO.Ref Nat
  stop : IO.Ref Bool
  lock : Std.BaseMutex
  cv : Std.Condvar

/-- The next ready module, waiting for one; `none` once every module is
done or the run stopped. -/
partial def Sched.next (sc : Sched) : IO (Option Nat) := do
  sc.lock.lock
  let rec loop : IO (Option Nat) := do
    if (← sc.stop.get) || (← sc.remaining.get) == 0 then return none
    match (← sc.ready.get).min? with
    | some k =>
      sc.ready.modify (·.erase k)
      return some k
    | none =>
      sc.cv.wait sc.lock
      loop
  let r ← loop
  sc.lock.unlock
  return r

/-- Module `k` done: its dependents' counts drop, the ready ones join the
queue. -/
def Sched.finish (sc : Sched) (k : Nat) : IO Unit := do
  let mut newly : Array Nat := #[]
  for d in (sc.dependents[k]?).getD #[] do
    match sc.counts[d]? with
    | some r =>
      let c ← r.modifyGet fun c => (c - 1, c - 1)
      if c == 0 then newly := newly.push d
    | none => pure ()
  sc.lock.lock
  sc.ready.modify fun t => newly.foldl (·.insert ·) t
  sc.remaining.modify (· - 1)
  sc.lock.unlock
  sc.cv.notifyAll

/-- Stop the run: every waiting worker wakes up and leaves. -/
def Sched.halt (sc : Sched) : IO Unit := do
  sc.lock.lock
  sc.stop.set true
  sc.lock.unlock
  sc.cv.notifyAll

/-! ## The run -/

/-- **The store**: the name index, the names with several alternates,
the units (deferred: a thunk over the promise the module's install
resolves) and every module's levels. -/
structure Store where
  idx : Array (Std.HashMap Name (List (Nat × Nat)))
  dups : Array Name
  slots : Array (Thunk ModSlot)
  lvls : Array ByteArray

/-- Module `i`'s view of the store. -/
def Store.view (S : Store) (i : Nat) : FEnv :=
  viewOf S.idx S.slots ((S.lvls[i]?).getD .empty)

/-- Module `i`'s records. -/
def declsAt (g : Array ModIn) (i : Nat) : Array Declaration := (g[i]?.map (·.decls)).getD #[]

/-- A module's install, tagged with its index. -/
structure ModRes (mode : CheckMode) (g : Array ModIn) (S : Store) where
  i : Nat
  res : Except (CheckError × Nat) (ModInstalled mode (declsAt g i) (S.view i))

/-- **The install of every module**: `jobs` workers take ready modules
off the queue, install each at its view, publish its unit, release its
dependents.  The first failure stops the run (every unpublished unit is
resolved empty, so nobody stays waiting). -/
def installAll (mode : CheckMode) (err : IO.FS.Stream) (jobs : Nat) (g : Array ModIn)
    (S : Store) (proms : Array (IO.Promise ModSlot)) :
    IO (Array (Option (ModRes mode g S))) := do
  let n := g.size
  let counts ← g.mapM fun m => IO.mkRef m.imports.size
  let mut dependents : Array (Array Nat) := Array.replicate n #[]
  for h : i in [0:n] do
    for (j, _) in g[i].imports do
      dependents := dependents.modify j (·.push i)
  let ready0 := (List.range n).filter (fun i => (g[i]?.map (·.imports.size)).getD 0 == 0)
  let ready ← IO.mkRef (ready0.foldl (fun t i => t.insert i) (∅ : Std.TreeSet Nat compare))
  let remaining ← IO.mkRef n
  let stop ← IO.mkRef false
  let lock ← Std.BaseMutex.new
  let cv ← Std.Condvar.new
  let sc : Sched := { counts, dependents, ready, remaining, stop, lock, cv }
  let results ← (Array.range n).mapM fun _ => IO.mkRef (none : Option (ModRes mode g S))
  let worker : IO Unit := do
    let rec loop (fuel : Nat) : IO Unit := do
      match fuel with
      | 0 => pure ()
      | fuel + 1 =>
        match ← sc.next with
        | none => pure ()
        | some k =>
          let r ← installModule mode err (declsAt g k) (S.view k)
          let unit := match r with
            | .ok e => unitOf ((g[k]?).getD default) e.fe
            | .error _ => {}
          OwnerParse.markOne unit
          match r with
          | .ok e =>
            OwnerParse.markOne e.fe
            OwnerParse.markOne e.pend
          | .error _ => pure ()
          if let some p := proms[k]? then p.resolve unit
          if let some ref := results[k]? then
            ref.set (some ⟨k, by
              exact r⟩)
          match r with
          | .error _ => sc.halt
          | .ok _ => sc.finish k
          loop fuel
    loop (n + 1)
  let w := max 1 (min jobs n)
  let tasks ← (Array.range w).mapM fun _ => IO.asTask (prio := .dedicated) worker
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error ioe => err.putStr s!"con-leche: install worker failed: {ioe}\n"
  -- nobody waits on an unpublished unit any more
  for p in proms do
    unless (← IO.hasFinished p.result?) do p.resolve {}
  results.mapM (·.get)

end ConLeche.Driver.Modular
