module

public import ConLeche.Driver.Run
public import ConLeche.Driver.CheckPool
public import ConLeche.Driver.OwnerParse
public import ConLeche.Frontend.Olean.Modules
public import ConLeche.Modular
public import ConLeche.Cached.ModStore
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

/-- **What every importer of module `k` at the exported level loads**: `k`
and the modules its `public import`s reach (Lean's rule `A ≥ private ∧
A public import B → B ≥ private`), at the exported level at least. -/
def pubReachOf (g : Array ModIn) (k : Nat) : ByteArray := Id.run do
  let mut r := ByteArray.mk (Array.replicate g.size 0)
  let mut work : Array Nat := #[k]
  let mut fuel := g.size + 1
  while fuel > 0 do
    match work.back? with
    | none => fuel := 0
    | some b =>
      work := work.pop
      if b < r.size && r.get! b == 0 then
        fuel := fuel - 1
        r := r.set! b 1
        for (j, im) in (g[b]?.map (·.imports)).getD #[] do
          if im.isExported then work := work.push j
  return r

/-- **Module `k`'s unit** from its installed view `fe` and its proofs
(`flagged`), with the reads `unitOk` verifies it against.  An oracle:
nothing here is trusted, `unitOk` checks what it returns.

* The exported presentation (`at1`).  Lean's exported views are not
  closed — an `@[inline]` definition's value, or a generated equation
  lemma's statement, may read the module's private `let rec` helper, and
  a public structure's private constructor is not stored at all — so the
  presentation is the exported part closed under what the presented
  constants' laws read within the module (a constant pulled in so is
  presented with its value hidden, if a definition: Lean's importers do
  not see it either; a pinned name is never presented as an assumption:
  the checker's fast paths read its kind, and Lean's kernel computes the
  `Nat` operations by name whatever the exported view says).
* The gates (`g1`, `v1`): a presented constant may read a name of
  another module that not every importer at the exported level loads (a
  realised equation lemma's statement reads the private matcher of a
  module the importer imports with `import all`).  Such a constant is
  presented only to a viewer that loads what it reads (`g1`), a
  definition's value only to one that loads what the value reads
  (`v1`), transitively. -/
def unitOf (g : Array ModIn) (S : Mod.Store) (flagged : Std.HashSet Name) (k : Nat) (fe : FEnv) :
    Except String (Mod.Unit' × Mod.Reads) := do
  let some m := g[k]? | throw "no module"
  let priv := fe.env.consts.reverse.toArray
  let n := priv.size
  let reach := pubReachOf g k
  let guaranteed (p : Nat × UInt8) : Bool := p.2 == 1 && reach.get! p.1 == 1
  let tblOf (ci : ConstantInfo) : Option ProjTable := fe.env.tables.find? (·.structName == ci.name)
  let typeLaws (ci : ConstantInfo) : List Expr × List Name :=
    Mod.lawsOf (tblOf ci) (match ci with | .defnInfo .. => Mod.asAxiom ci | _ => ci)
  let resolve (d : Name) : Except String (Nat × Nat) :=
    match Mod.target k fe d with
    | some t => pure t
    | none => throw s!"{d} does not resolve in its module"
  let mut tReads : Array (Array (Name × Nat × Nat)) := Array.mkEmpty n
  let mut vReads : Array (Array (Name × Nat × Nat)) := Array.mkEmpty n
  for ci in priv do
    let (es, ns) := typeLaws ci
    let dt := Mod.collectGo es {} (ns.foldl (·.insert ·) {})
    let dv := match ci with
      | .defnInfo _ v _ => (Mod.collectGo [v] {} {}).toArray.filter (!dt.contains ·)
      | _ => #[]
    tReads := tReads.push (← dt.toArray.mapM fun d => return (d, ← resolve d))
    vReads := vReads.push (← dv.mapM fun d => return (d, ← resolve d))
  let isOwn (t : Nat × Nat) : Bool := t.1 == k
  -- the exported presentation: the exported part, closed within the module
  let mut pres : Array (Option Bool) := priv.map fun ci => match (m.expo[ci.name]? : Option Expo) with
    | some .same => some true
    | some .hidden => some (!Mod.hideable ci)
    | _ => none
  let mut work : Array Nat := (Array.range n).filter fun j => (pres[j]!).isSome
  let mut fuel := n + 1
  while fuel > 0 do
    match work.back? with
    | none => fuel := 0
    | some j =>
      work := work.pop
      fuel := fuel - 1
      let full := pres[j]!.getD false
      for (_, t) in tReads[j]! ++ (if full then vReads[j]! else #[]) do
        if isOwn t && t.2 < n && (pres[t.2]!).isNone then
          pres := pres.set! t.2 (some (match priv[t.2]! with
            | .defnInfo .. => !Mod.hideable priv[t.2]!
            | _ => true))
          work := work.push t.2
  -- the gates, to a fixed point (own gates only grow)
  let pairOf (t : Nat × Nat) : Nat × UInt8 := if isOwn t then (k, 1) else (t.1, S.needAt t.1 t.2)
  let tgtGate (g1 : Array (Array (Nat × UInt8))) (t : Nat × Nat) : Array (Nat × UInt8) :=
    if isOwn t then g1[t.2]?.getD #[]
    else if S.needAt t.1 t.2 == 1 then S.gateAt t.1 t.2 else #[]
  let gateOver (g1 : Array (Array (Nat × UInt8))) (rs : Array (Name × Nat × Nat)) :
      Array (Nat × UInt8) := Id.run do
    let mut out : Std.HashSet (Nat × UInt8) := {}
    for (_, t) in rs do
      let p := pairOf t
      unless guaranteed p do out := out.insert p
      for q in tgtGate g1 t do
        unless guaranteed q do out := out.insert q
    return out.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  -- a definition presented with its value, whose value reads must not be
  -- gated apart (a pinned name: all or nothing)
  let valueApart (j : Nat) : Bool := pres[j]! == some true && Mod.hideable priv[j]! &&
    (match priv[j]! with | .defnInfo .. => true | _ => false)
  let mut g1 : Array (Array (Nat × UInt8)) := Array.replicate n #[]
  let mut changed := true
  let mut rounds := n + 1
  while changed && rounds > 0 do
    changed := false
    rounds := rounds - 1
    for j in [0:n] do
      if (pres[j]!).isSome then
        let rs := if pres[j]! == some true && !valueApart j then tReads[j]! ++ vReads[j]!
          else tReads[j]!
        let gt := gateOver g1 rs
        if gt != g1[j]! then
          g1 := g1.set! j gt
          changed := true
  let mut v1 : Array (Array (Nat × UInt8)) := Array.replicate n #[]
  for j in [0:n] do
    if valueApart j then
      v1 := v1.set! j ((gateOver g1 vReads[j]!).filter (!g1[j]!.contains ·))
  -- what the importers check
  let slot : ModSlot := {
    priv, at1 := (Array.range n).map fun j => Mod.at1Of pres[j]! priv[j]!,
    tbls := priv.map tblOf, g1, v1,
    prf := priv.map fun ci => flagged.contains ci.name }
  let keyOf (t : Nat × Nat) (d : Name) : ConLeche.Modular.Key :=
    if isOwn t then Mod.keyOfSlot slot k t.2 d else S.keyAt t.1 t.2 d
  let dupName (d : Name) : Bool := (S.alts d).length ≥ 2
  let mut fp1 : Std.HashSet (Nat × UInt8) := {}
  let mut d1 : Array (Name × ConLeche.Modular.Key) := #[]
  let mut d2 : Array (Name × ConLeche.Modular.Key) := #[]
  let mut all2 : Std.HashSet Name := {}
  let mut all1 : Std.HashSet Name := {}
  let mut gated : Array (Nat × Array Name × Array Name) := #[]
  for j in [0:n] do
    for (d, t) in tReads[j]! ++ vReads[j]! do
      all2 := all2.insert d
      if dupName d then
        let x := (d, keyOf t d)
        unless d2.contains x do d2 := d2.push x
    if let some full := pres[j]! then
      let rs := tReads[j]! ++ (if full then vReads[j]! else #[])
      for (d, t) in rs do
        let p := pairOf t
        if guaranteed p then fp1 := fp1.insert p
        for q in tgtGate g1 t do
          if guaranteed q then fp1 := fp1.insert q
        if dupName d then
          let x := (d, keyOf t d)
          unless d1.contains x do d1 := d1.push x
      if g1[j]!.isEmpty && v1[j]!.isEmpty then
        for (d, _) in rs do all1 := all1.insert d
      else
        let tn := if v1[j]!.isEmpty then rs else tReads[j]!
        gated := gated.push (j, tn.map (·.1), if v1[j]!.isEmpty then #[] else vReads[j]!.map (·.1))
  return ({ slot, fp1 := fp1.toArray, dups1 := d1, dups2 := d2 },
    { all2 := all2.toArray, all1 := all1.toArray, gated })

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

/-! ## The proofs of a module -/

/-- **A module's proofs**: its theorems, and every definition or opaque
constant whose name another module stores too and whose value passes
the theorem record's check (its type a proposition) — never a pinned
name.  Read off the module's recorded checks: a theorem's record and a
value record are what its declarations leave. -/
def proofsOf (mode : CheckMode) (dups : Std.HashSet Name) (fe : FEnv)
    (pend : Array PendingCheck) : Std.HashSet Name := Id.run do
  let mut out : Std.HashSet Name := {}
  for pc in pend do
    if !Mod.isPinned pc.vg.cv.name then
      if pc.vg.kind == .thm then out := out.insert pc.vg.cv.name
      else if dups.contains pc.vg.cv.name then
        match checkPending mode fe { pc with vg := { pc.vg with kind := .thm } } {} with
        | .ok _ => out := out.insert pc.vg.cv.name
        | .error _ => pure ()
  return out

/-! ## The run -/

/-- Module `i`'s records. -/
def declsAt (g : Array ModIn) (i : Nat) : Array Declaration := (g[i]?.map (·.decls)).getD #[]

/-- A module's install, tagged with its index. -/
structure ModRes (mode : CheckMode) (g : Array ModIn) (S : Mod.Store) where
  i : Nat
  unit : Mod.Unit'
  res : Except (CheckError × Nat) (ModInstalled mode (declsAt g i) (S.view i))

/-- **The install of every module**: `jobs` workers take ready modules
off the queue, install each at its view, publish its unit, release its
dependents.  The first failure stops the run (every unpublished unit is
resolved empty, so nobody stays waiting). -/
def installAll (mode : CheckMode) (err : IO.FS.Stream) (jobs : Nat) (g : Array ModIn)
    (S : Mod.Store) (dups : Std.HashSet Name) (proms : Array (IO.Promise ModSlot)) :
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
          let flags := match r with
            | .ok e => proofsOf mode dups e.fe e.pend
            | .error _ => {}
          let (r, u) := match r with
            | .ok e => match unitOf g S flags k e.fe with
              | .ok (u, rd) =>
                if Mod.unitOk S k e.fe flags.contains u rd then (r, u)
                else (.error (.internal "the unit of the module fails its check", 0), default)
              | .error msg => (.error (.internal s!"the unit of the module: {msg}", 0), default)
            | .error _ => (r, default)
          let unit := u.slot
          OwnerParse.markOne unit
          match r with
          | .ok e =>
            -- the module's own part of its view (its base reaches the
            -- units' thunks, which the mark would wait for)
            OwnerParse.markOne e.fe.env
            OwnerParse.markOne e.fe.idx
            OwnerParse.markOne e.fe.tbls
            OwnerParse.markOne e.pend
          | .error _ => pure ()
          if let some p := proms[k]? then p.resolve unit
          if let some ref := results[k]? then
            ref.set (some ⟨k, u, r⟩)
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

/-! ## The local checks -/

/-- A module's name, for messages. -/
def nameOf (g : Array ModIn) (h : Nat) : Name := (g[h]?.map (·.name)).getD .anonymous

/-- Why module `m`'s local checks fail, for the message. -/
def localWhy (g : Array ModIn) (S : Mod.Store) (units : Array Mod.Unit') (m : Nat) : String := Id.run do
  let lv := S.lvl m
  for h in [0:lv.size] do
    let l := Mod.lvlAt lv h
    if l != 0 then
      if !(h < m && l ≤ 2) then return s!"{nameOf g m} loads the later module {nameOf g h}"
      let some u := units[h]? | return "no unit"
      if l == 2 then
        let lh := S.lvl h
        for x in [0:lh.size] do
          unless Mod.lvlAt lh x ≤ Mod.lvlAt lv x do
            return s!"{nameOf g m} loads {nameOf g h} at its private level but not {nameOf g x}, \
              which {nameOf g h}'s context holds"
      else
        for (x, need) in u.fp1 do
          unless Mod.lvlAt lv x ≥ need do
            return s!"{nameOf g h}'s exported constants read {nameOf g x}, which {nameOf g m} \
              does not load"
      for (d, k) in (if l == 2 then u.dups2 else u.dups1) do
        unless S.keyIn m d == some k do
          return s!"{d} is read by a constant of {nameOf g h} and resolved differently in \
            {nameOf g m}"
  return "the local checks fail"

/-! ## Parallel maps -/

/-- `f 0 … f (n-1)` on `jobs` dedicated workers, claiming one index at a
time off a shared counter; the results in index order. -/
def parMap {α : Type} [Inhabited α] (jobs n : Nat) (f : Nat → α) : IO (Array α) := do
  let next ← IO.mkRef 0
  let w := max 1 (min jobs n)
  let worker : IO (Array (Nat × α)) := do
    let rec loop (fuel : Nat) (acc : Array (Nat × α)) : IO (Array (Nat × α)) := do
      match fuel with
      | 0 => return acc
      | fuel + 1 =>
        let k ← next.modifyGet fun a => (a, a + 1)
        if k < n then loop fuel (acc.push (k, f k)) else return acc
    loop (n + 1) #[]
  let tasks ← (Array.range w).mapM fun _ => IO.asTask (prio := .dedicated) worker
  let mut out : Array α := Array.replicate n default
  for t in tasks do
    match ← IO.wait t with
    | .ok rs => for (k, a) in rs do out := out.set! k a
    | .error ioe => throw ioe
  return out

/-! ## The run -/

/-- **The modular run**: read, build the graph and the store, install
every module, compute the requirements, run the local checks and every
record's check; the verdict line and the exit code. -/
def checkModular (sp : SearchPath) (roots : Array Name) (mode : CheckMode) (stride jobs : Nat) :
    IO UInt32 := do
  let t0 ← IO.monoMsNow
  let err ← IO.getStderr
  let modeTag : String := match mode with
    | .verified | .verifiedEager => "--verified"
    | .trusted | .trustedEager => "--trusted"
  let phase (what : String) : IO Unit := do
    if stride > 0 then
      let now ← IO.monoMsNow
      err.putStr s!"con-leche: {what} t={ConLeche.Cached.msSecs (now - t0)}s\n"
      err.flush
  let fail (e : CheckError) (where_ : String) : IO UInt32 := do
    match e with
    | .notImplemented w => IO.eprintln s!"con-leche: declined: {w} [at {where_}] ({modeTag})"
    | .invalid w => IO.eprintln s!"con-leche: invalid: {w} [at {where_}] ({modeTag})"
    | .internal w => IO.eprintln s!"con-leche: {w} [at {where_}] ({modeTag})"
    return e.exitCode
  let pre ← match ConLeche.Frontend.builtinPreludeE with
    | .ok p => pure p
    | .error _ =>
      IO.eprintln s!"con-leche: the built-in prelude does not parse ({modeTag})"
      return 3
  let rs ← match ← readClosure sp roots jobs with
    | .ok rs => pure rs
    | .error e => return ← fail e "reading the oleans"
  phase s!"read {rs.size} modules"
  let g ← match buildGraph pre rs with
    | .ok g => pure g
    | .error (e, m) => return ← fail e s!"module {m}"
  -- the graph lives to the end and every worker reads it (its names are
  -- hash-consed across modules): persistent before any worker starts, so
  -- that no later mark (an installed unit's) reaches a counted object
  -- another thread is counting
  OwnerParse.markOne g
  let nDecls := g.foldl (· + ·.decls.size) 0
  let lvls ← parMap jobs g.size (levelsOf g)
  let (idx, dupArr) := buildIdx g
  let dups : Std.HashSet Name := dupArr.foldl (·.insert ·) {}
  phase s!"graph: {g.size} modules, {nDecls} records, {dupArr.size} names stored twice"
  -- the index and the levels live to the end and are read by every
  -- worker: persistent, so that no lookup counts references on them
  -- (the slots are thunks over the units' promises, which the mark would
  -- wait for)
  OwnerParse.markOne idx
  OwnerParse.markOne lvls
  let proms ← g.mapM fun _ => IO.Promise.new
  let slots : Array (Thunk ModSlot) := proms.map fun p => Thunk.mk fun _ => (p.result?.get).getD {}
  let S : Mod.Store := { idx, dups := dupArr, slots, lvls }
  let results ← installAll mode err jobs g S dups proms
  -- the first failing module in module order (a module after a failure
  -- may never have been installed: the run stopped)
  let mut ins : Array (Option (ModRes mode g S)) := results
  for h : k in [0:results.size] do
    if let some r := results[k] then
      if let .error (e, pos) := r.res then
        let d := match (declsAt g k)[pos]? with
          | some d => s!"{ConLeche.Cached.declCLabel d}, record {pos} of "
          | none => ""
        -- for a rejection on an unknown constant: the names neither the
        -- context nor the module itself stores
        let ownNames : Std.HashSet Name :=
          (declsAt g k).foldl (fun s d => d.names.foldl (·.insert ·) s) {}
        let extra := match (declsAt g k)[pos]? with
          | some (.thmDecl cv v) | some (.defnDecl cv v _) | some (.opaqueDecl cv v) =>
            let bad := (Mod.collectGo [cv.type, v] {} {}).toList.filter fun n =>
              ((S.view k).find? n).isNone && !ownNames.contains n
            if bad.isEmpty then "" else s!" (not in the module's context: {bad.take 5})"
          | _ => ""
        return ← fail e s!"{d}module {nameOf g k}{extra}"
  for h : k in [0:results.size] do
    if results[k].isNone then
      return ← fail (.internal "the module was never installed") s!"module {nameOf g k}"
  phase "install done"
  let units : Array Mod.Unit' := ins.map fun r? => (r?.map (·.unit)).getD default
  let fes : Array FEnv := ins.map fun r? => match r? with
    | some ⟨_, _, .ok e⟩ => e.fe
    | _ => mkFEnv Env.empty
  ins := #[]
  let locals ← parMap jobs g.size (Mod.localOk S units)
  for h : k in [0:locals.size] do
    unless locals[k] do
      return ← fail (.invalid (localWhy g S units k)) s!"module {nameOf g k}"
  phase "local checks done"
  -- every record of every module, checked at its module's final view
  let pends : Array (Array PendingCheck) := results.map fun r? => match r? with
    | some ⟨_, _, .ok e⟩ => e.pend
    | _ => #[]
  let jobsList : Array (Nat × Nat) := Id.run do
    let mut a := #[]
    for h : i in [0:pends.size] do
      for k in [0:pends[i].size] do a := a.push (i, k)
    return a
  phase s!"{jobsList.size} checks"
  let chk ← parMap jobs jobsList.size fun q =>
    match jobsList[q]? with
    | some (i, k) => match pends[i]?.bind (·[k]?), fes[i]? with
      | some pc, some fe => match checkPending mode fe pc {} with
        | .ok _ => (none : Option (CheckError × Nat))
        | .error e => some (e, i)
      | _, _ => some (.internal "no such record", i)
    | none => some (.internal "no such check", 0)
  for h : q in [0:chk.size] do
    if let some (e, i) := chk[q] then
      let k := (jobsList[q]?.map (·.2)).getD 0
      let pc? := (pends[i]?).bind (·[k]?)
      let nm := pc?.map (·.vg.cv.name) |>.getD .anonymous
      -- the names that do not resolve, for an unknown-constant rejection
      let extra := match pc?, fes[i]? with
        | some pc, some fe =>
          let bad := (Mod.collectGo [pc.vg.cv.type, pc.vg.jv] {} {}).toList.filter
            fun d => ((fe.restrictTo pc.vis).find? d).isNone
          if bad.isEmpty then "" else s!" (not in the module's context: {bad.take 5})"
        | _, _ => ""
      return ← fail e s!"{nm}, module {nameOf g i}{extra}"
  phase "checks done"
  IO.println s!"con-leche: accepted {nDecls} declarations in {g.size} modules ({modeTag})"
  return 0

end ConLeche.Driver.Modular
