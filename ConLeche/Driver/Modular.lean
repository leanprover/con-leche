module

public import ConLeche.Driver.Run
public import ConLeche.Driver.CheckPool
public import ConLeche.Driver.OwnerParse
public import ConLeche.Frontend.Olean.Modules
public import ConLeche.Modular
public import ConLeche.Cached.ModStore
public import Std.Data.TreeSet.Basic
/- `decodeModuleSpec_eq_fast` (`@[csimp]`): the reader is passed the
specification `decodeModuleSpec`, and the compiler runs the fast decoder. -/
import ConLeche.Verify.Frontend.Olean.Equiv

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

/-- Counts of what the exported presentations leave out (diagnostics
only): exported constants presented as an assumption or absent because
what they read is not there (by kind), constants with a gate, constants
with a full gate; a few examples. -/
structure Diag where
  assumed : Array (String × Nat) := #[]
  absent : Array (String × Nat) := #[]
  gated : Nat := 0
  vgated : Nat := 0
  ex : Array String := #[]
  /-- every type former presented as an assumption -/
  indEx : Array String := #[]
  deriving Inhabited

def Diag.addKind (a : Array (String × Nat)) (k : String) (c : Nat) : Array (String × Nat) :=
  match a.findIdx? (·.1 == k) with
  | some i => a.modify i fun (k', c') => (k', c' + c)
  | none => a.push (k, c)

def Diag.merge (a b : Diag) : Diag :=
  { assumed := b.assumed.foldl (fun acc (k, c) => Diag.addKind acc k c) a.assumed,
    absent := b.absent.foldl (fun acc (k, c) => Diag.addKind acc k c) a.absent,
    gated := a.gated + b.gated, vgated := a.vgated + b.vgated,
    ex := if a.ex.size ≥ 16 then a.ex else a.ex ++ b.ex.extract 0 (16 - a.ex.size),
    indEx := a.indEx ++ b.indEx }

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom/opaque" | .defnInfo .. => "definition" | .thmInfo _ => "theorem"
  | .indInfo .. => "inductive" | .ctorInfo .. => "constructor" | .recInfo .. => "recursor"

/-- **Module `k`'s unit** from its installed view `fe`, its records `ds`
and its proofs (`flagged`), with the reads `unitOk` verifies it against.
An oracle: nothing here is trusted, `unitOk` checks what it returns.

**The exported presentation** (maintainer's ruling, 2026-10-27: remove,
never add).  An exported constant is presented to an importer at the
exported level as stored if its type and its value (a definition's
value; for an inductive type former, its block: every constructor's and
recursor's type and rules, its table) mention only names present in the
importer's context; as the assumption of its statement if its type does
but its value does not; and not at all if its type does not.  A
constructor or recursor is presented exactly when its block is complete.
A name of the module itself is present when the exported part stores it
and it is presented (a fixed point over the module's constants, in the
unit: Lean's exported views are not closed — a generated equation
lemma's statement may read the module's private `let rec` helper, a
public structure's constructor may be private); a member of an inductive
block is stored only if the whole block is complete, and otherwise
presented as the assumption of its type, if that is complete; a name of another module
is present when the importer loads that module at a level that presents
it — which the importer decides against its own levels through the
constant's **gates** (`g1`: what its presence needs, `v1`: what its full
presentation needs beyond that), transitively.  A pinned name is never
presented as an assumption or left out: one whose presentation would be
is an error. -/
def unitOf (g : Array ModIn) (S : Mod.Store) (flagged : Std.HashSet Name) (k : Nat)
    (ds : Array Declaration) (fe : FEnv) : Except String (Mod.Unit' × Mod.Reads × Diag) := do
  let _ := ds
  let some m := g[k]? | throw "no module"
  let priv := fe.env.consts.reverse.toArray
  let n := priv.size
  let reach := pubReachOf g k
  let guaranteed (p : Nat × UInt8) : Bool := p.2 == 1 && reach.get! p.1 == 1
  let tblOf (ci : ConstantInfo) : Option ProjTable := fe.env.tables.find? (·.structName == ci.name)
  let resolve (d : Name) : Except String (Nat × Nat) :=
    match Mod.target k fe d with
    | some t => pure t
    | none => throw s!"{d} does not resolve in its module"
  -- a read: a name, its target, and the kind it must be stored as (`none`:
  -- present at all)
  let readsOf (l : Mod.Laws) : Except String (Array (Name × (Nat × Nat) × Option Mod.Want)) := do
    let pres := Mod.collectGo l.es {} (l.ns.foldl (·.insert ·) {})
    let projs := Mod.collectProjs l.es {} {}
    let fis := l.fi.foldl (·.insert ·) projs
    let fcs : Std.HashSet Name := l.fc.foldl (·.insert ·) {}
    let mut out : Array (Name × (Nat × Nat) × Option Mod.Want) := #[]
    for d in pres.toArray do out := out.push (d, ← resolve d, none)
    for d in fis.toArray do out := out.push (d, ← resolve d, some .ind)
    for d in fcs.toArray do out := out.push (d, ← resolve d, some .ctor)
    return out
  let mut tReads : Array (Array (Name × (Nat × Nat) × Option Mod.Want)) := Array.mkEmpty n
  let mut fReads : Array (Array (Name × (Nat × Nat) × Option Mod.Want)) := Array.mkEmpty n
  for ci in priv do
    tReads := tReads.push (← readsOf (Mod.lawsOf none (Mod.asAxiom ci)))
    fReads := fReads.push (← readsOf (Mod.lawsOf (tblOf ci) ci))
  let isOwn (t : Nat × Nat) : Bool := t.1 == k
  let wantOk (w : Option Mod.Want) (ci : ConstantInfo) : Bool := match w with
    | some w => w.ok ci
    | none => true
  -- the presentation independent of the importer: 2 as stored, 1 as an
  -- assumption, 0 absent; a fixed point (states only drop).  A read of an
  -- own constant is met when that constant is presented (as stored, of
  -- the wanted kind, for a full read).
  let init : Array Nat := priv.map fun ci => match (m.expo[ci.name]? : Option Expo) with
    | some .same => 2
    | some .hidden => if Mod.isPinned ci.name then 2 else 1
    | _ => 0
  let met (st : Array Nat) (r : Name × (Nat × Nat) × Option Mod.Want) : Bool :=
    let (_, t, w) := r
    if isOwn t then
      match w with
      | none => st[t.2]! > 0
      | some w => st[t.2]! == 2 && w.ok priv[t.2]!
    else
      match w with
      | none => true
      | some w => (((S.slot t.1).priv[t.2]?).map w.ok).getD false
  let mut st := init
  let mut changed := true
  let mut rounds := n + 1
  while changed && rounds > 0 do
    changed := false
    rounds := rounds - 1
    for j in [0:n] do
      if st[j]! > 0 then
        let s' := if !(tReads[j]!.all (met st)) then 0
          else if st[j]! == 2 && !(fReads[j]!.all (met st)) then 1
          else st[j]!
        if s' != st[j]! then
          st := st.set! j s'
          changed := true
  for j in [0:n] do
    if Mod.isPinned priv[j]!.name && init[j]! > 0 && st[j]! != 2 then
      throw s!"the pinned constant {priv[j]!.name} is exported but reads what its importers lack"
  -- the gates, to a fixed point (gates only grow)
  let pairOf (r : Name × (Nat × Nat) × Option Mod.Want) : Nat × UInt8 :=
    let (_, t, w) := r
    if isOwn t then (k, 1)
    else match w with
      | none => (t.1, S.needAt t.1 t.2)
      | some _ =>
        if (S.slot t.1).at1[t.2]? == some ((S.slot t.1).priv[t.2]?) then (t.1, 1) else (t.1, 2)
  let tgtGate (g1 v1 : Array (Array (Nat × UInt8))) (r : Name × (Nat × Nat) × Option Mod.Want) :
      Array (Nat × UInt8) :=
    let (_, t, w) := r
    if isOwn t then
      match w with
      | none => g1[t.2]?.getD #[]
      | some _ => g1[t.2]?.getD #[] ++ v1[t.2]?.getD #[]
    else match w with
      | none => if S.needAt t.1 t.2 == 1 then S.gateAt t.1 t.2 else #[]
      | some _ =>
        if (S.slot t.1).at1[t.2]? == some ((S.slot t.1).priv[t.2]?) then S.fullGateAt t.1 t.2
        else #[]
  let gateOver (g1 v1 : Array (Array (Nat × UInt8)))
      (rs : Array (Name × (Nat × Nat) × Option Mod.Want)) : Std.HashSet (Nat × UInt8) := Id.run do
    let mut out : Std.HashSet (Nat × UInt8) := {}
    for r in rs do
      let p := pairOf r
      unless guaranteed p do out := out.insert p
      for q in tgtGate g1 v1 r do
        unless guaranteed q do out := out.insert q
    return out
  let sortG (s : Std.HashSet (Nat × UInt8)) : Array (Nat × UInt8) :=
    s.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  let mut g1 : Array (Array (Nat × UInt8)) := Array.replicate n #[]
  let mut v1 : Array (Array (Nat × UInt8)) := Array.replicate n #[]
  changed := true
  rounds := 2 * n + 2
  while changed && rounds > 0 do
    changed := false
    rounds := rounds - 1
    for j in [0:n] do
      if st[j]! > 0 then
        let gt := sortG (gateOver g1 v1 tReads[j]!)
        let gf := if st[j]! == 2 then
            (sortG (gateOver g1 v1 fReads[j]!)).filter (!gt.contains ·) else #[]
        -- a pinned constant is all or nothing
        let (gt, gf) := if Mod.isPinned priv[j]!.name then
            (sortG ((gt ++ gf).foldl (·.insert ·) {}), #[]) else (gt, gf)
        if gt != g1[j]! || gf != v1[j]! then
          g1 := g1.set! j gt
          v1 := v1.set! j gf
          changed := true
  if changed then throw "the gates do not settle"
  for j in [0:n] do
    if Mod.isPinned priv[j]!.name && st[j]! > 0 && !g1[j]!.isEmpty then
      throw s!"the pinned constant {priv[j]!.name} reads a module its importers need not load"
  -- what is left out, for the statistics
  let mut diag : Diag := {}
  for j in [0:n] do
    let c := priv[j]!
    let kc := kindOf c
    let entry : Array (String × Nat) := #[(kc, 1)]
    if init[j]! > 0 && st[j]! == 0 then
      let msg := s!"absent: {c.name} ({kc}) of {m.name}"
      diag := diag.merge { absent := entry, ex := #[msg] }
    else if init[j]! == 2 && st[j]! == 1 then
      let msg := s!"assumption: {c.name} ({kc}) of {m.name}"
      let ie : Array String := #[msg]
      diag := diag.merge { assumed := entry, ex := #[msg], indEx := ie }
    if st[j]! > 0 && !g1[j]!.isEmpty then
      let why := g1[j]!.toList.take 3 |>.map fun (x, l) =>
        s!"{((g[x]?).map ModIn.name).getD Name.anonymous}@{l}"
      let msg := s!"gated: {c.name} ({kc}) of {m.name} needs {why}"
      diag := diag.merge { gated := 1, ex := #[msg] }
    if st[j]! > 0 && !v1[j]!.isEmpty then
      let msg := s!"full-gated: {c.name} ({kc}) of {m.name}"
      diag := diag.merge { vgated := 1, ex := #[msg] }
  -- the unit
  let slot : ModSlot := {
    priv, at1 := (Array.range n).map fun j =>
      if st[j]! == 2 then some priv[j]! else if st[j]! == 1 then some (Mod.asAxiom priv[j]!)
      else none,
    tbls := priv.map tblOf, g1, v1,
    prf := priv.map fun ci => flagged.contains ci.name }
  let dummy (d : Name) : Nat × ConstantInfo := (0, .axiomInfo ⟨d, [], .sort .zero⟩)
  let addReads (r : Mod.ReadSet) (rs : Array (Name × (Nat × Nat) × Option Mod.Want)) :
      Mod.ReadSet :=
    rs.foldl (fun r (d, _, w) =>
      let r := { r with d := r.d.insert d (dummy d) }
      match w with
      | some .ind => { r with fi := r.fi.insert d }
      | some .ctor => { r with fc := r.fc.insert d }
      | none => r) r
  let mut fp1 : Std.HashSet (Nat × UInt8) := {}
  let mut all2 : Mod.ReadSet := {}
  let mut all1 : Mod.ReadSet := {}
  let mut gated : Array (Nat × Mod.ReadSet × Mod.ReadSet) := #[]
  for j in [0:n] do
    all2 := addReads all2 fReads[j]!
    if st[j]! > 0 then
      let full := st[j]! == 2
      let rs := if full then fReads[j]! else tReads[j]!
      for r in rs do
        let p := pairOf r
        if guaranteed p then fp1 := fp1.insert p
        for q in tgtGate g1 v1 r do
          if guaranteed q then fp1 := fp1.insert q
      if g1[j]!.isEmpty && v1[j]!.isEmpty then
        all1 := addReads all1 rs
      else
        let rt := if v1[j]!.isEmpty then addReads {} rs else addReads {} tReads[j]!
        let rf := if v1[j]!.isEmpty then {} else addReads {} fReads[j]!
        gated := gated.push (j, rt, rf)
  return ({ slot, fp1 := fp1.toArray }, { all2, all1, gated }, diag)

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
  diag : Diag
  res : Except (CheckError × Nat) (ModInstalled mode (declsAt g i) (S.view i))

/-- **The install of every module**: `jobs` workers take ready modules
off the queue, install each at its view, publish its unit, release its
dependents.  The first failure stops the run (every unpublished unit is
resolved empty, so nobody stays waiting). -/
def installAll (mode : CheckMode) (err : IO.FS.Stream) (jobs : Nat) (g : Array ModIn)
    (S : Mod.Store) (dups : Std.HashSet Name) (proms : Array (IO.Promise ModSlot))
    (keepGoing : Bool := false) :
    IO (Array (Option (ModRes mode g S))) := do
  let n := g.size
  let failed ← (Array.range n).mapM fun _ => IO.mkRef false
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
          -- `--keep-going`: a module importing a failed one is skipped
          let skip ← ((g[k]?.map (·.imports)).getD #[]).anyM fun (j, _) =>
            match failed[j]? with
            | some r => r.get
            | none => pure false
          let r ← if skip then
              pure (.error (.internal "skipped: it imports a module that failed", 0))
            else installModule mode err (declsAt g k) (S.view k)
          let flags := match r with
            | .ok e => proofsOf mode dups e.fe e.pend
            | .error _ => {}
          let (r, u, dg) := match r with
            | .ok e => match unitOf g S flags k (declsAt g k) e.fe with
              | .ok (u, rd, dg) =>
                if Mod.unitOk S k e.fe flags.contains u rd then (r, u, dg)
                else (.error (.internal "the unit of the module fails its check", 0), default, {})
              | .error msg => (.error (.internal s!"the unit of the module: {msg}", 0), default, {})
            | .error _ => (r, default, {})
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
            ref.set (some ⟨k, u, dg, r⟩)
          match r with
          | .error _ =>
            if keepGoing then
              if let some f := failed[k]? then f.set true
              sc.finish k
            else sc.halt
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
  for n in S.dups do
    unless Mod.oneKey S m n do
      return s!"two modules store constants named {n} under different qualified names (not \
        proofs of one statement), and both are in the context of {nameOf g m}"
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
def checkModular (sp : SearchPath) (roots : Array Name) (mode : CheckMode) (stride jobs : Nat)
    (keepGoing : Bool := false) : IO UInt32 := do
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
  let rs ← match ← readClosure decodeModuleSpec sp roots jobs with
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
  let results ← installAll mode err jobs g S dups proms keepGoing
  if keepGoing then
    let mut nFail := 0
    let mut nSkip := 0
    for h : k in [0:results.size] do
      if let some r := results[k] then
        if let .error (e, pos) := r.res then
          if (toString e).startsWith "skipped" then nSkip := nSkip + 1
          else
            nFail := nFail + 1
            let d := match (declsAt g k)[pos]? with
              | some d => s!"{ConLeche.Cached.declCLabel d}, record {pos} of "
              | none => ""
            IO.eprintln s!"con-leche: FAILED {e} [at {d}module {nameOf g k}]"
    if nFail > 0 then
      IO.eprintln s!"con-leche: {nFail} modules failed, {nSkip} skipped ({modeTag})"
      return 1
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
  if stride > 0 then
    let dg : Diag := results.foldl (fun (d : Diag) r? => d.merge ((r?.map (·.diag)).getD {})) {}
    err.putStr s!"con-leche: exported presentations: assumption {dg.assumed}, absent {dg.absent}, \
      gated {dg.gated}, full-gated {dg.vgated}\n"
    for x in dg.ex do err.putStr s!"con-leche:   {x}\n"
    for x in dg.indEx do err.putStr s!"con-leche:   {x}\n"
  let units : Array Mod.Unit' := ins.map fun r? => (r?.map (·.unit)).getD default
  let fes : Array FEnv := ins.map fun r? => match r? with
    | some ⟨_, _, _, .ok e⟩ => e.fe
    | _ => mkFEnv Env.empty
  ins := #[]
  unless Mod.dupsOk S do
    return ← fail (.internal "the store's list of names stored twice is incomplete") "the store"
  let locals ← parMap jobs g.size (Mod.localOk S units)
  for h : k in [0:locals.size] do
    unless locals[k] do
      return ← fail (.invalid (localWhy g S units k)) s!"module {nameOf g k}"
  phase "local checks done"
  -- every record of every module, checked at its module's final view
  let pends : Array (Array PendingCheck) := results.map fun r? => match r? with
    | some ⟨_, _, _, .ok e⟩ => e.pend
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
  let mut nBad := 0
  for h : q in [0:chk.size] do
    if let some (e, i) := chk[q] then
      nBad := nBad + 1
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
      if keepGoing then
        IO.eprintln s!"con-leche: FAILED {e} [at {nm}, module {nameOf g i}{extra}]"
      else
        return ← fail e s!"{nm}, module {nameOf g i}{extra}"
  if nBad > 0 then
    IO.eprintln s!"con-leche: {nBad} checks failed ({modeTag})"
    return 1
  phase "checks done"
  IO.println s!"con-leche: accepted {nDecls} declarations in {g.size} modules ({modeTag})"
  return 0

end ConLeche.Driver.Modular
