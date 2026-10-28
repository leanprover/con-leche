module

public import ConLeche.Driver.Run
import ConLeche.Driver.OwnerParse
public import ConLeche.Frontend.Olean.Modules
import ConLeche.Modular
import ConLeche.Cached.ModStore
import ConLeche.Verify.Modular.Dev
public import ConLeche.Verify.Modular.Isolated
import ConLeche.Verify.Modular.Scope
public import Std.Data.TreeSet.Basic
/- `decodeModuleSpec_eq_fast` (`@[csimp]`): the reader is passed the
specification `decodeModuleSpec`, and the compiler runs the fast decoder. -/
import ConLeche.Verify.Frontend.Olean.Equiv
/- `isoBuild_fenv`, `isoBuild_look`, `isoBuild_keysOk`: an isolated module's
one-pass context build computes the specifications its evidence is
stated in. -/
public import ConLeche.Verify.Modular.IsoFast
/- `isoCtx_mask`: a challenge's context from the masked units is its
context (the comparison's evidence). -/
import ConLeche.Verify.Modular.Mask

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

**The isolated mode** (`--modular=isolated`, task #374) builds no store:
module `M`'s work (`isoWork`) reads `M`'s own records and the units of
the modules Lean loads for `M` (`Mod.mask`: their interfaces, the private
records of those loaded with `import all`), and nothing else — its
context, the install and checks of its records, its unit and the unit's
check, its local checks.  What is decided about the whole run is only
the coverage (`isoRunOk`: a unit per module, published as checked).
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
  /-- **A compared module** (`--compare`, a challenge): its solution's
  index and its own records, which are not installed into the store (the
  module's `decls` are empty) but compared (`compareOne`) -/
  cmp : Option (Nat × Array Declaration) := none
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
    out := out.push ⟨r.name, r.isModule, imps, prepareModule pre ds, expo, none⟩
  return out

/-- **The compared pairs, read into the closure** (`--compare C S`): the
challenge `C` imports its solution `S` with `import all` (its context
is read from `S`'s private part, so that every constant of `S` is
presented as stored), and the modules are put back in an order where
every module comes after its imports, the read order kept where it can
be (a stable topological sort).  A solution that imports its challenge
is a cycle, an error. -/
def addCompares (rs : Array ModRead) (cmps : Array (Name × Name)) :
    Except String (Array ModRead) := do
  let pos : Std.HashMap Name Nat := rs.size.fold (init := {}) fun i _ m => m.insert rs[i].name i
  let mut rs := rs
  for (c, s) in cmps do
    let some ic := pos[c]? | throw s!"the challenge {c} was not read"
    let some _ := pos[s]? | throw s!"the solution {s} was not read"
    if c == s then throw s!"{c} is compared with itself"
    if rs[ic]!.imports.any (·.module == s) then
      throw s!"the challenge {c} imports its solution {s}"
    rs := rs.modify ic fun r =>
      { r with imports := r.imports.push (ImportRec.mk s true false false) }
  -- the stable topological sort: repeatedly the first module in read
  -- order whose imports are all placed
  let n := rs.size
  let mut placed : Std.HashSet Name := {}
  let mut done : Array Bool := Array.replicate n false
  let mut out : Array ModRead := Array.mkEmpty n
  let mut start := 0
  for _ in [0:n] do
    let mut found := false
    let mut j := start
    while !found && j < n do
      if !done[j]! && rs[j]!.imports.all fun im => placed.contains im.module || !pos.contains im.module then
        found := true
      else j := j + 1
    if !found then throw "a solution imports its challenge (an import cycle through --compare)"
    out := out.push rs[j]!
    placed := placed.insert rs[j]!.name
    done := done.set! j true
    while start < n && done[start]! do start := start + 1
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
is an error.

**What it reads** (task #374): the module's own constants (`fe`, their
index) and records' exported levels (`expo`, from its own `.olean`
files), its import graph's headers (`pubReachOf`, the public imports
from it: all modules it loads), and its context through `U` alone — the
context's lookup and the interfaces of the modules it loads.  The unit
records the module's levels `lv` (for its `import all` importers). -/
def unitOf (g : Array ModIn) (U : Mod.UView) (flagged : Std.HashSet Name) (k : Nat)
    (lv : ByteArray) (fe : FEnv) : Except String (ModSlot × Mod.Reads × Diag) := do
  let some m := g[k]? | throw "no module"
  let priv := fe.env.consts.reverse.toArray
  let n := priv.size
  let reach := pubReachOf g k
  let guaranteed (p : Nat × UInt8) : Bool := p.2 == 1 && reach.get! p.1 == 1
  let tblOf (ci : ConstantInfo) : Option ProjTable := fe.env.tables.find? (·.structName == ci.name)
  let resolve (d : Name) : Except String (Nat × Nat) :=
    match Mod.target k fe U d with
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
  -- the presentation independent of the importer: 2 as stored, 1 as an
  -- assumption, 0 absent; a fixed point (states only drop).  A read of an
  -- own constant is met when that constant is presented (as stored, of
  -- the wanted kind, for a full read).
  let init : Array Nat := priv.map fun ci => match (m.expo[ci.name]? : Option Expo) with
    | some .same => 2
    | some .hidden => if Mod.isPinned ci.name then 2 else 1
    | _ => 0
  let met (st : Array Nat) (r : Name × (Nat × Nat) × Option Mod.Want) : Bool :=
    let (d, t, w) := r
    if isOwn t then
      match w with
      | none => st[t.2]! > 0
      | some w => st[t.2]! == 2 && w.ok priv[t.2]!
    else
      match w with
      | none => true
      | some w => ((U.look d).map fun (_, _, ci) => w.ok ci).getD false
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
      | none => (t.1, U.needAt t.1 t.2)
      | some _ =>
        if U.storedAt t.1 t.2 then (t.1, 1) else (t.1, 2)
  let tgtGate (g1 v1 : Array (Array (Nat × UInt8))) (r : Name × (Nat × Nat) × Option Mod.Want) :
      Array (Nat × UInt8) :=
    let (_, t, w) := r
    if isOwn t then
      match w with
      | none => g1[t.2]?.getD #[]
      | some _ => g1[t.2]?.getD #[] ++ v1[t.2]?.getD #[]
    else match w with
      | none => if U.needAt t.1 t.2 == 1 then U.gateAt t.1 t.2 else #[]
      | some _ =>
        if U.storedAt t.1 t.2 then U.fullGateAt t.1 t.2
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
  let tbls := priv.map tblOf
  let at1 : Array (Option ConstantInfo) := (Array.range n).map fun j =>
    if st[j]! == 2 then some priv[j]! else if st[j]! == 1 then some (Mod.asAxiom priv[j]!)
    else none
  -- presented as stored: the presentation is the constant (an assumption
  -- presented as an assumption included)
  let stored : Array Bool := (Array.range n).map fun j => at1[j]! == some priv[j]!
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
  let slot : ModSlot := {
    exp := {
      at1, stored,
      tbls := (Array.range n).map fun j => if stored[j]! then tbls[j]! else none,
      g1, v1, prf := priv.map fun ci => flagged.contains ci.name, fp1 := fp1.toArray }
    prv := { priv, tbls, lvl := lv } }
  return (slot, { all2, all1, gated }, diag)

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

/-- A name added to a module's proofs: a recorded declaration's, not
pinned, a theorem or passing the theorem record's check. -/
theorem attested_insert {mode : CheckMode} {fe : FEnv} {pend : Array PendingCheck}
    {s : Std.HashSet Name} (h : Mod.ProofsAttested mode s.contains fe pend) {pc : PendingCheck}
    (hm : pc ∈ pend.toList) (hpin : pc.vg.cv.name ∉ ConLeche.Modular.pinnedNames)
    (hk : pc.vg.kind = .thm ∨ (pc.vg.kind ≠ .thm ∧
      ∃ st, checkPending mode fe { pc with vg := { pc.vg with kind := .thm } } {} = .ok ((), st))) :
    Mod.ProofsAttested mode (s.insert pc.vg.cv.name).contains fe pend := by
  intro n hn
  rw [Std.HashSet.contains_insert] at hn
  rcases Bool.or_eq_true_iff.mp hn with h1 | h1
  · have := eq_of_beq h1
    subst this
    exact ⟨pc, hm, rfl, hpin, hk⟩
  · exact h n h1

/-- The walk of `proofsOf` over the records left. -/
def proofsGo (mode : CheckMode) (find : Name → Option ConstantInfo) (fe : FEnv)
    (pend : Array PendingCheck) :
    (l : List PendingCheck) → (∀ pc ∈ l, pc ∈ pend.toList) → (s : Std.HashSet Name) →
      Mod.ProofsAttested mode s.contains fe pend →
      { s : Std.HashSet Name // Mod.ProofsAttested mode s.contains fe pend }
  | [], _, s, h => ⟨s, h⟩
  | pc :: l, hl, s, h =>
    have hm : pc ∈ pend.toList := hl pc (List.mem_cons_self ..)
    have hl' : ∀ x ∈ l, x ∈ pend.toList := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    if hp : Mod.isPinned pc.vg.cv.name = true then proofsGo mode find fe pend l hl' s h
    else
      have hpin : pc.vg.cv.name ∉ ConLeche.Modular.pinnedNames := fun hn => by
        simp [Mod.isPinned, hn] at hp
      if hk : pc.vg.kind = .thm then
        proofsGo mode find fe pend l hl' _ (attested_insert h hm hpin (.inl hk))
      else if Mod.isTypeCheap find pc.vg.cv.type then proofsGo mode find fe pend l hl' s h
      else
        match hc : checkPending mode fe { pc with vg := { pc.vg with kind := .thm } } {} with
        | .ok ((), st) =>
          proofsGo mode find fe pend l hl' _ (attested_insert h hm hpin (.inr ⟨hk, st, hc⟩))
        | .error _ => proofsGo mode find fe pend l hl' s h

/-- **A module's proofs**: its theorems, and every definition or opaque
constant that passes the theorem record's check — its type inferred to
be a proposition, its value of that type — never a pinned name.  The
check is the checker's own (`checkPending` with the record's kind set to
theorem), run once at the module that installs the constant, over its
environment, and skipped for a definition whose statement is cheaply
seen to be a type (`Mod.isTypeCheap`: it would fail); for any other
definition whose type is not a proposition it stops after inferring the
type's sort.  Read off the module's recorded
checks: a theorem's record and a value record are what its declarations
leave.  A function of the module and its context alone.  With the
evidence that every name in it is attested (`ProofsAttested`). -/
def proofsOf (mode : CheckMode) (find : Name → Option ConstantInfo) (fe : FEnv)
    (pend : Array PendingCheck) : { s : Std.HashSet Name // Mod.ProofsAttested mode s.contains fe pend } :=
  proofsGo mode find fe pend pend.toList (fun _ h => h) {} (fun n hn => by
    simp at hn)

/-! ## Facts below a bound -/

/-- A fact about one index, tagged with it (an element of a parallel
map's result, whose type cannot depend on the index). -/
structure At {ι : Type} (P : ι → Prop) where
  i : ι
  h : P i

/-- The walk of `allBelow` from `j`. -/
def allBelow.go {E : Type} {P : Nat → Prop} (n : Nat) (f : (j : Nat) → j < n → Except E (PLift (P j))) :
    (j : Nat) → (∀ x, x < j → P x) → Except E (PLift (∀ x, x < n → P x))
  | j, acc =>
    if hj : j < n then
      match f j hj with
      | .ok ⟨h⟩ => allBelow.go n f (j + 1) (fun x hx => by
          rcases Nat.lt_or_ge x j with hxj | hxj
          · exact acc x hxj
          · have : x = j := by omega
            subst this; exact h)
      | .error e => .error e
    else .ok ⟨fun x hx => acc x (by omega)⟩
  termination_by j => n - j

/-- **A fact at every index below `n`**, decided index by index. -/
def allBelow {E : Type} {P : Nat → Prop} (n : Nat) (f : (j : Nat) → j < n → Except E (PLift (P j))) :
    Except E (PLift (∀ x, x < n → P x)) :=
  allBelow.go n f 0 (fun _ h => absurd h (Nat.not_lt_zero _))

/-- A tagged fact, if it is the one at `i`. -/
def At.get? {ι : Type} [DecidableEq ι] {P : ι → Prop} (a : Option (At P)) (i : ι) :
    Option (PLift (P i)) :=
  match a with
  | some c => if h : c.i = i then some ⟨h ▸ c.h⟩ else none
  | none => none

/-- Two arrays equal, entry by entry, each the pointer first. -/
def sameArr {α : Type} [DecidableEq α] (a b : Array α) : Option (PLift (a = b)) :=
  if hs : a.size = b.size then
    let r : Except Unit (PLift (∀ x, x < a.size → ∀ (h₁ : x < a.size) (h₂ : x < b.size),
        a[x] = b[x])) :=
      allBelow a.size (fun j hj => if h : OwnerParse.sameB a[j] (b[j]'(hs ▸ hj)) = true then
          .ok ⟨fun _ _ => OwnerParse.sameB_iff.mp h⟩
        else .error ())
    match r with
    | .ok ⟨h⟩ => some ⟨Array.ext hs fun j h₁ h₂ => h j h₁ h₁ h₂⟩
    | .error () => none
  else none

/-- A module's name, for messages. -/
def nameOf (g : Array ModIn) (h : Nat) : Name := (g[h]?.map (·.name)).getD .anonymous

/-! ## Compared modules (`--compare`) -/

/-- **A challenge's holes**: its theorems, definitions and opaque
constants whose value uses `sorryAx`. -/
def holesOf (ds : Array Declaration) : Std.HashSet Name :=
  ds.foldl (init := {}) fun h d => match d with
    | .thmDecl cv v | .defnDecl cv v _ | .opaqueDecl cv v =>
      if v.mentionsConst sorryAxName then h.insert cv.name else h
    | _ => h

/-- The kind of a constant, as a number (for the comparison of a hole). -/
def kindTag : ConstantInfo → Nat
  | .axiomInfo .. => 0 | .defnInfo .. => 1 | .thmInfo .. => 2 | .indInfo .. => 3
  | .ctorInfo .. => 4 | .recInfo .. => 5

/-- **A challenge constant met by its context**: a hole by a constant of
the same statement (name, level parameters, type; a theorem's by a
theorem, a definition's by a definition, the solution's value whatever
it is, or its assumption), anything else by the constant itself. -/
def cmpOk (holes : Std.HashSet Name) (o : Option ConstantInfo) (ci : ConstantInfo) : Bool :=
  match o with
  | some ci' =>
    if holes.contains ci.name then
      decide (ci'.toConstantVal = ci.toConstantVal) &&
        (kindTag ci' == kindTag ci || kindTag ci' == 0)
    else decide (ci' = ci)
  | none => false

/-- **What a compared module establishes**: its records, installed at a
view of the store (the challenge's own context: its imports, not its
solution), give constants every one of which its context (`Mod.ctxOf`,
read from its solution) meets (`cmpOk`). -/
def CmpClaim (mode : CheckMode) (S : Mod.Store) (i : Nat) (chal : Array Declaration) : Prop :=
  ∃ lv n fe pend, InstallRun mode natOpPinSets chal.toList (0, Mod.viewOf ⟨S.idx, S.slots, lv⟩, #[])
      (n, fe, pend) ∧
    ∀ ci ∈ fe.env.consts, cmpOk (holesOf chal) ((Mod.ctxOf (S.mb i)).find? ci.name) ci = true

/-- **Compare challenge `i`**, in its own work: install its records at
its own context (`lv`, its levels without its solution) — types checked,
values not (a hole's value is `sorry`) — and meet every constant they
give with its context.  The holes, each with the module its context
reads it from, beside the evidence. -/
def compareOne (mode : CheckMode) (err : IO.FS.Stream) (S : Mod.Store) (i : Nat)
    (chal : Array Declaration) (lv : ByteArray) :
    IO (Except String (PLift (CmpClaim mode S i chal) × Array (Name × Nat))) := do
  match ← installModule mode err chal (Mod.viewOf ⟨S.idx, S.slots, lv⟩) with
  | .error (e, pos) =>
    let d := match chal[pos]? with
      | some d => s!"{ConLeche.Cached.declCLabel d}: "
      | none => ""
    return .error s!"the challenge's records do not install at its own context: {d}{e}"
  | .ok e =>
    let holes := holesOf chal
    let mb := S.mb i
    if h : e.fe.env.consts.all (fun ci => cmpOk holes (mb.find? ci.name) ci) = true then
      let filled := e.fe.env.consts.filterMap fun ci =>
        if holes.contains ci.name then
          some (ci.name, match mb.pick? ci.name with
            | some (h, _, _) => h
            | none => 0)
        else none
      return .ok (⟨⟨lv, _, e.fe, e.pend, e.run.choose_spec, fun ci hci => by
        have := List.all_eq_true.mp h ci hci
        rw [Mod.ctxOf_find?]
        exact this⟩⟩, filled.reverse.toArray)
    else
      let bad := e.fe.env.consts.filter fun ci => !cmpOk holes (mb.find? ci.name) ci
      let why := bad.reverse.take 5 |>.map fun ci => match mb.find? ci.name with
        | none => s!"{ci.name}: the solution has no such constant"
        | some _ =>
          if holes.contains ci.name then s!"{ci.name}: the solution states it differently"
          else s!"{ci.name}: the solution's constant is not the challenge's"
      return .error (String.intercalate "; " why)

/-- **What a compared module establishes in isolated mode**: its records,
installed from the context its own levels give it (`lv`, without its
solution) built from the units it reads, give constants every one of
which its context — the one its levels with its solution (`lvC`) give
it, built from the units — meets (`cmpOk`). -/
def IsoCmpClaim (mode : CheckMode) (slots : Array (Thunk ModSlot)) (lvC : ByteArray)
    (chal : Array Declaration) : Prop :=
  ∃ lv n fe pend, InstallRun mode natOpPinSets chal.toList
      (0, mkFEnv (Mod.isoCtx (Mod.mask (Mod.slotOf slots) lv) lv), #[]) (n, fe, pend) ∧
    ∀ ci ∈ (Mod.ownPart (Mod.isoCtx (Mod.mask (Mod.slotOf slots) lv) lv) fe.env).consts,
      cmpOk (holesOf chal) ((Mod.isoCtx (Mod.slotOf slots) lvC).find? ci.name) ci = true

/-- **Compare a challenge in isolated mode**, in its own work: as
`compareOne`, every context built from the units the challenge reads
at the levels in question (`lv`, its own without its solution; `lvC`,
with it), so that the comparison reads only what the challenge loads. -/
def compareOneIso (mode : CheckMode) (err : IO.FS.Stream) (slots : Array (Thunk ModSlot))
    (lvC : ByteArray) (chal : Array Declaration) (lv : ByteArray) :
    IO (Except String (PLift (IsoCmpClaim mode slots lvC chal) × Array (Name × Nat))) := do
  let aS := Mod.isoBuild (Mod.mask (Mod.slotOf slots) lv) lv
  let feS := aS.fenv
  let CS := feS.env
  match ← installModule mode err chal feS with
  | .error (e, pos) =>
    let d := match chal[pos]? with
      | some d => s!"{ConLeche.Cached.declCLabel d}: "
      | none => ""
    return .error s!"the challenge's records do not install at its own context: {d}{e}"
  | .ok e =>
    let holes := holesOf chal
    let aC := Mod.isoBuild (Mod.mask (Mod.slotOf slots) lvC) lvC
    let own := (Mod.ownPart CS e.fe.env).consts
    if h : own.all (fun ci => cmpOk holes (aC.fenv.find? ci.name) ci) = true then
      let filled := own.filterMap fun ci =>
        if holes.contains ci.name then
          some (ci.name, match aC.look ci.name with
            | some (h, _, _) => h
            | none => 0)
        else none
      have hfS : feS = mkFEnv (Mod.isoCtx (Mod.mask (Mod.slotOf slots) lv) lv) :=
        Mod.isoBuild_fenv _ lv
      have hrun₀ : ∃ n, InstallRun mode natOpPinSets chal.toList
          (0, mkFEnv (Mod.isoCtx (Mod.mask (Mod.slotOf slots) lv) lv), #[]) (n, e.fe, e.pend) := by
        rw [← hfS]; exact e.run
      have hrun := hrun₀.choose_spec
      return .ok (⟨⟨lv, _, e.fe, e.pend, hrun, fun ci hci => by
        have hC : CS = Mod.isoCtx (Mod.mask (Mod.slotOf slots) lv) lv := by
          show feS.env = _
          rw [hfS]; rfl
        have hci' : ci ∈ (Mod.ownPart CS e.fe.env).consts := by rw [hC]; exact hci
        have := List.all_eq_true.mp h ci hci'
        rw [Mod.isoBuild_fenv, Mod.isoIndex, mkFEnv_find?, Mod.isoCtx_mask] at this
        exact this⟩⟩, filled.reverse.toArray)
    else
      let bad := own.filter fun ci => !cmpOk holes (aC.fenv.find? ci.name) ci
      let why := bad.reverse.take 5 |>.map fun ci => match aC.fenv.find? ci.name with
        | none => s!"{ci.name}: the solution has no such constant"
        | some _ =>
          if holes.contains ci.name then s!"{ci.name}: the solution states it differently"
          else s!"{ci.name}: the solution's constant is not the challenge's"
      return .error (String.intercalate "; " why)

/-! ## The run -/

/-- Module `i`'s records. -/
def declsAt (g : Array ModIn) (i : Nat) : Array Declaration := (g[i]?.map (·.decls)).getD #[]

/-- **A module installed and its unit checked**, with the evidence the
run's theorem needs of it (`Mod.RunOk`): its records are the graph's,
installed at its view with the accepting run, its proofs attested, its
unit checked; and, for a challenge, its comparison (`CmpClaim`) with the
holes it filled. -/
structure ModOk (mode : CheckMode) (g : Array ModIn) (S : Mod.Store) where
  i : Nat
  d : Mod.ModData
  ds : d.ds = declsAt g i
  run : ∃ n, InstallRun mode natOpPinSets d.ds.toList (0, S.view i, #[]) (n, d.fe, d.pend)
  prf : Mod.ProofsAttested mode d.flags.contains d.fe d.pend
  unit : Mod.unitOk (S.uview i) i d.fe d.flags.contains d.unit d.reads = true
  filled : Array (Name × Nat)
  cmp : ∀ is chal, (g[i]?.bind (·.cmp)) = some (is, chal) → CmpClaim mode S i chal

/-- **A module checked in isolation** (`--modular=isolated`), with the
evidence the run's theorem needs of it (`Mod.IsoRunOk`), all about the
units it reads (`Mod.mask`: those of the modules it loads, at the level
it loads them; its levels those its unit records): its records are the
graph's, installed from the canonical index of the context built from
them (`Mod.isoCtx`) with the accepting run, every record checked there,
its proofs attested there; its data's index the canonical index of its
own constants; its unit checked against them and that context
(`Mod.isoUView`); its local checks (`Mod.localOkIso`); for a challenge,
its comparison (`IsoCmpClaim`) with the holes it filled. -/
structure IsoModOk (mode : CheckMode) (g : Array ModIn) (slots : Array (Thunk ModSlot)) where
  i : Nat
  d : Mod.ModData
  ds : d.ds = declsAt g i
  iso : ∃ n feI pendI,
    InstallRun mode natOpPinSets d.ds.toList
      (0, mkFEnv (Mod.isoCtx (Mod.mask (Mod.slotOf slots) d.unit.prv.lvl) d.unit.prv.lvl), #[])
      (n, feI, pendI) ∧
    (∀ pc ∈ pendI.toList, ∃ s, checkPending mode feI pc {} = .ok ((), s)) ∧
    Mod.ProofsAttested mode d.flags.contains feI pendI ∧
    feI.env = Mod.Env.over d.fe.env
      (Mod.isoCtx (Mod.mask (Mod.slotOf slots) d.unit.prv.lvl) d.unit.prv.lvl)
  own : d.fe = mkFEnv d.fe.env
  unit : Mod.unitOk (Mod.isoUView (Mod.mask (Mod.slotOf slots) d.unit.prv.lvl) d.unit.prv.lvl) i
    d.fe d.flags.contains d.unit d.reads = true
  locals : Mod.localOkIso i (Mod.mask (Mod.slotOf slots) d.unit.prv.lvl) d.unit.prv.lvl = true
  filled : Array (Name × Nat)
  cmp : ∀ is chal, (g[i]?.bind (·.cmp)) = some (is, chal) → IsoCmpClaim mode slots d.unit.prv.lvl chal

/-- A module's install, tagged with its index. -/
structure ModRes (α : Type) where
  i : Nat
  unit : ModSlot
  diag : Diag
  res : Except (CheckError × Nat) α

/-- **One module's work**: its install and its unit (published as soon as
it is there, its dependents released), and the rest of its work, done
after (an isolated module's record checks). -/
abbrev Work (α : Type) :=
  Nat → IO (Except (CheckError × Nat) (ModSlot × Diag × (Unit → IO (Except (CheckError × Nat) α))))

/-- **The install of every module**: `jobs` workers take ready modules
off the queue, do each one's work (`work`), publish its unit, release
its dependents, finish its work.  The first failure stops the run (every
unpublished unit is resolved empty, so nobody stays waiting). -/
def installAll {α : Type} (err : IO.FS.Stream) (jobs : Nat) (g : Array ModIn)
    (proms : Array (IO.Promise ModSlot)) (keepGoing : Bool) (work : Work α) (mark : α → IO Unit) :
    IO (Array (Option (ModRes α))) := do
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
  let results ← (Array.range n).mapM fun _ => IO.mkRef (none : Option (ModRes α))
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
            else work k
          match r with
          | .ok (u, dg, rest) =>
            let unit := u
            OwnerParse.markOne unit
            if let some p := proms[k]? then p.resolve unit
            sc.finish k
            let r₂ ← rest ()
            match r₂ with
            | .ok a => mark a
            | .error _ => pure ()
            if let some ref := results[k]? then
              ref.set (some ⟨k, u, dg, r₂⟩)
            match r₂ with
            | .error _ =>
              if keepGoing then
                if let some f := failed[k]? then f.set true
              else sc.halt
            | .ok _ => pure ()
          | .error e =>
            let unit : ModSlot := {}
            OwnerParse.markOne unit
            if let some p := proms[k]? then p.resolve unit
            if let some ref := results[k]? then
              ref.set (some ⟨k, default, {}, .error e⟩)
            if keepGoing then
              if let some f := failed[k]? then f.set true
              sc.finish k
            else sc.halt
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

/-- A module's data, kept to the end and read by every worker of the
later phases: its own part of its view persistent (its base reaches the
units' thunks, which the mark would wait for). -/
def markData (d : Mod.ModData) : IO Unit := do
  OwnerParse.markOne d.fe.env
  OwnerParse.markOne d.fe.idx
  OwnerParse.markOne d.fe.tbls
  OwnerParse.markOne d.pend

/-- **A module's work in store mode**: its records installed at its view
of the store, its proofs, its unit and the unit's check; the unit
published; then, for a challenge, its comparison (at `sideLv`, its levels
without its solution). -/
def storeWork (mode : CheckMode) (err : IO.FS.Stream) (g : Array ModIn) (S : Mod.Store)
    (sideLv : Nat → ByteArray) : Work (ModOk mode g S) := fun k => do
  match ← installModule mode err (declsAt g k) (S.view k) with
  | .error e => return .error e
  | .ok e =>
    let ⟨flags, hprf⟩ := proofsOf mode e.fe.find? e.fe e.pend
    match unitOf g (S.uview k) flags k (S.lvl k) e.fe with
    | .error msg => return .error (.internal s!"the unit of the module: {msg}", 0)
    | .ok (u, rd, dg) =>
      let d : Mod.ModData :=
        { imports := ((g[k]?.map (·.imports)).getD #[]).toList.map (·.1)
          ds := declsAt g k, fe := e.fe, pend := e.pend, unit := u, flags, reads := rd }
      if hu : Mod.unitOk (S.uview k) k d.fe d.flags.contains d.unit d.reads = true then
        return .ok (u, dg, fun _ => do
          match hg : g[k]?.bind (·.cmp) with
          | none => pure (.ok ⟨k, d, rfl, e.run, hprf, hu, #[], fun _ _ h => by
              rw [hg] at h; cases h⟩)
          | some (is, chal) =>
            match ← compareOne mode err S k chal (sideLv k) with
            | .error msg =>
              pure (.error (.invalid s!"compared with {nameOf g is}: {msg}", (declsAt g k).size))
            | .ok (⟨hcl⟩, filled) => pure (.ok ⟨k, d, rfl, e.run, hprf, hu, filled,
                fun is' chal' h => by
                  rw [hg] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  exact hcl⟩))
      else return .error (.internal "the unit of the module fails its check", 0)

/-- Why a module's levels fail their check against the units it reads,
for the message. -/
def levelsWhy (g : Array ModIn) (m : Nat) (lv : ByteArray) (unit : Nat → ModSlot) :
    Option String := Id.run do
  let nm (h : Nat) : Name := (g[h]?.map (·.name)).getD .anonymous
  for h in [0:lv.size] do
    let l := Mod.lvlAt lv h
    if l != 0 then
      if !(h < m && l ≤ 2) then return some s!"{nm m} loads the later module {nm h}"
      if l == 2 then
        let lh := (unit h).prv.lvl
        for x in [0:lh.size] do
          unless Mod.lvlAt lh x ≤ Mod.lvlAt lv x do
            return some s!"{nm m} loads {nm h} at its private level but not {nm x}, \
              which {nm h}'s context holds"
      else
        for (x, need) in (unit h).exp.fp1 do
          unless Mod.lvlAt lv x ≥ need do
            return some s!"{nm h}'s exported constants read {nm x}, which {nm m} does not load"
  return none

/-- **A module's work in isolated mode**, a function of the module's own
records and of the units it reads (`Mod.mask`: the interface of every
module it loads, the private record of those it loads with `import all`,
nothing else): its context's index, lookup and duplicates in one pass
(`Mod.isoBuild`), its records installed from that index, its proofs; its
unit computed and checked from its own constants and that context
(`Mod.isoUView`); its local checks; the unit published; then every record
checked in the module's environment, which is dropped after, and, for a
challenge, its comparison (at `sideLv`, its levels without its
solution, and its own levels). -/
def isoWork (mode : CheckMode) (err : IO.FS.Stream) (g : Array ModIn) (slots : Array (Thunk ModSlot))
    (lvls : Array ByteArray) (sideLv : Nat → ByteArray) : Work (IsoModOk mode g slots) := fun k => do
  let lv := (lvls[k]?).getD .empty
  -- the units module `k` reads: what Lean loads for it, and nothing else
  let units := Mod.mask (Mod.slotOf slots) lv
  -- the context in one pass; what the bookkeeping needs of it is taken out
  -- before the install, so that the install's index is never shared (its
  -- first insertion would copy it): the provenance arrays, the size, the
  -- duplicates' check, the environment
  let a := Mod.isoBuild units lv
  let srcH := a.srcH
  let srcJ := a.srcJ
  let nC := a.n
  let dupOk := a.keysOk units
  let fe₀ := a.fenv
  let C := fe₀.env
  match ← installModule mode err (declsAt g k) fe₀ with
  | .error e => return .error e
  | .ok e =>
    let ⟨flags, hprf⟩ := proofsOf mode e.fe.find? e.fe e.pend
    let own := Mod.ownPart C e.fe.env
    -- the context's lookup, answered by the install's own index
    let U : Mod.UView := ⟨fun h => (units h).exp, Mod.lookAfter e.fe srcH srcJ nC⟩
    match unitOf g U flags k lv (mkFEnv own) with
    | .error msg => return .error (.internal s!"the unit of the module: {msg}", 0)
    | .ok (u, rd, dg) =>
      let d : Mod.ModData :=
        { imports := ((g[k]?.map (·.imports)).getD #[]).toList.map (·.1)
          ds := declsAt g k, fe := mkFEnv own, pend := #[], unit := u, flags, reads := rd }
      if hlv : OwnerParse.sameB d.unit.prv.lvl lv = true then
      if hu : Mod.unitOk U k d.fe d.flags.contains d.unit d.reads = true then
      if hl : (Mod.levelsOk k lv units && dupOk) = true then
        have hlv : d.unit.prv.lvl = lv := OwnerParse.sameB_iff.mp hlv
        have hfe : fe₀ = mkFEnv (Mod.isoCtx units lv) := Mod.isoBuild_fenv units lv
        have hrun₀ : ∃ n, InstallRun mode natOpPinSets (declsAt g k).toList
            (0, mkFEnv (Mod.isoCtx units lv), #[]) (n, e.fe, e.pend) := by
          rw [← hfe]; exact e.run
        have hrun := hrun₀.choose_spec
        have hU : U = Mod.isoUView units lv := by
          show (⟨_, Mod.lookAfter e.fe (Mod.isoBuild units lv).srcH (Mod.isoBuild units lv).srcJ
            (Mod.isoBuild units lv).n⟩ : Mod.UView) = ⟨_, _⟩
          rw [Mod.lookAfter_iso hrun]
        have hC : C = Mod.isoCtx units lv := by
          show fe₀.env = _
          rw [hfe]; rfl
        have henv : e.fe.env = Mod.Env.over d.fe.env (Mod.isoCtx units lv) := by
          have h1 := hrun.over_ctx
          have h2 : (mkFEnv own).env = Mod.ownPart (Mod.isoCtx units lv) e.fe.env := by
            show Mod.ownPart C e.fe.env = _
            rw [hC]
          show e.fe.env = Mod.Env.over (mkFEnv own).env _
          rw [h2]; exact h1
        have hloc : Mod.localOkIso k units lv = true := by
          unfold Mod.localOkIso
          rw [← Mod.isoBuild_keysOk units lv]
          exact hl
        return .ok (u, dg, fun _ => do
          match hc : checkPendingList mode e.fe e.pend.toList with
          | .ok () =>
            have hiso : ∃ n feI pendI, InstallRun mode natOpPinSets d.ds.toList
                (0, mkFEnv (Mod.isoCtx (Mod.mask (Mod.slotOf slots) d.unit.prv.lvl)
                  d.unit.prv.lvl), #[]) (n, feI, pendI) ∧
                (∀ pc ∈ pendI.toList, ∃ s, checkPending mode feI pc {} = .ok ((), s)) ∧
                Mod.ProofsAttested mode d.flags.contains feI pendI ∧
                feI.env = Mod.Env.over d.fe.env
                  (Mod.isoCtx (Mod.mask (Mod.slotOf slots) d.unit.prv.lvl) d.unit.prv.lvl) := by
              rw [hlv]
              exact ⟨_, e.fe, e.pend, hrun, checkPendingList_records mode e.fe _ hc, hprf, henv⟩
            have hu' : Mod.unitOk (Mod.isoUView (Mod.mask (Mod.slotOf slots) d.unit.prv.lvl)
                d.unit.prv.lvl) k d.fe d.flags.contains d.unit d.reads = true := by
              rw [hlv, ← hU]; exact hu
            have hloc' : Mod.localOkIso k (Mod.mask (Mod.slotOf slots) d.unit.prv.lvl)
                d.unit.prv.lvl = true := by rw [hlv]; exact hloc
            match hg : g[k]?.bind (·.cmp) with
            | none => pure (.ok ⟨k, d, rfl, hiso, rfl, hu', hloc', #[], fun _ _ h => by
                rw [hg] at h; cases h⟩)
            | some (is, chal) =>
              match ← compareOneIso mode err slots d.unit.prv.lvl chal (sideLv k) with
              | .error msg =>
                pure (.error (.invalid s!"compared with {nameOf g is}: {msg}", (declsAt g k).size))
              | .ok (⟨hcl⟩, filled) => pure (.ok ⟨k, d, rfl, hiso, rfl, hu', hloc', filled,
                  fun is' chal' h => by
                    rw [hg] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    exact hcl⟩)
          | .error (x, pos) => pure (.error (x, pos)))
      else
        -- (a failure: the one-pass state built again, for the message)
        let a' := Mod.isoBuild units lv
        let bad := a'.dropped.find? fun (h, j, n) => match a'.look n with
          | some (h₀, j₀, _) => Mod.keyOfSlot (units h) h j != Mod.keyOfSlot (units h₀) h₀ j₀
          | none => true
        let why := match levelsWhy g k lv units with
          | some w => w
          | none => s!"two modules store constants named {(bad.map (·.2.2)).getD .anonymous} \
              under different keys (not proofs of one statement), and both are in \
              the context of {(g[k]?.map (·.name)).getD .anonymous}"
        -- a position past the records: the failure is the module's, not a record's
        return .error (.invalid why, (declsAt g k).size)
      else return .error (.internal "the unit of the module fails its check", 0)
      else return .error (.internal "the unit does not record the module's levels", 0)

/-! ## The local checks -/

/-- Why module `m`'s local checks fail in a store run, for the message. -/
def localWhy (g : Array ModIn) (S : Mod.Store) (m : Nat) : String := Id.run do
  if let some w := levelsWhy g m (S.lvl m) S.slot then return w
  for n in S.dups do
    unless Mod.oneKey S m n do
      return s!"two modules store constants named {n} under different keys (not \
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

/-! ## The run's theorem -/

/-- What a record's check establishes: record `k` of module `i` passes. -/
def ChkP (mode : CheckMode) (M : Array Mod.ModData) (q : Nat × Nat) : Prop :=
  ∀ (hi : q.1 < M.size) (hk : q.2 < M[q.1].pend.size),
    ∃ s, checkPending mode M[q.1].fe M[q.1].pend[q.2] {} = .ok ((), s)

/-- The facts a module's `ModOk` carries, read at its position. -/
theorem modOk_facts {mode : CheckMode} {g : Array ModIn} {S : Mod.Store}
    {A : Array (ModOk mode g S)} (hA : ∀ k, k < A.size → ∀ h : k < A.size, A[k].i = k)
    (i : Nat) (h : i < (A.map ModOk.d).size) :
    (∃ n, InstallRun mode natOpPinSets (A.map ModOk.d)[i].ds.toList (0, S.view i, #[])
        (n, (A.map ModOk.d)[i].fe, (A.map ModOk.d)[i].pend)) ∧
    Mod.ProofsAttested mode (A.map ModOk.d)[i].flags.contains (A.map ModOk.d)[i].fe
      (A.map ModOk.d)[i].pend ∧
    Mod.unitOk (S.uview i) i (A.map ModOk.d)[i].fe (A.map ModOk.d)[i].flags.contains
      (A.map ModOk.d)[i].unit (A.map ModOk.d)[i].reads = true ∧
    (A.map ModOk.d)[i].ds = declsAt g i := by
  have h' : i < A.size := by simpa using h
  simp only [Array.getElem_map]
  have hi := hA i h' h'
  have r := A[i].run
  have p := A[i].prf
  have u := A[i].unit
  have dd := A[i].ds
  rw [hi] at r u dd
  exact ⟨r, p, u, dd⟩

/-- The facts a module's `IsoModOk` carries, read at its position. -/
theorem isoModOk_facts {mode : CheckMode} {g : Array ModIn} {slots : Array (Thunk ModSlot)}
    {A : Array (IsoModOk mode g slots)} (hA : ∀ k, k < A.size → ∀ h : k < A.size, A[k].i = k)
    (i : Nat) (h : i < (A.map IsoModOk.d).size) :
    let d := (A.map IsoModOk.d)[i]
    let units := Mod.mask (Mod.slotOf slots) d.unit.prv.lvl
    (∃ n feI pendI,
      InstallRun mode natOpPinSets d.ds.toList (0, mkFEnv (Mod.isoCtx units d.unit.prv.lvl), #[])
        (n, feI, pendI) ∧
      (∀ pc ∈ pendI.toList, ∃ s, checkPending mode feI pc {} = .ok ((), s)) ∧
      Mod.ProofsAttested mode d.flags.contains feI pendI ∧
      feI.env = Mod.Env.over d.fe.env (Mod.isoCtx units d.unit.prv.lvl)) ∧
    d.fe = mkFEnv d.fe.env ∧
    Mod.unitOk (Mod.isoUView units d.unit.prv.lvl) i d.fe d.flags.contains d.unit d.reads = true ∧
    Mod.localOkIso i units d.unit.prv.lvl = true ∧
    d.ds = declsAt g i := by
  have h' : i < A.size := by simpa using h
  simp only [Array.getElem_map]
  have hi := hA i h' h'
  have r := A[i].iso
  have o := A[i].own
  have u := A[i].unit
  have l := A[i].locals
  have dd := A[i].ds
  rw [hi] at u l dd
  exact ⟨r, o, u, l, dd⟩

/-- **The facts of a store run decided after every module**, about the
modules' data `M`: the sizes, the imports below, the published units the
store's, the units' constants the installs', the levels each unit records
the store's, the local checks, the list of names stored twice, and the
name index listing every unit constant. -/
structure CommonOk (S : Mod.Store) (M : Array Mod.ModData) : Prop where
  slots : S.slots.size = M.size
  lvls : ∀ i, i < M.size → (S.lvl i).size = M.size
  below : ∀ i (h : i < M.size), ∀ b ∈ M[i].imports, b < i
  slot : ∀ i (h : i < M.size), S.slot i = M[i].unit
  priv : ∀ i (h : i < M.size), M[i].unit.prv.priv = M[i].fe.env.consts.reverse.toArray
  ulvl : ∀ i (h : i < M.size), M[i].unit.prv.lvl = S.lvl i
  locals : ∀ i, i < M.size → Mod.localOk S i = true
  dups : Mod.dupsOk S = true
  idx : Mod.IdxOk S

/-- Decide the facts of `CommonOk`, from the local checks' tagged
results. -/
def commonOk (S : Mod.Store) (M : Array Mod.ModData)
    (locs : Array (Option (At fun i => Mod.localOk S i = true))) :
    Except String (PLift (CommonOk S M)) := do
  let hslots ← if h : S.slots.size = M.size then pure (PLift.up h)
    else .error "the store has a unit per module"
  let ⟨hlvls⟩ ← (allBelow M.size fun i _ =>
      if h : (S.lvl i).size = M.size then .ok ⟨h⟩ else .error s!"module {i}'s levels" :
    Except String (PLift (∀ i, i < M.size → (S.lvl i).size = M.size)))
  let ⟨hbelow⟩ ← (allBelow M.size fun i hi =>
      if h : M[i].imports.all (· < i) = true then
        .ok ⟨fun _ b hb => by simpa using List.all_eq_true.mp h b hb⟩
      else .error s!"module {i}'s imports" :
    Except String (PLift (∀ i, i < M.size → ∀ h : i < M.size, ∀ b ∈ (M[i]'h).imports, b < i)))
  let ⟨hslot⟩ ← (allBelow M.size fun i hi =>
      if h : OwnerParse.sameB (S.slot i) M[i].unit = true then
        .ok ⟨fun _ => OwnerParse.sameB_iff.mp h⟩
      else .error s!"module {i}'s published unit" :
    Except String (PLift (∀ i, i < M.size → ∀ h : i < M.size, S.slot i = (M[i]'h).unit)))
  let ⟨hpriv⟩ ← (allBelow M.size fun i hi =>
      let r : Option (PLift (M[i].unit.prv.priv = M[i].fe.env.consts.reverse.toArray)) :=
        sameArr M[i].unit.prv.priv M[i].fe.env.consts.reverse.toArray
      match r with
      | some ⟨h⟩ => .ok ⟨fun _ => h⟩
      | none => .error s!"module {i}'s unit's constants" :
    Except String (PLift (∀ i, i < M.size → ∀ h : i < M.size,
      (M[i]'h).unit.prv.priv = (M[i]'h).fe.env.consts.reverse.toArray)))
  let ⟨hulvl⟩ ← (allBelow M.size fun i hi =>
      if h : OwnerParse.sameB M[i].unit.prv.lvl (S.lvl i) = true then
        .ok ⟨fun _ => OwnerParse.sameB_iff.mp h⟩
      else .error s!"module {i}'s unit's levels" :
    Except String (PLift (∀ i, i < M.size → ∀ h : i < M.size,
      (M[i]'h).unit.prv.lvl = S.lvl i)))
  let ⟨hloc⟩ ← (allBelow M.size fun i _ =>
      match At.get? (locs[i]?.join) i with
      | some h => .ok h
      | none => .error s!"module {i}'s local checks" :
    Except String (PLift (∀ i, i < M.size → Mod.localOk S i = true)))
  let hdups ← if h : Mod.dupsOk S = true then pure (PLift.up h)
    else .error "the store's list of names stored twice"
  let hidx ← if h : Mod.idxOk S = true then pure (PLift.up (Mod.idxOk_spec h))
    else .error "the store's name index does not list every unit constant in module order"
  return ⟨{ slots := hslots.down, lvls := hlvls, below := fun i h => hbelow i h h,
            slot := fun i h => hslot i h h, priv := fun i h => hpriv i h h,
            ulvl := fun i h => hulvl i h h, locals := hloc,
            dups := hdups.down, idx := hidx.down }⟩

/-- Every slot of an array of tagged results holds its own index. -/
def indexed {β : Type} (A : Array β) (ix : β → Nat) :
    Except String (PLift (∀ k, k < A.size → ∀ h : k < A.size, ix (A[k]'h) = k)) :=
  allBelow A.size fun k hk =>
    if h : ix A[k] = k then .ok ⟨fun _ => h⟩ else .error s!"slot {k} holds module {ix A[k]}"

/-- **The store run's evidence, assembled**: from the modules' `ModOk`s
(one per module, in module order), the facts decided after every module,
and the records' checks' tagged results (`off[i]` the position of module
`i`'s first record check). -/
def runOk (mode : CheckMode) (g : Array ModIn) (S : Mod.Store) (A : Array (ModOk mode g S))
    (hc : CommonOk S (A.map ModOk.d))
    (chks : Array (Option (At (ChkP mode (A.map ModOk.d))))) (off : Array Nat) :
    Except String (PLift (Mod.RunOk mode S (A.map ModOk.d) ∧
      ∀ i (h : i < (A.map ModOk.d).size), (A.map ModOk.d)[i].ds = declsAt g i)) := do
  let M := A.map ModOk.d
  let ⟨hA⟩ ← indexed A ModOk.i
  let ⟨hchk⟩ ← (allBelow M.size fun i hi =>
      let r : Except String (PLift (∀ k, k < (M[i]'hi).pend.size → ChkP mode M (i, k))) :=
        allBelow (M[i]'hi).pend.size fun k _ =>
          match At.get? (chks[(off[i]?.getD 0) + k]?.join) (i, k) with
          | some h => .ok h
          | none => .error s!"record {k} of module {i}"
      match r with
      | .ok ⟨h⟩ => .ok ⟨fun _ => h⟩
      | .error e => .error e :
    Except String (PLift (∀ i, i < M.size → ∀ h : i < M.size, ∀ k, k < (M[i]'h).pend.size →
      ChkP mode M (i, k))))
  return ⟨{
    slots := hc.slots
    lvls := hc.lvls
    below := hc.below
    run := fun i h => (modOk_facts hA i h).1
    chk := fun i h pc hpc => by
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hpc)
      exact hchk i h h k hk h hk
    prf := fun i h => (modOk_facts hA i h).2.1
    slot := hc.slot
    priv := hc.priv
    ulvl := hc.ulvl
    unit := fun i h => (modOk_facts hA i h).2.2.1
    locals := hc.locals
    idx := hc.idx
    dups := hc.dups }, fun i h => (modOk_facts hA i h).2.2.2⟩

/-- **The isolated run's evidence, assembled**: from the modules'
`IsoModOk`s (one per module, in module order), each established by the
module's own work, and the coverage — one unit per module, the published
unit the module's data, its constants the install's, imports earlier,
levels over the run's modules — decided here.  No name index, no list of
names stored twice: nothing about the whole closure beyond the
coverage. -/
def isoRunOk (mode : CheckMode) (g : Array ModIn) (slots : Array (Thunk ModSlot))
    (A : Array (IsoModOk mode g slots)) :
    Except String (PLift (Mod.IsoRunOk mode slots (A.map IsoModOk.d) ∧
      ∀ i (h : i < (A.map IsoModOk.d).size), (A.map IsoModOk.d)[i].ds = declsAt g i)) := do
  let M := A.map IsoModOk.d
  let ⟨hA⟩ ← indexed A IsoModOk.i
  let hsz ← if h : slots.size = M.size then pure (PLift.up h)
    else .error "a unit per module"
  let ⟨hlvls⟩ ← (allBelow M.size fun i _ =>
      if h : M[i].unit.prv.lvl.size = M.size then .ok ⟨fun _ => h⟩
      else .error s!"module {i}'s levels" :
    Except String (PLift (∀ i, i < M.size → ∀ h : i < M.size, (M[i]'h).unit.prv.lvl.size = M.size)))
  let ⟨hbelow⟩ ← (allBelow M.size fun i hi =>
      if h : M[i].imports.all (· < i) = true then
        .ok ⟨fun _ b hb => by simpa using List.all_eq_true.mp h b hb⟩
      else .error s!"module {i}'s imports" :
    Except String (PLift (∀ i, i < M.size → ∀ h : i < M.size, ∀ b ∈ (M[i]'h).imports, b < i)))
  let ⟨hslot⟩ ← (allBelow M.size fun i hi =>
      if h : OwnerParse.sameB (Mod.slotOf slots i) M[i].unit = true then
        .ok ⟨fun _ => OwnerParse.sameB_iff.mp h⟩
      else .error s!"module {i}'s published unit" :
    Except String (PLift (∀ i, i < M.size → ∀ h : i < M.size, Mod.slotOf slots i = (M[i]'h).unit)))
  let ⟨hpriv⟩ ← (allBelow M.size fun i hi =>
      let r : Option (PLift (M[i].unit.prv.priv = M[i].fe.env.consts.reverse.toArray)) :=
        sameArr M[i].unit.prv.priv M[i].fe.env.consts.reverse.toArray
      match r with
      | some ⟨h⟩ => .ok ⟨fun _ => h⟩
      | none => .error s!"module {i}'s unit's constants" :
    Except String (PLift (∀ i, i < M.size → ∀ h : i < M.size,
      (M[i]'h).unit.prv.priv = (M[i]'h).fe.env.consts.reverse.toArray)))
  return ⟨{
    sizes := hsz.down
    below := fun i h => hbelow i h h
    lvls := fun i h => hlvls i h h
    slot := fun i h => hslot i h h
    priv := fun i h => hpriv i h h
    own := fun i h => (isoModOk_facts hA i h).2.1
    iso := fun i h => (isoModOk_facts hA i h).1
    unit := fun i h => (isoModOk_facts hA i h).2.2.1
    locals := fun i h => (isoModOk_facts hA i h).2.2.2.1 }, fun i h => (isoModOk_facts hA i h).2.2.2.2⟩

/-- **A modular accept** (store mode): the store and the modules' data of
a run with its evidence (`Mod.RunOk`), one module per graph module, each
one's records the graph's, the name index listing every unit constant,
every compared module's records met by its context (each compared in
its own work).  By
`Mod.RunOk.localOk` every module of the development it stands for
(`Mod.devOf`) passes its local checks — the hypothesis of the capstones
`ConLeche.modular_model_exists` and `ConLeche.modular_no_False`
(`ConLeche/MainTheorem.lean`); and it is an isolated accept
(`Accepted.isolated`), so the same holds of the isolated development
(`Accepted.localOk_iso`). -/
structure Accepted (mode : CheckMode) (g : Array ModIn) where
  S : Mod.Store
  M : Array Mod.ModData
  ok : Mod.RunOk mode S M
  size : M.size = g.size
  decls : ∀ i (h : i < M.size), M[i].ds = declsAt g i
  /-- every compared module's records are met by its context -/
  compared : ∀ i (h : i < g.size) is chal, g[i].cmp = some (is, chal) → CmpClaim mode S i chal

/-- Every module of an accept passes its local checks. -/
theorem Accepted.localOk {mode : CheckMode} {g : Array ModIn} (a : Accepted mode g) (i : Nat) :
    ConLeche.Modular.LocalOk mode natOpPinSets (Mod.devOf a.S a.M) i :=
  a.ok.localOk i

/-- **A store accept is an isolated accept**: every module checked in
isolation passes, with the same units. -/
theorem Accepted.isolated {mode : CheckMode} {g : Array ModIn} (a : Accepted mode g) :
    Mod.IsoStoreOk mode a.S a.M :=
  a.ok.isoStoreOk

/-- Every module of a store accept passes its local checks in the
isolated development. -/
theorem Accepted.localOk_iso {mode : CheckMode} {g : Array ModIn} (a : Accepted mode g) (i : Nat) :
    ConLeche.Modular.LocalOk mode natOpPinSets (Mod.isoDevOf a.S a.M) i :=
  a.isolated.localOk i

/-- **An isolated accept** (`--modular=isolated`): the published units
and the modules' data of a run with its evidence (`Mod.IsoRunOk`: every
module checked in an environment of its own, built from the units it
reads), one module per graph module, each one's records the graph's,
every compared module's records met by its context (each compared in
its own work, from the units it reads).  By
`Mod.IsoRunOk.localOk` every module of the development it stands for
(`Mod.isoRunDev`) passes its local checks. -/
structure IsoAccepted (mode : CheckMode) (g : Array ModIn) where
  slots : Array (Thunk ModSlot)
  M : Array Mod.ModData
  ok : Mod.IsoRunOk mode slots M
  size : M.size = g.size
  decls : ∀ i (h : i < M.size), M[i].ds = declsAt g i
  compared : ∀ i (h : i < M.size) is chal, (g[i]?.bind (·.cmp)) = some (is, chal) →
    IsoCmpClaim mode slots M[i].unit.prv.lvl chal

/-- Every module of an isolated accept passes its local checks. -/
theorem IsoAccepted.localOk {mode : CheckMode} {g : Array ModIn} (a : IsoAccepted mode g)
    (i : Nat) : ConLeche.Modular.LocalOk mode natOpPinSets (Mod.isoRunDev a.slots a.M) i :=
  a.ok.localOk i

/-- **An isolated accept is a store accept** at the store of its units
(which exists in the proof only: the run built no name index). -/
theorem IsoAccepted.store {mode : CheckMode} {g : Array ModIn} (a : IsoAccepted mode g) :
    ∃ M', Mod.RunOk mode (Mod.ghostStore a.slots) M' ∧
      ∀ k, Mod.devOf (Mod.ghostStore a.slots) M' k =
        Mod.devOf (Mod.ghostStore a.slots) (Mod.ghostData a.slots a.M) k :=
  a.ok.storeOk.runOk

/-! ## The run -/

/-- The first failing module of an install, in module order (a module
after a failure may never have been installed: the run stopped), with
its message; the counts under `--keep-going`. -/
def installFailure {α : Type} (g : Array ModIn) (inCtx : Nat → Name → Bool) (keepGoing : Bool)
    (results : Array (Option (ModRes α))) (fail : CheckError → String → IO UInt32)
    (modeTag : String) : IO (Option UInt32) := do
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
      return some 1
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
        let ctxK := inCtx k
        let extra := match (declsAt g k)[pos]? with
          | some (.thmDecl cv v) | some (.defnDecl cv v _) | some (.opaqueDecl cv v) =>
            let bad := (Mod.collectGo [cv.type, v] {} {}).toList.filter fun n =>
              !ctxK n && !ownNames.contains n
            if bad.isEmpty then "" else s!" (not in the module's context: {bad.take 5})"
          | _ => ""
        return some (← fail e s!"{d}module {nameOf g k}{extra}")
  for h : k in [0:results.size] do
    if results[k].isNone then
      return some (← fail (.internal "the module was never installed") s!"module {nameOf g k}")
  return none

/-- The modules' evidence in module order, or the module that has none. -/
def collectOk {α : Type} (g : Array ModIn) (results : Array (Option (ModRes α))) :
    Except String (Array α) := do
  let mut A : Array α := #[]
  for h : k in [0:results.size] do
    match results[k] with
    | some ⟨_, _, _, .ok e⟩ => A := A.push e
    | _ => throw s!"module {nameOf g k}"
  return A

/-- **The local checks of every module**, in parallel, tagged; the first
failing module's message. -/
def localChecks (g : Array ModIn) (S : Mod.Store) (M : Array Mod.ModData) (jobs : Nat) :
    IO (Except (String × Nat) (Array (Option (At fun i => Mod.localOk S i = true)))) := do
  let locals ← parMap jobs M.size fun i =>
    if h : Mod.localOk S i = true then
      some (⟨i, h⟩ : At fun i => Mod.localOk S i = true)
    else none
  for h : k in [0:locals.size] do
    if locals[k].isNone then
      return .error (localWhy g S k, k)
  return .ok locals

/-- The comparisons' report, in module order: per challenge its solution,
its records and the holes it filled, each with the module its context
reads it from. -/
def reportCompared (g : Array ModIn) (cmps : Array (Nat × Array (Name × Nat))) : IO Unit := do
  for (i, filled) in cmps do
    if let some (is, chal) := g[i]?.bind (·.cmp) then
      IO.println s!"con-leche: {nameOf g i} compared with {nameOf g is}: {chal.size} records, \
        {filled.size} holes"
      for (n, h) in filled do
        IO.println s!"con-leche:   hole {n} filled by {nameOf g h}"

/-- **The modular run**: read, build the graph and the store, install
every module, compute the requirements, run the local checks and every
record's check; the verdict line and the exit code.  `isolated`
(`--modular=isolated`): every module is installed and its records
checked in an environment of its own, built from its imports' units
(`Mod.isoCtx`) and dropped after its checks, instead of at its view of
the store; everything else is the same. -/
def checkModular (sp : SearchPath) (roots : Array Name) (mode : CheckMode) (stride jobs : Nat)
    (keepGoing : Bool := false) (cmps : Array (Name × Name) := #[]) (isolated : Bool := false) :
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
  let roots := cmps.foldl (fun r (c, s) => r.push c |>.push s) roots
  let rs ← match ← readClosure decodeModuleSpec sp roots jobs with
    | .ok rs => pure rs
    | .error e => return ← fail e "reading the oleans"
  let rs ← match addCompares rs cmps with
    | .ok rs => pure rs
    | .error msg => return ← fail (.internal msg) "--compare"
  phase s!"read {rs.size} modules"
  let g ← match buildGraph pre rs with
    | .ok g => pure g
    | .error (e, m) => return ← fail e s!"module {m}"
  -- the compared modules: their records set aside, their solution noted
  let gpos : Std.HashMap Name Nat := g.size.fold (init := {}) fun i _ m => m.insert g[i].name i
  let mut cmpIx : Array (Nat × Nat) := #[]
  let mut g := g
  for (c, s) in cmps do
    match gpos[c]?, gpos[s]? with
    | some ic, some is =>
      cmpIx := cmpIx.push (ic, is)
      g := g.modify ic fun m => { m with cmp := some (is, m.decls), decls := #[] }
    | _, _ => return ← fail (.internal s!"{c} or {s} is not in the graph") "--compare"
  -- a challenge's own context, for the install of its records: its
  -- levels without the import of its solution
  let sideLvls : Array ByteArray := cmpIx.map fun (ic, is) =>
    levelsOf (g.modify ic fun m => { m with imports := m.imports.filter (·.1 != is) }) ic
  let sideLv (i : Nat) : ByteArray := ((cmpIx.findIdx? (·.1 == i)).bind (sideLvls[·]?)).getD .empty
  -- the graph lives to the end and every worker reads it (its names are
  -- hash-consed across modules): persistent before any worker starts, so
  -- that no later mark (an installed unit's) reaches a counted object
  -- another thread is counting
  OwnerParse.markOne g
  let nDecls := g.foldl (· + ·.decls.size) 0
  let lvls ← parMap jobs g.size (levelsOf g)
  -- the levels live to the end and are read by every worker: persistent,
  -- so that no lookup counts references on them
  OwnerParse.markOne lvls
  let proms ← g.mapM fun _ => IO.Promise.new
  let slots : Array (Thunk ModSlot) := proms.map fun p => Thunk.mk fun _ => (p.result?.get).getD {}
  let diagOf {α : Type} (results : Array (Option (ModRes α))) : IO Unit := do
    if stride > 0 then
      let dg : Diag := results.foldl (fun (d : Diag) r? => d.merge ((r?.map (·.diag)).getD {})) {}
      err.putStr s!"con-leche: exported presentations: assumption {dg.assumed}, absent {dg.absent}, \
        gated {dg.gated}, full-gated {dg.vgated}\n"
      for x in dg.ex do err.putStr s!"con-leche:   {x}\n"
      for x in dg.indEx do err.putStr s!"con-leche:   {x}\n"
  if isolated then
    -- every module in an environment of its own, from the units it reads:
    -- no name index, nothing about the whole closure
    phase s!"graph: {g.size} modules, {nDecls} records"
    let lvlOf (k : Nat) : ByteArray := (lvls[k]?).getD .empty
    let inCtx (k : Nat) : Name → Bool :=
      let a := Mod.isoBuild (Mod.mask (Mod.slotOf slots) (lvlOf k)) (lvlOf k)
      fun n => (a.fenv.find? n).isSome
    let results ← installAll err jobs g proms keepGoing (isoWork mode err g slots lvls sideLv)
      (fun a => markData a.d)
    if let some code ← installFailure g inCtx keepGoing results fail modeTag then return code
    phase "modules checked in isolation"
    diagOf results
    let A ← match collectOk g results with
      | .ok A => pure A
      | .error m => return ← fail (.internal "the module was never installed") m
    let M : Array Mod.ModData := A.map IsoModOk.d
    match isoRunOk mode g slots A with
    | .error msg => fail (.internal s!"the run's evidence: {msg}") "the run"
    | .ok ⟨⟨hR, hds⟩⟩ =>
      if hs : M.size = g.size then
        match indexed A IsoModOk.i with
        | .error msg => fail (.internal s!"the run's evidence: {msg}") "the run"
        | .ok ⟨hA⟩ =>
          have hcmp : ∀ i (h : i < M.size) is chal, (g[i]?.bind (·.cmp)) = some (is, chal) →
              IsoCmpClaim mode slots M[i].unit.prv.lvl chal := fun i h is chal hc => by
            have h' : i < A.size := by simpa [M] using h
            have := A[i].cmp is chal (by rw [hA i h' h']; exact hc)
            simpa [M] using this
          let acc : IsoAccepted mode g := ⟨slots, M, hR, hs, hds, hcmp⟩
          reportCompared g (A.map fun a => (a.i, a.filled))
          IO.println s!"con-leche: accepted {nDecls} declarations in {acc.M.size} modules, \
            each checked in isolation ({modeTag})"
          return 0
      else fail (.internal "the run lost a module") "the run"
  else
  let (idx, dupArr) := buildIdx g
  phase s!"graph: {g.size} modules, {nDecls} records, {dupArr.size} names stored twice"
  -- the index lives to the end and is read by every worker: persistent,
  -- so that no lookup counts references on it (the slots are thunks over
  -- the units' promises, which the mark would wait for)
  OwnerParse.markOne idx
  let S : Mod.Store := { idx, dups := dupArr, slots, lvls }
  let results ← installAll err jobs g proms keepGoing (storeWork mode err g S sideLv)
    (fun a => markData a.d)
  if let some code ← installFailure g (fun k n => ((S.view k).find? n).isSome) keepGoing results
      fail modeTag then return code
  phase "install done"
  diagOf results
  -- the modules' data in module order, each with its evidence
  let A ← match collectOk g results with
    | .ok A => pure A
    | .error m => return ← fail (.internal "the module was never installed") m
  let M : Array Mod.ModData := A.map ModOk.d
  let locs ← match ← localChecks g S M jobs with
    | .ok l => pure l
    | .error (why, k) => return ← fail (.invalid why) s!"module {nameOf g k}"
  phase "local checks done"
  -- every record of every module, checked at its module's final view
  let (jobsList, off) : Array (Nat × Nat) × Array Nat := Id.run do
    let mut a := #[]
    let mut off := #[]
    for h : i in [0:M.size] do
      off := off.push a.size
      for k in [0:M[i].pend.size] do a := a.push (i, k)
    return (a, off)
  phase s!"{jobsList.size} checks"
  let chk ← parMap jobs jobsList.size fun q =>
    (some <| match jobsList[q]? with
      | some (i, k) =>
        if hi : i < M.size then
          if hk : k < M[i].pend.size then
            match hc : checkPending mode M[i].fe M[i].pend[k] {} with
            | .ok ((), st) => .ok (⟨(i, k), fun _ _ => ⟨st, hc⟩⟩ : At (ChkP mode M))
            | .error e => .error (e, i, k)
          else .error (.internal "no such record", i, k)
        else .error (.internal "no such module", i, k)
      | none => .error (.internal "no such check", 0, 0) :
      Option (Except (CheckError × Nat × Nat) (At (ChkP mode M))))
  let mut nBad := 0
  for h : q in [0:chk.size] do
    if let some (.error (e, i, k)) := chk[q] then
      nBad := nBad + 1
      let pc? := (M[i]?).bind (·.pend[k]?)
      let nm := pc?.map (·.vg.cv.name) |>.getD .anonymous
      -- the names that do not resolve, for an unknown-constant rejection
      let extra := match pc?, M[i]? with
        | some pc, some d =>
          let bad := (Mod.collectGo [pc.vg.cv.type, pc.vg.jv] {} {}).toList.filter
            fun x => ((d.fe.restrictTo pc.vis).find? x).isNone
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
  let chks : Array (Option (At (ChkP mode M))) := chk.map fun r => match r with
    | some (.ok c) => some c
    | _ => none
  -- **the accept is printed from the run's evidence and from nothing
  -- else**: `runOk` assembles `Mod.RunOk`, whose theorem
  -- `Mod.RunOk.localOk` is the capstones' hypothesis
  match commonOk S M locs with
  | .error msg => fail (.internal s!"the run's evidence: {msg}") "the run"
  | .ok ⟨hc⟩ =>
  match runOk mode g S A hc chks off with
  | .error msg => fail (.internal s!"the run's evidence: {msg}") "the run"
  | .ok ⟨⟨hR, hds⟩⟩ =>
    if hs : M.size = g.size then
      match indexed A ModOk.i with
      | .error msg => fail (.internal s!"the run's evidence: {msg}") "the run"
      | .ok ⟨hA⟩ =>
        have hcmp : ∀ i (h : i < g.size) is chal, g[i].cmp = some (is, chal) →
            CmpClaim mode S i chal := fun i h is chal hc => by
          have h' : i < A.size := by
            have e : A.size = g.size := by simpa [M] using hs
            omega
          have := A[i].cmp is chal (by rw [hA i h' h']; simp [h, hc])
          rwa [hA i h' h'] at this
        let acc : Accepted mode g := ⟨S, M, hR, hs, hds, hcmp⟩
        reportCompared g (A.map fun a => (a.i, a.filled))
        IO.println s!"con-leche: accepted {nDecls} declarations in {acc.M.size} modules ({modeTag})"
        return 0
    else fail (.internal "the run lost a module") "the run"

end ConLeche.Driver.Modular
