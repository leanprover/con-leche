module

public import ConLeche.Kernel.Core

@[expose] public section

/-!
# `FEnv`: the environment with a name index

The spec environment together with a name index whose lookup function
agrees with `Env.find?`, built once per top-level entry call, plus the
`Env`-guard twins that read through it (`natLitSupportedF`,
`strLitSupportedF`, `natOpGuardF`, `natOpStoredF`).

**Representation-free.**  Nothing here mentions an expression
representation: `FEnv` indexes `ConstantInfo`s by `Name`, and the four
guards ask only about the constants an environment holds.  Both
executable cores read the environment through it, and the F-mirror
agreement (`ConLeche/Verify/EnvBound.lean`) is stated about it.  The
`F` suffix on the guards reads "through the index".
-/

namespace ConLeche
/-! ## The frozen base layer -/

/-- The shard a name's base entry lives in, among `m` shards: the high
half of its hash, modulo `m` (the low bits choose the bucket inside a
shard's map). -/
@[inline] def baseShard (n : Name) (m : Nat) : Nat := (n.hashData >>> 32).toNat % m

/-- **A module's interface** (task #370): what a module loading it at its
exported level reads, and nothing else — for each of the module's
installed constants, in push order: its presentation (`at1`: the
constant, the assumption of its statement, or `none`), whether that is
the constant as stored (`stored`), the projection table of a structure
presented as stored (`tbls`), the **gates** (`g1`: the modules, with a
level at each, that a viewer must load for the constant to be presented
at all; `v1`: for it to be presented as stored, beyond that), and
whether it is a proof (`prf`: its qualified name is its statement); and
the modules, with a level at each, that its presentations read and that
every importer at the exported level loads by Lean's rules (`fp1`: the
importer checks that it does, task #374). -/
structure ModIface where
  at1 : Array (Option ConstantInfo) := #[]
  stored : Array Bool := #[]
  tbls : Array (Option ProjTable) := #[]
  g1 : Array (Array (Nat × UInt8)) := #[]
  v1 : Array (Array (Nat × UInt8)) := #[]
  prf : Array Bool := #[]
  fp1 : Array (Nat × UInt8) := #[]
  deriving DecidableEq, Inhabited

/-- **A module's private record** (task #370): the constants its install
pushed, in push order, with their projection tables, and the module's
own level of every module (`lvl`, as in `MBase.lvl`: an `import all`
importer checks that it loads that context at least as high, task #374) —
what a module loading it with `import all` reads. -/
structure ModPriv where
  priv : Array ConstantInfo := #[]
  tbls : Array (Option ProjTable) := #[]
  lvl : ByteArray := ByteArray.empty
  deriving DecidableEq, Inhabited

/-- **One module's unit, published**: its interface and its private
record, two separate objects (the boundary between what an ordinary
importer and an `import all` importer reads is a property of the data). -/
structure ModSlot where
  exp : ModIface := {}
  prv : ModPriv := {}
  deriving DecidableEq, Inhabited

/-- **The module store, as one module sees it** (task #370): the store's
name index — every name with the modules storing it and its position
among each one's installed constants, sharded by name hash
(`baseShard`) — the modules' published slots, and the VIEWING module's
level of every module: `0` not loaded, `1` its exported part, `2` its
private part.  A lookup answers the first alternate the viewer loads at
a level that stores it; the name index and the slots are shared by
every view, the level array is the view's own. -/
structure MBase where
  idx : Array (Std.HashMap Name (List (Nat × Nat))) := #[]
  slots : Array (Thunk ModSlot) := #[]
  lvl : ByteArray := ByteArray.empty

/-- A gate is open for the viewer: it loads every listed module at least
at the listed level. -/
@[inline] def MBase.gateOk (b : @& MBase) (g : Array (Nat × UInt8)) : Bool :=
  g.all fun (h, l) => (if hl : h < b.lvl.size then b.lvl[h]'hl else 0) ≥ l

/-- The constant module `h` stores at position `j`, at the viewer's level
of `h` (at the exported level, through its gates). -/
@[inline] def MBase.at? (b : @& MBase) (h j : Nat) : Option ConstantInfo :=
  if hl : h < b.lvl.size then
    let l := b.lvl[h]'hl
    if l == 2 then
      if hh : h < b.slots.size then (b.slots[h]).get.prv.priv[j]? else none
    else if l == 1 then
      if hh : h < b.slots.size then
        let s := (b.slots[h]).get.exp
        match (s.at1[j]?).join with
        | some ci =>
          if b.gateOk ((s.g1[j]?).getD #[]) then
            if b.gateOk ((s.v1[j]?).getD #[]) then some ci
            else some (.axiomInfo ci.toConstantVal)
          else none
        | none => none
      else none
    else none
  else none

/-- The first visible alternate of a name: its home module, its position
there and its constant.  A constant answers for `n` only if it is named
`n`. -/
def MBase.pickIn (b : @& MBase) (n : Name) :
    List (Nat × Nat) → Option (Nat × Nat × ConstantInfo)
  | [] => none
  | (h, j) :: rest =>
    match b.at? h j with
    | some ci => if ci.name == n then some (h, j, ci) else b.pickIn n rest
    | none => b.pickIn n rest

/-- The alternates of a name in the store's index. -/
@[inline] def MBase.alts (b : @& MBase) (n : Name) : List (Nat × Nat) :=
  match b.idx[baseShard n b.idx.size]? with
  | some m => m.getD n []
  | none => []

/-- **The view's lookup**: the first alternate the viewer sees. -/
def MBase.pick? (b : @& MBase) (n : Name) : Option (Nat × Nat × ConstantInfo) :=
  b.pickIn n (b.alts n)

def MBase.find? (b : @& MBase) (n : Name) : Option ConstantInfo :=
  match b.pick? n with
  | some (_, _, ci) => some ci
  | none => none

/-- The view's table lookup: the table of `T` its visible alternate's
module installed, when the alternate is presented as the type former it
is (an assumed former has no table). -/
def MBase.findTable? (b : @& MBase) (T : Name) : Option ProjTable :=
  match b.pick? T with
  | some (h, j, .indInfo ..) =>
    if hh : h < b.slots.size then
      let t? := if hl : h < b.lvl.size then
          if b.lvl[h]'hl == 2 then (b.slots[h]).get.prv.tbls[j]? else (b.slots[h]).get.exp.tbls[j]?
        else none
      match t?.join with
      | some t => if t.structName == T then some t else none
      | none => none
    else none
  | _ => none

/-- **A frozen lookup layer of deferred slots** (task #329): the name
index of a parallel install's predicted slots, built once before the
workers start and never written again.  An entry `n ↦ (c, k, j)` says
that the constant named `n` gets the installation counter `c` and is
the `j`-th constant record `k` installs; `slots[k]` is a thunk that
delivers record `k`'s installed constants and projection tables, each
in install order (forcing it waits for the record's installer to
publish them).  An entry is visible to lookups
below the bound `below` only, so a lookup waits only on an earlier
record, never on the looker itself.

The index holds no thunk (only numbers and names), so it can be marked
persistent before the workers start; the thunks sit in their own array
and are read borrowed, so a lookup counts no reference on them.
Logically `Thunk.get` is a projection, so `find?` is an ordinary
function of the layer's contents; the empty layer answers `none`
everywhere (`FBase.find?_empty`), which is every `FEnv` but a worker's
view. -/
structure FBase where
  idx : Array (Std.HashMap Name (Nat × Nat × Nat)) := #[]
  slots : Array (Thunk (Array ConstantInfo × List ProjTable)) := #[]
  below : Nat := 0
  /-- The module store a modular run's views read (`MBase`, task #370):
  when present, it answers instead of the three fields above. -/
  mb : Option MBase := none


/-- **The sharded base index's lookup**: the entry for `n` in its
shard.  The base is built one shard per task (task #329, COMMIT); no
lemma depends on which shard an entry sits in, only on what the
entries say (`buildBase_inj`), so a misplaced entry would be a miss,
never a wrong answer. -/
def baseGet? (idx : Array (Std.HashMap Name (Nat × Nat × Nat))) (n : Name) :
    Option (Nat × Nat × Nat) :=
  match idx[baseShard n idx.size]? with
  | some m => m[n]?
  | none => none

/-- The base layer's lookup: a visible entry's constant, from its
record's slot. -/
def FBase.find? (b : FBase) (n : Name) : Option ConstantInfo :=
  match b.mb with
  | some m => m.find? n
  | none =>
  match baseGet? b.idx n with
  | some (c, k, j) =>
    if c < b.below then
      if h : k < b.slots.size then (b.slots[k]).get.1[j]? else none
    else none
  | none => none

/-- The last table of `T` in a list of tables in install order: the one
installed last, which a table map built by inserting them in order
holds. -/
def ProjTable.lastOf? (T : Name) : List ProjTable → Option ProjTable
  | [] => none
  | t :: ts =>
    match ProjTable.lastOf? T ts with
    | some r => some r
    | none => if t.structName == T then some t else none

/-- The base layer's table lookup (task #362): the table of `T` among
the tables of the record that installs `T` — a table is installed by
its structure's record — visible where `T` is. -/
def FBase.findTable? (b : FBase) (T : Name) : Option ProjTable :=
  match b.mb with
  | some m => m.findTable? T
  | none =>
  match baseGet? b.idx T with
  | some (c, k, _) =>
    if c < b.below then
      if h : k < b.slots.size then ProjTable.lastOf? T (b.slots[k]).get.2 else none
    else none
  | none => none

/-! ## The indexed environment -/

/-- The spec environment together with a name index whose lookup function
agrees with `Env.find?` (built once per top-level entry call).

Every index entry carries its **installation counter** — the number of
constants installed before it, i.e. its position counted from the bottom
of `env.consts` — and the environment carries a **visibility bound**,
`visibleBelow`: `find?` returns `none` for an entry whose counter is at
or above the bound, so a single `FEnv` value answers lookups against any
*prefix* of itself at `O(1)` (task #108; a field comparison on the entry
— never a filtered copy or a second environment value).  `visibleBelow`
doubles as the next counter to hand out, so on the ordinary
install-and-check path it is exactly `env.consts.length` and nothing is
ever hidden (`mkFEnv_find?`); lowering it to `k` is the prefix view of
the first `k` installed constants (`mkFEnv_find?_visibleBelow`,
`ConLeche/Verify/EnvBound.lean`). -/
structure FEnv where
  env : Env
  idx : Std.HashMap Name (Nat × ConstantInfo)
  /-- Entries with counter `< visibleBelow` are visible; also the next
  counter `push` hands out. -/
  visibleBelow : Nat
  /-- The frozen lookup layer under the index (`FBase`): consulted on an
  index miss.  Empty everywhere except in a parallel install's worker
  views; `mkFEnv`, `push` and `restrictTo` leave it as it is. -/
  base : FBase
  /-- The **overlay** (task #329): constants consed onto `env` WITHOUT
  entering the index, newest first (`overlay`).  Empty on every
  environment the install threads (`mkFEnv`, `push`); non-empty only on
  the inductive block's rule-less-recursor environment, a read-only view
  that shares the constructors' index instead of copying it.  `find?`
  reads it before the index, as if its constants had been pushed
  (`find?_overlay_pushAll`, `ConLeche/Verify/Cached/BlockOverlay.lean`). -/
  ovl : List ConstantInfo
  /-- **The projection tables** (task #362), keyed on the structure's
  name: `env.tables` as a map (the newest table of a name wins, as
  `List.find?` takes the first).  No counter: a table is visible
  exactly where its structure is (`findTable?`), so the prefix and
  worker views need nothing of their own for it. -/
  tbls : Std.HashMap Name ProjTable

/-- The index build, from the back: the newest (front) constant is
inserted last and wins, exactly as `List.find?` takes the first match —
so the agreement with `Env.find?` is unconditional (no freshness
assumption).  The `Nat` component is the running counter, so the build
stays linear (the tail's length is returned, not recomputed). -/
def mkFEnvGo : List ConstantInfo → Nat × Std.HashMap Name (Nat × ConstantInfo)
  | [] => (0, ∅)
  | ci :: cs =>
    let p := mkFEnvGo cs
    (p.1 + 1, p.2.insert ci.name (p.1, ci))

/-- The table map's build, from the back: the newest (front) table is
inserted last and wins, exactly as `List.find?` takes the first. -/
def mkTblsGo : List ProjTable → Std.HashMap Name ProjTable
  | [] => ∅
  | t :: ts => (mkTblsGo ts).insert t.structName t

/-- Build the index of `env`, with nothing hidden (`visibleBelow` is the
constant count). -/
def mkFEnv (env : Env) : FEnv :=
  let p := mkFEnvGo env.consts
  ⟨env, p.2, p.1, {}, [], mkTblsGo env.tables⟩

namespace FEnv

/-- Indexed lookup, bounded by the visibility counter (`= Env.find?` for
`mkFEnv`, which hides nothing); an index miss falls through to the base
layer (empty but in a worker's view).  With an overlay, the overlay
first and the bound advanced past it — exactly what pushing the
overlay's constants would answer.  `fe` is borrowed: the overlay branch
otherwise makes the compiler take it owned, reference-count traffic on
every lookup. -/
def find? (fe : @& FEnv) (n : Name) : Option ConstantInfo :=
  match fe.ovl with
  | [] =>
    match fe.idx[n]? with
    | some (c, ci) => if c < fe.visibleBelow then some ci else none
    | none => fe.base.find? n
  | ovl@(_ :: _) =>
    match ovl.find? (·.name == n) with
    | some ci => some ci
    | none =>
      match fe.idx[n]? with
      | some (c, ci) => if c < fe.visibleBelow + ovl.length then some ci else none
      | none => fe.base.find? n

/-- Restrict the view to the first `k` installed constants (task #108).
`O(1)`: a field update on the single linearly-threaded index. -/
def restrictTo (fe : FEnv) (k : Nat) : FEnv :=
  { fe with visibleBelow := k }

/-- The index of the cons-extended environment (`push_mkFEnv`:
`FEnv.push (mkFEnv env) ci = mkFEnv ⟨ci :: env.consts, env.tables⟩`,
definitionally).
The new entry gets the next installation counter, and the visibility
bound advances with it — so a push is visible to everything checked
after it and to nothing checked before (task #108). -/
def push (fe : FEnv) (ci : ConstantInfo) : FEnv :=
  ⟨⟨ci :: fe.env.consts, fe.env.tables⟩, fe.idx.insert ci.name (fe.visibleBelow, ci),
   fe.visibleBelow + 1, fe.base, fe.ovl, fe.tbls⟩

/-- **Install a projection table** (task #362): the table component
extended, the constant index untouched (`pushTable_mkFEnv`:
`FEnv.pushTable (mkFEnv env) t = mkFEnv ⟨env.consts, t :: env.tables⟩`,
definitionally). -/
def pushTable (fe : FEnv) (t : ProjTable) : FEnv :=
  ⟨⟨fe.env.consts, t :: fe.env.tables⟩, fe.idx, fe.visibleBelow, fe.base, fe.ovl,
   fe.tbls.insert t.structName t⟩

/-- Install a list of tables, head first (as `FEnv.pushAll` pushes
constants): `(pushTables Q fe).env.tables = Q.reverse ++ fe.env.tables`.
Tail-recursive, so the index is threaded owned. -/
def pushTables : List ProjTable → FEnv → FEnv
  | [], fe => fe
  | t :: Q, fe => pushTables Q (fe.pushTable t)

/-- **Cons `new` (newest first) as an overlay** (task #329): the
environment `new` pushed onto `fe` would be (`find?_overlay`, for an
`fe` without an overlay), with the index SHARED, not mutated — two live
environments, one bucket array.  Read-only: the install never pushes
onto it. -/
def overlay (fe : FEnv) (new : List ConstantInfo) : FEnv :=
  ⟨⟨new ++ fe.env.consts, fe.env.tables⟩, fe.idx, fe.visibleBelow, fe.base, new ++ fe.ovl,
   fe.tbls⟩

/-- **Mark the index linear** (task #331): the identity
(`markLinear_eq`), which at run time also sets the runtime's linearity
bit on the index's bucket array (`Std.HashMap.markLinear`).  From then
on a copy of that array — an insert while a second reference to the
index is alive — panics (the binary sets `LEAN_ABORT_ON_NONLINEAR`,
`Main.lean`) instead of silently copying a million-slot array.  Applied
at the install driver's start, never inside `mkFEnv`: `mkFEnv
Env.empty` is a closed term, persistent, and a persistent array is
copied on its first insert by design.  `@[never_extract]` keeps an
application to a closed argument from being hoisted into a persistent
closed term itself.  The table map is marked too: it is threaded the
same way. -/
@[never_extract, noinline]
def markLinear (fe : FEnv) : FEnv :=
  { fe with idx := fe.idx.markLinear, tbls := fe.tbls.markLinear }

theorem markLinear_eq (fe : FEnv) : fe.markLinear = fe := rfl

/-- The table map's lookup, ungated: a miss in the map falls through to
the base layer (empty but in a worker's view). -/
def rawTable? (fe : FEnv) (T : Name) : Option ProjTable :=
  match fe.tbls[T]? with
  | some t => some t
  | none => fe.base.findTable? T

/-- **The table lookup** (task #362): `T`'s table, visible exactly
where the constant `T` is — the table map holds every installed table,
and the prefix views (`restrictTo`) and the worker views hide a table by
hiding its structure (`= Env.findTable?` for `mkFEnv`,
`mkFEnv_findTable?`). -/
def findTable? (fe : FEnv) (T : Name) : Option ProjTable :=
  if (fe.find? T).isSome then fe.rawTable? T else none

/-- Indexed projection-table lookup (`= Env.findProj?` for `mkFEnv`). -/
def findProj? (fe : FEnv) (T : Name) (i : Nat) : Option ProjEntry :=
  match fe.findTable? T with
  | some tbl => if i < tbl.numFields then some (tbl.entry i) else none
  | none => none

/-- `towerSlotsAll` through the index. -/
def towerSlotsAllF (fe : FEnv) (T : Name) (nF : Nat) : Bool :=
  (List.range nF).all fun j => (fe.findProj? T j).isSome

/-- `andRescueSlots` through the index. -/
def andRescueSlotsF (fe : FEnv) (ctor : Name) (nP : Nat) (ust : List Level) : Bool :=
  andRescueSlotsOf fe.findProj? ctor nP ust

end FEnv

/-! ### Indexed guard twins (same result as the `Env` versions) -/

/-- `natLitSupported` through the index. -/
def natLitSupportedF (fe : FEnv) : Bool :=
  natIndOk (fe.find? natName) && natZeroOk (fe.find? natZeroName) &&
    natSuccOk (fe.find? natSuccName)

/-- `strLitSupported` through the index. -/
def strLitSupportedF (fe : FEnv) : Bool :=
  natLitSupportedF fe &&
    stringTyOk (fe.find? stringName) &&
    stringOfListTyOk (fe.find? stringOfListName) &&
    listTyOk (fe.find? listName) &&
    listNilTyOk (fe.find? listNilName) &&
    listConsTyOk (fe.find? listConsName) &&
    charTyOk (fe.find? charName) &&
    charOfNatTyOk (fe.find? charOfNatName)

/-- `natOpGuard` through the index. -/
def natOpGuardF (fe : FEnv) (c : Name) : Bool :=
  natLitSupportedF fe &&
  (natOpDeps c).all (fun n => match fe.find? n with
    | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
    | _ => false) &&
  (if c = natBeqName || c = natBleName || natDivModNames.contains c then
    (match fe.find? boolTrueName with
      | some ci => ci.toConstantVal.levelParams.isEmpty &&
          ci.toConstantVal.type == .const boolName []
      | none => false) &&
    (match fe.find? boolFalseName with
      | some ci => ci.toConstantVal.levelParams.isEmpty &&
          ci.toConstantVal.type == .const boolName []
      | none => false)
   else true)

/-- `natOpStored` through the index (task #161 item B3). -/
def natOpStoredF (fe : FEnv) (c : Name) : Bool :=
  match fe.find? c with
  | some (.defnInfo _ _ _) => true
  | _ => false
end ConLeche
