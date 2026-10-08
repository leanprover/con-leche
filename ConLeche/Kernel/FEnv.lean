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

/-- **A frozen, task-valued lookup layer** (task #329): the name index of
a parallel install's predicted slots, built once before the workers
start and never written again.  An entry `n ↦ (c, j, t)` says that the
constant named `n` is the `j`-th constant installed by some record,
whose installed constants the task `t` delivers, and that it gets the
installation counter `c`; it is visible to lookups below the bound
`below` only.  A lookup of a visible entry waits for `t` — the record
that installs it is below the looker in the stream, so the wait is on
an earlier record, never on the looker itself.

Logically `Task.get` is a projection, so `find?` is an ordinary
function of the layer's contents; the empty layer answers `none`
everywhere (`FBase.find?_empty`), which is every `FEnv` but a worker's
view. -/
structure FBase where
  idx : Std.HashMap Name (Nat × Nat × Task (Array ConstantInfo)) := {}
  below : Nat := 0

/-- The base layer's lookup: a visible entry's constant, from its
record's task. -/
def FBase.find? (b : FBase) (n : Name) : Option ConstantInfo :=
  match b.idx[n]? with
  | some (c, j, t) => if c < b.below then t.get[j]? else none
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

/-- Build the index of `env`, with nothing hidden (`visibleBelow` is the
constant count). -/
def mkFEnv (env : Env) : FEnv :=
  let p := mkFEnvGo env.consts
  ⟨env, p.2, p.1, {}, []⟩

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
`FEnv.push (mkFEnv env) ci = mkFEnv ⟨ci :: env.consts⟩`, definitionally).
The new entry gets the next installation counter, and the visibility
bound advances with it — so a push is visible to everything checked
after it and to nothing checked before (task #108). -/
def push (fe : FEnv) (ci : ConstantInfo) : FEnv :=
  ⟨⟨ci :: fe.env.consts⟩, fe.idx.insert ci.name (fe.visibleBelow, ci),
   fe.visibleBelow + 1, fe.base, fe.ovl⟩

/-- **Cons `new` (newest first) as an overlay** (task #329): the
environment `new` pushed onto `fe` would be (`find?_overlay`, for an
`fe` without an overlay), with the index SHARED, not mutated — two live
environments, one bucket array.  Read-only: the install never pushes
onto it. -/
def overlay (fe : FEnv) (new : List ConstantInfo) : FEnv :=
  ⟨⟨new ++ fe.env.consts⟩, fe.idx, fe.visibleBelow, fe.base, new ++ fe.ovl⟩

/-- Indexed projection-table lookup (`= Env.findProj?` for `mkFEnv`). -/
def findProj? (fe : FEnv) (T : Name) (i : Nat) : Option ProjEntry :=
  match fe.find? (projTableName T) with
  | some (.projInfo tbl) => if i < tbl.numFields then some (tbl.entry i) else none
  | _ => none

/-- `towerSlotsAll` through the index. -/
def towerSlotsAllF (fe : FEnv) (T : Name) (nF : Nat) : Bool :=
  (List.range nF).all fun j => (fe.findProj? T j).isSome

/-- `andRescueSlots` through the index. -/
def andRescueSlotsF (fe : FEnv) (ctor : Name) (nP : Nat) (ust : List Level) : Bool :=
  andRescueSlotsOf fe.findProj? ctor nP ust

/-- `recSlotsAll` through the index. -/
def recSlotsAllF (fe : FEnv) (T : Name) (nF : Nat) : Bool :=
  (List.range nF).all fun j =>
    match fe.find? (projFnName T j) with
    | some (.recInfo _ _ _ _) => true
    | _ => false

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
      | some ci => ci.toConstantVal.levelParams.isEmpty
      | none => false) &&
    (match fe.find? boolFalseName with
      | some ci => ci.toConstantVal.levelParams.isEmpty
      | none => false)
   else true)

/-- `natOpStored` through the index (task #161 item B3). -/
def natOpStoredF (fe : FEnv) (c : Name) : Bool :=
  match fe.find? c with
  | some (.defnInfo _ _ _) => true
  | _ => false
end ConLeche
