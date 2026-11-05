module

public import ConLeche.Kernel.Core

@[expose] public section

/-!
# `FEnv`: the environment with a name index

The spec environment together with a name index whose lookup function
agrees with `Env.find?`, built once per top-level entry call, plus the
`Env`-guard twins that read through it (`natLitStoredF`,
`strLitStoredF`, `natOpGuardF`).

**Representation-free.**  Nothing here mentions an expression
representation: `FEnv` indexes `ConstantInfo`s by `Name`, and the four
guards ask only about the constants an environment holds.  Both
executable cores read the environment through it, and the F-mirror
agreement (`ConLeche/Verify/EnvBound.lean`) is stated about it.  The
`F` suffix on the guards reads "through the index".
-/

namespace ConLeche
/-! ## The frozen base layer -/

/-- **A frozen lookup layer**: the index of a whole stream, built once
before any record is checked and never written again
(`ConLeche/Cached/StreamIndex.lean`).  An entry `n ↦ (c, ci)` says that
the first constant named `n` in the stream is `ci`, at counter `c`; an
entry `T ↦ (r, t)` says that the first table of `T` is `t`, of record `r`.
A view of the stream below a record reads the entries below that record's
first counter `below` and that record's position `belowRec` only.  The
empty layer answers `none` everywhere (`FBase.find?_empty`). -/
structure FBase where
  idx : Std.HashMap Name (Nat × ConstantInfo) := {}
  tbls : Std.HashMap Name (Nat × ProjTable) := {}
  below : Nat := 0
  belowRec : Nat := 0

/-- The base layer's lookup: a visible entry's constant. -/
def FBase.find? (b : @& FBase) (n : Name) : Option ConstantInfo :=
  match b.idx[n]? with
  | some (c, ci) => if c < b.below then some ci else none
  | none => none

/-- The base layer's table lookup: a visible entry's table. -/
def FBase.findTable? (b : @& FBase) (T : Name) : Option ProjTable :=
  match b.tbls[T]? with
  | some (r, t) => if r < b.belowRec then some t else none
  | none => none

/-! ## The indexed environment -/

/-- The spec environment together with a name index whose lookup function
agrees with `Env.find?` (built once per top-level entry call), over the
frozen layer of a stream's index (`base`). -/
structure FEnv where
  env : Env
  idx : Std.HashMap Name ConstantInfo
  /-- The frozen lookup layer under the index (`FBase`): consulted on an
  index miss.  Empty everywhere except in a view of a stream's index;
  `mkFEnv` and `push` leave it as it is. -/
  base : FBase
  /-- The **overlay**: constants consed onto `env` WITHOUT
  entering the index, newest first (`overlay`).  Empty on every
  environment a step threads (`mkFEnv`, `push`); non-empty only on
  the inductive block's rule-less-recursor environment, a read-only view
  that shares the constructors' index instead of copying it.  `find?`
  reads it before the index, as if its constants had been pushed
  (`find?_overlay_pushAll`, `ConLeche/Verify/Cached/BlockOverlay.lean`). -/
  ovl : List ConstantInfo
  /-- **The projection tables** (task #362), keyed on the structure's
  name: `env.tables` as a map (the newest table of a name wins, as
  `List.find?` takes the first). -/
  tbls : Std.HashMap Name ProjTable

/-- The index build, from the back: the newest (front) constant is
inserted last and wins, exactly as `List.find?` takes the first match —
so the agreement with `Env.find?` is unconditional (no freshness
assumption). -/
def mkIdxGo : List ConstantInfo → Std.HashMap Name ConstantInfo
  | [] => ∅
  | ci :: cs => (mkIdxGo cs).insert ci.name ci

/-- The table map's build, from the back: the newest (front) table is
inserted last and wins, exactly as `List.find?` takes the first. -/
def mkTblsGo : List ProjTable → Std.HashMap Name ProjTable
  | [] => ∅
  | t :: ts => (mkTblsGo ts).insert t.structName t

/-- Build the index of `env`. -/
def mkFEnv (env : Env) : FEnv :=
  ⟨env, mkIdxGo env.consts, {}, [], mkTblsGo env.tables⟩

namespace FEnv

/-- Indexed lookup (`= Env.find?` for `mkFEnv`); an index miss falls through to the base layer (empty
but in a view of a stream's index).  With an overlay, the overlay first -- exactly what pushing the
overlay's constants would answer.  `fe` is borrowed: the overlay branch otherwise makes the compiler
take it owned, reference-count traffic on every lookup. -/
def find? (fe : @& FEnv) (n : Name) : Option ConstantInfo :=
  match fe.ovl with
  | [] =>
    match fe.idx[n]? with
    | some ci => some ci
    | none => fe.base.find? n
  | ovl@(_ :: _) =>
    match ovl.find? (·.name == n) with
    | some ci => some ci
    | none =>
      match fe.idx[n]? with
      | some ci => some ci
      | none => fe.base.find? n

/-- The index of the cons-extended environment (`push_mkFEnv`:
`FEnv.push (mkFEnv env) ci = mkFEnv ⟨ci :: env.consts, env.tables⟩`,
definitionally). -/
def push (fe : FEnv) (ci : ConstantInfo) : FEnv :=
  ⟨⟨ci :: fe.env.consts, fe.env.tables⟩, fe.idx.insert ci.name ci, fe.base, fe.ovl, fe.tbls⟩

/-- **Push a projection table** (task #362): the table component
extended, the constant index untouched (`pushTable_mkFEnv`:
`FEnv.pushTable (mkFEnv env) t = mkFEnv ⟨env.consts, t :: env.tables⟩`,
definitionally). -/
def pushTable (fe : FEnv) (t : ProjTable) : FEnv :=
  ⟨⟨fe.env.consts, t :: fe.env.tables⟩, fe.idx, fe.base, fe.ovl, fe.tbls.insert t.structName t⟩

/-- Install a list of tables, head first (as `FEnv.pushAll` pushes
constants): `(pushTables Q fe).env.tables = Q.reverse ++ fe.env.tables`.
Tail-recursive, so the index is threaded owned. -/
def pushTables : List ProjTable → FEnv → FEnv
  | [], fe => fe
  | t :: Q, fe => pushTables Q (fe.pushTable t)

/-- **Cons `new` (newest first) as an overlay**: the environment `new` pushed onto `fe` would be
(`find?_overlay`, for an `fe` without an overlay), with the index SHARED, not mutated -- two live
environments, one bucket array.  Read-only: nothing pushes onto it. -/
def overlay (fe : FEnv) (new : List ConstantInfo) : FEnv :=
  ⟨⟨new ++ fe.env.consts, fe.env.tables⟩, fe.idx, fe.base, new ++ fe.ovl, fe.tbls⟩

/-- The table map's lookup, ungated: a miss in the map falls through to
the base layer (empty but in a view of a stream's index). -/
def rawTable? (fe : FEnv) (T : Name) : Option ProjTable :=
  match fe.tbls[T]? with
  | some t => some t
  | none => fe.base.findTable? T

/-- **The table lookup** (task #362): `T`'s table, visible exactly
where the constant `T` is (`= Env.findTable?` for `mkFEnv`,
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
def andRescueSlotsF (fe : FEnv) (ctor : Name) (nP : Nat) : Bool :=
  andRescueSlotsOf fe.findProj? ctor nP

end FEnv

/-! ### Indexed guard twins (same result as the `Env` versions) -/

/-- `natLitSupported` through the index. -/
def natLitSupportedF (fe : FEnv) : Bool :=
  natIndOk (fe.find? natName) && natZeroOk (fe.find? natZeroName) &&
    natSuccOk (fe.find? natSuccName)

/-- `natLitStored` through the index. -/
def natLitStoredF (fe : FEnv) : Bool :=
  (fe.find? natName).isSome && (fe.find? natZeroName).isSome && (fe.find? natSuccName).isSome

/-- `strLitStored` through the index. -/
def strLitStoredF (fe : FEnv) : Bool :=
  natLitStoredF fe && (fe.find? stringName).isSome && (fe.find? stringOfListName).isSome &&
    (fe.find? listName).isSome && (fe.find? listNilName).isSome &&
    (fe.find? listConsName).isSome && (fe.find? charName).isSome &&
    (fe.find? charOfNatName).isSome

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

end ConLeche
