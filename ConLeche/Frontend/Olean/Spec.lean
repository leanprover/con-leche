module

public import ConLeche.Frontend.Olean.Region
public import ConLeche.Frontend.Scan.Types

@[expose] public section

/-!
# Reading `.olean` files: the specification (task #371)

**What the reader computes from a module's bytes**, written as plainly
as possible: a value is read off the object it is stored as, field by
field, by recursion on the location — every pointer points to an
object at an earlier location (`Region.down`), so the recursion is
well-founded.  No memo, no sharing, no worklist; on a real module this
is exponential in the sharing of its expressions, and it is never
executed: the driver calls `decodeModuleSpec`, and the compiler runs
the fast decoder `decodeModuleFast` (`ConLeche/Frontend/Olean/Fast.lean`)
on the strength of the theorem `decodeModuleSpec_eq_fast`
(`ConLeche/Verify/Frontend/Olean/Equiv.lean`, `@[csimp]`), which says the
two are the same function.

What is read of each Lean type is its v4.35.0 runtime layout — the
constructor tags in declaration order, the pointer fields in
declaration order, then the scalar area (the computed hash/data words
of `Name`, `Level` and `Expr` first, which are skipped, then the
one-byte fields in declaration order):

| type | constructor (tag) — pointer fields — scalars |
|---|---|
| `Name` | `anonymous` = scalar 0; `str` (1) `pre s`; `num` (2) `pre i` |
| `Level` | `zero` (0, or the scalar 0); `succ` (1) `u`; `max` (2), `imax` (3) `u v`; `param` (4) `n`; `mvar` (5) |
| `Expr` | `bvar` (0) `i`; `fvar` (1); `mvar` (2); `sort` (3) `u`; `const` (4) `n us`; `app` (5) `f a`; `lam` (6), `forallE` (7) `n t b` — binder info; `letE` (8) `n t v b` — nondep; `lit` (9) `l`; `mdata` (10) `d e`; `proj` (11) `s i e` |
| `Literal` | `natVal` (0) `n`; `strVal` (1) `s` |
| `List` | `nil` = scalar 0; `cons` (1) `head tail` |
| `ConstantInfo` | `axiomInfo` … `recInfo` (0–7), one field: the `…Val` |
| `ConstantVal` | `name levelParams type` |
| `ModuleData` | `imports constNames constants extraConstNames entries` — `isModule` |

**Binder names, binder infos, `nonDep` and metadata are dropped**, as
lean4export drops them (`removeMData`, the `nonDep := false`
normalisation) and as the checker's `Expr` has no place for them; a
free variable or a metavariable in a stored constant is malformed
input, as is every object of a tag or field count the table does not
list.  A field the reader does not use is not read.

**The shape of the reading.**  Each recursive type has a *node*
function (`nameNode`, `levelNode`, `levelsNode`, `exprNode`): one
object, its fields read, its sub-values of the recursive types obtained
from a function argument for locations below the object.  The
specification ties the knot with itself (`nameAt` … `exprAt`); the
fast decoder hands the same node functions its memo instead.  The
constants and the module data are read in two layers: a *skeleton*
(`constSkel`, `moduleSkel`) holds every field except the names and
expressions, which stay pointers, and `CEntryF.mapM` reads those
(`decodeModuleSpec`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## Pointers held by an object

A pointer the object at `g` holds, read as a value of a recursive type
through `sub`, which is only ever asked about locations below `g`.  The
scalar a type's nullary constructor is stored as (`Name.anonymous`,
`Level.zero`, `[]`) needs no object. -/

@[inline] def Region.nameIn (r : Region) (g : Nat) (v : UInt64)
    (sub : (c : Nat) → c < g → Option Name) : Option Name :=
  if v == 1 then some .anonymous
  else match h : r.down g v with
    | some c => sub c (Region.down_lt h)
    | none => none

@[inline] def Region.levelIn (r : Region) (g : Nat) (v : UInt64)
    (sub : (c : Nat) → c < g → Option Level) : Option Level :=
  if v == 1 then some .zero
  else match h : r.down g v with
    | some c => sub c (Region.down_lt h)
    | none => none

@[inline] def Region.levelsIn (r : Region) (g : Nat) (v : UInt64)
    (sub : (c : Nat) → c < g → Option (List Level)) : Option (List Level) :=
  if v == 1 then some []
  else match h : r.down g v with
    | some c => sub c (Region.down_lt h)
    | none => none

@[inline] def Region.exprIn (r : Region) (g : Nat) (v : UInt64)
    (sub : (c : Nat) → c < g → Option Expr) : Option Expr :=
  match h : r.down g v with
  | some c => sub c (Region.down_lt h)
  | none => none

/-- **A `Literal`** the object at `g` holds. -/
def Region.litP (r : Region) (g : Nat) (v : UInt64) : Option Literal :=
  match r.down g v with
  | some c =>
    if r.isCtor c 0 1 then (r.natP c (r.fld c 0)).map .natVal
    else if r.isCtor c 1 1 then (r.strP c (r.fld c 0)).map .strVal
    else none
  | none => none

/-! ## One object of each recursive type -/

/-- **A `Name` object** at `g`. -/
@[specialize] def nameNode (r : Region) (g : Nat) (nm : (c : Nat) → c < g → Option Name) :
    Option Name :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 1, 2 => do
      let p ← r.nameIn g (r.fld g 0) nm
      let s ← r.strP g (r.fld g 1)
      pure (.str p s)
    | 2, 2 => do
      let p ← r.nameIn g (r.fld g 0) nm
      let i ← r.natP g (r.fld g 1)
      pure (.num p i)
    | _, _ => none
  else none

/-- **A `Level` object** at `g` (`mvar` is malformed input). -/
@[specialize] def levelNode (r : Region) (g : Nat) (lv : (c : Nat) → c < g → Option Level)
    (nm : (c : Nat) → c < g → Option Name) : Option Level :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 0, 0 => some .zero
    | 1, 1 => do
      let u ← r.levelIn g (r.fld g 0) lv
      pure (.succ u)
    | 2, 2 => do
      let u ← r.levelIn g (r.fld g 0) lv
      let v ← r.levelIn g (r.fld g 1) lv
      pure (.max u v)
    | 3, 2 => do
      let u ← r.levelIn g (r.fld g 0) lv
      let v ← r.levelIn g (r.fld g 1) lv
      pure (.imax u v)
    | 4, 1 => do
      let n ← r.nameIn g (r.fld g 0) nm
      pure (.param n)
    | _, _ => none
  else none

/-- **A `List Level` cell** at `g`. -/
@[specialize] def levelsNode (r : Region) (g : Nat) (ls : (c : Nat) → c < g → Option (List Level))
    (lv : (c : Nat) → c < g → Option Level) : Option (List Level) :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 1, 2 => do
      let u ← r.levelIn g (r.fld g 0) lv
      let us ← r.levelsIn g (r.fld g 1) ls
      pure (u :: us)
    | _, _ => none
  else none

/-- **An `Expr` object** at `g`.  Metadata is transparent: an `mdata`
node IS its body. -/
@[specialize] def exprNode (r : Region) (g : Nat) (ex : (c : Nat) → c < g → Option Expr)
    (nm : (c : Nat) → c < g → Option Name) (lv : (c : Nat) → c < g → Option Level)
    (ls : (c : Nat) → c < g → Option (List Level)) : Option Expr :=
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 0, 1 => do
      let i ← r.natP g (r.fld g 0)
      pure (.bvar i)
    | 3, 1 => do
      let u ← r.levelIn g (r.fld g 0) lv
      pure (.sort u)
    | 4, 2 => do
      let n ← r.nameIn g (r.fld g 0) nm
      let us ← r.levelsIn g (r.fld g 1) ls
      pure (.const n us)
    | 5, 2 => do
      let f ← r.exprIn g (r.fld g 0) ex
      let a ← r.exprIn g (r.fld g 1) ex
      pure (.app f a)
    | 6, 3 => do
      let t ← r.exprIn g (r.fld g 1) ex
      let b ← r.exprIn g (r.fld g 2) ex
      pure (.lam t b)
    | 7, 3 => do
      let t ← r.exprIn g (r.fld g 1) ex
      let b ← r.exprIn g (r.fld g 2) ex
      pure (.forallE t b)
    | 8, 4 => do
      let t ← r.exprIn g (r.fld g 1) ex
      let v ← r.exprIn g (r.fld g 2) ex
      let b ← r.exprIn g (r.fld g 3) ex
      pure (.letE t v b)
    | 9, 1 => do
      let l ← r.litP g (r.fld g 0)
      pure (.lit l)
    | 10, 2 => r.exprIn g (r.fld g 1) ex
    | 11, 3 => do
      let s ← r.nameIn g (r.fld g 0) nm
      let i ← r.natP g (r.fld g 1)
      let e ← r.exprIn g (r.fld g 2) ex
      pure (.proj s i e)
    | _, _ => none
  else none

/-! ## The specification of the recursive types -/

/-- **The `Name` stored at location `g`.** -/
def nameAt (r : Region) (g : Nat) : Option Name :=
  nameNode r g fun c _ => nameAt r c
termination_by g

/-- **The `Level` stored at location `g`.** -/
def levelAt (r : Region) (g : Nat) : Option Level :=
  levelNode r g (fun c _ => levelAt r c) (fun c _ => nameAt r c)
termination_by g

/-- **The `List Level` stored at location `g`.** -/
def levelsAt (r : Region) (g : Nat) : Option (List Level) :=
  levelsNode r g (fun c _ => levelsAt r c) (fun c _ => levelAt r c)
termination_by g

/-- **The `Expr` stored at location `g`.** -/
def exprAt (r : Region) (g : Nat) : Option Expr :=
  exprNode r g (fun c _ => exprAt r c) (fun c _ => nameAt r c) (fun c _ => levelAt r c)
    (fun c _ => levelsAt r c)
termination_by g

/-- The `Name` a pointer stands for. -/
def nameP (r : Region) (v : UInt64) : Option Name :=
  if v == 1 then some .anonymous
  else match r.loc v with
    | some c => nameAt r c
    | none => none

/-- The `Expr` a pointer stands for. -/
def exprP (r : Region) (v : UInt64) : Option Expr :=
  match r.loc v with
  | some c => exprAt r c
  | none => none

/-! ## Constants

One stored constant, generic in what stands for a name (`N`) and an
expression (`E`): pointers in the skeleton, the checker's values once
read. -/

inductive CKindF (N E : Type) where
  | ax (isUnsafe : Bool)
  | defn (value : E) (hints : HintsRec) (safety : String)
  | thm (value : E) (all : List N)
  | opaq (value : E) (isUnsafe : Bool)
  | quot (kind : String)
  | induct (numParams numIndices : Nat) (all ctors : List N) (numNested : Nat)
      (isRec isUnsafe isReflexive : Bool)
  | ctor (induct : N) (cidx numParams numFields : Nat) (isUnsafe : Bool)
  | recur (all : List N) (numParams numIndices numMotives numMinors : Nat)
      (rules : List (N × Nat × E)) (k isUnsafe : Bool)

structure CEntryF (N E : Type) where
  name : N
  levelParams : List N
  type : E
  kind : CKindF N E

/-- A constant's kind, the checker's values throughout. -/
abbrev CKind := CKindF Name Expr

/-- Read every name and expression of a kind. -/
def CKindF.mapM {m : Type → Type} [Monad m] {N E N' E' : Type} (fn : N → m N')
    (fe : E → m E') : CKindF N E → m (CKindF N' E')
  | .ax u => pure (.ax u)
  | .defn v h s => do pure (.defn (← fe v) h s)
  | .thm v all => do
    let v ← fe v
    let all ← all.mapM fn
    pure (.thm v all)
  | .opaq v u => do pure (.opaq (← fe v) u)
  | .quot k => pure (.quot k)
  | .induct np ni all cs nn ir iu irf => do
    let all ← all.mapM fn
    let cs ← cs.mapM fn
    pure (.induct np ni all cs nn ir iu irf)
  | .ctor ind ci np nf iu => do pure (.ctor (← fn ind) ci np nf iu)
  | .recur all np ni nmo nmi rules k iu => do
    let all ← all.mapM fn
    let rules ← rules.mapM fun (c, n, e) => do
      let c ← fn c
      let e ← fe e
      pure (c, n, e)
    pure (.recur all np ni nmo nmi rules k iu)

/-- Read every name and expression of a constant. -/
def CEntryF.mapM {m : Type → Type} [Monad m] {N E N' E' : Type} (fn : N → m N')
    (fe : E → m E') (c : CEntryF N E) : m (CEntryF N' E') := do
  let name ← fn c.name
  let lps ← c.levelParams.mapM fn
  let type ← fe c.type
  let kind ← c.kind.mapM fn fe
  pure ⟨name, lps, type, kind⟩

/-- A `Nat` field. -/
@[inline] def Region.natF (r : Region) (g i : Nat) : Option Nat := r.natP g (r.fld g i)

/-- A `List Name` field: its elements' pointers. -/
@[inline] def Region.nameList (r : Region) (g i : Nat) : Option (List UInt64) :=
  (r.list g (r.fld g i)).map (·.toList)

/-- **The skeleton of the `ConstantInfo` at location `c`**: everything
but its names and expressions, which stay pointers. -/
def constSkel (r : Region) (c : Nat) : Option (CEntryF UInt64 UInt64) := do
  unless r.nobjs c == 1 && r.tag c ≤ 7 && r.fits c do none
  let x ← r.down c (r.fld c 0)
  let cv ← r.down x (r.fld x 0)
  unless r.isCtor cv 0 3 do none
  let name ← r.ptrFld cv 0
  let lps ← r.nameList cv 1
  let type ← r.ptrFld cv 2
  let kind ← match r.tag c with
    | 0 => do
      unless r.isCtor x 0 1 do none
      pure (CKindF.ax (← r.bool x 0))
    | 1 => do
      unless r.isCtor x 0 4 do none
      let value ← r.ptrFld x 1
      let hv := r.fld x 2
      let hints ← if hv == 1 then pure HintsRec.«opaque»
        else if hv == 3 then pure HintsRec.«abbrev»
        else do
          let h ← r.down x hv
          unless r.isCtor h 2 0 do none
          pure (HintsRec.regular (← r.u32 h 0).toNat)
      let safety ← match ← r.u8 x 0 with
        | 0 => pure "unsafe" | 1 => pure "safe" | 2 => pure "partial"
        | _ => none
      pure (CKindF.defn value hints safety)
    | 2 => do
      unless r.isCtor x 0 3 do none
      pure (CKindF.thm (← r.ptrFld x 1) (← r.nameList x 2))
    | 3 => do
      unless r.isCtor x 0 3 do none
      pure (CKindF.opaq (← r.ptrFld x 1) (← r.bool x 0))
    | 4 => do
      unless r.isCtor x 0 1 do none
      let k ← match ← r.u8 x 0 with
        | 0 => pure "type" | 1 => pure "ctor" | 2 => pure "lift" | 3 => pure "ind"
        | _ => none
      pure (CKindF.quot k)
    | 5 => do
      unless r.isCtor x 0 6 do none
      pure (CKindF.induct (← r.natF x 1) (← r.natF x 2) (← r.nameList x 3)
        (← r.nameList x 4) (← r.natF x 5) (← r.bool x 0) (← r.bool x 1) (← r.bool x 2))
    | 6 => do
      unless r.isCtor x 0 5 do none
      pure (CKindF.ctor (← r.ptrFld x 1) (← r.natF x 2) (← r.natF x 3) (← r.natF x 4)
        (← r.bool x 0))
    | _ => do
      unless r.isCtor x 0 7 do none
      let all ← r.nameList x 1
      let cells ← r.list x (r.fld x 6)
      let rules ← cells.toList.mapM fun v => do
        let y ← r.loc v
        unless r.isCtor y 0 3 do none
        pure ((← r.ptrFld y 0), (← r.natP y (r.fld y 1)), (← r.ptrFld y 2))
      pure (CKindF.recur all (← r.natF x 2) (← r.natF x 3) (← r.natF x 4) (← r.natF x 5) rules
        (← r.bool x 0) (← r.bool x 1))
  pure { name, levelParams := lps, type, kind }

/-! ## The module data -/

/-- **The skeleton of the root `ModuleData`**: its participation flag,
its imports' module names (pointers) and its constants' locations.  The
environment-extension entries are not the kernel's and are not read. -/
structure ModSkel where
  isModule : Bool
  imports : List UInt64
  consts : List Nat

def moduleSkel (r : Region) (root : UInt64) : Option ModSkel := do
  let g ← r.loc root
  unless r.isCtor g 0 5 do none
  let isModule ← r.bool g 0
  let imps ← r.objArray g (r.fld g 0)
  let imports ← imps.toList.mapM fun i => do
    unless r.isCtor i 0 1 do none
    r.ptrFld i 0
  let consts ← r.objArray g (r.fld g 2)
  pure ⟨isModule, imports, consts.toList⟩

/-- What the reader takes of a module: the participation flag, the
imported modules and the constants. -/
structure ModDecoded where
  isModule : Bool
  imports : Array Name
  constants : Array (CEntryF Name Expr)

/-- **The constant at location `c`.** -/
def constSpec (r : Region) (c : Nat) : Option (CEntryF Name Expr) := do
  let s ← constSkel r c
  s.mapM (nameP r) (exprP r)

/-- **THE SPECIFICATION: the module stored in a region from its root
pointer** — with its constants when `consts`, its imports alone
otherwise. -/
def decodeModuleSpec (r : Region) (root : UInt64) (consts : Bool) : Option ModDecoded := do
  let sk ← moduleSkel r root
  let imports ← sk.imports.mapM (nameP r)
  let constants ← if consts then sk.consts.mapM (constSpec r) else pure []
  pure ⟨sk.isModule, imports.toArray, constants.toArray⟩

end ConLeche.Frontend.Olean
