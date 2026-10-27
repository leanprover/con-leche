module

public import ConLeche.Frontend.Olean.Region
public import ConLeche.Frontend.Scan.Types

@[expose] public section

/-!
# Reading `.olean` files: the object decoder (task #369)

The objects of a module's region (`ConLeche/Frontend/Olean/Region.lean`)
decoded into the checker's own values: `Name`, `Level`, `Expr` and one
`CEntry` per `ConstantInfo` of the module's `ModuleData`.  What is read
of each Lean type is its v4.35.0 runtime layout — the constructor tags
in declaration order, the pointer fields in declaration order, then the
scalar area (the computed hash/data words of `Name`, `Level` and
`Expr` first, which are skipped, then the one-byte fields in
declaration order):

| type | constructor (tag) — pointer fields — scalars |
|---|---|
| `Name` | `anonymous` = scalar 0; `str` (1) `pre s`; `num` (2) `pre i` |
| `Level` | `zero` (0); `succ` (1) `u`; `max` (2), `imax` (3) `u v`; `param` (4) `n`; `mvar` (5) |
| `Expr` | `bvar` (0) `i`; `fvar` (1); `mvar` (2); `sort` (3) `u`; `const` (4) `n us`; `app` (5) `f a`; `lam` (6), `forallE` (7) `n t b` — binder info; `letE` (8) `n t v b` — nondep; `lit` (9) `l`; `mdata` (10) `d e`; `proj` (11) `s i e` |
| `ConstantInfo` | `axiomInfo` … `recInfo` (0–7), one field: the `…Val` |
| `ConstantVal` | `name levelParams type` |

**Binder names, binder infos, `nonDep` and metadata are dropped**, as
lean4export drops them (`removeMData`, the `nonDep := false`
normalisation) and as the checker's `Expr` has no place for them; a
free variable or a metavariable in a stored constant is malformed
input.

**The walk is bottom-up and iterative** (`exprLoop`): an expression
graph can be deep (long application spines, `let` towers), so there is
no recursion over it.  A node is built once its children are, from the
per-module memo (`DS.exprs`, keyed by address); the result is then
shared within the module exactly as the file shares it (the compactor
max-shares every module's objects).  Across modules expressions are
NOT hash-consed: measured on `Init`, a run-wide table cost twice the
peak memory and saved 1 % of the check (DESIGN.md, task #369); the
checker's equality is structural with a pointer fast path, so a
duplicate is only a missed shortcut.  Names and levels are shallow:
they are decoded recursively, memoized, and hash-consed across the
run.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- The decoder state: the module's address memos and the run's
hash-cons tables.  Flat, so that an update replaces one field of a
uniquely held record (the linearity rules of the
`lean-rc-linearity` skill). -/
structure DS where
  /-- per slot: bit 0 a name, bit 1 a level, bit 2 an expression is memoized -/
  flags : ByteArray := .empty
  names : Array Name := #[]
  levels : Array Level := #[]
  exprs : Array Expr := #[]
  cNames : Std.HashMap Name Name := {}
  cLevels : Std.HashMap Level Level := {}

abbrev DM := StateT DS (Except String)

@[inline] def liftE (x : Except String α) : DM α := StateT.lift x

/-! ### The memos

**Dense, by slot** (`Region.slot`): one array per kind, as long as the
module's files in words, and a flag byte per slot.  An address is a
multiple of 8, so a hash map keyed by addresses clusters its buckets;
a dense array needs no hashing and no rehash, at the price of three
pointers per word of the module while it is decoded.

**Each update takes the arrays OUT of the record before changing them**
(the destructuring `let`): `{ st with f := st.f.set … }` would change
the array while the old record still holds it, at reference count 2,
and copy the whole array at every update (the linearity rules of the
`lean-rc-linearity` skill). -/

/-- A fresh set of memos for a region of `n` slots; the hash-cons
tables are kept. -/
def DS.fresh (st : DS) (n : Nat) : DS :=
  let { cNames, cLevels, .. } := st
  let rec zeros (k : Nat) (b : ByteArray) : ByteArray :=
    match k with
    | 0 => b
    | k + 1 => zeros k (b.push 0)
  { flags := zeros n (ByteArray.emptyWithCapacity n),
    names := Array.replicate n .anonymous, levels := Array.replicate n .zero,
    exprs := Array.replicate n (.bvar 0), cNames, cLevels }

@[inline] def DS.flag (st : @& DS) (i : Nat) (bit : UInt8) : Bool :=
  rdU8 st.flags i &&& bit != 0

@[inline] def setFlag (b : ByteArray) (i : Nat) (bit : UInt8) : ByteArray :=
  if h : i < b.size then b.set i (b[i] ||| bit) h else b

@[inline] def DS.getName? (st : @& DS) (i : Nat) : Option Name :=
  if st.flag i 1 then st.names[i]? else none

@[inline] def DS.getLevel? (st : @& DS) (i : Nat) : Option Level :=
  if st.flag i 2 then st.levels[i]? else none

@[inline] def DS.getExpr? (st : @& DS) (i : Nat) : Option Expr :=
  if st.flag i 4 then st.exprs[i]? else none

@[inline] def DS.putName (st : DS) (i : Nat) (n : Name) : DS :=
  let { flags, names, levels, exprs, cNames, cLevels } := st
  { flags := setFlag flags i 1, names := names.setIfInBounds i n, levels, exprs,
    cNames, cLevels }

@[inline] def DS.putLevel (st : DS) (i : Nat) (l : Level) : DS :=
  let { flags, names, levels, exprs, cNames, cLevels } := st
  { flags := setFlag flags i 2, names, levels := levels.setIfInBounds i l, exprs,
    cNames, cLevels }

@[inline] def DS.putExpr (st : DS) (i : Nat) (e : Expr) : DS :=
  let { flags, names, levels, exprs, cNames, cLevels } := st
  { flags := setFlag flags i 4, names, levels, exprs := exprs.setIfInBounds i e,
    cNames, cLevels }

/-- The memoized expression at an address, if any. -/
@[inline] def DS.exprAt? (st : @& DS) (r : @& Region) (a : UInt64) : Option Expr :=
  st.getExpr? (r.slot a)

/-- Is the expression at an address built?  (No allocation.) -/
@[inline] def DS.built (st : @& DS) (r : @& Region) (a : UInt64) : Bool :=
  st.flag (r.slot a) 4

/-- The hash-consed copy of a name. -/
@[inline] def canonName (n : Name) : DM Name := modifyGet fun st =>
  let m := st.cNames
  let st := { st with cNames := {} }
  let (old, m) := m.getThenInsertIfNew? n n
  (old.getD n, { st with cNames := m })

@[inline] def canonLevel (l : Level) : DM Level := modifyGet fun st =>
  let m := st.cLevels
  let st := { st with cLevels := {} }
  let (old, m) := m.getThenInsertIfNew? l l
  (old.getD l, { st with cLevels := m })

/-- Depth bound of the recursive name and level decoders.  A pointer
always points below its object, so the recursion ends anyway; the bound
keeps a crafted chain from exhausting the stack (a few MB at this
depth), far above any real name's component count or universe's
nesting. -/
def shallowFuel : Nat := 10000

/-- **A `Name`**, memoized by address. -/
def nameAt (r : @& Region) (v : UInt64) : Nat → DM Name
  | 0 => throw "name nested too deeply"
  | fuel + 1 => do
    if v == 1 then return .anonymous
    let x ← liftE (r.obj v)
    if let some n := (← get).getName? x.slot then return n
    let n ← match x.tag.toNat with
      | 1 => do
        liftE (x.expect 1 2 "Name.str")
        let p ← nameAt r (← liftE (x.field 0)) fuel
        pure (Name.str p (← liftE (r.str (← liftE (x.field 1)))))
      | 2 => do
        liftE (x.expect 2 2 "Name.num")
        let p ← nameAt r (← liftE (x.field 0)) fuel
        pure (Name.num p (← liftE (r.nat (← liftE (x.field 1)))))
      | t => throw s!"object {v}: expected a Name, found tag {t}"
    let n ← canonName n
    modify (·.putName x.slot n)
    pure n

/-- **A `Level`**, memoized by address. -/
def levelAt (r : @& Region) (v : UInt64) : Nat → DM Level
  | 0 => throw "level nested too deeply"
  | fuel + 1 => do
    if v == 1 then return .zero
    let x ← liftE (r.obj v)
    if let some l := (← get).getLevel? x.slot then return l
    let l ← match x.tag.toNat with
      | 0 => do liftE (x.expect 0 0 "Level.zero"); pure Level.zero
      | 1 => do
        liftE (x.expect 1 1 "Level.succ")
        pure (Level.succ (← levelAt r (← liftE (x.field 0)) fuel))
      | 2 => do
        liftE (x.expect 2 2 "Level.max")
        let u ← levelAt r (← liftE (x.field 0)) fuel
        pure (Level.max u (← levelAt r (← liftE (x.field 1)) fuel))
      | 3 => do
        liftE (x.expect 3 2 "Level.imax")
        let u ← levelAt r (← liftE (x.field 0)) fuel
        pure (Level.imax u (← levelAt r (← liftE (x.field 1)) fuel))
      | 4 => do
        liftE (x.expect 4 1 "Level.param")
        pure (Level.param (← nameAt r (← liftE (x.field 0)) shallowFuel))
      | 5 => throw s!"object {v}: a universe metavariable in a stored constant"
      | t => throw s!"object {v}: expected a Level, found tag {t}"
    let l ← canonLevel l
    modify (·.putLevel x.slot l)
    pure l

/-- A list of names. -/
def namesAt (r : @& Region) (v : UInt64) : DM (List Name) := do
  let cells ← liftE (r.list v)
  cells.toList.mapM fun c => nameAt r c shallowFuel

/-- A list of levels. -/
def levelsAt (r : @& Region) (v : UInt64) : DM (List Level) := do
  let cells ← liftE (r.list v)
  cells.toList.mapM fun c => levelAt r c shallowFuel

/-- **An `Expr` object's shape**: the tag's field count, and the range
of its fields that are expressions (first index, count). -/
def exprShape (x : @& Obj) : Except String (Nat × Nat) :=
  let chk (n : Nat) (what : String) (k : Nat × Nat) : Except String (Nat × Nat) := do
    x.expect x.tag.toNat n what; pure k
  match x.tag.toNat with
  | 0 => chk 1 "Expr.bvar" (0, 0)
  | 3 => chk 1 "Expr.sort" (0, 0)
  | 4 => chk 2 "Expr.const" (0, 0)
  | 5 => chk 2 "Expr.app" (0, 2)
  | 6 => chk 3 "Expr.lam" (1, 2)
  | 7 => chk 3 "Expr.forallE" (1, 2)
  | 8 => chk 4 "Expr.letE" (1, 3)
  | 9 => chk 1 "Expr.lit" (0, 0)
  | 10 => chk 2 "Expr.mdata" (1, 1)
  | 11 => chk 3 "Expr.proj" (2, 1)
  | 1 => throw s!"object {x.addr}: a free variable in a stored constant"
  | 2 => throw s!"object {x.addr}: a metavariable in a stored constant"
  | t => throw s!"object {x.addr}: expected an Expr, found tag {t}"

/-- Push the expression children `[lo, lo + n)` of `x` that are not
built yet; the flag says whether any was. -/
def pushKids (r : @& Region) (st : @& DS) (x : @& Obj) (lo : Nat) :
    Nat → Array UInt64 → Bool → Array UInt64 × Bool
  | 0, stack, any => (stack, any)
  | n + 1, stack, any =>
    let c := x.f (lo + n)
    if st.built r c then pushKids r st x lo n stack any
    else pushKids r st x lo n (stack.push c) true

/-- A child already built (the walk builds children first). -/
@[inline] def builtKid (r : @& Region) (v : UInt64) : DM Expr := do
  match (← get).exprAt? r v with
  | some e => pure e
  | none => throw s!"object {v}: expression child not built"

/-- **One `Expr` node**, its children built.  Metadata is transparent:
an `mdata` node IS its body. -/
def buildExpr (r : @& Region) (x : Obj) : DM Expr := do
  let e ← match x.tag.toNat with
    | 0 => do
      liftE (x.expect 0 1 "Expr.bvar")
      pure (Expr.bvar (← liftE (r.nat (← liftE (x.field 0)))))
    | 1 => throw s!"object {x.addr}: a free variable in a stored constant"
    | 2 => throw s!"object {x.addr}: a metavariable in a stored constant"
    | 3 => do
      liftE (x.expect 3 1 "Expr.sort")
      pure (Expr.sort (← levelAt r (← liftE (x.field 0)) shallowFuel))
    | 4 => do
      liftE (x.expect 4 2 "Expr.const")
      let n ← nameAt r (← liftE (x.field 0)) shallowFuel
      pure (Expr.const n (← levelsAt r (← liftE (x.field 1))))
    | 5 => do pure (Expr.app (← builtKid r (← liftE (x.field 0))) (← builtKid r (← liftE (x.field 1))))
    | 6 => do pure (Expr.lam (← builtKid r (← liftE (x.field 1))) (← builtKid r (← liftE (x.field 2))))
    | 7 => do pure (Expr.forallE (← builtKid r (← liftE (x.field 1))) (← builtKid r (← liftE (x.field 2))))
    | 8 => do
      pure (Expr.letE (← builtKid r (← liftE (x.field 1))) (← builtKid r (← liftE (x.field 2)))
        (← builtKid r (← liftE (x.field 3))))
    | 9 => do
      liftE (x.expect 9 1 "Expr.lit")
      let l ← liftE (r.obj (← liftE (x.field 0)))
      match l.tag.toNat with
      | 0 => do
        liftE (l.expect 0 1 "Literal.natVal")
        let n ← liftE (r.nat (← liftE (l.field 0)))
        pure (Expr.lit (.natVal n))
      | 1 => do
        liftE (l.expect 1 1 "Literal.strVal")
        let s ← liftE (r.str (← liftE (l.field 0)))
        pure (Expr.lit (.strVal s))
      | t => throw s!"object {l.addr}: expected a Literal, found tag {t}"
    | 10 => return (← builtKid r (← liftE (x.field 1)))
    | 11 => do
      let s ← nameAt r (← liftE (x.field 0)) shallowFuel
      let i ← liftE (r.nat (← liftE (x.field 1)))
      pure (Expr.proj s i (← builtKid r (← liftE (x.field 2))))
    | t => throw s!"object {x.addr}: expected an Expr, found tag {t}"
  pure e

/-- **The bottom-up walk**: the stack holds addresses still to build; a
node whose children are all built is built and popped, otherwise its
missing children are pushed.  Every iteration either pops or pushes
children of a node that is not built yet, and children lie below their
parent, so the walk ends; the fuel (the region's size in bytes) only
makes that visible to Lean.  The state is an explicit argument, read
(the membership tests) before it is changed (`buildExpr`, `putExpr`). -/
def exprLoopS (r : @& Region) (stack : Array UInt64) (fuel : Nat) (st : DS) :
    Except String DS :=
  match fuel with
  | 0 => throw "expression walk ran out of fuel"
  | fuel + 1 =>
    match stack.back? with
    | none => pure st
    | some a =>
      if st.built r a then exprLoopS r stack.pop fuel st
      else
        match r.obj a with
        | .error e => throw e
        | .ok x =>
          match exprShape x with
          | .error e => throw e
          | .ok (lo, n) =>
            let (stack, pushed) := pushKids r st x lo n stack false
            if pushed then exprLoopS r stack fuel st
            else
              match (buildExpr r x).run st with
              | .error e => throw e
              | .ok (e, st) => exprLoopS r stack.pop fuel (st.putExpr x.slot e)

/-- The walk, in the decoder monad. -/
def exprLoop (r : @& Region) (stack : Array UInt64) (fuel : Nat) : DM Unit := fun st => do
  pure ((), ← exprLoopS r stack fuel st)

/-- **An `Expr`**, through the walk. -/
def exprAt (r : @& Region) (v : UInt64) : DM Expr := do
  if isScalar v then throw s!"expected an expression, found the scalar {v}"
  exprLoop r #[v] (4 * r.words + 4)
  builtKid r v

/-! ## Constants -/

/-- **One stored constant**, as the merge and the emitter need it
(`ConLeche/Frontend/Olean/Load.lean`): the `ConstantInfo`'s kind with
its fields, the checker's values throughout. -/
inductive CKind where
  | ax (isUnsafe : Bool)
  | defn (value : Expr) (hints : HintsRec) (safety : String)
  | thm (value : Expr) (all : List Name)
  | opaq (value : Expr) (isUnsafe : Bool)
  | quot (kind : String)
  | induct (numParams numIndices : Nat) (all ctors : List Name) (numNested : Nat)
      (isRec isUnsafe isReflexive : Bool)
  | ctor (induct : Name) (cidx numParams numFields : Nat) (isUnsafe : Bool)
  | recur (all : List Name) (numParams numIndices numMotives numMinors : Nat)
      (rules : List (Name × Nat × Expr)) (k isUnsafe : Bool)

structure CEntry where
  name : Name
  levelParams : List Name
  type : Expr
  kind : CKind
  /-- the constants its type and values mention, in first-visit order
  (`constsOf`, computed by the module's decode worker) -/
  uses : Array Name := #[]

/-- lean4export's filter (`dumpConstant`): unsafe and partial constants
are not exported. -/
def CEntry.skipped (c : CEntry) : Bool :=
  match c.kind with
  | .ax u | .opaq _ u | .induct _ _ _ _ _ _ u _ | .ctor _ _ _ _ u | .recur _ _ _ _ _ _ _ u => u
  | .defn _ _ s => s != "safe"
  | .thm .. | .quot _ => false

/-- A one-byte `Bool` scalar. -/
def boolAt (x : @& Obj) (k : Nat) : Except String Bool := do
  match ← x.u8 k with
  | 0 => pure false
  | 1 => pure true
  | b => throw s!"object {x.addr}: {b} is not a Bool"

/-- The `ConstantVal` a `…Val` structure extends: its field `0`. -/
def cvAt (r : @& Region) (v : UInt64) : DM (Name × List Name × Expr) := do
  let x ← liftE (r.obj v)
  liftE (x.expect 0 3 "ConstantVal")
  let n ← nameAt r (← liftE (x.field 0)) shallowFuel
  let lps ← namesAt r (← liftE (x.field 1))
  pure (n, lps, ← exprAt r (← liftE (x.field 2)))

/-- **One `ConstantInfo`.** -/
def constAt (r : @& Region) (v : UInt64) : DM CEntry := do
  let ci ← liftE (r.obj v)
  unless ci.other == 1 && ci.tag ≤ 7 do
    throw s!"object {v}: expected a ConstantInfo, found tag {ci.tag} with {ci.other} fields"
  let x ← liftE (r.obj (← liftE (ci.field 0)))
  let f (i : Nat) : DM UInt64 := liftE (x.field i)
  let nat (i : Nat) : DM Nat := do liftE (r.nat (← f i))
  let b (k : Nat) : DM Bool := liftE (boolAt x k)
  let shape (n : Nat) (what : String) : DM Unit := liftE (x.expect 0 n what)
  let (name, lps, ty) ← cvAt r (← f 0)
  let kind ← match ci.tag.toNat with
    | 0 => do shape 1 "AxiomVal"; pure (CKind.ax (← b 0))
    | 1 => do
      shape 4 "DefinitionVal"
      let value ← exprAt r (← f 1)
      let hv ← f 2
      let hints ← if hv == 1 then pure HintsRec.«opaque»
        else if hv == 3 then pure HintsRec.«abbrev»
        else do
          let h ← liftE (r.obj hv)
          liftE (h.expect 2 0 "ReducibilityHints.regular")
          pure (HintsRec.regular (← liftE (h.u32 0)).toNat)
      let safety ← match ← liftE (x.u8 0) with
        | 0 => pure "unsafe" | 1 => pure "safe" | 2 => pure "partial"
        | s => throw s!"object {x.addr}: {s} is not a DefinitionSafety"
      pure (CKind.defn value hints safety)
    | 2 => do
      shape 3 "TheoremVal"
      let value ← exprAt r (← f 1)
      pure (CKind.thm value (← namesAt r (← f 2)))
    | 3 => do
      shape 3 "OpaqueVal"
      pure (CKind.opaq (← exprAt r (← f 1)) (← b 0))
    | 4 => do
      shape 1 "QuotVal"
      let k ← match ← liftE (x.u8 0) with
        | 0 => pure "type" | 1 => pure "ctor" | 2 => pure "lift" | 3 => pure "ind"
        | k => throw s!"object {x.addr}: {k} is not a QuotKind"
      pure (CKind.quot k)
    | 5 => do
      shape 6 "InductiveVal"
      pure (CKind.induct (← nat 1) (← nat 2) (← namesAt r (← f 3)) (← namesAt r (← f 4))
        (← nat 5) (← b 0) (← b 1) (← b 2))
    | 6 => do
      shape 5 "ConstructorVal"
      pure (CKind.ctor (← nameAt r (← f 1) shallowFuel) (← nat 2) (← nat 3) (← nat 4) (← b 0))
    | _ => do
      shape 7 "RecursorVal"
      let all ← namesAt r (← f 1)
      let cells ← liftE (r.list (← f 6))
      let rules ← cells.toList.mapM fun c => do
        let y ← liftE (r.obj c)
        liftE (y.expect 0 3 "RecursorRule")
        let cn ← nameAt r (← liftE (y.field 0)) shallowFuel
        let nf ← liftE (r.nat (← liftE (y.field 1)))
        pure (cn, nf, ← exprAt r (← liftE (y.field 2)))
      pure (CKind.recur all (← nat 2) (← nat 3) (← nat 4) (← nat 5) rules (← b 0) (← b 1))
  pure { name, levelParams := lps, type := ty, kind }

/-! ## The module data -/

/-- What the reader takes of a `ModuleData` (`isModule`, `imports`,
`constNames`, `constants`, `extraConstNames`, `entries`): the
participation flag, the imported modules and the constants.  The
environment-extension entries are not the kernel's and are not read. -/
structure ModuleInfo where
  isModule : Bool
  imports : Array Name
  constants : Array UInt64

/-- **The root `ModuleData`.** -/
def moduleAt (r : @& Region) (v : UInt64) : DM ModuleInfo := do
  let x ← liftE (r.obj v)
  liftE (x.expect 0 5 "ModuleData")
  let isModule ← liftE (boolAt x 0)
  let imps ← liftE (r.array (← liftE (x.field 0)))
  let imports ← imps.mapM fun i => do
    let y ← liftE (r.obj i)
    liftE (y.expect 0 1 "Import")
    nameAt r (← liftE (y.field 0)) shallowFuel
  pure ⟨isModule, imports, ← liftE (r.array (← liftE (x.field 2)))⟩

end ConLeche.Frontend.Olean
