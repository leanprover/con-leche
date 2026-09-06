module
public import Lean
public meta import Lech.Kernel.Expr

/-!
# The pin-dump interchange format (task #176)

The pinned `Nat`-operation declarations and their certificate proof
blobs used to be *computed* while `Lech/Kernel/NatOpPins.lean`
elaborated, by loading `Lech/PinGen/Certs.olean` into a full-view
environment (`importModules` at `OLeanLevel.private`).  That is not an
import edge, so Lake never ordered the two — on a cold tree
`lake build lech` failed with

    object file '…/Lech/PinGen/Certs.olean' of module
    Lech.PinGen.Certs does not exist

(the `extraDepTargets` in `lakefile.toml` did not reach the module when
it was built through the executable's import graph).  The user's
ruling: *commit the pin as a file* — which is what multi-toolchain
support needs anyway.

This module is the format both ends share:

* the **generator** (`PinDump.lean`, the `natop-pins-export`
  executable — it lives in the certificate library's world, where the
  proof bodies are visible) computes the pins exactly as before and
  serialises them here;
* the **loader** (`Lech/Kernel/NatOpPins.lean`) `include_str`s the
  committed dump and splices it at elaboration time.

Nothing here reads an olean by name, so both ends are ordinary Lake
targets with ordinary import edges.

## What is dumped

Not the `Lech.Expr` tree, but the **share table** the emitter builds
from it (`Lech.PinGen.ShareSt`): pins share subterms heavily, and
emitting them unshared would explode.  A dumped blob is therefore an
array of `PinEntry`s — each one constructor application whose
arguments are *absolute* indices of earlier entries — plus the root
reference.  `PinBlob.value` turns that back into the `let`-chain
`Lean.Expr` the splice `addDecl`s, and `buildExprValue` (the emitter
the `#gen_trust_pins` pins still go through) is literally
`(blobOf ·).value`, so there is one emitter, not two: the committed
dump reproduces the pre-#176 declaration values by construction.
Receipt, taken once at #176: the eight pins and their nineteen
certificate blobs, re-serialised out of the SPLICED constants, are
byte-identical before (`#gen_natop_pins`) and after
(`#load_natop_pins`) — 40 908 lines, `diff -q` clean.

## Encoding

JSON, via `Lean.Json` — the toolchain's own parser, already the
generator's input format (`scripts/natop_prefix.json`).  The
alternative, our ndjson export dialect, would have wanted the
frontend's `Expr` parser, and that is unreachable from here:
`Lech.Frontend.*` imports `Lech.Kernel.*`, which imports
`Lech.Kernel.NatOpPins` — a cycle.  A bespoke line format would have
had to re-solve string escaping (name components and `strVal`
literals) that JSON already solves.

Entries are compact tag-led arrays (`["a",123,124]` for an
application), one per line in the emitted file, so the committed dump
diffs readably.
-/

public meta section

namespace Lech.PinGen

open Lean

/-! ## References

The share table's entries reference each other by absolute index.  Two
subobjects are never given entries of their own — `Name.anonymous` and
`Level.zero` are emitted inline, exactly as the pre-#176 builder did —
so a reference is one of three things. -/

/-- A reference to a shared subobject. -/
inductive PinRef where
  /-- Entry `i` of the table. -/
  | idx (i : Nat)
  /-- The inline `Lech.Name.anonymous`. -/
  | anon
  /-- The inline `Lech.Level.zero`. -/
  | lzero
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- The three entry *sorts*; they fix the `let` binder's name prefix and
type, and they are what makes the emitted chain readable. -/
inductive PinSort where
  | nameS | levelS | exprS
  deriving DecidableEq, Repr, Inhabited

/-- One share-table entry: a constructor application over references. -/
inductive PinEntry where
  | nameStr (p : PinRef) (s : String)
  | nameNum (p : PinRef) (i : Nat)
  | levSucc (u : PinRef)
  | levMax (u v : PinRef)
  | levImax (u v : PinRef)
  | levParam (n : PinRef)
  | exBVar (i : Nat)
  | exFVar (idx : Nat) (n ty : PinRef)
  | exSort (u : PinRef)
  | exConst (n : PinRef) (us : List PinRef)
  | exApp (f a : PinRef)
  | exLam (n ty b : PinRef) (bi : Lech.BinderInfo) (pw : Option (List Lech.Name))
  | exForall (n ty b : PinRef) (bi : Lech.BinderInfo) (pw : Option (List Lech.Name))
  | exLet (n ty v b : PinRef)
  | exLitNat (v : Nat)
  | exLitStr (s : String)
  | exProj (s : PinRef) (i : Nat) (e : PinRef)
  deriving Inhabited

/-- One dumped blob: the share table and the root reference. -/
structure PinBlob where
  root : PinRef
  entries : Array PinEntry
  deriving Inhabited

/-- One operation's dumped data. -/
structure PinOpDump where
  /-- The pinned toolchain operation (for diagnostics). -/
  op : String
  /-- The spliced definition names. -/
  pinName : String
  proofsName : String
  pin : PinBlob
  proofs : Array PinBlob
  deriving Inhabited

/-- A whole dump file. -/
structure PinDumpFile where
  toolchain : String
  leanVersion : String
  ops : Array PinOpDump
  deriving Inhabited

/-- The format tag written into, and required of, a dump file. -/
def dumpFormatTag : String := "lech-natop-pins/1"

/-- The dump file's basename for a toolchain: the `lean-toolchain`
string with everything outside `[A-Za-z0-9._-]` turned into `-`
(`leanprover/lean4:v4.33.0` ↦ `leanprover-lean4-v4.33.0.json`), so a
second toolchain's dump sits beside the first. -/
def toolchainFileName (tc : String) : String :=
  (tc.map fun c =>
    if c.isAlphanum || c == '.' || c == '-' || c == '_' then c else '-')
  ++ ".json"

/-! ## Rebuilding the `Lean.Expr`

`refExpr`, `PinEntry.sort`, `PinEntry.decl` and `assemble` together are
the pre-#176 `ShareSt` emitter, factored so that the generator and the
loader run the *same* code. -/

def nameT : Lean.Expr := .const ``Lech.Name []
def levelT : Lean.Expr := .const ``Lech.Level []
def exprT : Lean.Expr := .const ``Lech.Expr []

/-- Quote a `Lech.Name` structurally (used for the `pw` parameter
lists, which the share table does not cover — they are tiny). -/
def quoteName : Lech.Name → Lean.Expr
  | .anonymous => .const ``Lech.Name.anonymous []
  | .str p s => mkApp2 (.const ``Lech.Name.str []) (quoteName p) (mkStrLit s)
  | .num p n => mkApp2 (.const ``Lech.Name.num []) (quoteName p) (mkRawNatLit n)

def quoteBinderInfo : Lech.BinderInfo → Lean.Expr
  | .default => .const ``Lech.BinderInfo.default []
  | .implicit => .const ``Lech.BinderInfo.implicit []
  | .strictImplicit => .const ``Lech.BinderInfo.strictImplicit []
  | .instImplicit => .const ``Lech.BinderInfo.instImplicit []

def quoteNameList (ns : List Lech.Name) : Lean.Expr :=
  ns.foldr
    (fun n acc => mkApp3 (.const ``List.cons [.zero]) nameT (quoteName n) acc)
    (.app (.const ``List.nil [.zero]) nameT)

/-- Quote a `PropWhen` through its public interface (`never` /
`ifAllZero`) — the representation is private. -/
def quotePropWhen : Option (List Lech.Name) → Lean.Expr
  | none => .const ``Lech.PropWhen.never []
  | some ps => .app (.const ``Lech.PropWhen.ifAllZero []) (quoteNameList ps)

def quoteBinderMeta (bi : Lech.BinderInfo)
    (pw : Option (List Lech.Name)) : Lean.Expr :=
  mkApp2 (.const ``Lech.BinderMeta.mk []) (quoteBinderInfo bi)
    (quotePropWhen pw)

/-- A reference as an *absolute* `.bvar` (entry references) or an
inline constant.  `assemble` rewrites the `.bvar`s into de Bruijn
indices; the emitted values contain no real bound variables, so the
disguise is unambiguous. -/
def refExpr : PinRef → Lean.Expr
  | .idx i => .bvar i
  | .anon => .const ``Lech.Name.anonymous []
  | .lzero => .const ``Lech.Level.zero []

def PinEntry.sort : PinEntry → PinSort
  | .nameStr .. | .nameNum .. => .nameS
  | .levSucc .. | .levMax .. | .levImax .. | .levParam .. => .levelS
  | _ => .exprS

def PinSort.prefix' : PinSort → String
  | .nameS => "n" | .levelS => "l" | .exprS => "e"

def PinSort.type : PinSort → Lean.Expr
  | .nameS => nameT | .levelS => levelT | .exprS => exprT

def levelListE (us : List Lean.Expr) : Lean.Expr :=
  us.foldr (fun u acc => mkApp3 (.const ``List.cons [.zero]) levelT u acc)
    (.app (.const ``List.nil [.zero]) levelT)

/-- The value of one entry, with absolute references. -/
def PinEntry.value : PinEntry → Lean.Expr
  | .nameStr p s =>
    mkApp2 (.const ``Lech.Name.str []) (refExpr p) (mkStrLit s)
  | .nameNum p i =>
    mkApp2 (.const ``Lech.Name.num []) (refExpr p) (mkRawNatLit i)
  | .levSucc u => .app (.const ``Lech.Level.succ []) (refExpr u)
  | .levMax u v =>
    mkApp2 (.const ``Lech.Level.max []) (refExpr u) (refExpr v)
  | .levImax u v =>
    mkApp2 (.const ``Lech.Level.imax []) (refExpr u) (refExpr v)
  | .levParam n => .app (.const ``Lech.Level.param []) (refExpr n)
  | .exBVar i => .app (.const ``Lech.Expr.bvar []) (mkRawNatLit i)
  | .exFVar idx n ty =>
    mkApp3 (.const ``Lech.Expr.fvar []) (mkRawNatLit idx) (refExpr n)
      (refExpr ty)
  | .exSort u => .app (.const ``Lech.Expr.sort []) (refExpr u)
  | .exConst n us =>
    mkApp2 (.const ``Lech.Expr.const []) (refExpr n)
      (levelListE (us.map refExpr))
  | .exApp f a =>
    mkApp2 (.const ``Lech.Expr.app []) (refExpr f) (refExpr a)
  | .exLam n ty b bi pw =>
    mkApp4 (.const ``Lech.Expr.lam []) (refExpr n) (refExpr ty) (refExpr b)
      (quoteBinderMeta bi pw)
  | .exForall n ty b bi pw =>
    mkApp4 (.const ``Lech.Expr.forallE []) (refExpr n) (refExpr ty)
      (refExpr b) (quoteBinderMeta bi pw)
  | .exLet n ty v b =>
    mkApp4 (.const ``Lech.Expr.letE []) (refExpr n) (refExpr ty) (refExpr v)
      (refExpr b)
  | .exLitNat v =>
    .app (.const ``Lech.Expr.lit [])
      (.app (.const ``Lech.Literal.natVal []) (mkRawNatLit v))
  | .exLitStr s =>
    .app (.const ``Lech.Expr.lit [])
      (.app (.const ``Lech.Literal.strVal []) (mkStrLit s))
  | .exProj s i e =>
    mkApp3 (.const ``Lech.Expr.proj []) (refExpr s) (mkRawNatLit i)
      (refExpr e)

/-- The `let` binder for entry `i`. -/
def PinEntry.decl (i : Nat) (en : PinEntry) :
    Lean.Name × Lean.Expr × Lean.Expr :=
  let s := en.sort
  (.mkSimple s!"{s.prefix'}{i}", s.type, en.value)

/-- Convert absolute entry references (`.bvar j`) into de Bruijn indices
for a position under `k` enclosing `let` binders.  The emitted values
are pure application trees, so only `app` recurses. -/
partial def relat (k : Nat) : Lean.Expr → Lean.Expr
  | .bvar j => .bvar (k - 1 - j)
  | .app f a => .app (relat k f) (relat k a)
  | e => e

/-- Wrap `root` (with absolute references) in the collected `let`-chain. -/
def assemble (entries : Array (Lean.Name × Lean.Expr × Lean.Expr))
    (root : Lean.Expr) : Lean.Expr := Id.run do
  let n := entries.size
  let mut body := relat n root
  for i in [0:n] do
    let k := n - 1 - i
    let (nm, ty, v) := entries[k]!
    body := .letE nm ty (relat k v) body false
  return body

/-- The definition value of a dumped blob: the shared `let`-chain. -/
def PinBlob.value (b : PinBlob) : Lean.Expr :=
  assemble (b.entries.mapIdx fun i en => PinEntry.decl i en) (refExpr b.root)

/-! ## The sharing builder

The pins share subterms heavily (every distinct name, level and
expression node occurs many times).  Emitting them through the plain
`ToExpr` instance would lose all sharing, so each distinct subobject
becomes one `PinEntry` (`Lech/PinGen/Dump.lean`), bound once in the
`let`-chain `PinBlob.value` assembles; references are absolute entry
indices.  The share table is also exactly what the committed dump
carries (task #176), so the generator and the loader emit the same
declaration value by construction. -/

structure ShareSt where
  /-- Emitted entries, in dependency order. -/
  entries : Array PinEntry := #[]
  nameMap : Std.HashMap Lech.Name PinRef := {}
  levelMap : Std.HashMap Lech.Level PinRef := {}
  exprMap : Std.HashMap Lech.Expr PinRef := {}

abbrev ShareM := StateM ShareSt

def pushEntry (en : PinEntry) : ShareM PinRef := do
  let n := (← get).entries.size
  modify fun st => { st with entries := st.entries.push en }
  return .idx n

partial def shareName (n : Lech.Name) : ShareM PinRef := do
  if let some r := (← get).nameMap[n]? then return r
  let r ← match n with
    | .anonymous => pure PinRef.anon
    | .str p s => do pushEntry (.nameStr (← shareName p) s)
    | .num p i => do pushEntry (.nameNum (← shareName p) i)
  modify fun st => { st with nameMap := st.nameMap.insert n r }
  return r

partial def shareLevel (l : Lech.Level) : ShareM PinRef := do
  if let some r := (← get).levelMap[l]? then return r
  let r ← match l with
    | .zero => pure PinRef.lzero
    | .succ u => do pushEntry (.levSucc (← shareLevel u))
    | .max u w => do
      let uv ← shareLevel u; let wv ← shareLevel w
      pushEntry (.levMax uv wv)
    | .imax u w => do
      let uv ← shareLevel u; let wv ← shareLevel w
      pushEntry (.levImax uv wv)
    | .param n => do pushEntry (.levParam (← shareName n))
  modify fun st => { st with levelMap := st.levelMap.insert l r }
  return r

partial def shareExpr (e : Lech.Expr) : ShareM PinRef := do
  if let some r := (← get).exprMap[e]? then return r
  let r ← match e with
    | .bvar i => pushEntry (.exBVar i)
    | .fvar idx n ty => do
      let nv ← shareName n
      let tv ← shareExpr ty
      pushEntry (.exFVar idx nv tv)
    | .sort u => do pushEntry (.exSort (← shareLevel u))
    | .const n us => do
      let nv ← shareName n
      let uvs ← us.mapM shareLevel
      pushEntry (.exConst nv uvs)
    | .app f a => do
      let fv ← shareExpr f
      let av ← shareExpr a
      pushEntry (.exApp fv av)
    | .lam n ty b m => do
      let nv ← shareName n
      let tv ← shareExpr ty
      let bv ← shareExpr b
      pushEntry (.exLam nv tv bv m.bi m.pw.toList?)
    | .forallE n ty b m => do
      let nv ← shareName n
      let tv ← shareExpr ty
      let bv ← shareExpr b
      pushEntry (.exForall nv tv bv m.bi m.pw.toList?)
    | .letE n ty v b => do
      let nv ← shareName n
      let tv ← shareExpr ty
      let vv ← shareExpr v
      let bv ← shareExpr b
      pushEntry (.exLet nv tv vv bv)
    | .lit (.natVal v) => pushEntry (.exLitNat v)
    | .lit (.strVal s) => pushEntry (.exLitStr s)
    | .proj s i x => do
      let sv ← shareName s
      let xv ← shareExpr x
      pushEntry (.exProj sv i xv)
  modify fun st => { st with exprMap := st.exprMap.insert e r }
  return r

/-- The share table of one expression: what the dump carries and what
`PinBlob.value` turns back into the emitted `let`-chain. -/
def blobOf (e : Lech.Expr) : PinBlob :=
  let (root, st) := Id.run (StateT.run (s := ({} : ShareSt)) (shareExpr e))
  { root, entries := st.entries }

/-- Build the value of a single-expression definition (`… : Expr`) as a
shared `let`-chain. -/
def buildExprValue (e : Lech.Expr) : Lean.Expr := (blobOf e).value

/-! ## JSON codec -/

def natJ (n : Nat) : Json := Json.num (JsonNumber.fromNat n)

def refToJson : PinRef → Json
  | .idx i => natJ i
  | .anon => Json.str "anon"
  | .lzero => Json.str "lzero"

def refOfJson (j : Json) : Except String PinRef :=
  match j with
  | Json.num _ => return .idx (← j.getNat?)
  | Json.str "anon" => return .anon
  | Json.str "lzero" => return .lzero
  | _ => .error s!"bad pin reference: {j.compress}"

def biToJson : Lech.BinderInfo → Json
  | .default => natJ 0
  | .implicit => natJ 1
  | .strictImplicit => natJ 2
  | .instImplicit => natJ 3

def biOfNat : Nat → Except String Lech.BinderInfo
  | 0 => return .default
  | 1 => return .implicit
  | 2 => return .strictImplicit
  | 3 => return .instImplicit
  | k => .error s!"bad binder info tag {k}"

/-- A `Lech.Name` as the array of its components, outermost last. -/
def snameComps : Lech.Name → Array Json → Array Json
  | .anonymous, acc => acc
  | .str p s, acc => (snameComps p acc).push (Json.str s)
  | .num p i, acc => (snameComps p acc).push (natJ i)

def snameToJson (n : Lech.Name) : Json := Json.arr (snameComps n #[])

def snameOfJson (j : Json) : Except String Lech.Name := do
  let arr ← j.getArr?
  let mut n : Lech.Name := .anonymous
  for c in arr do
    match c with
    | Json.str s => n := .str n s
    | Json.num _ => n := .num n (← c.getNat?)
    | _ => throw s!"bad name component: {c.compress}"
  return n

def pwToJson : Option (List Lech.Name) → Json
  | none => Json.null
  | some ps => Json.arr (ps.map snameToJson).toArray

def pwOfJson : Json → Except String (Option (List Lech.Name))
  | Json.null => return none
  | j => do
    let arr ← j.getArr?
    return some (← arr.toList.mapM snameOfJson)

def PinEntry.toJson : PinEntry → Json
  | .nameStr p s => Json.arr #[Json.str "ns", refToJson p, Json.str s]
  | .nameNum p i => Json.arr #[Json.str "nn", refToJson p, natJ i]
  | .levSucc u => Json.arr #[Json.str "ls", refToJson u]
  | .levMax u v => Json.arr #[Json.str "lM", refToJson u, refToJson v]
  | .levImax u v => Json.arr #[Json.str "lI", refToJson u, refToJson v]
  | .levParam n => Json.arr #[Json.str "lp", refToJson n]
  | .exBVar i => Json.arr #[Json.str "b", natJ i]
  | .exFVar idx n ty =>
    Json.arr #[Json.str "f", natJ idx, refToJson n, refToJson ty]
  | .exSort u => Json.arr #[Json.str "s", refToJson u]
  | .exConst n us =>
    Json.arr #[Json.str "c", refToJson n,
      Json.arr (us.map refToJson).toArray]
  | .exApp f a => Json.arr #[Json.str "a", refToJson f, refToJson a]
  | .exLam n ty b bi pw =>
    Json.arr #[Json.str "lam", refToJson n, refToJson ty, refToJson b,
      biToJson bi, pwToJson pw]
  | .exForall n ty b bi pw =>
    Json.arr #[Json.str "fa", refToJson n, refToJson ty, refToJson b,
      biToJson bi, pwToJson pw]
  | .exLet n ty v b =>
    Json.arr #[Json.str "le", refToJson n, refToJson ty, refToJson v,
      refToJson b]
  | .exLitNat v => Json.arr #[Json.str "ln", natJ v]
  | .exLitStr s => Json.arr #[Json.str "lstr", Json.str s]
  | .exProj s i e =>
    Json.arr #[Json.str "p", refToJson s, natJ i, refToJson e]

def pinEntryOfJson (j : Json) : Except String PinEntry := do
  let a ← j.getArr?
  let at? (i : Nat) : Except String Json :=
    match a[i]? with
    | some v => return v
    | none => .error s!"pin entry field {i} missing: {j.compress}"
  let tag ← (← at? 0).getStr?
  let ref (i : Nat) : Except String PinRef := do refOfJson (← at? i)
  let nat (i : Nat) : Except String Nat := do (← at? i).getNat?
  let str (i : Nat) : Except String String := do (← at? i).getStr?
  match tag with
  | "ns" => return .nameStr (← ref 1) (← str 2)
  | "nn" => return .nameNum (← ref 1) (← nat 2)
  | "ls" => return .levSucc (← ref 1)
  | "lM" => return .levMax (← ref 1) (← ref 2)
  | "lI" => return .levImax (← ref 1) (← ref 2)
  | "lp" => return .levParam (← ref 1)
  | "b" => return .exBVar (← nat 1)
  | "f" => return .exFVar (← nat 1) (← ref 2) (← ref 3)
  | "s" => return .exSort (← ref 1)
  | "c" => do
    let us ← (← at? 2).getArr?
    return .exConst (← ref 1) (← us.toList.mapM refOfJson)
  | "a" => return .exApp (← ref 1) (← ref 2)
  | "lam" =>
    return .exLam (← ref 1) (← ref 2) (← ref 3) (← biOfNat (← nat 4))
      (← pwOfJson (← at? 5))
  | "fa" =>
    return .exForall (← ref 1) (← ref 2) (← ref 3) (← biOfNat (← nat 4))
      (← pwOfJson (← at? 5))
  | "le" => return .exLet (← ref 1) (← ref 2) (← ref 3) (← ref 4)
  | "ln" => return .exLitNat (← nat 1)
  | "lstr" => return .exLitStr (← str 1)
  | "p" => return .exProj (← ref 1) (← nat 2) (← ref 3)
  | t => .error s!"unknown pin entry tag {t}"

def blobOfJson (j : Json) : Except String PinBlob := do
  let root ← refOfJson (← j.getObjVal? "root")
  let es ← (← j.getObjVal? "entries").getArr?
  return { root, entries := ← es.mapM pinEntryOfJson }

def opDumpOfJson (j : Json) : Except String PinOpDump := do
  return {
    op := ← (← j.getObjVal? "op").getStr?
    pinName := ← (← j.getObjVal? "pinName").getStr?
    proofsName := ← (← j.getObjVal? "proofsName").getStr?
    pin := ← blobOfJson (← j.getObjVal? "pin")
    proofs := ← (← (← j.getObjVal? "proofs").getArr?).mapM blobOfJson }

/-- Parse a dump file, checking the format tag. -/
def dumpFileOfJson (j : Json) : Except String PinDumpFile := do
  let fmt ← (← j.getObjVal? "format").getStr?
  unless fmt == dumpFormatTag do
    throw s!"pin dump format {fmt}, expected {dumpFormatTag}"
  return {
    toolchain := ← (← j.getObjVal? "toolchain").getStr?
    leanVersion := ← (← j.getObjVal? "leanVersion").getStr?
    ops := ← (← (← j.getObjVal? "ops").getArr?).mapM opDumpOfJson }

def parseDumpFile (s : String) : Except String PinDumpFile := do
  dumpFileOfJson (← Json.parse s)

/-! ## Rendering

Written by hand rather than through `Json.compress` on one giant
object: the dump is a few MB and putting each share-table entry on its
own line keeps the committed file diffable. -/

def blobLines (b : PinBlob) (indent : String) : Array String := Id.run do
  let mut out := #[indent ++ "{\"root\":" ++ (refToJson b.root).compress ++
    ",\"entries\":["]
  for i in [0:b.entries.size] do
    let sep := if i + 1 == b.entries.size then "" else ","
    out := out.push ((b.entries[i]!).toJson.compress ++ sep)
  out := out.push (indent ++ "]}")
  return out

/-! ## The loader

`Lech/Kernel/NatOpPins.lean` `include_str`s the committed dump and
invokes `#load_natop_pins` on it.  Everything the splice needs is in
the dump (the definition names included), so the loader consults
neither `opSpecs` nor any olean; the only thing it insists on is that
the dump was generated by the running toolchain. -/

/-- Splice one operation's pin and certificate proofs into the ambient
environment (kernel-checked, then compiled).

Each certificate proof becomes its **own** definition
(`…CertProofs_i`), and `…CertProofs` is the shallow list of those
constants: consumers that reduce the *list* structure (the model
bridge's `CertRuns` destructuring) then never zeta through the blobs'
`let`-chains — the self-contained blobs of task #113 are deep enough
that doing so exceeds the kernel's recursion depth, and the blobs are
meant to stay opaque to the model anyway. -/
def spliceOpDump (o : PinOpDump) : Elab.TermElabM Unit := do
  let pinDecl := Declaration.defnDecl {
    name := o.pinName.toName, levelParams := [], type := exprT,
    value := o.pin.value, hints := .abbrev, safety := .safe }
  addDecl pinDecl
  compileDecl pinDecl
  let proofsName := o.proofsName.toName
  let mut proofConsts : List Lean.Expr := []
  for i in [0:o.proofs.size] do
    let elemName := proofsName.appendAfter s!"_{i}"
    let elemDecl := Declaration.defnDecl {
      name := elemName, levelParams := [], type := exprT,
      value := o.proofs[i]!.value, hints := .abbrev, safety := .safe }
    addDecl elemDecl
    compileDecl elemDecl
    proofConsts := proofConsts ++ [.const elemName []]
  let proofsDecl := Declaration.defnDecl {
    name := proofsName, levelParams := [],
    type := Lean.Expr.app (.const ``List [.zero]) exprT,
    value := proofConsts.foldr
      (fun p acc => mkApp3 (.const ``List.cons [.zero]) exprT p acc)
      (.app (.const ``List.nil [.zero]) exprT),
    hints := .abbrev, safety := .safe }
  addDecl proofsDecl
  compileDecl proofsDecl

/-- Parse a committed dump and splice every operation in it. -/
def loadPinsFromText (text : String) : Elab.Command.CommandElabM Unit := do
  let d ← match parseDumpFile text with
    | .ok d => pure d
    | .error e => throwError "bad pin dump: {e}"
  unless d.leanVersion == Lean.versionString do
    throwError "the committed pin dump was generated by Lean \
      {d.leanVersion} ({d.toolchain}), this is Lean {Lean.versionString}. \
      Regenerate with `lake exe natop-pins-export` (and see \
      Lech/Kernel/NatOpPins.lean for the toolchain-named file)."
  Elab.Command.liftTermElabM do
    for o in d.ops do
      spliceOpDump o

/-- `#load_natop_pins <string literal>` — splice the committed pin
dump.  The argument is meant to be an `include_str`, which elaborates
to a string literal, so the text is read off the syntax tree with no
evaluation. -/
elab "#load_natop_pins" s:term : command => do
  let text ← Elab.Command.liftTermElabM do
    let e ← instantiateMVars (← Elab.Term.elabTerm s (some (.const ``String [])))
    match e with
    | .lit (.strVal t) => pure t
    | _ =>
      throwError "#load_natop_pins expects a string literal \
        (an `include_str` of the committed dump)"
  loadPinsFromText text

def dumpLines (d : PinDumpFile) : Array String := Id.run do
  let mut out := #["{"]
  out := out.push ("\"format\":" ++ (Json.str dumpFormatTag).compress ++ ",")
  -- JSON has no comments, so the file's header is a pair of ignored
  -- fields (the reader only looks at the ones it knows).
  out := out.push ("\"_README\":" ++ (Json.str
    ("GENERATED FILE — do not edit.  The pinned Nat-operation defining \
     expressions and their certificate proof blobs, as share tables \
     (see Lech/PinGen/Dump.lean for the encoding).  Spliced into \
     Lech/Kernel/NatOpPins.lean by #load_natop_pins.")).compress ++ ",")
  out := out.push ("\"_regenerate\":" ++ (Json.str
    ("lake exe natop-pins-export   — then commit the result; \
     tests/pindump.sh (run from tests/arena.sh) diffs this file \
     against a fresh regeneration and fails if it is stale.")).compress
    ++ ",")
  out := out.push ("\"toolchain\":" ++ (Json.str d.toolchain).compress ++ ",")
  out := out.push
    ("\"leanVersion\":" ++ (Json.str d.leanVersion).compress ++ ",")
  out := out.push "\"ops\":["
  for oi in [0:d.ops.size] do
    let o := d.ops[oi]!
    out := out.push "{"
    out := out.push ("\"op\":" ++ (Json.str o.op).compress ++ ",")
    out := out.push ("\"pinName\":" ++ (Json.str o.pinName).compress ++ ",")
    out := out.push
      ("\"proofsName\":" ++ (Json.str o.proofsName).compress ++ ",")
    out := out.push "\"pin\":"
    out := out ++ blobLines o.pin ""
    out := out.push ",\"proofs\":["
    for pi in [0:o.proofs.size] do
      out := out ++ blobLines o.proofs[pi]! ""
      if pi + 1 != o.proofs.size then out := out.push ","
    out := out.push "]"
    out := out.push (if oi + 1 == d.ops.size then "}" else "},")
  out := out.push "]"
  out := out.push "}"
  return out

end Lech.PinGen
