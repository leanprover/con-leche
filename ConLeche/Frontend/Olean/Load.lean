module

public import ConLeche.Frontend.Olean.Fast
public import ConLeche.Frontend.ExportC
public import Std.Data.HashSet.Basic

@[expose] public section

/-!
# Reading `.olean` files: the import closure as one record stream (task #369)

`con-leche --olean M₁ … Mₙ` checks the modules `Mᵢ` and everything they
import, read from their `.olean` files.  This file turns the import
closure into the same `Declaration` records the lean4export reader
produces (`ConLeche/Frontend/ExportC.lean`), so that everything after
the parse — the prelude preparation, the install and the check, and the
main theorem about them — is the stream path's, unchanged.

**What is merged is what lean4export exports**: the closure loaded at
the PRIVATE level (each module-system module's `.olean.private`, whose
`ModuleData` holds the full constants — theorems with their proofs,
definitions with their bodies; a module outside the module system has
only its `.olean`), merged as Lean's own `finalizeImport` merges them,
and exported in lean4export's order:

1. **Loading** (`loadClosure`): the modules in import order, each
   module after its imports (a depth-first post-order from the roots, as
   `importModules` builds its module array), each module's files read,
   validated and decoded once by the decoder the caller passes — the
   driver passes the specification `decodeModuleSpec`
   (`ConLeche/Frontend/Olean/Spec.lean`), which the compiler replaces by
   the fast decoder.
2. **Merging** (`mergeEntry`): a name stored by two modules is kept once,
   by `subsumesInfo`'s rule (`Lean/Environment.lean`): the later copy
   replaces the earlier one when it subsumes it, the earlier one stays
   when it subsumes the later, and otherwise the closure is invalid —
   Lean's own import refuses it ("environment already contains").
3. **Emitting** (`emitAll`): lean4export's `dumpConstant` walk — every
   constant whose name is not internal is a root, every constant is
   emitted after the constants its type and value mention, an inductive
   block as one record with its constructors and recursors, the quotient
   package as its four records after `Eq`, unsafe and partial constants
   left out.  The walk is iterative (`Work` items on an explicit stack).
4. **Building** (`declsOf`): each emitted record becomes a `Declaration`
   through the stream reader's own builder `declOfF`, so the validation
   of inductive records (`validateIndF`) and every decline are the
   stream path's.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## Files -/

/-- The search path: the directories holding `.olean` trees, as
`LEAN_PATH` lists them. -/
abbrev SearchPath := List System.FilePath

/-- The file a module's level is stored in. -/
def modFile (dir : System.FilePath) (m : Name) (ext : String) : System.FilePath :=
  let rec comps : Name → List String
    | .anonymous => []
    | .str p s => comps p ++ [s]
    | .num p n => comps p ++ [toString n]
  (comps m).foldl (· / ·) dir |>.addExtension ext

/-- The first search-path directory holding the module's `.olean`. -/
def findModule (sp : SearchPath) (m : Name) : IO (Option System.FilePath) := do
  for d in sp do
    if ← (modFile d m "olean").pathExists then return some d
  return none

/-- Read and validate one file. -/
def readPart (p : System.FilePath) : IO (Except CheckError Part) := do
  let b ← IO.FS.readBinFile p
  pure (Part.ofBytes p.toString b)

/-! ## Dependencies -/

/-- A name from its components. -/
def mkN (cs : List String) : Name := cs.foldl .str .anonymous

/-- The DAG walk of `constsOf`. -/
partial def constsGo (stack : List Expr) (seen : Std.HashSet Expr) (seenN : Std.HashSet Name)
    (out : Array Name) : Array Name :=
  let add (n : Name) (s : Std.HashSet Name) (o : Array Name) :=
    if s.contains n then (s, o) else (s.insert n, o.push n)
  match stack with
  | [] => out
  | e :: rest =>
    -- leaves need no visited entry: only compound nodes are shared work
    match e with
    | .const n _ => let (s, o) := add n seenN out; constsGo rest seen s o
    | .lit (.natVal _) => let (s, o) := add (mkN ["Nat"]) seenN out; constsGo rest seen s o
    | .lit (.strVal _) =>
      let (s, o) := add (mkN ["Char", "ofNat"]) seenN out
      let (s, o) := add (mkN ["String", "ofList"]) s o
      constsGo rest seen s o
    | .bvar _ | .sort _ => constsGo rest seen seenN out
    | _ =>
      if seen.contains e then constsGo rest seen seenN out
      else
        let seen := seen.insert e
        match e with
        | .app f a => constsGo (f :: a :: rest) seen seenN out
        | .lam t b | .forallE t b => constsGo (t :: b :: rest) seen seenN out
        | .letE t v b => constsGo (t :: v :: b :: rest) seen seenN out
        | .proj _ _ x => constsGo (x :: rest) seen seenN out
        | .fvar _ t => constsGo (t :: rest) seen seenN out
        | _ => constsGo rest seen seenN out

/-- **The constants an expression mentions**, in first-visit order, and
the literal dependencies lean4export adds (`dumpNatDeps`,
`dumpStrDeps`): `Nat` for a numeral, `Char.ofNat` and `String.ofList`
for a string.  An iterative walk over the DAG, each node once. -/
def constsOf (es : List Expr) : Array Name := constsGo es {} {} #[]

/-! ## One module -/

/-- **One stored constant**, as the merge and the emitter need it: the
decoded `ConstantInfo` and the constants its type and values mention,
in first-visit order (`constsOf`, computed by the module's decode
worker). -/
structure CEntry extends CEntryF Name Expr where
  uses : Array Name := #[]

/-- lean4export's filter (`dumpConstant`): unsafe and partial constants
are not exported. -/
def CEntry.skipped (c : CEntry) : Bool :=
  match c.kind with
  | .ax u | .opaq _ u | .induct _ _ _ _ _ _ u _ | .ctor _ _ _ _ u | .recur _ _ _ _ _ _ _ u => u
  | .defn _ _ s => s != "safe"
  | .thm .. | .quot _ => false

/-- The constants a record depends on. -/
def CEntry.deps (c : CEntry) : List Expr :=
  match c.kind with
  | .defn v .. | .thm v _ | .opaq v _ => [c.type, v]
  | .recur _ _ _ _ _ rules _ _ => c.type :: rules.map (·.2.2)
  | _ => [c.type]

/-- A module decoder: the module stored in a region from its root
pointer, with its constants or its imports alone
(`decodeModuleSpec`). -/
abbrev Decoder := Region → UInt64 → Bool → Option ModDecoded

/-- A loaded module: its imports and its decoded constants. -/
structure Loaded where
  name : Name
  imports : Array Name
  constants : Array CEntry

/-- The module's files do not decode. -/
def undecodable (m : Name) : CheckError :=
  .internal s!"module {m}: malformed .olean data (an object of the wrong shape, or a \
    pointer that does not point below its object)"

/-- **Load one module**: its `.olean`, and for a module of the module
system its `.olean.server` and `.olean.private`, decoded from the
private part's root. -/
def loadModule (dec : Decoder) (sp : SearchPath) (m : Name) :
    IO (Except CheckError Loaded) := do
  let some dir ← findModule sp m
    | return .error (.internal s!"module {m}: no .olean on the search path")
  let ex ← readPart (modFile dir m "olean")
  let ex ← match ex with
    | .ok p => pure p
    | .error e => return .error e
  -- the exported part's root says whether the module is a module-system
  -- one (the `isModule` byte of its `ModuleData`)
  let some sk := moduleSkel (Region.single ex) ex.root
    | return .error (undecodable m)
  let (r, root) ← if sk.isModule then do
      let sv ← readPart (modFile dir m "olean.server")
      let pv ← readPart (modFile dir m "olean.private")
      match sv, pv with
      | .ok s, .ok p =>
        match Region.ofParts #[ex, s, p] with
        | .ok r => pure (r, p.root)
        | .error e => return .error e
      | .error e, _ | _, .error e => return .error e
    else pure (Region.single ex, ex.root)
  match dec r root true with
  | some d =>
    pure (.ok ⟨m, d.imports, d.constants.map fun c =>
      let c : CEntry := { toCEntryF := c }
      { c with uses := constsOf c.deps }⟩)
  | none => pure (.error (undecodable m))

/-! ## The closure -/

/-- A module's imports, read off its exported `.olean` alone. -/
def moduleImports (dec : Decoder) (sp : SearchPath) (m : Name) :
    IO (Except CheckError (Array Name)) := do
  let some dir ← findModule sp m
    | return .error (.internal s!"module {m}: no .olean on the search path")
  match ← readPart (modFile dir m "olean") with
  | .error e => pure (.error e)
  | .ok ex =>
    match dec (Region.single ex) ex.root false with
    | some d => pure (.ok d.imports)
    | none => pure (.error (undecodable m))

/-- **The import closure, in Lean's module order**: a module after
everything it imports, the roots and each module's imports in their
order (a depth-first post-order, as `importModules` builds its module
array).  An explicit stack (`(module, imports expanded?)`) instead of
recursion. -/
partial def closureGo (dec : Decoder) (sp : SearchPath) (stack : List (Name × Bool))
    (seen : Std.HashSet Name) (out : Array Name) : IO (Except CheckError (Array Name)) := do
  match stack with
  | [] => pure (.ok out)
  | (m, true) :: rest => closureGo dec sp rest seen (out.push m)
  | (m, false) :: rest =>
    if seen.contains m then closureGo dec sp rest seen out
    else
      match ← moduleImports dec sp m with
      | .error e => pure (.error e)
      | .ok imps =>
        let kids := imps.toList.filter (!seen.contains ·) |>.map (·, false)
        closureGo dec sp (kids ++ (m, true) :: rest) (seen.insert m) out

def closureOrder (dec : Decoder) (sp : SearchPath) (roots : Array Name) :
    IO (Except CheckError (Array Name)) :=
  closureGo dec sp (roots.toList.map (·, false)) {} #[]

/-- The modules decoded one after the other. -/
partial def loadSerial (dec : Decoder) (sp : SearchPath) (ms : List Name) (out : Array Loaded) :
    IO (Except CheckError (Array Loaded)) := do
  match ms with
  | [] => pure (.ok out)
  | m :: rest =>
    match ← loadModule dec sp m with
    | .error e => pure (.error e)
    | .ok l => loadSerial dec sp rest (out.push l)

/-- **The closure, loaded**: its modules in Lean's order, decoded.  The
decode of a module needs nothing of any other module, so above one
worker the modules are dealt round-robin to `jobs` workers, each
decoding its share one after the other (so at most `jobs` modules are
in flight, and their memos are the only per-module memory alive), and
the results are put back in module order; the first failure in that
order is the one reported. -/
def loadClosure (dec : Decoder) (sp : SearchPath) (roots : Array Name) (jobs : Nat := 1) :
    IO (Except CheckError (Array Loaded)) := do
  match ← closureOrder dec sp roots with
  | .error e => pure (.error e)
  | .ok order =>
    if jobs ≤ 1 then loadSerial dec sp order.toList #[]
    else
      let w := min jobs order.size
      let shares := (List.range w).map fun k =>
        (List.range order.size).filter (· % w == k) |>.filterMap (order[·]?)
      let tasks ← shares.toArray.mapM fun ms =>
        IO.asTask (prio := .dedicated) (loadSerial dec sp ms #[])
      let mut parts : Array (Array Loaded) := #[]
      for t in tasks do
        match ← IO.wait t with
        | .ok (.ok ls) => parts := parts.push ls
        | .ok (.error e) => return .error e
        | .error ioe => return .error (.internal s!"reading the oleans: {ioe}")
      -- module `i` is element `i / w` of share `i % w`
      let out := (List.range order.size).filterMap fun i =>
        (parts[i % w]?).bind (·[i / w]?)
      pure (.ok out.toArray)

/-! ## The merge -/

/-- Lean's `isPropCheap`: the statement is a telescope over a constant
applied to as many arguments as its own type has binders before a
`Prop` result. -/
def isPropCheap (m : Std.HashMap Name CEntry) (ty : Expr) : Bool :=
  let rec body : Expr → Expr
    | .forallE _ b => body b
    | e => e
  let rec head : Expr → Nat → Option (Name × Nat)
    | .app f _, k => head f (k + 1)
    | .const n _, k => some (n, k)
    | _, _ => none
  let rec drop : Expr → Nat → Option Expr
    | e, 0 => some e
    | .forallE _ b, k + 1 => drop b k
    | _, _ => none
  match head (body ty) 0 with
  | some (n, k) =>
    match m[n]? with
    | some d => match drop d.type k with
      | some (.sort .zero) => true
      | _ => false
    | none => false
  | none => false

/-- `subsumesInfo` (`Lean/Environment.lean`): may `c₁` stand for `c₂`? -/
def subsumes (m : Std.HashMap Name CEntry) (c₁ c₂ : CEntry) : Bool :=
  c₁.name == c₂.name && c₁.type == c₂.type && c₁.levelParams == c₂.levelParams &&
  match c₁.kind, c₂.kind with
  | .thm _ a₁, .thm _ a₂ => a₁ == a₂
  | .thm _ a₁, .ax u₂ => a₁ == [c₂.name] && !u₂
  | .ax u₁, .ax u₂ => u₁ == u₂ && isPropCheap m c₁.type
  | _, _ => false

/-- The merged constants and the order they were first stored in. -/
structure Merged where
  map : Std.HashMap Name CEntry := {}
  order : Array Name := #[]

/-- **Merge one constant** (`finalizeImport`'s rule). -/
def mergeEntry (mg : Merged) (c : CEntry) : Except CheckError Merged :=
  match mg.map[c.name]? with
  | none =>
    let { map, order } := mg
    pure { map := map.insert c.name c, order := order.push c.name }
  | some prev =>
    if subsumes mg.map c prev then
      let { map, order } := mg
      pure { map := map.insert c.name c, order }
    else if subsumes mg.map prev c then pure mg
    else throw (.invalid s!"two modules store different constants named {c.name}")

def mergeAll (ls : Array Loaded) : Except CheckError Merged :=
  ls.foldlM (fun mg l => l.constants.foldlM mergeEntry mg) {}

/-! ## The emission order -/

/-- Lean's `Name.isInternal`: some component starts with `_`. -/
def Name.isInternal : Name → Bool
  | .str p s => s.front == '_' || Name.isInternal p
  | .num p _ => Name.isInternal p
  | .anonymous => false

/-- One step of the emission walk. -/
inductive Work where
  | visit (n : Name)
  | one (c : CEntry)
  | quot (cs : List CEntry)
  | block (tys ctors recs : List CEntry)

/-- The emitter's output: the record stream in the stream reader's
syntax (`DeclRec`, indices into the two tables). -/
structure Emit where
  visited : Std.HashSet Name := {}
  names : Array Name := #[]
  exprs : Array Expr := #[]
  out : Array DeclRec := #[]

/-! The updates below take the field out of the record before changing
it, so that the array or set is changed at reference count 1 (the
`DS.mark` in `ConLeche/Frontend/Olean/Fast.lean` says why). -/

def Emit.name (st : Emit) (n : Name) : Emit × Nat :=
  let { visited, names, exprs, out } := st
  let i := names.size
  ({ visited, names := names.push n, exprs, out }, i)

def Emit.expr (st : Emit) (e : Expr) : Emit × Nat :=
  let { visited, names, exprs, out } := st
  let i := exprs.size
  ({ visited, names, exprs := exprs.push e, out }, i)

def Emit.push (st : Emit) (d : DeclRec) : Emit :=
  let { visited, names, exprs, out } := st
  { visited, names, exprs, out := out.push d }

def Emit.mark (st : Emit) (n : Name) : Emit :=
  let { visited, names, exprs, out } := st
  { visited := visited.insert n, names, exprs, out }

def Emit.cv (st : Emit) (c : CEntry) : Emit × CVRec :=
  let (st, n) := st.name c.name
  let (st, lps) := c.levelParams.foldl (fun (st, acc) p =>
    let (st, i) := st.name p; (st, acc.push i)) (st, #[])
  let (st, t) := st.expr c.type
  (st, ⟨n, lps.toList, t⟩)

def Emit.names' (st : Emit) (ns : List Name) : Emit × List Nat :=
  let (st, acc) := ns.foldl (fun (st, acc) p =>
    let (st, i) := st.name p; (st, acc.push i)) (st, #[])
  (st, acc.toList)

/-- **One constant's record.** -/
def Emit.one (st : Emit) (c : CEntry) : Emit :=
  let (st, cv) := st.cv c
  let (st, d) : Emit × Option DeclRec := match c.kind with
    | .ax u => (st, some (.ax cv u))
    | .defn v h s => let (st, i) := st.expr v; (st, some (.defn cv i h s))
    | .thm v _ => let (st, i) := st.expr v; (st, some (.thm cv i))
    | .opaq v u => let (st, i) := st.expr v; (st, some (.opaq cv i u))
    | .quot k => (st, some (.quot cv k))
    | _ => (st, none)
  match d with
  | some d => st.push d
  | none => st

/-- **An inductive block's record**: lean4export's `inductive` object. -/
def Emit.block (st : Emit) (tys ctors recs : List CEntry) : Emit :=
  let (st, ts) := tys.foldl (fun (st, acc) c =>
    match c.kind with
    | .induct np ni _ cs nn ir iu irf =>
      let (st, cv) := st.cv c
      let (st, cs) := st.names' cs
      (st, acc.push { cv, ctors := cs, isRec := ir, isReflexive := irf, isUnsafe := iu,
                      numIndices := ni, numNested := nn, numParams := np : IndTypeRec })
    | _ => (st, acc)) (st, #[])
  let (st, cts) := ctors.foldl (fun (st, acc) c =>
    match c.kind with
    | .ctor ind cidx np nf iu =>
      let (st, cv) := st.cv c
      let (st, ii) := st.name ind
      (st, acc.push { cv, isUnsafe := iu, numFields := nf, numParams := np,
                      cidx := some cidx, induct := some ii : IndCtorRec })
    | _ => (st, acc)) (st, #[])
  let (st, rs) := recs.foldl (fun (st, acc) c =>
    match c.kind with
    | .recur _ np ni nmo nmi rules k iu =>
      let (st, cv) := st.cv c
      let (st, rr) := rules.foldl (fun (st, acc) (cn, nf, rhs) =>
        let (st, ci) := st.name cn
        let (st, ri) := st.expr rhs
        (st, acc.push ({ ctor := ci, nfields := nf, rhs := ri } : RuleRec))) (st, #[])
      (st, acc.push { cv, isUnsafe := iu, k, numIndices := ni, numMinors := nmi,
                      numMotives := nmo, numParams := np, rules := rr.toList : IndRecRec })
    | _ => (st, acc)) (st, #[])
  st.push (.ind ts.toList cts.toList rs.toList)

/-- **The emission walk** (lean4export's `dumpConstant`, iterative):
`visit n` emits `n`'s record after its dependencies. -/
partial def emitLoop (mg : Merged) (recMap : Std.HashMap Name (Array Name))
    (stack : List Work) (st : Emit) : Emit :=
  match stack with
  | [] => st
  | .one c :: rest => emitLoop mg recMap rest (st.one c)
  | .quot cs :: rest => emitLoop mg recMap rest (cs.foldl Emit.one st)
  | .block ts cs rs :: rest => emitLoop mg recMap rest (st.block ts cs rs)
  | .visit n :: rest =>
    if st.visited.contains n then emitLoop mg recMap rest st else
    match mg.map[n]? with
    | none => emitLoop mg recMap rest st
    | some c =>
      if c.skipped then emitLoop mg recMap rest st else
      let st := st.mark n
      let visits (cs : List CEntry) : List Work :=
        cs.flatMap fun c => c.uses.toList.map Work.visit
      match c.kind with
      | .ax _ | .defn .. | .thm .. | .opaq .. =>
        emitLoop mg recMap (visits [c] ++ Work.one c :: rest) st
      | .quot _ =>
        let qs := [mkN ["Quot"], mkN ["Quot", "mk"], mkN ["Quot", "lift"], mkN ["Quot", "ind"]].filterMap (mg.map[·]?)
        let st := qs.foldl (fun st q => st.mark q.name) st
        emitLoop mg recMap (Work.visit (mkN ["Eq"]) :: Work.quot qs :: rest) st
      | .ctor ind .. => emitLoop mg recMap (Work.visit ind :: rest) st
      | .recur all .. => emitLoop mg recMap (all.map Work.visit ++ rest) st
      | .induct _ _ all _ _ _ _ _ =>
        let tys : List CEntry := all.filterMap (mg.map[·]?)
        let ctors := tys.flatMap fun t => match t.kind with
          | .induct _ _ _ cs _ _ _ _ => cs.filterMap (mg.map[·]?)
          | _ => []
        let recs : List CEntry := ((recMap[n]?).getD #[]).toList.filterMap (mg.map[·]?)
        let st := (tys ++ ctors ++ recs).foldl
          (fun st x => st.mark x.name) st
        emitLoop mg recMap (visits (tys ++ ctors ++ recs) ++ Work.block tys ctors recs :: rest) st

/-- **The record stream of the merged closure.** -/
def emitAll (mg : Merged) : Emit :=
  let recMap := mg.order.foldl (fun (m : Std.HashMap Name (Array Name)) n =>
    match (mg.map[n]?).map (·.kind) with
    | some (CKindF.recur all ..) =>
      all.foldl (fun m i => m.alter i fun
        | none => some #[n]
        | some a => some (if a.contains n then a else a.push n)) m
    | _ => m) {}
  let roots := mg.order.filter (!Name.isInternal ·)
  emitLoop mg recMap (roots.toList.map .visit) {}

/-! ## The records -/

/-- **The `Declaration` records**, through the stream reader's builder.
A record's verdict (a decline, a contradiction between its fields) is
the stream path's, at the record's position. -/
def declsOf (em : Emit) : Except (CheckError × Nat) (Array Declaration) :=
  let nm (i : Nat) : M Name := match em.names[i]? with
    | some n => pure n | none => throw s!"undefined name index {i}"
  let lv (_ : Nat) : M Level := throw "no level table"
  let ex (i : Nat) : M Expr := match em.exprs[i]? with
    | some e => pure e | none => throw s!"undefined expr index {i}"
  em.out.size.fold (init := .ok #[]) fun k _ acc => do
    let ds ← acc
    match declOfF nm lv ex em.out[k] with
    | .ok (.inl d) => pure (ds.push d)
    | .ok (.inr v) => throw (v.toError, k)
    | .error msg => throw (.internal msg, k)

/-- **The whole read**: load, merge, emit, build. -/
def readOleans (dec : Decoder) (sp : SearchPath) (roots : Array Name) (jobs : Nat := 1) :
    IO (Except (CheckError × Nat) (Array Declaration)) := do
  match ← loadClosure dec sp roots jobs with
  | .error e => pure (.error (e, 0))
  | .ok ls =>
    match mergeAll ls with
    | .error e => pure (.error (e, 0))
    | .ok mg => pure (declsOf (emitAll mg))

end ConLeche.Frontend.Olean
