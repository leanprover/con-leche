import ConLeche.Frontend.Stream
import ConLeche.Frontend.Olean
import ConLeche.Driver.CheckMain
import ConLeche.Driver.Reach
/- NOT a `module`, like `PinDump.lean`: a development tool, not part of
the checker.  As a `module` it would have to be a root of
`tests/shake.sh`, whose `lake shake` loads every root into one
environment, and its `main` collides with `Main.lean`'s. -/

/-!
# `olean-compare` — the olean reader against lean4export

    lake exe olean-compare [--constant=NAME]... EXPORT.ndjson SEARCHPATH MODULE...
    lake exe olean-compare --views SEARCHPATH MODULE...
    lake exe olean-compare --home SEARCHPATH MODULE...
    lake exe olean-compare --reads [--jobs=N] [--loads] [--levels] SEARCHPATH MODULE
    lake exe olean-compare --reach [--jobs=N] [--list] SEARCHPATH MODULE

Parses a lean4export stream of `MODULE...` with the stream reader and
the same modules' import closure with the olean reader
(`ConLeche/Frontend/Olean/Records.lean`), and compares the two
`Declaration` arrays as maps from a record's first declared name to
the record.  Two orders lean4export takes from hash-map and `NameSet`
iteration are normalised before comparing: the record order itself
(hence the map) and the order of the recursors inside an inductive
block (sorted by name).  Prints the records present on one side only
and the records that differ, and exits 1 if there are any, if either
side has two records of one key, or if the two sides' record counts
differ (so the maps' equality is equality record for record).

`--views` reads every module of the closure at its home (`readAllViews`: all three
views with one memo, checked against each other) and compares each view with
`readView`'s; exit 0, or the first failure's exit code.

`--home` is each module's home read alone (`homeOf` over its private part's files: the private
view loaded, its three parts checked against each other); exit 0, or the first failure's exit code.

`--reads` is a worker's reads at one module (`workerReads`: the header fixpoint, the
name index of the loaded parts, Lean's clash rule and freshness), with their counts;
`--loads` prints each loaded module with its flags, in the order, for comparing with
Lean's own `importModules`; `--levels` stops after the header fixpoint and the
public-import closures.  Exit 0, or the failure's exit code.

`--reach` is a worker's context at one module (`reach`, after `workerReads`): the reach
from the names the module's own records read, the completion, the capture check, the
proof flags at clashes, the context's validation, with its counts; `--list` prints each
context record's first name and home and each completed name.  Exit 0, or the failure's
exit code.

A development tool, not a default target: the gate it gives
(`tests/olean-compare.sh`, in the standard battery) is the statement "the
olean reader produces exactly the records lean4export writes".
-/

open ConLeche

def normalize : Declaration → Declaration
  | .indDecl block np =>
    let isRec : ConstantInfo → Bool := fun | .recInfo .. => true | _ => false
    let recs := block.filter isRec
    let rest := block.filter (!isRec ·)
    let key (c : ConstantInfo) : String := toString c.name
    .indDecl (rest ++ (recs.toArray.qsort (key · < key ·)).toList) np
  | d => d

/-! The records are compared field by field with every `Expr` compared
by its `BEq` instance (`Expr.beq`: pointer-equality first, memoized on
pointer pairs).  The derived `DecidableEq Declaration` once compared
`Expr`s by the derived tree walk, exponential on the sharing in
Mathlib's proof terms (a full-Mathlib compare spent more than 20
minutes in it without finishing a record pass); since task #554 that
instance reaches `Expr.decEqPtr`, but the field-by-field comparison
stays explicit. -/

def valEq (a b : ConstantVal) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type

/-- The right-hand side by `Expr.beq`, the other (scalar) fields by
their decidable equality. -/
def ruleEq (a b : RecRule) : Bool :=
  a.rhs == b.rhs && decide ({ a with rhs := .bvar 0 } = { b with rhs := .bvar 0 })

def listEq {α} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listEq f as bs
  | _, _ => false

def infoEq : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo v, .axiomInfo w => valEq v w
  | .defnInfo v e h, .defnInfo w e' h' => valEq v w && e == e' && decide (h = h')
  | .thmInfo v, .thmInfo w => valEq v w
  | .indInfo v c, .indInfo w c' => valEq v w && decide (c = c')
  | .ctorInfo v p f t, .ctorInfo w p' f' t' => valEq v w && p == p' && f == f' && t == t'
  | .recInfo v m r k rs, .recInfo w m' r' k' rs' =>
    valEq v w && m == m' && r == r' && k == k' && listEq ruleEq rs rs'
  | _, _ => false

def declEq : Declaration → Declaration → Bool
  | .axiomDecl v, .axiomDecl w => valEq v w
  | .defnDecl v e h, .defnDecl w e' h' => valEq v w && e == e' && decide (h = h')
  | .thmDecl v e, .thmDecl w e' => valEq v w && e == e'
  | .opaqueDecl v e, .opaqueDecl w e' => valEq v w && e == e'
  | .indDecl b n, .indDecl b' n' => listEq infoEq b b' && n == n'
  | .quotDecl k v, .quotDecl k' w => decide (k = k') && valEq v w
  | _, _ => false

/-- A one-component name. -/
def nm (s : String) : Name := .str .anonymous s

/-- A term of tree size `2^n` and DAG size `n`: `x ↦ x x`, iterated
`n` times on the constant `c`. -/
def dag (c : Name) : Nat → Expr
  | 0 => .const c []
  | n + 1 => let x := dag c n; .app x x

/-- `dag` again, so that the two sides of a comparison are equal
without being pointer-equal. -/
def dag' (c : Name) : Nat → Expr
  | 0 => .const c []
  | n + 1 => let x := dag' c n; .app x x

/- Regression (the Mathlib compare): records whose `Expr`s share like
proof terms do.  Under the derived `DecidableEq` each would walk 2^200
nodes. -/
#guard declEq (.thmDecl ⟨nm "t", [], .sort .zero⟩ (dag (nm "a") 200))
              (.thmDecl ⟨nm "t", [], .sort .zero⟩ (dag' (nm "a") 200))
#guard !declEq (.thmDecl ⟨nm "t", [], .sort .zero⟩ (.app (dag (nm "a") 200) (.const (nm "a") [])))
               (.thmDecl ⟨nm "t", [], .sort .zero⟩ (.app (dag' (nm "a") 200) (.const (nm "b") [])))
#guard !declEq (.indDecl [.recInfo ⟨nm "r", [], .sort .zero⟩ 0 0 false
                  [{ ctor := nm "c", nfields := 0, fire := .plain, rhs := dag (nm "a") 200 }]] 0)
               (.indDecl [.recInfo ⟨nm "r", [], .sort .zero⟩ 0 0 false
                  [{ ctor := nm "c", nfields := 1, fire := .plain, rhs := dag' (nm "a") 200 }]] 0)

def toMap (ds : Array Declaration) : Std.HashMap Name Declaration × Nat :=
  ds.foldl (fun (m, dup) d =>
    let k := (d.names.head?).getD .anonymous
    if m.contains k then (m, dup + 1) else (m.insert k (normalize d), dup)) ({}, 0)

/-- A view's constants by the checker's equality. -/
def viewsEq (a b : Frontend.Olean.ModDecoded) : Bool :=
  a.isModule == b.isModule && a.imports == b.imports && a.constants.size == b.constants.size &&
    (a.constants.zip b.constants).all fun (x, y) => Frontend.Olean.entrySame x y

open Frontend.Olean in
/-- `--views`: every module of the closure. -/
def runViews (sp : List System.FilePath) (roots : Array Name) : IO UInt32 := do
  let (order, sp) ← match ← (closureOrder sp roots : IO _) with
    | .ok o => pure o
    | .error e => IO.eprintln s!"closure: {e}"; return e.exitCode.toUInt32
  for m in order do
    let (v, _) ← match ← (readAllViews sp m : IO _) with
      | .ok x => pure x
      | .error e => IO.eprintln s!"{e}"; return e.exitCode.toUInt32
    for level in [OLeanLevel.exported, .server, .private] do
      let d ← match ← (readView sp m level : IO _) with
        | .ok d => pure d
        | .error e => IO.eprintln s!"{e}"; return e.exitCode.toUInt32
      unless viewsEq d (v.at level) do
        IO.eprintln s!"module {m}: the {repr level} view differs from the home's"
        return 3
  IO.println s!"{order.size} modules: every view read, one memo, agrees"
  return 0

open Frontend.Olean in
/-- `--home`: each module's home read. -/
def runHome (sp : List System.FilePath) (mods : Array Name) : IO UInt32 := do
  for m in mods do
    match (← (readFiles sp m .private : IO _)).bind (homeOf m) with
    | .ok (l, expo) =>
      let n (x : Expo) := (expo.filter (· == x)).size
      IO.println s!"{m}: {l.constants.size} constants, exported {n .same} same, {n .hidden} hidden, \
        {n .absent} absent"
    | .error e => IO.eprintln s!"{e}"; return e.exitCode.toUInt32
  return 0

open Frontend.Olean in
/-- `--reads`: a worker's reads at one module. -/
def runReads (sp : List System.FilePath) (m : Name) (jobs : Nat) (dump levelsOnly : Bool) :
    IO UInt32 := do
  if levelsOnly then
    match ← (readPartNames sp (m, .private) : IO _) with
    | .error e => IO.eprintln s!"{e}"; return e.exitCode.toUInt32
    | .ok own =>
      match ← (headerFixpoint (moduleImports sp) own.header.isModule own.header.imports : IO _) with
      | .error e => IO.eprintln s!"{e}"; return e.exitCode.toUInt32
      | .ok ld =>
        let pub := pubClosures ld
        IO.println s!"{m}: loads {ld.order.size} modules; {pub.size} public-import closures"
        return 0
  match ← (workerReads (.ofPath sp) m jobs : IO _) with
  | .error e => IO.eprintln s!"{e}"; return e.exitCode.toUInt32
  | .ok w =>
    let ld := w.loads
    if dump then
      for (n, fl) in ld.order.zip ld.flags do
        IO.println s!"load {n} {fl.importAll} {fl.isExported}"
    let priv := (ld.flags.filter (·.importAll)).size
    let names := w.index.first.size
    let pubAvg := if ld.order.isEmpty then 0 else
      (w.pub.foldl (fun n s => n + s.card) 0) / ld.order.size
    let merged := w.clashes.foldl (fun n c => n + c.copies.size) 0
    IO.println s!"{m}: own {w.own.consts.size} constants; loads {ld.order.size} modules \
      ({priv} private, {ld.order.size - priv} exported); {names} names, \
      {w.index.more.size} later copies; {w.clashes.size} names held twice ({merged} copies), merged; \
      public-import closure {pubAvg} modules on average"
    return 0

open Frontend.Olean Driver in
/-- `--reach`: a worker's context at one module. -/
def runReach (sp : List System.FilePath) (m : Name) (jobs : Nat) (list : Bool) : IO UInt32 := do
  let fail (e : CheckError) : IO UInt32 := do IO.eprintln s!"{e}"; return e.exitCode.toUInt32
  match ← (workerReads (.ofPath sp) m jobs : IO _) with
  | .error e => fail e
  | .ok w =>
    match ← (readFiles sp m .private : IO _) with
    | .error e => fail e
    | .ok f =>
      match loadView 0 m f with
      | .error e => fail e
      | .ok l =>
        let own : Std.HashSet Name := l.constants.foldl (fun s c => s.insert c.name) {}
        let cs := l.constants.toList.filter (!·.skipped)
        let mg := mergedOfList cs
        match declsOf (emitAll mg (cs.map (·.name)).toArray) with
        | .error (e, _) => fail e
        | .ok ds =>
          let roots := ds.foldl (fun acc d => acc ++ Cached.recordReads d) #[] ++
            cs.foldl (fun acc c => acc ++ c.uses.toArray) #[]
          match ← (reach (.ofPath sp) m w own roots : IO _) with
          | .error e => fail e
          | .ok r =>
            let consts := r.ctx.foldl (fun n d => n + (declConstants d).length) 0
            let groups := (r.ctx.filter fun | .indDecl .. => true | _ => false).size
            let mods := (r.homes.foldl (fun (s : Std.HashSet Name) h => s.insert h) {}).size
            if list then
              for (d, h) in r.ctx.zip r.homes do
                IO.println s!"ctx {((Modular.declNames d).head?).getD .anonymous} {h}"
              for (y, h) in r.completed do
                IO.println s!"completed {y} in the view of {h}"
            IO.println s!"{m}: own {ds.size} records; loads {w.loads.order.size} modules, \
              {w.index.first.size} names; reach {r.ctx.size} records ({consts} constants, \
              {groups} groups) from {mods} modules; {r.completed.size} completed; \
              {r.searches} searches; {r.inferred} flags inferred"
            return 0

/-- Lean's `Name.isInternal`: lean4export's default roots leave out the constants so named,
which the reader starts from, so a record only the reader has must be so named. -/
def internalName : Name → Bool
  | .str p s => s.front == '_' || internalName p
  | .num p _ => internalName p
  | .anonymous => false

def main (args : List String) : IO UInt32 := do
  let (flags, args) := args.partition (·.startsWith "--constant=")
  let named := flags.toArray.filterMap fun s =>
    Frontend.Olean.parseConstName (s.drop "--constant=".length).toString
  let constants := if named.isEmpty then none else some named
  match args with
  | "--home" :: sp :: mods@(_ :: _) =>
    runHome ((sp.splitOn ":").map System.FilePath.mk) (mods.toArray.filterMap Frontend.Olean.parseModName)
  | "--reads" :: rest =>
    let (opts, rest) := rest.partition (·.startsWith "--")
    let jobs := (opts.findSome? fun o => (o.dropPrefix? "--jobs=").bind (·.toString.toNat?)).getD 1
    match rest with
    | [sp, m] =>
      match Frontend.Olean.parseModName m with
      | some m =>
        runReads ((sp.splitOn ":").map System.FilePath.mk) m jobs (opts.contains "--loads")
          (opts.contains "--levels")
      | none => IO.eprintln s!"not a module name: {m}"; return 3
    | _ => IO.eprintln "usage: olean-compare --reads [--jobs=N] [--loads] [--levels] SEARCHPATH MODULE"; return 3
  | "--reach" :: rest =>
    let (opts, rest) := rest.partition (·.startsWith "--")
    let jobs := (opts.findSome? fun o => (o.dropPrefix? "--jobs=").bind (·.toString.toNat?)).getD 1
    match rest with
    | [sp, m] =>
      match Frontend.Olean.parseModName m with
      | some m => runReach ((sp.splitOn ":").map System.FilePath.mk) m jobs (opts.contains "--list")
      | none => IO.eprintln s!"not a module name: {m}"; return 3
    | _ => IO.eprintln "usage: olean-compare --reach [--jobs=N] [--list] SEARCHPATH MODULE"; return 3
  | "--views" :: sp :: mods@(_ :: _) =>
    runViews ((sp.splitOn ":").map System.FilePath.mk) (mods.toArray.filterMap Frontend.Olean.parseModName)
  | file :: sp :: mods@(_ :: _) =>
    let t0 ← IO.monoMsNow
    let js ← match ← (Frontend.parseFileS file : IO _) with
      | .ok r => pure r.decls
      | .error (e, l) => IO.eprintln s!"stream: {e} at line {l}"; return 3
    let t1 ← IO.monoMsNow
    let roots := mods.toArray.filterMap Frontend.Olean.parseModName
    let os ← match ← Frontend.Olean.readOleansFull ((sp.splitOn ":").map System.FilePath.mk) roots constants (jobs := 8) with
      | .ok ds => pure ds
      | .error (e, l) => IO.eprintln s!"oleans: {e} at record {l}"; return 3
    let t2 ← IO.monoMsNow
    IO.println s!"stream: {js.size} records ({t1 - t0} ms); oleans: {os.size} records ({t2 - t1} ms)"
    let (jm, jd) := toMap js
    let (om, od) := toMap os
    IO.println s!"duplicate keys: stream {jd}, oleans {od}"
    let mut bad := 0
    let mut shown := 0
    for (k, d) in jm do
      match om[k]? with
      | none =>
        bad := bad + 1
        if shown < 20 then IO.println s!"only in the stream: {k}"; shown := shown + 1
      | some d' =>
        unless declEq d d' do
          bad := bad + 1
          if shown < 20 then
            IO.println s!"differs: {k}\n  stream: {(repr d).pretty 200 |>.take 600}\n  oleans: {(repr d').pretty 200 |>.take 600}"
            shown := shown + 1
    let mut extra := 0
    for (k, _) in om do
      unless jm.contains k do
        -- the export's default roots are the names that are not internal, so a record
        -- it does not have must be under an internal name
        if constants.isNone && internalName k then extra := extra + 1
        else
          bad := bad + 1
          if shown < 40 then IO.println s!"only in the oleans: {k}"; shown := shown + 1
    -- record for record: a key two records share, or a
    -- different number of records, is a difference the maps hide
    let countDiff := if js.size + extra == os.size then 0 else 1
    IO.println s!"{extra} records under internal names, which the export's default leaves out"
    IO.println s!"{jm.size} stream keys, {om.size} olean keys, {bad} differences, \
      {jd + od} duplicate keys, {js.size} / {os.size} records"
    return if bad == 0 && jd == 0 && od == 0 && countDiff == 0 then 0 else 1
  | _ =>
    IO.eprintln "usage: olean-compare EXPORT.ndjson SEARCHPATH MODULE..."
    return 3
