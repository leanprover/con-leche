import ConLeche.Frontend.Stream
import ConLeche.Frontend.Olean
import ConLeche.Driver.CheckMain
/- NOT a `module`, like `PinDump.lean`: a development tool, not part of
the checker.  As a `module` it would have to be a root of
`tests/shake.sh`, whose `lake shake` loads every root into one
environment, and its `main` collides with `Main.lean`'s. -/

/-!
# `olean-compare` — the olean reader against lean4export

    lake exe olean-compare [--constant=NAME]... EXPORT.ndjson SEARCHPATH MODULE...
    lake exe olean-compare --views SEARCHPATH MODULE...

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
pointer pairs), never by the derived `DecidableEq Declaration`, whose
`Expr` comparison is the derived tree walk: exponential on the sharing
in Mathlib's proof terms (a full-Mathlib compare spent more than 20
minutes in `instDecidableEqExpr` without finishing a record pass). -/

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
  | .ctorInfo v p f, .ctorInfo w p' f' => valEq v w && p == p' && f == f'
  | .recInfo v m r rs, .recInfo w m' r' rs' =>
    valEq v w && m == m' && r == r' && listEq ruleEq rs rs'
  | _, _ => false

def declEq : Declaration → Declaration → Bool
  | .axiomDecl v, .axiomDecl w => valEq v w
  | .defnDecl v e h, .defnDecl w e' h' => valEq v w && e == e' && decide (h = h')
  | .thmDecl v e, .thmDecl w e' => valEq v w && e == e'
  | .opaqueDecl v e, .opaqueDecl w e' => valEq v w && e == e'
  | .basisDecl k, .basisDecl k' => decide (k = k')
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
#guard !declEq (.indDecl [.recInfo ⟨nm "r", [], .sort .zero⟩ 0 0
                  [{ ctor := nm "c", nfields := 0, ctorParams := 0, fire := .plain,
                     rhs := dag (nm "a") 200 }]] 0)
               (.indDecl [.recInfo ⟨nm "r", [], .sort .zero⟩ 0 0
                  [{ ctor := nm "c", nfields := 0, ctorParams := 0, fire := .plain,
                     rhs := dag' (nm "a") 200, k := true }]] 0)

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
  let order ← match ← (closureOrder sp roots : IO _) with
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
