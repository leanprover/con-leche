import ConLeche.Frontend.Stream
import ConLeche.Frontend.Olean.Load
/- NOT a `module`, like `PinDump.lean`: a development tool, not part of
the checker.  As a `module` it would have to be a root of
`tests/shake.sh`, whose `lake shake` loads every root into one
environment, and its `main` collides with `Main.lean`'s. -/

/-!
# `olean-compare` — the olean reader against lean4export (task #369)

    lake exe olean-compare EXPORT.ndjson SEARCHPATH MODULE...

Parses a lean4export stream of `MODULE...` with the stream reader and
the same modules' import closure with the olean reader
(`ConLeche/Frontend/Olean/Load.lean`), and compares the two
`Declaration` arrays as maps from a record's first declared name to
the record.  Two orders lean4export takes from hash-map and `NameSet`
iteration are normalised before comparing: the record order itself
(hence the map) and the order of the recursors inside an inductive
block (sorted by name).  Prints the records present on one side only
and the records that differ, and exits 1 if there are any.

A development tool, not a default target: the gate it gives is the
statement "the olean reader produces exactly the records lean4export
writes", re-run when the reader or the toolchain changes.
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

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--time-stream", file] =>
    match (← Frontend.parseExportStreamS file).val with
    | .ok r => IO.println s!"{r.decls.size} records"; return 0
    | .error (e, l) => IO.eprintln s!"stream: {e} at line {l}"; return 3
  | ["--time", jobs, sp, m] =>
    -- the olean read's stages, timed one by one
    let roots := #[(m.splitOn ".").foldl Name.str Name.anonymous]
    let sp := (sp.splitOn ":").map System.FilePath.mk
    let t00 ← IO.monoMsNow
    let .ok order ← Frontend.Olean.closureOrder Frontend.Olean.decodeModuleFast sp roots | IO.eprintln "closure failed"; return 3
    let t0 ← IO.monoMsNow
    IO.println s!"closure {t0 - t00} ms ({order.size} modules)"
    let .ok ls ← Frontend.Olean.loadClosure Frontend.Olean.decodeModuleFast sp roots jobs.toNat! | IO.eprintln "load failed"; return 3
    let t1 ← IO.monoMsNow
    let .ok mg := Frontend.Olean.mergeAll ls | IO.eprintln "merge failed"; return 3
    let t2 ← IO.monoMsNow
    let em := Frontend.Olean.emitAll mg
    IO.println s!"{em.out.size} records"
    let t3 ← IO.monoMsNow
    let .ok ds := Frontend.Olean.declsOf em | IO.eprintln "build failed"; return 3
    IO.println s!"{ds.size} declarations"
    let t4 ← IO.monoMsNow
    IO.println s!"load {t1 - t0} ms ({ls.size} modules), merge {t2 - t1} ms, emit {t3 - t2} ms, build {t4 - t3} ms"
    return 0
  | file :: sp :: mods@(_ :: _) =>
    let t0 ← IO.monoMsNow
    let js ← match (← Frontend.parseExportStreamS file).val with
      | .ok r => pure r.decls
      | .error (e, l) => IO.eprintln s!"stream: {e} at line {l}"; return 3
    let t1 ← IO.monoMsNow
    let roots := mods.toArray.map fun m => (m.splitOn ".").foldl Name.str Name.anonymous
    let os ← match ← Frontend.Olean.readOleans Frontend.Olean.decodeModuleFast ((sp.splitOn ":").map System.FilePath.mk) roots 8 with
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
    for (k, _) in om do
      unless jm.contains k do
        bad := bad + 1
        if shown < 40 then IO.println s!"only in the oleans: {k}"; shown := shown + 1
    IO.println s!"{jm.size} stream keys, {om.size} olean keys, {bad} differences"
    return if bad == 0 then 0 else 1
  | _ =>
    IO.eprintln "usage: olean-compare EXPORT.ndjson SEARCHPATH MODULE..."
    return 3
