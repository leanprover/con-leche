module

public import ConLeche.Frontend.Stream
public import ConLeche.Frontend.Olean.Load

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

def toMap (ds : Array Declaration) : Std.HashMap Name Declaration × Nat :=
  ds.foldl (fun (m, dup) d =>
    let k := (d.names.head?).getD .anonymous
    if m.contains k then (m, dup + 1) else (m.insert k (normalize d), dup)) ({}, 0)

public def main (args : List String) : IO UInt32 := do
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
    let .ok order ← Frontend.Olean.closureOrder sp roots | IO.eprintln "closure failed"; return 3
    let t0 ← IO.monoMsNow
    IO.println s!"closure {t0 - t00} ms ({order.size} modules)"
    let .ok ls ← Frontend.Olean.loadClosure sp roots jobs.toNat! | IO.eprintln "load failed"; return 3
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
    let os ← match ← Frontend.Olean.readOleans ((sp.splitOn ":").map System.FilePath.mk) roots 8 with
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
        unless d == d' do
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
