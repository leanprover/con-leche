import ConLeche.Frontend.ExportWrite

/-!
# The in-process modeller's debug dump (task #200)

`CON_LECHE_INMODEL_DUMP=OUT` writes a copy of the raw input with the records
the in-process modeller generated for each block spliced in ahead of
that block's `inductive` record — a stream you can diff or re-check,
and the generator's gate (`tests/inmodel.sh` re-checks the dump: every
in-process block must then route `modeled`, since the stream now
carries its model).  Not on the checking path; the splice is keyed by
the block's ordinal among the input's `inductive` records, and the
spliced records use table indices above the input's maximum.
-/

namespace ConLeche.Frontend

open ConLeche.Cached (DeclC)

/-- The number after a fixed key in a record line (`"ie":N`,
`{"in":N`, …), `0` when absent. -/
private def numAfter (line key : String) : Nat :=
  match line.splitOn key with
  | _ :: rest :: _ => (rest.takeWhile Char.isDigit).toNat?.getD 0
  | _ => 0

/-- The largest name/level/expression index the input uses. -/
private partial def maxIndex (file : String) : IO Nat := do
  let h ← IO.FS.Handle.mk file .read
  let rec loop (m : Nat) : IO Nat := do
    let line ← h.getLine
    if line.isEmpty then return m
    let m := if line.startsWith "{\"in\":" then max m (numAfter line "{\"in\":")
      else if line.startsWith "{\"il\":" then max m (numAfter line "{\"il\":")
      else if line.startsWith "{\"ie\":" || (line.startsWith "{\"" && (line.splitOn "\"ie\":").length > 1)
        then max m (numAfter line "\"ie\":")
      else m
    loop m
  loop 0

/-- Write the spliced stream. -/
partial def dumpInModel (file out : String) (gen : Array (Nat × Array DeclC)) : IO Unit := do
  let base ← maxIndex file
  let h ← IO.FS.Handle.mk file .read
  let o ← IO.FS.Handle.mk out .write
  let rec loop (w : ExportWriter) (indSeen : Nat) : IO Unit := do
    let line ← h.getLine
    if line.isEmpty then return
    let mut w := w
    let mut indSeen := indSeen
    if line.startsWith "{\"inductive\"" then
      if let some (_, ds) := gen.find? (·.1 == indSeen) then
        w := { w with out := #[] }
        for d in ds do
          w := w.decl d
        for l in w.out do
          o.putStr l
          o.putStr "\n"
      indSeen := indSeen + 1
    o.putStr line
    loop w indSeen
  loop (ExportWriter.init (base + 1)) 0
  o.flush

end ConLeche.Frontend
