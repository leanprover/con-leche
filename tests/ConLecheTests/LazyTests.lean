module

public import ConLeche.Driver.LazyParse
public import ConLeche.Cached.Installed
/- The tests below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Driver.LazyParse
meta import ConLeche.Cached.Installed

public section

/-!
# The lazy parse (task #329)

`LazyParse.parseExportLazy` scans every chunk, sweeps backward for the
expression lines install needs, builds those in windows of chunks, in
rounds, on worker threads, checks every chunk against the finished
tables, keeps the other lines for the theorem values' builds, and
falls back to the serial parse — from the state the chunks before the
failure reached, materialized — on anything unusual.  Its result
carries the proof that `parseChunks` returns the records it stands for;
what is pinned here is the IO around that proof and the fallback's
reach: at small chunk and window sizes (a chunk of one to a few lines,
a window of one to five chunks, two and three workers), every fixture's
result, its theorem values built (`toEager`), is the wholesale parse's,
verdict, line number and records alike, and the fixtures a stream in
increasing order makes are parsed without falling back.
-/

namespace ConLecheTests

open ConLeche ConLeche.Frontend ConLeche.Driver.LazyParse

/-- A parse result, printed: the verdict, the error's line, the records
with their values' sizes. -/
def lazySummary : Except (CheckError × Nat) ParseResultD → String
  | .ok r => s!"ok {r.decls.toList.map fun d => (ConLeche.Cached.declCLabel d, match d with
      | .thmDecl _ v => toString (hash v)
      | _ => "")}"
  | .error (.internal m, n) => s!"internal {n}: {m}"
  | .error (.invalid m, n) => s!"invalid {n}: {m}"
  | .error (.notImplemented m, n) => s!"declined {n}: {m}"

/-- Every chunk size, window size and worker count agrees with
`parseBytes` of the whole file; `lazy` says whether no window may fall
back (`some true`), some window must (`some false`), or either. -/
def lazyAgrees (path : System.FilePath) (lazy : Option Bool) : IO Unit := do
  let b ← IO.FS.readBinFile path
  let want := lazySummary (parseBytes b)
  for csz in [64, 1000, 65536] do
    for m in [1, 2, 5] do
      for jobs in [2, 3] do
        let (r, info) ← parseExportLazyInfo path jobs m csz.toUSize 2 false
        let r ← match r with
          | .eager o => pure o.val
          | .lazy r h => match ← toEager jobs r h with
            | some o => pure o.val
            | none => throw <| IO.userError s!"{path}: a value did not build"
        let got := lazySummary r
        unless got == want do
          throw <| IO.userError s!"{path} at chunk {csz}, window {m}, {jobs} workers: \
            {got.take 200} ≠ {want.take 200}"
        match lazy with
        | some true => unless info.fallbacks == 0 do
            throw <| IO.userError s!"{path} at chunk {csz}, window {m}: fell back ({info.why})"
        | some false => unless info.fallbacks == 1 do
            throw <| IO.userError s!"{path} at chunk {csz}, window {m}: did not fall back"
        | none => pure ()

-- streams binding every index in order: lazily
#eval lazyAgrees "tests/e2e/and_rec_def.ndjson" (some true)
#eval lazyAgrees "tests/e2e/prop_proj.ndjson" (some true)
#eval lazyAgrees "tests/e2e/nat_ops.ndjson" (some true)
#eval lazyAgrees "tests/e2e/natop_order.ndjson" (some true)
-- increasing indices with gaps: lazily
#eval lazyAgrees "tests/e2e/rounds_gappy_ids.ndjson" (some true)
-- an index below its table's counter: the serial parse's
#eval lazyAgrees "tests/e2e/rounds_decreasing_id.ndjson" (some false)
-- a reference to an index bound further on, across chunks: the serial
-- parse's error, at its line
#eval lazyAgrees "tests/e2e/rounds_forward_ref.ndjson" (some false)
#eval lazyAgrees "tests/e2e/lazy_forward_ref.ndjson" (some false)
-- a bad reference in a theorem-only line
#eval lazyAgrees "tests/e2e/lazy_bad_ref.ndjson" (some false)
-- a malformed line in a late chunk; a stream malformed in the middle;
-- a last line without a newline
#eval lazyAgrees "tests/e2e/rounds_error_late.ndjson" (some false)
#eval lazyAgrees "tests/e2e/lazy_error_late.ndjson" (some false)
#eval lazyAgrees "tests/e2e/malformed_midstream.ndjson" (some false)
#eval lazyAgrees "tests/e2e/final_line_no_newline.ndjson" (some false)
-- a record the parse turns into a verdict (an unsafe inductive): the
-- check does not pass it, the serial parse gives the verdict
#eval lazyAgrees "tests/e2e/ind_unsafe.ndjson" (some false)

end ConLecheTests
