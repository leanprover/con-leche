module

public import ConLeche.Driver.OwnerParse
public import ConLeche.Cached.Installed
/- The tests below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Driver.OwnerParse
meta import ConLeche.Cached.Installed

public section

/-!
# The rounds parse (task #329)

`OwnerParse.parseExportStreamO` applies a stream's chunks a window at a
time — one chunk per owner thread — in rounds, and falls back to the
serial parse on anything unusual.  Its result carries the proof that `parseChunks`
returns it; what is pinned here is the IO around that proof and the
fallback's reach: at small chunk sizes (a chunk of one to a few lines,
so that a fixture takes many windows) and one, two, three and five
owners, every fixture's result is the wholesale parse's, verdict, line
number and records alike, and the fixtures a stream in increasing
order makes are parsed without falling back.
-/

namespace ConLecheTests

open ConLeche ConLeche.Frontend

/-- A parse result, printed: the verdict, the error's line, the records. -/
def roundsSummary : Except (CheckError × Nat) ParseResultD → String
  | .ok r => s!"ok {r.decls.toList.map ConLeche.Cached.declCLabel}"
  | .error (.internal m, n) => s!"internal {n}: {m}"
  | .error (.invalid m, n) => s!"invalid {n}: {m}"
  | .error (.notImplemented m, n) => s!"declined {n}: {m}"

/-- Every chunk size and owner count agrees with `parseBytes` of the
whole file; `rounds` says whether no window may fall back (`some true`),
some window must (`some false`), or either.  At 64-byte chunks every
fixture takes several windows. -/
def roundsAgrees (path : System.FilePath) (rounds : Option Bool) : IO Unit := do
  let b ← IO.FS.readBinFile path
  let want := roundsSummary (parseBytes b)
  for csz in [64, 1000, 65536] do
    for jobs in [1, 2, 3, 5] do
      let (r, fb, wins, _) ← ConLeche.Driver.OwnerParse.parseExportStreamOInfo path jobs
        csz.toUSize false
      let got := roundsSummary r.val
      unless got == want do
        throw <| IO.userError s!"{path} at chunk {csz}, {jobs} owners: \
          {got.take 200} ≠ {want.take 200}"
      match rounds with
      | some true =>
        unless fb == 0 do
          throw <| IO.userError s!"{path} at chunk {csz}, {jobs} owners: fell back"
        -- small chunks: many windows through the rounds
        unless csz != 64 || b.size < 64 * jobs * 3 || wins ≥ 3 do
          throw <| IO.userError s!"{path} at chunk {csz}, {jobs} owners: {wins} windows"
      | some false => unless fb == 1 do
          throw <| IO.userError s!"{path} at chunk {csz}, {jobs} owners: did not fall back"
      | none => pure ()

-- streams binding every index in order: through the rounds
#eval roundsAgrees "tests/e2e/and_rec_def.ndjson" (some true)
#eval roundsAgrees "tests/e2e/prop_proj.ndjson" (some true)
#eval roundsAgrees "tests/e2e/nat_ops.ndjson" (some true)
-- increasing indices with gaps: through the rounds
#eval roundsAgrees "tests/e2e/rounds_gappy_ids.ndjson" (some true)
-- gaps of 10^15 between consecutive indices: through the rounds, the
-- finished tables as small as their entries
#eval roundsAgrees "tests/e2e/rounds_huge_gaps.ndjson" (some true)
-- an index below its table's counter: the serial parse's
#eval roundsAgrees "tests/e2e/rounds_decreasing_id.ndjson" (some false)
-- a reference to an index bound further on, across chunks: the serial
-- parse's error, at its line
#eval roundsAgrees "tests/e2e/rounds_forward_ref.ndjson" (some false)
-- a malformed line in a late chunk; a stream malformed in the middle
#eval roundsAgrees "tests/e2e/rounds_error_late.ndjson" (some false)
#eval roundsAgrees "tests/e2e/malformed_midstream.ndjson" (some false)
-- a last line without a newline: the windows take every complete line,
-- the serial parse the last one (not a fallback)
#eval roundsAgrees "tests/e2e/final_line_no_newline.ndjson" (some true)
-- a record the parse turns into a verdict (an unsafe inductive): the
-- window's records are not all built, the serial parse gives the verdict
#eval roundsAgrees "tests/e2e/ind_unsafe.ndjson" (some false)

end ConLecheTests
