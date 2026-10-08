module

public import ConLeche.Frontend.Pipeline
public import ConLeche.Cached.Installed
/- The tests below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Frontend.Pipeline
meta import ConLeche.Cached.Installed

public section

/-!
# The pipelined parse (task #329)

`parseExportHandleP` cuts every read at its last newline, scans the
chunks on worker tasks and applies them in order.  Its result carries
the proof that `parseChunks` returns it; what is pinned here is that
the IO around that proof — the cut, the carried leftover, the queue —
hands the fold the bytes of the file and nothing else: on fixtures
read at every chunk size from one byte up and at one to three chunks
in flight, the result is the wholesale parse's, verdict, line number
and records alike.
-/

namespace ConLecheTests

open ConLeche ConLeche.Frontend

/-- A parse result, printed: the verdict, the error's line, the records. -/
def parseSummary : Except (CheckError × Nat) ParseResultD → String
  | .ok r => s!"ok {r.decls.toList.map ConLeche.Cached.declCLabel}"
  | .error (.internal m, n) => s!"internal {n}: {m}"
  | .error (.invalid m, n) => s!"invalid {n}: {m}"
  | .error (.notImplemented m, n) => s!"declined {n}: {m}"

/-- Every chunk size and in-flight count agree with `parseBytes` of the
whole file. -/
def pipelineAgrees (path : System.FilePath) : IO Unit := do
  let b ← IO.FS.readBinFile path
  let want := parseSummary (parseBytes b)
  for chunk in [1, 2, 7, 64, 1000, 4096] do
    for inflight in [1, 2, 3] do
      let got := parseSummary (← parseExportStreamP path inflight chunk.toUSize).val
      unless got == want do
        throw <| IO.userError s!"{path} at chunk {chunk}, {inflight} in flight: \
          {got.take 200} ≠ {want.take 200}"

-- an accepted stream, a stream malformed in the middle, and one whose
-- last line has no newline
#eval pipelineAgrees "tests/e2e/and_rec_def.ndjson"
#eval pipelineAgrees "tests/e2e/malformed_midstream.ndjson"
#eval pipelineAgrees "tests/e2e/final_line_no_newline.ndjson"

-- the pure halves: a chunk whose last line is cut, applied from its
-- scan, is `feedChunk`'s (a theorem, `applyScanned_scanChunk`; here
-- on a value, with the tail position)
#guard
  let b := "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}\n{\"in\":2,\"str\":{\"pre\":1,".toUTF8
  match applyScanned .init (scanChunk b) 0, feedChunk .init b 0 0 with
  | .ok (_, n, t), .ok (_, n', t') => n == 1 && n' == 1 && t == t' && t.toNat == 35
  | _, _ => false

end ConLecheTests
