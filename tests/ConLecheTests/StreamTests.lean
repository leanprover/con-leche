module

public import ConLeche.Frontend.Stream
public import ConLeche.Cached.Installed
/- The tests below are EVALUATED, so the constants they name have to be
reachable from meta code too; a module needed at both levels is imported
twice. -/
meta import ConLeche.Frontend.Stream
meta import ConLeche.Cached.Installed

public section

/-!
# The serial streaming parse (task #329)

`parseExportStreamS` feeds every read to `chunkStep`, the incomplete
tail of a read carried into the next.  Its result carries the proof
that `parseChunks` returns it; what is pinned here is that the IO
around that proof — the reads, the carried tail — hands the fold the
bytes of the file and nothing else: on fixtures read at every chunk
size from one byte up, the result is the wholesale parse's, verdict,
line number and records alike.
-/

namespace ConLecheTests

open ConLeche ConLeche.Frontend

/-- A parse result, printed: the verdict, the error's line, the records. -/
def parseSummary : Except (CheckError × Nat) ParseResultD → String
  | .ok r => s!"ok {r.decls.toList.map ConLeche.Cached.declCLabel}"
  | .error (.internal m, n) => s!"internal {n}: {m}"
  | .error (.invalid m, n) => s!"invalid {n}: {m}"
  | .error (.notImplemented m, n) => s!"declined {n}: {m}"

/-- Every chunk size agrees with `parseBytes` of the whole file. -/
def serialAgrees (path : System.FilePath) : IO Unit := do
  let b ← IO.FS.readBinFile path
  let want := parseSummary (parseBytes b)
  for chunk in [1, 2, 7, 64, 1000, 4096] do
    let got := parseSummary (← parseExportStreamS path chunk.toUSize).val
    unless got == want do
      throw <| IO.userError s!"{path} at chunk {chunk}: {got.take 200} ≠ {want.take 200}"

-- an accepted stream, a stream malformed in the middle, and one whose
-- last line has no newline
#eval serialAgrees "tests/e2e/and_rec_def.ndjson"
#eval serialAgrees "tests/e2e/malformed_midstream.ndjson"
#eval serialAgrees "tests/e2e/final_line_no_newline.ndjson"
-- `natVal` literals past `2^32 - 1`, string literals, non-ASCII names,
-- inductive blocks
#eval serialAgrees "tests/e2e/nat_ops.ndjson"
#eval serialAgrees "tests/e2e/str_lit_declined.ndjson"
#eval serialAgrees "tests/e2e/complete_m3_proj_param.ndjson"
#eval serialAgrees "tests/e2e/and_rec_opaque.ndjson"

-- the pure halves: a chunk whose last line is cut, applied from its
-- scan, is `feedChunk`'s (a theorem, `applyScanned_scanChunk`; here
-- on a value, with the tail position)
#guard
  let b := "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}\n{\"in\":2,\"str\":{\"pre\":1,".toUTF8
  match applyScanned .init (scanChunk b) 0, feedChunk .init b 0 0 with
  | .ok (_, n, t), .ok (_, n', t') => n == 1 && n' == 1 && t == t' && t.toNat == 35
  | _, _ => false

end ConLecheTests
