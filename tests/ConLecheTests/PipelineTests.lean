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
-- the flat format's corners: `natVal` literals past `2^32 - 1` (the
-- escaped number), string literals, non-ASCII names, inductive blocks
#eval pipelineAgrees "tests/e2e/nat_ops.ndjson"
#eval pipelineAgrees "tests/e2e/str_lit_declined.ndjson"
#eval pipelineAgrees "tests/e2e/complete_m3_proj_param.ndjson"
#eval pipelineAgrees "tests/e2e/and_rec_opaque.ndjson"

-- the pure halves: a chunk whose last line is cut, applied from its
-- scan, is `feedChunk`'s (a theorem, `applyScanned_scanChunk`; here
-- on a value, with the tail position)
#guard
  let b := "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}\n{\"in\":2,\"str\":{\"pre\":1,".toUTF8
  match applyScanned .init (scanChunk b) 0, feedChunk .init b 0 0 with
  | .ok (_, n, t), .ok (_, n', t') => n == 1 && n' == 1 && t == t' && t.toNat == 35
  | _, _ => false

/-! ## The flat format (task #329, FLATSCAN)

`Flat.rdLine` and `Flat.withLineU_spec` are the round trip; here it is
on values: every line kind, numbers on both sides of the escape, a
non-ASCII string, read back by the specification's reader and by the
fast one, and re-encoded. -/

def flatSamples : List LineRec :=
  let cv : CVRec := ⟨5, [1, 2], 7⟩
  [ .expr 1 (.app 2 3), .expr 4294967294 (.app 4294967295 (2 ^ 70)),
    .expr 2 (.lam 1 0 .never), .expr 3 (.forallE 1 2 (.ifAllZero [1, 2, 3])),
    .name 1 (.str 0 "αβ.x\"y"), .name 2 (.num 1 (2 ^ 64)),
    .expr 5 (.const 3 [1, 2]), .expr 6 (.letE 1 2 3), .expr 7 (.bvar 0),
    .expr 8 (.sort 1), .expr 9 (.proj 1 2 3), .expr 10 (.natVal (10 ^ 30)),
    .expr 11 (.strVal ""), .level 1 (.succ 0), .level 2 (.max 1 0),
    .level 3 (.imax 1 2), .level 4 (.param 1),
    .decl (.ax cv true), .decl (.defn cv 3 (.regular 4) "safe"), .decl (.thm cv 3),
    .decl (.opaq cv 3 false), .decl (.quot cv "type"),
    .decl (.ind [⟨cv, [8, 9], true, false, false, 1, 0, 2⟩]
      [⟨cv, false, 2, 1, some 0, none⟩, ⟨cv, true, 0, 1, none, some 5⟩]
      [⟨cv, false, true, 1, 2, 1, 2, [⟨8, 0, 3⟩, ⟨9, 2, 4⟩]⟩]),
    .header, .blank ]

/-- Every sample, written into one buffer, read back in order by both
readers: the bytes re-encoded and the positions advanced to the end. -/
def flatRoundTrip : Bool :=
  let d := flatSamples.foldl Flat.wLine .empty
  let rec go (p : Nat) (q : USize) : List LineRec → Bool
    | [] => p == d.size && q.toNat == d.size
    | r :: rs =>
      let (r1, p') := Flat.rLine d p
      let (e2, q') := Flat.withLineU d q fun r q => (Flat.encLine r, q)
      Flat.encLine r1 == Flat.encLine r && e2 == Flat.encLine r && go p' q' rs
  go 0 0 flatSamples

#guard flatRoundTrip

-- the flat scan of a chunk, applied, is `applyScanned` of its record
-- scan (a theorem, `applyFlat_eq`; here on a value)
#guard
  let b := "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"a\"}}\n{\"in\":2,\"str\":{\"pre\":1,".toUTF8
  match applyFlat .init (scanFlat 0 b) 0, applyScanned .init (scanChunk b) 0 with
  | .ok (_, n, t), .ok (_, n', t') => n == 1 && n' == 1 && t == t' && (scanFlat 0 b).count == 1
  | _, _ => false

end ConLecheTests
