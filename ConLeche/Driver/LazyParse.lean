module

public import ConLeche.Driver.ParParse
public import ConLeche.Verify.Frontend.Lazy
public import ConLeche.Verify.Frontend.Chunks

/-!
# The lazy parse driver (task #329)

The parse at `--jobs` above one.  Four passes over the stream:

1. **Read and scan.**  The stream is read forward in chunks of whole
   lines (each read cut at its last newline), and every chunk is
   scanned flat on a worker (`scanFlat`).  The chunks' bytes are dropped
   as soon as they are scanned (a chunk whose scan did not end at its
   end keeps them: only the serial parse can say what such a chunk is);
   the flat scans stay, all of them, until the parse is done.
2. **The sweep** (`sweepChunk`, `ConLeche/Frontend/Lazy.lean`): backward
   over every line, marking the expression lines install needs.
3. **The windows**, as in the rounds parse (`ConLeche/Driver/ParParse.lean`):
   a window's chunks are built in rounds on the workers, but an
   unmarked expression line is bound to the placeholder `lazyExpr`, not
   built; then every chunk is CHECKED line by line (`checkFlatL`), which
   also keeps its lazy lines (the store).  A chunk passing the check is
   one more step of the serial parse (`LGOK.chunk`,
   `ConLeche/Verify/Frontend/Lazy.lean`).
4. **The theorem values**, built from the store on the workers
   (`buildVal`), each one the serial parse's entry (`buildVal_sound`).

Nothing the sweep or the rounds compute is believed.  On any anomaly —
a chunk that does not qualify, rounds that do not finish, a chunk that
fails its check, a value that does not build — the stream is parsed
serially from its start, over the flat scans still held
(`serialL`): the serial verdict, at the serial line.
-/

@[expose] public section

namespace ConLeche.Driver.LazyParse

open ConLeche ConLeche.Frontend ConLeche.Driver.ParParse

/-! ## Scanned chunks -/

/-- A chunk's flat scan, its size, and its bytes when its scan did not
end at its end (or it is the last): it is the scan of SOME bytes of
that size. -/
def LScanOK (x : FlatChunk × Nat × Option ByteArray) : Prop :=
  ∃ b : ByteArray, b.size = x.2.1 ∧ x.1.Encodes (scanChunk b) ∧
    (match x.2.2 with
     | some b' => b' = b
     | none => ∃ i, x.1.stop = .tail i ∧ i.toNat = b.size)

abbrev LScanned := { x : FlatChunk × Nat × Option ByteArray // LScanOK x }

instance : Inhabited LScanned :=
  ⟨⟨(scanFlat 0 .empty, 0, some .empty), .empty, rfl, scanFlat_encodes _ _, rfl⟩⟩

/-- Did the scan end at the chunk's end? -/
@[inline] def scanFull (fc : FlatChunk) (sz : Nat) : Bool :=
  match fc.stop with
  | .tail i => i.toNat == sz
  | _ => false

theorem scanFull_spec {fc : FlatChunk} {sz : Nat} (h : scanFull fc sz = true) :
    ∃ i, fc.stop = .tail i ∧ i.toNat = sz := by
  simp only [scanFull] at h
  split at h
  · rename_i i hi; exact ⟨i, hi, by simpa using h⟩
  · simp at h

/-- A chunk scanned: its bytes kept when asked to (`keep`) or when its
scan did not end at its end. -/
def scanChunkL (blk : ByteArray) (keep : Bool) : LScanned :=
  let fc := scanFlat (blk.size / 2) blk
  if h : keep = false ∧ scanFull fc blk.size = true then
    ⟨(fc, blk.size, none), blk, rfl, scanFlat_encodes _ _, scanFull_spec h.2⟩
  else ⟨(fc, blk.size, some blk), blk, rfl, scanFlat_encodes _ _, rfl⟩

/-- The scan job: the chunk `pending ++ buf0[0, k)`, put together and
scanned on the worker. -/
def scanJobL (pending buf0 : ByteArray) (k : Nat) (keep : Bool) : IO LScanned :=
  IO.lazyPure fun _ =>
    scanChunkL (if pending.isEmpty then buf0.extract 0 k else pending ++ buf0.extract 0 k) keep

/-- Read the whole stream, each chunk's scan a job; the last chunk keeps
its bytes. -/
partial def readAll (pl : Pool) (h : IO.FS.Handle) (csz : USize)
    (acc : Array (IO.Promise LScanned)) (pending : ByteArray) :
    IO (Array (IO.Promise LScanned)) := do
  let buf0 ← h.read csz
  if buf0.isEmpty then
    if pending.isEmpty then return acc
    else return acc.push (← pl.run .lo (scanJobL pending .empty 0 true))
  else
    match lastNewlineBelow buf0 buf0.size with
    | none => readAll pl h csz acc (pending ++ buf0)
    | some k =>
      let p ← pl.run .lo (scanJobL pending buf0 (k + 1) false)
      readAll pl h csz (acc.push p) (buf0.extract (k + 1) buf0.size)

/-! ## The fallback: the serial parse from the stream's start -/

/-- The serial parse over the scanned chunks, from a reached state.
(A chunk without its bytes after a carried tail cannot happen — only
the last chunk can leave a tail — and is answered by reading the file
again.) -/
def serialL (path : System.FilePath) (inflight : Nat) (st : StateD) (carry : ByteArray)
    (lineNo total : Nat) (hr : Reached st carry lineNo total) :
    List LScanned → IO ParseOutcome
  | [] => return ⟨chunkFinish st carry lineNo, hr.finish⟩
  | x :: xs =>
    match hb : x.val.2.2 with
    | some b =>
      have hx : x.val.1.Encodes (scanChunk b) := by
        obtain ⟨b', -, he, hm⟩ := x.property
        rw [hb] at hm; subst hm; exact he
      match hs : chunkStepF st carry lineNo total b x.val.1 with
      | .error e =>
        return ⟨.error e, hr.error (c := b) (by
          rw [← chunkStepF_of_encodes _ _ _ _ _ _ hx]; exact hs)⟩
      | .ok (st', carry', lineNo', total') =>
        serialL path inflight st' carry' lineNo' total' (hr.step (c := b) (by
          rw [← chunkStepF_of_encodes _ _ _ _ _ _ hx]; exact hs)) xs
    | none =>
      if hc : carry.isEmpty then
        have key : ∃ b : ByteArray, chunkStepNB st lineNo total x.val.2.1 x.val.1 =
            chunkStep st carry lineNo total b := by
          obtain ⟨b, hsz, he, hm⟩ := x.property
          rw [hb] at hm
          obtain ⟨i, hi, hi'⟩ := hm
          refine ⟨b, ?_⟩
          rw [eq_empty_of_isEmpty hc, ← hsz]
          exact chunkStepNB_eq he hi hi'
        match hs : chunkStepNB st lineNo total x.val.2.1 x.val.1 with
        | .error e =>
          return ⟨.error e, by
            obtain ⟨b, hbe⟩ := key
            exact hr.error (c := b) (by rw [← hbe]; exact hs)⟩
        | .ok (st', carry', lineNo', total') =>
          serialL path inflight st' carry' lineNo' total' (by
            obtain ⟨b, hbe⟩ := key
            exact hr.step (c := b) (by rw [← hbe]; exact hs)) xs
      else
        Frontend.parseExportStreamP path inflight

/-! ## A window -/

/-- A window's tables, untrusted: `computeW` of the rounds parse with
the sweep's marks (`round0`'s bitmap): an unmarked expression line is
bound, not built. -/
def computeWL (pl : Pool) (cfg : Cfg) (mk : ByteArray) (P : Prior) (c0 : Ctr) (total : Nat)
    (xs : Array LScanned) :
    IO (Except String (Win × Array (Array Name) × Array (Array Level) × Array (Array Expr))) := do
  let (fits, _) := xs.foldl (fun (ok, t) x => (ok && chunkFitsN x.val.2.1 x.val.1 t,
    t + x.val.2.1)) (true, total)
  if !fits then return .error "a chunk does not qualify"
  let mut ps : Array (IO.Promise R0) := #[]
  for i in [0:xs.size] do
    let fc := (xs.getD i default).val.1
    ps := ps.push (← pl.run .hi (do
      let o ← IO.lazyPure fun _ => round0 P mk c0 i fc
      markEach cfg.noMark o.dn; markEach cfg.noMark o.dl; markEach cfg.noMark o.de
      return o))
  let os ← ps.mapM await
  let W := Win.ofRound0 c0 (xs.map (·.val.1.data)) os
  if !after0 W os then
    return .error s!"round 0: {(os.toList.findIdx? (·.bad)).map fun c => s!"anomaly in chunk {c}"}"
  let some W ← roundsIO pl cfg.noMark P W (os.map (·.pend)) (os.map (·.npend)) 0
    | return .error "the later rounds"
  let cE := W.cEnd
  let nn ← pagesIO pl P.n W.n c0.n cE.n
  let nl ← pagesIO pl P.l W.l c0.l cE.l
  let ne ← pagesIO pl P.e W.e c0.e cE.e
  return .ok (W, nn, nl, ne)

/-- A chunk's lazy check, with the evidence that it is `checkFlatL` of
the chunk at the given counters. -/
structure CheckResL (P : Prior) (nd : ByteArray) where
  x : LScanned
  s : Ctr
  r : Option (Ctr × LAcc)
  h : r = checkFlatL P nd x.val.1 s

/-- The lazy checks of a window, on the workers. -/
def startChecksL (pl : Pool) (cfg : Cfg) (P : Prior) (nd : ByteArray) (W : Win)
    (xs : Array LScanned) : IO (Array (IO.Promise (CheckResL P nd))) := do
  let mut cps : Array (IO.Promise (CheckResL P nd)) := #[]
  for i in [0:xs.size] do
    let x := xs.getD i default
    let s := W.start i
    have : Nonempty (CheckResL P nd) := ⟨⟨x, s, _, rfl⟩⟩
    cps := cps.push (← pl.run .mid (do
      let r ← IO.lazyPure fun _ =>
        (⟨checkFlatL P nd x.val.1 s, rfl⟩ : { r // r = checkFlatL P nd x.val.1 s })
      if let some (_, a) := r.val then markEach cfg.noMark a.ds
      return ⟨x, s, r.val, r.property⟩))
  return cps

/-- **The checked chunks, folded**: each chunk whose check ran at the
counters the chunks before reached and passed is one more serial step
(`LGOK.chunk`); `none` at the first that is not. -/
def foldChecksL (P : Prior) (nd : ByteArray) : List (CheckResL P nd) → (g : LGSt) → LGOK g →
    g.P = P →
    Except String { g : LGSt // LGOK g }
  | [], g, hg, _ => .ok ⟨g, hg⟩
  | r :: rest, g, hg, hP =>
    if hs : r.s.beq g.c then
      match hr : r.r with
      | some (c', a) =>
        if hf : chunkFitsN r.x.val.2.1 r.x.val.1 g.total then
          foldChecksL P nd rest
            { g with c := c', ds := g.ds ++ a.ds, lineNo := g.lineNo + r.x.val.1.count,
                     total := g.total + r.x.val.2.1, S := g.S.push ⟨a.cd, a.spId, a.spOff⟩ }
            (by
              obtain ⟨b, hsz, he, -⟩ := r.x.property
              rw [← hsz] at hf ⊢
              exact LGOK.chunk hg he hf (by rw [hP, ← Ctr.beq_iff.mp hs, ← r.h, hr]))
            hP
        else .error s!"a chunk does not fit, at line {g.lineNo}"
      | none => .error s!"a chunk fails its check, at line {g.lineNo}"
    else .error s!"a chunk's counters, at line {g.lineNo}"

/-- A window whose tables have joined the finished ones and whose
checks are running. -/
structure PendL where
  g : LGSt
  hg : LGOK g
  nd : ByteArray
  cps : Array (IO.Promise (CheckResL g.P nd))
  cEnd : Ctr
  tEnd : Nat

/-- Where the parse is between windows. -/
inductive DoneL where
  | ready (g : LGSt) (hg : LGOK g)
  | pend (p : PendL)

/-- A window's checks, waited for and folded. -/
def foldPendL (p : PendL) : IO (Except String { g : LGSt // LGOK g }) := do
  have : Nonempty (CheckResL p.g.P p.nd) := ⟨⟨default, default, _, rfl⟩⟩
  let cs ← p.cps.mapM await
  return foldChecksL p.g.P p.nd cs.toList p.g p.hg rfl

/-- **The windows**, from chunk `i`: a window's tables are computed
while the window before it is being checked.  `none`: fall back. -/
partial def winLoop (pl : Pool) (cfg : Cfg) (mk nd : ByteArray) (xs : Array LScanned) (i : Nat)
    (d : DoneL) : IO (Except String { g : LGSt // LGOK g }) := do
  let win := xs.extract i (i + cfg.m)
  let comp ← if win.isEmpty then pure (.error "") else
    match d with
    | .ready g _ => computeWL pl cfg mk g.P g.c g.total win
    | .pend p => computeWL pl cfg mk p.g.P p.cEnd p.tEnd win
  let r ← match d with
    | .ready g hg => pure (.ok ⟨g, hg⟩)
    | .pend p => foldPendL p
  match r with
  | .error e => return .error e
  | .ok ⟨g, hg⟩ =>
    if win.isEmpty then return .ok ⟨g, hg⟩
    match comp with
    | .error e => return .error s!"window at chunk {i}: {e}"
    | .ok (W, nn, nl, ne) =>
      if hk : g.P.keeps g.c nn nl ne then
        let P' := g.P.setFrom g.c nn nl ne
        let g1 : LGSt := { g with P := P' }
        let cps ← startChecksL pl cfg P' nd W win
        let tEnd := win.foldl (fun t x => t + x.val.2.1) g.total
        winLoop pl cfg mk nd xs (i + cfg.m) (.pend ⟨g1, LGOK.keep hg hk, nd, cps, W.cEnd, tEnd⟩)
      else return .error s!"window at chunk {i}: the tables do not keep"

/-! ## The theorem values -/

/-- The records with every theorem value built, on the workers (slices
of the record array), with the evidence that each is the run-time
record filled (`FillInv`). -/
def fillAll (pl : Pool) (jobs : Nat) (S : LStore) (ds : Array Declaration) :
    IO (Option { e : Array Declaration // e.size = ds.size ∧ FillInv S ds 0 e }) := do
  let n := ds.size
  let parts := max 1 (4 * jobs)
  let step := max 1 ((n + parts - 1) / parts)
  let mut ps : Array (Σ' (lo hi : Nat), IO.Promise
      { o : Option (Array Declaration) // o = fillRange S ds lo hi #[] }) := #[]
  let mut l0 := 0
  while l0 < n do
    let a := l0
    let b := min n (a + step)
    have : Nonempty { o : Option (Array Declaration) // o = fillRange S ds a b #[] } :=
      ⟨⟨_, rfl⟩⟩
    let p ← pl.run .hi (IO.lazyPure fun _ =>
      (⟨fillRange S ds a b #[], rfl⟩ : { o // o = fillRange S ds a b #[] }))
    ps := ps.push ⟨a, b, p⟩
    l0 := b
  let mut acc : { e : Array Declaration // FillInv S ds 0 e } := ⟨#[], fun k h => absurd h (by simp)⟩
  for ⟨lo, hi, p⟩ in ps do
    have : Nonempty { o : Option (Array Declaration) // o = fillRange S ds lo hi #[] } :=
      ⟨⟨_, rfl⟩⟩
    let r ← await p
    match hr : r.val with
    | none => return none
    | some a =>
      if hlo : acc.val.size = lo then
        have hspec := fillRange_spec S ds lo hi (hi - lo) lo #[] a (by omega) (by simp)
          (Nat.le_refl _) (fun k h => absurd h (by simp)) (by rw [← r.property, hr])
        acc := ⟨acc.val ++ a, FillInv.append acc.property (hlo ▸ hspec.2)⟩
      else return none
  if h : acc.val.size = ds.size then return some ⟨acc.val, h, acc.property⟩
  else return none

/-! ## The stream -/

/-- What the tests read off a run: the fallbacks, and whether the marks
left anything lazy. -/
structure LInfo where
  fallbacks : Nat
  why : String := ""
  lazyLines : Nat
  /-- phase times (ms): read and scan, line starts, sweep, windows -/
  times : Array Nat := #[]

/-- The lazy parse's result: the run-time records (a theorem's value is
the placeholder `ph`) and the store its values are built from. -/
structure LazyRes where
  ds : Array Declaration
  S : LStore

/-- **What the lazy parse promises**: the serial parse of some chunks
succeeds, its final state is related to the store's tables and lines,
and its records to the run-time ones. -/
def LazyGhost (r : LazyRes) : Prop :=
  ∃ cs stF, parseChunks cs = .ok ⟨stF.decls⟩ ∧ SHolds stF r.S ∧
    StoreOK stF r.S.chunks ∧ Pw (DRel stF) r.ds.toList stF.decls.toList

/-- A parse's outcome: the serial parse's (a fallback, or `--jobs=1`),
or the lazy parse's records with their store. -/
inductive ParseOut where
  | eager (o : ParseOutcome)
  | lazy (r : LazyRes) (h : LazyGhost r)

/-- The lazy parse's records with every theorem value built (on `jobs`
workers): the serial parse's outcome. `none` if a value does not
build. -/
def toEager (jobs : Nat) (r : LazyRes) (h : LazyGhost r) : IO (Option ParseOutcome) := do
  let pl ← Pool.start jobs
  let res ← fillAll pl jobs r.S r.ds
  pl.shutdown
  match res with
  | none => return none
  | some ⟨e, hsz, hinv⟩ =>
    return some ⟨.ok ⟨e⟩, by
      obtain ⟨cs, stF, hcs, hh, hs, hd⟩ := h
      refine ⟨cs, ?_⟩
      rw [hcs]
      have := fill_eq hh hs hd hsz hinv
      congr 2
      exact Array.toList_inj.mp this.symm⟩

/-- **The lazy parse of a file** on `jobs` workers, windows of `m`
chunks of about `csz` bytes. -/
def parseExportLazyInfo (path : System.FilePath) (jobs m : Nat) (csz : USize) (inflight : Nat)
    (noMark : Bool) : IO (ParseOut × LInfo) := do
  let h ← IO.FS.Handle.mk path .read
  let fb ← IO.mkRef 0
  let pl ← Pool.start jobs
  let cfg : Cfg := ⟨max 1 m, csz, inflight, noMark, 0, fb⟩
  let t0 ← IO.monoMsNow
  -- 1. read and scan
  let ps ← readAll pl h csz #[] .empty
  let xs ← ps.mapM await
  let t1 ← IO.monoMsNow
  -- 2. the sweep: line starts on the workers, then backward on this thread
  let lps ← xs.mapM fun x => pl.run .hi (IO.lazyPure fun _ => lineStarts x.val.1)
  let ls ← lps.mapM await
  let t2 ← IO.monoMsNow
  let maxId := ls.foldl (fun a l => max a l.2) 0
  let nLines := xs.foldl (fun a x => a + x.val.1.count) 0
  let marks ← IO.lazyPure fun _ =>
    if maxId < 16 * nLines + 67108864 then
      let z := zeroBytes (maxId / 8 + 1)
      (List.range xs.size).foldr (fun c (m : SwMarks) =>
        let x := xs.getD c default
        sweepChunk x.val.1.data (ls.getD c default).1 x.val.1.count m) ⟨z, z⟩
    else ⟨.empty, .empty⟩
  let t3 ← IO.monoMsNow
  -- 3. the windows
  match ← winLoop pl cfg marks.mkd marks.nd xs 0 (.ready LGSt.init LGOK.init) with
  | .error why =>
    pl.shutdown
    let r ← serialL path inflight .init .empty 0 0 Reached.init xs.toList
    return (.eager r, ⟨1, why, 0, #[]⟩)
  | .ok ⟨g, hg⟩ =>
    pl.shutdown
    let t4 ← IO.monoMsNow
    -- the retained table, validated; the finished expression pages
    -- are dropped with `g.P`
    let rt := RTab.build marks.mkd marks.nd g.P g.c.e
    if hrt : rtValid rt g.P g.c.e then
      let S := LStore.ofChunks g.S g.P g.c rt
      let nLazy := S.chunks.foldl (fun a C => a + C.spId.size) 0
      let r : LazyRes := ⟨g.ds, S⟩
      let hr : LazyGhost r := by
        obtain ⟨cs, stF, hcs, hh, hd, hs⟩ := LGOK.finish hg
        exact ⟨cs, stF, hcs, SHolds.ofChunks hh g.S hrt, hs.ofChunks g.P g.c rt, hd⟩
      let t5 ← IO.monoMsNow
      -- without the sweep's marks (a stream with huge gaps) nothing is
      -- retained: every value is built now
      if marks.mkd.size == 0 then
        match ← toEager jobs r hr with
        | some o => return (.eager o, ⟨0, "no marks", nLazy, #[t1 - t0, t2 - t1, t3 - t2, t4 - t3, t5 - t4]⟩)
        | none =>
          let o ← serialL path inflight .init .empty 0 0 Reached.init xs.toList
          return (.eager o, ⟨1, "a value did not build", 0, #[]⟩)
      return (.lazy r hr, ⟨0, "", nLazy, #[t1 - t0, t2 - t1, t3 - t2, t4 - t3, t5 - t4]⟩)
    else
      let o ← serialL path inflight .init .empty 0 0 Reached.init xs.toList
      return (.eager o, ⟨1, "the retained table", 0, #[]⟩)

/-- **The lazy parse of a file**; with `verbose`, its phase times on
stderr. -/
def parseExportLazy (path : System.FilePath) (jobs m : Nat) (csz : USize) (inflight : Nat)
    (noMark verbose : Bool) : IO ParseOut := do
  let (r, info) ← parseExportLazyInfo path jobs m csz inflight noMark
  if verbose then
    IO.eprintln s!"con-leche: lazy parse: {info.lazyLines} sparse entries, {info.fallbacks} \
      fallbacks {info.why}, phases {info.times} ms"
  return r

end ConLeche.Driver.LazyParse
