module

public import ConLeche.Driver.OwnerParse
public import ConLeche.Verify.Frontend.StreamModel

/-!
# The stream parse, generic in the IO class (tasks #424, #450)

`parseStreamG` reads a lean4export stream through the checker's IO
class (`ConLeche/Frontend/CheckerIO.lean`): at one job by the serial
fold (`Frontend.parseFileS`, `foldChunks`), above one by the fold over
windows (`foldWindows`, chunks of whole lines, one per owner), each
window's rounds on the owner threads (`RoundsOps`,
`ConLeche/Driver/OwnerParse.lean`), started, called and stopped
through `CheckerIO.liftIO`.  Both folds are ordinary code over the
class's positional read (`CheckerIO.readRange`).

**The step over a window** (`winStep`).  Between windows the state is
the rounds parse's (`GSt`), or, once a window fell back, the serial
parse's.  The owners return a window's next state with the proof that
it advances the rounds parse's invariant over the window's chunks
(`WinAdv`: whatever chunks led here, those and the window's lead
there), or nothing — the window falls back: its chunks, and every chunk
after it, are applied by `chunkStep` from the state the windows before
reached (`GOK.reached`, the finished tables as a parse state).  The
bytes after the file's last newline (a final line without one) are
applied at the end (`winFin`).

**In the model** (`parseStreamG_model`): every outcome that is records
`r` — whatever the owners' `liftIO` calls answered, each answer
carrying its proof — means the file's bytes in the snapshot parse to
`r` as one chunk, `parseChunks [b] = .ok r`: the form the main
corollary `ConLeche.main_no_False` needs of the file's bytes.  The
reads of the folds are the model's (`readsFrom`, `winsOf`); that they
put together are the file is `ConLeche/Verify/Frontend/StreamModel.lean`.
-/

@[expose] public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend

/-- The windows' fold state: the rounds parse's, or the serial parse's
once a window fell back. -/
inductive WSt where
  | rounds (g : GSt)
  | serial (s : SerSt)

/-- Chunks applied by the serial parse's step, one after the other. -/
def serialApply : SerSt → List ByteArray → Except (CheckError × Nat) SerSt
  | s, [] => .ok s
  | (st, carry, lineNo, total), c :: cs =>
    match chunkStep st carry lineNo total c with
    | .error e => .error e
    | .ok s => serialApply s cs

/-- The state a window that falls back continues the serial parse from:
the finished tables as a parse state, nothing carried. -/
def fallSt (g : GSt) : SerSt := ((g.P.toState g.c g.ds).markLinear, .empty, g.lineNo, g.total)

/-- Chunks applied serially, as a step of the windows' fold. -/
@[inline] def serialWin (s : SerSt) (bs : Array ByteArray) :
    Except (Except (CheckError × Nat) ParseResultD) WSt :=
  match serialApply s bs.toList with
  | .error e => .error (.error e)
  | .ok s => .ok (.serial s)

/-- **The windows' step**: a window through the rounds parse's owners
(an `IO` action, `CheckerIO.liftIO`; its reply carries the proof that
it advances the invariant), or, once fallen back, by the serial
parse. -/
def winStep {μ : Type → Type} [CheckerIO μ] (R : OwnerParse.RoundsOps) :
    WSt → Array ByteArray → μ (Array ByteArray) →
    μ (Except (Except (CheckError × Nat) ParseResultD) WSt)
  | .serial s, bs, _ => pure (serialWin s bs)
  | .rounds g, bs, nxt => do
    let n ← nxt
    match ← CheckerIO.liftIO (R.window g bs (pure n)) with
    | some ⟨g', _⟩ => pure (.ok (.rounds g'))
    | none => pure (serialWin (fallSt g) bs)

/-- The serial parse's end, after the bytes after the last newline. -/
def serialEnd (s : SerSt) (tail : ByteArray) : Except (CheckError × Nat) ParseResultD :=
  if tail.isEmpty then serFin s
  else
    match serialApply s [tail] with
    | .error e => .error e
    | .ok s => serFin s

/-- **The windows' end**: the bytes after the file's last newline, if
any, by the serial parse; without them, the rounds parse's records. -/
def winFin : WSt → ByteArray → Except (CheckError × Nat) ParseResultD
  | .rounds g, tail => if tail.isEmpty then .ok ⟨g.ds⟩ else serialEnd (fallSt g) tail
  | .serial s, tail => serialEnd s tail

/-- **The rounds parse of a file**: the fold over its windows of `w`
chunks of about `csz` bytes, the owners stopped however it ends (an IO
error — a read that fails, a dropped promise — propagates instead of
leaving them blocked, which would keep the process from exiting). -/
def parseFileW {μ : Type → Type} [CheckerIO μ] (R : OwnerParse.RoundsOps) (path : System.FilePath)
    (csz : USize) (w : Nat) : μ (Except (CheckError × Nat) ParseResultD) := do
  let r ← tryCatchThe IO.Error
    (foldWindows path csz w (WSt.rounds .init) (winStep R) winFin)
    (fun e => do CheckerIO.liftIO R.stop; throwThe IO.Error e)
  CheckerIO.liftIO R.stop
  return r

/-- The rounds parse's chunk size: about a sixteenth of an owner's share
of the file, between 64 KiB and 4 MiB (1 MiB when the size is unknown). -/
def roundsChunk (size jobs : Nat) : Nat :=
  if size == 0 then 1048576 else max 65536 (min 4194304 (size / (16 * jobs)))

/-- **The stream parse** (task #424): at `--jobs=1` the serial one
(`parseFileS`, each 4 MiB read fed to `chunkStep`); above, the rounds
parse on `jobs` owner threads (`OwnerParse.startRounds`, through `liftIO`), a
window of one chunk per owner. -/
def parseStreamG {μ : Type → Type} [CheckerIO μ] (file : String) (jobs : Nat) (noMark : Bool) :
    μ (Except (CheckError × Nat) ParseResultD) := do
  if jobs ≤ 1 then
    parseFileS file
  else
    let size ← CheckerIO.fileSize file
    let R ← CheckerIO.liftIO do OwnerParse.startRounds (← OwnerParse.Cfg.new noMark) jobs
    parseFileW R file (roundsChunk size jobs).toUSize jobs

/-! ## In the model -/

/-- What the windows' fold has reached after the chunks `done`. -/
def WInv (done : List ByteArray) : WSt → Prop
  | .rounds g => GOK done g
  | .serial (st, carry, lineNo, total) => Reached done st carry lineNo total

theorem serialApply_reached (cs : List ByteArray) :
    ∀ {done : List ByteArray} {s s' : SerSt}, WInv done (.serial s) →
    serialApply s cs = .ok s' → WInv (done ++ cs) (.serial s') := by
  induction cs with
  | nil =>
    intro done s s' h hs
    simp only [serialApply, Except.ok.injEq] at hs
    subst hs; simpa using h
  | cons c cs ih =>
    intro done s s' h hs
    obtain ⟨st, carry, lineNo, total⟩ := s
    simp only [serialApply] at hs
    split at hs
    · cases hs
    · rename_i s'' hst
      obtain ⟨st'', carry'', lineNo'', total''⟩ := s''
      have := ih (done := done ++ [c]) (Reached.step h hst) hs
      simpa using this

theorem fallSt_inv {done : List ByteArray} {g : GSt} (h : GOK done g) :
    WInv done (.serial (fallSt g)) := by
  simp only [WInv, fallSt, StateD.markLinear_eq]
  exact h.reached

theorem serialWin_ok {done : List ByteArray} {s : SerSt} {bs : Array ByteArray} {s' : WSt}
    (h : WInv done (.serial s)) (hs : serialWin s bs = .ok s') :
    WInv (done ++ bs.toList) s' := by
  unfold serialWin at hs
  split at hs
  · cases hs
  · rename_i s'' hap
    cases hs
    exact serialApply_reached _ h hap

theorem serialWin_ne (s : SerSt) (bs : Array ByteArray) (r : ParseResultD) :
    serialWin s bs ≠ .error (.ok r) := by
  unfold serialWin
  split <;> simp

theorem serialEnd_ok {done : List ByteArray} {s : SerSt} {tail : ByteArray}
    {r : ParseResultD} (h : WInv done (.serial s)) (hs : serialEnd s tail = .ok r) :
    parseChunks (done ++ tailL tail) = .ok r := by
  unfold serialEnd at hs
  unfold tailL
  split at hs
  · rename_i he
    rw [ite_eq_left he, List.append_nil]
    obtain ⟨st, carry, lineNo, total⟩ := s
    rw [(show Reached done st carry lineNo total from h).finish]
    exact hs
  · rename_i he
    rw [ite_eq_right he]
    split at hs
    · cases hs
    · rename_i s' hap
      have h' := serialApply_reached _ h hap
      obtain ⟨st, carry, lineNo, total⟩ := s'
      rw [(show Reached (done ++ [tail]) st carry lineNo total from h').finish]
      exact hs

theorem winFin_ok {done : List ByteArray} {s : WSt} {tail : ByteArray} {r : ParseResultD}
    (h : WInv done s) (hs : winFin s tail = .ok r) : parseChunks (done ++ tailL tail) = .ok r := by
  cases s with
  | rounds g =>
    simp only [winFin] at hs
    split at hs
    · rename_i he
      simp only [Except.ok.injEq] at hs
      subst hs
      rw [tailL, ite_eq_left he, List.append_nil]
      exact GOK.finish h
    · exact serialEnd_ok (fallSt_inv h) hs
  | serial s => exact serialEnd_ok h hs

/-- **The windows' fold in the model**: an outcome that is records `r`,
from a state the chunks `done` reached, means `parseChunks` of those,
the windows' chunks and the bytes after the last newline returns `r`,
whatever the owners answered (every answer carries its proof). -/
theorem foldWins_winStep (R : OwnerParse.RoundsOps) (tail : ByteArray) (fs : FS)
    (ws : List (Array ByteArray)) :
    ∀ {done : List ByteArray} {s : WSt} {r : ParseResultD}, WInv done s →
    (ModelIO.foldWins (winStep R) winFin tail s ws) fs (.ok (.ok r)) →
    parseChunks (done ++ winChunks ws ++ tailL tail) = .ok r := by
  induction ws with
  | nil =>
    intro done s r h hr
    simp only [ModelIO.foldWins, ModelIO.pure_iff, Except.ok.injEq] at hr
    simpa [winChunks] using winFin_ok h hr.symm
  | cons w ws ih =>
    intro done s r h hr
    have key : ∀ {s' : WSt}, WInv (done ++ w.toList) s' →
        (ModelIO.foldWins (winStep R) winFin tail s' ws) fs (.ok (.ok r)) →
        parseChunks (done ++ winChunks (w :: ws) ++ tailL tail) = .ok r := by
      intro s' h' hr'
      have := ih h' hr'
      simpa [winChunks, List.append_assoc] using this
    simp only [ModelIO.foldWins, ModelIO.bind_ok] at hr
    obtain ⟨x, hx, hr⟩ := hr
    cases s with
    | serial s =>
      simp only [winStep, ModelIO.pure_iff, Except.ok.injEq] at hx
      subst hx
      rcases hsw : serialWin s w with y | s'
      · rw [hsw] at hr
        simp only [ModelIO.pure_iff, Except.ok.injEq] at hr
        subst hr; exact absurd hsw (serialWin_ne _ _ _)
      · rw [hsw] at hr
        exact key (serialWin_ok h hsw) hr
    | rounds g =>
      simp only [winStep, ModelIO.bind_ok] at hx
      obtain ⟨n, -, a, -, hx⟩ := hx
      rcases a with _ | ⟨g', hadv⟩
      · simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
        subst hx
        rcases hsw : serialWin (fallSt g) w with y | s'
        · rw [hsw] at hr
          simp only [ModelIO.pure_iff, Except.ok.injEq] at hr
          subst hr; exact absurd hsw (serialWin_ne _ _ _)
        · rw [hsw] at hr
          exact key (serialWin_ok (fallSt_inv h) hsw) hr
      · simp only [ModelIO.pure_iff, Except.ok.injEq] at hx
        subst hx
        exact key (s' := .rounds g') (hadv done h) hr

theorem chunkSize_pos : 0 < chunkSize.toNat := by
  unfold chunkSize
  cases USize.size_eq <;> simp_all [USize.toNat_mul]

theorem toNat_roundsChunk (size jobs : Nat) : 0 < (roundsChunk size jobs).toUSize.toNat := by
  have hlt : roundsChunk size jobs < USize.size := by
    have := USize.le_size
    unfold roundsChunk; split <;> omega
  have hpos : 0 < roundsChunk size jobs := by unfold roundsChunk; split <;> omega
  rw [Nat.toUSize, USize.toNat_ofNat_of_lt' hlt]
  exact hpos

/-- **The stream parse in the model** (tasks #424, #450): an outcome
that is records `r` on a snapshot `fs` means the file has bytes `b`
there and `parseChunks [b] = .ok r` — the file's own bytes parse, as one
chunk, to the records the driver goes on with, whatever the owner
threads (`liftIO`) answered. -/
theorem parseStreamG_model {file : String} {jobs : Nat} {noMark : Bool} {fs : FS}
    {r : ParseResultD}
    (h : (parseStreamG file jobs noMark : ModelIO _) fs (.ok (.ok r))) :
    ∃ b, fs.file file = some b ∧ parseChunks [b] = .ok r := by
  unfold parseStreamG at h
  split at h
  · -- the serial fold
    rw [parseFileS] at h
    obtain ⟨b, hb, hr⟩ := foldChunks_model h
    refine ⟨b, hb, ?_⟩
    rw [foldList_serStep] at hr
    exact parseChunks_single_of_concat (concatBytes_reads chunkSize_pos b) hr.symm
  · -- the windows' fold
    rename_i hj
    simp only [ModelIO.bind_ok] at h
    obtain ⟨size, -, R, -, h⟩ := h
    simp only [parseFileW, ModelIO.bind_ok, ModelIO.tryCatch_ok] at h
    obtain ⟨v, hv, -, -, hr⟩ := h
    simp only [ModelIO.pure_iff, Except.ok.injEq] at hr
    subst hr
    rcases hv with hf | ⟨e, -, he⟩
    · obtain ⟨b, hb, hf⟩ := foldWindows_model hf
      refine ⟨b, hb, ?_⟩
      have := foldWins_winStep R _ fs _ (done := []) (s := .rounds .init) GOK.init hf
      rw [List.nil_append] at this
      exact parseChunks_single_of_concat
        (concatBytes_windowsOf (toNat_roundsChunk size jobs) (by omega) b) this
    · simp only [ModelIO.throw_ok] at he
      -- (the handler stops the owners, then rethrows: no value)
      obtain ⟨_, _, he⟩ := he
      exact he.elim

end ConLeche.Driver
