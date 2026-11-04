module

public import ConLeche.Frontend.CheckerIO

/-!
# The IO model's outcomes (task #450)

The checker's IO class (`CheckerIO`, `ConLeche/Frontend/CheckerIO.lean`)
has a model, `ModelIO α = FS → Except IO.Error α → Prop`: an action's
possible outcomes on a file system snapshot.  Here: that it is a lawful
monad, the equations the proofs peel `do` blocks with (an outcome that
is a value came from values all along: `bind_ok`, `tryCatch_ok`), the
determined operations, and the folds over a file's reads in the model.

* **The folds over a file's reads** (`foldReads`, `foldChunks`,
  `foldWindows`): a file's reads are `readsFrom` (`foldReads_model`),
  the serial fold is `foldList` over them (`foldChunks_model`), and the
  windows' fold is `ModelIO.foldWins` over `windowsOf`, the reads cut at
  their last newlines and grouped (`foldWindows_model`).
-/

public section

namespace ConLeche

theorem ModelIO.ext {α : Type} {x y : ModelIO α} (h : ∀ fs o, x fs o ↔ y fs o) : x = y :=
  funext fun fs => funext fun o => propext (h fs o)

@[simp] theorem ModelIO.pure_iff {α : Type} (a : α) (_fs : FS) (o : Except IO.Error α) :
    (pure a : ModelIO α) _fs o ↔ o = .ok a := Iff.rfl

/-- An outcome of a sequence that is a value: a value of the first
action, and that value's continuation. -/
@[simp] theorem ModelIO.bind_ok {α β : Type} (x : ModelIO α) (f : α → ModelIO β) (fs : FS) (v : β) :
    (x >>= f) fs (.ok v) ↔ ∃ a, x fs (.ok a) ∧ f a fs (.ok v) := by
  show ((∃ a, x fs (.ok a) ∧ f a fs (.ok v)) ∨ (∃ e, (Except.ok v : Except IO.Error β) = .error e ∧ x fs (.error e))) ↔ _
  constructor
  · rintro (h | ⟨e, he, _⟩)
    · exact h
    · cases he
  · exact Or.inl

/-- A caught action's outcome that is a value. -/
@[simp] theorem ModelIO.tryCatch_ok {α : Type} (x : ModelIO α) (h : IO.Error → ModelIO α) (fs : FS)
    (v : α) : (tryCatchThe IO.Error x h : ModelIO α) fs (.ok v) ↔
      x fs (.ok v) ∨ ∃ e, x fs (.error e) ∧ h e fs (.ok v) := by
  show ((∃ a, (Except.ok v : Except IO.Error α) = .ok a ∧ x fs (.ok a)) ∨
    (∃ e, x fs (.error e) ∧ h e fs (.ok v))) ↔ _
  constructor
  · rintro (⟨a, ha, hx⟩ | h)
    · cases ha; exact Or.inl hx
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨v, rfl, h⟩
    · exact Or.inr h

@[simp] theorem ModelIO.throw_ok {α : Type} (e : IO.Error) (fs : FS) (v : α) :
    (throwThe IO.Error e : ModelIO α) fs (.ok v) ↔ False := by
  show ((Except.ok v : Except IO.Error α) = .error e) ↔ False
  simp

/-- The escape, in the model: every outcome. -/
@[simp] theorem ModelIO.liftIO_iff {α : Type} (a : IO α) (fs : FS) (o : Except IO.Error α) :
    (CheckerIO.liftIO a : ModelIO α) fs o ↔ True := Iff.rfl

@[simp] theorem ModelIO.answer_ok {α : Type} (x : Option α) (v : α) :
    ModelIO.answer x (.ok v) ↔ x = some v := by
  cases x <;> simp [ModelIO.answer, eq_comm]

instance : LawfulMonad ModelIO := LawfulMonad.mk'
  (id_map := fun x => ModelIO.ext fun fs o => by
    show ((∃ a, x fs (.ok a) ∧ o = .ok a) ∨ (∃ e, o = .error e ∧ x fs (.error e))) ↔ x fs o
    cases o with
    | ok v => simp
    | error e => simp)
  (pure_bind := fun a f => ModelIO.ext fun fs o => by
    show ((∃ a', (Except.ok a' : Except IO.Error _) = .ok a ∧ f a' fs o) ∨
      (∃ e, o = .error e ∧ (Except.error e : Except IO.Error _) = .ok a)) ↔ f a fs o
    simp)
  (bind_assoc := fun x f g => ModelIO.ext fun fs o => by
    show ((∃ b, ((∃ a, x fs (.ok a) ∧ f a fs (.ok b)) ∨ (∃ e, (Except.ok b : Except IO.Error _) = .error e ∧ x fs (.error e))) ∧ g b fs o) ∨
        (∃ e, o = .error e ∧ ((∃ a, x fs (.ok a) ∧ f a fs (.error e)) ∨ (∃ e', (Except.error e : Except IO.Error _) = .error e' ∧ x fs (.error e'))))) ↔
      ((∃ a, x fs (.ok a) ∧ ((∃ b, f a fs (.ok b) ∧ g b fs o) ∨ (∃ e, o = .error e ∧ f a fs (.error e)))) ∨
        (∃ e, o = .error e ∧ x fs (.error e)))
    constructor
    · rintro (⟨b, (⟨a, ha, hb⟩ | ⟨e, he, _⟩), hg⟩ | ⟨e, rfl, (⟨a, ha, hf⟩ | ⟨e', he', hx⟩)⟩)
      · exact Or.inl ⟨a, ha, Or.inl ⟨b, hb, hg⟩⟩
      · cases he
      · exact Or.inl ⟨a, ha, Or.inr ⟨e, rfl, hf⟩⟩
      · cases he'; exact Or.inr ⟨e, rfl, hx⟩
    · rintro (⟨a, ha, (⟨b, hb, hg⟩ | ⟨e, rfl, hf⟩)⟩ | ⟨e, rfl, hx⟩)
      · exact Or.inl ⟨b, Or.inl ⟨a, ha, hb⟩, hg⟩
      · exact Or.inr ⟨e, rfl, Or.inl ⟨a, ha, hf⟩⟩
      · exact Or.inr ⟨e, rfl, Or.inr ⟨e, rfl, hx⟩⟩)

/-- An outcome of a mapped action that is a value. -/
@[simp] theorem ModelIO.map_ok {α β : Type} (g : α → β) (x : ModelIO α) (fs : FS) (v : β) :
    (g <$> x) fs (.ok v) ↔ ∃ a, x fs (.ok a) ∧ g a = v := by
  rw [map_eq_pure_bind, ModelIO.bind_ok]
  simp [eq_comm]

/-- Two continuations that agree on a snapshot give the same outcomes there. -/
theorem ModelIO.bind_congr_at {α β : Type} (x : ModelIO α) {f g : α → ModelIO β} {fs : FS}
    (h : ∀ a, f a fs = g a fs) : (x >>= f) fs = (x >>= g) fs := by
  show (fun o => (∃ a, x fs (.ok a) ∧ f a fs o) ∨ (∃ e, o = .error e ∧ x fs (.error e))) =
    (fun o => (∃ a, x fs (.ok a) ∧ g a fs o) ∨ (∃ e, o = .error e ∧ x fs (.error e)))
  simp only [h]

/-- A determined action's continuation. -/
theorem ModelIO.bind_det {α β : Type} {x : ModelIO α} {a : α} {fs : FS}
    (hx : x fs = ModelIO.answer (some a)) (f : α → ModelIO β) : (x >>= f) fs = f a fs := by
  funext o
  show ((∃ a', x fs (.ok a') ∧ f a' fs o) ∨ (∃ e, o = .error e ∧ x fs (.error e))) = f a fs o
  rw [hx]
  simp [ModelIO.answer]

/-! ## Every value outcome: the calculus the driver's theorems use -/

/-- **Every value outcome of `x` on `fs` satisfies `P`**: what a theorem
about a run in the model states ("every exit 0 means …").  The rules
below peel a `do` block one step at a time: a bind hands its
continuation the first action's value with the fact that it is an
outcome; `pure` is its value; `liftIO` may answer anything. -/
@[expose] def ModelIO.AllOk {α : Type} (x : ModelIO α) (fs : FS) (P : α → Prop) : Prop :=
  ∀ v, x fs (.ok v) → P v

@[simp] theorem ModelIO.allOk_bind {α β : Type} (x : ModelIO α) (f : α → ModelIO β) (fs : FS)
    (P : β → Prop) :
    ModelIO.AllOk (x >>= f) fs P ↔ ∀ a, x fs (.ok a) → ModelIO.AllOk (f a) fs P := by
  simp only [ModelIO.AllOk, ModelIO.bind_ok]
  exact ⟨fun h a ha v hv => h v ⟨a, ha, hv⟩, fun h v ⟨a, ha, hv⟩ => h a ha v hv⟩

@[simp] theorem ModelIO.allOk_pure {α : Type} (a : α) (fs : FS) (P : α → Prop) :
    ModelIO.AllOk (pure a) fs P ↔ P a := by
  simp only [ModelIO.AllOk, ModelIO.pure_iff, Except.ok.injEq]
  exact ⟨fun h => h a rfl, fun h v hv => hv ▸ h⟩

@[simp] theorem ModelIO.allOk_liftIO {α : Type} (a : IO α) (fs : FS) (P : α → Prop) :
    ModelIO.AllOk (CheckerIO.liftIO a) fs P ↔ ∀ v, P v := by
  simp only [ModelIO.AllOk, ModelIO.liftIO_iff, forall_const]

@[simp] theorem ModelIO.allOk_map {α β : Type} (g : α → β) (x : ModelIO α) (fs : FS)
    (P : β → Prop) : ModelIO.AllOk (g <$> x) fs P ↔ ∀ a, x fs (.ok a) → P (g a) := by
  rw [map_eq_pure_bind, ModelIO.allOk_bind]
  simp only [ModelIO.allOk_pure]

/-- A caught action: its values, and the handler's for each exception
it may throw. -/
theorem ModelIO.allOk_tryCatch {α : Type} {x : ModelIO α} {h : IO.Error → ModelIO α} {fs : FS}
    {P : α → Prop} (hx : ModelIO.AllOk x fs P)
    (hh : ∀ e, x fs (.error e) → ModelIO.AllOk (h e) fs P) :
    ModelIO.AllOk (tryCatchThe IO.Error x h) fs P := by
  intro v hv
  rcases (ModelIO.tryCatch_ok x h fs v).1 hv with hv | ⟨e, he, hv⟩
  · exact hx v hv
  · exact hh e he v hv

theorem ModelIO.allOk_ite {α : Type} {c : Prop} [Decidable c] {t e : ModelIO α} {fs : FS}
    {P : α → Prop} (ht : c → ModelIO.AllOk t fs P) (he : ¬c → ModelIO.AllOk e fs P) :
    ModelIO.AllOk (if c then t else e) fs P := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact ht hc
  · simp only [hc, ↓reduceIte]; exact he hc

/-! ## The folds over a file's reads, in the model -/

/-- **A file's reads in the model**: `csz` bytes at a time from `off`,
the last read the rest (a read of a regular file returns what it asked
for, but at its end); none at `csz = 0`, whose first read is empty. -/
@[expose] def readsFrom (csz : Nat) (b : ByteArray) (off : Nat) : List ByteArray :=
  if _h : 0 < csz ∧ off < b.size then
    b.extract off (min (off + csz) b.size) :: readsFrom csz b (min (off + csz) b.size)
  else []
termination_by b.size - off
decreasing_by omega

/-- The serial fold over a list of reads, up to its first `.error`. -/
@[expose] def foldList {σ ρ : Type} (step : σ → ByteArray → Except ρ σ) (fin : σ → ρ) :
    σ → List ByteArray → ρ
  | s, [] => fin s
  | s, c :: cs =>
    match step s c with
    | .error r => r
    | .ok s => foldList step fin s cs

/-- **A file's windows in the model**: the reads cut at their last
newlines (`cutRead`), the chunks taken `m` at a time, the last window
what is left; with the bytes after the last newline.  The fold over the
windows reads the same chunks in the same groups. -/
@[expose] def winsOf (m : Nat) (acc : Array ByteArray) (pending : ByteArray) :
    List ByteArray → List (Array ByteArray) × ByteArray
  | [] => (if acc.isEmpty then [] else [acc], pending)
  | r :: rs =>
    match cutRead pending r with
    | (none, p) => winsOf m acc p rs
    | (some c, p) =>
      if m ≤ acc.size + 1 then
        let x := winsOf m #[] p rs
        (acc.push c :: x.1, x.2)
      else winsOf m (acc.push c) p rs

/-- A file's windows of `m` chunks, reads of `csz` bytes; none at
`m = 0`. -/
@[expose] def windowsOf (csz : USize) (m : Nat) (b : ByteArray) : List (Array ByteArray) × ByteArray :=
  if m = 0 then ([], .empty) else winsOf m #[] .empty (readsFrom csz.toNat b 0)

/-- The fold over a list of windows in the model, each step handed the
next window (an empty array after the last). -/
@[expose] def ModelIO.foldWins {σ ρ : Type}
    (step : σ → Array ByteArray → ModelIO (Array ByteArray) → ModelIO (Except ρ σ))
    (fin : σ → ByteArray → ρ) (tail : ByteArray) : σ → List (Array ByteArray) → ModelIO ρ
  | s, [] => pure (fin s tail)
  | s, w :: ws => do
    match ← step s w (pure (ws.headD #[])) with
    | .error r => pure r
    | .ok s => ModelIO.foldWins step fin tail s ws

/-- The monadic fold over a list of reads, up to its first `.error`. -/
@[expose] def foldListM {m : Type → Type} [Monad m] {σ ρ : Type}
    (step : σ → ByteArray → m (Except ρ σ)) (fin : σ → m ρ) : σ → List ByteArray → m ρ
  | s, [] => fin s
  | s, c :: cs => do
    match ← step s c with
    | .error r => pure r
    | .ok s => foldListM step fin s cs

/-- A positional read of a file the snapshot holds: its slice. -/
theorem ModelIO.readRange_bind {β : Type} {p : System.FilePath} {b : ByteArray} {fs : FS}
    (hb : fs.file p = some b) (off len : Nat) (f : ByteArray → ModelIO β) :
    (CheckerIO.readRange p off len >>= f : ModelIO β) fs =
      f (b.extract off (min (off + len) b.size)) fs := by
  apply ModelIO.bind_det
  show ModelIO.answer ((fs.file p).map _) = _
  rw [hb]; rfl

/-- The size of a file is its bytes' size: a value outcome of it means
the snapshot holds the file. -/
theorem ModelIO.fileSize_ok {p : System.FilePath} {fs : FS} {n : Nat} :
    (CheckerIO.fileSize p : ModelIO Nat) fs (.ok n) ↔ ∃ b, fs.file p = some b ∧ n = b.size := by
  show ModelIO.answer ((fs.file p).map (·.size)) (.ok n) ↔ _
  rw [ModelIO.answer_ok]
  cases fs.file p <;> simp [eq_comm]

/-- **A file's reads, in the model**: on a snapshot where the file has
bytes `b`, the reads of `foldReads` are `readsFrom`. -/
theorem foldReads_model {σ ρ : Type} (p : System.FilePath) (csz : Nat) {b : ByteArray} {fs : FS}
    (hb : fs.file p = some b) (step : σ → ByteArray → ModelIO (Except ρ σ))
    (fin : σ → ModelIO ρ) (off : Nat) (s : σ) :
    (foldReads (fun off => (CheckerIO.readRange p off csz : ModelIO ByteArray)) csz b.size
      step fin off s) fs = (foldListM step fin s (readsFrom csz b off)) fs := by
  induction off, s using foldReads.induct (csz := csz) (size := b.size) with
  | case1 off s h ih =>
    rw [foldReads, readsFrom, dite_eq_left h, dite_eq_left h]
    simp only [foldListM]
    rw [ModelIO.readRange_bind hb]
    apply ModelIO.bind_congr_at
    intro x
    cases x with
    | error r => rfl
    | ok s' => exact ih s'
  | case2 off s h =>
    rw [foldReads, readsFrom, dite_eq_right h, dite_eq_right h]
    rfl

/-- The monadic fold with pure steps is the pure fold. -/
theorem foldListM_pure {σ ρ : Type} (step : σ → ByteArray → Except ρ σ) (fin : σ → ρ) :
    ∀ (cs : List ByteArray) (s : σ),
    (foldListM (m := ModelIO) (fun s c => pure (step s c)) (fun s => pure (fin s)) s cs) =
      pure (foldList step fin s cs)
  | [], s => rfl
  | c :: cs, s => by
    simp only [foldListM, foldList, pure_bind]
    cases step s c with
    | error r => rfl
    | ok s' => exact foldListM_pure step fin cs s'

/-- **The serial fold, in the model**: an outcome that is a value means
the snapshot holds the file's bytes `b`, and the value is `foldList`
over the file's reads (`readsFrom`). -/
theorem foldChunks_model {σ ρ : Type} {p : System.FilePath} {csz : USize} {init : σ}
    {step : σ → ByteArray → Except ρ σ} {fin : σ → ρ} {fs : FS} {r : ρ}
    (h : (foldChunks p csz init step fin : ModelIO ρ) fs (.ok r)) :
    ∃ b, fs.file p = some b ∧ r = foldList step fin init (readsFrom csz.toNat b 0) := by
  simp only [foldChunks, ModelIO.bind_ok, ModelIO.fileSize_ok] at h
  obtain ⟨_, ⟨b, hb, rfl⟩, h⟩ := h
  refine ⟨b, hb, ?_⟩
  rw [foldReads_model p csz.toNat hb, foldListM_pure] at h
  simpa [eq_comm] using h

/-- The last chunks gathered, stepped as the last window: the fold over
the windows they are. -/
theorem winLast_foldWins {σ ρ : Type}
    (step : σ → Array ByteArray → ModelIO (Array ByteArray) → ModelIO (Except ρ σ))
    (fin : σ → ByteArray → ρ) (s : σ) (acc : Array ByteArray) (pending : ByteArray) :
    winLast step fin s acc pending =
      ModelIO.foldWins step fin pending s (if acc.isEmpty then [] else [acc]) := by
  unfold winLast
  by_cases h : acc.isEmpty
  · simp only [h, ↓reduceIte, ModelIO.foldWins]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, ModelIO.foldWins, List.headD_nil]
    congr 1

theorem headD_last (acc : Array ByteArray) :
    (if acc.isEmpty then ([] : List (Array ByteArray)) else [acc]).headD #[] = acc := by
  by_cases h : acc.isEmpty
  · simp only [h, ↓reduceIte, List.headD_nil]
    exact (Array.isEmpty_iff.1 h).symm
  · simp [h]

/-- **The windows' fold over a list of reads is the fold over their
windows** (`winsOf`): with no full window pending, the fold over the
windows of the reads; with one, that window stepped first, handed the
first of them. -/
theorem foldListM_winRead {σ ρ : Type} (w : Nat)
    (step : σ → Array ByteArray → ModelIO (Array ByteArray) → ModelIO (Except ρ σ))
    (fin : σ → ByteArray → ρ) :
    ∀ (rs : List ByteArray) (s : σ) (prev : Option (Array ByteArray)) (acc : Array ByteArray)
      (pending : ByteArray),
    foldListM (winRead w step) (winEnd step fin) (s, prev, acc, pending) rs =
      match prev with
      | none => ModelIO.foldWins step fin (winsOf w acc pending rs).2 s (winsOf w acc pending rs).1
      | some pw => step s pw (pure ((winsOf w acc pending rs).1.headD #[])) >>= fun
        | .error r => pure r
        | .ok s => ModelIO.foldWins step fin (winsOf w acc pending rs).2 s (winsOf w acc pending rs).1
  | [], s, prev, acc, pending => by
    cases prev with
    | none => simp only [foldListM, winEnd, winsOf, winLast_foldWins]
    | some pw =>
      simp only [foldListM, winEnd, winsOf, headD_last]
      congr 1
      funext x
      cases x
      · rfl
      · exact winLast_foldWins _ _ _ _ _
  | r :: rs, s, prev, acc, pending => by
    simp only [foldListM, winRead, winsOf]
    rcases hc : cutRead pending r with ⟨_ | c, p⟩
    · simp only [pure_bind]
      exact foldListM_winRead w step fin rs s prev acc p
    · simp only [Array.size_push]
      by_cases hw : w ≤ acc.size + 1
      · simp only [hw, ↓reduceIte]
        cases prev with
        | none =>
          simp only [pure_bind, foldListM_winRead w step fin rs s (some (acc.push c)) #[] p,
            ModelIO.foldWins]
        | some pw =>
          simp only [bind_assoc, ModelIO.foldWins, List.headD_cons]
          show _ = step s pw (pure (acc.push c)) >>= _
          congr 1
          funext x
          cases x with
          | error r => simp only [pure_bind]
          | ok s' =>
            simp only [pure_bind]
            exact foldListM_winRead w step fin rs s' (some (acc.push c)) #[] p
      · simp only [hw, ↓reduceIte, pure_bind]
        exact foldListM_winRead w step fin rs s prev (acc.push c) p

/-- **The windows' fold, in the model**: an outcome that is a value means
the snapshot holds the file's bytes `b`, and it is an outcome of the
fold over the file's windows (`windowsOf`), each step handed the next
window. -/
theorem foldWindows_model {σ ρ : Type} {p : System.FilePath} {csz : USize} {w : Nat} {init : σ}
    {step : σ → Array ByteArray → ModelIO (Array ByteArray) → ModelIO (Except ρ σ)}
    {fin : σ → ByteArray → ρ} {fs : FS} {r : ρ}
    (h : (foldWindows p csz w init step fin : ModelIO ρ) fs (.ok r)) :
    ∃ b, fs.file p = some b ∧
      ModelIO.foldWins step fin (windowsOf csz w b).2 init (windowsOf csz w b).1 fs (.ok r) := by
  simp only [foldWindows, ModelIO.bind_ok, ModelIO.fileSize_ok] at h
  obtain ⟨_, ⟨b, hb, rfl⟩, h⟩ := h
  refine ⟨b, hb, ?_⟩
  by_cases hw : w = 0
  · simp only [hw, ↓reduceIte, windowsOf, ModelIO.foldWins] at h ⊢
    exact h
  · simp only [hw, ↓reduceIte, windowsOf] at h ⊢
    rw [foldReads_model p csz.toNat hb, foldListM_winRead] at h
    exact h

end ConLeche
