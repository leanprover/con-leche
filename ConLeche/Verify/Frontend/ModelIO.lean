module

public import ConLeche.Frontend.CheckerIO

/-!
# The IO model's outcomes (task #450)

The checker's IO class (`CheckerIO`, `ConLeche/Frontend/CheckerIO.lean`)
has a model, `ModelIO α = FS → HS → Except IO.Error α → HS → Prop`: an
action's possible outcomes on a file system snapshot, from the open
handles before it to the open handles after it.  Here: that it is a
lawful monad, the equations the proofs peel `do` blocks with (an outcome
that is a value came from values all along: `bind_ok`, `tryCatch_ok`),
the determined operations, and the folds over a file's reads in the
model.

* **Determined actions** (`ModelIO.Det`): an action built from the file
  operations alone has one answer, and one set of open handles after it,
  on a snapshot from given handles.
* **Actions that use no handle** (`ModelIO.NoHandles`): their outcomes
  are the same from any open handles, and leave them as they were —
  `pure`, `liftIO`, and what is built from them.
* **The folds over a file's reads** (`foldReads`, `foldChunks`,
  `foldWindows`): a handle's reads are `readsFrom` (`foldReads_model`),
  the serial fold is `foldList` over them (`foldChunks_model`), and the
  windows' fold, whose steps use no handle, is `ModelIO.foldWins` over
  `windowsOf`, the reads cut at their last newlines and grouped
  (`foldWindows_model`).
-/

public section

namespace ConLeche

theorem ModelIO.ext {α : Type} {x y : ModelIO α}
    (h : ∀ fs hs o hs', x fs hs o hs' ↔ y fs hs o hs') : x = y :=
  funext fun fs => funext fun hs => funext fun o => funext fun hs' => propext (h fs hs o hs')

@[simp] theorem ModelIO.pure_iff {α : Type} (a : α) (_fs : FS) (hs : HS) (o : Except IO.Error α)
    (hs' : HS) : (pure a : ModelIO α) _fs hs o hs' ↔ o = .ok a ∧ hs' = hs := Iff.rfl

/-- An outcome of a sequence that is a value: a value of the first
action, and that value's continuation from the handles it left. -/
@[simp] theorem ModelIO.bind_ok {α β : Type} (x : ModelIO α) (f : α → ModelIO β) (fs : FS)
    (hs : HS) (v : β) (hs'' : HS) :
    (x >>= f) fs hs (.ok v) hs'' ↔ ∃ a hs', x fs hs (.ok a) hs' ∧ f a fs hs' (.ok v) hs'' := by
  show ((∃ a hs', x fs hs (.ok a) hs' ∧ f a fs hs' (.ok v) hs'') ∨
    (∃ e, (Except.ok v : Except IO.Error β) = .error e ∧ x fs hs (.error e) hs'')) ↔ _
  constructor
  · rintro (h | ⟨e, he, _⟩)
    · exact h
    · cases he
  · exact Or.inl

/-- A caught action's outcome that is a value. -/
@[simp] theorem ModelIO.tryCatch_ok {α : Type} (x : ModelIO α) (h : IO.Error → ModelIO α) (fs : FS)
    (hs : HS) (v : α) (hs' : HS) : (tryCatchThe IO.Error x h : ModelIO α) fs hs (.ok v) hs' ↔
      x fs hs (.ok v) hs' ∨ ∃ e hs₁, x fs hs (.error e) hs₁ ∧ h e fs hs₁ (.ok v) hs' := by
  show ((∃ a, (Except.ok v : Except IO.Error α) = .ok a ∧ x fs hs (.ok a) hs') ∨
    (∃ e hs₁, x fs hs (.error e) hs₁ ∧ h e fs hs₁ (.ok v) hs')) ↔ _
  constructor
  · rintro (⟨a, ha, hx⟩ | h)
    · cases ha; exact Or.inl hx
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨v, rfl, h⟩
    · exact Or.inr h

@[simp] theorem ModelIO.throw_ok {α : Type} (e : IO.Error) (fs : FS) (hs : HS) (v : α) (hs' : HS) :
    (throwThe IO.Error e : ModelIO α) fs hs (.ok v) hs' ↔ False := by
  show ((Except.ok v : Except IO.Error α) = .error e ∧ hs' = hs) ↔ False
  simp

/-- The escape, in the model: every outcome, the handles as they were. -/
@[simp] theorem ModelIO.liftIO_iff {α : Type} (a : IO α) (fs : FS) (hs : HS)
    (o : Except IO.Error α) (hs' : HS) :
    (CheckerIO.liftIO a : ModelIO α) fs hs o hs' ↔ hs' = hs := Iff.rfl

@[simp] theorem ModelIO.answer_ok {α : Type} (x : Option α) (v : α) :
    ModelIO.answer x (.ok v) ↔ x = some v := by
  cases x <;> simp [ModelIO.answer, eq_comm]

@[simp] theorem ModelIO.ret_ok {α : Type} (x : Option α) (hs₁ : HS) (v : α) (hs' : HS) :
    ModelIO.ret x hs₁ (.ok v) hs' ↔ x = some v ∧ hs' = hs₁ := by
  simp [ModelIO.ret]

instance : LawfulMonad ModelIO := LawfulMonad.mk'
  (id_map := fun x => ModelIO.ext fun fs hs o hs' => by
    show ((∃ a hs₁, x fs hs (.ok a) hs₁ ∧ (o = .ok a ∧ hs' = hs₁)) ∨
      (∃ e, o = .error e ∧ x fs hs (.error e) hs')) ↔ x fs hs o hs'
    cases o with
    | ok v => simp
    | error e => simp)
  (pure_bind := fun a f => ModelIO.ext fun fs hs o hs' => by
    show ((∃ a' hs₁, ((Except.ok a' : Except IO.Error _) = .ok a ∧ hs₁ = hs) ∧ f a' fs hs₁ o hs') ∨
      (∃ e, o = .error e ∧ ((Except.error e : Except IO.Error _) = .ok a ∧ hs' = hs))) ↔
        f a fs hs o hs'
    simp only [Except.ok.injEq, reduceCtorEq, false_and, and_false, exists_false, or_false]
    exact ⟨fun ⟨_, _, ⟨h1, h2⟩, h⟩ => h1 ▸ h2 ▸ h, fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩⟩)
  (bind_assoc := fun x f g => ModelIO.ext fun fs hs o hs'' => by
    show ((∃ b hs₂, ((∃ a hs₁, x fs hs (.ok a) hs₁ ∧ f a fs hs₁ (.ok b) hs₂) ∨
          (∃ e, (Except.ok b : Except IO.Error _) = .error e ∧ x fs hs (.error e) hs₂)) ∧
          g b fs hs₂ o hs'') ∨
        (∃ e, o = .error e ∧ ((∃ a hs₁, x fs hs (.ok a) hs₁ ∧ f a fs hs₁ (.error e) hs'') ∨
          (∃ e', (Except.error e : Except IO.Error _) = .error e' ∧ x fs hs (.error e') hs'')))) ↔
      ((∃ a hs₁, x fs hs (.ok a) hs₁ ∧ ((∃ b hs₂, f a fs hs₁ (.ok b) hs₂ ∧ g b fs hs₂ o hs'') ∨
          (∃ e, o = .error e ∧ f a fs hs₁ (.error e) hs''))) ∨
        (∃ e, o = .error e ∧ x fs hs (.error e) hs''))
    constructor
    · rintro (⟨b, hs₂, (⟨a, hs₁, ha, hb⟩ | ⟨e, he, _⟩), hg⟩ |
        ⟨e, rfl, (⟨a, hs₁, ha, hf⟩ | ⟨e', he', hx⟩)⟩)
      · exact Or.inl ⟨a, hs₁, ha, Or.inl ⟨b, hs₂, hb, hg⟩⟩
      · cases he
      · exact Or.inl ⟨a, hs₁, ha, Or.inr ⟨e, rfl, hf⟩⟩
      · cases he'; exact Or.inr ⟨e, rfl, hx⟩
    · rintro (⟨a, hs₁, ha, (⟨b, hs₂, hb, hg⟩ | ⟨e, rfl, hf⟩)⟩ | ⟨e, rfl, hx⟩)
      · exact Or.inl ⟨b, hs₂, Or.inl ⟨a, hs₁, ha, hb⟩, hg⟩
      · exact Or.inr ⟨e, rfl, Or.inl ⟨a, hs₁, ha, hf⟩⟩
      · exact Or.inr ⟨e, rfl, Or.inr ⟨e, rfl, hx⟩⟩)

/-- An outcome of a mapped action that is a value. -/
@[simp] theorem ModelIO.map_ok {α β : Type} (g : α → β) (x : ModelIO α) (fs : FS) (hs : HS)
    (v : β) (hs' : HS) :
    (g <$> x) fs hs (.ok v) hs' ↔ ∃ a, x fs hs (.ok a) hs' ∧ g a = v := by
  rw [map_eq_pure_bind, ModelIO.bind_ok]
  simp only [ModelIO.pure_iff, Except.ok.injEq]
  constructor
  · rintro ⟨a, hs₁, ha, rfl, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, hs', ha, rfl, rfl⟩

/-- Two continuations that agree on a snapshot give the same outcomes there. -/
theorem ModelIO.bind_congr_at {α β : Type} (x : ModelIO α) {f g : α → ModelIO β} {fs : FS}
    {hs : HS} (h : ∀ a hs₁, f a fs hs₁ = g a fs hs₁) : (x >>= f) fs hs = (x >>= g) fs hs := by
  show (fun o hs'' => (∃ a hs₁, x fs hs (.ok a) hs₁ ∧ f a fs hs₁ o hs'') ∨
      (∃ e, o = .error e ∧ x fs hs (.error e) hs'')) =
    (fun o hs'' => (∃ a hs₁, x fs hs (.ok a) hs₁ ∧ g a fs hs₁ o hs'') ∨
      (∃ e, o = .error e ∧ x fs hs (.error e) hs''))
  simp only [h]

/-- A determined action's continuation. -/
theorem ModelIO.bind_det {α β : Type} {x : ModelIO α} {a : α} {fs : FS} {hs hs₁ : HS}
    (hx : x fs hs = ModelIO.ret (some a) hs₁) (f : α → ModelIO β) :
    (x >>= f) fs hs = f a fs hs₁ := by
  funext o hs''
  show ((∃ a' hs', x fs hs (.ok a') hs' ∧ f a' fs hs' o hs'') ∨
    (∃ e, o = .error e ∧ x fs hs (.error e) hs'')) = f a fs hs₁ o hs''
  rw [hx]
  simp only [ModelIO.ret, ModelIO.answer, Except.ok.injEq, reduceCtorEq, false_and,
    exists_false, and_false, or_false, eq_iff_iff]
  exact ⟨fun ⟨_, _, ⟨h1, h2⟩, h⟩ => h1 ▸ h2 ▸ h, fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩⟩

/-! ## Every value outcome: the calculus the driver's theorems use -/

/-- **Every value outcome of `x` on `fs` from the open handles `hs`
satisfies `P`**: what a theorem about a run in the model states ("every
exit 0 means …").  The rules below peel a `do` block one step at a
time: a bind hands its continuation the first action's value with the
fact that it is an outcome, and the handles it left; `pure` is its
value; `liftIO` may answer anything. -/
@[expose] def ModelIO.AllOk {α : Type} (x : ModelIO α) (fs : FS) (hs : HS) (P : α → Prop) : Prop :=
  ∀ v hs', x fs hs (.ok v) hs' → P v

@[simp] theorem ModelIO.allOk_bind {α β : Type} (x : ModelIO α) (f : α → ModelIO β) (fs : FS)
    (hs : HS) (P : β → Prop) :
    ModelIO.AllOk (x >>= f) fs hs P ↔
      ∀ a hs', x fs hs (.ok a) hs' → ModelIO.AllOk (f a) fs hs' P := by
  simp only [ModelIO.AllOk, ModelIO.bind_ok]
  exact ⟨fun h a hs₁ ha v hs₂ hv => h v hs₂ ⟨a, hs₁, ha, hv⟩,
    fun h v hs₂ ⟨a, hs₁, ha, hv⟩ => h a hs₁ ha v hs₂ hv⟩

@[simp] theorem ModelIO.allOk_pure {α : Type} (a : α) (fs : FS) (hs : HS) (P : α → Prop) :
    ModelIO.AllOk (pure a) fs hs P ↔ P a := by
  simp only [ModelIO.AllOk, ModelIO.pure_iff, Except.ok.injEq]
  exact ⟨fun h => h a hs ⟨rfl, rfl⟩, fun h v _ ⟨hv, _⟩ => hv ▸ h⟩

@[simp] theorem ModelIO.allOk_liftIO {α : Type} (a : IO α) (fs : FS) (hs : HS) (P : α → Prop) :
    ModelIO.AllOk (CheckerIO.liftIO a) fs hs P ↔ ∀ v, P v := by
  simp only [ModelIO.AllOk, ModelIO.liftIO_iff]
  exact ⟨fun h v => h v hs rfl, fun h v _ _ => h v⟩

/-- The escape, then a continuation: the continuation at every value, from
the same handles. -/
@[simp] theorem ModelIO.allOk_liftIO_bind {α β : Type} (a : IO α) (f : α → ModelIO β) (fs : FS)
    (hs : HS) (P : β → Prop) :
    ModelIO.AllOk (CheckerIO.liftIO a >>= f) fs hs P ↔ ∀ v, ModelIO.AllOk (f v) fs hs P := by
  rw [ModelIO.allOk_bind]
  simp only [ModelIO.liftIO_iff]
  exact ⟨fun h v => h v hs rfl, fun h v _ he => he ▸ h v⟩

@[simp] theorem ModelIO.allOk_map {α β : Type} (g : α → β) (x : ModelIO α) (fs : FS) (hs : HS)
    (P : β → Prop) :
    ModelIO.AllOk (g <$> x) fs hs P ↔ ∀ a hs', x fs hs (.ok a) hs' → P (g a) := by
  rw [map_eq_pure_bind, ModelIO.allOk_bind]
  simp only [ModelIO.allOk_pure]

/-- A caught action: its values, and the handler's for each exception
it may throw. -/
theorem ModelIO.allOk_tryCatch {α : Type} {x : ModelIO α} {h : IO.Error → ModelIO α} {fs : FS}
    {hs : HS} {P : α → Prop} (hx : ModelIO.AllOk x fs hs P)
    (hh : ∀ e hs₁, x fs hs (.error e) hs₁ → ModelIO.AllOk (h e) fs hs₁ P) :
    ModelIO.AllOk (tryCatchThe IO.Error x h) fs hs P := by
  intro v hs' hv
  rcases (ModelIO.tryCatch_ok x h fs hs v hs').1 hv with hv | ⟨e, hs₁, he, hv⟩
  · exact hx v hs' hv
  · exact hh e hs₁ he v hs' hv

theorem ModelIO.allOk_ite {α : Type} {c : Prop} [Decidable c] {t e : ModelIO α} {fs : FS}
    {hs : HS} {P : α → Prop} (ht : c → ModelIO.AllOk t fs hs P) (he : ¬c → ModelIO.AllOk e fs hs P) :
    ModelIO.AllOk (if c then t else e) fs hs P := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact ht hc
  · simp only [hc, ↓reduceIte]; exact he hc

/-! ## Determined actions -/

/-- **The snapshot determines the action**: one answer from any open
handles — a value, or every exception (the model does not say which) —
and one set of open handles after it, from each.  What every action
built from the file operations alone is, and `liftIO` is not. -/
@[expose] def ModelIO.Det {α : Type} (x : ModelIO α) (fs : FS) : Prop :=
  ∃ a, ∀ hs, ∃ hs₁, x fs hs = ModelIO.ret a hs₁

/-- **The action gives `v`**: determined, and its answer is the value `v`. -/
@[expose] def ModelIO.Gives {α : Type} (x : ModelIO α) (fs : FS) (v : α) : Prop :=
  ∀ hs, ∃ hs₁, x fs hs = ModelIO.ret (some v) hs₁

/-- A determined action with a value outcome gives that value. -/
theorem ModelIO.Det.of_ok {α : Type} {x : ModelIO α} {fs : FS} {hs hs' : HS} {v : α}
    (hd : x.Det fs) (h : x fs hs (.ok v) hs') : x.Gives fs v := by
  obtain ⟨a, ha⟩ := hd
  obtain ⟨hs₁, h1⟩ := ha hs
  rw [h1] at h
  obtain ⟨rfl, -⟩ := (ModelIO.ret_ok a hs₁ v hs').1 h
  exact ha

theorem ModelIO.Gives.det {α : Type} {x : ModelIO α} {fs : FS} {v : α} (h : x.Gives fs v) :
    x.Det fs := ⟨some v, h⟩

/-- What an action that gives `v` has as a value outcome: `v`. -/
theorem ModelIO.Gives.ok {α : Type} {x : ModelIO α} {fs : FS} {v : α} (h : x.Gives fs v)
    {hs hs' : HS} {w : α} (hw : x fs hs (.ok w) hs') : w = v := by
  obtain ⟨hs₁, h1⟩ := h hs
  rw [h1, ModelIO.ret_ok] at hw
  exact (Option.some.inj hw.1).symm

/-- An action that gives `v` has it as an outcome, from any open handles. -/
theorem ModelIO.Gives.outcome {α : Type} {x : ModelIO α} {fs : FS} {v : α} (h : x.Gives fs v)
    (hs : HS) : ∃ hs', x fs hs (.ok v) hs' := by
  obtain ⟨hs₁, h1⟩ := h hs
  exact ⟨hs₁, by rw [h1, ModelIO.ret_ok]; exact ⟨rfl, rfl⟩⟩

/-- **`v` is a value the action can give**: a value outcome of it, from
some open handles to some.  What the specifications of the `.olean`
reads say of an action whose answer does not depend on the handles. -/
@[expose] def ModelIO.CanGive {α : Type} (x : ModelIO α) (fs : FS) (v : α) : Prop :=
  ∃ hs hs', x fs hs (.ok v) hs'

theorem ModelIO.Det.gives {α : Type} {x : ModelIO α} {fs : FS} {v : α} (hd : x.Det fs)
    (h : x.CanGive fs v) : x.Gives fs v :=
  let ⟨_, _, h⟩ := h
  hd.of_ok h

theorem ModelIO.Gives.canGive {α : Type} {x : ModelIO α} {fs : FS} {v : α} (h : x.Gives fs v) :
    x.CanGive fs v :=
  let ⟨hs', h'⟩ := h.outcome #[]
  ⟨#[], hs', h'⟩

theorem ModelIO.Gives.eq {α : Type} {x : ModelIO α} {fs : FS} {v w : α} (h : x.Gives fs v)
    (h' : x.CanGive fs w) : w = v :=
  let ⟨_, _, h'⟩ := h'
  h.ok h'

theorem ModelIO.pure_eq_ret {α : Type} (a : α) (fs : FS) (hs : HS) :
    (pure a : ModelIO α) fs hs = ModelIO.ret (some a) hs := rfl

theorem ModelIO.gives_pure {α : Type} (a : α) (fs : FS) : (pure a : ModelIO α).Gives fs a :=
  fun hs => ⟨hs, rfl⟩

theorem ModelIO.det_pure {α : Type} (a : α) (fs : FS) : (pure a : ModelIO α).Det fs :=
  (ModelIO.gives_pure a fs).det

/-- An action that gives `a`, then a continuation: the continuation at
`a`, from the open handles it left. -/
theorem ModelIO.Gives.bind_eq {α β : Type} {x : ModelIO α} {fs : FS} {a : α} (hx : x.Gives fs a)
    (f : α → ModelIO β) (hs : HS) : ∃ hs₁, (x >>= f) fs hs = f a fs hs₁ := by
  obtain ⟨hs₁, h1⟩ := hx hs
  exact ⟨hs₁, ModelIO.bind_det h1 f⟩

theorem ModelIO.Gives.bind {α β : Type} {x : ModelIO α} {f : α → ModelIO β} {fs : FS} {a : α}
    {v : β} (hx : x.Gives fs a) (hf : (f a).Gives fs v) : (x >>= f).Gives fs v := by
  intro hs
  obtain ⟨hs₁, h1⟩ := hx.bind_eq f hs
  rw [h1]
  exact hf hs₁

theorem ModelIO.det_bind {α β : Type} {x : ModelIO α} {f : α → ModelIO β} {fs : FS}
    (hx : x.Det fs) (hf : ∀ a, (f a).Det fs) : (x >>= f).Det fs := by
  obtain ⟨a, ha⟩ := hx
  cases a with
  | some v =>
    obtain ⟨b, hb⟩ := hf v
    refine ⟨b, fun hs => ?_⟩
    obtain ⟨hs₁, h1⟩ := ModelIO.Gives.bind_eq ha f hs
    rw [h1]
    exact hb hs₁
  | none =>
    refine ⟨none, fun hs => ?_⟩
    obtain ⟨hs₁, h1⟩ := ha hs
    refine ⟨hs₁, ?_⟩
    funext o hs''
    show ((∃ a' hs', x fs hs (.ok a') hs' ∧ f a' fs hs' o hs'') ∨
      (∃ e, o = .error e ∧ x fs hs (.error e) hs'')) = _
    rw [h1]
    simp only [ModelIO.ret, ModelIO.answer, reduceCtorEq, exists_false, false_and,
      false_or, Except.error.injEq, exists_eq', true_and, eq_iff_iff]
    constructor
    · rintro ⟨e, rfl, h⟩; exact ⟨⟨e, rfl⟩, h⟩
    · rintro ⟨⟨e, rfl⟩, h⟩; exact ⟨e, rfl, h⟩

theorem ModelIO.det_mapM {α β : Type} {f : α → ModelIO β} {fs : FS} :
    ∀ {xs : List α}, (∀ a ∈ xs, (f a).Det fs) → (xs.mapM f).Det fs
  | [], _ => ModelIO.det_pure _ _
  | x :: xs, h => by
    rw [List.mapM_cons]
    refine ModelIO.det_bind (h x List.mem_cons_self) fun _ => ?_
    refine ModelIO.det_bind (ModelIO.det_mapM fun a ha => h a (List.mem_cons_of_mem _ ha))
      fun _ => ModelIO.det_pure _ _

/-- A determined action, caught: its value, the handler never asked. -/
theorem ModelIO.tryCatch_det {α : Type} {x : ModelIO α} {h : IO.Error → ModelIO α} {fs : FS}
    {hs hs₁ : HS} {a : α} (hx : x fs hs = ModelIO.ret (some a) hs₁) :
    (tryCatchThe IO.Error x h : ModelIO α) fs hs = ModelIO.ret (some a) hs₁ := by
  funext o hs'
  show ((∃ a', o = .ok a' ∧ x fs hs (.ok a') hs') ∨
    (∃ e hs₂, x fs hs (.error e) hs₂ ∧ h e fs hs₂ o hs')) = _
  rw [hx]
  simp only [ModelIO.ret, ModelIO.answer, Except.ok.injEq, reduceCtorEq, false_and,
    exists_false, or_false, eq_iff_iff]
  constructor
  · rintro ⟨_, rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨_, rfl, rfl, rfl⟩

/-- A determined action, mapped. -/
theorem ModelIO.map_det {α β : Type} {x : ModelIO α} {g : α → β} {fs : FS} {hs hs₁ : HS} {a : α}
    (hx : x fs hs = ModelIO.ret (some a) hs₁) :
    (g <$> x : ModelIO β) fs hs = ModelIO.ret (some (g a)) hs₁ := by
  rw [map_eq_pure_bind, ModelIO.bind_det hx]
  rfl

/-- An action that gives `a`, caught: it gives `a`, the handler never asked. -/
theorem ModelIO.Gives.tryCatch {α : Type} {x : ModelIO α} {h : IO.Error → ModelIO α} {fs : FS}
    {a : α} (hx : x.Gives fs a) : (tryCatchThe IO.Error x h : ModelIO α).Gives fs a := fun hs => by
  obtain ⟨hs₁, h1⟩ := hx hs
  exact ⟨hs₁, ModelIO.tryCatch_det h1⟩

/-- An action that gives `a`, mapped. -/
theorem ModelIO.Gives.map {α β : Type} {x : ModelIO α} {g : α → β} {fs : FS} {a : α}
    (hx : x.Gives fs a) : (g <$> x : ModelIO β).Gives fs (g a) := fun hs => by
  obtain ⟨hs₁, h1⟩ := hx hs
  exact ⟨hs₁, ModelIO.map_det h1⟩

/-! ## Actions that use no handle -/

/-- **An action that uses no handle**: its outcomes from any open handles
are its outcomes from none, and it leaves the handles as they were. -/
@[expose] def ModelIO.NoHandles {α : Type} (x : ModelIO α) : Prop :=
  ∀ fs hs o hs', x fs hs o hs' ↔ x fs #[] o #[] ∧ hs' = hs

theorem ModelIO.noHandles_pure {α : Type} (a : α) : (pure a : ModelIO α).NoHandles := by
  intro fs hs o hs'
  simp only [ModelIO.pure_iff, and_true]

theorem ModelIO.noHandles_liftIO {α : Type} (a : IO α) :
    (CheckerIO.liftIO a : ModelIO α).NoHandles := by
  intro fs hs o hs'
  simp only [ModelIO.liftIO_iff, true_and]

theorem ModelIO.noHandles_bind {α β : Type} {x : ModelIO α} {f : α → ModelIO β}
    (hx : x.NoHandles) (hf : ∀ a, (f a).NoHandles) : (x >>= f).NoHandles := by
  intro fs hs o hs''
  show ((∃ a hs₁, x fs hs (.ok a) hs₁ ∧ f a fs hs₁ o hs'') ∨
      (∃ e, o = .error e ∧ x fs hs (.error e) hs'')) ↔
    ((∃ a hs₁, x fs #[] (.ok a) hs₁ ∧ f a fs hs₁ o #[]) ∨
      (∃ e, o = .error e ∧ x fs #[] (.error e) #[])) ∧ hs'' = hs
  constructor
  · rintro (⟨a, hs₁, ha, hb⟩ | ⟨e, rfl, he⟩)
    · have h1 := (hx fs hs _ hs₁).1 ha
      have h2 := (hf a fs hs₁ o hs'').1 hb
      have h1' : x fs #[] (.ok a) #[] := h1.1
      exact ⟨Or.inl ⟨a, #[], (hx fs #[] _ #[]).2 ⟨h1', rfl⟩, h2.1⟩, h2.2.trans h1.2⟩
    · have h1 := (hx fs hs _ hs'').1 he
      exact ⟨Or.inr ⟨e, rfl, h1.1⟩, h1.2⟩
  · rintro ⟨(⟨a, hs₁, ha, hb⟩ | ⟨e, rfl, he⟩), hh⟩
    · have h1 := (hx fs #[] _ hs₁).1 ha
      have h2 := (hf a fs hs₁ o #[]).1 hb
      exact Or.inl ⟨a, hs, (hx fs hs _ hs).2 ⟨h1.1, rfl⟩, (hf a fs hs o hs'').2 ⟨h2.1, hh⟩⟩
    · exact Or.inr ⟨e, rfl, (hx fs hs _ hs'').2 ⟨he, hh⟩⟩

theorem ModelIO.NoHandles.at {α : Type} {x : ModelIO α} (hx : x.NoHandles) {fs : FS} {hs : HS}
    {o : Except IO.Error α} {hs' : HS} (h : x fs hs o hs') : x fs #[] o #[] :=
  ((hx fs hs o hs').1 h).1

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

/-- A read of an open handle: the slice from its position, and the
position moved past it. -/
theorem ModelIO.read_at {h : Nat} {b : ByteArray} {pos : Nat} {hs : HS} (hh : hs[h]? = some (b, pos))
    (n : USize) (fs : FS) :
    (CheckerIO.read (m := ModelIO) h n) fs hs =
      ModelIO.ret (some (b.extract pos (min (pos + n.toNat) b.size)))
        (hs.set! h (b, min (pos + n.toNat) b.size)) := by
  show ModelIO.read h n fs hs = _
  unfold ModelIO.read
  rw [hh]

/-- The open of a file the snapshot holds: a new handle at its start. -/
theorem ModelIO.openRead_at {p : System.FilePath} {b : ByteArray} {fs : FS}
    (hb : fs.file p = some b) (hs : HS) :
    (CheckerIO.openRead (m := ModelIO) p) fs hs = ModelIO.ret (some hs.size) (hs.push (b, 0)) := by
  show ModelIO.openRead p fs hs = _
  unfold ModelIO.openRead
  rw [hb]

/-- The size of a file the snapshot holds. -/
theorem ModelIO.fileSize_at {p : System.FilePath} {b : ByteArray} {fs : FS}
    (hb : fs.file p = some b) (hs : HS) :
    (CheckerIO.fileSize p : ModelIO Nat) fs hs = ModelIO.ret (some b.size) hs := by
  show ModelIO.ret ((fs.file p).map (·.size)) hs = _
  rw [hb]; rfl

/-- The size of a file is its bytes' size: a value outcome of it means
the snapshot holds the file. -/
theorem ModelIO.fileSize_ok {p : System.FilePath} {fs : FS} {hs : HS} {n : Nat} {hs' : HS} :
    (CheckerIO.fileSize p : ModelIO Nat) fs hs (.ok n) hs' ↔
      ∃ b, fs.file p = some b ∧ n = b.size ∧ hs' = hs := by
  show ModelIO.ret ((fs.file p).map (·.size)) hs (.ok n) hs' ↔ _
  rw [ModelIO.ret_ok]
  cases fs.file p <;> simp [eq_comm]

/-- The read of the handle `h` once more, at the position the last left. -/
theorem getElem?_set!_handle {hs : HS} {h : Nat} {b : ByteArray} {pos q : Nat}
    (hh : hs[h]? = some (b, pos)) : (hs.set! h (b, q))[h]? = some (b, q) := by
  have hlt : h < hs.size := by
    rcases Nat.lt_or_ge h hs.size with hl | hl
    · exact hl
    · rw [Array.getElem?_eq_none hl] at hh; cases hh
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt]

/-- **A handle's reads with pure steps, in the model**: from the handle's
position `off`, determined — `foldList` over `readsFrom`, whatever the
open handles after. -/
theorem foldReads_pure {σ ρ : Type} (csz : USize) {b : ByteArray} (step : σ → ByteArray → Except ρ σ)
    (fin : σ → ρ) (h : Nat) (fs : FS) (off : Nat) (s : σ) :
    ∀ {hs : HS}, hs[h]? = some (b, off) → ∃ hs₁,
    (foldReads (CheckerIO.read (m := ModelIO) h csz) csz.toNat b.size
      (fun s c => pure (step s c)) (fun s => pure (fin s)) off s) fs hs =
      ModelIO.ret (some (foldList step fin s (readsFrom csz.toNat b off))) hs₁ := by
  induction off, s using foldReads.induct (csz := csz.toNat) (size := b.size) with
  | case1 off s hc ih =>
    intro hs hh
    rw [foldReads, readsFrom, dite_eq_left hc, dite_eq_left hc]
    rw [ModelIO.bind_det (ModelIO.read_at hh csz fs), pure_bind]
    simp only [foldList]
    cases step s (b.extract off (min (off + csz.toNat) b.size)) with
    | error r => exact ⟨_, rfl⟩
    | ok s' => exact ih s' (getElem?_set!_handle hh)
  | case2 off s hc =>
    intro hs _
    rw [foldReads, readsFrom, dite_eq_right hc, dite_eq_right hc]
    exact ⟨hs, rfl⟩

/-- **A handle's reads, in the model**: with steps and an end that use no
handle, an outcome of the reads of `h` from its position `off` is an
outcome of the fold over `readsFrom`, from no open handles. -/
theorem foldReads_model {σ ρ : Type} (csz : USize) {b : ByteArray}
    {step : σ → ByteArray → ModelIO (Except ρ σ)} {fin : σ → ModelIO ρ}
    (hstep : ∀ s c, (step s c).NoHandles) (hfin : ∀ s, (fin s).NoHandles) (h : Nat) (fs : FS)
    (off : Nat) (s : σ) :
    ∀ {hs : HS} {o : Except IO.Error ρ} {hs' : HS}, hs[h]? = some (b, off) →
    (foldReads (CheckerIO.read (m := ModelIO) h csz) csz.toNat b.size step fin off s) fs hs o hs' →
      (foldListM step fin s (readsFrom csz.toNat b off)) fs #[] o #[] := by
  induction off, s using foldReads.induct (csz := csz.toNat) (size := b.size) with
  | case1 off s hc ih =>
    intro hs o hs' hh hf
    rw [foldReads, dite_eq_left hc, ModelIO.bind_det (ModelIO.read_at hh csz fs)] at hf
    rw [readsFrom, dite_eq_left hc]
    simp only [foldListM]
    rcases hf with ⟨x, hs₁, hx, hk⟩ | ⟨e, rfl, he⟩
    · have hx' := (hstep _ _).at hx
      refine Or.inl ⟨x, #[], (hstep _ _ fs #[] _ #[]).2 ⟨hx', rfl⟩, ?_⟩
      have he : hs₁ = hs.set! h (b, min (off + csz.toNat) b.size) := ((hstep _ _ _ _ _ _).1 hx).2
      subst he
      cases x with
      | error r => exact ⟨hk.1, rfl⟩
      | ok s' => exact ih s' (getElem?_set!_handle hh) hk
    · exact Or.inr ⟨e, rfl, (hstep _ _).at he⟩
  | case2 off s hc =>
    intro hs o hs' _ hf
    rw [foldReads, dite_eq_right hc] at hf
    rw [readsFrom, dite_eq_right hc]
    exact (hfin s).at hf

/-- **The serial fold on a file the snapshot holds**: determined, `foldList`
over the file's reads, whatever the open handles after. -/
theorem foldChunks_det {σ ρ : Type} {p : System.FilePath} (csz : USize) (init : σ)
    (step : σ → ByteArray → Except ρ σ) (fin : σ → ρ) {fs : FS} {b : ByteArray}
    (hb : fs.file p = some b) :
    (foldChunks p csz init step fin : ModelIO ρ).Gives fs
      (foldList step fin init (readsFrom csz.toNat b 0)) := by
  intro hs
  simp only [foldChunks]
  rw [ModelIO.bind_det (ModelIO.fileSize_at hb hs), ModelIO.bind_det (ModelIO.openRead_at hb hs)]
  exact foldReads_pure csz step fin hs.size fs 0 init Array.getElem?_push_size

/-- **The serial fold, in the model**: an outcome that is a value means
the snapshot holds the file's bytes `b`, and the value is `foldList`
over the file's reads (`readsFrom`). -/
theorem foldChunks_model {σ ρ : Type} {p : System.FilePath} {csz : USize} {init : σ}
    {step : σ → ByteArray → Except ρ σ} {fin : σ → ρ} {fs : FS} {hs : HS} {r : ρ} {hs' : HS}
    (h : (foldChunks p csz init step fin : ModelIO ρ) fs hs (.ok r) hs') :
    ∃ b, fs.file p = some b ∧ r = foldList step fin init (readsFrom csz.toNat b 0) := by
  have h0 := h
  simp only [foldChunks, ModelIO.bind_ok, ModelIO.fileSize_ok] at h0
  obtain ⟨_, _, ⟨b, hb, -, -⟩, -⟩ := h0
  refine ⟨b, hb, ?_⟩
  obtain ⟨hs₁, he⟩ := foldChunks_det csz init step fin hb hs
  rw [he, ModelIO.ret_ok] at h
  exact (Option.some.inj h.1).symm

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

/-- A step of the windows' fold that uses no handle on every window to
come it is handed. -/
abbrev WinStepNoHandles {σ ρ : Type}
    (step : σ → Array ByteArray → ModelIO (Array ByteArray) → ModelIO (Except ρ σ)) : Prop :=
  ∀ s w (ws : Array ByteArray), (step s w (pure ws)).NoHandles

theorem winLast_noHandles {σ ρ : Type}
    {step : σ → Array ByteArray → ModelIO (Array ByteArray) → ModelIO (Except ρ σ)}
    (hstep : WinStepNoHandles step) (fin : σ → ByteArray → ρ) (s : σ) (acc : Array ByteArray)
    (pending : ByteArray) : (winLast step fin s acc pending).NoHandles := by
  unfold winLast
  split
  · exact ModelIO.noHandles_pure _
  · refine ModelIO.noHandles_bind (hstep _ _ _) fun x => ?_
    cases x <;> exact ModelIO.noHandles_pure _

theorem winEnd_noHandles {σ ρ : Type}
    {step : σ → Array ByteArray → ModelIO (Array ByteArray) → ModelIO (Except ρ σ)}
    (hstep : WinStepNoHandles step) (fin : σ → ByteArray → ρ) (b : WinBuf σ) :
    (winEnd step fin b).NoHandles := by
  obtain ⟨s, _ | pw, acc, pending⟩ := b
  · exact winLast_noHandles hstep fin s acc pending
  · refine ModelIO.noHandles_bind (hstep _ _ _) fun x => ?_
    cases x
    · exact ModelIO.noHandles_pure _
    · exact winLast_noHandles hstep fin _ acc pending

theorem winRead_noHandles {σ ρ : Type} (w : Nat)
    {step : σ → Array ByteArray → ModelIO (Array ByteArray) → ModelIO (Except ρ σ)}
    (hstep : WinStepNoHandles step) (b : WinBuf σ) (r : ByteArray) :
    (winRead w step b r).NoHandles := by
  obtain ⟨s, prev, acc, pending⟩ := b
  simp only [winRead]
  repeat' split
  all_goals first
    | exact ModelIO.noHandles_pure _
    | exact ModelIO.noHandles_bind (hstep _ _ _) fun x => by
        cases x <;> exact ModelIO.noHandles_pure _

/-- **The windows' fold, in the model**: with a step that uses no handle,
an outcome that is a value means the snapshot holds the file's bytes
`b`, and it is an outcome, from no open handles, of the fold over the
file's windows (`windowsOf`), each step handed the next window. -/
theorem foldWindows_model {σ ρ : Type} {p : System.FilePath} {csz : USize} {w : Nat} {init : σ}
    {step : σ → Array ByteArray → ModelIO (Array ByteArray) → ModelIO (Except ρ σ)}
    {fin : σ → ByteArray → ρ} {fs : FS} {hs : HS} {r : ρ} {hs' : HS}
    (hstep : WinStepNoHandles step)
    (h : (foldWindows p csz w init step fin : ModelIO ρ) fs hs (.ok r) hs') :
    ∃ b, fs.file p = some b ∧
      ModelIO.foldWins step fin (windowsOf csz w b).2 init (windowsOf csz w b).1 fs #[]
        (.ok r) #[] := by
  have h0 := h
  simp only [foldWindows, ModelIO.bind_ok, ModelIO.fileSize_ok] at h0
  obtain ⟨_, _, ⟨b, hb, -, -⟩, -⟩ := h0
  refine ⟨b, hb, ?_⟩
  simp only [foldWindows] at h
  rw [ModelIO.bind_det (ModelIO.fileSize_at hb hs)] at h
  by_cases hw : w = 0
  · simp only [hw, ↓reduceIte, ModelIO.pure_iff, Except.ok.injEq] at h
    simp only [hw, ↓reduceIte, windowsOf, ModelIO.foldWins, ModelIO.pure_iff, and_true]
    exact congrArg Except.ok h.1
  · simp only [hw, ↓reduceIte] at h
    rw [ModelIO.bind_det (ModelIO.openRead_at hb hs)] at h
    have := foldReads_model csz (winRead_noHandles w hstep) (winEnd_noHandles hstep fin)
      hs.size fs 0 _ Array.getElem?_push_size h
    simp only [hw, ↓reduceIte, windowsOf]
    rw [foldListM_winRead] at this
    exact this

end ConLeche
