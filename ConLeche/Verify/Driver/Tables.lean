module

public import ConLeche.Driver.Tables
public import ConLeche.Verify.Driver.Shared

/-!
# The tables, in the model

What the tables of `ConLeche/Driver/Tables.lean` hold, on a snapshot:

* `modTables_within` — **the tables' reads refine the search path's**: every table was read off
  the snapshot (`TablesOk`: the module's location is `findModule`'s answer, its imports, where
  held, `moduleImports`', its two parts' name positions, where held, `readPartNamesAt`'s at that
  location, its private view's files, where held, `readFilesAt`'s there), so each of the three reads answered from them is one of the search path's
  (`OleanReads.Within`): a held value is one the read can give, a read at a table's location is
  the search path's read, since the location is the one `findModule` gives (it is determined
  on the snapshot);
* `workerTables_ok` — **a worker's tables are read off the snapshot**: its own module's table,
  and every table the header fixpoint's run enters (`tabImports`), whatever the run's outcome
  (`levelsGo_keeps`: an invariant of the state that every header read keeps is kept by the
  whole fixpoint).
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-! ## The tables' reads -/

/-- **Tables read off the snapshot.** -/
@[expose] def TablesOk (fs : FS) (sp : Roots) (T : ModTables) : Prop :=
  ∀ t ∈ T.mods, ModelIO.CanGive (findModule sp t.name) fs (.ok t.loc) ∧
    (∀ is, t.imports = some is → ModelIO.CanGive (moduleImports sp t.name) fs (.ok is)) ∧
    (∀ p, t.priv = some p →
      ModelIO.CanGive (readPartNamesAt t.loc (t.name, .private)) fs (.ok p)) ∧
    (∀ p, t.expo = some p →
      ModelIO.CanGive (readPartNamesAt t.loc (t.name, .exported)) fs (.ok p)) ∧
    (∀ f, t.files = some f → ModelIO.CanGive (readFilesAt t.loc t.name .private) fs (.ok f))

theorem ModTables.find_mem {T : ModTables} {m : Name} {t : ModTable} (h : T.find m = some t) :
    t ∈ T.mods ∧ t.name = m := by
  simp only [ModTables.find] at h
  split at h
  · split at h
    · rename_i t' ht'
      by_cases hn : (t'.name == m) = true
      · simp only [hn, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨Array.mem_of_getElem? ht', beq_iff_eq.1 hn⟩
      · simp [hn] at h
    · cases h
  · cases h

/-- A value a table holds is one the read it stands for gives, from any open handles. -/
theorem ModelIO.Within.of_table {α : Type} {fs : FS} {a : ModelIO α} {v : α}
    (ha : ModelIO.Within fs a a) (hv : ModelIO.CanGive a fs v) : ModelIO.Within fs (pure v) a := by
  intro _ o _ ho hs₀
  simp only [ModelIO.pure_iff] at ho
  obtain ⟨rfl, -⟩ := ho
  obtain ⟨_, _, hv⟩ := hv
  exact ha _ _ _ hv hs₀

/-- A read at a module's location, where the location is the search path's: the read on the
search path, from any open handles. -/
theorem ModelIO.Within.at_loc {α : Type} {fs : FS} {sp : Roots} {m : Name} {loc : Located}
    {a : Located → ModelIO (Except CheckError α)} (hloc : ModelIO.CanGive (findModule sp m) fs (.ok loc))
    (ha : ModelIO.Within fs (a loc) (a loc)) :
    ModelIO.Within fs (a loc) (do
      match ← findModule sp m with
      | .error e => pure (.error e)
      | .ok loc => a loc) := by
  intro hs o hs' ho hs₀
  obtain ⟨_, _, hf⟩ := hloc
  obtain ⟨hs₂, hf⟩ := findModule_within fs sp m _ _ _ hf hs₀
  obtain ⟨hs₁, hr⟩ := ha hs o hs' ho hs₂
  exact ⟨hs₁, Or.inl ⟨_, hs₂, hf, hr⟩⟩

theorem readPartNamesAt_within (fs : FS) (loc : Located) (x : Name × OLeanLevel) :
    ModelIO.Within fs (readPartNamesAt loc x) (readPartNamesAt loc x) := by
  simp only [readPartNamesAt]
  exact ModelIO.Within.bind (readFilesAt_within fs _ _ _) fun r => by
    rcases r with e | f
    · exact ModelIO.Within.pure _
    · exact ModelIO.Within.pure _

/-- **The tables' reads refine the search path's**, a read the tables do not hold made
through roots read off the snapshot. -/
theorem modTables_within {fs : FS} {sp : Roots} {R : Roots} {T : ModTables}
    (hR : R.Ok fs) (hp : R.bare = sp) (hT : TablesOk fs sp T) :
    OleanReads.Within fs (T.reads R) sp := by
  refine ⟨fun m => ?_, fun m level => ?_, fun x => ?_⟩
  · simp only [ModTables.reads]
    split
    · rename_i t ht
      obtain ⟨hm, rfl⟩ := ModTables.find_mem ht
      split
      · rename_i is his
        exact ModelIO.Within.of_table (moduleImports_within fs _ _) ((hT t hm).2.1 is his)
      · exact ModelIO.Within.at_loc (a := fun loc => readImportsAt loc t.name) (hT t hm).1
          (readImportsAt_within fs _ _)
    · exact ModelIO.Within.of_sub (moduleImports_sub' hR hp m) (moduleImports_within fs _ m)
  · simp only [ModTables.reads]
    split
    · rename_i t ht
      obtain ⟨hm, rfl⟩ := ModTables.find_mem ht
      have hat : ∀ level, ModelIO.Within fs (readFilesAt t.loc t.name level)
          (readFiles (sp : Roots) t.name level) := fun level =>
        ModelIO.Within.at_loc (a := fun loc => readFilesAt loc t.name level) (hT t hm).1
          (readFilesAt_within fs _ _ _)
      split
      · rename_i f hf
        exact ModelIO.Within.of_table (readFiles_within fs _ _ _)
          ((hat .private).canGive ((hT t hm).2.2.2.2 f hf))
      · exact hat _
    · exact ModelIO.Within.of_sub (readFiles_sub' hR hp m level) (readFiles_within fs _ m level)
  · obtain ⟨n, level⟩ := x
    simp only [ModTables.reads]
    split
    · rename_i t ht
      obtain ⟨hm, rfl⟩ := ModTables.find_mem ht
      have hat : ∀ level, ModelIO.Within fs (readPartNamesAt t.loc (t.name, level))
          (readPartNames (sp : Roots) (t.name, level)) := fun level =>
        ModelIO.Within.at_loc (a := fun loc => readPartNamesAt loc (t.name, level)) (hT t hm).1
          (readPartNamesAt_within fs _ _)
      split
      · rename_i p hp
        exact ModelIO.Within.of_table (readPartNames_within fs _ _)
          ((hat .private).canGive ((hT t hm).2.2.1 p hp))
      · rename_i e he
        exact ModelIO.Within.of_table (readPartNames_within fs _ _)
          ((hat .exported).canGive ((hT t hm).2.2.2.1 e he))
      · exact hat _
    · exact ModelIO.Within.of_sub (readPartNames_sub' hR hp (n, level))
        (readPartNames_within fs _ (n, level))

/-! ## A state kept by the header fixpoint -/

/-- **`P` of the state is kept by `x`**: at every value outcome of `x` from a state where `P`
holds, `P` holds of the state `x` leaves. -/
@[expose] def StateKeeps {σ α : Type} (P : σ → Prop) (fs : FS) (x : StateT σ ModelIO α) : Prop :=
  ∀ T hs a T' hs', x T fs hs (.ok (a, T')) hs' → P T → P T'

theorem StateKeeps.pure {σ α : Type} {P : σ → Prop} {fs : FS} (v : α) :
    StateKeeps P fs (Pure.pure v : StateT σ ModelIO α) := by
  intro T hs a T' hs' h hT
  have h' : (Pure.pure (v, T) : ModelIO (α × σ)) fs hs (.ok (a, T')) hs' := h
  simp only [ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h'
  obtain ⟨⟨-, rfl⟩, -⟩ := h'
  exact hT

theorem StateKeeps.bind {σ α β : Type} {P : σ → Prop} {fs : FS} {x : StateT σ ModelIO α}
    {f : α → StateT σ ModelIO β} (hx : StateKeeps P fs x) (hf : ∀ a, StateKeeps P fs (f a)) :
    StateKeeps P fs (x >>= f) := by
  intro T hs b T' hs' h hT
  have h' : (x T >>= fun p => f p.1 p.2 : ModelIO (β × σ)) fs hs (.ok (b, T')) hs' := h
  simp only [ModelIO.bind_ok] at h'
  obtain ⟨⟨a, T₁⟩, hs₁, h1, h2⟩ := h'
  exact hf a T₁ hs₁ b T' hs' h2 (hx T hs a T₁ hs₁ h1 hT)

/-- **The header fixpoint keeps what its header reads keep.** -/
theorem levelsGo_keeps {σ : Type} {P : σ → Prop} {fs : FS}
    {imps : Name → StateT σ ModelIO (Except CheckError (Array ImportRec))}
    (h : ∀ m, StateKeeps P fs (imps m)) (gPriv : Bool) :
    ∀ fuel ws st, StateKeeps P fs (levelsGo imps gPriv fuel ws st)
  | _, [], st => by simp only [levelsGo]; exact StateKeeps.pure _
  | 0, _ :: _, _ => by simp only [levelsGo]; exact StateKeeps.pure _
  | fuel + 1, .done m fl :: rest, st => by
    simp only [levelsGo]
    exact levelsGo_keeps h gPriv fuel _ _
  | fuel + 1, .imp pf i :: rest, st => by
    simp only [levelsGo]
    split
    · exact levelsGo_keeps h gPriv fuel _ _
    · split
      · split
        · exact levelsGo_keeps h gPriv fuel _ _
        · exact levelsGo_keeps h gPriv fuel _ _
      · split
        · exact StateKeeps.pure _
        · refine StateKeeps.bind (h _) fun r => ?_
          rcases r with e | is
          · exact StateKeeps.pure _
          · exact levelsGo_keeps h gPriv fuel _ _

theorem headerFixpoint_keeps {σ : Type} {P : σ → Prop} {fs : FS}
    {imps : Name → StateT σ ModelIO (Except CheckError (Array ImportRec))}
    (h : ∀ m, StateKeeps P fs (imps m)) (isModule : Bool) (imports : Array ImportRec) :
    StateKeeps P fs (headerFixpoint imps isModule imports) := by
  simp only [headerFixpoint]
  refine StateKeeps.bind (levelsGo_keeps h _ _ _ _) fun r => ?_
  rcases r with e | st <;> exact StateKeeps.pure _

/-! ## A worker's tables -/

theorem TablesOk.push {fs : FS} {sp : Roots} {T : ModTables} {t : ModTable}
    (hT : TablesOk fs sp T)
    (ht : ModelIO.CanGive (findModule sp t.name) fs (.ok t.loc) ∧
      (∀ is, t.imports = some is → ModelIO.CanGive (moduleImports sp t.name) fs (.ok is)) ∧
      (∀ p, t.priv = some p →
        ModelIO.CanGive (readPartNamesAt t.loc (t.name, .private)) fs (.ok p)) ∧
      (∀ p, t.expo = some p →
        ModelIO.CanGive (readPartNamesAt t.loc (t.name, .exported)) fs (.ok p)) ∧
      (∀ f, t.files = some f →
        ModelIO.CanGive (readFilesAt t.loc t.name .private) fs (.ok f))) :
    TablesOk fs sp (T.push t) := by
  intro u hu
  simp only [ModTables.push, Array.mem_push] at hu
  rcases hu with hu | rfl
  · exact hT u hu
  · exact ht

theorem TablesOk.empty (fs : FS) (sp : Roots) : TablesOk fs sp {} := by
  intro t ht
  simp at ht

/-- A header read at the location `findModule` gives is `moduleImports`'. -/
theorem moduleImports_at {sp : Roots} {n : Name} {fs : FS} {loc : Located}
    {is : Array ImportRec} {hs hs₁ hs₂ : HS}
    (hf : (findModule sp n : ModelIO _) fs hs (.ok (.ok loc)) hs₁)
    (hr : (readImportsAt loc n : ModelIO _) fs hs₁ (.ok (.ok is)) hs₂) :
    ModelIO.CanGive (moduleImports sp n) fs (.ok is) :=
  ⟨hs, hs₂, by simp only [moduleImports, ModelIO.bind_ok]; exact ⟨_, _, hf, hr⟩⟩

/-- **What a worker's tables keep**: the roots read off the snapshot, on the search path `sp`,
and the tables. -/
@[expose] def WorkerTablesOk (fs : FS) (sp : Roots) (RT : Roots × ModTables) : Prop :=
  RT.1.Ok fs ∧ RT.1.bare = sp ∧ TablesOk fs sp RT.2

/-- A location through roots read off the snapshot is the search path's. -/
theorem findModule_at {fs : FS} {sp : Roots} {R : Roots} (hR : R.Ok fs) (hp : R.bare = sp)
    {n : Name} {loc : Located} {hs hs₁ : HS}
    (hf : (findModule R n : ModelIO _) fs hs (.ok (.ok loc)) hs₁) :
    (findModule (sp : Roots) n : ModelIO _) fs hs (.ok (.ok loc)) hs₁ := by
  have := findModule_sub hR n _ _ _ hf
  rwa [hp] at this

theorem tabImports_keeps (fs : FS) (sp : Roots) (n : Name) :
    StateKeeps (WorkerTablesOk fs sp) fs (tabImports n) := by
  intro ⟨R, T⟩ hs a RT' hs' h ⟨hR, hp, hT⟩
  simp only [tabImports, ModelIO.bind_ok] at h
  obtain ⟨R₁, hs₀, hR₁, x, hs₁, hx, h⟩ := h
  obtain ⟨hR₁ok, hR₁p⟩ := Roots.resolve_ok hR hR₁
  have hp₁ : R₁.bare = sp := hR₁p.trans hp
  rcases x with e | loc
  · simp only [ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact ⟨hR₁ok, hp₁, hT⟩
  simp only [ModelIO.bind_ok] at h
  obtain ⟨y, hs₂, hy, h⟩ := h
  rcases y with e | is
  · simp only [ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact ⟨hR₁ok, hp₁, hT⟩
  simp only [ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, rfl⟩, -⟩ := h
  have hx' := findModule_at hR₁ok hp₁ hx
  refine ⟨hR₁ok, hp₁, hT.push ⟨⟨_, _, hx'⟩, fun is' h' => ?_, (fun _ h' => by cases h'),
    (fun _ h' => by cases h'), (fun _ h' => by cases h')⟩⟩
  cases h'
  exact moduleImports_at hx' hy

/-- **A worker's tables are read off the snapshot**, and so are the roots beside them. -/
theorem workerTables_ok {fs : FS} {sp : Roots} (hsp : sp.bare = sp) {m : Name} {R : Roots}
    {T : ModTables} {hs hs' : HS} (h : (workerTables sp m : ModelIO _) fs hs (.ok (R, T)) hs') :
    R.Ok fs ∧ R.bare = sp ∧ TablesOk fs sp T := by
  simp only [workerTables, ModelIO.bind_ok] at h
  obtain ⟨R₀, hs₀, hR₀, x, hs₁, hx, h⟩ := h
  obtain ⟨hR₀ok, hR₀p⟩ := Roots.resolve_ok (hsp ▸ Roots.ok_bare fs sp) hR₀
  replace hR₀p := hR₀p.trans hsp
  rcases x with e | loc
  · simp only [ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact ⟨hR₀ok, hR₀p, TablesOk.empty fs sp⟩
  have hx' := findModule_at hR₀ok hR₀p hx
  simp only [ModelIO.bind_ok] at h
  obtain ⟨y, hs₂, hy, h⟩ := h
  rcases y with e | f
  · simp only [ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact ⟨hR₀ok, hR₀p, (TablesOk.empty fs sp).push ⟨⟨_, _, hx'⟩, (fun _ h' => by cases h'),
      (fun _ h' => by cases h'), (fun _ h' => by cases h'), (fun _ h' => by cases h')⟩⟩
  have hf : ModelIO.CanGive (readFilesAt loc m .private) fs (.ok f) := ⟨_, _, hy⟩
  simp only at h
  cases hn : namesOf m f .private with
  | error e =>
    simp only [hn, ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact ⟨hR₀ok, hR₀p, (TablesOk.empty fs sp).push ⟨⟨_, _, hx'⟩, (fun _ h' => by cases h'),
      (fun _ h' => by cases h'), (fun _ h' => by cases h'), (fun f' h' => by cases h'; exact hf)⟩⟩
  | ok own =>
  simp only [hn, ModelIO.bind_ok] at h
  obtain ⟨⟨r, RT⟩, hs₃, hr, h⟩ := h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨h, -⟩ := h
  subst h
  have hp : ModelIO.CanGive (readPartNamesAt loc (m, .private)) fs (.ok own) := by
    refine ⟨hs₁, hs₂, ?_⟩
    simp only [readPartNamesAt, ModelIO.bind_ok]
    exact ⟨.ok f, hs₂, hy, by simp [hn]⟩
  exact headerFixpoint_keeps (tabImports_keeps fs sp) _ _ _ _ _ _ _ hr
    ⟨hR₀ok, hR₀p, (TablesOk.empty fs sp).push ⟨⟨_, _, hx'⟩, (fun _ h' => by cases h'),
      (fun p h' => by cases h'; exact hp), (fun _ h' => by cases h'),
      (fun f' h' => by cases h'; exact hf)⟩⟩

end ConLeche.Driver
