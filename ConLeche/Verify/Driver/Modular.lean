module

public import ConLeche.Driver.Modular
public import ConLeche.Verify.Driver.Worker
import ConLeche.Verify.Driver.Graph

/-!
# The one-process mode, in the model

What an exit 0 of the one-process mode at a root (`checkModularG`,
`ConLeche/Driver/Modular.lean`) establishes on a snapshot:

* `modTables_within` — **the tables' reads refine the search path's**: every table was read off
  the snapshot (`TablesOk`: the module's location is `findModule`'s answer, its imports
  `moduleImports`', its two parts' name positions `readPartNamesAt`'s at that location), so each
  of the three reads answered from them is one of the search path's (`OleanReads.Within`);
* `checkModularG_accept` — **every module of the closure is an accepted worker**: the closure
  is the graph check's (`graphOf`, whose accepting outcome gives `checkGraphG_ok`'s facts,
  `graphOf_ok`), and at every module of it, `WorkerAccepted` at one job: the per-module facts
  an exit 0 of `--module` at that module gives (`checkModuleG_accept`), the same steps run over
  the tables.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-- **The sequential map's accepting outcome, element by element**: each result is an element's,
and each element has one among the results. -/
theorem mapExcept_both {α β ε : Type} {f : α → ModelIO (Except ε β)} {fs : FS} :
    ∀ {xs : List α} {ys : List β} {hs hs' : HS},
      (mapExcept f xs : ModelIO _) fs hs (.ok (.ok ys)) hs' →
      (∀ y ∈ ys, ∃ x ∈ xs, ModelIO.CanGive (f x) fs (.ok y)) ∧
        (∀ x ∈ xs, ∃ y ∈ ys, ModelIO.CanGive (f x) fs (.ok y))
  | [], ys, _, _, h => by
    simp only [mapExcept, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    subst h; simp
  | a :: xs, ys, _, _, h => by
    simp only [mapExcept, ModelIO.bind_ok] at h
    obtain ⟨u, _, hu, h⟩ := h
    rcases u with e | b
    · simp at h
    simp only [ModelIO.bind_ok] at h
    obtain ⟨v, _, hv, h⟩ := h
    rcases v with e | bs
    · simp at h
    simp only [ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    subst h
    obtain ⟨h1, h2⟩ := mapExcept_both hv
    refine ⟨fun y hy => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨a, List.mem_cons_self .., _, _, hu⟩
      · obtain ⟨x, hx, h⟩ := h1 y hy
        exact ⟨x, List.mem_cons_of_mem _ hx, h⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨b, List.mem_cons_self .., _, _, hu⟩
      · obtain ⟨y, hy, h⟩ := h2 x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

/-! ## The tables -/

/-- **Tables read off the snapshot.** -/
def TablesOk (fs : FS) (sp : SearchPath) (T : ModTables) : Prop :=
  ∀ t ∈ T.mods, ModelIO.CanGive (findModule sp t.name) fs (.ok t.loc) ∧
    ModelIO.CanGive (moduleImports sp t.name) fs (.ok t.imports) ∧
    ModelIO.CanGive (readPartNamesAt t.loc (t.name, .private)) fs (.ok t.priv) ∧
    ModelIO.CanGive (readPartNamesAt t.loc (t.name, .exported)) fs (.ok t.expo)

theorem readModTable_ok {sp : SearchPath} {fs : FS} {e : Graph.Node} {t : ModTable} {hs hs' : HS}
    (h : (readModTable sp e : ModelIO _) fs hs (.ok (.ok t)) hs') :
    t.name = e.1 ∧ t.imports = e.2 ∧ ModelIO.CanGive (findModule sp e.1) fs (.ok t.loc) ∧
    ModelIO.CanGive (readPartNamesAt t.loc (e.1, .private)) fs (.ok t.priv) ∧
    ModelIO.CanGive (readPartNamesAt t.loc (e.1, .exported)) fs (.ok t.expo) := by
  simp only [readModTable, ModelIO.bind_ok] at h
  obtain ⟨x, hs₁, hx, h⟩ := h
  rcases x with err | loc
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨y, hs₂, hy, h⟩ := h
  rcases y with err | priv
  · simp at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨z, hs₃, hz, h⟩ := h
  rcases z with err | expo
  · simp at h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨h, -⟩ := h
  subst h
  exact ⟨rfl, rfl, ⟨_, _, hx⟩, ⟨_, _, hy⟩, ⟨_, _, hz⟩⟩

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
theorem ModelIO.Within.at_loc {α : Type} {fs : FS} {sp : SearchPath} {m : Name} {loc : Located}
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

/-- **The tables' reads refine the search path's.** -/
theorem modTables_within {fs : FS} {sp : SearchPath} {T : ModTables} (hT : TablesOk fs sp T) :
    OleanReads.Within fs (T.reads sp) sp := by
  refine ⟨fun m => ?_, fun m level => ?_, fun x => ?_⟩
  · simp only [ModTables.reads]
    split
    · rename_i t ht
      obtain ⟨hm, rfl⟩ := ModTables.find_mem ht
      exact ModelIO.Within.of_table (moduleImports_within fs sp _) (hT t hm).2.1
    · exact moduleImports_within fs sp m
  · simp only [ModTables.reads]
    split
    · rename_i t ht
      obtain ⟨hm, rfl⟩ := ModTables.find_mem ht
      exact ModelIO.Within.at_loc (a := fun loc => readFilesAt loc t.name level) (hT t hm).1
        (readFilesAt_within fs _ _ _)
    · exact readFiles_within fs sp m level
  · obtain ⟨n, level⟩ := x
    simp only [ModTables.reads]
    split
    · rename_i t ht
      obtain ⟨hm, rfl⟩ := ModTables.find_mem ht
      have hf := (hT t hm).1
      have hat : ∀ level, ModelIO.Within fs (readPartNamesAt t.loc (t.name, level))
          (readPartNames sp (t.name, level)) := fun level =>
        ModelIO.Within.at_loc (a := fun loc => readPartNamesAt loc (t.name, level)) hf (by
          simp only [readPartNamesAt]
          exact ModelIO.Within.bind (readFilesAt_within fs _ _ _) fun r => by
            rcases r with e | f
            · exact ModelIO.Within.pure _
            · simp only
              split <;> exact ModelIO.Within.pure _)
      cases level with
      | «private» =>
        exact ModelIO.Within.of_table (readPartNames_within fs sp _)
          ((hat .private).canGive (hT t hm).2.2.1)
      | exported =>
        exact ModelIO.Within.of_table (readPartNames_within fs sp _)
          ((hat .exported).canGive (hT t hm).2.2.2)
      | server => exact hat .server
    · exact readPartNames_within fs sp (n, level)

/-- The tables of the graph's modules, read off the snapshot. -/
theorem tables_ok {sp : SearchPath} {fs : FS} {C : List Graph.Node} {ts : List ModTable}
    (hC : ∀ e ∈ C, ModelIO.CanGive (moduleImports sp e.1) fs (.ok e.2))
    (h : ∀ t ∈ ts, ∃ e ∈ C, ModelIO.CanGive (readModTable sp e) fs (.ok t)) :
    TablesOk fs sp (ModTables.ofArray ts.toArray) := by
  intro t ht
  simp only [ModTables.ofArray, List.mem_toArray] at ht
  obtain ⟨e, he, _, _, hr⟩ := h t ht
  obtain ⟨hn, hi, h1, h2, h3⟩ := readModTable_ok hr
  rw [hn, hi]
  exact ⟨h1, hC e he, h2, h3⟩

/-! ## The run -/

/-- **An exit 0 of the one-process mode, in the model**: the closure is the graph check's
accepting outcome, and every module of it is an accepted worker (`WorkerAccepted`, at one job),
whatever the `liftIO` actions answered. -/
theorem checkModularG_accept {sp : SearchPath} {root : Name} {mode : CheckMode} {pace : Pace}
    {jobs : Nat} {fs : FS} {hs hs' : HS}
    (h : (checkModularG sp root mode pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ C, ModelIO.CanGive (Graph.graphOf sp [root] jobs) fs (.ok C) ∧
      ∀ e ∈ C.toList, WorkerAccepted mode sp fs e.1 1 := by
  simp only [checkModularG, clockMs, diagLine, outLine, ModelIO.bind_ok] at h
  obtain ⟨t0, _, -, x, _, hx, h⟩ := h
  rcases x with e | C
  · simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    exact absurd h.symm (CheckError.exitCode_ne_zero _)
  simp only [ModelIO.bind_ok] at h
  obtain ⟨_, _, -, y, _, hy, h⟩ := h
  rcases y with e | ts
  · simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    exact absurd h.symm (CheckError.exitCode_ne_zero _)
  obtain ⟨rk, hgood, -, -, -⟩ := Graph.graphOf_ok hx
  have hT := tables_ok hgood (mapExcept_both hy).1
  simp only [ModelIO.bind_ok] at h
  obtain ⟨_, _, -, _, _, -, ⟨ss, res⟩, _, hz, h⟩ := h
  rcases res with e | rs
  · exact nomatch e
  have hm := (mapExcept_both (hz : workerMap _ _ _ fs _ (.ok (ss, .ok rs)) _).2).2
  simp only [ModelIO.bind_ok] at h
  obtain ⟨_, _, -, h⟩ := h
  cases hf : rs.find? (·.2 != 0) with
  | none =>
    have hn := hf
    refine ⟨C, ⟨_, _, hx⟩, fun e he => ?_⟩
    have hmem : e.1 ∈ C.toList.map (·.1) := List.mem_map_of_mem he
    obtain ⟨r, hr, _, _, hw⟩ := hm _ hmem
    obtain ⟨s, -, s', hs⟩ := hw
    simp only [modularStep, ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq,
      Prod.mk.injEq] at hs
    obtain ⟨c, _, hc, ⟨-, rfl⟩, -⟩ := hs
    have h0 : c = 0 := by
      have := List.find?_eq_none.1 hn _ hr
      simpa using this
    subst h0
    exact checkModuleG_accept (modTables_within hT) hc
  | some mc =>
    obtain ⟨m, c⟩ := mc
    simp only [hf, ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    have := List.find?_some hf
    simp only [bne_iff_ne, ne_eq] at this
    exact absurd h.symm this

end ConLeche.Driver
