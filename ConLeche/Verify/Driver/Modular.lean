module

public import ConLeche.Driver.Modular
public import ConLeche.Verify.Driver.Worker
public import ConLeche.Verify.Driver.Tables
import ConLeche.Verify.Driver.Graph

/-!
# The one-process mode, in the model

What an exit 0 of the one-process mode at a root (`checkModularG`,
`ConLeche/Driver/Modular.lean`) establishes on a snapshot:

* `tables_ok` — **the tables are read off the snapshot** (`TablesOk`, so that their reads refine
  the search path's, `modTables_within`, `ConLeche/Verify/Driver/Tables.lean`): each module's
  location is `findModule`'s answer, its imports the graph's, its two parts' name positions
  `readPartNamesAt`'s at that location;
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

theorem readModTable_ok {sp : Roots} {fs : FS} {e : Graph.Node} {t : ModTable} {hs hs' : HS}
    (h : (readModTable sp e : ModelIO _) fs hs (.ok (.ok t)) hs') :
    t.name = e.1 ∧ t.imports = some e.2 ∧ ModelIO.CanGive (findModule sp e.1) fs (.ok t.loc) ∧
    (∀ p, t.priv = some p → ModelIO.CanGive (readPartNamesAt t.loc (e.1, .private)) fs (.ok p)) ∧
    (∀ p, t.expo = some p → ModelIO.CanGive (readPartNamesAt t.loc (e.1, .exported)) fs (.ok p)) ∧
    t.files = none := by
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
  exact ⟨rfl, rfl, ⟨_, _, hx⟩, (fun p h => by cases h; exact ⟨_, _, hy⟩),
    (fun p h => by cases h; exact ⟨_, _, hz⟩), rfl⟩

/-- The tables of the graph's modules, read off the snapshot. -/
theorem tables_ok {sp : Roots} {R : Roots} {fs : FS} {C : List Graph.Node}
    {ts : List ModTable} (hR : R.Ok fs) (hp : R.bare = sp)
    (hC : ∀ e ∈ C, ModelIO.CanGive (moduleImports sp e.1) fs (.ok e.2))
    (h : ∀ t ∈ ts, ∃ e ∈ C, ModelIO.CanGive (readModTable R e) fs (.ok t)) :
    TablesOk fs sp (ModTables.ofArray ts.toArray) := by
  intro t ht
  simp only [ModTables.ofArray, List.mem_toArray] at ht
  obtain ⟨e, he, _, _, hr⟩ := h t ht
  obtain ⟨hn, hi, h1, h2, h3, h4⟩ := readModTable_ok hr
  rw [hn]
  exact ⟨(hp ▸ findModule_sub hR _ : ModelIO.Sub fs _ (findModule (sp : Roots) _)).canGive h1, (fun is h => by rw [hi] at h; cases h; exact hC e he),
    h2, h3, fun f h => by rw [h4] at h; cases h⟩

/-! ## The run -/

/-- **An exit 0 of the one-process mode, in the model**: the closure is the graph check's
accepting outcome, and every module of it is an accepted worker (`WorkerAccepted`, at one job),
whatever the `liftIO` actions answered. -/
theorem checkModularG_accept {sp : Roots} (hsp : sp.bare = sp) {root : Name} {mode : CheckMode} {maxNatSize : Nat} {pace : Pace}
    {jobs : Nat} {fs : FS} {hs hs' : HS}
    (h : (checkModularG sp root mode maxNatSize pace jobs : ModelIO _) fs hs (.ok 0) hs') :
    ∃ C T, ModelIO.CanGive (Graph.graphOf sp [root] jobs) fs (.ok (C, T)) ∧
      ∀ e ∈ C.toList, WorkerAccepted mode maxNatSize sp fs e.1 1 := by
  simp only [checkModularG, clockMs, diagLine, outLine, ModelIO.bind_ok] at h
  obtain ⟨t0, _, -, x, _, hx, h⟩ := h
  rcases x with e | ⟨C, R⟩
  · simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    exact absurd h.symm (CheckError.exitCode_ne_zero _)
  simp only [ModelIO.bind_ok] at h
  obtain ⟨_, _, -, y, _, hy, h⟩ := h
  rcases y with e | ts
  · simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    exact absurd h.symm (CheckError.exitCode_ne_zero _)
  obtain ⟨rk, hgood, -, -, -, hR, hp⟩ := Graph.graphOf_ok hsp hx
  have hT := tables_ok hR hp (fun e he => (hgood e he).plain) (mapExcept_both hy).1
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
    refine ⟨C, R, ⟨_, _, hx⟩, fun e he => ?_⟩
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
    exact checkModuleG_accept (modTables_within hR hp hT) hR hp hc
  | some mc =>
    obtain ⟨m, c⟩ := mc
    simp only [hf, ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    have := List.find?_some hf
    simp only [bne_iff_ne, ne_eq] at this
    exact absurd h.symm this

end ConLeche.Driver
