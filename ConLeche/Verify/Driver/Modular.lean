module

public import ConLeche.Driver.Modular
public import ConLeche.Verify.Driver.Tables
public import ConLeche.Verify.Driver.Graph
public import ConLeche.Verify.Driver.CompareModule

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

/-- A node of a graph with imports added, with its header's imports. -/
theorem headerNode_ok {sp : Roots} {fs : FS} {extra : Name → Array ImportRec} {e : Graph.Node}
    (h : Graph.NodeOk sp fs extra e) :
    ModelIO.CanGive (moduleImports sp (headerNode extra e).1) fs (.ok (headerNode extra e).2) := by
  obtain ⟨imps, hi, he⟩ := h
  simp only [headerNode, he, Array.size_append, Nat.add_sub_cancel]
  rw [Array.extract_append_left]
  simpa using hi

/-- **The challenge's closure of a compared run**: none for a run that compares nothing, else the
graph through the challenge's lookup. -/
theorem chalGraph_ok {spC : Roots} {root : Name} {sol : Option Name}
    {why : ModelIO (Option String)} {modeTag : String} {jobs : Nat} {fs : FS} {hs hs' : HS}
    {CC : Array Graph.Node} {RC : Roots}
    (h : (chalGraph spC root sol why modeTag jobs : ModelIO _) fs hs (.ok (.ok (CC, RC))) hs') :
    (sol = none → CC = #[] ∧ RC = spC) ∧
      (sol.isSome → ModelIO.CanGive (Graph.graphOf spC [root] jobs) fs (.ok (CC, RC))) := by
  cases sol with
  | none =>
    simp only [chalGraph, ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨fun _ => ⟨h.1.1, h.1.2⟩, fun h' => absurd h' (by simp)⟩
  | some S =>
    refine ⟨fun h' => absurd h' (by simp), fun _ => ?_⟩
    simp only [chalGraph, ModelIO.bind_ok] at h
    obtain ⟨x, _, hx, h⟩ := h
    rcases x with e | r
    · simp only [ModelIO.bind_ok] at h
      obtain ⟨w, _, -, h⟩ := h
      split at h
      · simp only [diagLine, ModelIO.bind_ok, ModelIO.liftIO_iff, ModelIO.pure_iff] at h
        obtain ⟨_, _, -, h, -⟩ := h
        cases h
      · simp only [diagLine, ModelIO.bind_ok, ModelIO.liftIO_iff, ModelIO.pure_iff] at h
        obtain ⟨_, _, -, h, -⟩ := h
        cases h
    · simp only [ModelIO.pure_iff, Except.ok.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨_, _, hx⟩

/-- **An exit 0 of the one-process mode, in the model**: the closure is the graph check's
accepting outcome, and every module of it is an accepted worker (`WorkerAccepted`, at one job),
whatever the `liftIO` actions answered; with `--compare` (`sol = some S`), the challenge `root`
is an accepting compare worker's (`CmpFacts`) instead, and a module of the challenge's closure
(`CC`, its graph through the challenge's lookup `spC`) an accepted worker through `spC`. -/
theorem checkModularG_accept {spC sp : Roots} (hspC : spC.bare = spC) (hsp : sp.bare = sp)
    (hC : spC.Trims sp) {root : Name} {sol : Option Name} {why : ModelIO (Option String)}
    {mode : CheckMode} {maxNatSize : Nat} {pace : Pace} {jobs : Nat} {fs : FS} {hs hs' : HS}
    (h : (checkModularG spC sp root sol why mode maxNatSize pace jobs : ModelIO _) fs hs
      (.ok 0) hs') :
    ∃ C T, ModelIO.CanGive (Graph.graphOf sp [root] jobs (modExtra root sol)) fs (.ok (C, T)) ∧
      ∃ CC : Array Graph.Node, (sol = none → CC = #[]) ∧
      (sol.isSome → ∃ RC, ModelIO.CanGive (Graph.graphOf spC [root] jobs) fs (.ok (CC, RC))) ∧
      (∀ e ∈ C.toList, (∀ S, sol = some S → e.1 ≠ root) →
        WorkerAccepted mode maxNatSize
          (if (Graph.namesOf CC.toList).contains e.1 = true then spC else sp) fs e.1 1) ∧
      ∀ S, sol = some S → ∃ c, CmpFacts spC sp fs root S 1 c := by
  simp only [checkModularG, clockMs, diagLine, outLine, ModelIO.bind_ok] at h
  obtain ⟨t0, _, -, x, _, hx, h⟩ := h
  rcases x with e | ⟨C, R⟩
  · simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    exact absurd h.symm (CheckError.exitCode_ne_zero _)
  simp only [ModelIO.bind_ok] at h
  obtain ⟨_, _, -, g, _, hg, h⟩ := h
  rcases g with c | ⟨CC, RC⟩
  · -- the challenge's walk failed: its exit code is not 0
    simp only [ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    cases sol with
    | none => simp [chalGraph] at hg
    | some S =>
      simp only [chalGraph, ModelIO.bind_ok] at hg
      obtain ⟨y, _, -, hg⟩ := hg
      rcases y with e | r
      · simp only [ModelIO.bind_ok] at hg
        obtain ⟨w, _, -, hg⟩ := hg
        split at hg
        · simp only [diagLine, ModelIO.bind_ok, ModelIO.liftIO_iff, ModelIO.pure_iff,
            Except.ok.injEq, Except.error.injEq] at hg
          obtain ⟨_, _, -, hg, -⟩ := hg
          cases hg
        · simp only [diagLine, ModelIO.bind_ok, ModelIO.liftIO_iff, ModelIO.pure_iff,
            Except.ok.injEq, Except.error.injEq] at hg
          obtain ⟨_, _, -, hg, -⟩ := hg
          exact absurd hg.symm (CheckError.exitCode_ne_zero _)
      · simp at hg
  obtain ⟨hnone, hsome⟩ := chalGraph_ok hg
  simp only [ModelIO.bind_ok] at h
  obtain ⟨y, _, hy, h⟩ := h
  rcases y with e | ts
  · simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    exact absurd h.symm (CheckError.exitCode_ne_zero _)
  simp only [ModelIO.bind_ok] at h
  obtain ⟨yC, _, hyC, h⟩ := h
  rcases yC with e | tsC
  · simp only [ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    exact absurd h.symm (CheckError.exitCode_ne_zero _)
  obtain ⟨rk, hgood, hroot, -, -, hR, hp⟩ := Graph.graphOf_ok hsp hx
  have hT := tables_ok hR hp (fun e he => by
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    exact headerNode_ok (hgood e₀ he₀)) (mapExcept_both hy).1
  have hrd := modTables_within hR hp hT
  -- the challenge's tables, through its lookup
  have hRC : RC.Ok fs ∧ RC.bare = spC ∧
      TablesOk fs spC (ModTables.ofArray tsC.toArray) := by
    cases hsol : sol with
    | none =>
      obtain ⟨hCC, hRC'⟩ := hnone hsol
      subst hCC
      rw [hRC']
      refine ⟨hspC ▸ Roots.ok_bare fs spC, hspC, ?_⟩
      have := (mapExcept_both hyC).1
      intro t ht
      simp only [ModTables.ofArray, List.mem_toArray] at ht
      obtain ⟨e, he, -⟩ := this t ht
      simp at he
    | some S =>
      obtain ⟨_, _, hgC⟩ := hsome (by simp [hsol])
      obtain ⟨-, hgoodC, -, -, -, hRC, hpC⟩ := Graph.graphOf_ok hspC hgC
      refine ⟨hRC, hpC, tables_ok hRC hpC (fun e he => ?_) (mapExcept_both hyC).1⟩
      obtain ⟨imps, hi, he2⟩ := hgoodC e he
      rw [he2]; simpa using hi
  obtain ⟨hRC, hpC, hTC⟩ := hRC
  have hrdC := modTables_within hRC hpC hTC
  simp only [ModelIO.bind_ok] at h
  obtain ⟨_, _, -, _, _, -, _, _, -, ⟨ss, res⟩, _, hz, h⟩ := h
  rcases res with e | rs
  · exact nomatch e
  have hm := (mapExcept_both (hz : workerMap _ _ _ fs _ (.ok (ss, .ok rs)) _).2).2
  simp only [ModelIO.bind_ok] at h
  obtain ⟨_, _, -, h⟩ := h
  cases hf : rs.find? (·.2 != 0) with
  | none =>
    have hn := hf
    have hstep : ∀ m ∈ C.toList.map (·.1), ∃ hs₁ hs₂, (modularStep RC R
        (ModTables.ofArray tsC.toArray) (ModTables.ofArray ts.toArray)
        (Graph.namesOf CC.toList).contains (sol.map (root, ·)) mode maxNatSize () m :
          ModelIO _) fs hs₁ (.ok ((), .ok (m, 0))) hs₂ := by
      intro m hmem
      obtain ⟨r, hr, _, _, hw⟩ := hm _ hmem
      obtain ⟨s, -, s', hs⟩ := hw
      have hs0 := hs
      simp only [modularStep, ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq,
        Prod.mk.injEq] at hs
      obtain ⟨c, _, -, ⟨-, rfl⟩, -⟩ := hs
      have h0 : c = 0 := by
        have := List.find?_eq_none.1 hn _ hr
        simpa using this
      subst h0
      exact ⟨_, _, hs0⟩
    refine ⟨C, R, ⟨_, _, hx⟩, CC, fun hs => (hnone hs).1,
      fun hs => ⟨RC, hsome hs⟩, fun e he hne => ?_, fun S hS => ?_⟩
    · obtain ⟨hsa, _, hs⟩ := hstep e.1 (List.mem_map_of_mem he)
      simp only [modularStep, ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq,
        Prod.mk.injEq] at hs
      obtain ⟨c, hs₁, hc, ⟨-, -, rfl⟩, -⟩ := hs
      cases hsol : sol with
      | none =>
        have hCC : CC = #[] := (hnone hsol).1
        subst hCC
        have hc' : (checkModuleG (ModTables.ofArray ts.toArray |>.reads R) R e.1 mode maxNatSize
            .off 1 false : ModelIO _) fs hsa (.ok 0) hs₁ := by
          simpa [hsol, stepCode] using hc
        simpa [Graph.namesOf] using checkModuleG_accept hrd hR hp hc'
      | some S =>
        have hne' : (e.1 == root) = false := by simpa using hne S hsol
        by_cases hch : (Graph.namesOf CC.toList).contains e.1 = true
        · have hc' : (checkModuleG (ModTables.ofArray tsC.toArray |>.reads RC) RC e.1 mode
              maxNatSize .off 1 false : ModelIO _) fs hsa (.ok 0) hs₁ := by
            simpa [hsol, hne', hch, stepCode] using hc
          simp only [hch, ↓reduceIte]
          exact checkModuleG_accept hrdC hRC hpC hc'
        · have hc' : (checkModuleG (ModTables.ofArray ts.toArray |>.reads R) R e.1 mode
              maxNatSize .off 1 false : ModelIO _) fs hsa (.ok 0) hs₁ := by
            simpa [hsol, hne', hch, stepCode] using hc
          simp only [hch, Bool.false_eq_true, ↓reduceIte]
          exact checkModuleG_accept hrd hR hp hc'
    · obtain ⟨_, _, hs⟩ := hstep root (hroot root (by simp))
      simp only [modularStep, ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq,
        Prod.mk.injEq] at hs
      obtain ⟨c, _, hc, ⟨-, -, rfl⟩, -⟩ := hs
      simp only [stepCode, hS, Option.map_some, beq_self_eq_true, ↓reduceIte] at hc
      exact checkCmpModuleG_accept hC hrdC hrd hc
  | some mc =>
    obtain ⟨m, c⟩ := mc
    simp only [hf, ModelIO.bind_ok, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨_, _, -, h, -⟩ := h
    have := List.find?_some hf
    simp only [bne_iff_ne, ne_eq] at this
    exact absurd h.symm this

end ConLeche.Driver
