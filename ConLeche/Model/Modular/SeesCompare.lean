module

import ConLeche.Model.Modular.Sees
public import ConLeche.Verify.Driver.SeesMoves
public import ConLeche.Verify.Driver.ComposeCompare
public import ConLeche.Driver.Cli
import ConLeche.Model.Modular.SeesMain
import ConLeche.Verify.Driver.Main
import ConLeche.Verify.Driver.SeesOwn
import ConLeche.Model.Modular.IsModel
import ConLeche.Model.Capstone
import ConLeche.Verify.Driver.Reach

public section

/-!
# The modular theorem over a challenge and its solution (task #619)

An accepted modular comparison of a challenge `C` and its solution `S` (`--check-graph
--compare`, `--olean --module` at every module of the closures of `C` and `S` but `C`, the compare
worker at `C`; or `--olean --modular --compare`) is a run (`Run.ofCompare`) whose module `C` has
`import all S` added to its header, every module read through the trusted path, then the search
path.  The family of `Run.sees_isModel` restricted to the closure of `C` through the trusted
path alone is the theorem's family:

* every module of that closure is a module of the run (`cmp_rank_le`, through `hdrClosure_trims`:
  the trusted path finds a module where the full lookup does);
* its constants through the trusted path are its constants through the full lookup
  (`inModulePart_trims`), so the run's model of the module is a model of them; `C`'s own: its
  records checked, its copies the loaded constants (`own_covers_x`);
* what it sees through the trusted path it sees in the run, with the solution added at `C`
  (`sees_trims`), and the run's family values it as the module it sees it from;
* on a snapshot that agrees with the run's under the trusted path, the closure, the constants and
  what each module sees are the same (`readFiles_iff_of_agree`).
-/

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Frontend ConLeche.Frontend.Olean

universe w

/-- **The family of an accepted compared run, over the challenge's closure through its own
directories** (see the module docstring). -/
theorem compare_sees_isModel (V : Type w) [SetTheory V] {C S : Name}
    {fs : FS} {T D : SearchPath}
    (Cg : List Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ Cg, Graph.NodeOk (⟨C, S, T, D, none⟩ : CmpReq).solRoots fs
      (Graph.cmpExtra C S) e)
    (hC : C ∈ Cg.map (·.1))
    (edges : ∀ e ∈ Cg, ∀ i ∈ e.2, i.module ∈ Cg.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (Cg.map fun e => rk e.1).Nodup)
    (hhdr : ∀ e ∈ Cg, Frontend.Olean.HdrClosure (⟨C, S, T, D, none⟩ : CmpReq).solRoots fs [C, S] e.1)
    (acc : ∀ M ∈ Cg.map (·.1), ∃ jobs, WorkerAccepted
      (⟨C, S, T, D, none⟩ : CmpReq).solRoots fs M jobs (Graph.cmpExtra C S M)) :
    ∀ fs', FS.AgreeUnder (trustedOr T D) fs fs' →
      ∃ model : Name → (Name → List Nat → V),
        (∀ m, InClosure (trustedOr T D : Roots) fs' #[C] m →
          IsModel V (model m) (moduleConstants (trustedOr T D : Roots) fs' m)) ∧
        (∀ m n m', InClosure (trustedOr T D : Roots) fs' #[C] m →
          Sees (trustedOr T D : Roots) fs' m n m' → model m n = model m' n) := by
  let r : CmpReq := ⟨C, S, T, D, none⟩
  have htr : ((trustedOr T D : SearchPath) : Roots).Trims r.solRoots := by
    have := r.chal_trims
    rwa [CmpReq.chalRoots_trustedOr] at this
  have plain := cmp_plain good hC edges hhdr
  obtain ⟨_, w0, -⟩ := acc C hC
  let R := Run.ofCompare C S Cg rk good edges inj plain acc w0
  have hnames : R.names = Cg.map (·.1) := Run.ofCompare_names C S Cg rk good edges inj plain acc _
  obtain ⟨model, hM, hS⟩ := Run.sees_isModel V R (fun _ => rfl)
  intro fs' hag
  have hf := readFiles_iff_of_agree hag
  have hmem : ∀ m, InClosure (trustedOr T D : Roots) fs' #[C] m → m ∈ R.names := by
    intro m hm
    have h1 := inClosure_hdr (inClosure_of_files hf hm)
    have h2 := hdrClosure_mono (roots' := [C, S]) (fun x hx => by simp at hx; simp [hx])
      (hdrClosure_trims htr h1)
    rw [hnames]
    exact (cmp_rank_le good hC edges h2).1
  refine ⟨model, fun m hm => ?_, fun m n m' hm hs => ?_⟩
  · refine (hM m (hmem m hm)).anti fun c hc => ?_
    exact inModulePart_trims htr ((inModulePart_iff hf).2 hc)
  · exact hS m (hmem m hm) n m' (sees_trims htr _ (sees_of_files hf hs))

/-- A level instantiation of a term is `False` only where the term is. -/
theorem inst_false {e : Expr} {ks : List Name} {us : List Level}
    (h : e.instantiateLevelParams ks us = .const falseName []) : e = .const falseName [] := by
  cases e <;> simp_all [Expr.instantiateLevelParams]

/-- **An accepted compared run holds no constant of type `False`** in a module of the challenge's
closure through its own directories: the constant is stored, as itself or as the copy it is, in
its module's own environment of the run, which has a model (`Model.no_constant_of_False`). -/
theorem compare_no_False (V : Type w) [SetTheory V] {C S : Name}
    {fs : FS} {T D : SearchPath}
    (Cg : List Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ Cg, Graph.NodeOk (⟨C, S, T, D, none⟩ : CmpReq).solRoots fs
      (Graph.cmpExtra C S) e)
    (hC : C ∈ Cg.map (·.1))
    (edges : ∀ e ∈ Cg, ∀ i ∈ e.2, i.module ∈ Cg.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (Cg.map fun e => rk e.1).Nodup)
    (hhdr : ∀ e ∈ Cg, Frontend.Olean.HdrClosure (⟨C, S, T, D, none⟩ : CmpReq).solRoots fs [C, S] e.1)
    (acc : ∀ M ∈ Cg.map (·.1), ∃ jobs, WorkerAccepted
      (⟨C, S, T, D, none⟩ : CmpReq).solRoots fs M jobs (Graph.cmpExtra C S M))
    {m : Name} {c : ConstantInfo}
    (hcl : InClosure (trustedOr T D : Roots) fs #[C] m)
    (hc0 : InModulePart (trustedOr T D : Roots) fs m .private c)
    (hty : c.type = .const falseName []) : False := by
  let r : CmpReq := ⟨C, S, T, D, none⟩
  have htr : ((trustedOr T D : SearchPath) : Roots).Trims r.solRoots := by
    have := r.chal_trims
    rwa [CmpReq.chalRoots_trustedOr] at this
  have plain := cmp_plain good hC edges hhdr
  obtain ⟨_, w0, -⟩ := acc C hC
  let R := Run.ofCompare C S Cg rk good edges inj plain acc w0
  have hnames : R.names = Cg.map (·.1) := Run.ofCompare_names C S Cg rk good edges inj plain acc _
  have hmR : m ∈ R.names := by
    have h2 := hdrClosure_mono (roots' := [C, S]) (fun x hx => by simp at hx; simp [hx])
      (hdrClosure_trims htr (inClosure_hdr hcl))
    rw [hnames]
    exact (cmp_rank_le good hC edges h2).1
  have hc : moduleConstants (R.look m) fs m c := inModulePart_trims htr hc0
  let i := R.rk m
  have hok : ∀ j ≤ i, Modular.LocalOk natOpPinSets R.dev j :=
    fun j _ => R.localOk j
  obtain ⟨mm, -⟩ := Model.Modular.modularModels (V := V) (pins := natOpPinSets) hok
  obtain ⟨mp, -⟩ := (mm i (by omega)).2.2.2.2
  have hcty : c.toConstantVal.type = .const falseName [] := hty
  rcases R.own_covers_x hmR hc with ⟨c', hc', hst⟩ | ⟨ci, hci, -, ⟨hst, -⟩ | hren⟩
  · obtain ⟨ci, hf, hst', -⟩ := Model.Modular.own_recordsStored (R.localOk i).importOk c' hc'
    refine Model.no_constant_of_False mp ci (Env.find?_mem hf) ?_
    rw [hst'.1, hst.1, hcty]
  · have hown : ci ∈ (R.dev i).own.consts := by
      show ci ∈ (R.dev (R.rk m)).own.consts
      rw [R.dev_rk hmR]
      exact (ConLeche.Driver.mem_streamEnv_consts _ _).2 (.inr hci)
    refine Model.no_constant_of_False mp ci hown ?_
    rw [hst.1, hcty]
  · have hown : ci ∈ (R.dev i).own.consts := by
      show ci ∈ (R.dev (R.rk m)).own.consts
      rw [R.dev_rk hmR]
      exact (ConLeche.Driver.mem_streamEnv_consts _ _).2 (.inr hci)
    obtain ⟨-, -, -, -, ht, -⟩ := hren
    rw [hcty] at ht
    exact Model.no_constant_of_False mp ci hown (inst_false ht.symm)

/-- **The modular comparison, run by run** (`--check-graph --compare`, a worker at every module of
the closures but the challenge's, the compare worker at the challenge). -/
theorem modular_compare_graph (V : Type w) [SetTheory V] {T D c s : String} {C S : Name}
    {fs : FS} (hc : parseModName c = some C) (hs : parseModName s = some S)
    (hgraph : ModelIO.CanGive (runArgs ["--check-graph", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0)
    (hwork : ∀ m, Frontend.Olean.HdrClosure
        (⟨C, S, searchPathOf T, searchPathOf D, none⟩ : CmpReq).solRoots fs [C, S] m → m ≠ C →
      ∃ root', parseModName root' = some m ∧ ModelIO.CanGive (runArgs ["--olean", "--module",
        "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", root']) fs 0)
    (hcmp : ModelIO.CanGive (runArgs ["--olean", "--module", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0) :
    ∀ fs', FS.AgreeUnder (trustedOr (searchPathOf T) (searchPathOf D)) fs fs' →
      ∃ model : Name → (Name → List Nat → V),
        (∀ m, InClosure (trustedOr (searchPathOf T) (searchPathOf D) : Roots) fs' #[C] m →
          IsModel V (model m)
            (moduleConstants (trustedOr (searchPathOf T) (searchPathOf D) : Roots) fs' m)) ∧
        (∀ m n m', InClosure (trustedOr (searchPathOf T) (searchPathOf D) : Roots) fs' #[C] m →
          Sees (trustedOr (searchPathOf T) (searchPathOf D) : Roots) fs' m n m' →
          model m n = model m' n) := by
  obtain ⟨_, _, hg⟩ := hgraph
  obtain ⟨gj, _, _, hg⟩ := runArgs_graphCmpT_accept hc hs hg
  obtain ⟨Cg, rk, good, hroots, edges, inj, hhdr⟩ :=
    Graph.checkGraphG_ok (CmpReq.solRoots_bare _) (roots' := [C, S])
      (fun r hr => by simp at hr; simp [hr])
      (fun m i hi => by
        unfold Graph.cmpExtra at hi
        split at hi
        · simp [Graph.solutionImport] at hi; simp [hi]
        · simp at hi) hg
  have hC : C ∈ Cg.map (·.1) := hroots C (by simp)
  obtain ⟨_, _, hcm⟩ := hcmp
  obtain ⟨C', S', cj, hc', hs', hcw⟩ := runArgs_cmpModuleT_accept hcm
  obtain rfl : C' = C := Option.some.inj (hc'.symm.trans hc)
  obtain rfl : S' = S := Option.some.inj (hs'.symm.trans hs)
  refine compare_sees_isModel V Cg rk good hC edges inj
    hhdr (fun M hM => ?_)
  by_cases hMC : M = C'
  · subst hMC
    exact ⟨cj, by rw [cmpExtra_self]; exact hcw⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
    obtain ⟨root', hp, _, _, hw⟩ := hwork e.1 (hhdr e he) hMC
    obtain ⟨m', jobs', hp', hacc⟩ := runArgs_moduleT_accept hw
    obtain rfl : m' = e.1 := Option.some.inj (hp'.symm.trans hp)
    exact ⟨jobs', by rw [cmpExtra_other hMC]; exact hacc C' S'⟩

/-- **The modular comparison, in one process** (`--olean --modular --compare`). -/
theorem modular_compare_one (V : Type w) [SetTheory V] {T D c s : String} {C S : Name}
    {fs : FS} (hc : parseModName c = some C) (hs : parseModName s = some S)
    (h : ModelIO.CanGive (runArgs ["--olean", "--modular", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0) :
    ∀ fs', FS.AgreeUnder (trustedOr (searchPathOf T) (searchPathOf D)) fs fs' →
      ∃ model : Name → (Name → List Nat → V),
        (∀ m, InClosure (trustedOr (searchPathOf T) (searchPathOf D) : Roots) fs' #[C] m →
          IsModel V (model m)
            (moduleConstants (trustedOr (searchPathOf T) (searchPathOf D) : Roots) fs' m)) ∧
        (∀ m n m', InClosure (trustedOr (searchPathOf T) (searchPathOf D) : Roots) fs' #[C] m →
          Sees (trustedOr (searchPathOf T) (searchPathOf D) : Roots) fs' m n m' →
          model m n = model m' n) := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨C', S', hc', hs', jobs, Cg, Tg, ⟨_, _, hg⟩, hall⟩ := runArgs_modularCmpT_accept h
  obtain rfl : C' = C := Option.some.inj (hc'.symm.trans hc)
  obtain rfl : S' = S := Option.some.inj (hs'.symm.trans hs)
  obtain ⟨rk, good, hroots, edges, inj, -⟩ := Graph.graphOf_ok (CmpReq.solRoots_bare _) hg
  have hhdr := Graph.graphOf_closure (CmpReq.solRoots_bare _) (roots' := [C', S'])
    (fun r hr => by simp at hr; simp [hr])
    (fun m i hi => by
      unfold Graph.cmpExtra at hi
      split at hi
      · simp [Graph.solutionImport] at hi; simp [hi]
      · simp at hi) hg
  exact compare_sees_isModel V Cg.toList rk good
    (hroots C' (by simp)) edges inj hhdr (fun M hM => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
      exact ⟨1, hall e he⟩)

/-- **No constant of type `False` in an accepted modular comparison, run by run.** -/
theorem modular_compare_graph_no_False (V : Type w) [SetTheory V] {T D c s : String} {C S : Name}
    {fs : FS} (hc : parseModName c = some C) (hs : parseModName s = some S)
    (hgraph : ModelIO.CanGive (runArgs ["--check-graph", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0)
    (hwork : ∀ m, Frontend.Olean.HdrClosure
        (⟨C, S, searchPathOf T, searchPathOf D, none⟩ : CmpReq).solRoots fs [C, S] m → m ≠ C →
      ∃ root', parseModName root' = some m ∧ ModelIO.CanGive (runArgs ["--olean", "--module",
        "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", root']) fs 0)
    (hcmp : ModelIO.CanGive (runArgs ["--olean", "--module", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0)
    {m : Name} {ci : ConstantInfo}
    (hcl : InClosure (trustedOr (searchPathOf T) (searchPathOf D) : Roots) fs #[C] m)
    (hci : InModulePart (trustedOr (searchPathOf T) (searchPathOf D) : Roots) fs m .private ci)
    (hty : ci.type = .const falseName []) : False := by
  obtain ⟨_, _, hg⟩ := hgraph
  obtain ⟨gj, _, _, hg⟩ := runArgs_graphCmpT_accept hc hs hg
  obtain ⟨Cg, rk, good, hroots, edges, inj, hhdr⟩ :=
    Graph.checkGraphG_ok (CmpReq.solRoots_bare _) (roots' := [C, S])
      (fun r hr => by simp at hr; simp [hr])
      (fun m i hi => by
        unfold Graph.cmpExtra at hi
        split at hi
        · simp [Graph.solutionImport] at hi; simp [hi]
        · simp at hi) hg
  have hC : C ∈ Cg.map (·.1) := hroots C (by simp)
  obtain ⟨_, _, hcm⟩ := hcmp
  obtain ⟨C', S', cj, hc', hs', hcw⟩ := runArgs_cmpModuleT_accept hcm
  obtain rfl : C' = C := Option.some.inj (hc'.symm.trans hc)
  obtain rfl : S' = S := Option.some.inj (hs'.symm.trans hs)
  refine compare_no_False V Cg rk good hC edges inj
    hhdr (fun M hM => ?_) hcl hci hty
  by_cases hMC : M = C'
  · subst hMC
    exact ⟨cj, by rw [cmpExtra_self]; exact hcw⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
    obtain ⟨root', hp, _, _, hw⟩ := hwork e.1 (hhdr e he) hMC
    obtain ⟨m', jobs', hp', hacc⟩ := runArgs_moduleT_accept hw
    obtain rfl : m' = e.1 := Option.some.inj (hp'.symm.trans hp)
    exact ⟨jobs', by rw [cmpExtra_other hMC]; exact hacc C' S'⟩

end ConLeche.Driver.Compose
