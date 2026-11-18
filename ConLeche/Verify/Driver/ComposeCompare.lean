module

public import ConLeche.Verify.Driver.Routes
public import ConLeche.Verify.Driver.CompareModule
import ConLeche.Verify.Driver.Groups
import ConLeche.Verify.Driver.Reach

/-!
# The run of a compared closure (task #608)

A challenge `Cn` and its solution `S` checked by `--check-graph --compare`, a `--module` worker at
every module of the closure but `Cn`, and the compare worker at `Cn`, all accepting on one
snapshot, are a run (`Run.ofCompare`) whose module `Cn` has the solution added to its header
(`Graph.cmpExtra`), its context the compare worker's reach and no own record.  Every module of
the run passes the local checks (`Run.localOk`), so the modular theorem applies to the family
over the closures of `Cn` and `S`.

* **No module imports the challenge** (`cmp_plain`): every module of the graph check's closure is
  in the headers' closure of `[Cn, S]`, of rank at most `Cn`'s (`S` an import of `Cn`'s node, the
  ranks decreasing along every import), so an import of `Cn` would rank `Cn` below itself.
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

variable {sp : SearchPath} {fs : FS} {maxNatSize : Nat}

/-- The compared run's added imports: the solution's import at the challenge, none elsewhere. -/
theorem cmpExtra_self (Cn S : Name) : Graph.cmpExtra Cn S Cn = #[Graph.solutionImport S] := by
  simp [Graph.cmpExtra]

theorem cmpExtra_other {Cn S m : Name} (h : m ≠ Cn) : Graph.cmpExtra Cn S m = #[] := by
  simp [Graph.cmpExtra, h]

/-- **Every module of a compared closure ranks at most the challenge.** -/
theorem cmp_rank_le {Cn S : Name} {C : List Graph.Node} {rk : Name → Nat}
    (good : ∀ e ∈ C, Graph.NodeOk sp fs (Graph.cmpExtra Cn S) e)
    (hroot : Cn ∈ C.map (·.1))
    (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1) {m : Name}
    (h : Graph.HdrClosure sp fs [Cn, S] m) : m ∈ C.map (·.1) ∧ rk m ≤ rk Cn := by
  induction h with
  | @root r hr =>
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨hroot, Nat.le_refl _⟩
    · rw [List.mem_singleton] at hr
      subst hr
      obtain ⟨e, he, he1⟩ := List.mem_map.1 hroot
      obtain ⟨imps, -, he2⟩ := good e he
      have hi : Graph.solutionImport r ∈ e.2 := by
        rw [he2, he1, cmpExtra_self]; simp
      have := edges e he _ hi
      rw [he1] at this
      exact ⟨this.1, Nat.le_of_lt this.2⟩
  | @step a is i _ ha hi ih =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ih.1
    obtain ⟨imps, himps, he2⟩ := good e he
    obtain rfl := moduleImports_canGive_unique himps ha
    have hi' : i ∈ e.2 := by rw [he2]; exact Array.mem_append_left _ hi
    have := edges e he i hi'
    exact ⟨this.1, by omega⟩

/-- **No module of a compared closure imports the challenge.** -/
theorem cmp_plain {Cn S : Name} {C : List Graph.Node} {rk : Name → Nat}
    (good : ∀ e ∈ C, Graph.NodeOk sp fs (Graph.cmpExtra Cn S) e)
    (hroot : Cn ∈ C.map (·.1))
    (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1)
    (hhdr : ∀ e ∈ C, Graph.HdrClosure sp fs [Cn, S] e.1) :
    ∀ e ∈ C, ∀ i ∈ e.2, Graph.cmpExtra Cn S i.module = #[] := by
  intro e he i hi
  refine cmpExtra_other fun hm => ?_
  have h1 := (edges e he i hi).2
  have h2 := (cmp_rank_le good hroot edges (hhdr e he)).2
  rw [hm] at h1
  omega

open Classical in
/-- **The run of a compared closure** (see the module docstring); `dflt` the read of a name
outside the closure. -/
noncomputable def Run.ofCompare (Cn S : Name) (C : List Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ C, Graph.NodeOk sp fs (Graph.cmpExtra Cn S) e)
    (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (C.map fun e => rk e.1).Nodup)
    (plain : ∀ e ∈ C, ∀ i ∈ e.2, Graph.cmpExtra Cn S i.module = #[])
    (acc : ∀ M ∈ C.map (·.1), M ≠ Cn → ∃ jobs, WorkerAccepted .verified maxNatSize sp fs M jobs)
    (cjobs : Nat) (cr : CmpModuleRead) (hcr : CmpFacts sp fs Cn S cjobs cr) (dflt : WorkerRead) :
    Run sp fs maxNatSize where
  C := C
  rk := rk
  x := Graph.cmpExtra Cn S
  good := good
  edges := edges
  inj := inj
  plain := plain
  w M := if hM : M ∈ C.map (·.1) ∧ M ≠ Cn then (acc M hM.1 hM.2).choose_spec.choose
    else if M = Cn then cr.w else dflt
  jobs M := if hM : M ∈ C.map (·.1) ∧ M ≠ Cn then (acc M hM.1 hM.2).choose else cjobs
  facts M hM := by
    by_cases hc : M = Cn
    · subst hc
      simp only [ne_eq, not_true_eq_false, and_false, ↓reduceDIte, ↓reduceIte]
      rw [cmpExtra_self]
      exact hcr.facts
    · have hm : M ∈ C.map (·.1) ∧ M ≠ Cn := ⟨hM, hc⟩
      rw [dite_eq_left hm, dite_eq_left hm, cmpExtra_other hc]
      exact (acc M hM hc).choose_spec.choose_spec.1
  run M hM := by
    by_cases hc : M = Cn
    · subst hc
      simp only [ne_eq, not_true_eq_false, and_false, ↓reduceDIte, ↓reduceIte, ownDecls]
      have hown : cr.w.own = #[] := by
        rw [hcr.facts.own, recsOf]
        simp
      simp only [hown, Array.toList_empty, List.map_nil, Array.size_empty, Nat.add_zero]
      exact .nil _
    · have hm : M ∈ C.map (·.1) ∧ M ≠ Cn := ⟨hM, hc⟩
      rw [dite_eq_left hm]
      exact (acc M hM hc).choose_spec.choose_spec.2

/-- The compared run's module at the challenge is the compare worker's read. -/
theorem Run.ofCompare_w (Cn S : Name) (C : List Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ C, Graph.NodeOk sp fs (Graph.cmpExtra Cn S) e)
    (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (C.map fun e => rk e.1).Nodup)
    (plain : ∀ e ∈ C, ∀ i ∈ e.2, Graph.cmpExtra Cn S i.module = #[])
    (acc : ∀ M ∈ C.map (·.1), M ≠ Cn → ∃ jobs, WorkerAccepted .verified maxNatSize sp fs M jobs)
    (cjobs : Nat) (cr : CmpModuleRead) (hcr : CmpFacts sp fs Cn S cjobs cr) (dflt : WorkerRead) :
    (Run.ofCompare Cn S C rk good edges inj plain acc cjobs cr hcr dflt).w Cn = cr.w := by
  classical
  show (if hM : Cn ∈ C.map (·.1) ∧ Cn ≠ Cn then _ else if Cn = Cn then cr.w else dflt) = cr.w
  simp

/-! ## Homes and the compared module's environment -/

/-- **The home of a context name** in a reach: the home of the first record storing it (what
`Run.homeIn` reads off a worker's reach). -/
@[expose] def ctxHome (r : Reach) (n : Name) : Name :=
  ((r.ctx.toList.findIdx? fun d => (declNames d).contains n).bind fun k => r.homes[k]?).getD
    .anonymous

namespace Run

variable (R : Run sp fs maxNatSize)

theorem homeIn_eq (M n : Name) : R.homeIn M n = ctxHome (R.w M).reach n := rfl

/-- **A context name's home is a module of the run**, of smaller rank, with no import added. -/
theorem ctx_home {M : Name} (hM : M ∈ R.names) {n : Name}
    (hn : ((streamEnv (R.w M).reach.ctx.toList).find? n).isSome = true) :
    R.homeIn M n ∈ R.names ∧ R.rk (R.homeIn M n) < R.rk M ∧ R.x (R.homeIn M n) = #[] := by
  obtain ⟨d, hdm, hnd⟩ := streamEnv_find_mem hn
  obtain ⟨i, h, hi, hh⟩ := worker_home (R.facts M hM) hdm
  rw [R.homeIn_spec hM hi hh hnd]
  exact R.home_rank hM hh

/-- **The home of a name, by the owner map** (the compare worker's lookup). -/
theorem homeIn_owner {M : Name} (hM : M ∈ R.names) {y : Name} {k : Nat}
    (hk : (ownerMap (R.w M).reach.ctx)[y]? = some k) :
    R.homeIn M y = (R.w M).reach.homes.getD k .anonymous := by
  obtain ⟨hlt, hy⟩ := ownerMap_spec hk
  obtain ⟨-, -, -, hsz, -⟩ := R.capture hM
  have hlt' : k < (R.w M).reach.homes.size := by rw [← hsz]; exact hlt
  have hd : (R.w M).reach.ctx[k]? = some ((R.w M).reach.ctx.getD k default) := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
  have hh : (R.w M).reach.homes[k]? = some ((R.w M).reach.homes.getD k .anonymous) := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt']
  exact R.homeIn_spec hM hd hh hy

/-- **A module's own environment is its worker's** (`ownEnvOf`). -/
theorem dev_own {M : Name} (hM : M ∈ R.names) :
    (R.dev (R.rk M)).own = ownEnvOf sp fs M (R.w M) := by
  rw [R.dev_rk hM]; rfl

/-- **A module with no own record**: its own environment is its context. -/
theorem ownEnv_noOwn {M : Name} (h : (R.w M).own = #[]) :
    ownEnvOf sp fs M (R.w M) = streamEnv (R.w M).reach.ctx.toList := by
  simp [ownEnvOf, ownDeclsOf, h, streamEnv]

end Run

end ConLeche.Driver.Compose
