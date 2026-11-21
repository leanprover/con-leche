module

public import ConLeche.Verify.Driver.Routes
import ConLeche.Verify.Driver.Groups
import ConLeche.Verify.Driver.Reach

/-!
# The run of a compared closure (task #608)

A challenge `Cn` and its solution `S` checked by `--check-graph --compare`, a `--module` worker at
every module of the closure but `Cn`, and the compare worker at `Cn`, all accepting on one
snapshot and reading through one lookup, are a run (`Run.ofCompare`) whose module `Cn` has the
solution added to its header (`Graph.cmpExtra`, task #619): its context the compare worker's
reach, its own records those of `Cn` no loaded module stores.  Every module of the run passes the
local checks (`Run.localOk`), so the modular theorem applies to the family over the closures of
`Cn` and `S`.

* **No module imports the challenge** (`cmp_plain`): every module of the graph check's closure is
  in the headers' closure of `[Cn, S]`, of rank at most `Cn`'s (`S` an import of `Cn`'s node, the
  ranks decreasing along every import), so an import of `Cn` would rank `Cn` below itself.
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

variable {sp : Roots} {fs : FS} {maxNatSize : Nat}

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
    (h : Frontend.Olean.HdrClosure sp fs [Cn, S] m) : m ∈ C.map (·.1) ∧ rk m ≤ rk Cn := by
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
    (hhdr : ∀ e ∈ C, Frontend.Olean.HdrClosure sp fs [Cn, S] e.1) :
    ∀ e ∈ C, ∀ i ∈ e.2, Graph.cmpExtra Cn S i.module = #[] := by
  intro e he i hi
  refine cmpExtra_other fun hm => ?_
  have h1 := (edges e he i hi).2
  have h2 := (cmp_rank_le good hroot edges (hhdr e he)).2
  rw [hm] at h1
  omega

open Classical in
/-- **The run of a compared closure** (see the module docstring), every module read through one
lookup; `dflt` the read of a name outside the closure. -/
@[expose] noncomputable def Run.ofCompare (Cn S : Name) (C : List Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ C, Graph.NodeOk sp fs (Graph.cmpExtra Cn S) e)
    (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (C.map fun e => rk e.1).Nodup)
    (plain : ∀ e ∈ C, ∀ i ∈ e.2, Graph.cmpExtra Cn S i.module = #[])
    (acc : ∀ M ∈ C.map (·.1), ∃ jobs,
      WorkerAccepted .verified maxNatSize sp fs M jobs (Graph.cmpExtra Cn S M))
    (dflt : WorkerRead) :
    Run sp fs maxNatSize where
  C := C
  rk := rk
  x := Graph.cmpExtra Cn S
  good := good
  edges := edges
  inj := inj
  plain := plain
  look := fun _ => sp
  trims := fun _ => Roots.Trims.refl sp
  w M := if hM : M ∈ C.map (·.1) then (acc M hM).choose_spec.choose else dflt
  jobs M := if hM : M ∈ C.map (·.1) then (acc M hM).choose else 0
  facts M hM := by simp only [hM, ↓reduceDIte]; exact (acc M hM).choose_spec.choose_spec.1
  run M hM := by simp only [hM, ↓reduceDIte]; exact (acc M hM).choose_spec.choose_spec.2

/-- The compared run's modules are the graph's. -/
theorem Run.ofCompare_names (Cn S : Name) (C : List Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ C, Graph.NodeOk sp fs (Graph.cmpExtra Cn S) e)
    (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (C.map fun e => rk e.1).Nodup)
    (plain : ∀ e ∈ C, ∀ i ∈ e.2, Graph.cmpExtra Cn S i.module = #[])
    (acc : ∀ M ∈ C.map (·.1), ∃ jobs,
      WorkerAccepted .verified maxNatSize sp fs M jobs (Graph.cmpExtra Cn S M))
    (dflt : WorkerRead) :
    (Run.ofCompare Cn S C rk good edges inj plain acc dflt).names = C.map (·.1) := rfl

end ConLeche.Driver.Compose
