module

public import ConLeche.Model.Modular.Sees
public import ConLeche.Driver.Cli
import ConLeche.Verify.Driver.Main
import ConLeche.Verify.Driver.Graph

public section

/-!
# The modular theorem over what each module sees, at the driver (task #618)

Every exit 0 of `--check-graph` together with exits 0 of `--olean --module` for every module of
the headers' closure, and every exit 0 of the one-process `--olean --modular`, is an accepted run
over a closure (`Driver.Compose.Run.ofAccepted`); the closure of the specification
(`Olean.InClosure`, over the private views) is inside it, so `Run.sees_isModel` gives the family.
-/

namespace ConLeche.Driver.Compose

variable {pins : List NatOpPinSet}

open ConLeche ConLeche.Frontend ConLeche.Frontend.Olean

universe w

/-- **The closure of the specification is inside the headers' closure.** -/
theorem inClosure_hdr {sp : Roots} {fs : FS} {roots : Array Name} {m : Name}
    (h : InClosure sp fs roots m) : Frontend.Olean.HdrClosure sp fs roots.toList m := by
  induction h with
  | root hr => exact .root (Array.mem_toList_iff.2 hr)
  | @step m d i _ hv hi ih =>
    obtain ⟨_, _, hrv⟩ := readView_of_viewOf hv
    exact .step ih (moduleImports_of_view hrv).canGive hi

/-- **What a module of a closure loads is in the closure.** -/
theorem loadsAt_inClosure {sp : Roots} {fs : FS} {roots : Array Name} {M : Name} {d : ModDecoded}
    (hM : InClosure sp fs roots M) (hv : ViewOf sp fs M d) {g : Bool} {m : Name} {b : Bool}
    (h : LoadsAt sp fs g d.imports m b) : InClosure sp fs roots m := by
  induction h with
  | root hi => exact .step hM hv hi
  | step _ hva hi _ ih => exact .step ih hva hi

/-- **What a module of a closure sees is in the closure.** -/
theorem sees_inClosure {sp : Roots} {fs : FS} {roots : Array Name} {M n m' : Name}
    (hM : InClosure sp fs roots M) (h : Sees sp fs M n m') : InClosure sp fs roots m' := by
  obtain ⟨p, -, ⟨d, hv, hl⟩, -, -⟩ := h
  cases p with
  | «private» => exact loadsAt_inClosure hM hv hl
  | exported => exact loadsAt_inClosure hM hv hl.1
  | server => exact hl.elim

/-- **A theorem of a module's private view is a constant of the module.** -/
theorem moduleConstants_thm {sp : Roots} {fs : FS} {m : Name} {d : ModDecoded}
    {c : CEntryF Name Expr} {v : Expr} {all : List Name} (hv : ViewOf sp fs m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all) :
    moduleConstants sp fs m (.thmInfo c.cv) := by
  obtain ⟨f, hf, hd⟩ := hv
  refine ⟨f, d, c, hf, hd, hmem, ?_⟩
  rcases c with ⟨n, l, t, k⟩
  simp only at hk
  subst hk
  simp [entryConstants, declOfEntry, Declaration.constants]

/-- **The family at an accepted closure** (`Run.sees_isModel`), over the specification's closure
of a module of it. -/
theorem closure_sees_isModel (V : Type w) [SetTheory V] {sp : Roots} {fs : FS}
    (C : List Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ C, ModelIO.CanGive (moduleImports sp e.1) fs (.ok e.2))
    (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (C.map fun e => rk e.1).Nodup)
    (acc : ∀ M ∈ C.map (·.1), ∃ jobs, WorkerAccepted pins sp fs M jobs)
    {r : Name} (hr : r ∈ C.map (·.1)) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ m, InClosure sp fs #[r] m → IsModel V (model m) (moduleConstants sp fs m)) ∧
      (∀ m n m', InClosure sp fs #[r] m → Sees sp fs m n m' → model m n = model m' n) := by
  obtain ⟨_, w, -⟩ := acc r hr
  let R := Run.ofAccepted C rk good edges inj acc w
  have hnames : R.names = C.map (·.1) := Run.ofAccepted_names C rk good edges inj acc w
  obtain ⟨model, hM, hS⟩ := Run.sees_isModel V R
    (Run.ofAccepted_look C rk good edges inj acc w)
  have hmem : ∀ m, InClosure sp fs #[r] m → m ∈ R.names := fun m hm => by
    rw [hnames]
    refine hdrClosure_mem good (fun r' hr' => ?_) (fun e he i hi => (edges e he i hi).1)
      (inClosure_hdr hm)
    simp only [List.mem_singleton] at hr'
    rw [hr']; exact hr
  exact ⟨model, fun m hm => hM m (hmem m hm), fun m n m' hm hs =>
    hS m (hmem m hm) n m' (sees_toX _ hs)⟩

/-- **The modular theorem over what each module sees, run by run** (`--check-graph` and a worker
for every module of the headers' closure). -/
theorem modular_sees_graph (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : parseModName root = some r)
    (h : ModelIO.CanGive (runArgs ["--check-graph", "--search-path=" ++ dirs, "--", root]) fs 0)
    (hwork : ∀ m', Frontend.Olean.HdrClosure (searchPathOf dirs) fs [r] m' → ∃ root',
      parseModName root' = some m' ∧ ModelIO.CanGive
        (runArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root']) fs 0) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ m, InClosure (searchPathOf dirs) fs #[r] m →
        IsModel V (model m) (moduleConstants (searchPathOf dirs) fs m)) ∧
      (∀ m n m', InClosure (searchPathOf dirs) fs #[r] m → Sees (searchPathOf dirs) fs m n m' →
        model m n = model m' n) := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨jobs, _, _, hg⟩ := runArgs_graph_accept hr h
  obtain ⟨C, rk, good, hroots, edges, inj, hhdr⟩ :=
    Graph.checkGraphG_ok rfl (fun _ h => h) (fun _ _ h => by simp at h) hg
  replace good := fun e he => (good e he).plain
  refine closure_sees_isModel V (pins := natOpPinSets) C rk good edges inj
    (fun M hM => ?_) (hroots r List.mem_cons_self)
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  obtain ⟨root', hp, _, _, hw⟩ := hwork e.1 (hhdr e he)
  obtain ⟨m', jobs', hp', hacc⟩ := runArgs_module_accept hw
  obtain rfl : m' = e.1 := Option.some.inj (hp'.symm.trans hp)
  exact ⟨jobs', hacc⟩

/-- **The modular theorem over what each module sees, in one process** (`--olean --modular`). -/
theorem modular_sees_one (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : parseModName root = some r)
    (h : ModelIO.CanGive
      (runArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root]) fs 0) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ m, InClosure (searchPathOf dirs) fs #[r] m →
        IsModel V (model m) (moduleConstants (searchPathOf dirs) fs m)) ∧
      (∀ m n m', InClosure (searchPathOf dirs) fs #[r] m → Sees (searchPathOf dirs) fs m n m' →
        model m n = model m' n) := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨m₀, hp, C, rk, good, hm₀, edges, inj, hacc⟩ := runArgs_modular_accept h
  obtain rfl : m₀ = r := Option.some.inj (hp.symm.trans hr)
  exact closure_sees_isModel V (pins := natOpPinSets) C rk good edges inj
    (fun M hM => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
      exact ⟨1, hacc e he⟩) hm₀

end ConLeche.Driver.Compose
