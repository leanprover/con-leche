module

public import ConLeche.Verify.Driver.Worker
public import ConLeche.Verify.Driver.Groups
public import ConLeche.Verify.Driver.Graph
import ConLeche.Verify.Driver.Reach
public import ConLeche.Verify.Driver.Loads
public import ConLeche.Verify.Driver.Capture
public import ConLeche.Verify.Driver.Clashes
public import ConLeche.Verify.Driver.Copies
public import ConLeche.Verify.Driver.PropPart
import ConLeche.Verify.Cached.Fill

/-!
# The composition: a development from an accepted run

An accepted run over a closure (`--check-graph` and a worker for every module of the closure on
one snapshot, or the one-process `--modular` run) is a development of modules
(`ConLeche/Modular.lean`) every module of which passes the local checks (`LocalOk`), so the
modular theorem applies to it.

* **The run** (`Run`): the graph check's closure `C` with its ranks `rk` (one-to-one on `C`,
  decreasing along every import), and for every module of `C` an accepted worker on the
  snapshot (`WorkerFacts` and the own records' accepted run).
* **The development** (`Run.dev`): module `j` is the module of `C` of rank `j`, empty if there is
  none.  Its context is its worker's sorted context, its own records the worker's own records with
  the theorems' values in place, a context name is read from the rank of the home of the record
  storing it (`Run.homeIn`), and it presents every context record any worker of the run read with
  it as the home (`Run.ifaceOf`).  It imports nothing: only `ImportOk.below` reads the imports,
  and the order the development needs is the sources' (`src_lt`).
* **What needs no capture fact** (`Run.localOk_of`): `InterfaceOk` (`interfaceOk_of_workers`),
  and of `ImportOk` everything the module's own worker gives (`worker_local`) and `presented`,
  given that every home of a context record is a module of `C` of smaller rank.  What a context
  record reads, and how it agrees (`ImportOk.reads`), is the capture check's.
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

/-- **A module's own records, with the theorems' values in place.** -/
@[expose] noncomputable def ownDecls (sp : SearchPath) (fs : FS) (M : Name) (w : WorkerRead) :
    List Declaration :=
  w.own.toList.map (fillDecl (fillOf sp fs #[⟨M, w.home.frontier⟩]))

/-- **An accepted run over a closure** (see the module docstring). -/
structure Run (sp : SearchPath) (fs : FS) where
  C : List Graph.Node
  rk : Name → Nat
  good : ∀ e ∈ C, ModelIO.CanGive (moduleImports sp e.1) fs (.ok e.2)
  edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1
  inj : (C.map fun e => rk e.1).Nodup
  w : Name → WorkerRead
  jobs : Name → Nat
  facts : ∀ M ∈ C.map (·.1), WorkerFacts sp fs M (jobs M) (w M)
  run : ∀ M ∈ C.map (·.1), DeclsRun .verified natOpPinSets (ownDecls sp fs M (w M))
    ((w M).reach.ctx.size, mkFEnv (streamEnv (w M).reach.ctx.toList))
    ((w M).reach.ctx.size + (w M).own.size,
      mkFEnv (streamEnv (ownDecls sp fs M (w M)) (streamEnv (w M).reach.ctx.toList)))

variable {sp : SearchPath} {fs : FS}

/-- **The run of a closure every module of which has an accepted worker.** -/
noncomputable def Run.ofAccepted (C : List Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ C, ModelIO.CanGive (moduleImports sp e.1) fs (.ok e.2))
    (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (C.map fun e => rk e.1).Nodup)
    (acc : ∀ M ∈ C.map (·.1), ∃ jobs, WorkerAccepted .verified sp fs M jobs)
    (dflt : WorkerRead) : Run sp fs := by
  classical
  exact
  { C, rk, good, edges, inj
    w := fun M => if h : M ∈ C.map (·.1) then (acc M h).choose_spec.choose else dflt
    jobs := fun M => if h : M ∈ C.map (·.1) then (acc M h).choose else 0
    facts := fun M hM => by simp only [hM, ↓reduceDIte]; exact (acc M hM).choose_spec.choose_spec.1
    run := fun M hM => by simp only [hM, ↓reduceDIte]; exact (acc M hM).choose_spec.choose_spec.2 }

namespace Run

variable (R : Run sp fs)

/-- The run's modules. -/
@[expose] def names : List Name := R.C.map (·.1)

/-- The run of an accepted closure has that closure's modules. -/
theorem ofAccepted_names (C : List Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ C, ModelIO.CanGive (moduleImports sp e.1) fs (.ok e.2))
    (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (C.map fun e => rk e.1).Nodup)
    (acc : ∀ M ∈ C.map (·.1), ∃ jobs, WorkerAccepted .verified sp fs M jobs) (dflt : WorkerRead) :
    (Run.ofAccepted C rk good edges inj acc dflt).names = C.map (·.1) := by
  classical
  rfl

/-- **The module of rank `j`.** -/
@[expose] def nameOf (j : Nat) : Option Name := (R.C.find? fun e => R.rk e.1 == j).map (·.1)

/-- A module's sorted context. -/
@[expose] def ctx (M : Name) : List Declaration := (R.w M).reach.ctx.toList

/-- **The home of the context record storing `n`** in module `M`'s context. -/
@[expose] def homeIn (M n : Name) : Name :=
  (((R.ctx M).findIdx? fun d => (declNames d).contains n).bind fun k =>
    (R.w M).reach.homes[k]?).getD .anonymous

/-- **What module `M` presents**: every context record a worker of the run read with home `M`. -/
@[expose] def ifaceOf (M : Name) : List Declaration :=
  R.C.flatMap fun e => (((R.w e.1).reach.ctx.toList.zip (R.w e.1).reach.homes.toList).filter
    fun p => p.2 == M).map (·.1)

/-- **Module `M` as a module of the development.** -/
@[expose] noncomputable def modOf (M : Name) : Module where
  imports := []
  ctx := R.ctx M
  decls := ownDecls sp fs M (R.w M)
  src n := R.rk (R.homeIn M n)
  iface := R.ifaceOf M

/-- The module of a rank no module of the run has. -/
@[expose] def emptyMod : Module where
  imports := []
  ctx := []
  decls := []
  src _ := 0
  iface := []

/-- **The development of the run.** -/
@[expose] noncomputable def dev (j : Nat) : Module :=
  match R.nameOf j with
  | some M => R.modOf M
  | none => emptyMod

/-! ## Ranks and modules -/

theorem nameOf_rk {M : Name} (hM : M ∈ R.names) : R.nameOf (R.rk M) = some M := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  unfold nameOf
  cases hf : R.C.find? (fun e' => R.rk e'.1 == R.rk e.1) with
  | none =>
    have := List.find?_eq_none.1 hf e he
    simp at this
  | some e' =>
    have he' := List.mem_of_find?_eq_some hf
    have hr : R.rk e'.1 = R.rk e.1 := by simpa using List.find?_some hf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem he'
    have hii : i' = i := by
      have hnd := R.inj
      exact List.Nodup.eq_of_getElem_eq hnd (by simpa using hi') (by simpa using hi)
        (by simpa using hr)
    subst hii
    rfl

theorem dev_rk {M : Name} (hM : M ∈ R.names) : R.dev (R.rk M) = R.modOf M := by
  simp only [dev, R.nameOf_rk hM]

theorem nameOf_some {j : Nat} {M : Name} (h : R.nameOf j = some M) : M ∈ R.names ∧ R.rk M = j := by
  unfold nameOf at h
  cases hf : R.C.find? (fun e => R.rk e.1 == j) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨List.mem_map_of_mem (List.mem_of_find?_eq_some hf), by simpa using List.find?_some hf⟩

/-! ## The homes of the context records -/

theorem findIdx?_spec {α : Type} {p : α → Bool} :
    ∀ {L : List α} {k : Nat}, L.findIdx? p = some k → ∃ hk : k < L.length, p L[k] = true
  | [], _, h => by simp at h
  | a :: L, k, h => by
    rw [List.findIdx?_cons] at h
    by_cases ha : p a = true
    · simp only [ha, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨by simp, ha⟩
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨k', hk', rfl⟩ := h
      obtain ⟨hl, hp⟩ := findIdx?_spec hk'
      exact ⟨by simp; omega, by simpa using hp⟩

theorem findIdx?_isSome {α : Type} {p : α → Bool} :
    ∀ {L : List α} {a : α}, a ∈ L → p a = true → (L.findIdx? p).isSome = true
  | [], _, h, _ => by simp at h
  | b :: L, a, h, hp => by
    rw [List.findIdx?_cons]
    by_cases hb : p b = true
    · simp [hb]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.isSome_map]
      rcases List.mem_cons.1 h with rfl | h
      · exact absurd hp hb
      · exact findIdx?_isSome h hp

/-- Two positions of a list whose images, concatenated, are distinct, sharing an element of their
images, are one. -/
theorem nodup_flatMap_pos {α β : Type} {f : α → List β} :
    ∀ {L : List α}, (L.flatMap f).Nodup → ∀ {i j : Nat} (hi : i < L.length) (hj : j < L.length),
      i ≠ j → ∀ {x : β}, x ∈ f L[i] → x ∈ f L[j] → False
  | [], _, _, _, hi, _, _, _, _, _ => by simp at hi
  | a :: L, h, i, j, hi, hj, hne, x, hx, hy => by
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨-, h2, h3⟩ := h
    match i, j with
    | 0, 0 => exact hne rfl
    | 0, j + 1 =>
      exact h3 x hx x (List.mem_flatMap.2 ⟨_, List.getElem_mem (by simp at hj; omega), hy⟩) rfl
    | i + 1, 0 =>
      exact h3 x hy x (List.mem_flatMap.2 ⟨_, List.getElem_mem (by simp at hi; omega), hx⟩) rfl
    | i + 1, j + 1 =>
      exact nodup_flatMap_pos h2 (by simp at hi; omega) (by simp at hj; omega) (by omega) hx hy

/-- **The record storing a context name, and its home**: the record at the first position whose
names hold `n`; it is the one record storing `n`. -/
theorem homeIn_spec {M : Name} (hM : M ∈ R.names) {k : Nat} {d : Declaration} {h : Name}
    (hd : (R.w M).reach.ctx[k]? = some d) (hh : (R.w M).reach.homes[k]? = some h) {n : Name}
    (hn : n ∈ declNames d) : R.homeIn M n = h := by
  have hw := R.facts M hM
  have hdl : d ∈ R.ctx M := by
    unfold ctx; rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? hd
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1
    (findIdx?_isSome (p := fun d => (declNames d).contains n) hdl (by simpa using hn))
  obtain ⟨hlt, hp⟩ := findIdx?_spec hk'
  have hd' : (R.ctx M)[k'] ∈ R.ctx M := List.getElem_mem hlt
  have heq : (R.ctx M)[k'] = d :=
    worker_one_record hw hd' hdl (by simpa using hp) hn
  -- one record stores `n` once: its positions agree
  have hkk : k' = k := by
    have hnd := hw.nodup
    obtain ⟨hk0, hd0⟩ := Array.getElem?_eq_some_iff.1 hd
    have hk : k < (R.w M).reach.ctx.toList.length := by simpa using hk0
    have hdk : (R.w M).reach.ctx.toList[k] = d := by simp [hd0]
    have hlt' : k' < (R.w M).reach.ctx.toList.length := hlt
    have heq' : (R.w M).reach.ctx.toList[k'] = d := heq
    refine Classical.byContradiction fun hne => ?_
    exact nodup_flatMap_pos hnd hlt' hk hne (by rw [heq']; exact hn) (by rw [hdk]; exact hn)
  subst hkk
  unfold homeIn
  rw [hk']
  simp [hh]

/-- A pair of a zip at a position. -/
theorem mem_zip_pos {α β : Type} {a : Array α} {b : Array β} {x : α} {y : β}
    (h : (x, y) ∈ a.toList.zip b.toList) : ∃ i : Nat, a[i]? = some x ∧ b[i]? = some y := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  rw [List.getElem_zip] at he
  simp only [Prod.mk.injEq] at he
  simp only [List.length_zip, Array.length_toList] at hi
  refine ⟨i, ?_, ?_⟩
  · rw [Array.getElem?_eq_getElem (by omega)]; simp [← he.1]
  · rw [Array.getElem?_eq_getElem (by omega)]; simp [← he.2]

theorem pos_mem_zip {α β : Type} {a : Array α} {b : Array β} {x : α} {y : β} {i : Nat}
    (ha : a[i]? = some x) (hb : b[i]? = some y) : (x, y) ∈ a.toList.zip b.toList := by
  obtain ⟨hia, rfl⟩ := Array.getElem?_eq_some_iff.1 ha
  obtain ⟨hib, rfl⟩ := Array.getElem?_eq_some_iff.1 hb
  have : i < (a.toList.zip b.toList).length := by simp; omega
  rw [List.mem_iff_getElem]
  exact ⟨i, this, by simp⟩

theorem mem_ifaceOf {M : Name} {e : Declaration} :
    e ∈ R.ifaceOf M ↔ ∃ M' ∈ R.names, ∃ i : Nat, (R.w M').reach.ctx[i]? = some e ∧
      (R.w M').reach.homes[i]? = some M := by
  unfold ifaceOf names
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨e', he', hm⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    obtain ⟨hz, hpM⟩ := List.mem_filter.1 hp
    obtain ⟨i, h1, h2⟩ := mem_zip_pos (x := p.1) (y := p.2) hz
    exact ⟨e'.1, List.mem_map_of_mem he', i, h1, by rw [h2, beq_iff_eq.1 hpM]⟩
  · rintro ⟨M', hM', i, h1, h2⟩
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hM'
    exact ⟨e', he', List.mem_map.2 ⟨(e, M), List.mem_filter.2 ⟨pos_mem_zip h1 h2, by simp⟩, rfl⟩⟩

/-- **The local checks that need no capture fact**: at every rank, given that every home of a
context record is a module of the run of smaller rank and that every context record reads what it
reads alike from its home (`ImportOk.reads`, the capture check's). -/
theorem localOk_of
    (hhome : ∀ M ∈ R.names, ∀ (k : Nat) h, (R.w M).reach.homes[k]? = some h → h ∈ R.names ∧ R.rk h < R.rk M)
    (hreads : ∀ M ∈ R.names, ∀ d ∈ R.ctx M, ∀ n ∈ declNames d,
      RecordScoped (readsAlike R.dev (R.rk M) ((R.dev (R.rk M)).src n)) d)
    (j : Nat) : LocalOk .verified natOpPinSets R.dev j := by
  cases hj : R.nameOf j with
  | none =>
    have hd : R.dev j = emptyMod := by simp [dev, hj]
    refine ⟨⟨fun e he => by simp [hd, emptyMod] at he⟩, ⟨fun b hb => by simp [hd, emptyMod] at hb,
      fun n hn => ?_, by simp [hd, emptyMod, Module.context, streamEnv, Env.empty],
      fun d hd' => by simp [hd, emptyMod] at hd', fun d hd' => by simp [hd, emptyMod] at hd',
      fun d hd' => by simp [hd, emptyMod] at hd', fun k hk => by simp [hd, emptyMod] at hk,
      ⟨_, by rw [hd]; exact DeclsRun.nil _⟩⟩⟩
    simp [hd, emptyMod, Module.context, streamEnv, Env.empty, Env.find?] at hn
  | some M =>
    obtain ⟨hM, rfl⟩ := R.nameOf_some hj
    have hd : R.dev (R.rk M) = R.modOf M := R.dev_rk hM
    have hw := R.facts M hM
    -- a context record's names are read from its home
    have hsrcd : ∀ d ∈ (R.dev (R.rk M)).ctx, ∀ n ∈ declNames d,
        (R.dev (R.rk M)).src n = R.rk (R.homeIn M ((declNames d).headD .anonymous)) := by
      intro d hdm n hn
      rw [hd] at hdm ⊢
      obtain ⟨i, h, hi, hh⟩ := worker_home hw hdm
      have hne : declNames d ≠ [] := List.ne_nil_of_mem hn
      have hhd : (declNames d).headD .anonymous ∈ declNames d := by
        cases hl : declNames d with
        | nil => exact absurd hl hne
        | cons a l => simp
      show R.rk (R.homeIn M n) = _
      rw [R.homeIn_spec hM hi hh hn, R.homeIn_spec hM hi hh hhd]
    obtain ⟨h1, h2, h3, h4, -, -⟩ := worker_local hw (R.run M hM) R.dev (R.rk M)
      (by rw [hd]; rfl) (by rw [hd]; rfl) _ hsrcd
    refine ⟨interfaceOk_of_workers hw R.dev (R.rk M) (by rw [hd]; rfl) fun e he => ?_,
      ⟨fun b hb => by simp [hd, modOf] at hb, fun n hn => ?_, h1, fun d hdm n hn => ?_, h2,
        fun d hdm n hn => hreads M hM d (by rw [hd] at hdm; exact hdm) n hn, h4, h3⟩⟩
    · rw [hd] at he
      obtain ⟨M', hM', i, h1, h2⟩ := (R.mem_ifaceOf).1 he
      exact ⟨M', R.jobs M', R.w M', i, R.facts M' hM', h1, h2⟩
    · rw [hd] at hn ⊢
      obtain ⟨d, hdm, hnd⟩ := streamEnv_find_mem hn
      obtain ⟨i, h, hi, hh⟩ := worker_home hw hdm
      show R.rk (R.homeIn M n) < R.rk M
      rw [R.homeIn_spec hM hi hh hnd]
      exact (hhome M hM i h hh).2
    · rw [hd] at hdm ⊢
      obtain ⟨i, h, hi, hh⟩ := worker_home hw hdm
      show d ∈ (R.dev (R.rk (R.homeIn M n))).iface
      rw [R.homeIn_spec hM hi hh hn, R.dev_rk (hhome M hM i h hh).1]
      exact (R.mem_ifaceOf).2 ⟨M, hM, i, hi, hh⟩

/-- **A theorem of a module's private view is a constant of its own environment**, with its
type (`worker_thm`). -/
theorem thm_own {M : Name} (hM : M ∈ R.names) {d : ModDecoded} {c : CEntryF Name Expr} {v : Expr}
    {all : List Name} (hv : ViewOf sp fs M d) (hc : c ∈ d.constants) (hk : c.kind = .thm v all) :
    ∃ ci ∈ (R.dev (R.rk M)).own.consts, ci.toConstantVal.type = c.type := by
  obtain ⟨code, hmem, -⟩ := worker_thm (R.facts M hM) hv hc hk
  refine ⟨.thmInfo ⟨c.name, c.levelParams, c.type⟩, ?_, rfl⟩
  rw [R.dev_rk hM]
  show _ ∈ (streamEnv (ownDecls sp fs M (R.w M)) (streamEnv (R.ctx M))).consts
  refine (mem_streamEnv_consts _ _).2 (.inl ⟨_, List.mem_map.2 ⟨_, Array.mem_toList_iff.2 hmem, rfl⟩, ?_⟩)
  rw [declConstants_fillDecl]
  simp [declConstants]

/-- **A module reached by imports from a module of the run is one of smaller rank.** -/
theorem impReach_rank {M : Name} (hM : M ∈ R.names) {imps0 : Array ImportRec}
    (h0 : ModelIO.CanGive (moduleImports sp M) fs (.ok imps0)) {m : Name}
    (h : ImpReach sp fs imps0 m) : m ∈ R.names ∧ R.rk m < R.rk M := by
  induction h with
  | @root i hi =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
    obtain rfl := moduleImports_canGive_unique (R.good e he) h0
    exact R.edges e he i hi
  | @step a is i _ ha hi ih =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ih.1
    obtain rfl := moduleImports_canGive_unique (R.good e he) ha
    have := R.edges e he i hi
    exact ⟨this.1, by omega⟩

end Run

/-! ## Where a view's copies are -/

theorem viewStep_mem {v : Std.HashMap Name Spot} {k : PartKey} {t : NamePositions} {y : Name}
    {s : Spot} (h : (viewStep v k t)[y]? = some s) :
    v[y]? = some s ∨ (s.part = k ∧ s.pos ∈ t.consts) := by
  unfold viewStep at h
  rw [← Array.foldl_toList] at h
  suffices H : ∀ (l : List NamePosition) (v : Std.HashMap Name Spot), (∀ q ∈ l, q ∈ t.consts) →
      (l.foldl (fun (v : Std.HashMap Name Spot) q =>
        if v.contains q.name then v else v.insert q.name ⟨k, q⟩) v)[y]? = some s →
      v[y]? = some s ∨ (s.part = k ∧ s.pos ∈ t.consts) from
    H _ v (fun q hq => Array.mem_toList_iff.1 hq) h
  intro l
  induction l with
  | nil => intro v _ h; exact .inl h
  | cons q l ih =>
    intro v hl h
    simp only [List.foldl_cons] at h
    rcases ih _ (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')) h with h' | h'
    · split at h'
      · exact .inl h'
      · rw [Std.HashMap.getElem?_insert] at h'
        split at h'
        · cases h'; exact .inr ⟨rfl, hl q List.mem_cons_self⟩
        · exact .inl h'
    · exact .inr h'

theorem viewFold_mem {y : Name} {s : Spot} :
    ∀ (l : List (PartKey × NamePositions)) (v : Std.HashMap Name Spot),
      (l.foldl (fun v kt => viewStep v kt.1 kt.2) v)[y]? = some s →
      v[y]? = some s ∨ ∃ kt ∈ l, s.part = kt.1 ∧ s.pos ∈ kt.2.consts
  | [], v, h => .inl h
  | kt :: l, v, h => by
    rcases viewFold_mem l _ h with h' | ⟨kt', hkt', h'⟩
    · rcases viewStep_mem h' with h'' | h''
      · exact .inl h''
      · exact .inr ⟨kt, List.mem_cons_self, h''⟩
    · exact .inr ⟨kt', List.mem_cons_of_mem _ hkt', h'⟩

theorem viewKeys_mem {h : Name} {ld : Loads} {k : PartKey} (hk : k ∈ viewKeys h ld) :
    k = ⟨h, .private⟩ ∨ k.mod ∈ ld.order := by
  unfold viewKeys at hk
  rcases List.mem_cons.1 hk with rfl | hk
  · exact .inl rfl
  · obtain ⟨⟨m, fl⟩, hm, rfl⟩ := List.mem_map.1 hk
    exact .inr (Array.mem_toList_iff.1 (List.of_mem_zip (Array.toList_zip ▸ hm)).1)

/-- **A copy in a home's view is in one of its parts**: `h`'s own private part, or a part its
header fixpoint loads. -/
theorem homeView_part {h y : Name} {ld : Loads} {ts : List NamePositions}
    {s : Spot} (hs : (((viewKeys h ld).zip ts).foldl (fun v kt => viewStep v kt.1 kt.2) {})[y]? =
      some s) :
    (s.part = ⟨h, .private⟩ ∨ s.part.mod ∈ ld.order) ∧ ∃ t, (s.part, t) ∈ (viewKeys h ld).zip ts ∧
      s.pos ∈ t.consts := by
  rcases viewFold_mem _ _ hs with h' | ⟨kt, hkt, hp, hq⟩
  · simp at h'
  · refine ⟨viewKeys_mem (hp ▸ (List.of_mem_zip hkt).1), kt.2, by rw [hp]; exact hkt, hq⟩

/-! ## Agreement from the capture check's routes

At one module `i` of any development, the pairs `(b, y)` the capture check passed (`Pr`): a read
of `y` as module `b` reads it.  Each passed by a route: the copy is `b`'s, or `b` reads `y` from an
earlier module `t` whose copy agrees with `b`'s; and `t` is the module `i` reads `y` from, or `t`'s
copy and `i`'s are two proofs of one statement whose names were passed as reads of `t`, each
stored before `y`.  Then every passed pair agrees (`agree_of_routes`), by induction on the
context's order. -/

/-- **`t`'s copy of `y` and the one module `i` reads are proofs of one statement** whose names
`Pr` passed as reads of `t`, each of smaller rank than `y`. -/
@[expose] def ProofAt (dev : Nat → Module) (i : Nat) (Pr : Nat → Name → Prop) (t : Nat)
    (y : Name) : Prop :=
  ∃ ci ci', (dev i).context.find? y = some ci ∧ (dev t).own.find? y = some ci' ∧
    ci'.toConstantVal = ci.toConstantVal ∧ ci.isStmtKind = true ∧ ci'.isStmtKind = true ∧
    (∀ c ∈ ci.toConstantVal.type.readNames, Pr t c ∧ (dev i).rank c < (dev i).rank y ∧
      ((dev i).context.find? c).isSome = true) ∧
    ProofSide dev i t y ci.toConstantVal.type ∧
    ProofSide dev i ((dev i).src y) y ci.toConstantVal.type

/-- **A route of a passed pair** (see the section docstring). -/
@[expose] def Route (dev : Nat → Module) (i : Nat) (Pr : Nat → Name → Prop) (b : Nat) (y : Name) :
    Prop :=
  ∃ t, (t = b ∨ ((dev b).context.find? y).isSome = true ∧ t < b ∧ Agree dev b t y) ∧
    (t = (dev i).src y ∨ ProofAt dev i Pr t y)

/-- **Every passed pair agrees.** -/
theorem agree_of_routes {dev : Nat → Module} {i : Nat} {Pr : Nat → Name → Prop}
    (hr : ∀ b y, Pr b y → ((dev i).context.find? y).isSome = true → Route dev i Pr b y) :
    ∀ b y, Pr b y → ((dev i).context.find? y).isSome = true → Agree dev i b y := by
  suffices H : ∀ r, ∀ b y, (dev i).rank y < r → Pr b y →
      ((dev i).context.find? y).isSome = true → Agree dev i b y from
    fun b y hp hy => H _ b y (Nat.lt_succ_self _) hp hy
  intro r
  induction r with
  | zero => intro b y h; exact absurd h (Nat.not_lt_zero _)
  | succ r ih =>
    intro b y hlt hp hy
    obtain ⟨t, htb, hts⟩ := hr b y hp hy
    have hit : Agree dev i t y := by
      rcases hts with rfl | ⟨ci, ci', h1, h2, h3, h4, h5, h6, h7, h8⟩
      · exact .same rfl
      · exact .proof h1 h2 h3 h4 h5 (fun c hc =>
          ih t c (by have := (h6 c hc).2.1; omega) (h6 c hc).1 (h6 c hc).2.2) h7 h8
    rcases htb with rfl | ⟨hb, hlt', hbt⟩
    · exact hit
    · exact .via hb hlt' hbt hit

/-! ## What the workers reach -/

namespace Run

variable (R : Run sp fs)

/-- **What a module reaches by imports, from its own header.** -/
theorem rootImports {M : Name} (hM : M ∈ R.names) {own : NamePositions}
    (hown : ModelIO.CanGive (readPartNames sp (M, .private)) fs (.ok own)) :
    ModelIO.CanGive (moduleImports sp M) fs (.ok own.header.imports) := by
  obtain ⟨f, hf, hl⟩ := workerFacts_load (R.facts M hM)
  exact readPartNames_header hf hl hown

/-- **A module of a header fixpoint read from a module of the run is one of smaller rank.** -/
theorem fixpoint_rank {M : Name} (hM : M ∈ R.names) {own : NamePositions} {ld : Loads}
    (hown : ModelIO.CanGive (readPartNames sp (M, .private)) fs (.ok own))
    (hld : ModelIO.CanGive (headerFixpoint (moduleImports sp) own.header.isModule
      own.header.imports) fs (.ok ld)) {m : Name} (hm : m ∈ ld.order) :
    m ∈ R.names ∧ R.rk m < R.rk M := by
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hm
  obtain ⟨-, -, -, hs, -⟩ := headerFixpoint_sound hld
  exact R.impReach_rank hM (R.rootImports hM hown) (hs k _ (by simp [hk])).1

/-- **What a worker of the run reaches, by loads and views, is a module of smaller rank.** -/
theorem reached_rank {M : Name} (hM : M ∈ R.names) {m : Name}
    (h : Reached sp fs (R.w M).reads m) : m ∈ R.names ∧ R.rk m < R.rk M := by
  induction h with
  | @loaded j hj =>
    obtain ⟨_, _, hrd⟩ := (R.facts M hM).reads
    obtain ⟨own, hown, hld, -⟩ := workerReads_loads hrd
    have : (R.w M).reads.loads.nameAt j ∈ (R.w M).reads.loads.order := by
      unfold Loads.nameAt; rw [Array.getElem?_eq_getElem hj]; simp
    exact R.fixpoint_rank hM hown hld this
  | @view h v y s _ hv hs ih =>
    obtain ⟨own, ld, ts, hown, hld, -, -, rfl⟩ := hv
    rcases (homeView_part hs).1 with hp | hp
    · rw [hp]; exact ih
    · have := R.fixpoint_rank ih.1 hown hld hp
      exact ⟨this.1, by omega⟩

/-- An importer copy's module is a loaded one. -/
theorem importerSpot_loaded {env : ReachEnv ModelIO} {y : Name} {i : Nat} {s : Spot}
    (hsize : env.wr.index.parts.size = env.wr.loads.order.size)
    (h : importerSpot env y = some (i, s)) :
    i < env.wr.loads.order.size ∧ s.part.mod = env.wr.loads.nameAt i := by
  unfold importerSpot at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨cp, -, q, hq, h⟩ := h
  cases h
  unfold NameIndex.at at hq
  obtain ⟨t, ht, -⟩ := Option.bind_eq_some_iff.1 hq
  exact ⟨by rw [← hsize]; exact (Array.getElem?_eq_some_iff.1 ht).1, rfl⟩

/-- **The capture facts of a module's worker** (`reach_capture`, at the run's worker). -/
theorem capture {M : Name} (hM : M ∈ R.names) :
    let wr := (R.w M).reads
    let env : ReachEnv ModelIO :=
      { rd := .ofPath sp, mod := M, wr, own := ownNames (R.w M).home, copies := clashCopiesOf wr }
    let r := (R.w M).reach
    ∃ (loc : Std.HashMap Name Spot) (pend : List (String × Name × ConstantVal))
      (P : List (Name × Name)),
      r.ctx.size = r.homes.size ∧
      (∀ (k : Nat) (d : Declaration) (hm : Name), r.ctx[k]? = some d → r.homes[k]? = some hm →
        (∃ x ∈ declNames d, ∃ s, copyOf env loc x = some s ∧ s.part.mod = hm ∧ ReadAt sp fs d s) ∧
        (∀ n ∈ declNames d, ∃ s, copyOf env loc n = some s ∧ s.part.mod = hm) ∧
        (∀ y ∈ recordReads d, (hm, y) ∈ P) ∧
        (∀ n ∈ declNames d, ∀ cs, env.copies[n]? = some cs → ∀ kc ∈ cs,
          ∀ y ∈ (needsGo {} #[] kc.2.type).2, (kc.1, y) ∈ P)) ∧
      (∀ x ∈ P, Passed sp fs env loc (· ∈ pend) (· ∈ P) x.1 x.2) ∧
      (∀ cl ∈ wr.clashes, ClashOk sp fs wr (· ∈ pend) cl) ∧
      inferFlags r.ctx.toList pend = .ok () ∧
      (∀ (y : Name) (s : Spot), loc[y]? = some s → importerSpot env y = none ∧
        s.part.level = .private ∧ CopyAt sp fs s ∧ Reached sp fs wr s.part.mod ∧ s.pos.name = y) ∧
      (∀ x ∈ P, Reached sp fs wr x.1 ∧ Origin sp fs env r.ctx r.homes x) := by
  intro wr env r
  have hw := R.facts M hM
  obtain ⟨_, _, hrd⟩ := hw.reads
  obtain ⟨hparts, hindex⟩ := workerReads_index hrd
  obtain ⟨-, -, -, -, hsize, -, -, hcm⟩ := workerReads_loads hrd
  obtain ⟨_, _, hre⟩ := hw.reach
  exact reach_capture hparts hindex (Nat.le_of_eq hsize)
    (fun cl hcl x hx => hcm cl (Array.mem_toList_iff.2 hcl) x (Array.mem_toList_iff.2 hx)) hre

/-- **Every home of a context record is a module of the run of smaller rank.** -/
theorem home_rank {M : Name} (hM : M ∈ R.names) {k : Nat} {h : Name}
    (hh : (R.w M).reach.homes[k]? = some h) : h ∈ R.names ∧ R.rk h < R.rk M := by
  obtain ⟨loc, pend, P, hsz, hrec, -, -, -, hloc, -⟩ := R.capture hM
  obtain ⟨_, _, hrd⟩ := (R.facts M hM).reads
  obtain ⟨-, -, -, -, hsize, -⟩ := workerReads_loads hrd
  have hk : k < (R.w M).reach.ctx.size := by
    rw [hsz]; exact (Array.getElem?_eq_some_iff.1 hh).1
  obtain ⟨⟨x, -, s, hs, hmod, -⟩, -⟩ := hrec k _ h (Array.getElem?_eq_getElem hk) hh
  apply R.reached_rank hM
  rw [← hmod]
  unfold copyOf at hs
  split at hs
  · rename_i i s' he
    cases hs
    obtain ⟨hi, hmod'⟩ := importerSpot_loaded hsize he
    rw [hmod']; exact .loaded hi
  · exact (hloc x s hs).2.2.2.1

end Run

end ConLeche.Driver.Compose
