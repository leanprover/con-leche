module

public import ConLeche.Verify.Driver.Compose
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Driver.PropPart
import ConLeche.Verify.Driver.Groups

/-!
# The composition: what a context record reads agrees with its home's copy

`ImportOk.reads` at every module of a run (`Run.reads_ok`), from the capture facts of the
module's worker (`Run.capture`): every read the capture check passed agrees (`Agree`), by
`agree_of_routes`, a route per pair read off the branch of `captureOne` that passed it.
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

variable {sp : SearchPath} {fs : FS} {maxNatSize : Nat}

/-- A presentation installs the names it presents. -/
theorem presents_names {d p : Declaration} (h : Presents d p) {n : Name} (hn : n ∈ declNames d) :
    n ∈ declNames p := by
  rcases h with ⟨hperm, -⟩ | ⟨rfl, -⟩
  · unfold declNames at hn ⊢
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
    exact List.mem_map_of_mem (hperm.mem_iff.1 hci)
  · cases p with
    | defnDecl cv v hh =>
      have := declNames_stmt (d := .axiomDecl cv) (.inl rfl) n hn
      simp [declNames, declConstants, this]; rfl
    | thmDecl cv v =>
      have := declNames_stmt (d := .axiomDecl cv) (.inl rfl) n hn
      simp [declNames, declConstants, this]; rfl
    | opaqueDecl cv v =>
      have := declNames_stmt (d := .axiomDecl cv) (.inl rfl) n hn
      simp [declNames, declConstants, this]; rfl
    | _ => exact hn

namespace Run

variable (R : Run sp fs maxNatSize)

/-- The reach's environment at module `M`'s worker. -/
@[expose] def envOf (M : Name) : ReachEnv ModelIO :=
  { rd := .ofPath sp, mod := M, wr := (R.w M).reads, own := ownOf (R.x M) (R.w M),
    copies := clashCopiesOf (R.w M).reads }

/-- **The capture facts of module `M`'s worker** over completions `loc`, inferences `pend` and
passed reads `P` (`Run.capture`'s statement). -/
@[expose] def CapFacts (M : Name) (loc : Std.HashMap Name Spot)
    (pend : List (String × Name × ConstantVal)) (P : List (Name × Name)) : Prop :=
  let wr := (R.w M).reads
  let env := R.envOf M
  let r := (R.w M).reach
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
  (∀ x ∈ P, Reached sp fs wr x.1 ∧ Origin sp fs env r.ctx r.homes x)

theorem capFacts_exists {M : Name} (hM : M ∈ R.names) :
    ∃ loc pend P, R.CapFacts M loc pend P := R.capture hM

/-- The capture data chosen at each module of the run. -/
@[expose] noncomputable def cap (M : Name) :
    Std.HashMap Name Spot × List (String × Name × ConstantVal) × List (Name × Name) := by
  classical
  exact if hM : M ∈ R.names then
    ⟨(R.capFacts_exists hM).choose, (R.capFacts_exists hM).choose_spec.choose,
      (R.capFacts_exists hM).choose_spec.choose_spec.choose⟩
  else default

theorem cap_facts {M : Name} (hM : M ∈ R.names) :
    R.CapFacts M (R.cap M).1 (R.cap M).2.1 (R.cap M).2.2 := by
  classical
  simp only [cap, hM, ↓reduceDIte]
  exact (R.capFacts_exists hM).choose_spec.choose_spec.choose_spec

/-! ## The module a context name is read from -/

/-- A context name of module `M`: a record storing it, at a position with a home. -/
theorem ctx_record {M : Name} (hM : M ∈ R.names) {y : Name}
    (hy : ((R.dev (R.rk M)).context.find? y).isSome = true) :
    ∃ (k : Nat) (d : Declaration) (h : Name), (R.w M).reach.ctx[k]? = some d ∧
      (R.w M).reach.homes[k]? = some h ∧ y ∈ declNames d := by
  rw [R.dev_rk hM] at hy
  obtain ⟨d, hd, hyd⟩ := streamEnv_find_mem hy
  obtain ⟨k, h, hk, hh⟩ := worker_home (R.facts M hM) hd
  exact ⟨k, d, h, hk, hh, hyd⟩

/-- **A context name is read from the module of its copy.** -/
theorem src_copy {M : Name} (hM : M ∈ R.names) {y : Name}
    (hy : ((R.dev (R.rk M)).context.find? y).isSome = true) :
    ∃ s, copyOf (R.envOf M) (R.cap M).1 y = some s ∧
      (R.dev (R.rk M)).src y = R.rk s.part.mod := by
  obtain ⟨k, d, h, hk, hh, hyd⟩ := R.ctx_record hM hy
  obtain ⟨-, hrec, -⟩ := R.cap_facts hM
  obtain ⟨s, hs, hmod⟩ := (hrec k d h hk hh).2.1 y hyd
  refine ⟨s, hs, ?_⟩
  rw [R.dev_rk hM]
  show R.rk (R.homeIn M y) = _
  rw [R.homeIn_spec hM hk hh hyd, hmod]

/-! ## `readsAlike`, by its lookup -/

theorem find?_filter_name' {l : List ConstantInfo} {t : List ProjTable} {q : Name → Bool}
    {n : Name} :
    (⟨l.filter fun c => q c.toConstantVal.name, []⟩ : Env).find? n =
      if q n = true then (⟨l, t⟩ : Env).find? n else none := by
  induction l with
  | nil => split <;> rfl
  | cons c l ih =>
    have e1 : ∀ (cs : List ConstantInfo) (ts : List ProjTable),
        (⟨cs, ts⟩ : Env).find? n = cs.find? (·.name == n) := fun _ _ => rfl
    rw [e1] at ih ⊢
    rw [e1, List.filter_cons]
    by_cases hc : c.name = n
    · have hc' : c.toConstantVal.name = n := hc
      by_cases hq : q n = true
      · simp [hc', hq, hc]
      · have hqf : q c.toConstantVal.name = false := by rw [hc']; simpa using hq
        rw [ite_eq_right hq] at ih ⊢
        simpa [hqf] using ih
    · have hc' : (c.name == n) = false := by simpa using hc
      split <;> simp only [List.find?_cons, hc'] <;> exact ih

/-- **A name `i` reads alike from `b`**: stored by `i`'s context, agreeing, and stored by `b`. -/
theorem readsAlike_isSome {dev : Nat → Module} {i b : Nat} {y : Name}
    (hc : ((dev i).context.find? y).isSome = true) (ha : Agree dev i b y)
    (hb : ((dev b).own.find? y).isSome = true) : ((readsAlike dev i b).find? y).isSome = true := by
  classical
  unfold readsAlike
  rw [find?_filter_name' (t := (dev b).own.tables)
    (q := fun n => decide (((dev i).context.find? n).isSome = true ∧ Agree dev i b n))]
  split
  · exact hb
  · next hn => exact absurd (by simpa using And.intro hc ha) hn

/-! ## Every passed read agrees -/

/-- The reads module `M`'s capture check passed, by the ranks of their reader modules. -/
@[expose] def Pr (M : Name) (b : Nat) (y : Name) : Prop :=
  ∃ h, R.rk h = b ∧ (h, y) ∈ (R.cap M).2.2

/-- **What the composition proves of a module**: every read its capture check passed, of a
name its context stores, agrees. -/
@[expose] def AgreeAll (M : Name) : Prop :=
  ∀ x ∈ (R.cap M).2.2, ((R.dev (R.rk M)).context.find? x.2).isSome = true →
    Agree R.dev (R.rk M) (R.rk x.1) x.2

/-- **Every passed read agrees at every module**, by strong induction on the rank, given a
route for each passed read from the modules of smaller rank. -/
theorem agree_all
    (hroute : ∀ M ∈ R.names, (∀ M' ∈ R.names, R.rk M' < R.rk M → R.AgreeAll M') →
      ∀ b y, R.Pr M b y → ((R.dev (R.rk M)).context.find? y).isSome = true →
        Route R.dev (R.rk M) (R.Pr M) b y) :
    ∀ M ∈ R.names, R.AgreeAll M := by
  suffices H : ∀ n, ∀ M ∈ R.names, R.rk M < n → R.AgreeAll M from
    fun M hM => H _ M hM (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro M _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro M hM hlt x hx hy
    exact agree_of_routes (hroute M hM fun M' hM' h' => ih M' hM' (by omega)) _ _
      ⟨x.1, rfl, hx⟩ hy

/-! ## A copy that agrees is stored -/

theorem own_of_decl {m : Module} {p : Declaration} (hp : p ∈ m.decls) {n : Name}
    (hn : n ∈ declNames p) : (m.own.find? n).isSome = true := by
  unfold declNames at hn
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hn
  simp only [Module.own, Env.find?, List.find?_isSome]
  exact ⟨ci, (mem_streamEnv_consts _ _).2 (.inl ⟨p, hp, hci⟩), by simp [ConstantInfo.name]⟩

theorem own_of_context {m : Module} {n : Name} (h : (m.context.find? n).isSome = true) :
    (m.own.find? n).isSome = true := by
  simp only [Module.context, Env.find?, List.find?_isSome] at h
  obtain ⟨ci, hci, he⟩ := h
  simp only [Module.own, Env.find?, List.find?_isSome]
  exact ⟨ci, (mem_streamEnv_consts _ _).2 (.inr hci), he⟩

/-- **The interface of a module of the run, and every context record presented** (the parts of
`localOk_of` that need no capture fact). -/
theorem iface_presented {M : Name} (hM : M ∈ R.names) :
    InterfaceOk R.dev (R.rk M) ∧
    ∀ d ∈ (R.dev (R.rk M)).ctx, ∀ n ∈ declNames d,
      d ∈ (R.dev ((R.dev (R.rk M)).src n)).iface := by
  have hd : R.dev (R.rk M) = R.modOf M := R.dev_rk hM
  have hw := R.facts M hM
  refine ⟨?_, fun d hdm n hn => ?_⟩
  · have hiface : ∀ e ∈ (R.dev (R.rk M)).iface, ∃ (M' : Name) (jM : Nat) (wM : WorkerRead)
        (xM : Array ImportRec) (i : Nat), WorkerFacts sp fs M' jM wM xM ∧
          wM.reach.ctx[i]? = some e ∧ wM.reach.homes[i]? = some M := fun e he => by
      rw [hd] at he
      obtain ⟨M', hM', i, h1, h2⟩ := (R.mem_ifaceOf).1 he
      exact ⟨M', R.jobs M', R.w M', R.x M', i, R.facts M' hM', h1, h2⟩
    by_cases hx : R.x M = #[]
    · exact interfaceOk_of_workers (R.facts₀ hM hx) R.dev (R.rk M) (by rw [hd]; rfl) hiface
    · refine ⟨fun e he => ?_⟩
      rw [hd] at he
      obtain ⟨M'', hM'', i', -, h2'⟩ := (R.mem_ifaceOf).1 he
      exact absurd (R.home_rank hM'' h2').2.2 hx
  · rw [hd] at hdm ⊢
    obtain ⟨i, h, hi, hh⟩ := worker_home hw hdm
    show d ∈ (R.dev (R.rk (R.homeIn M n))).iface
    rw [R.homeIn_spec hM hi hh hn, R.dev_rk (R.home_rank hM hh).1]
    exact (R.mem_ifaceOf).2 ⟨M, hM, i, hi, hh⟩

/-- **A copy that agrees with a module of the run's is stored**: by its source's presented
record, by the context it is read through, or as one of the two proofs. -/
theorem stored_of_agree {M : Name} (hM : M ∈ R.names) {b : Nat} {y : Name}
    (hy : ((R.dev (R.rk M)).context.find? y).isSome = true) (ha : Agree R.dev (R.rk M) b y) :
    ((R.dev b).own.find? y).isSome = true := by
  cases ha with
  | same hb =>
    subst hb
    obtain ⟨d, hd, hyd⟩ := streamEnv_find_mem hy
    have hpres := (R.iface_presented hM).2 d hd y hyd
    -- the source is a module of the run: its rank's module presents `d`
    obtain ⟨k, d', h, hk, hh, hyd'⟩ := R.ctx_record hM hy
    have hsrc : (R.dev (R.rk M)).src y = R.rk h := by
      rw [R.dev_rk hM]; show R.rk (R.homeIn M y) = _; rw [R.homeIn_spec hM hk hh hyd']
    have hh' := (R.home_rank hM hh).1
    rw [hsrc] at hpres ⊢
    obtain ⟨p, hp, hpr⟩ := (R.iface_presented hh').1.presents d hpres
    exact own_of_decl hp (presents_names hpr hyd)
  | via hb _ _ _ => exact own_of_context hb
  | proof _ h2 _ _ _ _ _ _ => rw [h2]; rfl
  | thm _ h2 _ _ _ _ _ _ _ _ _ => rw [h2]; rfl

/-- **`ImportOk.reads` from the agreement of every passed read.** -/
theorem reads_of_agree (hall : ∀ M ∈ R.names, R.AgreeAll M) :
    ∀ M ∈ R.names, ∀ d ∈ R.ctx M, ∀ n ∈ declNames d,
      RecordScoped (readsAlike R.dev (R.rk M) ((R.dev (R.rk M)).src n)) d := by
  intro M hM d hd n hn
  have hw := R.facts M hM
  obtain ⟨k, h, hk, hh⟩ := worker_home hw hd
  have hsrc : (R.dev (R.rk M)).src n = R.rk h := by
    rw [R.dev_rk hM]; show R.rk (R.homeIn M n) = _; rw [R.homeIn_spec hM hk hh hn]
  rw [hsrc]
  obtain ⟨-, hrec, -⟩ := R.cap_facts hM
  apply recordReads_scoped
  intro y hyr
  have hy : ((R.dev (R.rk M)).context.find? y).isSome = true := by
    rw [R.dev_rk hM]; exact (worker_ctx hw).2.2.1 d hd y hyr
  have hP := (hrec k d h hk hh).2.2.1 y hyr
  have ha := hall M hM (h, y) hP hy
  exact readsAlike_isSome hy ha (R.stored_of_agree hM hy ha)

/-! ## The routes -/

/-- **A passed read at module `M`, opened**: the reader `h` (a module of the run of smaller rank),
the context's copy `s₁`, whose module the name is read from, and the branch of `captureOne` that
passed it. -/
theorem passed_open {M : Name} (hM : M ∈ R.names) {h y : Name} (hP : (h, y) ∈ (R.cap M).2.2)
    (hy : ((R.dev (R.rk M)).context.find? y).isSome = true) :
    h ∈ R.names ∧ R.rk h < R.rk M ∧ R.x h = #[] ∧ ∃ s₁, copyOf (R.envOf M) (R.cap M).1 y = some s₁ ∧
      (R.dev (R.rk M)).src y = R.rk s₁.part.mod ∧
      (s₁.part.mod = h ∨ PubRoute sp fs (R.envOf M) h y s₁ ∨
        ∃ v s₂, HomeView sp fs h v ∧ v[y]? = some s₂ ∧
          AgreeOk sp fs (· ∈ (R.cap M).2.1) (· ∈ (R.cap M).2.2) y s₁ s₂) := by
  obtain ⟨-, -, hpass, -, -, -, hreach⟩ := R.cap_facts hM
  obtain ⟨hhn, hhr⟩ := R.reached_rank hM (hreach _ hP).1
  obtain ⟨s₁, hs₁, hb⟩ := hpass _ hP
  obtain ⟨s, hs, hsrc⟩ := R.src_copy hM hy
  obtain rfl : s₁ = s := Option.some.inj (hs₁.symm.trans hs)
  exact ⟨hhn, hhr.1, hhr.2, s₁, hs, hsrc, hb⟩

/-- **The route of a read whose copy is its reader's own** (`Agree.same`). -/
theorem route_same {M : Name} (hM : M ∈ R.names) {h y : Name} (hP : (h, y) ∈ (R.cap M).2.2)
    (hy : ((R.dev (R.rk M)).context.find? y).isSome = true) {s₁ : Spot}
    (hs₁ : copyOf (R.envOf M) (R.cap M).1 y = some s₁) (hmod : s₁.part.mod = h) :
    Route R.dev (R.rk M) (R.Pr M) (R.rk h) y := by
  obtain ⟨-, -, -, s, hs, hsrc, -⟩ := R.passed_open hM hP hy
  obtain rfl : s₁ = s := Option.some.inj (hs₁.symm.trans hs)
  exact ⟨R.rk h, .inl rfl, .inl (by rw [hsrc, hmod])⟩

/-- **`ImportOk.reads` at every module, from a route for every passed read** that is not its
reader's own copy. -/
theorem reads_of_routes
    (hroute : ∀ M ∈ R.names, (∀ M' ∈ R.names, R.rk M' < R.rk M → R.AgreeAll M') →
      ∀ h y, (h, y) ∈ (R.cap M).2.2 → ((R.dev (R.rk M)).context.find? y).isSome = true →
      ∀ s₁, copyOf (R.envOf M) (R.cap M).1 y = some s₁ → s₁.part.mod ≠ h →
        Route R.dev (R.rk M) (R.Pr M) (R.rk h) y) :
    ∀ M ∈ R.names, ∀ d ∈ R.ctx M, ∀ n ∈ declNames d,
      RecordScoped (readsAlike R.dev (R.rk M) ((R.dev (R.rk M)).src n)) d := by
  refine R.reads_of_agree (R.agree_all fun M hM ih b y hPr hy => ?_)
  obtain ⟨h, rfl, hP⟩ := hPr
  obtain ⟨-, -, -, s₁, hs₁, -, -⟩ := R.passed_open hM hP hy
  by_cases hmod : s₁.part.mod = h
  · exact R.route_same hM hP hy hs₁ hmod
  · exact hroute M hM ih h y hP hy s₁ hs₁ hmod

end Run

end ConLeche.Driver.Compose
