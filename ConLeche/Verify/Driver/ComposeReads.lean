module

public import ConLeche.Verify.Driver.Compose
import ConLeche.Verify.Driver.Reach

/-!
# The composition: what a context record reads agrees with its home's copy

`ImportOk.reads` at every module of a run (`Run.reads_ok`), from the capture facts of the
module's worker (`Run.capture`): every read the capture check passed agrees (`Agree`), by
`agree_of_routes`, a route per pair read off the branch of `captureOne` that passed it.
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

variable {sp : SearchPath} {fs : FS}

namespace Run

variable (R : Run sp fs)

/-- The reach's environment at module `M`'s worker. -/
@[expose] def envOf (M : Name) : ReachEnv ModelIO :=
  { rd := .ofPath sp, mod := M, wr := (R.w M).reads, own := ownNames (R.w M).home,
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
    s.part.level = .private ∧ CopyAt sp fs s ∧ Reached sp fs wr s.part.mod) ∧
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

end Run

end ConLeche.Driver.Compose
