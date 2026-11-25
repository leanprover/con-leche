module

public import ConLeche.SetModel.TupleTower

@[expose] public section

/-!
# The tagged disjoint union (task #175 sum-types)

The semantic carrier of a directly-installed inductive with **any
number of constructors other than one**: a value is the pair of a
**numeral tag** — the constructor's index, a finite ordinal
`vnat i ∈ ω` — and that constructor's tuple tower
(`ConLeche/SetModel/TupleTower.lean`):

    sumSetL w fs  = sigmaSet w ω (finFibre fs) _
    sumSet w n f  = sigmaSet w ω (boundFibre n f) _
    inj i a       = spair (vnat i) a

`finFibre fs` is the first-order finite-list tag fibre over `ω`:
`fs[i]` at `vnat i` for `i < fs.length`, and `empty` everywhere else —
including at any non-standard element of `ω`.  `boundFibre n f` wraps
`finFibre` on `f 0, …, f (n - 1)`.

Both regimes ride one definition: `sigmaSet` reads `w` only through
its zero test, so at `w = 0` the carrier is the truth value "some
constructor's tower is inhabited" (`sumSet_zero_elim`) with every
member the proof point, and above `0` it is the set of tagged pairs
(`sumSet_elim`).  The tag domain `ω` sits in `univ w` for every `w ≥ 1`
(`omega_mem_univ_succ` + cumulativity), which is where the carrier's
formation lands (`sumSet_mem_univ`); at `w = 0` no bound is needed
(`sumSet_zero_mem_univZero`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory.Tower

universe u

variable {V : Type u} [SetTheory V]

open Classical in
/-- Auxiliary indexed list lookup over numerals starting at `n`. -/
noncomputable def finFibreFrom (n : Nat) : List V → V → V
  | [], _ => empty
  | a :: rest, k => if k = vnat n then a else finFibreFrom (n + 1) rest k

/-- Finite-list tag fibre over `ω`: `fs[i]` at `vnat i` for `i < fs.length`,
and `empty` everywhere else (including all non-standard members of `ω`). -/
noncomputable def finFibre (fs : List V) (k : V) : V :=
  finFibreFrom 0 fs k

theorem finFibreFrom_vnat_lt : ∀ (n : Nat) (fs : List V) (i : Nat) (hi : i < fs.length),
    finFibreFrom n fs (vnat (n + i)) = fs[i]
  | _, [], _, hi => absurd hi (Nat.not_lt_zero _)
  | n, a :: _, 0, _ => by
    unfold finFibreFrom
    simp
  | n, a :: rest, i + 1, hi => by
    unfold finFibreFrom
    have hne : (vnat (n + (i + 1)) : V) ≠ vnat n := fun h => by
      have := vnat_inj h
      omega
    rw [ite_eq_right hne, show n + (i + 1) = (n + 1) + i from by omega]
    exact finFibreFrom_vnat_lt (n + 1) rest i (Nat.lt_of_succ_lt_succ hi)

theorem finFibre_vnat_lt (fs : List V) {i : Nat} (hi : i < fs.length) :
    finFibre fs (vnat i) = fs[i] := by
  simpa [finFibre] using finFibreFrom_vnat_lt 0 fs i hi

theorem finFibreFrom_cases : ∀ (n : Nat) (fs : List V) (k : V),
    (∃ i, ∃ (hi : i < fs.length), k = vnat (n + i) ∧ finFibreFrom n fs k = fs[i]) ∨
    ((∀ i, i < fs.length → k ≠ vnat (n + i)) ∧ finFibreFrom n fs k = empty)
  | _, [], _ => Or.inr ⟨fun _ hi => absurd hi (Nat.not_lt_zero _), rfl⟩
  | n, a :: rest, k => by
    by_cases hk : k = vnat n
    · refine Or.inl ⟨0, Nat.zero_lt_succ _, by simpa using hk, ?_⟩
      unfold finFibreFrom
      exact ite_eq_left hk
    · have ih := finFibreFrom_cases (n + 1) rest k
      have hstep : finFibreFrom n (a :: rest) k = finFibreFrom (n + 1) rest k :=
        ite_eq_right hk
      rw [hstep]
      rcases ih with ⟨j, hj, hkj, hval⟩ | ⟨hno, hval⟩
      · refine Or.inl ⟨j + 1, Nat.succ_lt_succ hj, ?_, hval⟩
        rwa [show n + (j + 1) = (n + 1) + j from by omega]
      · refine Or.inr ⟨fun i hi => ?_, hval⟩
        cases i with
        | zero => simpa using hk
        | succ j =>
          rw [show n + (j + 1) = (n + 1) + j from by omega]
          exact hno j (Nat.lt_of_succ_lt_succ hi)

theorem finFibre_cases (fs : List V) (k : V) :
    (∃ i, ∃ (hi : i < fs.length), k = vnat i ∧ finFibre fs k = fs[i]) ∨
    ((∀ i, i < fs.length → k ≠ vnat i) ∧ finFibre fs k = empty) := by
  simpa [finFibre] using finFibreFrom_cases 0 fs k

theorem finFibre_empty_of_not_lt {fs : List V} {k : V}
    (h : ∀ i, i < fs.length → k ≠ vnat i) : finFibre fs k = empty := by
  rcases finFibre_cases fs k with ⟨i, hi, hki, _⟩ | ⟨_, hemp⟩
  · exact absurd hki (h i hi)
  · exact hemp

theorem finFibre_vnat_ge (fs : List V) {i : Nat} (hi : fs.length ≤ i) :
    finFibre fs (vnat i) = empty :=
  finFibre_empty_of_not_lt fun j hj h => by
    have := vnat_inj h
    omega

theorem _root_.ConLeche.SetTheory.DefFun.finFibreFrom_apply_list {p : Nat}
    (n : Nat) (fs : List ((Fin p → V) → V)) {K : (Fin p → V) → V}
    (hfs : ∀ f ∈ fs, DefFun p f) (hK : DefFun p K) :
    DefFun p fun env => finFibreFrom n (fs.map fun f => f env) (K env) := by
  induction fs generalizing n with
  | nil => exact DefFun.empty
  | cons f rest ih =>
    exact DefFun.ite (DefRel.eq_apply hK (DefFun.const (vnat n)))
      (hfs f (.head _))
      (ih (n + 1) (fun g hg => hfs g (.tail _ hg)))

theorem _root_.ConLeche.SetTheory.DefFun.finFibre_apply_list {p : Nat}
    (fs : List ((Fin p → V) → V)) {K : (Fin p → V) → V}
    (hfs : ∀ f ∈ fs, DefFun p f) (hK : DefFun p K) :
    DefFun p fun env => finFibre (fs.map fun f => f env) (K env) :=
  _root_.ConLeche.SetTheory.DefFun.finFibreFrom_apply_list 0 fs hfs hK

theorem _root_.ConLeche.SetTheory.DefFun.finFibreFrom_apply {p : Nat}
    (n : Nat) (fs : List V) {K : (Fin p → V) → V} (hK : DefFun p K) :
    DefFun p fun env => finFibreFrom n fs (K env) := by
  induction fs generalizing n with
  | nil => exact DefFun.empty
  | cons a rest ih =>
    exact DefFun.ite (DefRel.eq_apply hK (DefFun.const (vnat n)))
      (DefFun.const a)
      (ih (n + 1))

theorem _root_.ConLeche.SetTheory.DefFun.finFibre_apply {p : Nat} (fs : List V)
    {K : (Fin p → V) → V} (hK : DefFun p K) :
    DefFun p fun env => finFibre fs (K env) :=
  _root_.ConLeche.SetTheory.DefFun.finFibreFrom_apply 0 fs hK

theorem defFun_finFibre (fs : List V) : DefFun 1 fun v => finFibre fs (v 0) :=
  _root_.ConLeche.SetTheory.DefFun.finFibre_apply fs (DefFun.proj 0)

theorem hasSigmaPairs_finFibre (A : V) (fs : List V) : HasSigmaPairs A (finFibre fs) :=
  hasSigmaPairs_of_defFun1 (defFun_finFibre fs)

theorem hasGraph_finFibre (A : V) (fs : List V) : HasGraph A (finFibre fs) :=
  hasGraph_of_defFun1 (defFun_finFibre fs)

/-- Bounded tag fibre for `n` functions `f 0, …, f (n - 1)`, and `empty` elsewhere. -/
noncomputable def boundFibre (n : Nat) (f : Nat → V) (k : V) : V :=
  finFibre (List.ofFn fun i : Fin n => f i.val) k

theorem boundFibre_vnat_lt {n : Nat} (f : Nat → V) {i : Nat} (hi : i < n) :
    boundFibre n f (vnat i) = f i := by
  unfold boundFibre
  rw [finFibre_vnat_lt _ (by simp [hi]), List.getElem_ofFn]

theorem boundFibre_cases (n : Nat) (f : Nat → V) (k : V) :
    (∃ i, i < n ∧ k = vnat i ∧ boundFibre n f k = f i) ∨
    ((∀ i, i < n → k ≠ vnat i) ∧ boundFibre n f k = empty) := by
  unfold boundFibre
  rcases finFibre_cases (List.ofFn fun i : Fin n => f i.val) k with
    ⟨i, hi, hki, hval⟩ | ⟨hno, hemp⟩
  · simp only [List.length_ofFn] at hi
    rw [List.getElem_ofFn] at hval
    exact Or.inl ⟨i, hi, hki, hval⟩
  · refine Or.inr ⟨fun i hi => hno i (by simp [hi]), hemp⟩

theorem boundFibre_empty_of_not_lt {n : Nat} {f : Nat → V} {k : V}
    (h : ∀ i, i < n → k ≠ vnat i) : boundFibre n f k = empty := by
  rcases boundFibre_cases n f k with ⟨i, hi, hki, _⟩ | ⟨_, hemp⟩
  · exact absurd hki (h i hi)
  · exact hemp

theorem boundFibre_vnat_ge {n : Nat} (f : Nat → V) {i : Nat} (hi : n ≤ i) :
    boundFibre n f (vnat i) = empty :=
  boundFibre_empty_of_not_lt fun j hj h => by
    have := vnat_inj h
    omega

theorem boundFibre_congr {n : Nat} {f g : Nat → V} (h : ∀ i, i < n → f i = g i) (k : V) :
    boundFibre n f k = boundFibre n g k := by
  unfold boundFibre
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn]
    exact h i h1

theorem _root_.ConLeche.SetTheory.DefFun.boundFibre_apply {p : Nat} (n : Nat)
    {F : Nat → (Fin p → V) → V} {K : (Fin p → V) → V}
    (hF : ∀ i, i < n → DefFun p (F i)) (hK : DefFun p K) :
    DefFun p fun env => boundFibre n (fun i => F i env) (K env) := by
  have h := _root_.ConLeche.SetTheory.DefFun.finFibre_apply_list
    (List.ofFn fun i : Fin n => F i.val)
    (fun g hg => by
      obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_ofFn.mp hg
      exact hF i hi) hK
  refine h.congr fun env => ?_
  unfold boundFibre
  rw [List.map_ofFn]
  rfl

theorem defFun_boundFibre (n : Nat) (f : Nat → V) :
    DefFun 1 fun v => boundFibre n f (v 0) :=
  _root_.ConLeche.SetTheory.DefFun.boundFibre_apply n
    (fun i _ => DefFun.const (f i)) (DefFun.proj 0)

theorem hasSigmaPairs_boundFibre (A : V) (n : Nat) (f : Nat → V) :
    HasSigmaPairs A (boundFibre n f) :=
  hasSigmaPairs_of_defFun1 (defFun_boundFibre n f)

theorem hasGraph_boundFibre (A : V) (n : Nat) (f : Nat → V) :
    HasGraph A (boundFibre n f) :=
  hasGraph_of_defFun1 (defFun_boundFibre n f)

/-- **The tagged sum carrier from a finite list of constructor towers.** -/
noncomputable def sumSetL (w : Nat) (fs : List V) : V :=
  sigmaSet w omega (finFibre fs) (hasSigmaPairs_finFibre omega fs)

/-- **The bounded tagged sum carrier** over `n` constructor towers `f 0, …, f (n - 1)`. -/
noncomputable def sumSet (w n : Nat) (f : Nat → V) : V :=
  sigmaSet w omega (boundFibre n f) (hasSigmaPairs_boundFibre omega n f)

theorem sumSet_eq_sumSetL (w n : Nat) (f : Nat → V) :
    sumSet w n f = sumSetL w (List.ofFn fun i : Fin n => f i.val) := rfl

theorem sumSet_congr (w n : Nat) {f g : Nat → V} (h : ∀ i, i < n → f i = g i) :
    sumSet w n f = sumSet w n g := by
  unfold sumSet
  exact sigmaSet_congr _ _ fun k _ => boundFibre_congr h k

/-- **The injection** of constructor `i`. -/
noncomputable def inj (i : Nat) (a : V) : V := spair (vnat i) a

theorem _root_.ConLeche.SetTheory.DefFun.inj_apply {p : Nat} (i : Nat) {A : (Fin p → V) → V}
    (hA : DefFun p A) : DefFun p fun env => inj i (A env) :=
  DefFun.spair_apply (DefFun.const (vnat i)) hA

theorem _root_.ConLeche.SetTheory.DefFun.sumSetL_apply {p : Nat} (w : Nat)
    (fs : List ((Fin p → V) → V)) (hfs : ∀ f ∈ fs, DefFun p f) :
    DefFun p fun env => sumSetL w (fs.map fun f => f env) := by
  unfold sumSetL
  exact DefFun.sigmaSet_apply_curry w DefFun.omega_const
    ((_root_.ConLeche.SetTheory.DefFun.finFibre_apply_list (fs.map fun f w => f (ftail w))
      (fun g hg => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
        exact (hfs f hf).weaken)
      (DefFun.proj 0)).congr fun env => by
        simp [List.map_map, Function.comp_def])

theorem _root_.ConLeche.SetTheory.DefFun.sumSet_apply {p : Nat} (w n : Nat)
    {F : Nat → (Fin p → V) → V} (hF : ∀ i, i < n → DefFun p (F i)) :
    DefFun p fun env => sumSet w n (fun i => F i env) := by
  unfold sumSet
  exact DefFun.sigmaSet_apply_curry w DefFun.omega_const
    (_root_.ConLeche.SetTheory.DefFun.boundFibre_apply n
      (fun i hi => (hF i hi).weaken) (DefFun.proj 0))

/-! ## Laws for `sumSetL` -/

/-- **Intro** (graph regime): the injection of a fitting payload is in `sumSetL`. -/
theorem inj_mem_sumSetL {w : Nat} (hw : w ≠ 0) {fs : List V} {i : Nat} (hi : i < fs.length)
    {a : V} (ha : a ∈ˢ fs[i]) : inj i a ∈ˢ sumSetL w fs := by
  unfold inj sumSetL
  refine spair_mem hw (vnat_mem_omega i) ?_
  rwa [finFibre_vnat_lt fs hi]

/-- **Intro** (squash regime): `sumSetL 0 fs` holds the point whenever some tower is inhabited. -/
theorem pt_mem_sumSetL_zero {fs : List V} {i : Nat} (hi : i < fs.length) {a : V}
    (ha : a ∈ˢ fs[i]) : (pt : V) ∈ˢ sumSetL 0 fs := by
  unfold sumSetL
  exact pt_mem_sigma (a := vnat i) (b := a) (vnat_mem_omega i)
    (by rwa [finFibre_vnat_lt fs hi])

/-- **Elim** (graph regime): every member of `sumSetL` is an injection of some `fs[i]`. -/
theorem sumSetL_elim {w : Nat} (hw : w ≠ 0) {fs : List V} {x : V}
    (hx : x ∈ˢ sumSetL w fs) : ∃ i, ∃ (_ : i < fs.length), ∃ a, a ∈ˢ fs[i] ∧ x = inj i a := by
  unfold sumSetL at hx
  obtain ⟨k, a, -, ha, -, hpos⟩ := mem_sigma_elim hx
  rcases finFibre_cases fs k with ⟨i, hi, rfl, hfib⟩ | ⟨_, hemp⟩
  · rw [hfib] at ha
    exact ⟨i, hi, a, ha, hpos hw⟩
  · rw [hemp] at ha
    exact absurd ha (not_mem_empty a)

/-- **Elim** (squash regime): a `w = 0` member is the point, and some `fs[i]` is inhabited. -/
theorem sumSetL_zero_elim {fs : List V} {x : V} (hx : x ∈ˢ sumSetL 0 fs) :
    x = pt ∧ ∃ i, ∃ (_ : i < fs.length), ∃ a, a ∈ˢ fs[i] := by
  unfold sumSetL at hx
  obtain ⟨k, a, -, ha, hz, -⟩ := mem_sigma_elim hx
  rcases finFibre_cases fs k with ⟨i, hi, rfl, hfib⟩ | ⟨_, hemp⟩
  · rw [hfib] at ha
    exact ⟨hz rfl, i, hi, a, ha⟩
  · rw [hemp] at ha
    exact absurd ha (not_mem_empty a)

/-- **Formation** (graph regime) for `sumSetL`. -/
theorem sumSetL_mem_univ {w : Nat} (hw : w ≠ 0) {fs : List V}
    (hf : ∀ a ∈ fs, a ∈ˢ (univ w : V)) : sumSetL w fs ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  have hω : (omega : V) ∈ˢ univ (w' + 1) := omega_mem_univ_succ w'
  have h := sigma_mem_univ (u := w' + 1) (v := w' + 1) (B := finFibre fs) hω
    (fun k _ => by
      rcases finFibre_cases fs k with ⟨i, hi, _, hfib⟩ | ⟨_, hemp⟩
      · rw [hfib]
        exact hf fs[i] (List.getElem_mem hi)
      · rw [hemp]
        exact empty_mem_univ (w' + 1))
    (hasSigmaPairs_finFibre omega fs)
  rwa [show Nat.max (w' + 1) (w' + 1) = w' + 1 from Nat.max_self _] at h

/-- **Formation** (squash regime), unconditional. -/
theorem sumSetL_zero_mem_univZero (fs : List V) : sumSetL 0 fs ∈ˢ (univZero : V) := by
  unfold sumSetL
  rw [sigmaSet_zero]
  exact truthVal_mem_univZero _

/-- Above `0` the list-tagged sum is strict. -/
theorem strict_sumSetL {w : Nat} (hw : w ≠ 0) (fs : List V) : Strict (sumSetL w fs) := by
  unfold sumSetL
  rw [sigmaSet_pos hw]
  exact strict_sigmaPairs

/-- A list-tagged sum is a type. -/
theorem IsTy_sumSetL (w : Nat) (fs : List V) : IsTy (sumSetL w fs) := by
  by_cases hw : w = 0
  · subst hw; exact Or.inl (sumSetL_zero_mem_univZero fs)
  · exact IsTy_of_strict (strict_sumSetL hw fs)

/-! ## Laws for `sumSet` -/

/-- **Intro** (graph regime): the injection of a fitting payload is in
the bounded carrier. -/
theorem inj_mem {w n : Nat} (hw : w ≠ 0) {f : Nat → V} {i : Nat} (hi : i < n) {a : V}
    (ha : a ∈ˢ f i) : inj i a ∈ˢ sumSet w n f := by
  unfold inj sumSet
  refine spair_mem hw (vnat_mem_omega i) ?_
  rwa [boundFibre_vnat_lt f hi]

/-- **Intro** (squash regime): the carrier at `w = 0` holds the point
whenever some constructor's tower is inhabited. -/
theorem pt_mem_sumSet_zero {n : Nat} {f : Nat → V} {i : Nat} (hi : i < n) {a : V}
    (ha : a ∈ˢ f i) : (pt : V) ∈ˢ sumSet 0 n f := by
  unfold sumSet
  exact pt_mem_sigma (a := vnat i) (b := a) (vnat_mem_omega i)
    (by rwa [boundFibre_vnat_lt f hi])

/-- **Elim** (graph regime): every carrier member is the injection of
a fitting payload below `n`. -/
theorem sumSet_elim {w n : Nat} (hw : w ≠ 0) {f : Nat → V} {x : V}
    (hx : x ∈ˢ sumSet w n f) : ∃ i a, i < n ∧ a ∈ˢ f i ∧ x = inj i a := by
  unfold sumSet at hx
  obtain ⟨k, a, -, ha, -, hpos⟩ := mem_sigma_elim hx
  rcases boundFibre_cases n f k with ⟨i, hi, rfl, hfib⟩ | ⟨_, hemp⟩
  · rw [hfib] at ha
    exact ⟨i, a, hi, ha, hpos hw⟩
  · rw [hemp] at ha
    exact absurd ha (not_mem_empty a)

/-- **Elim** (squash regime): a `w = 0` carrier member is the point,
and some constructor's tower below `n` is inhabited. -/
theorem sumSet_zero_elim {n : Nat} {f : Nat → V} {x : V} (hx : x ∈ˢ sumSet 0 n f) :
    x = pt ∧ ∃ i a, i < n ∧ a ∈ˢ f i := by
  unfold sumSet at hx
  obtain ⟨k, a, -, ha, hz, -⟩ := mem_sigma_elim hx
  rcases boundFibre_cases n f k with ⟨i, hi, rfl, hfib⟩ | ⟨_, hemp⟩
  · rw [hfib] at ha
    exact ⟨hz rfl, i, a, hi, ha⟩
  · rw [hemp] at ha
    exact absurd ha (not_mem_empty a)

/-- **Tag disjointness and injectivity**: equal injections have equal
tags and payloads. -/
theorem inj_inj {i j : Nat} {a b : V} (h : inj i a = inj j b) : i = j ∧ a = b := by
  unfold inj at h
  have h1 := congrArg sfst h
  have h2 := congrArg ssnd h
  rw [sfst_spair, sfst_spair] at h1
  rw [ssnd_spair, ssnd_spair] at h2
  exact ⟨vnat_inj h1, h2⟩

/-- **Formation** (graph regime): with every tower below `n` in `univ w`,
the carrier is too — the tag domain `ω` sits in every `univ w` above `0`,
and any non-standard `k ∈ˢ ω` evaluates to `empty ∈ˢ univ w`. -/
theorem sumSet_mem_univ {w n : Nat} (hw : w ≠ 0) {f : Nat → V}
    (hf : ∀ i, i < n → f i ∈ˢ (univ w : V)) : sumSet w n f ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  have hω : (omega : V) ∈ˢ univ (w' + 1) := omega_mem_univ_succ w'
  have h := sigma_mem_univ (u := w' + 1) (v := w' + 1) (B := boundFibre n f) hω
    (fun k _ => by
      rcases boundFibre_cases n f k with ⟨i, hi, _, hfib⟩ | ⟨_, hemp⟩
      · rw [hfib]
        exact hf i hi
      · rw [hemp]
        exact empty_mem_univ (w' + 1))
    (hasSigmaPairs_boundFibre omega n f)
  rwa [show Nat.max (w' + 1) (w' + 1) = w' + 1 from Nat.max_self _] at h

/-- **Formation** (squash regime), unconditional. -/
theorem sumSet_zero_mem_univZero (n : Nat) (f : Nat → V) :
    sumSet 0 n f ∈ˢ (univZero : V) := by
  unfold sumSet
  rw [sigmaSet_zero]
  exact truthVal_mem_univZero _

/-- Above `0` the carrier is strict: its members are pairs. -/
theorem strict_sumSet {w : Nat} (hw : w ≠ 0) (n : Nat) (f : Nat → V) :
    Strict (sumSet w n f) := by
  unfold sumSet
  rw [sigmaSet_pos hw]
  exact strict_sigmaPairs

/-- A tagged sum is a type: a truth value at squash, strict above. -/
theorem IsTy_sumSet (w n : Nat) (f : Nat → V) : IsTy (sumSet w n f) := by
  by_cases hw : w = 0
  · subst hw; exact Or.inl (sumSet_zero_mem_univZero n f)
  · exact IsTy_of_strict (strict_sumSet hw n f)

/-! ## Degeneracy checks -/

/-- Zero constructors: the carrier is empty in the graph regime. -/
example {w : Nat} (hw : w ≠ 0) {x : V} (hx : x ∈ˢ sumSet w 0 (fun _ => (empty : V))) : False := by
  obtain ⟨i, _, hi, -⟩ := sumSet_elim hw hx
  exact Nat.not_lt_zero i hi

/-- Two constructors: the two injections are distinct. -/
example (a b : V) : inj 0 a ≠ inj 1 b := fun h => by
  have := (inj_inj h).1
  omega

end ConLeche.SetTheory.Tower
