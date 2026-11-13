module

public import ConLeche.Verify.Ground.Sim
import ConLeche.Verify.Ground.Machine

public section

/-!
# Two frame stacks, one shape (task #423 soundness, layer (d), item 2(c))

The step simulation's relation on the frame stacks of two runs (`Sim.lean`'s
two programs).  `FS2 N PA PB fa fb t` parses `fa[0, t)` and `fb[0, t)` frame
by frame, as `FS` does one stack: a frame's top word (its tag) is one word
on both sides, and so is every other word, except a frame's entry word (ι,
the literal operations: related entries with names in `N`, `ERel`) and a projection frame's
row word (`PiRel`).  So both runs see the same frame tags, count the same
argument frames on top and read the same argument cells
(`FS2.countArgs`, `FS2.topEq`); popping and pushing keep the relation.
-/

namespace ConLeche.Verify.Ground

open ConLeche

/-- A projection frame's row word: no row on both sides, or related rows. -/
@[expose] def PiRel (PA PB : G4Prog) (a b : Nat) : Prop :=
  (a = 0 ∧ b = 0) ∨ ∃ qA qB, a = qA + 1 ∧ b = qB + 1 ∧ PrjRel PA PB qA qB

/-- **Two entries of one key**, its constant in `N`. -/
@[expose] def ERel (N : Name → Prop) (PA PB : G4Prog) (kA kB : Nat) : Prop :=
  EntRel PA PB kA kB ∧ ∀ iA, PA.kInfo[kA]? = some iA → N (infoKey iA).1

/-- **Two frame stacks of one shape**, `[0, t)`. -/
inductive FS2 (N : Name → Prop) (PA PB : G4Prog) (fa fb : Array Nat) : Nat → Prop where
  | nil : FS2 N PA PB fa fb 0
  /-- an argument, update or `Nat.succ` frame: one word -/
  | one {t : Nat} : fb[t]! = fa[t]! → (fa[t]! &&& 15 = 1 ∨ fa[t]! &&& 15 = 2 ∨ fa[t]! &&& 15 = 7) →
      FS2 N PA PB fa fb t → FS2 N PA PB fa fb (t + 1)
  | iota {t : Nat} : fb[t + 3]! = fa[t + 3]! → fa[t + 3]! &&& 15 = 3 → ERel N PA PB fa[t]! fb[t]! →
      fb[t + 1]! = fa[t + 1]! → fb[t + 2]! = fa[t + 2]! → FS2 N PA PB fa fb t → FS2 N PA PB fa fb (t + 4)
  | proj {t : Nat} : fb[t + 1]! = fa[t + 1]! → fa[t + 1]! &&& 15 = 4 → PiRel PA PB fa[t]! fb[t]! →
      FS2 N PA PB fa fb t → FS2 N PA PB fa fb (t + 2)
  | natA {t : Nat} : fb[t + 3]! = fa[t + 3]! → fa[t + 3]! &&& 15 = 5 → ERel N PA PB fa[t]! fb[t]! →
      fb[t + 1]! = fa[t + 1]! → fb[t + 2]! = fa[t + 2]! → FS2 N PA PB fa fb t → FS2 N PA PB fa fb (t + 4)
  | natB {t : Nat} : fb[t + 4]! = fa[t + 4]! → fa[t + 4]! &&& 15 = 6 → ERel N PA PB fa[t]! fb[t]! →
      fb[t + 1]! = fa[t + 1]! → fb[t + 2]! = fa[t + 2]! → fb[t + 3]! = fa[t + 3]! →
      FS2 N PA PB fa fb t → FS2 N PA PB fa fb (t + 5)

section
variable {j : Nat} {N : Name → Prop} {PA PB : G4Prog}

theorem ERel.ext {PA' PB' : G4Prog} (hA : ExtR PA PA') (hB : ExtR PB PB') {kA kB : Nat}
    (h : ERel N PA PB kA kB) : ERel N PA' PB' kA kB := by
  refine ⟨h.1.ext hA hB, fun iA hi => ?_⟩
  obtain ⟨iA', iB, h₁, -, -⟩ := h.1
  rw [hA.kInfo_some h₁] at hi; obtain rfl := Option.some.inj hi
  exact h.2 iA' h₁

theorem PrjRel.ext {PA' PB' : G4Prog} (hA : ExtR PA PA') (hB : ExtR PB PB') {qA qB : Nat}
    (h : PrjRel PA PB qA qB) : PrjRel PA' PB' qA qB := by
  obtain ⟨pj, h₁, h₂⟩ := h
  exact ⟨pj, hA.projs_some h₁, hB.projs_some h₂⟩

theorem PiRel.ext {PA' PB' : G4Prog} (hA : ExtR PA PA') (hB : ExtR PB PB') {a b : Nat}
    (h : PiRel PA PB a b) : PiRel PA' PB' a b := by
  rcases h with h | ⟨qA, qB, h₁, h₂, h₃⟩
  · exact .inl h
  · exact .inr ⟨qA, qB, h₁, h₂, h₃.ext hA hB⟩

/-- The programs grow. -/
theorem FS2.ext {PA' PB' : G4Prog} (hA : ExtR PA PA') (hB : ExtR PB PB') {fa fb : Array Nat} :
    ∀ {t : Nat}, FS2 N PA PB fa fb t → FS2 N PA' PB' fa fb t
  | _, .nil => .nil
  | _, .one e h r => .one e h (r.ext hA hB)
  | _, .iota e h k e₁ e₂ r => .iota e h (k.ext hA hB) e₁ e₂ (r.ext hA hB)
  | _, .proj e h p r => .proj e h (p.ext hA hB) (r.ext hA hB)
  | _, .natA e h k e₁ e₂ r => .natA e h (k.ext hA hB) e₁ e₂ (r.ext hA hB)
  | _, .natB e h k e₁ e₂ e₃ r => .natB e h (k.ext hA hB) e₁ e₂ e₃ (r.ext hA hB)

/-- **A parse reads only below its top**: arrays that keep the words below
`t` keep it. -/
theorem FS2.congr {fa fb fa' fb' : Array Nat} :
    ∀ {t : Nat}, FS2 N PA PB fa fb t → (∀ i, i < t → fa'[i]! = fa[i]!) → (∀ i, i < t → fb'[i]! = fb[i]!) →
      FS2 N PA PB fa' fb' t
  | _, .nil, _, _ => .nil
  | _, .one e h r, ha, hb => by
    refine .one ?_ ?_ (r.congr (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)))
    · rw [ha _ (by omega), hb _ (by omega)]; exact e
    · rw [ha _ (by omega)]; exact h
  | _, .iota e h k e₁ e₂ r, ha, hb => by
    refine .iota ?_ ?_ ?_ ?_ ?_ (r.congr (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)))
    · rw [ha _ (by omega), hb _ (by omega)]; exact e
    · rw [ha _ (by omega)]; exact h
    · rw [ha _ (by omega), hb _ (by omega)]; exact k
    · rw [ha _ (by omega), hb _ (by omega)]; exact e₁
    · rw [ha _ (by omega), hb _ (by omega)]; exact e₂
  | _, .proj e h p r, ha, hb => by
    refine .proj ?_ ?_ ?_ (r.congr (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)))
    · rw [ha _ (by omega), hb _ (by omega)]; exact e
    · rw [ha _ (by omega)]; exact h
    · rw [ha _ (by omega), hb _ (by omega)]; exact p
  | _, .natA e h k e₁ e₂ r, ha, hb => by
    refine .natA ?_ ?_ ?_ ?_ ?_ (r.congr (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)))
    · rw [ha _ (by omega), hb _ (by omega)]; exact e
    · rw [ha _ (by omega)]; exact h
    · rw [ha _ (by omega), hb _ (by omega)]; exact k
    · rw [ha _ (by omega), hb _ (by omega)]; exact e₁
    · rw [ha _ (by omega), hb _ (by omega)]; exact e₂
  | _, .natB e h k e₁ e₂ e₃ r, ha, hb => by
    refine .natB ?_ ?_ ?_ ?_ ?_ ?_ (r.congr (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)))
    · rw [ha _ (by omega), hb _ (by omega)]; exact e
    · rw [ha _ (by omega)]; exact h
    · rw [ha _ (by omega), hb _ (by omega)]; exact k
    · rw [ha _ (by omega), hb _ (by omega)]; exact e₁
    · rw [ha _ (by omega), hb _ (by omega)]; exact e₂
    · rw [ha _ (by omega), hb _ (by omega)]; exact e₃

/-- **The relation on two frame stacks**: one size, one shape. -/
@[expose] def FsRel (N : Name → Prop) (PA PB : G4Prog) (fa fb : Array Nat) : Prop :=
  fb.size = fa.size ∧ FS2 N PA PB fa fb fa.size

theorem FsRel.ext {PA' PB' : G4Prog} (hA : ExtR PA PA') (hB : ExtR PB PB') {fa fb : Array Nat}
    (h : FsRel N PA PB fa fb) : FsRel N PA' PB' fa fb := ⟨h.1, h.2.ext hA hB⟩

/-- Pushing related words above a parse keeps it below. -/
theorem FS2.push {fa fb : Array Nat} {t : Nat} (h : FS2 N PA PB fa fb t) (ht : t ≤ fa.size)
    (hs : fb.size = fa.size) (x y : Nat) : FS2 N PA PB (fa.push x) (fb.push y) t :=
  h.congr (fun i hi => getElem!_push_lt' (by omega)) (fun i hi => getElem!_push_lt' (by omega))

/-- **Pushing a one-word frame** (argument, update, `Nat.succ`). -/
theorem FsRel.pushOne {fa fb : Array Nat} (h : FsRel N PA PB fa fb) (w : Nat)
    (ht : w &&& 15 = 1 ∨ w &&& 15 = 2 ∨ w &&& 15 = 7) : FsRel N PA PB (fa.push w) (fb.push w) := by
  refine ⟨by simp [h.1], ?_⟩
  rw [Array.size_push]
  refine .one ?_ ?_ (h.2.push (Nat.le_refl _) h.1 w w)
  · rw [← h.1, getElem!_push_eq', h.1, getElem!_push_eq']
  · rw [getElem!_push_eq']; exact ht

theorem popN_get : ∀ (k : Nat) {a : Array Nat} {i : Nat}, i < a.size - k → (g4PopN a k)[i]! = a[i]!
  | 0, _, _, _ => rfl
  | k + 1, a, i, h => by
    simp only [g4PopN]
    rw [popN_get k (by simp; omega), getElem!_pop (by omega)]

/-- A parse below `t` survives popping down to `t`. -/
theorem FS2.popN {fa fb : Array Nat} {t : Nat} (h : FS2 N PA PB fa fb t) (k : Nat) (ht : t ≤ fa.size - k)
    (hs : fb.size = fa.size) : FS2 N PA PB (g4PopN fa k) (g4PopN fb k) t :=
  h.congr (fun i hi => popN_get k (by omega)) (fun i hi => popN_get k (by omega))

theorem FS2.pop {fa fb : Array Nat} {t : Nat} (h : FS2 N PA PB fa fb t) (ht : t ≤ fa.size - 1)
    (hs : fb.size = fa.size) : FS2 N PA PB fa.pop fb.pop t :=
  h.congr (fun i hi => getElem!_pop (by omega)) (fun i hi => getElem!_pop (by omega))

/-- **The top word is one word.** -/
theorem FS2.top {fa fb : Array Nat} {u : Nat} (h : FS2 N PA PB fa fb u) (hu : 0 < u) :
    fb[u - 1]! = fa[u - 1]! := by
  cases h with
  | nil => omega
  | one e _ _ => simpa using e
  | iota e _ _ _ _ _ | natA e _ _ _ _ _ => simpa using e
  | proj e _ _ _ => simpa using e
  | natB e _ _ _ _ _ _ => simpa using e

theorem FsRel.top {fa fb : Array Nat} (h : FsRel N PA PB fa fb) (hn : 0 < fa.size) :
    fb[fa.size - 1]! = fa[fa.size - 1]! :=
  h.2.top hn

/-- **A one-word frame on top**: the stack below is related. -/
theorem FsRel.popOne {fa fb : Array Nat} (h : FsRel N PA PB fa fb) (hn : 0 < fa.size)
    (ht : fa[fa.size - 1]! &&& 15 = 1 ∨ fa[fa.size - 1]! &&& 15 = 2 ∨ fa[fa.size - 1]! &&& 15 = 7) :
    FsRel N PA PB fa.pop fb.pop := by
  refine ⟨by simp [h.1], ?_⟩
  have h2 := h.2
  generalize hu : fa.size = u at h2 ht
  cases h2 with
  | nil => omega
  | @one t _ _ r => simp only [Array.size_pop, hu]; exact r.pop (by omega) h.1
  | @iota t _ h₀ _ _ _ _ | @natA t _ h₀ _ _ _ _ =>
    rw [show t + 4 - 1 = t + 3 by omega, h₀] at ht; simp at ht
  | @proj t _ h₀ _ _ => rw [show t + 2 - 1 = t + 1 by omega, h₀] at ht; simp at ht
  | @natB t _ h₀ _ _ _ _ _ => rw [show t + 5 - 1 = t + 4 by omega, h₀] at ht; simp at ht

/-! ## The multi-word frames on top -/

/-- **An ι frame on top**: its entry words related, its span words one, the
stack below related. -/
theorem FsRel.iotaTop {fa fb : Array Nat} (h : FsRel N PA PB fa fb) (hn : 0 < fa.size)
    (ht : fa[fa.size - 1]! &&& 15 = 3) :
    ERel N PA PB fa[fa.size - 4]! fb[fa.size - 4]! ∧ fb[fa.size - 3]! = fa[fa.size - 3]! ∧
      fb[fa.size - 2]! = fa[fa.size - 2]! ∧ FsRel N PA PB (g4PopN fa 4) (g4PopN fb 4) := by
  have h2 := h.2
  generalize hu : fa.size = u at h2 ht hn ⊢
  cases h2 with
  | nil => omega
  | @one t e h₀ _ => rw [show t + 1 - 1 = t by omega] at ht; rcases h₀ with h₀ | h₀ | h₀ <;> rw [h₀] at ht <;> cases ht
  | @iota t _ _ k e₁ e₂ r =>
    refine ⟨by simpa using k, by simpa [show t + 4 - 3 = t + 1 by omega] using e₁,
      by simpa [show t + 4 - 2 = t + 2 by omega] using e₂, by simp [g4PopN_size, h.1, hu], ?_⟩
    rw [g4PopN_size, hu, show t + 4 - 4 = t by omega]; exact r.popN 4 (by omega) h.1
  | @natA t _ h₀ _ _ _ _ => rw [show t + 4 - 1 = t + 3 by omega, h₀] at ht; cases ht
  | @proj t _ h₀ _ _ => rw [show t + 2 - 1 = t + 1 by omega, h₀] at ht; cases ht
  | @natB t _ h₀ _ _ _ _ _ => rw [show t + 5 - 1 = t + 4 by omega, h₀] at ht; cases ht

/-- **A projection frame on top**: its row words related, the stack below
related. -/
theorem FsRel.projTop {fa fb : Array Nat} (h : FsRel N PA PB fa fb) (hn : 0 < fa.size)
    (ht : fa[fa.size - 1]! &&& 15 = 4) :
    PiRel PA PB fa[fa.size - 2]! fb[fa.size - 2]! ∧ FsRel N PA PB fa.pop.pop fb.pop.pop := by
  have h2 := h.2
  generalize hu : fa.size = u at h2 ht hn ⊢
  cases h2 with
  | nil => omega
  | @one t e h₀ _ => rw [show t + 1 - 1 = t by omega] at ht; rcases h₀ with h₀ | h₀ | h₀ <;> rw [h₀] at ht <;> cases ht
  | @proj t _ _ p r =>
    refine ⟨by simpa using p, by simp [h.1, hu], ?_⟩
    simp only [Array.size_pop, hu, show t + 2 - 1 - 1 = t by omega]
    exact (r.pop (by omega) h.1).pop (by simp; omega) (by simp [h.1])
  | @iota t _ h₀ _ _ _ _ | @natA t _ h₀ _ _ _ _ => rw [show t + 4 - 1 = t + 3 by omega, h₀] at ht; cases ht
  | @natB t _ h₀ _ _ _ _ _ => rw [show t + 5 - 1 = t + 4 by omega, h₀] at ht; cases ht

/-- **A first literal frame on top**: its entry words related, its cell words
one, the stack below related. -/
theorem FsRel.natATop {fa fb : Array Nat} (h : FsRel N PA PB fa fb) (hn : 0 < fa.size)
    (ht : fa[fa.size - 1]! &&& 15 = 5) :
    ERel N PA PB fa[fa.size - 4]! fb[fa.size - 4]! ∧ fb[fa.size - 3]! = fa[fa.size - 3]! ∧
      fb[fa.size - 2]! = fa[fa.size - 2]! ∧ FsRel N PA PB (g4PopN fa 4) (g4PopN fb 4) := by
  have h2 := h.2
  generalize hu : fa.size = u at h2 ht hn ⊢
  cases h2 with
  | nil => omega
  | @one t e h₀ _ => rw [show t + 1 - 1 = t by omega] at ht; rcases h₀ with h₀ | h₀ | h₀ <;> rw [h₀] at ht <;> cases ht
  | @natA t _ _ k e₁ e₂ r =>
    refine ⟨by simpa using k, by simpa [show t + 4 - 3 = t + 1 by omega] using e₁,
      by simpa [show t + 4 - 2 = t + 2 by omega] using e₂, by simp [g4PopN_size, h.1, hu], ?_⟩
    rw [g4PopN_size, hu, show t + 4 - 4 = t by omega]; exact r.popN 4 (by omega) h.1
  | @iota t _ h₀ _ _ _ _ => rw [show t + 4 - 1 = t + 3 by omega, h₀] at ht; cases ht
  | @proj t _ h₀ _ _ => rw [show t + 2 - 1 = t + 1 by omega, h₀] at ht; cases ht
  | @natB t _ h₀ _ _ _ _ _ => rw [show t + 5 - 1 = t + 4 by omega, h₀] at ht; cases ht

/-- **A second literal frame on top**: its entry words related, its other
words one, the stack below related. -/
theorem FsRel.natBTop {fa fb : Array Nat} (h : FsRel N PA PB fa fb) (hn : 0 < fa.size)
    (ht : fa[fa.size - 1]! &&& 15 = 6) :
    ERel N PA PB fa[fa.size - 5]! fb[fa.size - 5]! ∧ fb[fa.size - 4]! = fa[fa.size - 4]! ∧
      fb[fa.size - 3]! = fa[fa.size - 3]! ∧ fb[fa.size - 2]! = fa[fa.size - 2]! ∧
      FsRel N PA PB (g4PopN fa 5) (g4PopN fb 5) := by
  have h2 := h.2
  generalize hu : fa.size = u at h2 ht hn ⊢
  cases h2 with
  | nil => omega
  | @one t e h₀ _ => rw [show t + 1 - 1 = t by omega] at ht; rcases h₀ with h₀ | h₀ | h₀ <;> rw [h₀] at ht <;> cases ht
  | @natB t _ _ k e₁ e₂ e₃ r =>
    refine ⟨by simpa using k, by simpa [show t + 5 - 4 = t + 1 by omega] using e₁,
      by simpa [show t + 5 - 3 = t + 2 by omega] using e₂,
      by simpa [show t + 5 - 2 = t + 3 by omega] using e₃, by simp [g4PopN_size, h.1, hu], ?_⟩
    rw [g4PopN_size, hu, show t + 5 - 5 = t by omega]; exact r.popN 5 (by omega) h.1
  | @iota t _ h₀ _ _ _ _ | @natA t _ h₀ _ _ _ _ => rw [show t + 4 - 1 = t + 3 by omega, h₀] at ht; cases ht
  | @proj t _ h₀ _ _ => rw [show t + 2 - 1 = t + 1 by omega, h₀] at ht; cases ht

/-! ## The argument frames on top -/

/-- The top `n` argument cells are one on both sides. -/
@[expose] def TopArgs (fa fb : Array Nat) (n : Nat) : Prop := ∀ j, j < n → g4ArgAt fb j = g4ArgAt fa j

theorem countArgs_le (fs : Array Nat) : ∀ (t n : Nat), g4CountArgs fs t n ≤ n + t
  | 0, n => by simp [g4CountArgs]
  | t + 1, n => by
    simp only [g4CountArgs]
    split
    · have := countArgs_le fs t (n + 1); omega
    · omega

theorem countArgs_stop (fs : Array Nat) {t n : Nat} (h : ¬fs[t]! &&& 15 = 1) :
    g4CountArgs fs (t + 1) n = n := by
  simp only [g4CountArgs, beq_iff_eq, h, ↓reduceIte]

/-- A frame other than an argument on top: no argument frames. -/
theorem FS2.stopAt {fa fb : Array Nat} {t : Nat} (h : FS2 N PA PB fa fb (t + 1)) (e : fb[t]! = fa[t]!)
    (ht : ¬fa[t]! &&& 15 = 1) (n : Nat) :
    g4CountArgs fb (t + 1) n = g4CountArgs fa (t + 1) n ∧
      (∀ j, n + j < g4CountArgs fa (t + 1) n → fb[t + 1 - 1 - j]! = fa[t + 1 - 1 - j]!) ∧
      ∀ k, n + k ≤ g4CountArgs fa (t + 1) n → FS2 N PA PB fa fb (t + 1 - k) := by
  rw [countArgs_stop fa ht, countArgs_stop fb (e ▸ ht)]
  exact ⟨rfl, fun j hj => by omega, fun k hk => by rw [show k = 0 by omega]; exact h⟩

/-- **One count of argument frames on top**, their words one, and the
stacks below them related. -/
theorem FS2.countArgs {fa fb : Array Nat} : ∀ {t : Nat}, FS2 N PA PB fa fb t → ∀ n,
    g4CountArgs fb t n = g4CountArgs fa t n ∧
      (∀ j, n + j < g4CountArgs fa t n → fb[t - 1 - j]! = fa[t - 1 - j]!) ∧
      ∀ k, n + k ≤ g4CountArgs fa t n → FS2 N PA PB fa fb (t - k)
  | _, .nil, n => ⟨rfl, fun j hj => by simp [g4CountArgs] at hj; omega,
      fun k hk => by simpa using FS2.nil⟩
  | t + 1, h@(.one e _ r), n => by
    by_cases h1 : fa[t]! &&& 15 = 1
    · simp only [g4CountArgs, e, h1, beq_self_eq_true, ↓reduceIte]
      obtain ⟨ih1, ih2, ih3⟩ := r.countArgs (n + 1)
      refine ⟨ih1, fun j hj => ?_, fun k hk => ?_⟩
      · rcases j with _ | j
        · simpa using e
        · have := ih2 j (by omega); rwa [show t - 1 - j = t + 1 - 1 - (j + 1) by omega] at this
      · rcases k with _ | k
        · exact h
        · have := ih3 k (by omega); rwa [show t - k = t + 1 - (k + 1) by omega] at this
    · exact FS2.stopAt h e h1 n
  | _, h@(.iota e ht _ _ _ _), n => FS2.stopAt h e (by rw [ht]; decide) n
  | _, h@(.natA e ht _ _ _ _), n => FS2.stopAt h e (by rw [ht]; decide) n
  | _, h@(.proj e ht _ _), n => FS2.stopAt h e (by rw [ht]; decide) n
  | _, h@(.natB e ht _ _ _ _ _), n => FS2.stopAt h e (by rw [ht]; decide) n

/-- **The argument frames on top**, from the relation on the stacks. -/
theorem FsRel.args {fa fb : Array Nat} (h : FsRel N PA PB fa fb) :
    g4CountArgs fb fb.size 0 = g4CountArgs fa fa.size 0 ∧ TopArgs fa fb (g4CountArgs fa fa.size 0) ∧
      ∀ k, k ≤ g4CountArgs fa fa.size 0 → FsRel N PA PB (g4PopN fa k) (g4PopN fb k) := by
  obtain ⟨c₁, c₂, c₃⟩ := h.2.countArgs 0
  have hle : g4CountArgs fa fa.size 0 ≤ fa.size := by
    have := countArgs_le fa fa.size 0; omega
  refine ⟨by rw [h.1]; exact c₁, fun j hj => ?_, fun k hk => ?_⟩
  · unfold g4ArgAt; rw [h.1, c₂ j (by omega)]
  · refine ⟨by simp [g4PopN_size, h.1], ?_⟩
    rw [g4PopN_size]
    exact (c₃ k (by omega)).popN k (by omega) h.1

/-! ## Reading the top argument cells -/

theorem copyArgs_congr {fa fb : Array Nat} : ∀ (n j : Nat) (argA : Array Nat),
    (∀ i, i < n → g4ArgAt fb (j + i) = g4ArgAt fa (j + i)) → g4CopyArgs fb argA n j = g4CopyArgs fa argA n j
  | 0, _, _, _ => rfl
  | n + 1, j, argA, h => by
    simp only [g4CopyArgs]
    rw [show g4ArgAt fb j = g4ArgAt fa j from by simpa using h 0 (by omega)]
    exact copyArgs_congr n (j + 1) _ fun i hi => by
      have := h (i + 1) (by omega); rwa [show j + (i + 1) = j + 1 + i by omega] at this

theorem hash_congr {fa fb : Array Nat} (k : Nat) : ∀ (n j : Nat) (h : UInt64),
    (∀ i, i < n → g4ArgAt fb (j + i) = g4ArgAt fa (j + i)) → g4Hash fb k n j h = g4Hash fa k n j h
  | 0, _, _, _ => rfl
  | n + 1, j, h, hh => by
    simp only [g4Hash]
    rw [show g4ArgAt fb j = g4ArgAt fa j from by simpa using hh 0 (by omega)]
    exact hash_congr k n (j + 1) _ fun i hi => by
      have := hh (i + 1) (by omega); rwa [show j + (i + 1) = j + 1 + i by omega] at this

theorem spanEq_congr {fa fb : Array Nat} (argA : Array Nat) (start : Nat) : ∀ (n j : Nat),
    (∀ i, i < n → g4ArgAt fb (j + i) = g4ArgAt fa (j + i)) →
      g4SpanEq fb argA start n j = g4SpanEq fa argA start n j
  | 0, _, _ => rfl
  | n + 1, j, hh => by
    have ih := spanEq_congr (fa := fa) (fb := fb) argA start n (j + 1) fun i hi => by
      have := hh (i + 1) (by omega); rwa [show j + (i + 1) = j + 1 + i by omega] at this
    have e : g4ArgAt fb j = g4ArgAt fa j := by simpa using hh 0 (by omega)
    simp only [g4SpanEq, e, ih]

theorem memoFind_congr {fa fb : Array Nat} (mem mT argA : Array Nat) (k n : Nat) (h : TopArgs fa fb n) :
    ∀ (f i : Nat), g4MemoFind mem mT fb argA k n f i = g4MemoFind mem mT fa argA k n f i
  | 0, _ => rfl
  | f + 1, i => by
    simp only [g4MemoFind]
    rw [spanEq_congr argA _ n 0 fun i hi => by simpa using h i hi, memoFind_congr mem mT argA k n h f]

theorem bindFrames_congr {fa fb : Array Nat} (hs : fb.size = fa.size) : ∀ (k j env : Nat) (ev : Array Nat),
    (∀ i, i < k → g4ArgAt fb (j + i) = g4ArgAt fa (j + i)) →
      g4BindFrames fb ev k j env = g4BindFrames fa ev k j env
  | 0, _, _, _, _ => rfl
  | k + 1, j, env, ev, hh => by
    simp only [g4BindFrames]
    have e : fb[fb.size - 1 - j]! >>> 4 = fa[fa.size - 1 - j]! >>> 4 := by
      simpa [g4ArgAt] using hh 0 (by omega)
    rw [e]
    exact bindFrames_congr hs k (j + 1) _ _ fun i hi => by
      have := hh (i + 1) (by omega); rwa [show j + (i + 1) = j + 1 + i by omega] at this

theorem TopArgs.mono {fa fb : Array Nat} {n m : Nat} (h : TopArgs fa fb n) (hm : m ≤ n) : TopArgs fa fb m :=
  fun j hj => h j (by omega)

theorem TopArgs.at {fa fb : Array Nat} {n : Nat} (h : TopArgs fa fb n) :
    ∀ i, i < n → g4ArgAt fb (0 + i) = g4ArgAt fa (0 + i) := fun i hi => by simpa using h i hi

/-- **Pushing argument frames** from a span keeps the relation. -/
theorem FsRel.pushArgs {fa fb : Array Nat} (argA : Array Nat) (start : Nat) :
    ∀ (n : Nat), FsRel N PA PB fa fb → FsRel N PA PB (g4PushArgs argA start fa n) (g4PushArgs argA start fb n)
  | 0, h => h
  | n + 1, h => by
    simp only [g4PushArgs]
    exact FsRel.pushArgs argA start n (h.pushOne _ (.inl (tag_and _ 1 (by omega))))

end

end ConLeche.Verify.Ground
