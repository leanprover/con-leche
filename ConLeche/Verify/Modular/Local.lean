module

public import ConLeche.Verify.Modular.Dev

public section

/-!
# A modular run's checks are the local checks (task #370)

`RunOk.localOk`: every module of the development a modular run stands
for (`devOf`) passes `ConLeche.Modular.LocalOk`.
-/

namespace ConLeche.Cached.Mod

open ConLeche ConLeche.Modular

variable {mode : CheckMode} {S : Store} {M : Array ModData}

/-! ## The store's lookups -/

theorem MBase.at?_some {b : MBase} {h j : Nat} {ci : ConstantInfo} (hat : b.at? h j = some ci) :
    ∃ (hl : h < b.lvl.size) (hs : h < b.slots.size),
      (b.lvl[h] = 2 ∧ (b.slots[h]).get.prv.priv[j]? = some ci) ∨
      (b.lvl[h] = 1 ∧ ∃ a, ((b.slots[h]).get.exp.at1[j]?).join = some a ∧
        b.gateOk (((b.slots[h]).get.exp.g1[j]?).getD #[]) = true ∧
        ((b.gateOk (((b.slots[h]).get.exp.v1[j]?).getD #[]) = true ∧ ci = a) ∨
         (b.gateOk (((b.slots[h]).get.exp.v1[j]?).getD #[]) = false ∧
           ci = .axiomInfo a.toConstantVal))) := by
  unfold MBase.at? at hat
  by_cases hl : h < b.lvl.size
  · simp only [hl, ↓reduceDIte] at hat
    refine ⟨hl, ?_⟩
    by_cases h2 : b.lvl[h] = 2
    · simp only [h2, beq_self_eq_true, ↓reduceIte] at hat
      by_cases hs : h < b.slots.size
      · simp only [hs, ↓reduceDIte] at hat
        exact ⟨hs, .inl ⟨h2, hat⟩⟩
      · simp only [hs, ↓reduceDIte] at hat; cases hat
    · simp only [beq_false_of_ne h2, Bool.false_eq_true, ↓reduceIte] at hat
      by_cases h1 : b.lvl[h] = 1
      · simp only [h1, beq_self_eq_true, ↓reduceIte] at hat
        by_cases hs : h < b.slots.size
        · simp only [hs, ↓reduceDIte] at hat
          refine ⟨hs, .inr ⟨h1, ?_⟩⟩
          cases ha : (b.slots[h].get.exp.at1[j]?).join with
          | none => rw [ha] at hat; cases hat
          | some a =>
            rw [ha] at hat
            dsimp only at hat
            refine ⟨a, rfl, ?_⟩
            by_cases hg : b.gateOk (b.slots[h].get.exp.g1[j]?.getD #[]) = true
            · simp only [hg, ↓reduceIte] at hat
              refine ⟨hg, ?_⟩
              by_cases hv : b.gateOk (b.slots[h].get.exp.v1[j]?.getD #[]) = true
              · simp only [hv, ↓reduceIte] at hat
                cases hat
                exact .inl ⟨hv, rfl⟩
              · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hat
                cases hat
                exact .inr ⟨Bool.of_not_eq_true hv, rfl⟩
            · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hat; cases hat
        · simp only [hs, ↓reduceDIte] at hat; cases hat
      · simp only [beq_false_of_ne h1, Bool.false_eq_true, ↓reduceIte] at hat; cases hat
  · simp only [hl, ↓reduceDIte] at hat; cases hat

theorem Store.mb_lvl (S : Store) (i : Nat) : (S.mb i).lvl = S.lvl i := rfl
theorem Store.mb_slots (S : Store) (i : Nat) : (S.mb i).slots = S.slots := rfl
theorem Store.mb_idx (S : Store) (i : Nat) : (S.mb i).idx = S.idx := rfl

theorem Store.slot_eq (S : Store) {h : Nat} (hs : h < S.slots.size) :
    (S.slots[h]).get = S.slot h := by
  unfold Store.slot
  rw [Array.getElem?_eq_getElem hs]
  rfl

/-- A visible alternate is a module the viewer loads. -/
theorem lvl_of_at? {i h j : Nat} {ci : ConstantInfo} (hat : (S.mb i).at? h j = some ci) :
    h < (S.lvl i).size ∧ (lvlAt (S.lvl i) h = 1 ∨ lvlAt (S.lvl i) h = 2) := by
  obtain ⟨hl, hs, hc⟩ := MBase.at?_some hat
  refine ⟨hl, ?_⟩
  unfold lvlAt
  have hl' : h < (S.lvl i).size := hl
  simp only [hl', ↓reduceDIte]
  rcases hc with ⟨h2, -⟩ | ⟨h1, -⟩
  · exact .inr h2
  · exact .inl h1

theorem lvlAt_eq {l : ByteArray} {h : Nat} (hl : h < l.size) : lvlAt l h = l[h] := by
  unfold lvlAt; simp only [hl, ↓reduceDIte]

/-- At the private level a visible alternate is the installed constant. -/
theorem at?_lvl2 {i h j : Nat} {ci : ConstantInfo} (hat : (S.mb i).at? h j = some ci)
    (h2 : lvlAt (S.lvl i) h = 2) : (S.slot h).prv.priv[j]? = some ci := by
  obtain ⟨hl, hs, hc⟩ := MBase.at?_some hat
  have hsl : (S.mb i).slots[h].get = S.slot h := Store.slot_eq S hs
  have hlv : (S.mb i).lvl[h] = lvlAt (S.lvl i) h := (lvlAt_eq (l := S.lvl i) hl).symm
  rcases hc with ⟨-, hp⟩ | ⟨h1, -⟩
  · rw [hsl] at hp; exact hp
  · rw [hlv, h2] at h1; cases h1

/-- At the exported level a visible alternate is its presentation, its
value hidden when the full gate is closed. -/
theorem at?_lvl1 {i h j : Nat} {ci : ConstantInfo} (hat : (S.mb i).at? h j = some ci)
    (h1 : lvlAt (S.lvl i) h = 1) :
    ∃ a, (S.slot h).exp.at1[j]? = some (some a) ∧
      (S.mb i).gateOk (((S.slot h).exp.g1[j]?).getD #[]) = true ∧
      ((S.mb i).gateOk (((S.slot h).exp.v1[j]?).getD #[]) = true ∧ ci = a ∨
       (S.mb i).gateOk (((S.slot h).exp.v1[j]?).getD #[]) = false ∧
         ci = .axiomInfo a.toConstantVal) := by
  obtain ⟨hl, hs, hc⟩ := MBase.at?_some hat
  have hsl : (S.mb i).slots[h].get = S.slot h := Store.slot_eq S hs
  have hlv : (S.mb i).lvl[h] = lvlAt (S.lvl i) h := (lvlAt_eq (l := S.lvl i) hl).symm
  rcases hc with ⟨h2, -⟩ | ⟨-, a, ha, hg, hv⟩
  · rw [hlv, h1] at h2; cases h2
  · rw [hsl] at ha hg hv
    refine ⟨a, ?_, hg, hv⟩
    cases hq : (S.slot h).exp.at1[j]? with
    | none => rw [hq] at ha; cases ha
    | some x => rw [hq] at ha; cases x with
      | none => cases ha
      | some a' => cases ha; rfl

/-! ## The local checks, unfolded -/

theorem localOk_lvl {units : Array Unit'} {m : Nat} (hl : localOk S units m = true) {h : Nat}
    (hh : h < (S.lvl m).size) (hnz : lvlAt (S.lvl m) h ≠ 0) :
    h < m ∧ lvlAt (S.lvl m) h ≤ 2 ∧ ∃ u, units[h]? = some u ∧
      (lvlAt (S.lvl m) h = 2 →
        ∀ x, x < (S.lvl h).size → lvlAt (S.lvl h) x ≤ lvlAt (S.lvl m) x) ∧
      (lvlAt (S.lvl m) h ≠ 2 → ∀ p ∈ u.fp1, lvlAt (S.lvl m) p.1 ≥ p.2) := by
  unfold localOk at hl
  rw [Bool.and_eq_true, List.all_eq_true] at hl
  have hx := hl.1 h (List.mem_range.mpr hh)
  simp only at hx
  rw [Bool.or_eq_true] at hx
  rcases hx with h0 | hx
  · exact absurd (beq_iff_eq.mp h0) hnz
  · rw [Bool.and_eq_true, Bool.and_eq_true] at hx
    obtain ⟨⟨hlt, hle⟩, hu⟩ := hx
    refine ⟨of_decide_eq_true hlt, of_decide_eq_true hle, ?_⟩
    cases hu' : units[h]? with
    | none => rw [hu'] at hu; cases hu
    | some u =>
      rw [hu'] at hu
      simp only at hu
      refine ⟨u, rfl, fun h2 x hx => ?_, fun h2 p hp => ?_⟩
      · rw [ite_eq_left (beq_iff_eq.mpr h2), List.all_eq_true] at hu
        exact of_decide_eq_true (hu x (List.mem_range.mpr hx))
      · rw [ite_eq_right (fun h' => h2 (beq_iff_eq.mp h')), Array.all_eq_true] at hu
        obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hp
        exact of_decide_eq_true (hu k hk)

theorem localOk_oneKey {units : Array Unit'} {m : Nat} (hl : localOk S units m = true) :
    ∀ n ∈ S.dups, oneKey S m n = true := by
  unfold localOk at hl
  simp only [Bool.and_eq_true, Array.all_eq_true] at hl
  intro n hn
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hn
  exact hl.2 k hk

/-! ## The development, unfolded -/

theorem devOf_of_lt {i : Nat} (hi : i < M.size) : devOf S M i = moduleOf S i M[i] := by
  unfold devOf; simp only [hi, ↓reduceDIte]

theorem devOf_of_ge {i : Nat} (hi : ¬ i < M.size) : devOf S M i = emptyModule := by
  unfold devOf; simp only [hi, ↓reduceDIte]

/-! ## A module's facts -/

theorem envAt_viewOf (mb : MBase) : envAt (viewOf mb) (ctxOf mb) = ctxOf mb := by
  unfold envAt viewOf; simp

/-- A module's view's environment at the end of its install is name-unique. -/
theorem RunOk.nodupOwn (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) :
    NodupNames (envAt M[i].fe (ctxOf (S.mb i))) := by
  obtain ⟨n, hrun⟩ := hR.run i hi
  obtain ⟨-, -, hch⟩ := viewRun_trace hrun (canonB_viewOf (S.mb i))
  have h := hch (ctxOf (S.mb i)) (by
    show PushChain _ (ConLeche.mkFEnv (envAt (viewOf (S.mb i)) (ctxOf (S.mb i))))
    rw [envAt_viewOf]; exact PushChain.refl _)
  exact h.2.2.1 (ctxOf_nodup _)

/-- **A context entry**: the store's visible alternate of a module the
viewer loads, earlier than it. -/
theorem RunOk.ctx_entry (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) {n : Name}
    {ci : ConstantInfo} (hf : (ctxOf (S.mb i)).find? n = some ci) :
    ∃ h j, (S.mb i).pick? n = some (h, j, ci) ∧ (S.mb i).at? h j = some ci ∧ ci.name = n ∧
      h < i ∧ h < (S.lvl i).size ∧ (lvlAt (S.lvl i) h = 1 ∨ lvlAt (S.lvl i) h = 2) := by
  rw [ctxOf_find?] at hf
  obtain ⟨h, j, hp⟩ := MBase.find?_some hf
  obtain ⟨hn, -, hat⟩ := MBase.pick?_some hp
  obtain ⟨hl, hlv⟩ := lvl_of_at? hat
  have hnz : lvlAt (S.lvl i) h ≠ 0 := by rcases hlv with h1 | h1 <;> rw [h1] <;> decide
  obtain ⟨hlt, -⟩ := localOk_lvl (hR.locals i hi) hl hnz
  exact ⟨h, j, hp, hat, hn, hlt, hl, hlv⟩

theorem RunOk.src_lt (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) (n : Name)
    (hn : ((devOf S M i).context.find? n).isSome = true) : (devOf S M i).src n < i := by
  rw [devOf_of_lt hi] at hn ⊢
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
  obtain ⟨h, j, hp, -, -, hlt, -⟩ := hR.ctx_entry hi hci
  show (match (S.mb i).pick? n with
    | some (h, _, _) => h
    | none => 0) < i
  rw [hp]
  exact hlt

theorem RunOk.accepted (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) :
    AcceptedFrom mode natOpPinSets (devOf S M i).proofs (devOf S M i).context
      (devOf S M i).decls (devOf S M i).own := by
  rw [devOf_of_lt hi]
  obtain ⟨n, hrun⟩ := hR.run i hi
  have h := accepted_of_run (hR.chk i hi) (hR.nodupOwn hi) (hR.prf i hi) hrun rfl
    (canonB_viewOf (S.mb i)) (by intro pc hpc; simp at hpc)
  rw [show envAt (S.view i) (ctxOf (S.mb i)) = ctxOf (S.mb i) from envAt_viewOf _] at h
  exact h

/-! ## Units -/

theorem shapeOk_spec {fe : FEnv} {flagged : Name → Bool} {s : ModSlot}
    (h : shapeOk fe flagged s = true) :
    s.prv.priv.size = s.exp.at1.size ∧ s.prv.priv.size = s.prv.tbls.size ∧
    s.prv.priv.size = s.exp.g1.size ∧ s.prv.priv.size = s.exp.v1.size ∧
    s.prv.priv.size = s.exp.prf.size ∧ s.prv.priv.size = s.exp.stored.size ∧
    s.prv.priv.size = s.exp.tbls.size ∧
    ∀ (j : Nat) (ci : ConstantInfo), s.prv.priv[j]? = some ci → ∃ st : Bool,
      s.exp.stored[j]? = some st ∧
      (s.exp.at1[j]? = some none ∨ s.exp.at1[j]? = some (some ci) ∨
        (s.exp.at1[j]? = some (some (asAxiom ci)) ∧ hideable ci = true)) ∧
      (st = true ↔ s.exp.at1[j]? = some (some ci)) ∧
      (∀ v : Array (Nat × UInt8), s.exp.v1[j]? = some v → v.isEmpty = true ∨
        (st = true ∧ hideable ci = true)) ∧
      s.exp.prf[j]? = some (flagged ci.name) ∧
      (flagged ci.name = true → (match ci with
        | .defnInfo .. | .thmInfo _ | .axiomInfo _ => true
        | _ => false) = true) ∧
      s.prv.tbls[j]? = some (fe.env.tables.find? (·.structName == ci.name)) ∧
      s.exp.tbls[j]? = some (if st then fe.env.tables.find? (·.structName == ci.name) else none) := by
  unfold shapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hall⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun j ci hci => ?_⟩
  have hj : j < s.prv.priv.size := by
    rcases Nat.lt_or_ge j s.prv.priv.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hci; cases hci
  have hj1 : j < s.exp.at1.size := by rw [← h1]; exact hj
  have hj2 : j < s.prv.tbls.size := by rw [← h2]; exact hj
  have hj4 : j < s.exp.v1.size := by rw [← h4]; exact hj
  have hj5 : j < s.exp.prf.size := by rw [← h5]; exact hj
  have hj6 : j < s.exp.stored.size := by rw [← h6]; exact hj
  have hj7 : j < s.exp.tbls.size := by rw [← h7]; exact hj
  have := hall j hj
  rw [hci, Array.getElem?_eq_getElem hj1, Array.getElem?_eq_getElem hj4,
    Array.getElem?_eq_getElem hj5, Array.getElem?_eq_getElem hj2,
    Array.getElem?_eq_getElem hj6, Array.getElem?_eq_getElem hj7] at this
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at this
  obtain ⟨⟨⟨⟨⟨⟨ha, hst⟩, hv⟩, hp⟩, hpk⟩, ht⟩, het⟩ := this
  refine ⟨s.exp.stored[j], Array.getElem?_eq_getElem hj6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Array.getElem?_eq_getElem hj1]
    revert ha
    cases s.exp.at1[j] with
    | none => intro _; exact .inl rfl
    | some a =>
      intro ha
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at ha
      rcases ha with rfl | ⟨rfl, hh⟩
      · exact .inr (.inl rfl)
      · exact .inr (.inr ⟨rfl, hh⟩)
  · rw [Array.getElem?_eq_getElem hj1, hst]
    simp
  · intro v hv'
    rw [Array.getElem?_eq_getElem hj4] at hv'
    cases hv'
    rcases hv with h | ⟨h, hh⟩
    · exact .inl h
    · exact .inr ⟨h, hh⟩
  · rw [Array.getElem?_eq_getElem hj5, hp]
  · intro hf
    rcases hpk with h | h
    · rw [hp] at h; rw [hf] at h; cases h
    · exact h
  · rw [Array.getElem?_eq_getElem hj2, ht]
  · rw [Array.getElem?_eq_getElem hj7, het, ht]

theorem unitOk_shape {h : Nat} {fe : FEnv} {flagged : Name → Bool} {u : Unit'} {r : Reads}
    (hu : unitOk S h fe flagged u r = true) : shapeOk fe flagged u.slot = true := by
  unfold unitOk at hu
  simp only [Bool.and_eq_true] at hu
  exact hu.1.1.1.1.1.1

/-- A name-unique list finds a member under its name. -/
theorem find?_of_mem_nodup {l : List ConstantInfo} (hnd : (l.map (·.name)).Nodup) {c : ConstantInfo}
    (hc : c ∈ l) : l.find? (·.name == c.name) = some c := by
  induction l with
  | nil => cases hc
  | cons x l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · have hne : (x.name == c.name) = false := by
        refine beq_false_of_ne fun he => hnd.1 ?_
        rw [he]; exact List.mem_map.mpr ⟨c, hc, rfl⟩
      rw [hne]
      exact ih hnd.2 hc

/-- **A home's own environment finds its installed constants.** -/
theorem RunOk.own_find? (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {j : Nat}
    {c : ConstantInfo} (hc : (S.slot h).prv.priv[j]? = some c) :
    (envAt M[h].fe (ctxOf (S.mb h))).find? c.name = some c := by
  rw [hR.slot h hh, hR.priv h hh] at hc
  have hmem : c ∈ M[h].fe.env.consts := by
    have := List.mem_of_getElem? (by simpa using hc)
    exact List.mem_reverse.mp this
  have hnd := hR.nodupOwn hh
  unfold NodupNames envAt at hnd
  simp only [List.map_append] at hnd
  unfold envAt Env.find?
  simp only
  rw [List.find?_append, find?_of_mem_nodup (List.nodup_append.mp hnd).1 hmem]
  rfl

/-! ## Entries and their homes -/

theorem gateOk_nil (b : MBase) : b.gateOk #[] = true := by
  unfold MBase.gateOk; simp

theorem RunOk.shape (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) :
    shapeOk M[h].fe M[h].flags.contains (S.slot h) = true := by
  rw [hR.slot h hh]; exact unitOk_shape (hR.unit h hh)

/-- **A visible alternate stands for its home's installed constant**: the
constant itself or the assumption of its statement, at a name that is not
pinned. -/
theorem RunOk.at?_home (hR : RunOk mode S M) {i h j : Nat} {ci : ConstantInfo}
    (hat : (S.mb i).at? h j = some ci) (hh : h < M.size) :
    ∃ c, (S.slot h).prv.priv[j]? = some c ∧
      (ci = c ∨ (ci = asAxiom c ∧ hideable c = true)) := by
  obtain ⟨hl, hs, hc⟩ := MBase.at?_some hat
  have hsl : (S.mb i).slots[h].get = S.slot h := Store.slot_eq S hs
  rw [hsl] at hc
  obtain ⟨h1, -, -, h4, -, h6, -, hj⟩ := shapeOk_spec (hR.shape hh)
  rcases hc with ⟨-, hp⟩ | ⟨-, a, ha, hg, hv⟩
  · exact ⟨ci, hp, .inl rfl⟩
  · have hjl : j < (S.slot h).exp.at1.size := by
      rcases Nat.lt_or_ge j (S.slot h).exp.at1.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at ha; cases ha
    have hjp : j < (S.slot h).prv.priv.size := by rw [h1]; exact hjl
    obtain ⟨st, hst, hat1, hstored, hv1, -⟩ :=
      hj j _ (Array.getElem?_eq_getElem hjp)
    refine ⟨_, Array.getElem?_eq_getElem hjp, ?_⟩
    rcases hat1 with h0 | h0 | ⟨h0, hhide⟩
    · rw [h0] at ha; cases ha
    · rw [h0] at ha
      cases ha
      rcases hv with ⟨-, rfl⟩ | ⟨hvf, rfl⟩
      · exact .inl rfl
      · -- a closed value gate is a non-empty one: the constant is stored and hideable
        have hjv : j < (S.slot h).exp.v1.size := by rw [← h4]; exact hjp
        rcases hv1 _ (Array.getElem?_eq_getElem hjv) with he | ⟨-, hhide⟩
        · rw [Array.getElem?_eq_getElem hjv] at hvf
          simp only [Option.getD_some] at hvf
          rw [Array.isEmpty_iff.mp he] at hvf
          exact absurd hvf (by rw [gateOk_nil]; decide)
        · exact .inr ⟨rfl, hhide⟩
    · rw [h0] at ha
      cases ha
      rcases hv with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact .inr ⟨rfl, hhide⟩
      · exact .inr ⟨rfl, hhide⟩

theorem not_pinned_of_hideable {c : ConstantInfo} (h : hideable c = true) :
    c.name ∉ pinnedNames := by
  unfold hideable isPinned at h
  intro hm
  simp [hm] at h

theorem RunOk.context_le (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) (n : Name)
    (ci : ConstantInfo) (hf : (devOf S M i).context.find? n = some ci) :
    ∃ ci', (devOf S M ((devOf S M i).src n)).own.find? n = some ci' ∧ Refines n ci ci' := by
  rw [devOf_of_lt hi] at hf ⊢
  obtain ⟨h, j, hp, hat, hn, hlt, -⟩ := hR.ctx_entry hi hf
  have hh : h < M.size := Nat.lt_trans hlt hi
  have hsrc : (moduleOf S i M[i]).src n = h := by
    show (match (S.mb i).pick? n with
      | some (h, _, _) => h
      | none => 0) = h
    rw [hp]
  rw [hsrc, devOf_of_lt hh]
  obtain ⟨c, hc, hci⟩ := hR.at?_home hat hh
  have hcn : c.name = n := by
    rcases hci with rfl | ⟨rfl, -⟩
    · exact hn
    · exact hn
  refine ⟨c, ?_, ?_⟩
  · rw [← hcn]; exact hR.own_find? hh hc
  · rcases hci with rfl | ⟨rfl, hhide⟩
    · exact .inl rfl
    · exact .inr ⟨hcn ▸ not_pinned_of_hideable hhide, rfl⟩

/-! ## The home's own lookups -/

/-- A home's own constant is not in its context. -/
theorem RunOk.own_not_ctx (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {j : Nat}
    {c : ConstantInfo} (hc : (S.slot h).prv.priv[j]? = some c) :
    (ctxOf (S.mb h)).find? c.name = none := by
  rw [hR.slot h hh, hR.priv h hh] at hc
  have hmem : c ∈ M[h].fe.env.consts := by
    have := List.mem_of_getElem? (by simpa using hc)
    exact List.mem_reverse.mp this
  have hnd := hR.nodupOwn hh
  unfold NodupNames envAt at hnd
  simp only [List.map_append] at hnd
  apply find?_none_of_not_mem
  intro hm
  exact (List.nodup_append.mp hnd).2.2 c.name (List.mem_map.mpr ⟨c, hmem, rfl⟩) c.name hm rfl

theorem RunOk.pick_none_own (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {j : Nat}
    {c : ConstantInfo} (hc : (S.slot h).prv.priv[j]? = some c) :
    (S.mb h).pick? c.name = none := by
  have := hR.own_not_ctx hh hc
  rw [ctxOf_find?] at this
  cases hp : (S.mb h).pick? c.name with
  | none => rfl
  | some x =>
    obtain ⟨h', j', ci⟩ := x
    unfold MBase.find? at this; rw [hp] at this; cases this

/-- **A home resolves its own constant to the qualified name the store
gives it.** -/
theorem RunOk.res_home (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {j : Nat}
    {c : ConstantInfo} (hc : (S.slot h).prv.priv[j]? = some c) :
    resOf S h M[h] c.name = S.keyAt h j c.name := by
  unfold resOf
  rw [hR.pick_none_own hh hc]
  simp only [hR.own_find? hh hc]
  unfold Store.keyAt keyOfSlot
  obtain ⟨-, -, -, -, -, -, -, hj⟩ := shapeOk_spec (hR.shape hh)
  obtain ⟨-, -, -, -, -, hpf, -⟩ := hj j c hc
  rw [hpf, hc]
  cases M[h].flags.contains c.name <;> rfl

theorem RunOk.res_context (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) (n : Name)
    (hn : ((devOf S M i).context.find? n).isSome = true) :
    (devOf S M i).res n = (devOf S M ((devOf S M i).src n)).res n := by
  rw [devOf_of_lt hi] at hn ⊢
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
  obtain ⟨h, j, hp, hat, hcn, hlt, -⟩ := hR.ctx_entry hi hci
  have hh : h < M.size := Nat.lt_trans hlt hi
  have hsrc : (moduleOf S i M[i]).src n = h := by
    show (match (S.mb i).pick? n with
      | some (h, _, _) => h
      | none => 0) = h
    rw [hp]
  rw [hsrc, devOf_of_lt hh]
  obtain ⟨c, hc, hci'⟩ := hR.at?_home hat hh
  have hname : c.name = n := by rcases hci' with rfl | ⟨rfl, -⟩ <;> exact hcn
  show resOf S i M[i] n = resOf S h M[h] n
  rw [← hname, hR.res_home hh hc]
  unfold resOf
  rw [hname, hp]

/-- A view at the end of its install looks up what the environment it
stands for stores. -/
theorem RunOk.fe_find? (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) (n : Name) :
    M[h].fe.find? n = (envAt M[h].fe (ctxOf (S.mb h))).find? n := by
  obtain ⟨k, hrun⟩ := hR.run h hh
  obtain ⟨hc, -, -⟩ := viewRun_trace hrun (canonB_viewOf (S.mb h))
  exact congrFun hc.twin.find n |>.trans (mkFEnv_find? _ n)

theorem RunOk.recFam (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) :
    ∀ n cv mI rP rules, (devOf S M i).context.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, ∀ cvj nP nF,
        (devOf S M ((devOf S M i).src n)).own.find? r.ctor = some (.ctorInfo cvj nP nF) →
        ∀ T us, cvj.type.piResult.getAppFn = .const T us →
          ∃ cvT capsT, (devOf S M ((devOf S M i).src n)).own.find? T = some (.indInfo cvT capsT) := by
  intro n cv mI rP rules hf r hr cvj nP nF hcj T us hT
  rw [devOf_of_lt hi] at hf hcj ⊢
  obtain ⟨h, j, hp, hat, hcn, hlt, -⟩ := hR.ctx_entry hi hf
  have hh : h < M.size := Nat.lt_trans hlt hi
  have hsrc : (moduleOf S i M[i]).src n = h := by
    show (match (S.mb i).pick? n with
      | some (h, _, _) => h
      | none => 0) = h
    rw [hp]
  rw [hsrc, devOf_of_lt hh] at hcj ⊢
  obtain ⟨c, hc, hci'⟩ := hR.at?_home hat hh
  have hcrec : c = .recInfo cv mI rP rules := by
    rcases hci' with rfl | ⟨h', -⟩
    · rfl
    · unfold asAxiom at h'; cases h'
  subst hcrec
  -- the unit's recursor check
  have hu := hR.unit h hh
  unfold unitOk at hu
  simp only [Bool.and_eq_true] at hu
  have hrf := hu.1.1.1.1.1.2
  rw [← hR.slot h hh, Array.all_eq_true] at hrf
  have hjs : j < (S.slot h).prv.priv.size := by
    rcases Nat.lt_or_ge j (S.slot h).prv.priv.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hc; cases hc
  have := hrf j hjs
  have hpj : (S.slot h).prv.priv[j] = .recInfo cv mI rP rules := by
    rw [Array.getElem?_eq_getElem hjs] at hc
    exact Option.some.inj hc
  rw [hpj] at this
  unfold recFamOk at this
  simp only [List.all_eq_true] at this
  have hr' := this r hr
  have hcj' : M[h].fe.find? r.ctor = some (.ctorInfo cvj nP nF) := by
    rw [hR.fe_find? hh]; exact hcj
  clear hcj
  rw [hcj'] at hr'
  simp only at hr'
  rw [hT] at hr'
  simp only at hr'
  revert hr'
  cases hfT : M[h].fe.find? T with
  | none => intro h'; cases h'
  | some cT =>
    intro h'
    cases cT with
    | indInfo cvT capsT =>
      refine ⟨cvT, capsT, ?_⟩
      show (envAt M[h].fe (ctxOf (S.mb h))).find? T = _
      rw [← hR.fe_find? hh]; exact hfT
    | _ => cases h'

/-! ## Tables -/

/-- **A home's own table is its environment's.** -/
theorem RunOk.own_findTable? (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {j : Nat}
    {c : ConstantInfo} (hc : (S.slot h).prv.priv[j]? = some c) :
    (envAt M[h].fe (ctxOf (S.mb h))).findTable? c.name =
      M[h].fe.env.tables.find? (·.structName == c.name) := by
  unfold Env.findTable?
  rw [hR.own_find? hh hc]
  simp only [Option.isSome_some, ↓reduceIte]
  unfold envAt
  simp only
  rw [List.find?_append]
  cases hq : M[h].fe.env.tables.find? (·.structName == c.name) with
  | some t => rfl
  | none =>
    simp only [Option.none_or]
    rw [ctxOf_tables_find?]
    cases ht : (S.mb h).findTable? c.name with
    | none => rfl
    | some t =>
      have := (MBase.findTable?_some ht).2
      rw [← ctxOf_find?, hR.own_not_ctx hh hc] at this
      cases this

theorem RunOk.tables (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) :
    ∀ T ci, (devOf S M i).context.find? T = some ci →
    (devOf S M i).context.findTable? T =
      match ci with
      | .indInfo .. => (devOf S M ((devOf S M i).src T)).own.findTable? T
      | _ => none := by
  intro T ci hf
  rw [devOf_of_lt hi] at hf ⊢
  obtain ⟨h, j, hp, hat, hcn, hlt, hl, hlv⟩ := hR.ctx_entry hi hf
  have hh : h < M.size := Nat.lt_trans hlt hi
  have hsrc : (moduleOf S i M[i]).src T = h := by
    show (match (S.mb i).pick? T with
      | some (h, _, _) => h
      | none => 0) = h
    rw [hp]
  rw [hsrc, devOf_of_lt hh]
  show (ctxOf (S.mb i)).findTable? T = _
  rw [ctxOf_findTable?]
  obtain ⟨c, hc, hci'⟩ := hR.at?_home hat hh
  cases ci with
  | indInfo cvI capsI =>
    have hci : c = .indInfo cvI capsI := by
      rcases hci' with rfl | ⟨h', -⟩
      · rfl
      · unfold asAxiom at h'; cases h'
    subst hci
    show _ = (envAt M[h].fe (ctxOf (S.mb h))).findTable? T
    rw [← hcn, hR.own_findTable? hh hc]
    obtain ⟨-, -, -, -, -, -, -, hj⟩ := shapeOk_spec (hR.shape hh)
    obtain ⟨st, hst, -, hstiff, -, -, -, hpt, het⟩ := hj j _ hc
    unfold MBase.findTable?
    rw [hcn, hp]
    simp only
    have hs : h < (S.mb i).slots.size := by
      have := (MBase.at?_some hat).2.1; exact this
    simp only [hs, ↓reduceDIte]
    have hsl : (S.mb i).slots[h].get = S.slot h := Store.slot_eq S hs
    have hl' : h < (S.mb i).lvl.size := hl
    simp only [hl', ↓reduceDIte, hsl]
    have hlv' : (S.mb i).lvl[h] = lvlAt (S.lvl i) h := by
      unfold lvlAt; simp only [hl, ↓reduceDIte]; rfl
    rw [hlv']
    -- the table found, whichever level
    have hsel : ((if lvlAt (S.lvl i) h == 2 then (S.slot h).prv.tbls[j]?
        else (S.slot h).exp.tbls[j]?)).join =
        M[h].fe.env.tables.find? (·.structName == (ConstantInfo.indInfo cvI capsI).name) := by
      rcases hlv with h1 | h2
      · rw [h1]
        simp only [show ((1 : UInt8) == 2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
        -- at the exported level the former is presented as stored
        obtain ⟨a, ha1, -, hv⟩ := at?_lvl1 hat h1
        have hst' : st = true := by
          rw [hstiff, ha1]
          rcases hv with ⟨-, rfl⟩ | ⟨-, h'⟩
          · rfl
          · cases h'
        rw [het, hst']
        rfl
      · rw [h2]
        simp only [show ((2 : UInt8) == 2) = true from rfl, ↓reduceIte]
        rw [hpt]
        rfl
    rw [hsel, hcn]
    cases hq : M[h].fe.env.tables.find? (·.structName == T) with
    | none => rfl
    | some t =>
      have := List.find?_some hq
      simp [this]
  | _ =>
    unfold MBase.findTable?
    rw [hp]

/-! ## The local checks -/

/-- **A modular run's checks are the local checks.** -/
theorem RunOk.localOk (hR : RunOk mode S M) (i : Nat) :
    LocalOk mode natOpPinSets (devOf S M) i := by
  by_cases hi : i < M.size
  case neg =>
    have hd := devOf_of_ge (S := S) hi
    refine { below := ?_, src_lt := ?_, nodup := ?_, accepted := ?_, compared_own := ?_,
             context_le := ?_, scoping := ?_, tables := ?_, projs := ?_, blocks := ?_,
             recFam := ?_, tables_mem := ?_, res_context := ?_, res_own := ?_ } <;>
      simp [hd, emptyModule, Env.find?, AcceptedFrom.nil]
  have hd := devOf_of_lt (S := S) hi
  refine { below := ?_, src_lt := hR.src_lt hi, nodup := ?_, accepted := fun _ => hR.accepted hi,
           compared_own := ?_, context_le := hR.context_le hi, scoping := ?_,
           tables := hR.tables hi, projs := ?_,
           blocks := ?_, recFam := hR.recFam hi, tables_mem := ?_,
           res_context := hR.res_context hi, res_own := ?_ }
  · rw [hd]; exact hR.below i hi
  · rw [hd]; exact ctxOf_nodup _
  · rw [hd]; intro h; cases h
  · sorry
  · sorry
  · sorry
  · rw [hd]; exact ctxOf_tables_mem _
  · rw [hd]
    intro n ci hown hctx
    change (envAt M[i].fe (ctxOf (S.mb i))).find? n = some ci at hown
    change (ctxOf (S.mb i)).find? n = none at hctx
    show resOf S i M[i] n = _
    unfold resOf
    rw [ctxOf_find?] at hctx
    have hp : (S.mb i).pick? n = none := by
      cases hp : (S.mb i).pick? n with
      | none => rfl
      | some x =>
        obtain ⟨h, j, ci'⟩ := x
        unfold MBase.find? at hctx; rw [hp] at hctx; cases hctx
    rw [hp]
    simp only [hown]
    show _ = (if M[i].flags.contains n = true then _ else _)
    rfl

end ConLeche.Cached.Mod
