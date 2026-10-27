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
      (flagged ci.name = true → proofKind ci = true) ∧
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

theorem gateOk_iff {i : Nat} {g : Array (Nat × UInt8)} :
    (S.mb i).gateOk g = true ↔ ∀ p ∈ g, lvlAt (S.lvl i) p.1 ≥ p.2 := by
  unfold MBase.gateOk lvlAt
  rw [Store.mb_lvl, Array.all_eq_true']
  constructor
  · intro h p hp
    have := h p hp
    obtain ⟨x, l⟩ := p
    simpa using this
  · intro h p hp
    have := h p hp
    obtain ⟨x, l⟩ := p
    simpa using this

theorem u8_one_two {x : UInt8} (h1 : 1 ≤ x) (h2 : x ≤ 2) : x = 1 ∨ x = 2 := by
  have a := UInt8.le_iff_toNat_le.mp h1
  have b := UInt8.le_iff_toNat_le.mp h2
  simp at a b
  rcases (show x.toNat = 1 ∨ x.toNat = 2 by omega) with h | h
  · left; exact UInt8.toNat_inj.mp (by simpa using h)
  · right; exact UInt8.toNat_inj.mp (by simpa using h)

theorem u8_two {x : UInt8} (h1 : 2 ≤ x) (h2 : x ≤ 2) : x = 2 := by
  have a := UInt8.le_iff_toNat_le.mp h1
  have b := UInt8.le_iff_toNat_le.mp h2
  simp at a b
  exact UInt8.toNat_inj.mp (by simp; omega)

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

/-! ## The first visible alternate, and qualified names -/

/-- The visible alternates of a name, in order. -/
def visAlts (mb : MBase) (n : Name) (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.filter fun (h, j) => match mb.at? h j with
    | some ci => ci.name == n
    | none => false

theorem pickIn_head {mb : MBase} {n : Name} :
    ∀ {l : List (Nat × Nat)} {h j : Nat} {ci : ConstantInfo}, mb.pickIn n l = some (h, j, ci) →
      (visAlts mb n l).head? = some (h, j)
  | [], _, _, _, hp => by simp [MBase.pickIn] at hp
  | (h', j') :: rest, h, j, ci, hp => by
    unfold MBase.pickIn at hp
    unfold visAlts
    rw [List.filter_cons]
    cases hat : mb.at? h' j' with
    | none =>
      rw [hat] at hp
      simp only [hat]
      exact pickIn_head hp
    | some c =>
      rw [hat] at hp
      simp only [hat]
      by_cases hn : (c.name == n) = true
      · simp only [hn, ↓reduceIte] at hp
        cases hp
        simp [hn]
      · simp only [hn, Bool.false_eq_true, ↓reduceIte] at hp
        simp only [hn, Bool.false_eq_true, ↓reduceIte]
        exact pickIn_head hp

theorem pickIn_isSome {mb : MBase} {n : Name} :
    ∀ {l : List (Nat × Nat)} {x : Nat × Nat} {c : ConstantInfo}, x ∈ l → mb.at? x.1 x.2 = some c →
      c.name = n → (mb.pickIn n l).isSome = true
  | [], _, _, hx, _, _ => by cases hx
  | (h', j') :: rest, x, c, hx, hat, hn => by
    unfold MBase.pickIn
    cases hat' : mb.at? h' j' with
    | some c' =>
      simp only
      by_cases hn' : (c'.name == n) = true
      · rw [ite_eq_left hn']; rfl
      · rw [ite_eq_right hn']
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hat'] at hat; cases hat; exact absurd (beq_iff_eq.mpr hn) hn'
        · exact pickIn_isSome hx hat hn
    | none =>
      simp only
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hat'] at hat; cases hat
      · exact pickIn_isSome hx hat hn

theorem mem_visAlts {mb : MBase} {n : Name} {l : List (Nat × Nat)} {x : Nat × Nat}
    {c : ConstantInfo} (hx : x ∈ l) (hat : mb.at? x.1 x.2 = some c) (hn : c.name = n) :
    x ∈ visAlts mb n l := by
  unfold visAlts
  refine List.mem_filter.mpr ⟨hx, ?_⟩
  obtain ⟨h, j⟩ := x
  simp only at hat
  simp [hat, hn]

theorem Store.alts_mb (S : Store) (i : Nat) (n : Name) : (S.mb i).alts n = S.alts n := rfl

/-- **Two visible alternates of a name that meets in a context have one
qualified name** (`oneKey`, `dupsOk`): the first visible one's and any
other's. -/
theorem RunOk.key_pick (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) {n : Name}
    {h j : Nat} {ci : ConstantInfo} (hp : (S.mb i).pick? n = some (h, j, ci))
    {x : Nat × Nat} {c : ConstantInfo} (hx : x ∈ S.alts n) (hat : (S.mb i).at? x.1 x.2 = some c)
    (hn : c.name = n) : S.keyAt x.1 x.2 n = S.keyAt h j n := by
  have hhead := pickIn_head hp
  have hvis := mem_visAlts (mb := S.mb i) (l := (S.mb i).alts n)
    (by rw [Store.alts_mb]; exact hx) hat hn
  by_cases hlen : (S.alts n).length < 2
  · -- one alternate: the visible one is the first
    have hone : S.alts n = [x] := by
      match hl : S.alts n with
      | [] => rw [hl] at hx; cases hx
      | [y] => rw [hl] at hx; rw [List.mem_singleton.mp hx]
      | _ :: _ :: _ => rw [hl] at hlen; exact absurd hlen (by simp)
    have hp' : (S.mb i).pickIn n [x] = some (h, j, ci) := by
      unfold MBase.pick? at hp; rw [Store.alts_mb, hone] at hp; exact hp
    unfold MBase.pickIn at hp'
    obtain ⟨xh, xj⟩ := x
    simp only at hat
    rw [hat] at hp'
    simp only [hn, beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hp'
    obtain ⟨rfl, rfl, -⟩ := hp'
    rfl
  · -- several: the name is listed, and its copies have one qualified name
    have hdup : n ∈ S.dups := by
      have hd := hR.dups
      unfold dupsOk at hd
      rw [Array.all_eq_true] at hd
      have hl : S.alts n ≠ [] := by intro h; rw [h] at hx; cases hx
      unfold Store.alts MBase.alts at hl hlen
      rw [Store.mb_idx] at hl hlen
      split at hl
      · rename_i m hm
        rw [hm] at hlen
        have hs : baseShard n S.idx.size < S.idx.size := by
          rcases Nat.lt_or_ge (baseShard n S.idx.size) S.idx.size with h' | h'
          · exact h'
          · rw [Array.getElem?_eq_none h'] at hm; cases hm
        have hm' : S.idx[baseShard n S.idx.size] = m := by
          rw [Array.getElem?_eq_getElem hs] at hm; exact Option.some.inj hm
        have := hd _ hs
        rw [hm', List.all_eq_true] at this
        have hc : m.contains n = true := by
          cases hc : m.contains n with
          | true => rfl
          | false => rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false hc] at hl; exact absurd rfl hl
        have hmem : (n, m.getD n []) ∈ m.toList := by
          rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
          rw [Std.HashMap.getElem?_eq_some_getD_of_contains hc]
        have := this _ hmem
        simp only [Bool.or_eq_true, decide_eq_true_eq] at this
        rcases this with h' | h'
        · exact absurd h' hlen
        · exact Array.mem_of_contains_eq_true h'
      · exact absurd rfl hl
    have hok := localOk_oneKey (hR.locals i hi) n hdup
    unfold oneKey at hok
    simp only at hok
    have hhead' : (visAlts (S.mb i) n ((S.mb i).alts n)).head? = some (h, j) := hhead
    have hok' : (match visAlts (S.mb i) n ((S.mb i).alts n) with
        | [] => true
        | (h₀, j₀) :: rest => rest.all fun x => S.keyAt x.1 x.2 n == S.keyAt h₀ j₀ n) = true :=
      hok
    generalize visAlts (S.mb i) n ((S.mb i).alts n) = vis at hok' hhead' hvis
    cases vis with
    | nil => cases hvis
    | cons y rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead'
      subst hhead'
      rcases List.mem_cons.mp hvis with rfl | hrest
      · rfl
      · simp only [List.all_eq_true] at hok'
        exact beq_iff_eq.mp (hok' x hrest)

/-! ## Targets -/

theorem RunOk.finalCanon (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) :
    CanonB M[h].fe { mb := some (S.mb h) } := by
  obtain ⟨k, hrun⟩ := hR.run h hh
  exact (viewRun_trace hrun (canonB_viewOf (S.mb h))).1

theorem idxSpec_rev {d : Name} :
    ∀ {l : List ConstantInfo} {c : Nat} {ci : ConstantInfo}, idxSpec l d = some (c, ci) →
      l.reverse[c]? = some ci ∧ ci.name = d
  | [], _, _, h => by simp [idxSpec] at h
  | x :: l, c, ci, h => by
    rw [idxSpec] at h
    by_cases hx : x.name == d
    · rw [ite_eq_left hx] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, beq_iff_eq.mp hx⟩
      rw [List.reverse_cons, List.getElem?_append_right (by simp)]
      simp
    · rw [ite_eq_right hx] at h
      obtain ⟨h1, h2⟩ := idxSpec_rev h
      refine ⟨?_, h2⟩
      rw [List.reverse_cons, List.getElem?_append_left]
      · exact h1
      · have := idxSpec_lt h; simpa using this

/-- A module does not load itself. -/
theorem RunOk.lvl_self (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) :
    lvlAt (S.lvl h) h = 0 := by
  by_cases hl : h < (S.lvl h).size
  · rcases Nat.eq_zero_or_pos (lvlAt (S.lvl h) h).toNat with h0 | h0
    · exact UInt8.toNat_inj.mp (by simpa using h0)
    · have hnz : lvlAt (S.lvl h) h ≠ 0 := by
        intro he; rw [he] at h0; simp at h0
      exact absurd (localOk_lvl (hR.locals h hh) hl hnz).1 (Nat.lt_irrefl h)
  · unfold lvlAt; simp [hl]

/-- **What a module resolves a name to**: its own constant at the
counter, or the store's visible alternate (of another module). -/
theorem RunOk.target_cases (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {d : Name}
    {t : Nat × Nat} (ht : target h M[h].fe d = some t) :
    (t.1 = h ∧ ∃ p, (S.slot h).prv.priv[t.2]? = some p ∧ p.name = d ∧
      M[h].fe.find? d = some p) ∨
    (t.1 ≠ h ∧ ∃ ci, (S.mb h).pick? d = some (t.1, t.2, ci) ∧ M[h].fe.find? d = some ci) := by
  have hc := hR.finalCanon hh
  unfold target at ht
  cases hi : M[h].fe.idx[d]? with
  | some x =>
    obtain ⟨c, ci⟩ := x
    rw [hi] at ht
    simp only at ht
    split at ht
    · rename_i hlt
      cases ht
      rw [hc.idx d] at hi
      obtain ⟨h1, h2⟩ := idxSpec_rev hi
      refine .inl ⟨rfl, ci, ?_, h2, ?_⟩
      · rw [hR.slot h hh, hR.priv h hh]
        simpa using h1
      · rw [hc.find? d]
        unfold Env.find?
        rw [idxSpec_some hi]
        rfl
    · cases ht
  | none =>
    rw [hi] at ht
    simp only at ht
    rw [hc.base] at ht
    simp only at ht
    cases hp' : (S.mb h).pick? d with
    | none => rw [hp'] at ht; cases ht
    | some x =>
      obtain ⟨h', j', ci⟩ := x
      have hp := hp'
      rw [hp'] at ht
      simp only [Option.map_some, Option.some.injEq] at ht
      subst ht
      have hat := (MBase.pick?_some hp).2.2
      obtain ⟨hl, hlv⟩ := lvl_of_at? hat
      have hne : h' ≠ h := by
        intro he; subst he
        rw [hR.lvl_self hh] at hlv
        rcases hlv with h1 | h1 <;> cases h1
      refine .inr ⟨hne, ci, rfl, ?_⟩
      rw [hc.find? d]
      have hnone : M[h].fe.env.find? d = none := by
        unfold Env.find?
        rw [hc.idx d] at hi
        exact idxSpec_none hi
      rw [hnone]
      show (({ mb := some (S.mb h) } : FBase).find? d) = _
      show (S.mb h).find? d = _
      unfold MBase.find?
      rw [hp]

/-! ## Visibility -/

theorem at?_of_lvl2 {i h j : Nat} {p : ConstantInfo} (hl : h < (S.lvl i).size)
    (hs : h < S.slots.size) (h2 : lvlAt (S.lvl i) h = 2) (hp : (S.slot h).prv.priv[j]? = some p) :
    (S.mb i).at? h j = some p := by
  unfold MBase.at?
  have hl' : h < (S.mb i).lvl.size := hl
  have hs' : h < (S.mb i).slots.size := hs
  have hlv : (S.mb i).lvl[h] = 2 := by rw [← h2, lvlAt_eq hl]; rfl
  simp only [hl', ↓reduceDIte, hlv, beq_self_eq_true, ↓reduceIte, hs']
  have hsl : (S.mb i).slots[h].get = S.slot h := Store.slot_eq S hs
  rw [hsl]; exact hp

theorem at?_of_lvl1 {i h j : Nat} {a : ConstantInfo} (hl : h < (S.lvl i).size)
    (hs : h < S.slots.size) (h1 : lvlAt (S.lvl i) h = 1)
    (ha : (S.slot h).exp.at1[j]? = some (some a))
    (hg : ∀ p ∈ ((S.slot h).exp.g1[j]?).getD #[], lvlAt (S.lvl i) p.1 ≥ p.2) :
    (S.mb i).at? h j =
      some (if (S.mb i).gateOk (((S.slot h).exp.v1[j]?).getD #[]) then a
        else .axiomInfo a.toConstantVal) := by
  unfold MBase.at?
  have hl' : h < (S.mb i).lvl.size := hl
  have hs' : h < (S.mb i).slots.size := hs
  have hlv : (S.mb i).lvl[h] = 1 := by rw [← h1, lvlAt_eq hl]; rfl
  simp only [hl', ↓reduceDIte, hlv, show ((1 : UInt8) == 2) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, hs']
  have hsl : (S.mb i).slots[h].get = S.slot h := Store.slot_eq S hs
  rw [hsl, ha]
  simp only [Option.join_some]
  rw [ite_eq_left (gateOk_iff.mpr hg)]
  split <;> rfl

/-- A visible alternate's name is its installed constant's. -/
theorem RunOk.at?_name (hR : RunOk mode S M) {i h j : Nat} {ci : ConstantInfo}
    (hat : (S.mb i).at? h j = some ci) (hh : h < M.size) :
    ∃ c, (S.slot h).prv.priv[j]? = some c ∧ c.name = ci.name := by
  obtain ⟨c, hc, hci⟩ := hR.at?_home hat hh
  refine ⟨c, hc, ?_⟩
  rcases hci with rfl | ⟨rfl, -⟩
  · rfl
  · rfl

/-- **Loading more keeps an alternate visible**, with its name; one
presented as stored stays so. -/
theorem RunOk.at?_mono (hR : RunOk mode S M) {a b h j : Nat} {ci : ConstantInfo}
    (hat : (S.mb a).at? h j = some ci) (hh : h < M.size)
    (hle : ∀ x, lvlAt (S.lvl a) x ≤ lvlAt (S.lvl b) x) (hb2 : lvlAt (S.lvl b) h ≤ 2)
    (hbs : (S.lvl a).size ≤ (S.lvl b).size) :
    ∃ ci', (S.mb b).at? h j = some ci' ∧ ci'.name = ci.name ∧
      ((S.slot h).prv.priv[j]? = some ci → ci' = ci) := by
  obtain ⟨hl, hlv⟩ := lvl_of_at? hat
  have hs : h < S.slots.size := by rw [hR.slots]; exact hh
  have hlb : h < (S.lvl b).size := Nat.lt_of_lt_of_le hl hbs
  obtain ⟨c, hc, hcn⟩ := hR.at?_name hat hh
  obtain ⟨h1, -, -, -, -, -, -, hj⟩ := shapeOk_spec (hR.shape hh)
  obtain ⟨st, -, hat1, hstiff, hv1, -⟩ := hj j c hc
  have hgmono : ∀ g : Array (Nat × UInt8), (S.mb a).gateOk g = true → (S.mb b).gateOk g = true :=
    fun g hg => gateOk_iff.mpr fun p hp => Nat.le_trans (gateOk_iff.mp hg p hp) (hle p.1)
  rcases hlv with ha1 | ha2
  · obtain ⟨x, hx, hg, hv⟩ := at?_lvl1 hat ha1
    have hb : lvlAt (S.lvl b) h = 1 ∨ lvlAt (S.lvl b) h = 2 := by
      have := hle h; rw [ha1] at this
      exact u8_one_two this hb2
    -- the presentation `x` is the constant or its assumption
    have hxc : x = c ∨ x = asAxiom c := by
      rcases hat1 with h0 | h0 | ⟨h0, -⟩ <;> rw [hx] at h0 <;> cases h0
      · exact .inl rfl
      · exact .inr rfl
    rcases hb with hb1 | hb2'
    · refine ⟨_, at?_of_lvl1 hlb hs hb1 hx (fun p hp => ?_), ?_, ?_⟩
      · exact Nat.le_trans (gateOk_iff.mp hg p hp) (hle p.1)
      · rcases hv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> split <;> rfl
      · intro hcc
        rw [hc] at hcc
        have hcc' : c = ci := Option.some.inj hcc
        subst hcc'
        rcases hv with ⟨hvo, hci⟩ | ⟨hvc, hci⟩
        · rw [ite_eq_left (hgmono _ hvo), hci]
        · -- a closed full gate is a non-empty one: the constant is stored, and an assumption
          have hjv : j < (S.slot h).exp.v1.size := by
            obtain ⟨-, -, -, h4, -⟩ := shapeOk_spec (hR.shape hh)
            have hjp : j < (S.slot h).prv.priv.size := by
              rcases Nat.lt_or_ge j (S.slot h).prv.priv.size with h' | h'
              · exact h'
              · rw [Array.getElem?_eq_none h'] at hc; cases hc
            rw [← h4]; exact hjp
          rcases hv1 _ (Array.getElem?_eq_getElem hjv) with he | ⟨hst, -⟩
          · rw [Array.getElem?_eq_getElem hjv] at hvc
            simp only [Option.getD_some] at hvc
            rw [Array.isEmpty_iff.mp he, gateOk_nil] at hvc
            cases hvc
          · have hxc : x = c := by
              have := hstiff.mp hst
              rw [hx] at this
              exact Option.some.inj (Option.some.inj this)
            subst hxc
            split
            · rfl
            · exact hci.symm
    · refine ⟨c, at?_of_lvl2 hlb hs hb2' hc, ?_, fun hcc => ?_⟩
      · rw [hcn]
      · rw [hc] at hcc; exact Option.some.inj hcc
  · have hb : lvlAt (S.lvl b) h = 2 := by
      have := hle h; rw [ha2] at this
      exact u8_two this hb2
    refine ⟨c, at?_of_lvl2 hlb hs hb hc, hcn, fun hcc => ?_⟩
    rw [hc] at hcc; exact Option.some.inj hcc

/-! ## Reads, read alike -/

/-- **A name module `i` reads as its home `h` does**: `h` stores it, `i`'s
context stores it, and both resolve it alike. -/
def GoodAt (S : Store) (M : Array ModData) (i h : Nat) (d : Name) : Prop :=
  ((devOf S M h).own.find? d).isSome = true ∧ ((devOf S M i).context.find? d).isSome = true ∧
  (devOf S M i).res d = (devOf S M h).res d

theorem readsAlike_find? {i h : Nat} {d : Name} (hg : GoodAt S M i h d) :
    ((readsAlike (devOf S M) i h).find? d).isSome = true := by
  obtain ⟨h1, h2, h3⟩ := hg
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h1
  have hcn : c.name = d := by
    unfold Env.find? at hc
    have := List.find?_some hc
    exact beq_iff_eq.mp this
  have hmem : c ∈ (devOf S M h).own.consts := by
    unfold Env.find? at hc; exact List.mem_of_find?_eq_some hc
  unfold readsAlike Env.find?
  simp only
  rw [List.find?_filter, List.find?_isSome]
  refine ⟨c, hmem, ?_⟩
  rw [hcn]
  have h2' := h2
  unfold Env.find? at h2'
  rw [List.find?_isSome] at h2'
  obtain ⟨x, hx, hxn⟩ := h2'
  simp [h3]
  exact ⟨x, hx, by simpa using hxn⟩

theorem lt_size_of_lvl {l : ByteArray} {x : Nat} (hx : lvlAt l x ≠ 0) : x < l.size := by
  rcases Nat.lt_or_ge x l.size with h | h
  · exact h
  · unfold lvlAt at hx; simp [Nat.not_lt.mpr h] at hx

/-- A module's levels: every loaded module is loaded at level 1 or 2. -/
theorem RunOk.lvl_le2 (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) (x : Nat) :
    lvlAt (S.lvl i) x ≤ 2 := by
  by_cases hx : x < (S.lvl i).size
  · by_cases hz : lvlAt (S.lvl i) x = 0
    · rw [hz]; decide
    · exact (localOk_lvl (hR.locals i hi) hx hz).2.1
  · unfold lvlAt; simp [hx]

theorem RunOk.lvl_lt (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) {x : Nat}
    (hx : lvlAt (S.lvl i) x ≠ 0) : x < i := by
  have hxs : x < (S.lvl i).size := lt_size_of_lvl hx
  exact (localOk_lvl (hR.locals i hi) hxs hx).1

/-- A visible alternate gives the name a constant in the context. -/
theorem ctx_isSome_of_vis {i : Nat} {d : Name} {x : Nat × Nat} {c : ConstantInfo}
    (hx : x ∈ S.alts d) (hat : (S.mb i).at? x.1 x.2 = some c) (hn : c.name = d) :
    ((ctxOf (S.mb i)).find? d).isSome = true := by
  rw [ctxOf_find?]
  have := pickIn_isSome (mb := S.mb i) (l := (S.mb i).alts d) (by rw [Store.alts_mb]; exact hx)
    hat hn
  unfold MBase.find?
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp this
  unfold MBase.pick?
  rw [hp]
  obtain ⟨_, _, _⟩ := p
  rfl

/-- **The common end of a good read**: a target the home resolves the name
to, visible in the reading module. -/
theorem RunOk.good_of_vis (hR : RunOk mode S M) {i h : Nat} (hi : i < M.size) (hh : h < M.size)
    {d : Name} {t : Nat × Nat} (ht : target h M[h].fe d = some t) (hx : t ∈ S.alts d)
    {c : ConstantInfo} (hat : (S.mb i).at? t.1 t.2 = some c) (hn : c.name = d) :
    GoodAt S M i h d := by
  have hctx := ctx_isSome_of_vis hx hat hn
  refine ⟨?_, ?_, ?_⟩
  · rw [devOf_of_lt hh]
    show ((envAt M[h].fe (ctxOf (S.mb h))).find? d).isSome = true
    rw [← hR.fe_find? hh]
    rcases hR.target_cases hh ht with ⟨-, p, -, -, hf⟩ | ⟨-, ci, -, hf⟩ <;> rw [hf] <;> rfl
  · rw [devOf_of_lt hi]; exact hctx
  · rw [devOf_of_lt hi, devOf_of_lt hh]
    show resOf S i M[i] d = resOf S h M[h] d
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (by rw [ctxOf_find?] at hctx; exact hctx)
    obtain ⟨h₀, j₀, hp⟩ := MBase.find?_some hy
    have hki := hR.key_pick hi hp hx hat hn
    have hli : resOf S i M[i] d = S.keyAt h₀ j₀ d := by unfold resOf; rw [hp]
    rw [hli, ← hki]
    rcases hR.target_cases hh ht with ⟨ht1, p, hp', hpn, -⟩ | ⟨-, ci, hph, -⟩
    · obtain ⟨t1, t2⟩ := t
      simp only at ht1 hp' ⊢
      subst ht1
      rw [← hpn, hR.res_home hh hp']
    · unfold resOf; rw [hph]

theorem RunOk.good2 (hR : RunOk mode S M) {i h : Nat} (hi : i < M.size) (hh : h < M.size)
    (h2 : lvlAt (S.lvl i) h = 2) {d : Name} (hr : read2Ok S h M[h].fe d = true) :
    GoodAt S M i h d := by
  unfold read2Ok at hr
  cases ht : target h M[h].fe d with
  | none => rw [ht] at hr; cases hr
  | some t =>
    rw [ht] at hr
    obtain ⟨t1, t2⟩ := t
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hr
    have hs : ∀ x, x < M.size → x < S.slots.size := fun x hx => by rw [hR.slots]; exact hx
    have hli : h < (S.lvl i).size := lt_size_of_lvl (by rw [h2]; decide)
    rcases hR.target_cases hh ht with ⟨ht1, p, hp, hpn, -⟩ | ⟨hne, ci, hph, -⟩
    · simp only at ht1 hp
      subst ht1
      have hx : (t1, t2) ∈ S.alts d := by
        rcases hr with h' | h'
        · exact absurd rfl h'
        · exact List.contains_iff_mem.mp h'
      exact hR.good_of_vis hi hh ht hx (at?_of_lvl2 hli (hs _ hh) h2 hp) hpn
    · simp only at hne hph
      obtain ⟨hn, hxa, hat⟩ := MBase.pick?_some hph
      have hlt : t1 < h := by
        obtain ⟨-, hlv⟩ := lvl_of_at? hat
        exact hR.lvl_lt hh (by rcases hlv with h' | h' <;> rw [h'] <;> decide)
      have ht1 : t1 < M.size := Nat.lt_trans hlt hh
      have hle : ∀ x, lvlAt (S.lvl h) x ≤ lvlAt (S.lvl i) x := by
        intro x
        by_cases hx : x < (S.lvl h).size
        · exact (localOk_lvl (hR.locals i hi) hli (by rw [h2]; decide)).2.2.choose_spec.2.1 h2 x hx
        · have : lvlAt (S.lvl h) x = 0 := by unfold lvlAt; simp [hx]
          rw [this]; exact UInt8.zero_le
      obtain ⟨ci', hat', hn', -⟩ := hR.at?_mono hat ht1 hle (hR.lvl_le2 hi t1)
        (by rw [hR.lvls h hh, hR.lvls i hi]; exact Nat.le_refl _)
      rw [Store.alts_mb] at hxa
      exact hR.good_of_vis hi hh ht hxa hat' (hn'.trans hn)

theorem RunOk.good1 (hR : RunOk mode S M) {i h : Nat} (hi : i < M.size) (hh : h < M.size)
    (h1 : lvlAt (S.lvl i) h = 1) {G : Array (Nat × UInt8)}
    (hG : ∀ p ∈ G, lvlAt (S.lvl i) p.1 ≥ p.2) {d : Name}
    (hr : read1Ok S h M[h].fe M[h].unit G d = true) : GoodAt S M i h d := by
  have hli : h < (S.lvl i).size := lt_size_of_lvl (by rw [h1]; decide)
  obtain ⟨-, -, u, hu, -, hfp⟩ := localOk_lvl (hR.locals i hi) hli (by rw [h1]; decide)
  have hu' : u = M[h].unit := by
    simp only [Array.getElem?_map, Array.getElem?_eq_getElem hh, Option.map_some,
      Option.some.injEq] at hu
    exact hu.symm
  subst hu'
  have hfp' := hfp (by rw [h1]; decide)
  have hinG : ∀ p, (M[h].unit.fp1.contains p || G.contains p) = true → lvlAt (S.lvl i) p.1 ≥ p.2 := by
    intro p hp
    rcases Bool.or_eq_true_iff.mp hp with h' | h'
    · exact hfp' p (Array.mem_of_contains_eq_true h')
    · exact hG p (Array.mem_of_contains_eq_true h')
  have hs : ∀ x, x < M.size → x < S.slots.size := fun x hx => by rw [hR.slots]; exact hx
  unfold read1Ok at hr
  cases ht : target h M[h].fe d with
  | none => rw [ht] at hr; cases hr
  | some t =>
    rw [ht] at hr
    obtain ⟨t1, t2⟩ := t
    simp only at hr
    rcases hR.target_cases hh ht with ⟨ht1, p, hp, hpn, -⟩ | ⟨hne, ci, hph, -⟩
    · simp only at ht1 hp
      subst ht1
      simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hr
      obtain ⟨⟨hxa, hat1⟩, hg⟩ := hr
      rw [← hR.slot t1 hh] at hat1 hg
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hat1
      have ha' : (S.slot t1).exp.at1[t2]? = some (some a) := by
        cases hq : (S.slot t1).exp.at1[t2]? with
        | none => rw [hq] at ha; cases ha
        | some x => rw [hq] at ha; cases x <;> simp_all
      have hat := at?_of_lvl1 hli (hs _ hh) h1 ha' (fun q hq => hinG q
        (by rw [Array.all_eq_true'] at hg; exact hg q hq))
      obtain ⟨-, -, -, -, -, -, -, hj⟩ := shapeOk_spec (hR.shape hh)
      obtain ⟨-, -, hat1', -⟩ := hj t2 p hp
      have hna : a.name = d := by
        rcases hat1' with h0 | h0 | ⟨h0, -⟩ <;> rw [ha'] at h0 <;> cases h0
        · exact hpn
        · exact hpn
      refine hR.good_of_vis hi hh ht (List.contains_iff_mem.mp hxa) hat ?_
      split <;> exact hna
    · simp only at hne hph
      simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        Bool.or_eq_true, bne_iff_ne, ne_eq] at hr
      obtain ⟨hin, hgate⟩ := hr
      obtain ⟨hn, hxa, hatH⟩ := MBase.pick?_some hph
      have hlt : t1 < h := by
        obtain ⟨-, hlv⟩ := lvl_of_at? hatH
        exact hR.lvl_lt hh (by rcases hlv with h' | h' <;> rw [h'] <;> decide)
      have ht1 : t1 < M.size := Nat.lt_trans hlt hh
      obtain ⟨c, hc, hcn⟩ := hR.at?_name hatH ht1
      have hneed := hinG _ (Bool.or_eq_true_iff.mpr hin)
      simp only at hneed
      rw [Store.alts_mb] at hxa
      have hli1 : t1 < (S.lvl i).size := by
        rw [hR.lvls i hi]; exact ht1
      rcases u8_one_two (Nat.le_trans (by unfold Store.needAt; split <;> decide) hneed)
          (hR.lvl_le2 hi t1) with hl1 | hl2
      · -- loaded at the exported level: then the target is presented there
        have hna : S.needAt t1 t2 = 1 := by
          have := hneed; rw [hl1] at this
          unfold Store.needAt at this ⊢
          split at this <;> first | rfl | simp at this
        unfold Store.needAt at hna
        split at hna
        · rename_i a ha
          have hat := at?_of_lvl1 hli1 (hs _ ht1) hl1 ha (fun q hq => hinG q (by
            rcases hgate with h' | h'
            · unfold Store.needAt at h'; rw [ha] at h'; exact absurd rfl h'
            · rw [Array.all_eq_true'] at h'; exact h' q hq))
          obtain ⟨-, -, -, -, -, -, -, hj⟩ := shapeOk_spec (hR.shape ht1)
          obtain ⟨-, -, hat1', -⟩ := hj t2 c hc
          have hna' : a.name = d := by
            rcases hat1' with h0 | h0 | ⟨h0, -⟩ <;> rw [ha] at h0 <;> cases h0
            · rw [hcn, hn]
            · show c.name = d; rw [hcn, hn]
          refine hR.good_of_vis hi hh ht hxa hat ?_
          split <;> exact hna'
        · cases hna
      · exact hR.good_of_vis hi hh ht hxa (at?_of_lvl2 hli1 (hs _ ht1) hl2 hc) (hcn.trans hn)

/-! ## Full reads -/

/-- Two installed constants of one module with one name are one. -/
theorem RunOk.priv_inj (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {j j' : Nat}
    {c c' : ConstantInfo} (hc : (S.slot h).prv.priv[j]? = some c)
    (hc' : (S.slot h).prv.priv[j']? = some c') (hn : c.name = c'.name) : j = j' := by
  rw [hR.slot h hh, hR.priv h hh] at hc hc'
  simp only [List.getElem?_toArray] at hc hc'
  have hnd := hR.nodupOwn hh
  unfold NodupNames envAt at hnd
  simp only [List.map_append] at hnd
  have hnd' : (M[h].fe.env.consts.reverse.map (·.name)).Nodup := by
    rw [List.map_reverse]
    exact List.pairwise_reverse.mpr ((List.nodup_append.mp hnd).1.imp fun h => Ne.symm h)
  have hj : j < (M[h].fe.env.consts.reverse.map (·.name)).length := by
    rcases Nat.lt_or_ge j M[h].fe.env.consts.reverse.length with h' | h'
    · simpa using h'
    · rw [List.getElem?_eq_none h'] at hc; cases hc
  refine (hnd'.getElem?_inj hj).mp ?_
  rw [List.getElem?_map, List.getElem?_map, hc, hc']
  simp [hn]

/-- A constant that is not a proof has the qualified name of its home. -/
theorem RunOk.keyAt_qual (hR : RunOk mode S M) {h j : Nat} (hh : h < M.size) {c : ConstantInfo}
    (hc : (S.slot h).prv.priv[j]? = some c)
    (hk : proofKind c = false) (n : Name) : S.keyAt h j n = .qual h n := by
  obtain ⟨-, -, -, -, -, -, -, hj⟩ := shapeOk_spec (hR.shape hh)
  obtain ⟨-, -, -, -, -, hpf, hpk, -⟩ := hj j c hc
  unfold Store.keyAt keyOfSlot
  rw [hpf, hc]
  cases hf : M[h].flags.contains c.name with
  | false => rfl
  | true => rw [hpk hf] at hk; cases hk

/-- **A visible alternate that is not a proof is the first visible one.** -/
theorem RunOk.pick_of_vis (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) {d : Name}
    {t : Nat × Nat} (hx : t ∈ S.alts d) (ht : t.1 < M.size) {c : ConstantInfo}
    (hat : (S.mb i).at? t.1 t.2 = some c) (hn : c.name = d)
    (hpc : (S.slot t.1).prv.priv[t.2]? = some c) (hk : proofKind c = false) :
    (ctxOf (S.mb i)).find? d = some c := by
  have hctx := ctx_isSome_of_vis hx hat hn
  rw [ctxOf_find?] at hctx ⊢
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hctx
  obtain ⟨h₀, j₀, hp⟩ := MBase.find?_some hy
  have hkey := hR.key_pick hi hp hx hat hn
  rw [hR.keyAt_qual ht hpc hk] at hkey
  obtain ⟨hyn, -, hyat⟩ := MBase.pick?_some hp
  obtain ⟨-, hlv⟩ := lvl_of_at? hyat
  have h0 : h₀ < M.size := Nat.lt_trans (hR.lvl_lt hi
    (by rcases hlv with h' | h' <;> rw [h'] <;> decide)) hi
  obtain ⟨c₀, hc₀, hc₀n⟩ := hR.at?_name hyat h0
  -- its qualified name is the home's and the name: the same module
  have hh0 : h₀ = t.1 := by
    unfold Store.keyAt keyOfSlot at hkey
    rw [hc₀] at hkey
    revert hkey
    cases (S.slot h₀).exp.prf[j₀]? with
    | none => intro hk; cases hk; rfl
    | some b =>
      cases b with
      | true => intro hk; cases hk
      | false => intro hk; cases hk; rfl
  subst hh0
  have hj : j₀ = t.2 := hR.priv_inj ht hc₀ hpc (by rw [hc₀n, hyn, hn])
  subst hj
  rw [hat] at hyat
  have : y = c := (Option.some.inj hyat).symm
  subst this
  unfold MBase.find?
  rw [hp]

theorem Want.ok_proofKind {w : Want} {c : ConstantInfo} (h : w.ok c = true) :
    proofKind c = false := by
  cases w <;> cases c <;> simp_all [Want.ok, proofKind]

theorem Want.ok_asAxiom {w : Want} {c : ConstantInfo} : w.ok (asAxiom c) = false := by
  cases w <;> rfl

/-- A visible alternate of a wanted kind is the installed constant. -/
theorem RunOk.at?_want (hR : RunOk mode S M) {i h j : Nat} {ci : ConstantInfo} {w : Want}
    (hat : (S.mb i).at? h j = some ci) (hh : h < M.size) (hw : w.ok ci = true) :
    (S.slot h).prv.priv[j]? = some ci := by
  obtain ⟨c, hc, hci⟩ := hR.at?_home hat hh
  rcases hci with rfl | ⟨rfl, -⟩
  · exact hc
  · rw [Want.ok_asAxiom] at hw; cases hw

theorem RunOk.full2 (hR : RunOk mode S M) {i h : Nat} (hi : i < M.size) (hh : h < M.size)
    (h2 : lvlAt (S.lvl i) h = 2) {w : Want} {d : Name}
    (hr : full2Ok S h M[h].fe M[h].unit w d = true) :
    ∃ x, (ctxOf (S.mb i)).find? d = some x ∧ w.ok x = true := by
  have hs : ∀ x, x < M.size → x < S.slots.size := fun x hx => by rw [hR.slots]; exact hx
  have hli : h < (S.lvl i).size := lt_size_of_lvl (by rw [h2]; decide)
  unfold full2Ok at hr
  cases ht : target h M[h].fe d with
  | none => rw [ht] at hr; cases hr
  | some t =>
    rw [ht] at hr
    obtain ⟨t1, t2⟩ := t
    simp only at hr
    rcases hR.target_cases hh ht with ⟨ht1, p, hp, hpn, -⟩ | ⟨hne, ci, hph, -⟩
    · simp only at ht1 hp
      subst ht1
      simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hr
      obtain ⟨hxa, hk⟩ := hr
      rw [← hR.slot t1 hh, hp] at hk
      simp only [Option.map_some, Option.getD_some] at hk
      exact ⟨p, hR.pick_of_vis hi (List.contains_iff_mem.mp hxa) hh
        (at?_of_lvl2 hli (hs _ hh) h2 hp) hpn hp (Want.ok_proofKind hk), hk⟩
    · simp only at hne hph
      simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte] at hr
      rw [(hR.finalCanon hh).base] at hr
      simp only at hr
      rw [hph] at hr
      simp only at hr
      obtain ⟨hn, hxa, hatH⟩ := MBase.pick?_some hph
      have hlt : t1 < h := by
        obtain ⟨-, hlv⟩ := lvl_of_at? hatH
        exact hR.lvl_lt hh (by rcases hlv with h' | h' <;> rw [h'] <;> decide)
      have ht1 : t1 < M.size := Nat.lt_trans hlt hh
      have hpc := hR.at?_want hatH ht1 hr
      have hle : ∀ x, lvlAt (S.lvl h) x ≤ lvlAt (S.lvl i) x := by
        intro x
        by_cases hx : x < (S.lvl h).size
        · exact (localOk_lvl (hR.locals i hi) hli (by rw [h2]; decide)).2.2.choose_spec.2.1 h2 x hx
        · have : lvlAt (S.lvl h) x = 0 := by unfold lvlAt; simp [hx]
          rw [this]; exact UInt8.zero_le
      obtain ⟨ci', hat', -, hfull⟩ := hR.at?_mono hatH ht1 hle (hR.lvl_le2 hi t1)
        (by rw [hR.lvls h hh, hR.lvls i hi]; exact Nat.le_refl _)
      have := hfull hpc
      subst this
      rw [Store.alts_mb] at hxa
      exact ⟨ci', hR.pick_of_vis hi hxa ht1 hat' hn hpc (Want.ok_proofKind hr), hr⟩

theorem RunOk.full1 (hR : RunOk mode S M) {i h : Nat} (hi : i < M.size) (hh : h < M.size)
    (h1 : lvlAt (S.lvl i) h = 1) {G : Array (Nat × UInt8)}
    (hG : ∀ p ∈ G, lvlAt (S.lvl i) p.1 ≥ p.2) {w : Want} {d : Name}
    (hr : full1Ok S h M[h].fe M[h].unit G w d = true) :
    ∃ x, (ctxOf (S.mb i)).find? d = some x ∧ w.ok x = true := by
  have hli : h < (S.lvl i).size := lt_size_of_lvl (by rw [h1]; decide)
  obtain ⟨-, -, u, hu, -, hfp⟩ := localOk_lvl (hR.locals i hi) hli (by rw [h1]; decide)
  have hu' : u = M[h].unit := by
    simp only [Array.getElem?_map, Array.getElem?_eq_getElem hh, Option.map_some,
      Option.some.injEq] at hu
    exact hu.symm
  subst hu'
  have hfp' := hfp (by rw [h1]; decide)
  have hinG : ∀ p, (M[h].unit.fp1.contains p || G.contains p) = true → lvlAt (S.lvl i) p.1 ≥ p.2 := by
    intro p hp
    rcases Bool.or_eq_true_iff.mp hp with h' | h'
    · exact hfp' p (Array.mem_of_contains_eq_true h')
    · exact hG p (Array.mem_of_contains_eq_true h')
  have hs : ∀ x, x < M.size → x < S.slots.size := fun x hx => by rw [hR.slots]; exact hx
  unfold full1Ok at hr
  cases ht : target h M[h].fe d with
  | none => rw [ht] at hr; cases hr
  | some t =>
    rw [ht] at hr
    obtain ⟨t1, t2⟩ := t
    simp only at hr
    rcases hR.target_cases hh ht with ⟨ht1, p, hp, hpn, -⟩ | ⟨hne, ci, hph, -⟩
    · simp only at ht1 hp
      subst ht1
      simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hr
      obtain ⟨⟨⟨hxa, hst⟩, hk⟩, hg⟩ := hr
      rw [← hR.slot t1 hh] at hst hk hg
      rw [hp] at hk
      simp only [Option.map_some, Option.getD_some] at hk
      obtain ⟨-, -, -, -, -, -, -, hj⟩ := shapeOk_spec (hR.shape hh)
      obtain ⟨st, hst', -, hstiff, -⟩ := hj t2 p hp
      rw [hst'] at hst
      simp only [Option.getD_some] at hst
      have ha := hstiff.mp hst
      rw [Array.all_eq_true'] at hg
      have hat := at?_of_lvl1 hli (hs _ hh) h1 ha (fun q hq => hinG q (hg q
        (Array.mem_append_left _ hq)))
      rw [ite_eq_left (gateOk_iff.mpr fun q hq => hinG q (hg q (Array.mem_append_right _ hq)))]
        at hat
      exact ⟨p, hR.pick_of_vis hi (List.contains_iff_mem.mp hxa) hh hat hpn hp
        (Want.ok_proofKind hk), hk⟩
    · simp only at hne hph
      simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte] at hr
      rw [(hR.finalCanon hh).base] at hr
      simp only at hr
      rw [hph] at hr
      simp only [Bool.and_eq_true] at hr
      obtain ⟨hw, hrest⟩ := hr
      obtain ⟨hn, hxa, hatH⟩ := MBase.pick?_some hph
      have hlt : t1 < h := by
        obtain ⟨-, hlv⟩ := lvl_of_at? hatH
        exact hR.lvl_lt hh (by rcases hlv with h' | h' <;> rw [h'] <;> decide)
      have ht1 : t1 < M.size := Nat.lt_trans hlt hh
      have hpc := hR.at?_want hatH ht1 hw
      have hli1 : t1 < (S.lvl i).size := by rw [hR.lvls i hi]; exact ht1
      rw [Store.alts_mb] at hxa
      have hk := Want.ok_proofKind hw
      split at hrest
      · rename_i hsto
        simp only [Bool.and_eq_true] at hrest
        obtain ⟨hin1, hgate⟩ := hrest
        have hl1 := hinG _ hin1
        simp only at hl1
        rcases u8_one_two hl1 (hR.lvl_le2 hi t1) with hl | hl
        · obtain ⟨-, -, -, -, -, -, -, hj⟩ := shapeOk_spec (hR.shape ht1)
          obtain ⟨st, hst', -, hstiff, -⟩ := hj t2 ci hpc
          unfold Store.storedAt at hsto
          rw [hst'] at hsto
          simp only [Option.getD_some] at hsto
          have ha := hstiff.mp hsto
          rw [Array.all_eq_true'] at hgate
          unfold Store.fullGateAt at hgate
          have hat := at?_of_lvl1 hli1 (hs _ ht1) hl ha (fun q hq => hinG q (hgate q
            (Array.mem_append_left _ hq)))
          rw [ite_eq_left (gateOk_iff.mpr fun q hq => hinG q (hgate q
            (Array.mem_append_right _ hq)))] at hat
          exact ⟨ci, hR.pick_of_vis hi hxa ht1 hat hn hpc hk, hw⟩
        · exact ⟨ci, hR.pick_of_vis hi hxa ht1 (at?_of_lvl2 hli1 (hs _ ht1) hl hpc) hn hpc hk, hw⟩
      · have hl2 := hinG _ hrest
        simp only at hl2
        have hl := u8_two hl2 (hR.lvl_le2 hi t1)
        exact ⟨ci, hR.pick_of_vis hi hxa ht1 (at?_of_lvl2 hli1 (hs _ ht1) hl hpc) hn hpc hk, hw⟩

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
