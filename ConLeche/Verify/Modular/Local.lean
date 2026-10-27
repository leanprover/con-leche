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
      (st = true → s.exp.at1[j]? = some (some ci)) ∧
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
  · intro hs
    rw [Array.getElem?_eq_getElem hj1]
    rcases hst with h | h
    · rw [hs] at h; cases h
    · rw [h]
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
           compared_own := ?_, context_le := ?_, scoping := ?_, tables := ?_, projs := ?_,
           blocks := ?_, recFam := ?_, tables_mem := ?_, res_context := ?_, res_own := ?_ }
  · rw [hd]; exact hR.below i hi
  · rw [hd]; exact ctxOf_nodup _
  · rw [hd]; intro h; cases h
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · rw [hd]; exact ctxOf_tables_mem _
  · sorry
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
