module

public import ConLeche.Verify.Driver.Loads
import ConLeche.Verify.Frontend.Olean.Files
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas

/-!
# The header fixpoint loads what `LoadsAt` derives (task #618)

`loadsAt_fixpoint`: every module the specification's `LoadsAt` derives from a header's imports is
in the header fixpoint's order, and loaded whole where the derivation loads it whole.  The
worklist keeps a demand invariant (`DemInv`): every import the root has, and every import a
placed or opened module follows at its flags, is covered at the flags it asks for (`DCov`): by
the flags of a placed module, a pending `done` item, or a pending import item that asks as much.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-- The `importAll` flag an import asks for, followed from flags `pf` under the global `g`. -/
@[expose] def lvNeed (g : Bool) (pf : LoadFlags) (j : ImportRec) : Bool :=
  g || pf.importAll && j.importAll

/-- An import is followed from flags `pf`. -/
@[expose] def lvFollow (pf : LoadFlags) (j : ImportRec) : Bool := j.isExported || pf.importAll

/-- **A module is covered at `b`**: placed, opened, or asked for by a pending import, each with
`importAll` where `b` asks it. -/
@[expose] def DCov (g : Bool) (ws : List LvWork) (st : LvState) (b : Bool) (m : Name) : Prop :=
  (∃ fl, st.flags[m]? = some fl ∧ (b = true → fl.importAll = true)) ∨
  (∃ fl, LvWork.done m fl ∈ ws ∧ (b = true → fl.importAll = true)) ∨
  (∃ pf j, LvWork.imp pf j ∈ ws ∧ j.module = m ∧ lvFollow pf j = true ∧
    (b = true → lvNeed g pf j = true))

/-- **The demand invariant** (see the module docstring). -/
structure DemInv (g : Bool) (imps0 : Array ImportRec) (ws : List LvWork) (st : LvState) :
    Prop where
  root : ∀ i ∈ imps0, DCov g ws st (g || i.importAll) i.module
  placed : ∀ (a : Name) (fl : LoadFlags) (is : Array ImportRec), st.flags[a]? = some fl → st.imports[a]? = some is → ∀ j ∈ is,
    lvFollow fl j = true → DCov g ws st (lvNeed g fl j) j.module
  opened : ∀ (a : Name) (fl : LoadFlags) (is : Array ImportRec), LvWork.done a fl ∈ ws → st.imports[a]? = some is → ∀ j ∈ is,
    lvFollow fl j = true → DCov g ws st (lvNeed g fl j) j.module

/-- Coverage moves along a step that keeps placed flags, settles or keeps `done` items, and
settles or keeps the followed import items. -/
theorem DCov.mono {g : Bool} {ws ws' : List LvWork} {st st' : LvState}
    (hf : ∀ (m : Name) (fl : LoadFlags), st.flags[m]? = some fl →
      ∃ fl', st'.flags[m]? = some fl' ∧ (fl.importAll = true → fl'.importAll = true))
    (hd : ∀ (m : Name) (fl : LoadFlags), LvWork.done m fl ∈ ws → LvWork.done m fl ∈ ws' ∨
      ∃ fl', st'.flags[m]? = some fl' ∧ (fl.importAll = true → fl'.importAll = true))
    (hi : ∀ (pf : LoadFlags) (j : ImportRec), LvWork.imp pf j ∈ ws → lvFollow pf j = true → LvWork.imp pf j ∈ ws' ∨
      (∃ fl', st'.flags[j.module]? = some fl' ∧ (lvNeed g pf j = true → fl'.importAll = true)) ∨
      ∃ fl, LvWork.done j.module fl ∈ ws' ∧ (lvNeed g pf j = true → fl.importAll = true))
    {b : Bool} {m : Name} (h : DCov g ws st b m) : DCov g ws' st' b m := by
  rcases h with ⟨fl, h1, h2⟩ | ⟨fl, h1, h2⟩ | ⟨pf, j, h1, rfl, h3, h4⟩
  · obtain ⟨fl', e1, e2⟩ := hf _ _ h1
    exact .inl ⟨fl', e1, fun hb => e2 (h2 hb)⟩
  · rcases hd _ _ h1 with e | ⟨fl', e1, e2⟩
    · exact .inr (.inl ⟨fl, e, h2⟩)
    · exact .inl ⟨fl', e1, fun hb => e2 (h2 hb)⟩
  · rcases hi _ _ h1 h3 with e | ⟨fl', e1, e2⟩ | ⟨fl', e1, e2⟩
    · exact .inr (.inr ⟨pf, j, e, rfl, h3, h4⟩)
    · exact .inl ⟨fl', e1, fun hb => e2 (h4 hb)⟩
    · exact .inr (.inl ⟨fl', e1, fun hb => e2 (h4 hb)⟩)

theorem DemInv.mono {g : Bool} {imps0 : Array ImportRec} {ws ws' : List LvWork}
    {st st' : LvState} (hI : DemInv g imps0 ws st)
    (hf : ∀ (m : Name) (fl : LoadFlags), st.flags[m]? = some fl →
      ∃ fl', st'.flags[m]? = some fl' ∧ (fl.importAll = true → fl'.importAll = true))
    (hd : ∀ (m : Name) (fl : LoadFlags), LvWork.done m fl ∈ ws → LvWork.done m fl ∈ ws' ∨
      ∃ fl', st'.flags[m]? = some fl' ∧ (fl.importAll = true → fl'.importAll = true))
    (hi : ∀ (pf : LoadFlags) (j : ImportRec), LvWork.imp pf j ∈ ws → lvFollow pf j = true → LvWork.imp pf j ∈ ws' ∨
      (∃ fl', st'.flags[j.module]? = some fl' ∧ (lvNeed g pf j = true → fl'.importAll = true)) ∨
      ∃ fl, LvWork.done j.module fl ∈ ws' ∧ (lvNeed g pf j = true → fl.importAll = true))
    (hp : ∀ (a : Name) (fl : LoadFlags) (is : Array ImportRec), st'.flags[a]? = some fl → st'.imports[a]? = some is → ∀ j ∈ is,
      lvFollow fl j = true → DCov g ws' st' (lvNeed g fl j) j.module)
    (ho : ∀ (a : Name) (fl : LoadFlags) (is : Array ImportRec), LvWork.done a fl ∈ ws' → st'.imports[a]? = some is → ∀ j ∈ is,
      lvFollow fl j = true → DCov g ws' st' (lvNeed g fl j) j.module) :
    DemInv g imps0 ws' st' :=
  ⟨fun i hi' => DCov.mono hf hd hi (hI.root i hi'), hp, ho⟩

theorem lvFlags_beq {a b : LoadFlags} (h : (a == b) = true) : a = b := by
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> first | rfl | exact absurd h (by decide)

theorem demInv_init (isM : Bool) (imps0 : Array ImportRec) :
    DemInv (!isM) imps0 (LvWork.ofImports { importAll := true, isExported := isM } imps0) {} := by
  refine ⟨fun i hi => .inr (.inr ⟨_, i, mem_ofImports.2 ⟨i, hi, rfl⟩, rfl, by simp [lvFollow],
    fun h => by simpa [lvNeed] using h⟩), fun a fl is h => by simp at h,
    fun a fl is h => ?_⟩
  obtain ⟨_, _, h⟩ := mem_ofImports.1 h; cases h

/-- **The worklist keeps the demand invariant**, to its accepting outcome. -/
theorem levelsGo_dem {sp : Roots} {fs : FS} {imps0 : Array ImportRec} {g : Bool} :
    ∀ (fuel : Nat) (ws : List LvWork) (st : LvState) {hs hs' : HS} {st' : LvState},
      (levelsGo (moduleImports sp) g fuel ws st : ModelIO _) fs hs (.ok (.ok st')) hs' →
      LvInv sp fs imps0 ws st → DemInv g imps0 ws st → DemInv g imps0 [] st'
  | _, [], st, _, _, _, h, _, hd => by
    simp only [levelsGo, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hd
  | 0, _ :: _, _, _, _, _, h, _, _ => by
    simp [levelsGo] at h
  | fuel + 1, .done m fl :: rest, st, _, _, _, h, hi, hd => by
    simp only [levelsGo] at h
    refine levelsGo_dem fuel _ _ h (lvInv_done hi) ?_
    obtain ⟨-, hnM, -⟩ := hi.done m fl List.mem_cons_self
    have hnone : st.flags[m]? = none := by
      cases hx : st.flags[m]? with
      | none => rfl
      | some _ => exact absurd ((hi.flags m).1 (by simp [hx])) hnM
    have hfl : ∀ (x : Name) (fl' : LoadFlags), st.flags[x]? = some fl' →
        ∃ fl'', (st.flags.insert m fl)[x]? = some fl'' ∧
          (fl'.importAll = true → fl''.importAll = true) := by
      intro x fl' hx
      refine ⟨fl', ?_, id⟩
      rw [Std.HashMap.getElem?_insert]
      split
      · next he => have := beq_iff_eq.1 he; subst this; rw [hnone] at hx; cases hx
      · exact hx
    have hdn : ∀ (x : Name) (fl' : LoadFlags), LvWork.done x fl' ∈ LvWork.done m fl :: rest → LvWork.done x fl' ∈ rest ∨
        ∃ fl'', (st.flags.insert m fl)[x]? = some fl'' ∧
          (fl'.importAll = true → fl''.importAll = true) := by
      intro x fl' hx
      rcases List.mem_cons.1 hx with he | he
      · cases he; exact .inr ⟨fl, by simp, id⟩
      · exact .inl he
    have him : ∀ (pf : LoadFlags) (j : ImportRec), LvWork.imp pf j ∈ LvWork.done m fl :: rest →
        LvWork.imp pf j ∈ rest := fun pf j hx => by
      rcases List.mem_cons.1 hx with he | he
      · cases he
      · exact he
    refine hd.mono (st' := ⟨st.flags.insert m fl, st.open_.erase m,
      st.order.push m, st.imports⟩) hfl hdn
      (fun pf j hx _ => .inl (him pf j hx)) ?_ ?_
    · intro a fl' is ha his j hj hfj
      simp only [Std.HashMap.getElem?_insert] at ha
      split at ha
      · next he =>
        have := beq_iff_eq.1 he; subst this; cases ha
        exact DCov.mono hfl hdn (fun pf j hx _ => .inl (him pf j hx))
          (hd.opened _ _ is List.mem_cons_self his j hj hfj)
      · exact DCov.mono hfl hdn (fun pf j hx _ => .inl (him pf j hx))
          (hd.placed a fl' is ha his j hj hfj)
    · intro a fl' is ha his j hj hfj
      exact DCov.mono hfl hdn (fun pf j hx _ => .inl (him pf j hx))
        (hd.opened a fl' is (List.mem_cons_of_mem _ ha) his j hj hfj)
  | fuel + 1, .imp pf i :: rest, st, _, _, _, h, hi, hd => by
    rw [levelsGo] at h
    split at h
    · rename_i hc
      refine levelsGo_dem fuel _ _ h (lvInv_skip hi rfl fun pf' i' he hf => ?_) ?_
      · cases he; simp [hf] at hc
      · have hk : ∀ (x : Name) (fl' : LoadFlags), LvWork.done x fl' ∈ LvWork.imp pf i :: rest → LvWork.done x fl' ∈ rest
            := fun x fl' hx => by
          rcases List.mem_cons.1 hx with he | he
          · cases he
          · exact he
        have hk2 : ∀ (pf' : LoadFlags) (j : ImportRec), LvWork.imp pf' j ∈ LvWork.imp pf i :: rest → lvFollow pf' j = true →
            LvWork.imp pf' j ∈ rest := fun pf' j hx hf => by
          rcases List.mem_cons.1 hx with he | he
          · cases he; simp only [lvFollow] at hf; simp [hf] at hc
          · exact he
        have hm := fun {b m} (h : DCov g (LvWork.imp pf i :: rest) st b m) =>
          DCov.mono (st' := st) (fun _ fl h => ⟨fl, h, id⟩) (fun x fl hx => .inl (hk x fl hx))
            (fun pf' j hx hf => .inl (hk2 pf' j hx hf)) h
        exact hd.mono (fun _ fl h => ⟨fl, h, id⟩) (fun x fl hx => .inl (hk x fl hx))
          (fun pf' j hx hf => .inl (hk2 pf' j hx hf))
          (fun a fl is ha his j hj hfj => hm (hd.placed a fl is ha his j hj hfj))
          (fun a fl is ha his j hj hfj => hm (hd.opened a fl is (List.mem_cons_of_mem _ ha) his j hj hfj))
    · rename_i hc
      have hfo : lvFollow pf i = true := by
        cases h1 : i.isExported <;> cases h2 : pf.importAll <;> simp_all [lvFollow]
      dsimp only at h
      have hk : ∀ (x : Name) (fl' : LoadFlags), LvWork.done x fl' ∈ LvWork.imp pf i :: rest → LvWork.done x fl' ∈ rest
          := fun x fl' hx => by
        rcases List.mem_cons.1 hx with he | he
        · cases he
        · exact he
      cases hold : st.flags[i.module]? with
      | some old =>
        simp only [hold] at h
        split at h
        · rename_i heq
          have hfeq := lvFlags_beq heq
          have hneed : lvNeed g pf i = true → old.importAll = true := by
            intro hn
            have := congrArg LoadFlags.importAll hfeq
            simp only at this
            rw [← this]; simp [lvNeed] at hn ⊢; simp [hn]
          have hk2 : ∀ (pf' : LoadFlags) (j : ImportRec), LvWork.imp pf' j ∈ LvWork.imp pf i :: rest → lvFollow pf' j = true →
              LvWork.imp pf' j ∈ rest ∨
              (∃ fl', st.flags[j.module]? = some fl' ∧ (lvNeed g pf' j = true → fl'.importAll = true)) ∨
              ∃ fl, LvWork.done j.module fl ∈ rest ∧ (lvNeed g pf' j = true → fl.importAll = true) :=
            fun pf' j hx _ => by
              rcases List.mem_cons.1 hx with he | he
              · cases he; exact .inr (.inl ⟨old, hold, hneed⟩)
              · exact .inl he
          have hm := fun {b m} (h : DCov g (LvWork.imp pf i :: rest) st b m) =>
            DCov.mono (st' := st) (fun _ fl h => ⟨fl, h, id⟩) (fun x fl hx => .inl (hk x fl hx))
              hk2 h
          refine levelsGo_dem fuel _ _ h (lvInv_skip hi rfl fun pf' i' he _ => by
            cases he; simp [hold]) ?_
          exact hd.mono (fun _ fl h => ⟨fl, h, id⟩) (fun x fl hx => .inl (hk x fl hx)) hk2
            (fun a fl is ha his j hj hfj => hm (hd.placed a fl is ha his j hj hfj))
            (fun a fl is ha his j hj hfj => hm (hd.opened a fl is (List.mem_cons_of_mem _ ha) his j hj hfj))
        · refine levelsGo_dem fuel _ _ h (lvInv_bump hi hold) ?_
          generalize hfl' : ({ importAll := (g || pf.importAll && i.importAll) || old.importAll,
                               isExported := (pf.isExported && i.isExported) || old.isExported } :
                               LoadFlags) = fl'
          generalize hisd : (st.imports[i.module]?).getD #[] = is
          have hfl'a : fl'.importAll = ((g || pf.importAll && i.importAll) || old.importAll) := by
            rw [← hfl']
          let ws' := LvWork.ofImports fl' is ++ rest
          let st' : LvState := ⟨st.flags.insert i.module fl', st.open_, st.order, st.imports⟩
          have hfl : ∀ (x : Name) (fl₀ : LoadFlags), st.flags[x]? = some fl₀ →
              ∃ fl'', st'.flags[x]? = some fl'' ∧ (fl₀.importAll = true → fl''.importAll = true) := by
            intro x fl₀ hx
            show ∃ fl'', (st.flags.insert i.module fl')[x]? = some fl'' ∧ _
            rw [Std.HashMap.getElem?_insert]
            split
            · next he =>
              have := beq_iff_eq.1 he; subst this
              rw [hold] at hx; cases hx
              exact ⟨fl', rfl, fun h => by rw [hfl'a]; simp [h]⟩
            · exact ⟨fl₀, hx, id⟩
          have hdn : ∀ (x : Name) (fl₀ : LoadFlags), LvWork.done x fl₀ ∈ LvWork.imp pf i :: rest → LvWork.done x fl₀ ∈ ws' ∨
              ∃ fl'', st'.flags[x]? = some fl'' ∧ (fl₀.importAll = true → fl''.importAll = true) :=
            fun x fl₀ hx => .inl (List.mem_append_right _ (hk x fl₀ hx))
          have him : ∀ (pf' : LoadFlags) (j : ImportRec), LvWork.imp pf' j ∈ LvWork.imp pf i :: rest → lvFollow pf' j = true →
              LvWork.imp pf' j ∈ ws' ∨
              (∃ fl'', st'.flags[j.module]? = some fl'' ∧
                (lvNeed g pf' j = true → fl''.importAll = true)) ∨
              ∃ fl₀, LvWork.done j.module fl₀ ∈ ws' ∧ (lvNeed g pf' j = true → fl₀.importAll = true) :=
            fun pf' j hx _ => by
              rcases List.mem_cons.1 hx with he | he
              · cases he
                refine .inr (.inl ⟨fl', ?_, fun hn => ?_⟩)
                · show (st.flags.insert i.module fl')[i.module]? = some fl'
                  simp
                · rw [hfl'a]; simp [lvNeed] at hn; simp [hn]
              · exact .inl (List.mem_append_right _ he)
          have hm := fun {b m} (h : DCov g (LvWork.imp pf i :: rest) st b m) =>
            DCov.mono hfl hdn him h
          refine hd.mono hfl hdn him (fun a fl is' ha his j hj hfj => ?_)
            (fun a fl is' ha his j hj hfj => ?_)
          · change (st.flags.insert i.module fl')[a]? = some fl at ha
            change st.imports[a]? = some is' at his
            rw [Std.HashMap.getElem?_insert] at ha
            split at ha
            · next he =>
              have := beq_iff_eq.1 he; subst this; cases ha
              rw [his] at hisd
              simp only [Option.getD_some] at hisd
              subst hisd
              exact .inr (.inr ⟨fl', j, List.mem_append_left _ (mem_ofImports.2 ⟨j, hj, rfl⟩),
                rfl, hfj, id⟩)
            · exact hm (hd.placed a fl is' ha his j hj hfj)
          · rcases List.mem_append.1 ha with ha | ha
            · obtain ⟨_, _, h⟩ := mem_ofImports.1 ha; cases h
            · exact hm (hd.opened a fl is' (List.mem_cons_of_mem _ ha) his j hj hfj)
      | none =>
        simp only [hold] at h
        split at h
        · simp at h
        · rename_i hnot
          simp only [ModelIO.bind_ok] at h
          obtain ⟨r, _, hr, h⟩ := h
          rcases r with e | is
          · simp at h
          · have hnot' : st.open_.contains i.module = false := by simpa using hnot
            refine levelsGo_dem fuel _ _ h (lvInv_open hi hold hnot' ⟨_, _, hr⟩) ?_
            generalize hfl : ({ importAll := g || pf.importAll && i.importAll,
                                isExported := pf.isExported && i.isExported } : LoadFlags) = fl
            have hfla : fl.importAll = lvNeed g pf i := by rw [← hfl]; rfl
            let ws' := LvWork.ofImports fl is ++ LvWork.done i.module fl :: rest
            let st' : LvState := ⟨st.flags, st.open_.insert i.module, st.order,
              st.imports.insert i.module is⟩
            have hflg : ∀ (x : Name) (fl₀ : LoadFlags), st.flags[x]? = some fl₀ →
                ∃ fl'', st'.flags[x]? = some fl'' ∧ (fl₀.importAll = true → fl''.importAll = true) :=
              fun x fl₀ hx => ⟨fl₀, hx, id⟩
            have hdn : ∀ (x : Name) (fl₀ : LoadFlags), LvWork.done x fl₀ ∈ LvWork.imp pf i :: rest → LvWork.done x fl₀ ∈ ws' ∨
                ∃ fl'', st'.flags[x]? = some fl'' ∧ (fl₀.importAll = true → fl''.importAll = true) :=
              fun x fl₀ hx => .inl (List.mem_append_right _ (List.mem_cons_of_mem _ (hk x fl₀ hx)))
            have him : ∀ (pf' : LoadFlags) (j : ImportRec), LvWork.imp pf' j ∈ LvWork.imp pf i :: rest → lvFollow pf' j = true →
                LvWork.imp pf' j ∈ ws' ∨
                (∃ fl'', st'.flags[j.module]? = some fl'' ∧
                  (lvNeed g pf' j = true → fl''.importAll = true)) ∨
                ∃ fl₀, LvWork.done j.module fl₀ ∈ ws' ∧
                  (lvNeed g pf' j = true → fl₀.importAll = true) :=
              fun pf' j hx _ => by
                rcases List.mem_cons.1 hx with he | he
                · cases he
                  exact .inr (.inr ⟨fl, List.mem_append_right _ List.mem_cons_self,
                    fun hn => by rw [hfla]; exact hn⟩)
                · exact .inl (List.mem_append_right _ (List.mem_cons_of_mem _ he))
            have hm := fun {b m} (h : DCov g (LvWork.imp pf i :: rest) st b m) =>
              DCov.mono hflg hdn him h
            refine hd.mono hflg hdn him (fun a fl₀ is' ha his j hj hfj => ?_)
              (fun a fl₀ is' ha his j hj hfj => ?_)
            · change st.flags[a]? = some fl₀ at ha
              change (st.imports.insert i.module is)[a]? = some is' at his
              rw [Std.HashMap.getElem?_insert] at his
              split at his
              · next he =>
                have := beq_iff_eq.1 he; subst this; rw [hold] at ha; cases ha
              · exact hm (hd.placed a fl₀ is' ha his j hj hfj)
            · change (st.imports.insert i.module is)[a]? = some is' at his
              rcases List.mem_append.1 ha with ha | ha
              · obtain ⟨_, _, h⟩ := mem_ofImports.1 ha; cases h
              rcases List.mem_cons.1 ha with ha | ha
              · cases ha
                simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at his
                subst his
                exact .inr (.inr ⟨_, j, List.mem_append_left _ (mem_ofImports.2 ⟨j, hj, rfl⟩),
                  rfl, hfj, id⟩)
              · have hne : a ≠ i.module := by
                  rintro rfl
                  have := (hi.done _ fl₀ (List.mem_cons_of_mem _ ha)).1
                  rw [hnot'] at this; cases this
                rw [Std.HashMap.getElem?_insert] at his
                have hb : (i.module == a) = false := by simpa using Ne.symm hne
                rw [hb] at his
                exact hm (hd.opened a fl₀ is' (List.mem_cons_of_mem _ ha) his j hj hfj)

/-- **The header fixpoint loads what `LoadsAt` derives**, whole where it derives a whole load. -/
theorem loadsAt_fixpoint {sp : Roots} {fs : FS} {isM : Bool} {imps0 : Array ImportRec}
    {ld : HeaderLoads}
    (h : ModelIO.CanGive (headerFixpoint (moduleImports sp) isM imps0) fs (.ok ld))
    {m : Name} {all : Bool} (hl : LoadsAt sp fs (!isM) imps0 m all) :
    ∃ k : Nat, ld.order[k]? = some m ∧ (all = true → ((ld.flags[k]?).getD (default : LoadFlags)).importAll = true) := by
  obtain ⟨_, _, h⟩ := h
  simp only [headerFixpoint, ModelIO.bind_ok] at h
  obtain ⟨r, _, hr, h⟩ := h
  rcases r with e | st
  · simp at h
  simp only [ModelIO.pure_iff, Except.ok.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hi := levelsGo_inv _ _ _ hr (lvInv_init isM imps0)
  have hd := levelsGo_dem _ _ _ hr (lvInv_init isM imps0) (demInv_init isM imps0)
  have hfin : ∀ {b x}, DCov (!isM) [] st b x →
      ∃ fl, st.flags[x]? = some fl ∧ (b = true → fl.importAll = true) := by
    rintro b x (h | ⟨_, h, _⟩ | ⟨_, _, h, _⟩)
    · exact h
    · cases h
    · cases h
  have key : ∃ fl, st.flags[m]? = some fl ∧ (all = true → fl.importAll = true) := by
    induction hl with
    | @root i hi0 => exact hfin (hd.root i hi0)
    | @step a all' d i _ hv hi' hfol ih =>
      obtain ⟨fl, hfa, hall⟩ := ih
      have ham : a ∈ st.order := (hi.flags a).1 (by simp [hfa])
      obtain ⟨is, his⟩ := Option.isSome_iff_exists.1 (hi.ordImps a ham)
      have hmi := (hi.imps a is his).2
      obtain ⟨_, _, hrv⟩ := readView_of_viewOf hv
      have hview := moduleImports_of_view hrv
      obtain rfl : is = d.imports := moduleImports_canGive_unique hmi hview.canGive
      have hf : lvFollow fl i = true := by
        simp only [lvFollow]
        cases he : i.isExported
        · simp only [he, Bool.false_or] at hfol ⊢; exact hall hfol
        · rfl
      obtain ⟨fl2, h2, h2a⟩ := hfin (hd.placed a fl d.imports hfa his i hi' hf)
      refine ⟨fl2, h2, fun hb => h2a ?_⟩
      simp only [lvNeed]
      cases hg : !isM
      · simp only [hg, Bool.false_or, Bool.and_eq_true] at hb ⊢
        exact ⟨hall hb.1, hb.2⟩
      · rfl
  obtain ⟨fl, hfl, hall⟩ := key
  have hm : m ∈ st.order := (hi.flags m).1 (by simp [hfl])
  obtain ⟨k, hk, hkm⟩ := Array.getElem_of_mem hm
  refine ⟨k, by rw [Array.getElem?_eq_getElem hk, hkm], fun ha => ?_⟩
  simp only [Array.getElem?_map, Array.getElem?_eq_getElem hk, hkm, hfl, Option.map_some,
    Option.getD_some]
  exact hall ha

end ConLeche.Driver
