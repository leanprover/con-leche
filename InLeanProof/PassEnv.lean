module

public import InLeanProof.PassInds
import ConLeche.Verify.EnvWF
/- `ConstantInfo.name` is read as a projection of `toConstantVal`. -/
import all Lean.Declaration
/- `FEnv.push` (not exposed in `InLean/Push.lean`). -/
import all InLean.Push

/-!
# O7-stages: the formers' environment against master's (task #451, lane O7-stages)

`presI_formers`: the relation holds between InLean's formers' environment
(`fe` with the block's mark in front, `blockMarks`, and the formers pushed,
`consBlockIndsF`) and master's (`consBlockInds` at `blockCapsAt`): Lane R's
ruling 4 made true.  Marking fresh names changes no reading of a stored
entry (`presI_mark`: a found entry's name is its key, `presI_key`); a marked
former is related at `blockCapsAt` (`presI_marked_former`, through
`toCaps_capsOf`), with no table on either side.
-/

public section

namespace InLeanProof

open Lean InLean

variable {fe : InLean.FEnv} {L : ConLeche.Env}

/-! ## The mark -/

/-- Marking names keeps every other name's mark. -/
theorem isPending_mark (fe : InLean.FEnv) {marks : List Name} {n : Name} (h : n ∉ marks) :
    ({ fe with pending := marks ++ fe.pending } : InLean.FEnv).isPending n = fe.isPending n := by
  simp only [InLean.FEnv.isPending, List.contains_append]
  have : marks.contains n = false := by simpa using h
  rw [this, Bool.false_or]

/-- **A found entry's name is its key** (con-leche's lookup finds by name,
and the relation relates the names). -/
theorem presI_key (hP : EnvPresI fe L) {n : Name} {ci : Lean.ConstantInfo}
    (h : fe.find? n = some ci) : ci.name = n := by
  obtain ⟨cci, hL, hrel⟩ := hP.entry n ci h
  have h1 := ConLeche.Env.find?_name hL
  have h2 := hrel.cv.1
  have h3 : cci.name = cci.toConstantVal.name := by cases cci <;> rfl
  rw [← ci_cv_name, ← h3, h1] at h2
  exact (toName_inj h2).symm

/-- `EntryRelI` reads the environment only through the former's mark and
its constructors' lookup. -/
theorem EntryRelI.congr {fe fe' : InLean.FEnv} {ci : Lean.ConstantInfo} {cci : ConLeche.ConstantInfo}
    (hp : ∀ v, ci = .inductInfo v → fe'.isPending v.name = fe.isPending v.name)
    (hf : ∀ c, fe'.find? c = fe.find? c) (h : EntryRelI fe ci cci) : EntryRelI fe' ci cci := by
  cases ci <;> cases cci <;> simp only [EntryRelI] at h ⊢ <;> try exact h
  case inductInfo.indInfo v ccv caps =>
    rw [hp v rfl]
    simp only [hf]
    exact h

/-- **Marking fresh names keeps the relation**: every stored former keeps
its reading (its name is its key, not marked). -/
theorem presI_mark (hP : EnvPresI fe L) {marks : List Name}
    (hfresh : ∀ m ∈ marks, fe.env.find? m = none) :
    EnvPresI { fe with pending := marks ++ fe.pending } L := by
  have hf : ∀ n, ({ fe with pending := marks ++ fe.pending } : InLean.FEnv).find? n = fe.find? n :=
    fun n => FEnv.find?_congr rfl rfl rfl
  have hpf : ∀ n, fe.env.find? n ≠ none →
      ({ fe with pending := marks ++ fe.pending } : InLean.FEnv).isPending n = fe.isPending n := by
    intro n hn
    exact isPending_mark fe fun hm => hn (hfresh n hm)
  refine ⟨?_, ?_, ?_, hP.tabNames⟩
  · intro n ci h
    rw [hf] at h
    obtain ⟨cci, hL, hrel⟩ := hP.entry n ci h
    refine ⟨cci, hL, EntryRelI.congr ?_ hf hrel⟩
    rintro v rfl
    apply hpf
    rw [show v.name = n from presI_key hP h, FEnv.env_of_find h]
    exact Option.some_ne_none _
  · intro n h
    rw [hf] at h
    exact hP.none n h
  · intro T
    have ht := hP.table T
    cases hT : L.findTable? (toName T) with
    | none =>
      rw [hT] at ht
      simp only [TableRelI] at ht ⊢
      unfold InLean.FEnv.findTable? at ht ⊢
      rw [hf]
      split
      · rename_i v hv
        rw [hv] at ht
        have hk : v.name = T := presI_key hP hv
        have hq := hpf v.name (by rw [hk, FEnv.env_of_find hv]; exact Option.some_ne_none _)
        simp only [hq, hf] at ht ⊢
        exact ht
      · rfl
    | some tbl =>
      rw [hT] at ht
      obtain ⟨v, c, cv, h1, h2, h3⟩ := ht
      refine ⟨v, c, cv, by rw [hf]; exact h1, ?_, by simpa only [hf] using h3⟩
      rw [hpf v.name (by
        rw [show v.name = T from presI_key hP h1, FEnv.env_of_find h1]; exact Option.some_ne_none _)]
      exact h2

/-! ## A marked former -/

theorem push_find {fe : InLean.FEnv} {ci : Lean.ConstantInfo} :
    (fe.push ci).env = InLean.addConst fe.env ci := by rfl

/-- **A marked former pushed** keeps the relation: it reads as con-leche's
former at `toCaps (capsOf …)`, with no table on either side. -/
theorem presI_marked_former (hlaws : EnvLaws) (hP : EnvPresI fe L) {v : InductiveVal}
    (hfresh : fe.env.find? v.name = none) (hvis : fe.sees v.name (.inductInfo v) = true)
    (hpend : fe.isPending v.name = true)
    {ccv : ConLeche.ConstantVal} (hcv : CVRel v.toConstantVal ccv) :
    EnvPresI (fe.push (.inductInfo v)) (L.pushDelta [.indInfo ccv (toCaps (capsOf v))] []) := by
  have hfeNone : fe.find? v.name = none := by
    simp only [FEnv.find?_eq_filter, hfresh, Option.filter_none]
  have hfe' : (fe.push (.inductInfo v)).find? v.name = some (.inductInfo v) := by
    rw [FEnv.find?_eq_filter, push_find, find_addConst hlaws (ci := .inductInfo v) hfresh]
    have hs' : (fe.push (.inductInfo v)).sees = fe.sees := by rfl
    simp only [show (ConstantInfo.inductInfo v).name = v.name by rfl, ↓reduceIte,
      Option.filter_some, hs', hvis]
  apply presI_push (fe' := fe.push (.inductInfo v)) (names := [v.name]) hP rfl rfl rfl
  · intro n hn; simp only [List.mem_singleton] at hn; subst hn; exact hfresh
  · intro n hn
    simp only [List.mem_singleton] at hn
    rw [push_find, find_addConst hlaws (ci := .inductInfo v) hfresh]
    exact ite_eq_right hn
  · intro c hc
    simp only [List.mem_singleton] at hc; subst hc
    exact ⟨v.name, by simp, hcv.1⟩
  · intro t ht; cases ht
  · intro n hn ci' hf
    simp only [List.mem_singleton] at hn; subst hn
    rw [hfe'] at hf
    cases hf
    refine ⟨.indInfo ccv (toCaps (capsOf v)), ?_, ?_⟩
    · rw [pushDelta_find]
      simp [show (ConLeche.ConstantInfo.indInfo ccv (toCaps (capsOf v))).name = ccv.name from rfl,
        hcv.1]
    · exact ⟨hcv, rfl, Or.inl hpend⟩
  · intro n hn hf
    simp only [List.mem_singleton] at hn; subst hn
    rw [hfe'] at hf; cases hf
  · intro T hT
    simp only [List.mem_singleton] at hT; subst hT
    rw [findTable_fresh hP hfeNone]
    simp only [TableRelI]
    unfold InLean.FEnv.findTable?
    rw [hfe']
    simp only
    exact ite_eq_left (show (fe.push (.inductInfo v)).isPending v.name = true from hpend)
  · intro t ht; cases ht

/-! ## The formers' fold -/

theorem blockMarks_eq (p : InLean.BlockShape) :
    InLean.blockMarks p = p.members.map (·.declared.name) := rfl

theorem getD_of_drop {α : Type} [Inhabited α] {l rest : List α} {k : Nat} {a : α}
    (h : l.drop k = a :: rest) : l.getD k default = a ∧ l.drop (k + 1) = rest := by
  have hk : l[k]? = some a := by
    have := congrArg (·[0]?) h
    simpa [List.getElem?_drop] using this
  refine ⟨by simp [List.getD_eq_getElem?_getD, hk], ?_⟩
  rw [← List.drop_drop, h]; rfl

/-- **The formers pushed, marked**, against master's `consBlockInds`. -/
theorem presI_consBlockIndsF (hlaws : EnvLaws) {p : InLean.BlockShape} {isRec : Bool} :
    ∀ (l : List InLean.MemberShape) (k : Nat) {fe : InLean.FEnv} {L : ConLeche.Env},
      p.members.drop k = l → EnvPresI fe L →
      (∀ ms ∈ l, fe.env.find? ms.declared.name = none) → (l.map (·.declared.name)).Nodup →
      (∀ ms ∈ l, ms.declared.name = InLean.sorryAxName → fe.coreAxioms = true) →
      (∀ ms ∈ l, fe.isPending ms.declared.name = true) →
      (∀ ms ∈ l, StoredT ms.declared.type (trC ms.declared.type)) →
      EnvPresI (InLean.consBlockIndsF p isRec (l.map (·.declared)) k fe)
        (ConLeche.consBlockInds (trShape p) isRec (l.map (trCV ·.declared)) k L)
  | [], _, _, _, _, hP, _, _, _, _, _ => hP
  | ms :: rest, k, fe, L, hd, hP, hfr, hnd, hso, hpf, hst => by
    obtain ⟨hgk, hdr⟩ := getD_of_drop hd
    have hgkC : (trShape p).members.getD k default = trMember ms := by
      have hk : p.members[k]? = some ms := by
        have := congrArg (·[0]?) hd
        simpa [List.getElem?_drop] using this
      simp [trShape, List.getD_eq_getElem?_getD, hk]
    simp only [List.map_cons, List.mem_cons, forall_eq_or_imp, List.nodup_cons, List.mem_map] at *
    simp only [InLean.consBlockIndsF, ConLeche.consBlockInds, hgk]
    -- the former, its visibility, its mark, its capabilities
    generalize hv : InductiveVal.mk ms.declared p.nP ms.nIdx p.memberNames
      (ms.ctors.map (·.1.name)) 0 isRec false false = v
    have hvn : v.name = ms.declared.name := by rw [← hv]
    have hvis : fe.sees v.name (.inductInfo v) = true :=
      sees_safe (by rw [← hv]; rfl) (fun h => hso.1 (hvn ▸ h))
    have hpend : fe.isPending v.name = true := by rw [hvn]; exact hpf.1
    have hcv : CVRel v.toConstantVal (trCV ms.declared) := by
      rw [← hv]; exact ⟨rfl, rfl, hst.1⟩
    have hcaps : toCaps (capsOf v) = ConLeche.blockCapsAt (trShape p) k isRec := by
      apply toCaps_capsOf (mi := k)
      · rw [hgkC, ← hv]; simp [trMember, trCtor]
      · rw [hgkC, ← hv]; rfl
      · rw [← hv]; rfl
      · rw [← hv, trShape_memberNames]
      · rw [← hv]
    have hstep := presI_marked_former hlaws hP (by rw [hvn]; exact hfr.1) hvis hpend hcv
    rw [hcaps] at hstep
    have hL : ({ consts := .indInfo (trCV ms.declared) (ConLeche.blockCapsAt (trShape p) k isRec)
        :: L.consts, tables := L.tables } : ConLeche.Env) =
        L.pushDelta [.indInfo (trCV ms.declared) (ConLeche.blockCapsAt (trShape p) k isRec)] [] := by
      simp [ConLeche.Env.pushDelta]
    rw [hL]
    have hfeq : ∀ n, n ≠ ms.declared.name → (fe.push (.inductInfo v)).env.find? n = fe.env.find? n := by
      intro n hn
      rw [push_find, find_addConst hlaws (ci := .inductInfo v) (by rw [show (ConstantInfo.inductInfo v).name = v.name by rfl, hvn]; exact hfr.1)]
      exact ite_eq_right (by rw [show (ConstantInfo.inductInfo v).name = v.name by rfl, hvn]; exact hn)
    refine presI_consBlockIndsF hlaws rest (k + 1) hdr hstep ?_ hnd.2 ?_ ?_ hst.2
    · intro m hm
      rw [hfeq _ (fun h => hnd.1 ⟨m, hm, h⟩)]
      exact hfr.2 m hm
    · exact hso.2
    · exact hpf.2

theorem isPending_marks {fe : InLean.FEnv} (p : InLean.BlockShape) {ms : InLean.MemberShape}
    (hms : ms ∈ p.members) :
    ({ fe with pending := InLean.blockMarks p ++ fe.pending } : InLean.FEnv).isPending
      ms.declared.name = true := by
  simp only [InLean.FEnv.isPending, List.contains_append, blockMarks_eq, Bool.or_eq_true]
  exact Or.inl (by simpa using ⟨ms, hms, rfl⟩)

/-- **The formers' environment against master's** (Lane R's ruling 4): `fe`
with the block's mark in front and the formers pushed presents master's
`consBlockInds` at `blockCapsAt`. -/
theorem presI_formers (hlaws : EnvLaws) (hP : EnvPresI fe L) {p : InLean.BlockShape} {isRec : Bool}
    (hfr : ∀ ms ∈ p.members, fe.env.find? ms.declared.name = none)
    (hnd : (p.members.map (·.declared.name)).Nodup)
    (hso : ∀ ms ∈ p.members, ms.declared.name = InLean.sorryAxName → fe.coreAxioms = true)
    (hst : ∀ ms ∈ p.members, StoredT ms.declared.type (trC ms.declared.type)) :
    EnvPresI (InLean.consBlockIndsF p isRec (p.members.map (·.declared)) 0
        { fe with pending := InLean.blockMarks p ++ fe.pending })
      (ConLeche.consBlockInds (trShape p) isRec ((trShape p).members.map (·.declared)) 0 L) := by
  have hM := presI_mark hP (marks := InLean.blockMarks p) (by
    intro m hm
    rw [blockMarks_eq] at hm
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.1 hm
    exact hfr ms hms)
  have hmap : (trShape p).members.map (·.declared) = p.members.map (trCV ·.declared) := by
    simp [trShape, trMember]
  rw [hmap]
  exact presI_consBlockIndsF hlaws p.members 0 (List.drop_zero) hM hfr hnd hso
    (fun ms hms => isPending_marks p hms)
    hst

/-! ## Freshness, read off the formers' run

`checkBlockTeleC` runs `checkConstantValC` on each member's former, whose
first guard is the name's freshness in Lean's environment. -/

theorem checkBlockTeleF_fresh {mode : InLean.CheckMode} {fe : InLean.FEnv} {nP : Nat}
    {ms : InLean.MemberShape} {s₀ s' : InLean.CState} {r : Lean.ConstantVal × Lean.Level}
    (h : InLean.checkBlockTeleC mode fe nP ms s₀ = .ok (r, s')) : fe.env.find? ms.cvT.name = none := by
  unfold InLean.checkBlockTeleC at h
  obtain ⟨_, _, h1, _⟩ := bindI_ok h
  exact checkConstantValC_fresh h1

theorem checkBlockTelesF_fresh {mode : InLean.CheckMode} {fe : InLean.FEnv} {nP : Nat} :
    ∀ {l : List InLean.MemberShape} {s₀ s' : InLean.CState} {r : List (Lean.ConstantVal × Lean.Level)},
      InLean.checkBlockTelesC mode fe nP l s₀ = .ok (r, s') → ∀ ms ∈ l, fe.env.find? ms.cvT.name = none
  | [], _, _, _, _ => by simp
  | ms :: rest, s₀, s', r, h => by
    unfold InLean.checkBlockTelesC at h
    obtain ⟨_, _, h1, h⟩ := bindI_ok h
    obtain ⟨_, _, h2, _⟩ := bindI_ok h
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact checkBlockTeleF_fresh h1
    · exact checkBlockTelesF_fresh h2 m hm

/-- **The formers' names are fresh in Lean's environment**, read off an
accepted formers' stage. -/
theorem checkBlockIndsF_fresh {mode : InLean.CheckMode} {fe : InLean.FEnv} {p : InLean.BlockShape}
    {isRec : Bool} {s₀ s' : InLean.CState} {r : InLean.FEnv × InLean.BlockShape}
    (h : InLean.checkBlockIndsC mode fe p isRec s₀ = .ok (r, s')) :
    ∀ ms ∈ p.members, fe.env.find? ms.cvT.name = none := by
  unfold InLean.checkBlockIndsC at h
  generalize hm : p.members = mems at h
  cases mems with
  | nil => exact (throwI_ok h).elim
  | cons ms0 rest =>
    simp only at h
    obtain ⟨_, _, h1, h⟩ := bindI_ok h
    obtain ⟨_, _, h2, _⟩ := bindI_ok h
    intro m hm'
    rcases List.mem_cons.1 hm' with rfl | hm'
    · exact checkBlockTeleF_fresh h1
    · exact checkBlockTelesF_fresh h2 m hm'

/-! ## Marked extensions: no projection table appears -/

/-- **`fe'` extends `fe` by marked formers**: the same policy, the mark only
grown, and every lookup either `fe`'s or a marked former. -/
structure MarkedExt (fe fe' : InLean.FEnv) : Prop where
  core : fe'.coreAxioms = fe.coreAxioms
  safety : fe'.safety = fe.safety
  pend : ∀ n, fe.isPending n = true → fe'.isPending n = true
  find : ∀ n, fe'.env.find? n = fe.env.find? n ∨
    ∃ v, fe'.env.find? n = some (.inductInfo v) ∧ fe'.isPending v.name = true

theorem MarkedExt.refl (fe : InLean.FEnv) : MarkedExt fe fe :=
  ⟨rfl, rfl, fun _ h => h, fun _ => .inl rfl⟩

theorem MarkedExt.trans {fe fe' fe'' : InLean.FEnv} (h₁ : MarkedExt fe fe') (h₂ : MarkedExt fe' fe'') :
    MarkedExt fe fe'' := by
  refine ⟨h₂.core.trans h₁.core, h₂.safety.trans h₁.safety, fun n h => h₂.pend n (h₁.pend n h),
    fun n => ?_⟩
  rcases h₂.find n with e | ⟨v, hv, hp⟩
  · rcases h₁.find n with e' | ⟨v, hv, hp⟩
    · exact .inl (e.trans e')
    · exact .inr ⟨v, e.trans hv, h₂.pend _ hp⟩
  · exact .inr ⟨v, hv, hp⟩

theorem MarkedExt.find? {fe fe' : InLean.FEnv} (hE : MarkedExt fe fe') {n : Name}
    {ci : Lean.ConstantInfo} (h : fe'.find? n = some ci) :
    fe.find? n = some ci ∨ ∃ v, ci = .inductInfo v ∧ fe'.isPending v.name = true := by
  rcases hE.find n with e | ⟨v, hv, hp⟩
  · exact .inl (by rw [← FEnv.find?_congr hE.core hE.safety e]; exact h)
  · have := FEnv.env_of_find h
    rw [hv] at this
    cases this
    exact .inr ⟨v, rfl, hp⟩

/-- **A marked extension adds no projection table.** -/
theorem MarkedExt.findTable? {fe fe' : InLean.FEnv} (hE : MarkedExt fe fe') {T : Name}
    {t : InLean.TableView} (h : fe'.findTable? T = some t) : fe.findTable? T = some t := by
  unfold InLean.FEnv.findTable? at h ⊢
  split at h
  next v hv =>
    split at h
    · cases h
    next hnp =>
      rcases hE.find? hv with hv' | ⟨w, hw, hp⟩
      · rw [hv']
        simp only
        rw [ite_eq_right (fun hq => hnp (hE.pend _ hq))]
        split at h
        next c hc =>
          split at h
          next hi =>
            rw [ite_eq_left hi]
            split at h
            next cv hcv =>
              rcases hE.find? hcv with hcv' | ⟨w, hw, _⟩
              · rw [hcv']; exact h
              · cases hw
            next => cases h
          next => cases h
        next => cases h
      · cases hw
        exact (hnp hp).elim
  next => cases h

/-- **A marked extension adds no projection.** -/
theorem MarkedExt.findProj? {fe fe' : InLean.FEnv} (hE : MarkedExt fe fe') {T : Name} {i : Nat}
    {e : InLean.ProjEntry} (h : fe'.findProj? T i = some e) : fe.findProj? T i = some e := by
  unfold InLean.FEnv.findProj? at h ⊢
  cases ht : fe'.findTable? T with
  | none => rw [ht] at h; cases h
  | some t => rw [ht] at h; rw [hE.findTable? ht]; exact h

theorem MarkedExt.projBodies {fe fe' : InLean.FEnv} (hE : MarkedExt fe fe')
    (h : ProjBodiesInRange fe) : ProjBodiesInRange fe' :=
  fun T i e he => h T i e (hE.findProj? he)

theorem markedExt_mark (fe : InLean.FEnv) (marks : List Name) :
    MarkedExt fe { fe with pending := marks ++ fe.pending } := by
  refine ⟨rfl, rfl, fun n h => ?_, fun _ => .inl rfl⟩
  simp only [InLean.FEnv.isPending, List.contains_append, Bool.or_eq_true] at h ⊢
  exact Or.inr h

theorem markedExt_push (hlaws : EnvLaws) {fe : InLean.FEnv} {v : InductiveVal}
    (hfresh : fe.env.find? v.name = none) (hpend : fe.isPending v.name = true) :
    MarkedExt fe (fe.push (.inductInfo v)) := by
  refine ⟨rfl, rfl, fun _ h => h, fun n => ?_⟩
  rw [push_find, find_addConst hlaws (ci := .inductInfo v) hfresh]
  by_cases hn : n = (ConstantInfo.inductInfo v).name
  · rw [ite_eq_left hn]; exact .inr ⟨v, rfl, hpend⟩
  · rw [ite_eq_right hn]; exact .inl rfl

/-- **The formers' fold is a marked extension.** -/
theorem markedExt_consBlockIndsF (hlaws : EnvLaws) {p : InLean.BlockShape} {isRec : Bool} :
    ∀ (l : List Lean.ConstantVal) (k : Nat) {fe : InLean.FEnv},
      (∀ cv ∈ l, fe.env.find? cv.name = none) → (l.map (·.name)).Nodup →
      (∀ cv ∈ l, fe.isPending cv.name = true) →
      MarkedExt fe (InLean.consBlockIndsF p isRec l k fe)
  | [], _, fe, _, _, _ => MarkedExt.refl fe
  | cv :: rest, k, fe, hfr, hnd, hpd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [InLean.consBlockIndsF]
    generalize hv : InductiveVal.mk cv p.nP (p.members.getD k default).nIdx p.memberNames
      ((p.members.getD k default).ctors.map (·.1.name)) 0 isRec false false = v
    have hvn : v.name = cv.name := by rw [← hv]
    have h1 := markedExt_push hlaws (v := v) (fe := fe) (by rw [hvn]; exact hfr cv List.mem_cons_self)
      (by rw [hvn]; exact hpd cv List.mem_cons_self)
    refine h1.trans (markedExt_consBlockIndsF hlaws rest (k + 1) (fun c hc => ?_) hnd.2
      (fun c hc => hpd c (List.mem_cons_of_mem _ hc)))
    rw [push_find, find_addConst hlaws (ci := .inductInfo v)
      (by rw [show (ConstantInfo.inductInfo v).name = v.name by rfl, hvn];
          exact hfr cv List.mem_cons_self)]
    rw [ite_eq_right (by
      rw [show (ConstantInfo.inductInfo v).name = v.name by rfl, hvn]
      exact fun h => hnd.1 ⟨c, hc, h⟩)]
    exact hfr c (List.mem_cons_of_mem _ hc)

/-! ## The job's premises at the formers' environment -/

/-- **`JobEnvI` at the formers' push** (finding 1 of lane O7-stages): from
the job's premises at `fe`/`L`, what the members' reduction and the block
give (`PassPremI`), the names' freshness read off the formers' run
(`checkBlockIndsF_fresh`) and master's formers' stage. -/
theorem jobEnvI_formers (hJ : JobEnvI fe L) {p : InLean.BlockShape} {isRec : Bool}
    (hpre : PassPremI fe L p) (hok : ∀ ms ∈ p.members, MemberOk ms)
    (hfr : ∀ ms ∈ p.members, fe.env.find? ms.cvT.name = none) {s0 : Lean.Level}
    {p₁c : ConLeche.BlockShape}
    (hR : ConLeche.Cached.Runs (ConLeche.checkBlockInds (ConLeche.fueledOpsM .verified) L (trShape p) isRec)
      (ConLeche.consBlockInds (trShape (p.withSort s0)) isRec ((trShape p).members.map (·.declared)) 0 L,
        p₁c)) :
    JobEnvI (InLean.consBlockIndsF (p.withSort s0) isRec (p.members.map (·.declared)) 0
        { fe with pending := InLean.blockMarks (p.withSort s0) ++ fe.pending })
      (ConLeche.consBlockInds (trShape (p.withSort s0)) isRec ((trShape p).members.map (·.declared)) 0 L) := by
  have hfr' : ∀ ms ∈ p.members, fe.env.find? ms.declared.name = none := fun ms hms => by
    rw [← hpre.name ms hms]; exact hfr ms hms
  have hpres := presI_formers hJ.laws hJ.pres (p := p.withSort s0) (isRec := isRec) hfr' hpre.nodup
    hpre.sorry_ (fun ms hms => StoredT_of (hpre.range ms hms) (toExprC_of_okC (hok ms hms).2.1))
  have hwf : ConLeche.EnvWF (ConLeche.consBlockInds (trShape (p.withSort s0)) isRec
      ((trShape p).members.map (·.declared)) 0 L) := by
    obtain ⟨F, hF⟩ := hR
    rw [ConLeche.checkBlockInds_datF] at hF
    refine (ConLeche.direct_block_inds_wf hJ.wf (fun ms hms => ?_) hF).1
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hms
    exact hpre.decl m hm
  have hE := (markedExt_mark fe (InLean.blockMarks (p.withSort s0))).trans
    (markedExt_consBlockIndsF hJ.laws (p := p.withSort s0) (isRec := isRec) (p.members.map (·.declared)) 0
      (fun cv hcv => by
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hcv
        exact hfr' m hm)
      (by rw [List.map_map]; exact hpre.nodup)
      (fun cv hcv => by
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hcv
        exact isPending_marks (p.withSort s0) (by simpa [InLean.BlockShape.withSort] using hm)))
  have hproj := hE.projBodies hJ.proj
  exact ⟨hJ.laws, hpres, hwf, hproj⟩

end InLeanProof
