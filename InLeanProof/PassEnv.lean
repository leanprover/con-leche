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
former is related at the marked field count (`presI_marked_former`, through
`toCaps_capsOf`), with no table on either side.
-/

public section

namespace InLeanProof

open Lean InLean

variable {fe : InLean.FEnv} {L : ConLeche.Env}

/-! ## The mark -/

theorem pendingGo_append (T : Name) :
    ∀ (l₁ l₂ : List (Name × Nat)),
      InLean.FEnv.pendingFields?.go T (l₁ ++ l₂) =
        (InLean.FEnv.pendingFields?.go T l₁).or (InLean.FEnv.pendingFields?.go T l₂)
  | [], _ => rfl
  | (n, k) :: l₁, l₂ => by
    simp only [List.cons_append, InLean.FEnv.pendingFields?.go]
    split
    · rfl
    · exact pendingGo_append T l₁ l₂

theorem pendingGo_none {T : Name} :
    ∀ {l : List (Name × Nat)}, (∀ m ∈ l, m.1 ≠ T) → InLean.FEnv.pendingFields?.go T l = none
  | [], _ => rfl
  | (n, k) :: l, h => by
    simp only [InLean.FEnv.pendingFields?.go]
    have hn : (n == T) = false := by
      simpa using h (n, k) (List.mem_cons_self ..)
    rw [hn]
    exact pendingGo_none fun m hm => h m (List.mem_cons_of_mem _ hm)

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
    (hp : ∀ v, ci = .inductInfo v → fe'.pendingFields? v.name = fe.pendingFields? v.name)
    (hf : ∀ c, fe'.find? c = fe.find? c) (h : EntryRelI fe ci cci) : EntryRelI fe' ci cci := by
  cases ci <;> cases cci <;> simp only [EntryRelI] at h ⊢ <;> try exact h
  case inductInfo.indInfo v ccv caps =>
    have hpv := hp v rfl
    have hip : fe'.isPending v.name = fe.isPending v.name := by
      simp only [InLean.FEnv.isPending, hpv]
    rw [capsOf_congr hpv (fun _ c _ => hf c), hip]
    simp only [hf]
    exact h

/-- **Marking fresh names keeps the relation**: every stored former keeps
its reading (its name is its key, not marked). -/
theorem presI_mark (hP : EnvPresI fe L) {marks : List (Name × Nat)}
    (hfresh : ∀ m ∈ marks, fe.env.find? m.1 = none) :
    EnvPresI { fe with pending := marks ++ fe.pending } L := by
  have hf : ∀ n, ({ fe with pending := marks ++ fe.pending } : InLean.FEnv).find? n = fe.find? n :=
    fun n => FEnv.find?_congr rfl rfl rfl
  have hpf : ∀ n, fe.env.find? n ≠ none →
      ({ fe with pending := marks ++ fe.pending } : InLean.FEnv).pendingFields? n =
        fe.pendingFields? n := by
    intro n hn
    show InLean.FEnv.pendingFields?.go n (marks ++ fe.pending) = InLean.FEnv.pendingFields?.go n fe.pending
    rw [pendingGo_append, pendingGo_none]
    · rfl
    · intro m hm he
      exact hn (he ▸ hfresh m hm)
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
      unfold InLean.FEnv.tableFields? at ht ⊢
      rw [hf]
      split
      · rename_i v hv
        rw [hv] at ht
        have hk : v.name = T := presI_key hP hv
        have hq := hpf v.name (by rw [hk, FEnv.env_of_find hv]; exact Option.some_ne_none _)
        simp only [InLean.FEnv.isPending, hq, hf] at ht ⊢
        exact ht
      · rfl
    | some tbl =>
      rw [hT] at ht
      obtain ⟨v, c, cv, h1, h2, h3⟩ := ht
      refine ⟨v, c, cv, by rw [hf]; exact h1, ?_, by simpa only [hf] using h3⟩
      simp only [InLean.FEnv.isPending] at h2 ⊢
      rw [hpf v.name (by
        rw [show v.name = T from presI_key hP h1, FEnv.env_of_find h1]; exact Option.some_ne_none _)]
      exact h2

/-! ## A marked former -/

theorem push_find {fe : InLean.FEnv} {ci : Lean.ConstantInfo} :
    (fe.push ci).env = InLean.addConst fe.env ci := by rfl

/-- **A marked former pushed** keeps the relation: it reads, at its marked
field count, as con-leche's former at `toCaps (capsOf …)`, with no table on
either side. -/
theorem presI_marked_former (hlaws : EnvLaws) (hP : EnvPresI fe L) {v : InductiveVal}
    (hfresh : fe.env.find? v.name = none) (hvis : fe.sees v.name (.inductInfo v) = true)
    (hpend : fe.isPending v.name = true)
    {ccv : ConLeche.ConstantVal} (hcv : CVRel v.toConstantVal ccv) :
    EnvPresI (fe.push (.inductInfo v)) (L.pushDelta [.indInfo ccv (toCaps (capsOf fe v))] []) := by
  have hfeNone : fe.find? v.name = none := by
    simp only [FEnv.find?_eq_filter, hfresh, Option.filter_none]
  have hfe' : (fe.push (.inductInfo v)).find? v.name = some (.inductInfo v) := by
    rw [FEnv.find?_eq_filter, push_find, find_addConst hlaws (ci := .inductInfo v) hfresh]
    have hs' : (fe.push (.inductInfo v)).sees = fe.sees := by rfl
    simp only [show (ConstantInfo.inductInfo v).name = v.name by rfl, ↓reduceIte,
      Option.filter_some, hs', hvis]
  have hcaps : capsOf (fe.push (.inductInfo v)) v = capsOf fe v :=
    capsOf_congr rfl (fun h => by rw [hpend] at h; cases h)
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
    refine ⟨.indInfo ccv (toCaps (capsOf fe v)), ?_, ?_⟩
    · rw [pushDelta_find]
      simp [show (ConLeche.ConstantInfo.indInfo ccv (toCaps (capsOf fe v))).name = ccv.name from rfl,
        hcv.1]
    · exact ⟨hcv, by rw [hcaps], Or.inl hpend⟩
  · intro n hn hf
    simp only [List.mem_singleton] at hn; subst hn
    rw [hfe'] at hf; cases hf
  · intro T hT
    simp only [List.mem_singleton] at hT; subst hT
    rw [findTable_fresh hP hfeNone]
    simp only [TableRelI]
    unfold InLean.FEnv.tableFields?
    rw [hfe']
    simp only
    exact ite_eq_left (show (fe.push (.inductInfo v)).isPending v.name = true from hpend)
  · intro t ht; cases ht

end InLeanProof
