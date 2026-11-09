module

public import ConLeche.Cached.StreamIndex
public import ConLeche.Verify.Cached.ViewCongr
public import ConLeche.Verify.Cached.PushChain

/-!
# Every job passing is an accept of the fold

`checkDecls_of_jobs`: if every record's job (`recordJob`, `ConLeche/Cached/StreamIndex.lean`) passes,
the fold `checkDecls` accepts the stream with the environment the records denote.  By induction along
the stream: the steps so far having accepted, the names so far are distinct (`PushChain`), so the
view of the next position answers every lookup as the fold's index does (`viewTwin`), so the job's
verdict is the fold's step (`checkDeclStepC_twin`).

The index's first-entry-wins builder enters through what it answers (`firstOcc`, `firstTbl`).  Nothing
here mentions a thread: the driver's jobs are values.
-/

public section

namespace ConLeche.Cached

open ConLeche

variable {mode : CheckMode} {pins : List NatOpPinSet}

/-! ## What the index answers -/

/-- The first constant named `n` in `L`, whose head has counter `c`. -/
def firstOcc (n : Name) : Nat → List ConstantInfo → Option (Nat × ConstantInfo)
  | _, [] => none
  | c, ci :: L => if ci.name = n then some (c, ci) else firstOcc n (c + 1) L

theorem firstOcc_append (n : Name) (c : Nat) (A B : List ConstantInfo) :
    firstOcc n c (A ++ B) = (firstOcc n c A).or (firstOcc n (c + A.length) B) := by
  induction A generalizing c with
  | nil => simp [firstOcc]
  | cons a A ih =>
    simp only [List.cons_append, firstOcc, List.length_cons]
    split
    · rfl
    · rw [ih]
      congr 2
      omega

theorem firstOcc_ge {n : Name} {c c' : Nat} {ci : ConstantInfo} :
    ∀ {L : List ConstantInfo}, firstOcc n c L = some (c', ci) → c ≤ c' ∧ c' < c + L.length
  | [], h => by simp [firstOcc] at h
  | a :: L, h => by
    simp only [firstOcc] at h
    split at h
    · cases h; simp
    · have := firstOcc_ge h
      simp only [List.length_cons]
      omega

/-- The insertion keeps the map's answers the first occurrences. -/
theorem insertConsts_spec {A : List ConstantInfo} :
    ∀ (L : List ConstantInfo) (idx : Std.HashMap Name (Nat × ConstantInfo)),
      (∀ n, idx[n]? = firstOcc n 0 A) →
      (insertConsts idx A.length L).2 = A.length + L.length ∧
      ∀ n, (insertConsts idx A.length L).1[n]? = firstOcc n 0 (A ++ L) := by
  intro L
  induction L generalizing A with
  | nil =>
    intro idx h
    simpa [insertConsts] using h
  | cons ci L ih =>
    intro idx h
    have hstep : ∀ n, (idx.insertIfNew ci.name (A.length, ci))[n]? = firstOcc n 0 (A ++ [ci]) := by
      intro n
      rw [Std.HashMap.getElem?_insertIfNew, firstOcc_append]
      simp only [firstOcc, Nat.zero_add]
      by_cases hn : ci.name = n
      · subst hn
        cases hf : firstOcc ci.name 0 A with
        | none =>
          have hm : ci.name ∉ idx := by
            intro hmem
            have := (Std.HashMap.mem_iff_isSome_getElem?).mp hmem
            rw [h, hf] at this
            exact absurd this (by simp)
          simp [hm]
        | some p =>
          have hm : ci.name ∈ idx := by
            rw [Std.HashMap.mem_iff_isSome_getElem?, h, hf]; rfl
          rw [ite_eq_right (by simp [hm]), h, hf]
          rfl
      · simp [hn, h]
    have := ih (A := A ++ [ci]) (idx.insertIfNew ci.name (A.length, ci)) hstep
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      List.append_assoc, List.cons_append, List.nil_append] at this
    simp only [insertConsts, List.length_cons]
    exact ⟨by rw [this.1]; omega, this.2⟩

/-- The first table of `T` among records' tables, each with its record's position. -/
def firstTbl (T : Name) : List (Nat × ProjTable) → Option (Nat × ProjTable)
  | [] => none
  | e :: L => if e.2.structName = T then some e else firstTbl T L

theorem firstTbl_append (T : Name) (A B : List (Nat × ProjTable)) :
    firstTbl T (A ++ B) = (firstTbl T A).or (firstTbl T B) := by
  induction A with
  | nil => simp [firstTbl]
  | cons a A ih =>
    simp only [List.cons_append, firstTbl]
    split
    · rfl
    · exact ih

theorem insertTables_spec (r : Nat) {A : List (Nat × ProjTable)} :
    ∀ (Q : List ProjTable) (tbls : Std.HashMap Name (Nat × ProjTable)),
      (∀ T, tbls[T]? = firstTbl T A) →
      ∀ T, (insertTables tbls r Q)[T]? = firstTbl T (A ++ Q.map (r, ·)) := by
  intro Q
  induction Q generalizing A with
  | nil =>
    intro tbls h
    simpa [insertTables] using h
  | cons t Q ih =>
    intro tbls h
    have hstep : ∀ T, (tbls.insertIfNew t.structName (r, t))[T]? = firstTbl T (A ++ [(r, t)]) := by
      intro T
      rw [Std.HashMap.getElem?_insertIfNew, firstTbl_append]
      simp only [firstTbl]
      by_cases hn : t.structName = T
      · subst hn
        cases hf : firstTbl t.structName A with
        | none =>
          have hm : t.structName ∉ tbls := by
            intro hmem
            have := (Std.HashMap.mem_iff_isSome_getElem?).mp hmem
            rw [h, hf] at this
            exact absurd this (by simp)
          simp [hm]
        | some p =>
          have hm : t.structName ∈ tbls := by
            rw [Std.HashMap.mem_iff_isSome_getElem?, h, hf]; rfl
          rw [ite_eq_right (by simp [hm]), h, hf]
          rfl
      · simp [hn, h]
    intro T
    have := ih (A := A ++ [(r, t)]) (tbls.insertIfNew t.structName (r, t)) hstep T
    simpa [insertTables] using this

/-- The constants of records, in order. -/
def recsConsts (ds : List Declaration) : List ConstantInfo := ds.flatMap declConstants

/-- The tables of records from position `r` on, each with its record's position. -/
def recsTables : Nat → List Declaration → List (Nat × ProjTable)
  | _, [] => []
  | r, pd :: ds => (declTables pd).map (r, ·) ++ recsTables (r + 1) ds

theorem recsConsts_snoc (ds : List Declaration) (pd : Declaration) :
    recsConsts (ds ++ [pd]) = recsConsts ds ++ declConstants pd := by
  simp [recsConsts]

theorem recsTables_append (r : Nat) (A B : List Declaration) :
    recsTables r (A ++ B) = recsTables r A ++ recsTables (r + A.length) B := by
  induction A generalizing r with
  | nil => simp [recsTables]
  | cons d A ih =>
    simp only [List.cons_append, recsTables, List.length_cons, ih, List.append_assoc]
    congr 3
    omega

theorem recsTables_snoc (r : Nat) (ds : List Declaration) (pd : Declaration) :
    recsTables r (ds ++ [pd]) = recsTables r ds ++ (declTables pd).map (r + ds.length, ·) := by
  simp [recsTables_append, recsTables]

theorem recsTables_bounds {e : Nat × ProjTable} :
    ∀ {ds : List Declaration} {r : Nat}, e ∈ recsTables r ds → r ≤ e.1 ∧ e.1 < r + ds.length
  | [], _, h => nomatch h
  | pd :: ds, r, h => by
    simp only [recsTables, List.mem_append, List.mem_map] at h
    rcases h with ⟨t, -, rfl⟩ | h
    · simp
    · have := recsTables_bounds h
      simp only [List.length_cons]
      omega

theorem recsTables_snd :
    ∀ (ds : List Declaration) (r : Nat), (recsTables r ds).map (·.2) = ds.flatMap declTables
  | [], _ => rfl
  | pd :: ds, r => by
    simp [recsTables, recsTables_snd ds (r + 1), List.map_map, Function.comp_def]

/-- **What the index of records holds.** -/
structure IndexSpec (ds : List Declaration) (I : StreamIndex) : Prop where
  next : I.next = (recsConsts ds).length
  firsts : ∀ k, (hk : k < ds.length) → I.firsts[k]? = some (recsConsts (ds.take k)).length
  size : I.firsts.size = ds.length
  idx : ∀ n, I.base.idx[n]? = firstOcc n 0 (recsConsts ds)
  tbls : ∀ T, I.base.tbls[T]? = firstTbl T (recsTables 0 ds)

theorem IndexSpec.add {ds : List Declaration} {I : StreamIndex} (h : IndexSpec ds I)
    (pd : Declaration) : IndexSpec (ds ++ [pd]) (I.add pd) := by
  have hc := insertConsts_spec (A := recsConsts ds) (declConstants pd) I.base.idx h.idx
  have hnext : I.next = (recsConsts ds).length := h.next
  have ht := insertTables_spec ds.length (A := recsTables 0 ds) (declTables pd) I.base.tbls h.tbls
  have hsz := h.size
  constructor
  · simp only [StreamIndex.add, hnext]
    rw [hc.1, recsConsts_snoc, List.length_append]
  · intro k hk
    simp only [StreamIndex.add, List.length_append, List.length_cons, List.length_nil] at hk ⊢
    rw [Array.getElem?_push]
    by_cases hk' : k = ds.length
    · subst hk'
      simp [hsz, hnext]
    · have hlt : k < ds.length := by omega
      rw [ite_eq_right (by omega), h.firsts k hlt, List.take_append_of_le_length (by omega)]
  · simp [StreamIndex.add, hsz]
  · intro n
    simp only [StreamIndex.add, hnext]
    rw [hc.2 n, recsConsts_snoc]
  · intro T
    simp only [StreamIndex.add, hsz]
    rw [ht T, recsTables_snoc]
    simp

theorem buildIndex_spec (ds : Array Declaration) : IndexSpec ds.toList (buildIndex ds) := by
  unfold buildIndex
  rw [← Array.foldl_toList]
  suffices ∀ (l acc : List Declaration) (I : StreamIndex), IndexSpec acc I →
      IndexSpec (acc ++ l) (l.foldl StreamIndex.add I) from
    by simpa using this ds.toList [] {} ⟨rfl, by simp, rfl, by simp [recsConsts, firstOcc],
      by simp [recsTables, firstTbl]⟩
  intro l
  induction l with
  | nil => intro acc I h; simpa using h
  | cons pd l ih =>
    intro acc I h
    have := ih (acc ++ [pd]) (I.add pd) (h.add pd)
    simpa using this

/-! ## The view of a position -/

/-- A list whose keys are distinct: the last with a key is the first. -/
theorem find?_reverse_of_nodup {α : Type} (f : α → Name) (n : Name) :
    ∀ {L : List α}, (L.map f).Nodup → L.reverse.find? (f · == n) = L.find? (f · == n)
  | [], _ => rfl
  | a :: L, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    simp only [List.reverse_cons, List.find?_append, List.find?_cons, List.find?_nil,
      find?_reverse_of_nodup f n h.2]
    by_cases ha : f a = n
    · have hnone : L.find? (f · == n) = none := by
        rw [List.find?_eq_none]
        intro b hb hq
        have hfb : f b = n := by simpa using hq
        exact h.1 b hb (hfb.trans ha.symm)
      simp [hnone, ha]
    · have hb : (f a == n) = false := by simpa using ha
      simp [hb]

theorem firstOcc_map (n : Name) :
    ∀ (L : List ConstantInfo) (c : Nat),
      (firstOcc n c L).map (·.2) = L.find? (·.name == n)
  | [], _ => rfl
  | ci :: L, c => by
    simp only [firstOcc, List.find?_cons]
    by_cases h : ci.name = n
    · simp [h]
    · have hb : (ci.name == n) = false := by simpa using h
      simp [h, hb, firstOcc_map n L (c + 1)]

theorem firstTbl_map (T : Name) :
    ∀ L : List (Nat × ProjTable),
      (firstTbl T L).map (·.2) = (L.map (·.2)).find? (·.structName == T)
  | [] => rfl
  | e :: L => by
    simp only [firstTbl, List.map_cons, List.find?_cons]
    by_cases h : e.2.structName = T
    · simp [h]
    · have hb : (e.2.structName == T) = false := by simpa using h
      simp [h, hb, firstTbl_map T L]

theorem firstTbl_mem {T : Name} {e : Nat × ProjTable} :
    ∀ {L : List (Nat × ProjTable)}, firstTbl T L = some e → e ∈ L
  | [], h => by simp [firstTbl] at h
  | a :: L, h => by
    simp only [firstTbl] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (firstTbl_mem h)

theorem streamEnv_consts (ds : List Declaration) (env : Env) :
    (streamEnv ds env).consts = (recsConsts ds).reverse ++ env.consts := by
  induction ds generalizing env with
  | nil => rfl
  | cons pd ds ih =>
    simp only [streamEnv, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [recsConsts, Env.pushDelta]

theorem streamEnv_tables (ds : List Declaration) (env : Env) :
    (streamEnv ds env).tables = (ds.flatMap declTables).reverse ++ env.tables := by
  induction ds generalizing env with
  | nil => rfl
  | cons pd ds ih =>
    simp only [streamEnv, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [Env.pushDelta]

/-! ## Tables are named after a record's constants -/

theorem blockTables_sublist (p : BlockShape) :
    ∀ l : List MemberShape,
      (((blockTables p l).getD []).map (·.structName)).Sublist (l.map (·.declared.name))
  | [] => .refl _
  | ms :: rest => by
    have ih := blockTables_sublist p rest
    simp only [blockTables, List.map_cons]
    split
    · rename_i c _
      cases structProjBodies ms.declared.name p.nP c.2 c.1.type with
      | none => exact List.nil_sublist _
      | some bodies =>
        cases h : blockTables p rest with
        | none => exact List.nil_sublist _
        | some Qr =>
          rw [h] at ih
          exact ih.cons_cons _
    · exact ih.cons _

theorem declTables_sublist (pd : Declaration) :
    ((declTables pd).map (·.structName)).Sublist ((declConstants pd).map (·.name)) := by
  cases pd with
  | indDecl block nP =>
    simp only [declTables, declConstants]
    cases readBlock nP block with
    | error _ => simp
    | ok p =>
      simp only
      rw [blockConstants_names, List.append_assoc]
      exact (blockTables_sublist p p.members).trans (List.sublist_append_left _ _)
  | _ => simp [declTables]

theorem recsTables_sublist :
    ∀ ds : List Declaration,
      ((ds.flatMap declTables).map (·.structName)).Sublist ((recsConsts ds).map (·.name))
  | [] => .refl _
  | pd :: ds => by
    simp only [recsConsts, List.flatMap_cons, List.map_append]
    exact (declTables_sublist pd).append (recsTables_sublist ds)

/-! ## The view of a position answers as the fold's index -/

theorem view_counter {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) :
    I.firsts.getD pre.length I.next = (recsConsts pre).length := by
  by_cases hk : pre.length < (pre ++ rest).length
  · have h := hI.firsts pre.length hk
    rw [List.take_left] at h
    simp [Array.getD_eq_getD_getElem?, h]
  · have hr : rest = [] := by
      simp only [List.length_append] at hk
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    have hsz := hI.size
    have : ¬ pre.length < I.firsts.size := by rw [hsz]; simp
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simpa using hI.next

theorem view_eq {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) :
    I.view pre.length = ⟨⟨[], []⟩, {},
      { I.base with below := (recsConsts pre).length, belowRec := pre.length }, [], {}⟩ := by
  simp only [StreamIndex.view, view_counter hI]

theorem view_find {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) (n : Name) :
    (I.view pre.length).find? n = (firstOcc n 0 (recsConsts pre)).map (·.2) := by
  rw [view_eq hI]
  simp only [FEnv.find?, FEnv.lookup_eq, Std.HashMap.getElem?_empty, FBase.find?]
  rw [hI.idx n]
  have hsplit : recsConsts (pre ++ rest) = recsConsts pre ++ recsConsts rest := by
    simp [recsConsts]
  rw [hsplit, firstOcc_append, Nat.zero_add]
  cases hp : firstOcc n 0 (recsConsts pre) with
  | some p =>
    obtain ⟨c, ci⟩ := p
    have := (firstOcc_ge hp).2
    simp only [Option.or, Option.map_some]
    rw [ite_eq_left (by omega)]
  | none =>
    simp only [Option.or, Option.map_none]
    cases hr : firstOcc n (recsConsts pre).length (recsConsts rest) with
    | none => rfl
    | some p =>
      obtain ⟨c, ci⟩ := p
      have := (firstOcc_ge hr).1
      simp only
      rw [ite_eq_right (by omega)]

theorem view_rawTable {pre rest : List Declaration} {I : StreamIndex}
    (hI : IndexSpec (pre ++ rest) I) (T : Name) :
    (I.view pre.length).rawTable? T = (firstTbl T (recsTables 0 pre)).map (·.2) := by
  rw [view_eq hI]
  simp only [FEnv.rawTable?, Std.HashMap.getElem?_empty, FBase.findTable?]
  rw [hI.tbls T, recsTables_append, firstTbl_append, Nat.zero_add]
  cases hp : firstTbl T (recsTables 0 pre) with
  | some e =>
    obtain ⟨r, t⟩ := e
    have := recsTables_bounds (firstTbl_mem hp)
    simp only [Option.or, Option.map_some]
    rw [ite_eq_left (by simp only at this; omega)]
  | none =>
    simp only [Option.or, Option.map_none]
    cases hr : firstTbl T (recsTables pre.length rest) with
    | none => rfl
    | some e =>
      obtain ⟨r, t⟩ := e
      have := recsTables_bounds (firstTbl_mem hr)
      simp only
      rw [ite_eq_right (by simp only at this; omega)]

/-- **The view of a position is a twin of the fold's index there**, the names so far being
distinct. -/
theorem viewTwin {pre rest : List Declaration} {I : StreamIndex} (hI : IndexSpec (pre ++ rest) I)
    {fe : FEnv} (hfe : fe = mkFEnv (streamEnv pre))
    (hnd : ((recsConsts pre).map (·.name)).Nodup) : Twin fe (I.view pre.length) := by
  have hcons : (streamEnv pre).consts = (recsConsts pre).reverse := by
    simpa [Env.empty] using streamEnv_consts pre Env.empty
  have htabs : (streamEnv pre).tables = (pre.flatMap declTables).reverse := by
    simpa [Env.empty] using streamEnv_tables pre Env.empty
  subst hfe
  refine ⟨?_, ?_, rfl, rfl⟩
  · funext n
    rw [mkFEnv_find?, view_find hI, firstOcc_map]
    unfold Env.find?
    rw [hcons]
    exact find?_reverse_of_nodup (fun ci : ConstantInfo => ci.name) n hnd
  · funext T
    rw [mkFEnv_rawTable?, view_rawTable hI, firstTbl_map, recsTables_snd, htabs]
    exact find?_reverse_of_nodup (fun t : ProjTable => t.structName) T ((recsTables_sublist pre).nodup hnd)

/-! ## The jobs and the fold -/

/-- **Every job passing is an accepting run**, position by position. -/
theorem jobs_run {ds : Array Declaration}
    (h : ∀ k (hk : k < ds.size), recordJob mode pins (buildIndex ds) k ds[k] = .ok ()) :
    ∀ k, k ≤ ds.size → ∃ fe,
      DeclsRun mode pins (ds.toList.take k) (0, mkFEnv Env.empty) (k, fe) ∧
      PushChain Env.empty fe ∧ fe = mkFEnv (streamEnv (ds.toList.take k))
  | 0, _ => ⟨mkFEnv Env.empty, by simpa using DeclsRun.nil _, PushChain.refl _, rfl⟩
  | k + 1, hk => by
    obtain ⟨fe, hrun, hchain, hfe⟩ := jobs_run h k (by omega)
    have hk' : k < ds.size := by omega
    have hkl : (ds.toList.take k).length = k := by simp; omega
    have hsplit : ds.toList.take k ++ ds.toList.drop k = ds.toList := List.take_append_drop k _
    have hI : IndexSpec (ds.toList.take k ++ ds.toList.drop k) (buildIndex ds) := by
      rw [hsplit]; exact buildIndex_spec ds
    have hnd : ((recsConsts (ds.toList.take k)).map (·.name)).Nodup := by
      have hN : NodupNames fe.env := hchain.2.2.1 (by simp [NodupNames, Env.empty])
      have hc : fe.env.consts = (recsConsts (ds.toList.take k)).reverse := by
        rw [hfe]
        show (streamEnv (ds.toList.take k)).consts = _
        simpa [Env.empty] using streamEnv_consts (ds.toList.take k) Env.empty
      unfold NodupNames at hN
      rw [hc, List.map_reverse] at hN
      exact (List.reverse_perm _).nodup_iff.mp hN
    have ht : Twin fe ((buildIndex ds).view k) := hkl ▸ viewTwin hI hfe hnd
    have hjob := h k hk'
    unfold recordJob at hjob
    split at hjob
    case isFalse => exact nomatch hjob
    rename_i hand
    rcases checkDeclStepC_twin (mode := mode) pins ht ds[k] {} with
      ⟨e, -, h₂⟩ | ⟨a₁, a₂, s', h₁, h₂, L', Q', rfl, rfl⟩
    · rw [h₂] at hjob; exact nomatch hjob
    · have hpush := checkDeclStepC_pushes (pins := pins) mode fe ds[k] {} _ s' h₁
      have hstep : declStep mode pins (k, fe) ds[k] = .ok (k + 1, FEnv.pushDelta L' Q' fe) := by
        unfold declStep
        simp only [hand, ↓reduceIte, h₁]
      have hL : ds.toList.take (k + 1) = ds.toList.take k ++ [ds[k]] := by
        rw [List.take_add_one]
        simp [Array.getElem?_eq_getElem hk']
      have hchain' := checkDeclStepC_push (pins := pins) mode hchain ds[k] {} _ s' h₁
      have hfe' : FEnv.pushDelta L' Q' fe = mkFEnv (streamEnv (ds.toList.take (k + 1))) := by
        rw [hpush, hfe, pushDelta_mkFEnv, hL]
        congr 1
        simp [streamEnv, List.foldl_append]
      refine ⟨_, ?_, hchain', hfe'⟩
      rw [hL]; exact hrun.snoc mode hstep

/-- **Every job passing is an accept of the fold**, at the environment the records denote. -/
theorem checkDecls_of_jobs {ds : Array Declaration}
    (h : ∀ k (hk : k < ds.size), recordJob mode pins (buildIndex ds) k ds[k] = .ok ()) :
    checkDecls mode pins ds = .ok (streamEnv ds.toList) := by
  obtain ⟨fe, hrun, -, hfe⟩ := jobs_run h ds.size (Nat.le_refl _)
  rw [List.take_of_length_le (by simp)] at hrun hfe
  rw [checkDecls_of_run mode hrun, hfe]
  rfl

end ConLeche.Cached
