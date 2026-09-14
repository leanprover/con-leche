module

public import ConLeche.Verify.Inductives.NestedInv
public import ConLeche.Verify.Inductives.NestedCopyStored
public import ConLeche.Kernel.Inductives.NestedInstall
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.NestedFacts

public section

/-!
# The restored constructors' NAMES (task #279 M-D′)

Two facts the nested install's post-checks owe the store:

* the restored constructors went through the PRE-ANNOTATED front door
  (`checkConstantValPre`, K.19) at the formers' environment, and that
  door returns its input — so a restored constant is its own front-door
  answer (`restoreCtors_pre`), which is what a re-check at the stored
  record asks for;
* the restored constructors of the REAL members carry distinct names
  (`nestedRestoredCtors_nodup`).  They are the auxiliary block's own
  constructors of the members below `p.k`: `auxStored?` reads member
  `t`'s constructors off `b.ownCtors t` at the scratch environment
  (`auxStored?_ctors`), the restore keeps the name
  (`restoreCtors_id`), and a lookup answers with a constant OF THAT
  NAME (`Env.find?_name`).  Distinctness is then the mutual core's
  first conjunct — `b.blockNames.Nodup` — read through the block
  indices: within a member the indices are a filter of `zipIdx`'s and
  within the flatten the members separate them.
-/

namespace ConLeche

/-! ## A member's own constructors, by block index -/

/-- A member's own constructor is the block's constructor at its
recorded index, and its member is that member. -/
theorem ownCtors_spec {b : MutualBlock} {t J : Nat} {c : MutualCtor}
    (h : (J, c) ∈ b.ownCtors t) : b.ctors[J]? = some c ∧ c.member = t := by
  unfold MutualBlock.ownCtors at h
  obtain ⟨hmem, hp⟩ := List.mem_filter.mp h
  refine ⟨?_, by simpa using hp⟩
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
  obtain ⟨c', J'⟩ := q
  simp only [Prod.mk.injEq] at hqe
  obtain ⟨rfl, rfl⟩ := hqe
  exact List.mk_mem_zipIdx_iff_getElem?.mp hq

/-- A member's own constructors carry DISTINCT block indices: the list
is a filter of `zipIdx`'s, whose second components are a `range'`. -/
theorem ownCtors_fst_nodup {b : MutualBlock} {t : Nat} :
    ((b.ownCtors t).map (fun q => q.1)).Nodup := by
  have hsub : (b.ownCtors t).Sublist (b.ctors.zipIdx.map (fun (c, J) => (J, c))) := by
    unfold MutualBlock.ownCtors
    exact List.filter_sublist
  have hmap : (b.ctors.zipIdx.map (fun (c, J) => (J, c))).map (fun q => q.1)
      = b.ctors.zipIdx.map Prod.snd := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro q _
    obtain ⟨c, J⟩ := q
    rfl
  refine List.Sublist.nodup (List.Sublist.map _ hsub) ?_
  rw [hmap, List.zipIdx_map_snd]
  exact List.nodup_range'

/-! ## The block's constructor names -/

/-- Two DIFFERENT positions of the block's constructor list carry
different names. -/
theorem ctorName_ne_of_index_ne {b : MutualBlock}
    (hnd : (b.ctors.map (·.cv.name)).Nodup) {J J' : Nat} {c c' : MutualCtor}
    (h : b.ctors[J]? = some c) (h' : b.ctors[J']? = some c') (hne : J ≠ J') :
    c.cv.name ≠ c'.cv.name := by
  intro heq
  refine hne ?_
  have hJ : J < (b.ctors.map (·.cv.name)).length := by
    simpa using (List.getElem?_eq_some_iff.mp h).1
  refine (List.getElem?_inj hJ hnd).mp ?_
  rw [List.getElem?_map, List.getElem?_map, h, h']
  simp [heq]

/-- One member's own constructor names are distinct. -/
theorem ownCtors_names_nodup {b : MutualBlock}
    (hnd : (b.ctors.map (·.cv.name)).Nodup) (t : Nat) :
    ((b.ownCtors t).map (fun q => q.2.cv.name)).Nodup := by
  have hfst : ((b.ownCtors t).map (fun q => q.1)).Nodup := ownCtors_fst_nodup
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hfst ⊢
  refine hfst.imp_of_mem ?_
  intro q q' hq hq' hJ
  obtain ⟨J, c⟩ := q
  obtain ⟨J', c'⟩ := q'
  exact ctorName_ne_of_index_ne hnd (ownCtors_spec hq).1 (ownCtors_spec hq').1 hJ

/-- The members' own constructor names, flattened over the first `N`
members, are distinct: within a member by the block indices, across
members because a constructor belongs to ONE member. -/
theorem ownCtorNames_flatten_nodup {b : MutualBlock}
    (hnd : (b.ctors.map (·.cv.name)).Nodup) (N : Nat) :
    (((List.range N).map fun t => (b.ownCtors t).map fun q => q.2.cv.name).flatten).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hl
    exact ownCtors_names_nodup hnd t
  · rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ (List.nodup_range (n := N))
    intro t t' hne x hx y hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hy
    obtain ⟨J, c⟩ := q
    obtain ⟨J', c'⟩ := q'
    obtain ⟨hc, hm⟩ := ownCtors_spec hq
    obtain ⟨hc', hm'⟩ := ownCtors_spec hq'
    refine ctorName_ne_of_index_ne hnd hc hc' ?_
    intro hJ
    subst hJ
    have hcc : c = c' := Option.some.inj (hc.symm.trans hc')
    exact hne (by rw [← hm, ← hm', hcc])

/-! ## The stored record's constructor list -/

/-- The stored record carries one constructor per own constructor of
the member (`auxStored?`'s `mapM` over `b.ownCtors`). -/
theorem auxStored?_ctors_length {envAux : Env} {b : MutualBlock} {i : Nat} {a : AuxStored}
    (h : auxStored? envAux b i = some a) : a.ctors.length = (b.ownCtors i).length := by
  unfold auxStored? at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨x, hf, ci, hci, h⟩ := h
  split at h
  · next cvTa caps =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨ci', -, h⟩ := h
    split at h
    · next cvRa mI rP rules =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ctors, hctors, h⟩ := h
      simp only [pure, Option.some.injEq] at h
      subst h
      exact (optionMapM_getElem? hctors).1
    · exact nomatch h
  · exact nomatch h

/-! ## The restored constructors -/

/-- The restored constructors went through the pre-annotated front door
at the formers' environment, and that door returns its input. -/
theorem restoreCtors_pre {mode : CheckMode} {env : Env} {R : RestoreTbl} {lps : List Name}
    {F : Nat} :
    ∀ {cs out : List (ConstantVal × Nat × Nat)},
      restoreCtors (m := CheckM) (fueledOps mode F) env R lps cs = .ok out →
      ∀ o ∈ out, checkConstantValPre (m := CheckM) (fueledOps mode F) env o.1 = .ok o.1 := by
  intro cs
  induction cs with
  | nil =>
    intro out h o ho
    simp only [restoreCtors, pure, Except.pure, Except.ok.injEq] at h
    rw [← h] at ho; exact absurd ho (by simp)
  | cons hd rest ih =>
    intro out h o ho
    obtain ⟨cvCa, nP, nF⟩ := hd
    unfold restoreCtors at h
    obtain ⟨ty, -, h⟩ := exceptBind_ok h
    obtain ⟨cvA, hpre, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    rcases List.mem_cons.mp ho with rfl | ho
    · show checkConstantValPre (m := CheckM) (fueledOps mode F) env cvA = .ok cvA
      have hid := checkConstantValPre_ok hpre
      subst hid
      exact hpre
    · exact ih hrest o ho

/-- **The restored constructors' names, positionally**: the restore
keeps the stored record's names, list by list. -/
theorem nestedRestoredCtors_names {mode : CheckMode} {F : Nat} {env₁ : Env}
    {p : NestedParts} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {R : RestoreTbl}
    (hctors : (stored.take p.k).mapM (fun a =>
        restoreCtors (m := CheckM) (fueledOps mode F) env₁ R p.lps a.ctors) = .ok ctorsR) :
    ∀ (i : Nat) (a : AuxStored) (o : List (ConstantVal × Nat × Nat)),
      (stored.take p.k)[i]? = some a → ctorsR[i]? = some o →
        o.length = a.ctors.length ∧
        ∀ (l : Nat) (c x : ConstantVal × Nat × Nat),
          a.ctors[l]? = some c → o[l]? = some x → x.1.name = c.1.name := by
  intro i a o ha ho
  obtain ⟨hlenR, hall⟩ := mapM_except_inv hctors
  have hi : i < (stored.take p.k).length := by
    have := (List.getElem?_eq_some_iff.mp ho).1
    omega
  obtain ⟨a', o', ha', ho', hrun⟩ := hall i hi
  have haa : a' = a := Option.some.inj (ha'.symm.trans ha)
  have hoo : o' = o := Option.some.inj (ho'.symm.trans ho)
  rw [haa, hoo] at hrun
  obtain ⟨hlen, hpos⟩ := restoreCtors_id hrun
  refine ⟨hlen, ?_⟩
  intro l c x hc hx
  obtain ⟨ty, -, rfl⟩ := hpos l c x hc hx
  rfl

/-- **The restored constructors of the real members carry distinct names**:
they are the auxiliary block's own constructors of the members below `p.k`
(`auxStored?` reads member `t`'s constructors off `b.ownCtors t` at the
scratch environment), and the block's constructor names are distinct
(`b.blockNames.Nodup`, the mutual core's first conjunct). -/
theorem nestedRestoredCtors_nodup {mode : CheckMode} {F : Nat} {env envAux env₁ : Env}
    {p : NestedParts} {b : MutualBlock} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {R : RestoreTbl}
    (hcore : checkMutualCore (m := CheckM) (fueledOps mode F) env b none true = .ok envAux)
    (hstored : auxStoredAll envAux b b.k = some stored)
    (hctors : (stored.take p.k).mapM (fun a =>
        restoreCtors (m := CheckM) (fueledOps mode F) env₁ R p.lps a.ctors) = .ok ctorsR) :
    (ctorsR.flatten.map (·.1.name)).Nodup := by
  -- the block's constructor names are distinct (the mutual core's first conjunct)
  have hnd : (b.ctors.map (·.cv.name)).Nodup := by
    have hNd := (checkMutualCore_inv hcore).1
    unfold MutualBlock.blockNames at hNd
    obtain ⟨hNd₁, -, -⟩ := List.nodup_append.mp hNd
    exact (List.nodup_append.mp hNd₁).2.1
  -- each restored member's names ARE the member's own constructors' names
  have hnames : ∀ (t : Nat) (o : List (ConstantVal × Nat × Nat)), ctorsR[t]? = some o →
      o.map (fun x => x.1.name) = (b.ownCtors t).map (fun q => q.2.cv.name) := by
    intro t o ho
    obtain ⟨hlenR, hall⟩ := mapM_except_inv hctors
    have ht : t < (stored.take p.k).length := by
      have := (List.getElem?_eq_some_iff.mp ho).1
      omega
    obtain ⟨a, o', ha, ho', hrun⟩ := hall t ht
    have hoo : o' = o := Option.some.inj (ho'.symm.trans ho)
    rw [hoo] at hrun
    have hak : auxStored? envAux b t = some a := by
      have htk : t < p.k := by
        have hlt : (stored.take p.k).length = min p.k stored.length := List.length_take
        omega
      rw [List.getElem?_take_of_lt htk] at ha
      exact (auxStoredAll_get hstored).2 t a ha
    obtain ⟨hlenO, hposO⟩ := restoreCtors_id hrun
    have hlenA : a.ctors.length = (b.ownCtors t).length := auxStored?_ctors_length hak
    refine List.ext_getElem? fun l => ?_
    rw [List.getElem?_map, List.getElem?_map]
    by_cases hl : l < (b.ownCtors t).length
    · obtain ⟨⟨J, c⟩, hJc⟩ : ∃ q, (b.ownCtors t)[l]? = some q := ⟨_, List.getElem?_eq_getElem hl⟩
      obtain ⟨y, hy, hfind⟩ := auxStored?_ctors hak l J c hJc
      obtain ⟨x, hx⟩ : ∃ x, o[l]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ty, -, rfl⟩ := hposO l y x hy hx
      have hyc : y.1.name = c.cv.name := by
        have hn := Env.find?_name hfind
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using hn
      rw [hx, hJc]
      simp [hyc]
    · rw [List.getElem?_eq_none_iff.mpr (by omega : (b.ownCtors t).length ≤ l),
        List.getElem?_eq_none_iff.mpr (by omega : o.length ≤ l)]
      rfl
  -- the flattened name list is the members' own names, flattened
  have hlists : ctorsR.map (fun o => o.map (fun x => x.1.name))
      = (List.range ctorsR.length).map
          (fun t => (b.ownCtors t).map (fun q => q.2.cv.name)) := by
    refine List.ext_getElem? fun i => ?_
    rw [List.getElem?_map, List.getElem?_map]
    cases hi : ctorsR[i]? with
    | none =>
      rw [List.getElem?_eq_none_iff.mpr
        (by simpa using List.getElem?_eq_none_iff.mp hi : (List.range ctorsR.length).length ≤ i)]
      rfl
    | some o =>
      rw [List.getElem?_range (List.getElem?_eq_some_iff.mp hi).1]
      simpa using hnames i o hi
  have heq : ctorsR.flatten.map (·.1.name)
      = ((List.range ctorsR.length).map
          (fun t => (b.ownCtors t).map (fun q => q.2.cv.name))).flatten := by
    rw [List.map_flatten, hlists]
  rw [heq]
  exact ownCtorNames_flatten_nodup hnd _

end ConLeche
