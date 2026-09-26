module

public import ConLeche.Semantics.Tower.FixRecCoreI

@[expose] public section

/-!
# The recursive squash regime's large eliminator (task #202, Stage A2)

At `w = 0` the family's fibres are truth values and the sole proof is
the point; with a large eliminator (`ℓ ≠ 0`) the recursor cannot case
on the major.  The block has ONE constructor whose data fields are
index expressions (the subsingleton criterion), so at a tuple `t` the
constructor's spine is READ OFF THE INDICES (`sqSpine`: the sum route's
`srcVals`), and the recursor's value is determined by the recursion
equation `R t = m (spine t) (ih⃗ from R at the predecessors)`.  The
value is the unique element of the recursor's GRAPH (`sqGraph`, the
least fixed point of `recGraphStep`, `ConLeche/SetModel/RecGraph`) —
singleton at every tuple of the family, by lfp induction on the
family's functor (`sqGraph_singleton`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel ConLeche.SetTheory
open SetTheory ConLeche.SetTheory.Tower

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Frame kit -/

theorem consList_getD_lt : ∀ (as : List V) (σ : Nat → V) (k : Nat), k < as.length →
    consList as σ k = as.getD (as.length - 1 - k) pt
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | a :: as, σ, k, hk => by
    rw [consList_cons]
    rcases Nat.lt_or_ge k as.length with hlt | hge
    · rw [consList_getD_lt as (cons a σ) k hlt, List.length_cons,
        show as.length + 1 - 1 - k = (as.length - 1 - k) + 1 from by omega, List.getD_cons_succ]
    · have hk' : k = as.length := by simp at hk; omega
      subst hk'
      have := consList_apply_add as (cons a σ) 0
      rw [Nat.zero_add] at this
      rw [this, cons_zero, List.length_cons, Nat.add_sub_cancel, Nat.sub_self, List.getD_cons_zero]

theorem map_teleVarsAV_interp' {m : Nat} {bs : List V} (hm : bs.length = m) (ρ : Nat → V) :
    (teleVarsAV m).map (interp V (consList bs ρ)) = bs := by
  subst hm
  have h : (teleVarsAV bs.length).map (interp V (consList bs ρ))
      = frameIdx bs.length (consList bs ρ) := by
    unfold teleVarsAV frameIdx
    rw [List.map_map]
    apply List.map_congr_left
    intro l _
    simp only [Function.comp_def, interp_bvar]
  rw [h, frameIdx_consList']

theorem map_teleVarsAV_interp (bs : List V) (ρ : Nat → V) :
    (teleVarsAV bs.length).map (interp V (consList bs ρ)) = bs :=
  map_teleVarsAV_interp' rfl ρ

/-! ## The slot's value along a telescope spine -/


/-! ## The sources -/

omit [SetTheory V] in
theorem srcList_length (Es : List AnnotTerm) (nF : Nat) : (srcList Es nF).length = nF := by
  simp [srcList]

theorem srcVals_length (is : List V) (src : List (Option Nat)) : (srcVals is src).length = src.length := by
  simp [srcVals]

omit [SetTheory V] in
/-- A source position's expression is the field's variable. -/
theorem srcOfEs_some {Es : List AnnotTerm} {nF j l : Nat} (h : srcOfEs Es nF j = some l) :
    l < Es.length ∧ Es.getD l default = .bvar (nF - 1 - j) := by
  unfold srcOfEs at h
  refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), ?_⟩
  have hp := List.find?_some h
  revert hp
  cases Es.getD l default <;> simp

omit [SetTheory V] in
/-- At an unsourced field no index expression is the field's variable. -/
theorem srcOfEs_none {Es : List AnnotTerm} {nF j l : Nat} (h : srcOfEs Es nF j = none)
    (hl : Es[l]? = some (.bvar (nF - 1 - j))) : False := by
  unfold srcOfEs at h
  have hlt : l < Es.length := (List.getElem?_eq_some_iff.mp hl).1
  have := List.find?_eq_none.mp h l (List.mem_range.mpr hlt)
  rw [List.getD_eq_getElem?_getD, hl, Option.getD_some] at this
  simp at this

/-- **The subsingleton criterion**: a spine fitting the fields whose
index values are the tuple is the source spine (an index-sourced field
is the index's value, the other fields are `Prop`s — points). -/
theorem srcVals_of_fit {ρp : Nat → V} {Fs Es : List AnnotTerm}
    (hprop : ∀ j, j < Fs.length → srcOfEs Es Fs.length j = none →
      ∀ fs : List V, SpineFit ρp (Fs.take j) fs →
        interp V (consList fs ρp) (Fs.getD j default) ∈ˢ (univZero : V))
    {fs is : List V} (hfit : SpineFit ρp Fs fs) (hidx : idxValsAt ρp Es fs = is) :
    fs = srcVals is (srcList Es Fs.length) := by
  have hlen : fs.length = Fs.length := hfit.length_eq
  apply List.ext_getElem
  · rw [srcVals_length, srcList_length, hlen]
  intro j h1 h2
  rw [srcVals_length, srcList_length] at h2
  have hfj : fs[j] = fs.getD j pt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  rw [hfj]
  cases hs : srcOfEs Es Fs.length j with
  | some l =>
    simp only [srcVals, srcList, List.getElem_map, List.getElem_range, hs]
    obtain ⟨hl, hE⟩ := srcOfEs_some hs
    subst hidx
    show fs.getD j pt = (Es.map (interp V (consList fs ρp))).getD l pt
    have hr : (Es.map (interp V (consList fs ρp))).getD l pt = interp V (consList fs ρp) Es[l] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]; rfl
    have hEl : Es[l] = AnnotTerm.bvar (Fs.length - 1 - j) := by
      rw [← hE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl
    rw [hr, hEl, interp_bvar, consList_getD_lt fs ρp _ (by omega),
      show fs.length - 1 - (Fs.length - 1 - j) = j from by omega]
  | none =>
    simp only [srcVals, srcList, List.getElem_map, List.getElem_range, hs]
    have hmem := FixKI.spineFit_getD_mem' hfit h2
    have hsp : SpineFit ρp (Fs.take j) (fs.take j) := by
      have := spineFit_prefix (as := fs.take j) (bs := fs.drop j) (by rw [List.take_append_drop]; exact hfit)
      rwa [List.length_take, hlen, Nat.min_eq_left (Nat.le_of_lt h2)] at this
    exact eq_pt_of_mem_univZero (hprop j h2 hs _ hsp) hmem

/-! ## The squash data at a tuple -/

/-- The index spine of a tuple (at level `0` every index is a proof). -/
noncomputable def isOfW (u nIdx : Nat) (t : V) : List V :=
  if u = 0 then List.replicate nIdx pt else projList nIdx t

/-- A fitting spine over `Prop`-regime domains is the points. -/
theorem spineFit_zero_replicate :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V} {is : List V}, FieldsBound 0 ρ Fs → SpineFit ρ Fs is →
      is = List.replicate Fs.length pt
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, h => h.elim
  | _ :: _, _, [], _, h => h.elim
  | F :: Fs, ρ, a :: is, hb, hsp => by
    obtain ⟨ha, hsp'⟩ := hsp
    have hpt : a = pt := by
      have := hb.1
      rw [univ_zero] at this
      exact eq_pt_of_mem_univZero this ha
    subst hpt
    rw [List.length_cons, List.replicate_succ]
    exact congrArg _ (spineFit_zero_replicate (hb.2 pt ha) hsp')

theorem isOfW_tupW {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} (hI : IdxOk u ρp Ids)
    {is : List V} (hsp : SpineFit ρp Ids is) : isOfW u Ids.length (tupW u is) = is := by
  by_cases hu : u = 0
  · rw [isOfW, if_pos hu]
    subst hu
    exact (spineFit_zero_replicate hI.2 hsp).symm
  · rw [isOfW, tupW, if_neg hu, if_neg hu]
    exact projList_mkTower _ _ hsp.length_eq

/-! ## The squash body at a K-frame -/

section Body

variable {ℓ u nP : Nat} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss : List (List (List AnnotTerm))} {rds : List (Nat × Nat × AnnotTerm)}

/-! ## The recursor's value at a K-frame -/

/-- A tuple of the index set is the tuple of a fitting spine. -/
theorem mem_idxSet_elim {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {t : V}
    (ht : t ∈ˢ idxSet u ρp Ids) : ∃ is : List V, SpineFit ρp Ids is ∧ t = tupW u is := by
  by_cases hu : u = 0
  · subst hu
    obtain ⟨rfl, as, has⟩ := towerSet_zero_elim (teleOfFields ρp Ids) ht
    exact ⟨as, fitsS_teleOfFields.mp has, (tupW_zero as).symm⟩
  · obtain ⟨hsp, heq⟩ := towerSet_elim_teleOfFields hu ht
    exact ⟨_, hsp, by rw [tupW_pos hu]; exact heq⟩

end Body

end ConLeche.Semantics
