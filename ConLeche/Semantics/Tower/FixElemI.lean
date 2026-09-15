module

public import ConLeche.Semantics.Tower.FixSquashI

@[expose] public section
/-!
# The recursor's graph over the elements (task #202 Stage B)

The graph regime's large eliminator at a recursive family whose fields
may be infinitary (a recursive field under a telescope — `Acc`-shaped
blocks at `Type`, W-types): the recursor's value at an ELEMENT `(t, x)`
(a tuple and a member of the family's fibre) is determined by the
recursion equation — minor `j` at `x`'s fields and the ih values, the
λ-towers over the recursive fields' telescopes of the recursor at the
calls' elements.  Stage A recursed on the ω-iterate's stages (finitary
fields only); this module instantiates the abstract recursion theorem
(`RecGraph`) at the elements: the index set `elemSet` (the pairs), the
predecessors `elemPred` (the recursive fields' values along their
telescopes at the calls' tuples), the bound `elemB` (the motive at the
indices and the element) and the step `elemSt`; the graph
`elemGraph` is a singleton at every element by lfp induction on the
family (`elemGraph_singleton`), so its selector obeys the recursion
equation (`elemK_facts`) — which is the body's iota at the K-frame.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.SetTheory.Tower

universe uv
variable {V : Type uv} [SetTheory V]

/-! ## The element data -/

/-- The elements of a family: the pairs of a tuple and a member of its
fibre. -/
noncomputable def elemSet (u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (μ : V) : V :=
  sigmaPairs (idxSet u ρp Ids) (fun t => SetTheory.app μ t)

/-- An element's constructor tag — the value's LOCAL tag (junk off the
elements). -/
noncomputable def elemTag (e : V) : Nat := natIdx (sfst (ssnd e))

/-- An element's constructor's FLAT position (task #279 D-1): the tag
map at the element's tuple applied to its local tag; the tag itself at
the empty table. -/
noncomputable def elemFlat (tbl : List (List Nat)) (Fss : List (List AnnotTerm)) (e : V) : Nat :=
  tagOf tbl Fss.length (sfst e) (elemTag e)

/-- An element's fields. -/
noncomputable def elemFields (tbl : List (List Nat)) (Fss : List (List AnnotTerm)) (e : V) : List V :=
  projList (Fss.getD (elemFlat tbl Fss e) []).length (ssnd (ssnd e))

theorem elemTag_mk (t : V) (jc : Nat) (fs : List V) :
    elemTag (kpair t (inj jc (mkTower (fs ++ [pt])))) = jc := by
  unfold elemTag
  rw [ssnd_kpair, sfst_inj, natIdx_vnat]

theorem elemFlat_mk (tbl : List (List Nat)) (Fss : List (List AnnotTerm)) (t : V) (jc : Nat) (fs : List V) :
    elemFlat tbl Fss (kpair t (inj jc (mkTower (fs ++ [pt])))) = tagOf tbl Fss.length t jc := by
  unfold elemFlat
  rw [elemTag_mk, sfst_kpair]

theorem elemFields_mk {tbl : List (List Nat)} {Fss : List (List AnnotTerm)} (t : V) {jc j : Nat}
    (hJ : j = tagOf tbl Fss.length t jc) {fs : List V} (hlen : fs.length = (Fss.getD j []).length) :
    elemFields tbl Fss (kpair t (inj jc (mkTower (fs ++ [pt])))) = fs := by
  unfold elemFields
  rw [elemFlat_mk, ← hJ, ssnd_kpair, ssnd_inj, ← hlen, projList_mkTower_append]

/-- The predecessors of an element: for each recursive field and each
spine fitting its telescope, the call's tuple paired with the field
applied to the spine. -/
noncomputable def elemPred (tbl : List (List Nat)) (u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm)))
    (Fss : List (List AnnotTerm)) (μ : V) (e : V) : V :=
  sep (elemSet u ρp Ids μ) fun e' =>
    ∃ i ∈ recIdx (rss.getD (elemFlat tbl Fss e) []) (Fss.getD (elemFlat tbl Fss e) []).length, ∃ bs : List V,
      SpineFit (consList ((elemFields tbl Fss e).take i) ρp) (((tlss.getD (elemFlat tbl Fss e) []).getD i []).map (·.2.2)) bs ∧
      e' = kpair
        (tupW u (((Eiss.getD (elemFlat tbl Fss e) []).getD i []).map
          (interp V (consList bs (consList ((elemFields tbl Fss e).take i) ρp)))))
        (bs.foldl SetTheory.app ((elemFields tbl Fss e).getD i pt))

/-- The bound: the motive at the tuple's indices and the element. -/
noncomputable def elemB (u nIdx : Nat) (M : V) (e : V) : V :=
  SetTheory.app ((isOfW u nIdx (sfst e)).foldl SetTheory.app M) (ssnd e)

/-- The ih values from a choice `g` of the predecessors' values: for
each recursive field, the λ-tower over its telescope of `g` at the
call's element. -/
noncomputable def elemIhs (ℓ u : Nat) (ρp : Nat → V) (rs : List Bool)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) (nF : Nat)
    (fs : List V) (g : V) : List V :=
  (recIdx rs nF).map fun i =>
    lamTower ℓ (consList (fs.take i) ρp) (tls.getD i []) fun σ' =>
      SetTheory.app g (kpair (tupW u ((Eis.getD i []).map (interp V σ')))
        ((frameIdx (tls.getD i []).length σ').foldl SetTheory.app (fs.getD i pt)))

/-- The step: the element's minor (from the minors' list) at its fields
and the ih values. -/
noncomputable def elemSt (tbl : List (List Nat)) (ℓ u : Nat) (ρp : Nat → V) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm)))
    (Fss : List (List AnnotTerm)) (msL : List V) (e g : V) : V :=
  (elemFields tbl Fss e ++
    elemIhs ℓ u ρp (rss.getD (elemFlat tbl Fss e) []) (tlss.getD (elemFlat tbl Fss e) [])
      (Eiss.getD (elemFlat tbl Fss e) [])
      (Fss.getD (elemFlat tbl Fss e) []).length (elemFields tbl Fss e) g).foldl SetTheory.app
    (msL.getD (elemFlat tbl Fss e) pt)

/-- **The recursor's graph over the elements.** -/
noncomputable def elemGraph (tbl : List (List Nat)) (ℓ u : Nat) (ρp : Nat → V) (M : V) (Ids : List AnnotTerm) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm)))
    (Fss : List (List AnnotTerm)) (msL : List V) (μ : V) : V :=
  recGraph ℓ (elemSet u ρp Ids μ) (elemPred tbl u ρp Ids rss tlss Eiss Fss μ) (elemB u Ids.length M)
    (elemSt tbl ℓ u ρp rss tlss Eiss Fss msL)

theorem elemPred_subset (tbl : List (List Nat)) (u : Nat) (ρp : Nat → V) (Ids : List AnnotTerm) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm)))
    (Fss : List (List AnnotTerm)) (μ e : V) : elemPred tbl u ρp Ids rss tlss Eiss Fss μ e ⊆ˢ elemSet u ρp Ids μ :=
  sep_subset

theorem mem_elemSet {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {μ e : V} :
    e ∈ˢ elemSet u ρp Ids μ ↔ ∃ t, t ∈ˢ idxSet u ρp Ids ∧ ∃ x, x ∈ˢ SetTheory.app μ t ∧ e = kpair t x :=
  mem_sigmaPairs

theorem mk_mem_elemSet {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {μ t x : V} (ht : t ∈ˢ idxSet u ρp Ids)
    (hx : x ∈ˢ SetTheory.app μ t) : kpair t x ∈ˢ elemSet u ρp Ids μ :=
  mem_sigmaPairs.mpr ⟨t, ht, x, hx, rfl⟩

/-- The predecessors of a constructor value (at its local tag `jc`,
flat position `j`). -/
theorem mem_elemPred_mk {tbl : List (List Nat)} {u : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss : List (List AnnotTerm)} {μ t : V} {jc j : Nat} (hJ : j = tagOf tbl Fss.length t jc) {fs : List V}
    (hlen : fs.length = (Fss.getD j []).length) {e' : V} :
    e' ∈ˢ elemPred tbl u ρp Ids rss tlss Eiss Fss μ (kpair t (inj jc (mkTower (fs ++ [pt])))) ↔
      e' ∈ˢ elemSet u ρp Ids μ ∧
      ∃ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length, ∃ bs : List V,
        SpineFit (consList (fs.take i) ρp) (((tlss.getD j []).getD i []).map (·.2.2)) bs ∧
        e' = kpair (tupW u (((Eiss.getD j []).getD i []).map (interp V (consList bs (consList (fs.take i) ρp)))))
          (bs.foldl SetTheory.app (fs.getD i pt)) := by
  unfold elemPred
  rw [mem_sep, elemFlat_mk, ← hJ, elemFields_mk t hJ hlen]

/-! ## The recursion theorem at the family -/

section Singleton

variable {tbl : List (List Nat)} {ℓ u w : Nat} {ρp : Nat → V} {M : V} {msL : List V} {Fss Ess Fss₀ : List (List AnnotTerm)}
  {Ids : List AnnotTerm} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss : List (List (List AnnotTerm))}

/-- **The graph is a singleton at every element of the family**, by lfp
induction on the family's functor: a member of the fibre at a
sub-family is a constructor value whose spine fits the X-chain there;
its recursive slots fold, along their telescopes, into the sub-family
at the calls' tuples, so every predecessor's fibre is a singleton of
the graph, and the local step applies. -/
theorem elemGraph_singleton (hX : XChainsOk tbl u w ρp Ids rss tlss Eiss Fss₀ Ess)
    (hreal : ChainsRealI (fixFamI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) u w ρp Ids rss tlss
      Eiss Fss₀ Fss Ess)
    (hw : w ≠ 0)
    (hB : ∀ e, e ∈ˢ elemSet u ρp Ids (fixFamI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) →
      elemB u Ids.length M e ∈ˢ (univ ℓ : V))
    (hst : ∀ e, e ∈ˢ elemSet u ρp Ids (fixFamI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) → ∀ g,
      g ∈ˢ piSet (elemPred tbl u ρp Ids rss tlss Eiss Fss (fixFamI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) e)
        (fun e' => SetTheory.app
          (elemGraph tbl ℓ u ρp M Ids rss tlss Eiss Fss msL (fixFamI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess)) e') →
      elemSt tbl ℓ u ρp rss tlss Eiss Fss msL e g ∈ˢ elemB u Ids.length M e) :
    ∀ t, t ∈ˢ idxSet u ρp Ids → ∀ x,
      x ∈ˢ SetTheory.app (fixFamI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) t →
      (∃ v, v ∈ˢ SetTheory.app
        (elemGraph tbl ℓ u ρp M Ids rss tlss Eiss Fss msL (fixFamI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess))
        (kpair t x)) ∧
      ∀ v v', v ∈ˢ SetTheory.app
          (elemGraph tbl ℓ u ρp M Ids rss tlss Eiss Fss msL (fixFamI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess))
          (kpair t x) →
        v' ∈ˢ SetTheory.app
          (elemGraph tbl ℓ u ρp M Ids rss tlss Eiss Fss msL (fixFamI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess))
          (kpair t x) → v = v' := by
  have hI : IdxOk u ρp Ids := hX.hI
  obtain ⟨hl₀, hlE, hEs', hlenj, hc⟩ := hreal
  let μ := fixFamI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess
  let G := elemGraph tbl ℓ u ρp M Ids rss tlss Eiss Fss msL μ
  let P : V → V → Prop := fun t x =>
    (∃ v, v ∈ˢ SetTheory.app G (kpair t x)) ∧
    ∀ v v', v ∈ˢ SetTheory.app G (kpair t x) → v' ∈ˢ SetTheory.app G (kpair t x) → v = v'
  have hpred : ∀ e, e ∈ˢ elemSet u ρp Ids μ → elemPred tbl u ρp Ids rss tlss Eiss Fss μ e ⊆ˢ elemSet u ρp Ids μ :=
    fun e _ => elemPred_subset tbl u ρp Ids rss tlss Eiss Fss μ e
  refine lfpFamSet_induction (w := w) (I := idxSet u ρp Ids)
    (F := fixFunVI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess) (fixFunVI_closed_exists hX)
    (fixFunVI_mono hX) P ?_
  intro t ht x hx
  -- the induction family
  let S := graph (fun i => sep (SetTheory.app (lfpFamSet w (idxSet u ρp Ids)
    (fixFunVI tbl u w ρp Ids Ids.length rss tlss Eiss Fss₀ Ess)) i) (P i)) (idxSet u ρp Ids)
  have hSmem : S ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) := by
    rw [lfpFamSpace_eq]
    exact graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpFamSet_mem _ _ _) hi)
  have hSle : FamLe (idxSet u ρp Ids) S μ := by
    intro i hi y hy
    rw [app_graph hi] at hy
    exact (mem_sep.mp hy).1
  have hfamS : ∀ t', SetTheory.app S t' ∈ˢ (univ w : V) := fun t' => famApp_mem_univ hSmem t'
  -- the member is in the family's fibre
  have hxμ : x ∈ˢ SetTheory.app μ t := by
    have hmono := fixFunVI_mono hX S μ (by rw [← lfpFamSpace_eq]; exact hSmem)
      (by rw [← lfpFamSpace_eq]; exact fixFamI_mem tbl u w ρp Ids rss tlss Eiss Fss₀ Ess) hSle t ht x hx
    exact lfpFamSet_closed (fixFunVI_closed_exists hX) (fixFunVI_mono hX) t ht x hmono
  rw [fixFunVI_app hSmem, famFI_app ht] at hx
  obtain ⟨jc, j, fs, hJ, rfl, hj₀, hlen₀, hspX, -⟩ := fixStepI_elim hw hx
  rw [hl₀] at hJ
  have hj : j < Fss.length := by omega
  have hlen : fs.length = (Fss.getD j []).length := by rw [hlen₀]; exact hlenj j hj
  have hfit := hX.hfit S hSmem t ht j hj₀
  -- the local step at the predecessors
  refine recGraph_singleton_of_preds hB hpred (mk_mem_elemSet ht hxμ)
    (hst _ (mk_mem_elemSet ht hxμ)) fun e' he' => ?_
  obtain ⟨-, i, hi, bs, hbs, rfl⟩ := (mem_elemPred_mk hJ hlen).mp he'
  obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
  have hri' : (rss.getD j []).getD (0 + i) false = true := by rw [Nat.zero_add]; exact hri
  obtain ⟨hslot, hmem⟩ := fitsXI_slot_mem hI (Fss₀.getD j []) 0 [] fs rfl hfit hspX i
    (by rw [hlen₀, hlenj j hj]; exact hik) hri'
  rw [Nat.zero_add, List.nil_append] at hslot hmem
  -- the slot's fold lies in the induction family at the call's tuple
  have hfold := slotSet_fold_mem hfamS hmem hbs
  obtain ⟨-, hvsp⟩ := hslot.2.2 bs hbs
  rw [consList_append] at hvsp
  rw [app_graph (tupW_mem hvsp)] at hfold
  exact (mem_sep.mp hfold).2

end Singleton

/-! ## The recursion equation at a K-frame -/

section KFrame

variable {tbl : List (List Nat)} {ℓ w u : Nat} {K : Nat → V} {Fss Ess Fss₀ : List (List AnnotTerm)} {Ids : List AnnotTerm}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}

/-- A member of the family's fibre at a tuple is a constructor value
whose spine fits the real fields with the tuple as its index values,
and whose recursive slots lie in the slot sets at the family. -/
theorem famK_elim (h : FixKI₀ tbl ℓ w u K Fss Ess Fss₀ Ids rss tlss Eiss) (hw : w ≠ 0)
    {is : List V} (hsp : SpineFit (frP Fss.length Ids.length K) Ids is) {x : V}
    (hx : x ∈ˢ SetTheory.app (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) (tupW u is)) :
    ∃ jc j fs, j = tagOf tbl Fss.length (tupW u is) jc ∧ x = inj jc (mkTower (fs ++ [pt])) ∧
      j < Fss.length ∧ fs.length = (Fss.getD j []).length ∧
      SpineFit (frP Fss.length Ids.length K) (Fss.getD j []) fs ∧
      idxValsAt (frP Fss.length Ids.length K) (Ess.getD j []) fs = is ∧
      ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
        SlotFit u w (frP Fss.length Ids.length K) Ids ((tlss.getD j []).getD i []) ((Eiss.getD j []).getD i [])
          (fs.take i) ∧
        fs.getD i pt ∈ˢ slotSet w u (consList (fs.take i) (frP Fss.length Ids.length K))
          ((tlss.getD j []).getD i []) ((Eiss.getD j []).getD i [])
          (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) := by
  have hI := h.hX.hI
  obtain ⟨hl₀, hlE, hEs, hlenj, hc⟩ := h.hreal
  have hμ := fixFamI_mem tbl u w (frP Fss.length Ids.length K) Ids rss tlss Eiss Fss₀ Ess
  have hfix := lfpFamSet_fixed (fixFunVI_closed_exists h.hX) (fixFunVI_mono h.hX) (fixFunVI_maps h.hX) _
    (tupW_mem hsp) x hx
  unfold fixFamI at hμ
  rw [fixFunVI_app hμ, famFI_app (tupW_mem hsp)] at hfix
  obtain ⟨jc, j, fs, hJ, rfl, hj₀, hlen₀, hspX, hall⟩ := fixStepI_elim hw hfix
  rw [hl₀] at hJ
  have hj : j < Fss.length := by omega
  have hfit := h.hX.hfit _ hμ _ (tupW_mem hsp) j hj₀
  have hlen : fs.length = (Fss.getD j []).length := by rw [hlen₀]; exact hlenj j hj
  refine ⟨jc, j, fs, hJ, rfl, hj, hlen, spineFit_real_of_XI hI (FamLe.refl _ _) (Fss₀.getD j []) (Fss.getD j []) 0 [] fs
    rfl (hc j hj) hfit hspX, ?_, ?_⟩
  · rw [← hlen₀] at hall
    exact idxValsAt_of_eqsXI hI hsp (hEs j hj) hall
  · intro i hi
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    have := fitsXI_slot_mem hI (Fss₀.getD j []) 0 [] fs rfl hfit hspX i (by rw [hlen]; exact hik)
      (by rw [Nat.zero_add]; exact hri)
    rw [Nat.zero_add, List.nil_append] at this
    exact this

/-- The bound at every element of the family lives in `univ ℓ`. -/
theorem elemB_mem (h : FixKI₀ tbl ℓ w u K Fss Ess Fss₀ Ids rss tlss Eiss) :
    ∀ e, e ∈ˢ elemSet u (frP Fss.length Ids.length K) Ids (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) →
      elemB u Ids.length (frM Fss.length Ids.length K) e ∈ˢ (univ ℓ : V) := by
  intro e he
  obtain ⟨t, ht, x, hx, rfl⟩ := mem_elemSet.mp he
  obtain ⟨is, hsp, rfl⟩ := mem_idxSet_elim ht
  unfold elemB
  rw [sfst_kpair, ssnd_kpair, isOfW_tupW h.hX.hI hsp]
  have hM := piTele_fold (Nat.succ_ne_zero ℓ) h.hyp.hMtele (fitsS_teleOfFields.mpr hsp)
  rw [List.nil_append] at hM
  exact app_mem_piR hM hx (fun h0 => absurd h0 (Nat.succ_ne_zero ℓ))

/-- The graph's fibres lie in the bound. -/
theorem elemGraph_sub_B (h : FixKI₀ tbl ℓ w u K Fss Ess Fss₀ Ids rss tlss Eiss) {e v : V}
    (he : e ∈ˢ elemSet u (frP Fss.length Ids.length K) Ids (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss))
    (hv : v ∈ˢ SetTheory.app (elemGraph tbl ℓ u (frP Fss.length Ids.length K) (frM Fss.length Ids.length K) Ids rss
      tlss Eiss Fss (frMsL Fss.length Ids.length K) (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss)) e) :
    v ∈ˢ elemB u Ids.length (frM Fss.length Ids.length K) e := by
  unfold elemGraph at hv
  rw [app_recGraph_eq (elemB_mem h) (fun e _ => elemPred_subset tbl u _ Ids rss tlss Eiss Fss _ e) he] at hv
  exact (mem_recGraphFibre.mp hv).1

/-- **The step lands in the bound** at every element and every choice
of the predecessors' values: the minor at the fields lies in the ih
tower, the ih values are λ-towers whose leaves are the choice's values
at the calls, in the motive there. -/
theorem elemSt_mem (h : FixKI₀ tbl ℓ w u K Fss Ess Fss₀ Ids rss tlss Eiss) (hw : w ≠ 0) (hℓ : ℓ ≠ 0) :
    ∀ e, e ∈ˢ elemSet u (frP Fss.length Ids.length K) Ids (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) → ∀ g,
      g ∈ˢ piSet (elemPred tbl u (frP Fss.length Ids.length K) Ids rss tlss Eiss Fss
          (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) e)
        (fun e' => SetTheory.app (elemGraph tbl ℓ u (frP Fss.length Ids.length K) (frM Fss.length Ids.length K) Ids
          rss tlss Eiss Fss (frMsL Fss.length Ids.length K) (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss)) e') →
      elemSt tbl ℓ u (frP Fss.length Ids.length K) rss tlss Eiss Fss (frMsL Fss.length Ids.length K) e g
        ∈ˢ elemB u Ids.length (frM Fss.length Ids.length K) e := by
  intro e he g hg
  obtain ⟨t, ht, x, hx, rfl⟩ := mem_elemSet.mp he
  obtain ⟨is, hsp, rfl⟩ := mem_idxSet_elim ht
  obtain ⟨jc, j, fs, hJ, rfl, hj, hlen, hspR, hidx, hslots⟩ := famK_elim h hw hsp hx
  have hfam : ∀ t', SetTheory.app (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) t' ∈ˢ (univ w : V) :=
    fun t' => famApp_mem_univ (fixFamI_mem tbl u w (frP Fss.length Ids.length K) Ids rss tlss Eiss Fss₀ Ess) t'
  have hloc : locOf tbl j = jc := locOf_tagOf h.hX.hoff.tbl hJ hj
  unfold elemSt elemB
  rw [elemFlat_mk, ← hJ, elemFields_mk _ hJ hlen, sfst_kpair, ssnd_kpair, isOfW_tupW h.hX.hI hsp, List.foldl_append,
    frMsL_getD Fss.length Ids.length K hj]
  have hfold := minorSpI_fold (fun h0 => absurd h0 hℓ) (h.hyp.hms j hj) hspR
  rw [List.nil_append] at hfold
  have hC0 : ℓ = 0 → concI tbl w (frP Fss.length Ids.length K) (frM Fss.length Ids.length K) (Ess.getD j []) j fs
      ∈ˢ (univZero : V) := fun h0 => absurd h0 hℓ
  have := ihSpL_fold hC0 (As := ihDomsI ℓ (frP Fss.length Ids.length K) (frM Fss.length Ids.length K) rss tlss Eiss
      (fun j => (Fss.getD j []).length) j fs)
    (vs := elemIhs ℓ u (frP Fss.length Ids.length K) (rss.getD j []) (tlss.getD j []) (Eiss.getD j [])
      (Fss.getD j []).length fs g) hfold (by simp [ihDomsI, elemIhs]) ?_
  · unfold concI ctorValI at this
    rw [hidx, if_neg hw, hloc] at this
    exact this
  · intro l hl
    unfold ihDomsI at hl
    rw [List.length_map] at hl
    have hi : (recIdx (rss.getD j []) (Fss.getD j []).length)[l]
        ∈ recIdx (rss.getD j []) (Fss.getD j []).length := List.getElem_mem hl
    unfold ihDomsI elemIhs
    rw [List.getD_eq_getElem?_getD (i := l), List.getElem?_map, List.getElem?_eq_getElem hl,
      Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD (i := l), List.getElem?_map,
      List.getElem?_eq_getElem hl, Option.map_some, Option.getD_some]
    generalize (recIdx (rss.getD j []) (Fss.getD j []).length)[l] = i at hi
    obtain ⟨hslot, hmem⟩ := hslots i hi
    refine lamTower_mem_piTele fun bs hbs => ?_
    simp only [List.nil_append]
    have hlenbs : bs.length = ((tlss.getD j []).getD i []).length := by
      rw [hbs.length_eq, List.length_map]
    rw [← hlenbs, frameIdx_consList']
    -- the call's element is a predecessor; the choice's value there is in the graph's fibre
    obtain ⟨-, hvsp⟩ := hslot.2.2 bs hbs
    rw [consList_append] at hvsp
    have hfmem := slotSet_fold_mem hfam hmem hbs
    have hpre : kpair (tupW u (((Eiss.getD j []).getD i []).map
        (interp V (consList bs (consList (fs.take i) (frP Fss.length Ids.length K))))))
        (bs.foldl SetTheory.app (fs.getD i pt))
        ∈ˢ elemPred tbl u (frP Fss.length Ids.length K) Ids rss tlss Eiss Fss
          (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) (kpair (tupW u is) (inj jc (mkTower (fs ++ [pt])))) :=
      (mem_elemPred_mk hJ hlen).mpr ⟨mk_mem_elemSet (tupW_mem hvsp) hfmem, i, hi, bs, hbs, rfl⟩
    have hgv := elemGraph_sub_B h (mk_mem_elemSet (tupW_mem hvsp) hfmem) (app_mem_of_mem_piSet hg hpre)
    unfold elemB at hgv
    rw [sfst_kpair, ssnd_kpair, isOfW_tupW h.hX.hI hvsp] at hgv
    exact hgv

/-- **The recursion equation at a K-frame**: at every member of the
family's fibre at a tuple the graph's selector lies in the motive and
is the step at the selector's graph over the predecessors. -/
theorem elemK_facts (h : FixKI₀ tbl ℓ w u K Fss Ess Fss₀ Ids rss tlss Eiss) (hw : w ≠ 0) (hℓ : ℓ ≠ 0)
    {is : List V} (hsp : SpineFit (frP Fss.length Ids.length K) Ids is) {x : V}
    (hx : x ∈ˢ SetTheory.app (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) (tupW u is)) :
    recSel (elemGraph tbl ℓ u (frP Fss.length Ids.length K) (frM Fss.length Ids.length K) Ids rss tlss Eiss Fss
        (frMsL Fss.length Ids.length K) (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss)) (kpair (tupW u is) x)
      ∈ˢ SetTheory.app (is.foldl SetTheory.app (frM Fss.length Ids.length K)) x ∧
    recSel (elemGraph tbl ℓ u (frP Fss.length Ids.length K) (frM Fss.length Ids.length K) Ids rss tlss Eiss Fss
        (frMsL Fss.length Ids.length K) (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss)) (kpair (tupW u is) x)
      = elemSt tbl ℓ u (frP Fss.length Ids.length K) rss tlss Eiss Fss (frMsL Fss.length Ids.length K)
          (kpair (tupW u is) x)
          (graph (fun e' => recSel (elemGraph tbl ℓ u (frP Fss.length Ids.length K) (frM Fss.length Ids.length K) Ids
              rss tlss Eiss Fss (frMsL Fss.length Ids.length K) (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss)) e')
            (elemPred tbl u (frP Fss.length Ids.length K) Ids rss tlss Eiss Fss
              (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) (kpair (tupW u is) x))) := by
  have hsing := elemGraph_singleton (M := frM Fss.length Ids.length K) (msL := frMsL Fss.length Ids.length K)
    (Fss := Fss) h.hX h.hreal hw (elemB_mem h) (elemSt_mem h hw hℓ)
  have he : kpair (tupW u is) x ∈ˢ elemSet u (frP Fss.length Ids.length K) Ids
      (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) := mk_mem_elemSet (tupW_mem hsp) hx
  have hsel := recSel_mem (hsing _ (tupW_mem hsp) x hx).1
  refine ⟨?_, ?_⟩
  · have := elemGraph_sub_B h he hsel
    unfold elemB at this
    rwa [sfst_kpair, ssnd_kpair, isOfW_tupW h.hX.hI hsp] at this
  · unfold elemGraph
    refine recSel_eq (elemB_mem h) (fun e _ => elemPred_subset tbl u _ Ids rss tlss Eiss Fss _ e) he
      (hsing _ (tupW_mem hsp) x hx).1 fun e' he' => ?_
    obtain ⟨t', ht', x', hx', rfl⟩ := mem_elemSet.mp (elemPred_subset tbl u _ Ids rss tlss Eiss Fss _ _ e' he')
    exact hsing t' ht' x' hx'

/-- **Inhabitation at a zero elimination level by lfp induction**
(graph regime): the motive is inhabited at every member of the
family's fibre — the property is closed under the functor: at a
constructor value over the X-chain at the family of members satisfying
it, the minor's ih tower is inhabited (every ih domain is, pointwise
under the field's telescope: the slot's fold lies in that family at
the call's tuple), so its conclusion is. -/
theorem famK_inhab_zero_pos (h : FixKI₀ tbl ℓ w u K Fss Ess Fss₀ Ids rss tlss Eiss) (hw : w ≠ 0) (h0 : ℓ = 0) :
    ∀ (is : List V) (t : V), SpineFit (frP Fss.length Ids.length K) Ids is →
      t ∈ˢ SetTheory.app (famK tbl u w K Fss Ess Fss₀ Ids rss tlss Eiss) (tupW u is) →
      ∃ y, y ∈ˢ SetTheory.app (is.foldl SetTheory.app (frM Fss.length Ids.length K)) t := by
  have hX := h.hX
  have hIds : IdxOk u (frP Fss.length Ids.length K) Ids := hX.hI
  obtain ⟨hl₀, hlE, hEs, hlenj, hc⟩ := h.hreal
  let P : V → V → Prop := fun i x => ∀ is, SpineFit (frP Fss.length Ids.length K) Ids is → i = tupW u is →
    ∃ y, y ∈ˢ SetTheory.app (is.foldl SetTheory.app (frM Fss.length Ids.length K)) x
  have hind := lfpFamSet_induction (w := w) (I := idxSet u (frP Fss.length Ids.length K) Ids)
    (F := fixFunVI tbl u w (frP Fss.length Ids.length K) Ids Ids.length rss tlss Eiss Fss₀ Ess)
    (fixFunVI_closed_exists hX) (fixFunVI_mono hX) P ?_
  · intro is t hsp ht
    exact hind (tupW u is) (tupW_mem hsp) t ht is hsp rfl
  intro i hi x hx is hsp hi'
  subst hi'
  -- the induction family
  let S := graph (fun i => sep (SetTheory.app (lfpFamSet w (idxSet u (frP Fss.length Ids.length K) Ids)
    (fixFunVI tbl u w (frP Fss.length Ids.length K) Ids Ids.length rss tlss Eiss Fss₀ Ess)) i) (P i))
    (idxSet u (frP Fss.length Ids.length K) Ids)
  have hSmem : S ∈ˢ lfpFamSpace V w (idxSet u (frP Fss.length Ids.length K) Ids) := by
    rw [lfpFamSpace_eq]
    exact graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpFamSet_mem _ _ _) hi)
  have hSle : FamLe (idxSet u (frP Fss.length Ids.length K) Ids) S
      (fixFamI tbl u w (frP Fss.length Ids.length K) Ids Ids.length rss tlss Eiss Fss₀ Ess) := by
    intro i hi y hy
    rw [app_graph hi] at hy
    exact (mem_sep.mp hy).1
  have hfamS : ∀ t', SetTheory.app S t' ∈ˢ (univ w : V) := fun t' => famApp_mem_univ hSmem t'
  rw [fixFunVI_app hSmem, famFI_app (tupW_mem hsp)] at hx
  obtain ⟨jc, j, fs, hJ, rfl, hj₀, hlen₀, hspX, hall⟩ := fixStepI_elim hw hx
  rw [hl₀] at hJ
  have hj : j < Fss.length := by omega
  have hloc : locOf tbl j = jc := locOf_tagOf hX.hoff.tbl hJ hj
  have hfit := hX.hfit S hSmem _ (tupW_mem hsp) j hj₀
  have hspR := spineFit_real_of_XI hIds hSle (Fss₀.getD j []) (Fss.getD j []) 0 [] fs rfl (hc j hj) hfit hspX
  have hlen : fs.length = (Fss.getD j []).length := by rw [hlen₀]; exact hlenj j hj
  have hidx : idxValsAt (frP Fss.length Ids.length K) (Ess.getD j []) fs = is := by
    rw [← hlen₀] at hall
    exact idxValsAt_of_eqsXI hIds hsp (hEs j hj) hall
  -- the minor's conclusion is inhabited once every ih domain is
  have hms := h.hyp.hms j hj
  rw [h0] at hms
  obtain ⟨x, hx⟩ := minorSpI_zero_inhab hms hspR
  rw [List.nil_append] at hx
  have := ihSpL_zero_inhab hx ?_
  · unfold concI ctorValI at this
    rwa [hidx, if_neg hw, hloc] at this
  · intro A hA
    unfold ihDomsI at hA
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    -- the field lies in the slot at the induction family
    have hslot := fitsXI_slot_mem hIds (Fss₀.getD j []) 0 [] fs rfl hfit hspX i (by rw [hlen]; exact hik)
      (by rw [Nat.zero_add]; exact hri)
    rw [Nat.zero_add, List.nil_append] at hslot
    obtain ⟨hf, hmem⟩ := hslot
    refine piTele_zero_inhab_of fun as has => ?_
    have has' : SpineFit (consList (fs.take i) (frP Fss.length Ids.length K))
        (((tlss.getD j []).getD i []).map (·.2.2)) as := fitsS_teleOfFields.mp has
    obtain ⟨-, hvsp⟩ := hf.2.2 as has'
    rw [consList_append] at hvsp
    have hz := slotSet_fold_mem hfamS hmem has'
    rw [app_graph (tupW_mem hvsp)] at hz
    obtain ⟨-, hPz⟩ := mem_sep.mp hz
    obtain ⟨y, hy⟩ := hPz _ hvsp rfl
    exact ⟨y, by simpa using hy⟩

end KFrame

end ConLeche.Semantics
