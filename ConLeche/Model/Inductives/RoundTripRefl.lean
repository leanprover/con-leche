module

public import ConLeche.Model.Inductives.RoundTripTransportR1
public section

/-!
# The REFLEXIVE arm, datum level: a telescoped recursive slot, the fields' fit (task #279 M-C′, DESIGN §M.39)

`RoundTripR2.lean`'s `slot_finitary`/`fieldsFit_of_chainFit` take the
container's recursive fields FINITARY (`hfin`): a recursive slot is the
target's carrier at the readings, and the induction hypothesis is at
the field's value.  A REFLEXIVE field (`List (Nat → T)` at `T`; kind
`.reflexive`, a non-empty telescope `tss`) has the slot as the nested
product over its telescope (`slotSet` = `piTele`) and the induction
hypothesis pointwise under it.  This module generalises the two:

* **`slot_general`** — at ANY recursive position, a value in the slot
  at the restricted family lies in the Π-tower over the telescope of
  the target's carrier at the readings (the field's entry: `recEntry`
  at a finitary position, `reflEntry` at a reflexive one — the tower's
  bits are the family's, `tssBits`; `interp_mkPisAV_piTele`,
  `piTele_mono` through `slotRecover` and `leaf`), and satisfies the
  predicate at every fitting telescope spine (`piTele_fold`, `mem_restrictedFam`);
* **`fieldsFit_of_chainFit'`** — `fieldsFit_of_chainFit` without
  `hfin`: the entries' readings are graded and fitting UNDER the
  telescope (`hEntry`), the induction hypotheses pointwise under it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A telescoped recursive slot -/

set_option maxHeartbeats 1600000 in
/-- **A recursive slot at the restricted family, telescopes included**:
at a recursive position `i` of constructor `J` targeting `tgt`, with
the field's readings graded and fitting the target's telescope under
every fitting telescope spine, a value in the slot lies in the Π-tower
over the field's telescope of the target's leaf at the parameter
variables and the readings (the entry's shape at both kinds), and
satisfies the predicate at the target's tuple under every fitting
telescope spine.  The family's sort is nonzero (`hw`: `piTele_fold`). -/
theorem slot_general {m : EnvModel V env} {dJ : IndRepData V} {ψ' : Name → Nat}
    {σ₀ : Nat → V} {P : V → V → Prop}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {tgt : Nat} {s : Level}
    (hs : ∀ φ : Name → Nat, s.eval φ = dJ.resSort.eval φ)
    (hrep : IndRep m (dJ.memberName tgt) cvT cvR mI rP rules (dJ.withSort s) tgt) (hw : dJ.w ψ' ≠ 0)
    {DsAv : List V} (hsat : Sat V (dJ.params ψ').reverse (consList DsAv σ₀))
    (hDsFit : SpineFit σ₀ (dJ.params ψ') DsAv) (hDsLen : DsAv.length = dJ.nP)
    {J i : Nat} {cA : ConstantVal × Nat} (hJ : dJ.ctorsA[J]? = some cA)
    (htgt : dJ.tgts J i = tgt) (hrec : (dJ.rss.getD J []).getD i false = true)
    (hbits : ∀ dd ∈ (dJ.tssF J ψ').getD i [], (dd.2.1 = 0 ↔ dJ.w ψ' = 0))
    {ws : List V} (hws : ws.length = i)
    (hEfit : ∀ bs : List V,
      SpineFit (consList ws (consList DsAv σ₀)) (((dJ.tssF J ψ').getD i []).map (·.2.2)) bs →
      (∀ E ∈ (dJ.eissF J ψ').getD i [], WellDenoted V (consList bs (consList ws (consList DsAv σ₀))) E) ∧
      SpineFit (consList DsAv σ₀) (dJ.IdsM tgt ψ')
        (((dJ.eissF J ψ').getD i []).map (interp V (consList bs (consList ws (consList DsAv σ₀))))))
    {f : V}
    (hf : f ∈ˢ slotSet (dJ.w ψ') (dJ.u ψ') (consList ws (consList DsAv σ₀)) (((dJ.tlss ψ').getD J []).getD i [])
      (((dJ.Eiss ψ').getD J []).getD i []) (predFam dJ ψ' (consList DsAv σ₀) P)) :
    f ∈ˢ interp V (consList ws (consList DsAv σ₀))
        (mkPisAV ((dJ.tssF J ψ').getD i [])
          (AnnotTerm.mkAppN (m.acval (dJ.memberName tgt) ψ')
            (paramBvarsAt dJ.nP (dJ.nP + i + ((dJ.tssF J ψ').getD i []).length) ++ (dJ.eissF J ψ').getD i []))) ∧
    ∀ bs : List V, SpineFit (consList ws (consList DsAv σ₀)) (((dJ.tssF J ψ').getD i []).map (·.2.2)) bs →
      P (dJ.tup ψ' tgt (((dJ.eissF J ψ').getD i []).map (interp V (consList bs (consList ws (consList DsAv σ₀))))))
        (bs.foldl SetTheory.app f) := by
  have hJlt : J < dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  rw [dJ.tlss_getD ψ' hJ] at hf
  unfold slotSet at hf
  -- the slot's tuple at a fitting telescope spine is the target's tuple
  have hslot : ∀ bs, SpineFit (consList ws (consList DsAv σ₀)) (((dJ.tssF J ψ').getD i []).map (·.2.2)) bs →
      tupW (dJ.u ψ')
          ((((dJ.Eiss ψ').getD J []).getD i []).map (interp V (consList bs (consList ws (consList DsAv σ₀)))))
        = dJ.tup ψ' tgt
            (((dJ.eissF J ψ').getD i []).map (interp V (consList bs (consList ws (consList DsAv σ₀))))) := by
    intro bs hbs
    have hbsLen : bs.length = ((dJ.tssF J ψ').getD i []).length := by rw [hbs.length_eq, List.length_map]
    have hshift : shiftE (i + ((dJ.tssF J ψ').getD i []).length) 0 (consList bs (consList ws (consList DsAv σ₀)))
        = consList DsAv σ₀ := by
      rw [← consList_append, show i + ((dJ.tssF J ψ').getD i []).length = (ws ++ bs).length by
        rw [List.length_append, hbsLen, hws]]
      exact shiftE_consList _ _
    have h : tupW (dJ.u ψ')
          ((((dJ.Eiss ψ').getD J []).getD i []).map (interp V (consList bs (consList ws (consList DsAv σ₀)))))
        = dJ.tup ψ' (dJ.tgts J i)
            (((dJ.eissF J ψ').getD i []).map (interp V (consList bs (consList ws (consList DsAv σ₀))))) :=
      hrep.slotRecover ψ' _ hsat J i hJlt hrec _ hshift (hEfit bs hbs).1
        (show SpineFit (consList DsAv σ₀) (dJ.IdsM (dJ.tgts J i) ψ') _ by rw [htgt]; exact (hEfit bs hbs).2)
    rw [htgt] at h
    exact h
  -- the tuples are in the index set
  have htup : ∀ bs, SpineFit (consList ws (consList DsAv σ₀)) (((dJ.tssF J ψ').getD i []).map (·.2.2)) bs →
      dJ.tup ψ' tgt (((dJ.eissF J ψ').getD i []).map (interp V (consList bs (consList ws (consList DsAv σ₀)))))
        ∈ˢ dJ.idx ψ' (consList DsAv σ₀) :=
    fun bs hbs => hrep.tupMem ψ' _ hsat _ (hEfit bs hbs).2
  refine ⟨?_, fun bs hbs => ?_⟩
  · -- the Π-tower's reading is the nested product of the target's carrier
    rw [ConLeche.Semantics.interp_mkPisAV_piTele (v := dJ.w ψ') (acc := [])
      (B := fun bs => (DsAv ++ ((dJ.eissF J ψ').getD i []).map
          (interp V (consList bs (consList ws (consList DsAv σ₀))))).foldl
        SetTheory.app (interp V σ₀ (m.acval (dJ.memberName tgt) ψ'))) hbits ?_]
    · refine piTele_mono (fun bs hbs => ?_) f hf
      simp only [List.nil_append]
      have hbs' := fitsS_teleOfFields.mp hbs
      intro z hz
      rw [hslot bs hbs'] at hz
      unfold predFam at hz
      rw [mem_restrictedFam (htup bs hbs')] at hz
      have hleaf := hrep.leaf ψ' σ₀ DsAv _ hDsFit (hEfit bs hbs').2
      rw [dJ.withSort_w, hs ψ'] at hleaf
      rw [hleaf]
      exact hz.1
    · intro bs hbs
      have hbsLen : bs.length = ((dJ.tssF J ψ').getD i []).length := by rw [hbs.length_eq, List.length_map]
      simp only [List.nil_append]
      rw [interp_mkAppN_map, List.map_append, Nat.add_assoc dJ.nP i,
        map_paramBvarsAt_interp (e := i + ((dJ.tssF J ψ').getD i []).length) (ρp := consList DsAv σ₀)
          (σ := consList bs (consList ws (consList DsAv σ₀)))
          (fun j => by
            rw [← consList_append, show i + ((dJ.tssF J ψ').getD i []).length = (ws ++ bs).length by
              rw [List.length_append, hbsLen, hws]]
            exact consList_apply_add _ _ j),
        range_reverse_map_consList' hDsLen, interp_closed (V := V) (m.cval_closedL _ ψ') _ σ₀]
  · -- the induction hypothesis at the leaf
    have hbs' : FitsS (teleOfFields (consList ws (consList DsAv σ₀)) (((dJ.tssF J ψ').getD i []).map (·.2.2))) bs :=
      fitsS_teleOfFields.mpr hbs
    have h := piTele_fold hw hf hbs'
    simp only [List.nil_append] at h
    rw [hslot bs hbs] at h
    unfold predFam at h
    rw [mem_restrictedFam (htup bs hbs)] at h
    exact h.2

/-! ## The fields fit the real domains, telescopes included -/

set_option maxHeartbeats 1600000 in
/-- **A chain-fitting spine fits the REAL domains, telescopes included**
(`fieldsFit_of_chainFit` without `hfin`): an ordinary position's value
is in its domain, a recursive one's in the Π-tower over its telescope
of the target's carrier at its readings — the field's entry
(`recEntry`/`reflEntry`, `slot_general`) — with the induction
hypothesis at every fitting telescope spine.  The entries' readings
are graded and fit the target's telescope under any fitting prefix and
telescope spine (`hEntry`); the family's sort is nonzero (`hw`), the
constructor facts' spelling of it evaluates alike (`hsJ`). -/
theorem fieldsFit_of_chainFit' {m : EnvModel V env} {dJ : IndRepData V} {ψ' : Name → Nat}
    {σ₀ : Nat → V} {P : V → V → Prop}
    (hrepT : dJ.RepsAt m) (hw : dJ.w ψ' ≠ 0)
    {DsAv : List V} (hsat : Sat V (dJ.params ψ').reverse (consList DsAv σ₀))
    (hDsFit : SpineFit σ₀ (dJ.params ψ') DsAv) (hDsLen : DsAv.length = dJ.nP)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : dJ.ctorsA[J]? = some cA) {lpsT : List Name}
    {sJ : Level} (hsJ : sJ.eval ψ' = dJ.resSort.eval ψ')
    (hC : FixCtorFactsAt m dJ.env₀ (dJ.memberName (dJ.mems J)) lpsT dJ.nP (dJ.nIdxAt (dJ.mems J))
      sJ dJ.isProp dJ.large dJ.idxF dJ.dsF dJ.esF dJ.srcsF dJ.ksF dJ.fvsPF dJ.xFvsF dJ.xrestF
      dJ.eissF dJ.tssF J cA (fun i => dJ.memberName (dJ.tgts J i)) (fun i => dJ.nIdxAt (dJ.tgts J i)))
    (htgts : ∀ i, dJ.tgts J i < dJ.k)
    (hEntry : ∀ i, i ∈ ConLeche.recIdxOf (dJ.ksF J) → ∀ ws : List V, ws.length = i →
      SpineFit (consList DsAv σ₀) ((((dJ.dsF J ψ').drop dJ.nP).map (·.2.2)).take i) ws →
      ∀ bs : List V, SpineFit (consList ws (consList DsAv σ₀)) (((dJ.tssF J ψ').getD i []).map (·.2.2)) bs →
        (∀ E ∈ (dJ.eissF J ψ').getD i [], WellDenoted V (consList bs (consList ws (consList DsAv σ₀))) E) ∧
        SpineFit (consList DsAv σ₀) (dJ.IdsM (dJ.tgts J i) ψ')
          (((dJ.eissF J ψ').getD i []).map (interp V (consList bs (consList ws (consList DsAv σ₀))))))
    {fs : List V} (hlen : fs.length = ((dJ.Fss ψ').getD J []).length)
    (hfields : ∀ (i : Nat) (F : AnnotTerm), ((dJ.Fss ψ').getD J [])[i]? = some F → ∀ f, fs[i]? = some f →
      ((dJ.rss.getD J []).getD i false = true →
        f ∈ˢ slotSet (dJ.w ψ') (dJ.u ψ') (consList (fs.take i) (consList DsAv σ₀))
          (((dJ.tlss ψ').getD J []).getD i []) (((dJ.Eiss ψ').getD J []).getD i [])
          (predFam dJ ψ' (consList DsAv σ₀) P)) ∧
      ((dJ.rss.getD J []).getD i false = false →
        f ∈ˢ interp V (consList (fs.take i) (consList DsAv σ₀)) F)) :
    SpineFit (consList DsAv σ₀) ((dJ.Fss ψ').getD J []) fs ∧
    ∀ i, i ∈ ConLeche.recIdxOf (dJ.ksF J) →
      ∀ bs : List V,
        SpineFit (consList (fs.take i) (consList DsAv σ₀)) (((dJ.tssF J ψ').getD i []).map (·.2.2)) bs →
        P (dJ.tup ψ' (dJ.tgts J i)
            (((dJ.eissF J ψ').getD i []).map (interp V (consList bs (consList (fs.take i) (consList DsAv σ₀))))))
          (bs.foldl SetTheory.app (fs.getD i pt)) := by
  have hJlt : J < dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  obtain ⟨-, -, hD⟩ := hC
  have hFs := dJ.Fss_getD ψ' hJ
  have hksLen : (dJ.ksF J).length = cA.2 := hD.ksLen
  have hnF : ((dJ.Fss ψ').getD J []).length = cA.2 := by
    rw [hFs, List.length_map, List.length_drop, hD.len ψ']
    omega
  -- the entry's shape and bits at a recursive position
  have hentry : ∀ n, n ∈ ConLeche.recIdxOf (dJ.ksF J) →
      ((dJ.dsF J ψ').getD (dJ.nP + n) default).2.2
        = mkPisAV ((dJ.tssF J ψ').getD n [])
            (AnnotTerm.mkAppN (m.acval (dJ.memberName (dJ.tgts J n)) ψ')
              (paramBvarsAt dJ.nP (dJ.nP + n + ((dJ.tssF J ψ').getD n []).length) ++ (dJ.eissF J ψ').getD n [])) := by
    intro n hn
    obtain ⟨hnk, hkind⟩ := mem_recIdxOf.mp hn
    have hnlt : n < cA.2 := by rw [← hksLen]; exact hnk
    rcases hkind with hk | hk
    · have htl : (dJ.tssF J ψ').getD n [] = [] := hD.tssNone ψ' n (by rw [hk]; decide)
      rw [hD.recEntry ψ' n hk hnlt, htl, List.length_nil, Nat.add_zero]
      rfl
    · exact hD.reflEntry ψ' n hk hnlt
  have hbits : ∀ n, ∀ dd ∈ (dJ.tssF J ψ').getD n [], (dd.2.1 = 0 ↔ dJ.w ψ' = 0) := by
    intro n dd hdd
    have := hD.tssBits ψ' n dd hdd
    rw [hsJ] at this
    exact this
  -- one position, given the prefix fits
  have hpos : ∀ (n : Nat) (F : AnnotTerm) (f : V), ((dJ.Fss ψ').getD J [])[n]? = some F →
      fs[n]? = some f → SpineFit (consList DsAv σ₀) (((dJ.Fss ψ').getD J []).take n) (fs.take n) →
      f ∈ˢ interp V (consList (fs.take n) (consList DsAv σ₀)) F ∧
      (n ∈ ConLeche.recIdxOf (dJ.ksF J) →
        ∀ bs : List V,
          SpineFit (consList (fs.take n) (consList DsAv σ₀)) (((dJ.tssF J ψ').getD n []).map (·.2.2)) bs →
          P (dJ.tup ψ' (dJ.tgts J n)
              (((dJ.eissF J ψ').getD n []).map
                (interp V (consList bs (consList (fs.take n) (consList DsAv σ₀))))))
            (bs.foldl SetTheory.app f)) := by
    intro n F f hF hf hpre
    have hnlt : n < cA.2 := by
      have := (List.getElem?_eq_some_iff.mp hF).1
      rwa [hnF] at this
    have hnfs : n < fs.length := (List.getElem?_eq_some_iff.mp hf).1
    have hFeq : F = ((dJ.dsF J ψ').getD (dJ.nP + n) default).2.2 := by
      have h := hF
      rw [hFs, List.getElem?_map, List.getElem?_drop] at h
      obtain ⟨dd, hdd, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [List.getD_eq_getElem?_getD, hdd]
      rfl
    have htake : (fs.take n).length = n := by rw [List.length_take]; omega
    by_cases hr : n ∈ ConLeche.recIdxOf (dJ.ksF J)
    · -- a recursive position, telescope or not
      have hrec : (dJ.rss.getD J []).getD n false = true :=
        (dJ.rss_getD_iff hJlt (by rw [hksLen]; exact hnlt)).mpr hr
      have hslot := (hfields n F hF f hf).1 hrec
      rw [hFs] at hpre
      obtain ⟨s', cvT', cvR', mI', rP', rules', hs', hrep'⟩ := hrepT _ (htgts n)
      have h := slot_general hs' hrep' hw hsat hDsFit hDsLen hJ rfl hrec (hbits n) htake
        (hEntry n hr (fs.take n) htake hpre) hslot
      refine ⟨?_, fun _ => h.2⟩
      rw [hFeq, hentry n hr]
      exact h.1
    · -- an ordinary position
      have hord : (dJ.rss.getD J []).getD n false = false := by
        have := (dJ.rss_getD_iff hJlt (by rw [hksLen]; exact hnlt))
        cases hb : (dJ.rss.getD J []).getD n false
        · rfl
        · exact absurd (this.mp hb) hr
      exact ⟨(hfields n F hF f hf).2 hord, fun h => absurd h hr⟩
  have hfit : SpineFit (consList DsAv σ₀) ((dJ.Fss ψ').getD J []) fs :=
    spineFit_of_prefix_pointwise hlen fun n F f hF hf hpre => (hpos n F f hF hf hpre).1
  refine ⟨hfit, fun i hi => ?_⟩
  have hilt : i < cA.2 := by rw [← hksLen]; exact (mem_recIdxOf.mp hi).1
  have hifs : i < fs.length := by rw [hlen, hnF]; exact hilt
  have hiF : i < ((dJ.Fss ψ').getD J []).length := by rw [hnF]; exact hilt
  have hpre : SpineFit (consList DsAv σ₀) (((dJ.Fss ψ').getD J []).take i) (fs.take i) :=
    spineFit_take' hfit (Nat.le_of_lt hiF)
  exact (hpos i _ (fs.getD i pt) (List.getElem?_eq_getElem hiF)
    (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hifs]; rfl) hpre).2 hi

end ConLeche.Model
