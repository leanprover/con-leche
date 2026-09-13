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

/-! ## The steps with the positions abstracted -/

set_option maxHeartbeats 1600000 in
/-- **THE STEP, positions abstracted** (task #279 M-C′, the reflexive
arm): `r2_step` with the container-recursive arm of `hpos` folded into
the third — every position is either ordinary on both sides or has
its round trip given (`MIXED.getD i pt = fs.getD i pt`); no induction
hypothesis is consumed here (the run level derives the equality at a
telescoped recursive position from the pointwise one,
`fieldsFit_of_chainFit'`). -/
theorem r2_step' (m : EnvModel V env) {dJ d : IndRepData V} {ψ' ψ : Name → Nat} {ρ σ₀ σ : Nat → V}
    {Ψ Φ Φ' : Nat → AnnotTerm} {k₀ base : Nat}
    -- the container's representations, at every member
    (hrepT : ∀ t, t < dJ.k → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IndRep m (dJ.memberName t) cvT cvR mI rP rules dJ t)
    (hsat : Sat V (dJ.params ψ').reverse σ)
    {DsAv : List V} (hσ : σ = consList DsAv σ₀) (hDsFit : SpineFit σ₀ (dJ.params ψ') DsAv)
    (hDsLen : DsAv.length = dJ.nP)
    -- the constructor and its copy
    {J J' : Nat} {cA cA' : ConstantVal × Nat} (hJ : dJ.ctorsA[J]? = some cA)
    (hlenD : (dJ.dsF J ψ').length = dJ.nP + cA.2)
    (hpIff : ∀ ρ' : Nat → V, Sat V (dJ.params ψ').reverse ρ' ↔
      Sat V (((dJ.dsF J ψ').take dJ.nP).map (·.2.2)).reverse ρ')
    (hmemJ : dJ.mems J < dJ.k)
    (hmemA : d.mems J' = k₀ + base + dJ.mems J)
    (hΦ : ∀ t, t < dJ.k → Φ t = Φ' (k₀ + base + t))
    -- the spine: it fits the real domains, the induction hypotheses at
    -- the recursive positions, the readings' facts, the terminator
    {fs : List V} (hfit : SpineFit σ ((dJ.Fss ψ').getD J []) fs)
    (hEsOk : ∀ E ∈ dJ.esF J ψ', WellDenoted V (consList fs σ) E)
    (hEsFit : SpineFit σ (dJ.IdsM (dJ.mems J) ψ') ((dJ.esF J ψ').map (interp V (consList fs σ))))
    {X tup : V}
    (hall : EqAll (consList fs (cons tup (cons X σ)))
      (eqsXI (dJ.IdsC ψ').length ((dJ.Fss ψ').getD J []).length ((dJ.Ess ψ').getD J [])))
    -- ψ's ι at values (`PsiSetup.fold_iota_vals`), the fold terms abstracted
    {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {via : Nat → Nat → Option ViaSpec}
    (hιΨ : ∀ vs : List V, SpineFit σ₀ ((dJ.dsF J ψ').map (·.2.2)) (DsAv ++ vs) →
      ((dJ.esF J ψ').map (interp V (consList vs σ)) ++
          [(DsAv ++ vs).foldl SetTheory.app (interp V σ₀ (m.acval cA.1.name ψ'))]).foldl
          SetTheory.app (interp V σ₀ (Ψ (dJ.mems J)))
        = (psiVals (dJ.bb ψ') σ (ConLeche.recIdxOf (dJ.ksR J)) (useIh J) (via J) vs
            ((ConLeche.recIdxOf (dJ.ksR J)).map fun i =>
              lamTower (dJ.bb ψ') (consList (vs.take i) σ) ((dJ.tssR J ψ').getD i []) fun σ'' =>
                (((dJ.eissR J ψ').getD i []).map (interp V σ'') ++
                  [(Semantics.frameIdx (((dJ.tssR J ψ').getD i []).length) σ'').foldl SetTheory.app
                    (vs.getD i pt)]).foldl SetTheory.app (interp V σ₀ (Ψ (dJ.tgtsR J i))))).foldl
            SetTheory.app (interp V σ (head J)))
    -- ψ⁻¹'s ι at values (`InvSetup.fold_iota_vals`), the fold terms abstracted
    {head' : Nat → AnnotTerm} {useIhA : Nat → Nat → Bool}
    (hιΦ : ∀ vs' : List V, SpineFit ρ ((d.dsF J' ψ).map (·.2.2)) (paramVals d.nP ρ ++ vs') →
      ((d.esF J' ψ).map (interp V (consList (paramVals d.nP ρ ++ vs') ρ)) ++
          [(paramVals d.nP ρ ++ vs').foldl SetTheory.app (interp V ρ (m.acval cA'.1.name ψ))]).foldl
          SetTheory.app (interp V ρ (Φ' (d.mems J')))
        = (mixedVals (ConLeche.recIdxOf (d.ksR J')) (useIhA J') vs'
            ((ConLeche.recIdxOf (d.ksR J')).map fun i =>
              lamTower (d.bb ψ) (consList (vs'.take i) ρ) ((d.tssR J' ψ).getD i []) fun σ'' =>
                (((d.eissR J' ψ).getD i []).map (interp V σ'') ++
                  [(Semantics.frameIdx (((d.tssR J' ψ).getD i []).length) σ'').foldl SetTheory.app
                    (vs'.getD i pt)]).foldl SetTheory.app (interp V ρ (Φ' (d.tgtsR J' i))))).foldl
            SetTheory.app (interp V ρ (head' J')))
    -- ψ's values and ψ⁻¹'s mixed values, named
    {VSψ MIXED : List V}
    (hVS : VSψ = psiVals (dJ.bb ψ') σ (ConLeche.recIdxOf (dJ.ksR J)) (useIh J) (via J) fs
      ((ConLeche.recIdxOf (dJ.ksR J)).map fun i =>
        lamTower (dJ.bb ψ') (consList (fs.take i) σ) ((dJ.tssR J ψ').getD i []) fun σ'' =>
          (((dJ.eissR J ψ').getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx (((dJ.tssR J ψ').getD i []).length) σ'').foldl SetTheory.app
              (fs.getD i pt)]).foldl SetTheory.app (interp V σ₀ (Ψ (dJ.tgtsR J i)))))
    (hMIX : MIXED = mixedVals (ConLeche.recIdxOf (d.ksR J')) (useIhA J') VSψ
      ((ConLeche.recIdxOf (d.ksR J')).map fun i =>
        lamTower (d.bb ψ) (consList (VSψ.take i) ρ) ((d.tssR J' ψ).getD i []) fun σ'' =>
          (((d.eissR J' ψ).getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx (((d.tssR J' ψ).getD i []).length) σ'').foldl SetTheory.app
              (VSψ.getD i pt)]).foldl SetTheory.app (interp V ρ (Φ' (d.tgtsR J' i)))))
    -- the copy constructor at ψ's values: its head (`psiHead`), ψ⁻¹'s head
    -- at the copy (the container constructor at the pin's readings),
    -- ψ's values fit its telescope (`psiVals_fit_copy`), its index
    -- readings there are the container's at the fields (the record's
    -- `es` off the replaced positions)
    (hheadψ : interp V σ (head J)
      = (paramVals d.nP ρ).foldl SetTheory.app (interp V ρ (m.acval cA'.1.name ψ)))
    (hheadφ : interp V ρ (head' J') = DsAv.foldl SetTheory.app (interp V σ₀ (m.acval cA.1.name ψ')))
    (hfitCopy : SpineFit ρ ((d.dsF J' ψ).map (·.2.2)) (paramVals d.nP ρ ++ VSψ))
    (hEs : (d.esF J' ψ).map (interp V (consList (paramVals d.nP ρ ++ VSψ) ρ))
      = (dJ.esF J ψ').map (interp V (consList fs σ)))
    -- per position: ordinary on both sides, or the round trip given
    (hpos : ∀ i, i < cA.2 →
      (¬ replaced (useIh J) (via J) i ∧ useIhA J' i = false) ∨
      MIXED.getD i pt = fs.getD i pt) :
    R2Pred dJ ψ' ρ σ₀ σ Ψ Φ tup (dJ.inj ψ' J fs) := by
  intro t' ht' is' his' htup
  have hJlt : J < dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  have hlenFs : fs.length = ((dJ.Fss ψ').getD J []).length := hfit.length_eq
  have hfsN : fs.length = cA.2 := by
    rw [hlenFs, dJ.Fss_getD ψ' hJ, List.length_map, List.length_drop, hlenD]
    omega
  -- the terminator: the constructor's member and its readings
  obtain ⟨cvT', cvR', mI', rP', rules', hrep'⟩ := hrepT t' ht'
  rw [htup] at hall
  obtain ⟨hmem, hisE⟩ := hrep'.idxRecover ψ' σ hsat is' his' X J fs hJlt hlenFs hEsOk hEsFit hall
  subst hisE
  subst hmem
  -- the injection is the constructor's value
  obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := hrepT _ hmemJ
  have hctor : dJ.inj ψ' J fs = (DsAv ++ fs).foldl SetTheory.app (interp V σ₀ (m.acval cA.1.name ψ')) :=
    (hrep.ctor J cA hJ ψ' σ₀ DsAv fs hDsFit (by rw [← hσ]; exact hfit)).symm
  -- the whole spine fits the constructor's telescope
  have hfitP : SpineFit σ₀ (((dJ.dsF J ψ').take dJ.nP).map (·.2.2)) DsAv :=
    spineFit_of_paramsIff hDsLen (by rw [List.length_map, List.length_take, hlenD]; omega) hDsFit hpIff
  have hfitAll : SpineFit σ₀ ((dJ.dsF J ψ').map (·.2.2)) (DsAv ++ fs) := by
    rw [← List.take_append_drop dJ.nP (dJ.dsF J ψ'), List.map_append]
    refine hfitP.append ?_
    rw [← hσ, ← dJ.Fss_getD ψ' hJ]
    exact hfit
  -- the mixed values are the fields
  have hVSlen : VSψ.length = fs.length := by rw [hVS, psiVals_length]
  have hMIXlen : MIXED.length = fs.length := by rw [hMIX, mixedVals_length, hVSlen]
  have hmixed : MIXED = fs := by
    refine list_ext_getD hMIXlen fun i hi => ?_
    have hiN : i < cA.2 := by rw [← hfsN, ← hMIXlen]; exact hi
    have hifs : i < fs.length := by rw [hfsN]; exact hiN
    have hiVS : i < VSψ.length := by rw [hVSlen]; exact hifs
    rcases hpos i hiN with ⟨hnr, huseA⟩ | hrest
    · -- ordinary on both sides
      have hnu : useIh J i = false := by
        cases h : useIh J i
        · rfl
        · exact absurd (Or.inl h) hnr
      have hnv : via J i = none := by
        cases h : via J i with
        | none => rfl
        | some v => exact absurd (Or.inr (by rw [h]; rfl)) hnr
      rw [hMIX, mixedVals_getD _ _ _ _ hiVS, huseA, hVS, psiVals_getD _ _ _ _ _ _ _ hifs, hnv]
      simp only [hnu, Bool.false_eq_true, if_false]
    · exact hrest
  -- assemble
  unfold foldApp
  rw [hctor, hιΨ fs hfitAll, hheadψ, ← List.foldl_append, ← hVS, hΦ _ hmemJ, ← hmemA, ← hEs,
    hιΦ VSψ hfitCopy, hheadφ, ← List.foldl_append, ← hMIX, hmixed]


set_option maxHeartbeats 1600000 in
/-- **R1's STEP, positions abstracted** (the reflexive arm): `r1_step`
with the container-recursive arm of `hpos` folded into the third
(`VS.getD i pt = vs'.getD i pt`); no induction hypothesis consumed
here. -/
theorem r1_step' (m : EnvModel V env) {dJ d : IndRepData V} {ψ' ψ : Name → Nat} {ρ σ₀ σ : Nat → V}
    {Ψ Ψ' Φ' : Nat → AnnotTerm} {k₀ base : Nat}
    -- the scratch block's representations, at every member (at the
    -- members' own spellings of the sort)
    (hrepT : d.RepsAt m)
    (hsat₀ : Sat V (d.params ψ).reverse σ₀)
    (hσ₀ : σ₀ = consList (paramVals d.nP ρ) ρ)
    (hpsFit : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
    {DsAv : List V}
    -- the copy constructor and its container constructor
    {J J' : Nat} {cA cA' : ConstantVal × Nat} (hJ' : d.ctorsA[J']? = some cA')
    (hlenD' : (d.dsF J' ψ).length = d.nP + cA'.2)
    (hpIff' : ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.dsF J' ψ).take d.nP).map (·.2.2)).reverse ρ')
    (hmemA : d.mems J' = k₀ + base + dJ.mems J) (hmemA' : d.mems J' < d.k) (hmemJ : dJ.mems J < dJ.k)
    (hΨ : ∀ t, t < dJ.k → Ψ' (k₀ + base + t) = Ψ t)
    -- the spine: it fits the real domains, the induction hypotheses at
    -- the recursive positions, the readings' facts, the terminator
    {vs' : List V} (hfit : SpineFit σ₀ ((d.Fss ψ).getD J' []) vs')
    (hEsOk : ∀ E ∈ d.esF J' ψ, WellDenoted V (consList vs' σ₀) E)
    (hEsFit : SpineFit σ₀ (d.IdsM (d.mems J') ψ) ((d.esF J' ψ).map (interp V (consList vs' σ₀))))
    {X tup : V}
    (hall : EqAll (consList vs' (cons tup (cons X σ₀)))
      (eqsXI (d.IdsC ψ).length ((d.Fss ψ).getD J' []).length ((d.Ess ψ).getD J' [])))
    -- ψ⁻¹'s ι at values (`InvSetup.fold_iota_vals`), the fold terms abstracted
    {head' : Nat → AnnotTerm} {useIhA : Nat → Nat → Bool}
    (hιΦ : ∀ vs : List V, SpineFit ρ ((d.dsF J' ψ).map (·.2.2)) (paramVals d.nP ρ ++ vs) →
      ((d.esF J' ψ).map (interp V (consList (paramVals d.nP ρ ++ vs) ρ)) ++
          [(paramVals d.nP ρ ++ vs).foldl SetTheory.app (interp V ρ (m.acval cA'.1.name ψ))]).foldl
          SetTheory.app (interp V ρ (Φ' (d.mems J')))
        = (mixedVals (ConLeche.recIdxOf (d.ksR J')) (useIhA J') vs
            ((ConLeche.recIdxOf (d.ksR J')).map fun i =>
              lamTower (d.bb ψ) (consList (vs.take i) ρ) ((d.tssR J' ψ).getD i []) fun σ'' =>
                (((d.eissR J' ψ).getD i []).map (interp V σ'') ++
                  [(Semantics.frameIdx (((d.tssR J' ψ).getD i []).length) σ'').foldl SetTheory.app
                    (vs.getD i pt)]).foldl SetTheory.app (interp V ρ (Φ' (d.tgtsR J' i))))).foldl
            SetTheory.app (interp V ρ (head' J')))
    -- ψ's ι at values (`PsiSetup.fold_iota_vals`), the fold terms abstracted
    {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {via : Nat → Nat → Option ViaSpec}
    (hιΨ : ∀ vs : List V, SpineFit σ₀ ((dJ.dsF J ψ').map (·.2.2)) (DsAv ++ vs) →
      ((dJ.esF J ψ').map (interp V (consList vs σ)) ++
          [(DsAv ++ vs).foldl SetTheory.app (interp V σ₀ (m.acval cA.1.name ψ'))]).foldl
          SetTheory.app (interp V σ₀ (Ψ (dJ.mems J)))
        = (psiVals (dJ.bb ψ') σ (ConLeche.recIdxOf (dJ.ksR J)) (useIh J) (via J) vs
            ((ConLeche.recIdxOf (dJ.ksR J)).map fun i =>
              lamTower (dJ.bb ψ') (consList (vs.take i) σ) ((dJ.tssR J ψ').getD i []) fun σ'' =>
                (((dJ.eissR J ψ').getD i []).map (interp V σ'') ++
                  [(Semantics.frameIdx (((dJ.tssR J ψ').getD i []).length) σ'').foldl SetTheory.app
                    (vs.getD i pt)]).foldl SetTheory.app (interp V σ₀ (Ψ (dJ.tgtsR J i))))).foldl
            SetTheory.app (interp V σ (head J)))
    -- ψ⁻¹'s mixed values and ψ's values at them, named
    {MIXED VS : List V}
    (hMIX : MIXED = mixedVals (ConLeche.recIdxOf (d.ksR J')) (useIhA J') vs'
      ((ConLeche.recIdxOf (d.ksR J')).map fun i =>
        lamTower (d.bb ψ) (consList (vs'.take i) ρ) ((d.tssR J' ψ).getD i []) fun σ'' =>
          (((d.eissR J' ψ).getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx (((d.tssR J' ψ).getD i []).length) σ'').foldl SetTheory.app
              (vs'.getD i pt)]).foldl SetTheory.app (interp V ρ (Φ' (d.tgtsR J' i)))))
    (hVS : VS = psiVals (dJ.bb ψ') σ (ConLeche.recIdxOf (dJ.ksR J)) (useIh J) (via J) MIXED
      ((ConLeche.recIdxOf (dJ.ksR J)).map fun i =>
        lamTower (dJ.bb ψ') (consList (MIXED.take i) σ) ((dJ.tssR J ψ').getD i []) fun σ'' =>
          (((dJ.eissR J ψ').getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx (((dJ.tssR J ψ').getD i []).length) σ'').foldl SetTheory.app
              (MIXED.getD i pt)]).foldl SetTheory.app (interp V σ₀ (Ψ (dJ.tgtsR J i)))))
    -- the constructors' facts at these values: the heads, the mixed
    -- values fit the container's telescope (NAMED: ψ⁻¹'s typing + `ord`),
    -- the container's index readings at the mixed values are the copy's
    -- at the fields (ψ's values need no fit of their own: they ARE the
    -- fields, `hvs`, before the copy's `ctor` is used)
    (hheadψ : interp V σ (head J)
      = (paramVals d.nP ρ).foldl SetTheory.app (interp V ρ (m.acval cA'.1.name ψ)))
    (hheadφ : interp V ρ (head' J') = DsAv.foldl SetTheory.app (interp V σ₀ (m.acval cA.1.name ψ')))
    (hfitMixed : SpineFit σ₀ ((dJ.dsF J ψ').map (·.2.2)) (DsAv ++ MIXED))
    (hEs : (dJ.esF J ψ').map (interp V (consList MIXED σ))
      = (d.esF J' ψ).map (interp V (consList vs' σ₀)))
    -- per position: ordinary on both sides, or the round trip given
    (hpos : ∀ i, i < cA'.2 →
      (¬ replaced (useIh J) (via J) i ∧ useIhA J' i = false) ∨
      VS.getD i pt = vs'.getD i pt) :
    R1Pred d ψ ρ σ₀ k₀ Ψ' Φ' tup (d.inj ψ J' vs') := by
  intro t' _ ht' is' his' htup
  have hJ'lt : J' < d.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ').1
  have hlenFs : vs'.length = ((d.Fss ψ).getD J' []).length := hfit.length_eq
  have hfsN : vs'.length = cA'.2 := by
    rw [hlenFs, d.Fss_getD ψ hJ', List.length_map, List.length_drop, hlenD']
    omega
  -- the terminator: the copy member and its readings (the sorted
  -- datum's clause, at the datum: it mentions no `w`)
  obtain ⟨s', cvT', cvR', mI', rP', rules', -, hrep'⟩ := hrepT t' ht'
  rw [htup] at hall
  obtain ⟨hmem, hisE⟩ : d.mems J' = t' ∧ (d.esF J' ψ).map (interp V (consList vs' σ₀)) = is' :=
    hrep'.idxRecover ψ σ₀ hsat₀ is' his' X J' vs' hJ'lt hlenFs hEsOk hEsFit hall
  subst hisE
  subst hmem
  -- the injection is the copy constructor's value
  obtain ⟨s, cvT, cvR, mI, rP, rules, -, hrep⟩ := hrepT _ hmemA'
  have hctor : d.inj ψ J' vs'
      = (paramVals d.nP ρ ++ vs').foldl SetTheory.app (interp V ρ (m.acval cA'.1.name ψ)) :=
    (hrep.ctor J' cA' hJ' ψ ρ (paramVals d.nP ρ) vs' hpsFit (by rw [← hσ₀]; exact hfit)).symm
  have hpvLen : (paramVals d.nP ρ).length = d.nP := paramVals_length _ _
  have hfitP : SpineFit ρ (((d.dsF J' ψ).take d.nP).map (·.2.2)) (paramVals d.nP ρ) :=
    spineFit_of_paramsIff hpvLen (by rw [List.length_map, List.length_take, hlenD']; omega) hpsFit hpIff'
  have hfitAll : SpineFit ρ ((d.dsF J' ψ).map (·.2.2)) (paramVals d.nP ρ ++ vs') := by
    rw [← List.take_append_drop d.nP (d.dsF J' ψ), List.map_append]
    refine hfitP.append ?_
    rw [← hσ₀, ← d.Fss_getD ψ hJ']
    exact hfit
  have hfr : consList (paramVals d.nP ρ ++ vs') ρ = consList vs' σ₀ := by
    rw [hσ₀, consList_append]
  -- ψ's values are the fields
  have hMIXlen : MIXED.length = vs'.length := by rw [hMIX, mixedVals_length]
  have hVSlen : VS.length = vs'.length := by rw [hVS, psiVals_length, hMIXlen]
  have hvs : VS = vs' := by
    refine list_ext_getD hVSlen fun i hi => ?_
    have hiN : i < cA'.2 := by rw [← hfsN, ← hVSlen]; exact hi
    have hifs : i < vs'.length := by rw [hfsN]; exact hiN
    have hiM : i < MIXED.length := by rw [hMIXlen]; exact hifs
    rcases hpos i hiN with ⟨hnr, huseA⟩ | hrest
    · -- ordinary on both sides
      have hnu : useIh J i = false := by
        cases h : useIh J i
        · rfl
        · exact absurd (Or.inl h) hnr
      have hnv : via J i = none := by
        cases h : via J i with
        | none => rfl
        | some v => exact absurd (Or.inr (by rw [h]; rfl)) hnr
      rw [hVS, psiVals_getD _ _ _ _ _ _ _ hiM, hnv]
      simp only [hnu, Bool.false_eq_true, if_false]
      rw [hMIX, mixedVals_getD _ _ _ _ hifs, huseA]
      simp only [Bool.false_eq_true, if_false]
    · exact hrest
  -- assemble
  unfold foldApp
  have h1 := hιΦ vs' hfitAll
  rw [hfr] at h1
  rw [hctor, h1, hheadφ, ← List.foldl_append, ← hMIX, hmemA, hΨ _ hmemJ, ← hEs, hιΨ MIXED hfitMixed,
    ← hVS, hheadψ, ← List.foldl_append, hvs]


/-! ## Two telescopes reading alike -/

/-- **Spine fits transfer across telescopes reading alike**: two
telescopes of equal length whose domains read alike at corresponding
frames under any prefix fitting the first accept the same spines. -/
theorem spineFit_congr_tele :
    ∀ {ds₁ ds₂ : List (Nat × Nat × AnnotTerm)} {ρ₁ ρ₂ : Nat → V},
      ds₁.length = ds₂.length →
      (∀ (k : Nat) (d₁ d₂ : Nat × Nat × AnnotTerm) (as : List V), ds₁[k]? = some d₁ → ds₂[k]? = some d₂ →
        SpineFit ρ₁ ((ds₁.take k).map (·.2.2)) as →
        interp V (consList as ρ₁) d₁.2.2 = interp V (consList as ρ₂) d₂.2.2) →
      ∀ bs : List V, SpineFit ρ₁ (ds₁.map (·.2.2)) bs ↔ SpineFit ρ₂ (ds₂.map (·.2.2)) bs
  | [], [], _, _, _, _, [] => Iff.rfl
  | [], [], _, _, _, _, _ :: _ => Iff.rfl
  | [], _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen
  | _ :: _, _ :: _, _, _, _, _, [] => Iff.rfl
  | d₁ :: ds₁, d₂ :: ds₂, ρ₁, ρ₂, hlen, hdom, b :: bs => by
    have hd : interp V ρ₁ d₁.2.2 = interp V ρ₂ d₂.2.2 := by
      have := hdom 0 d₁ d₂ [] rfl rfl trivial
      simpa using this
    show b ∈ˢ interp V ρ₁ d₁.2.2 ∧ SpineFit (cons b ρ₁) (ds₁.map (·.2.2)) bs ↔
      b ∈ˢ interp V ρ₂ d₂.2.2 ∧ SpineFit (cons b ρ₂) (ds₂.map (·.2.2)) bs
    rw [hd]
    refine and_congr_right fun hb => ?_
    refine spineFit_congr_tele (by simpa using hlen) ?_ bs
    intro k e₁ e₂ as h1 h2 has
    have := hdom (k + 1) e₁ e₂ (b :: as) (by simpa using h1) (by simpa using h2)
      ⟨by show b ∈ˢ interp V ρ₁ d₁.2.2; rw [hd]; exact hb, has⟩
    simpa using this

/-- **Two λ-towers over telescopes reading alike agree** when their
bodies agree at corresponding leaf frames. -/
theorem lamTower_congr_tele {m : Nat} {g₁ g₂ : (Nat → V) → V} :
    ∀ {ds₁ ds₂ : List (Nat × Nat × AnnotTerm)} {ρ₁ ρ₂ : Nat → V},
      ds₁.length = ds₂.length →
      (∀ (k : Nat) (d₁ d₂ : Nat × Nat × AnnotTerm) (as : List V), ds₁[k]? = some d₁ → ds₂[k]? = some d₂ →
        SpineFit ρ₁ ((ds₁.take k).map (·.2.2)) as →
        interp V (consList as ρ₁) d₁.2.2 = interp V (consList as ρ₂) d₂.2.2) →
      (∀ bs : List V, SpineFit ρ₁ (ds₁.map (·.2.2)) bs → g₁ (consList bs ρ₁) = g₂ (consList bs ρ₂)) →
      lamTower m ρ₁ ds₁ g₁ = lamTower m ρ₂ ds₂ g₂
  | [], [], ρ₁, ρ₂, _, _, hg => by
    show g₁ ρ₁ = g₂ ρ₂
    exact hg [] trivial
  | [], _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen
  | d₁ :: ds₁, d₂ :: ds₂, ρ₁, ρ₂, hlen, hdom, hg => by
    have hd : interp V ρ₁ d₁.2.2 = interp V ρ₂ d₂.2.2 := by
      have := hdom 0 d₁ d₂ [] rfl rfl trivial
      simpa using this
    show lamR m (interp V ρ₁ d₁.2.2) (fun a => lamTower m (cons a ρ₁) ds₁ g₁)
      = lamR m (interp V ρ₂ d₂.2.2) (fun a => lamTower m (cons a ρ₂) ds₂ g₂)
    rw [hd]
    refine lamR_congr fun a ha => ?_
    refine lamTower_congr_tele (by simpa using hlen) ?_ ?_
    · intro k e₁ e₂ as h1 h2 has
      have := hdom (k + 1) e₁ e₂ (a :: as) (by simpa using h1) (by simpa using h2)
        ⟨by show a ∈ˢ interp V ρ₁ d₁.2.2; rw [hd]; exact ha, has⟩
      simpa using this
    · intro bs hbs
      have := hg (a :: bs) ⟨by show a ∈ˢ interp V ρ₁ d₁.2.2; rw [hd]; exact ha, hbs⟩
      simpa using this

end ConLeche.Model
