module

public import ConLeche.Model.Inductives.RoundTripReflRunR1
public section

/-!
# The REFLEXIVE arm at the transports: R2 with telescoped transports (task #279 M-C′, DESIGN §M.40)

`RoundTripReflRun.lean` lifted `hfin` but kept the transports finitary
(`hfinT`).  A TELESCOPED TRANSPORT is a container-ordinary field
`Nat → List T` of `J` at the pin `J T`: the copy's field is recursive
into the copy of `List T` under a telescope.  ψ's value there is
`viaVal`'s λ-tower over the (lifted, rebitted) copy telescope, ψ⁻¹'s
mixed value the λ-tower over the copy telescope whose leaves apply
ψ⁻¹'s fold at the target copy — the same shape as `mixed_recJ`, the
round trip inside being R2 at the target pin pointwise.

* **`mixed_transport'`** — THE POSITION at any telescope (`mixed_transport`
  was at the empty one);
* **`pos_refl'`/`r2Grp_refl'`/`r2Grp_order_refl'`/`r2Grp_order_full`** —
  R2 at the run with NO restriction on the fields' shapes.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock ElimState)

universe w

variable {V : Type w} [SetTheory V]

namespace NestedRunFacts

variable {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState}
  {b : MutualBlock} {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)}
  {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
  {lpsT : List Name} {order : List Nat} {s : Level}
  (R : NestedRunFacts F env p st b params pbs mpAux d ψ cd lpsT order s)

include R

set_option maxHeartbeats 6400000 in
/-- **ψ⁻¹'s mixed value at a TRANSPORT is the field, telescopes
included**: ψ's value is `viaVal`'s tower over the lifted copy
telescope, whose leaf at `bs` is the target pin's term at the copy's
readings and the field's application (`spineFit_liftDoms`,
`interp_liftN_middle`, `shiftE_consList_middle` undo the lifts); ψ⁻¹'s
mixed value the tower over the copy telescope whose leaf applies the
fold at the target copy; the field lies in the target pin's carrier at
the readings under every fitting `bs` (`containerDom_transport`,
`interp_mkPisAV_piTele` at the copy's bits, `piTele_fold`,
`transport_fits` at `bs`), so R2 at the target pin closes each leaf,
and η (`piTele_eta`) closes the tower. -/
theorem mixed_transport' (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    {i : Nat} (hi : i < cA.2) (hT : i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J))
    (hA : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)))
    {j' : Nat} (htgt : d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + j')
    (hR2 : IndRepData.R2At mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j')
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j')
      (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j')))
    {fs : List V}
    (hfit : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (((cd j).dJ.Fss (cd j).ψ').getD J []) fs) :
    (d.mixedValsAt mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) order s tbl₀ ρ j J fs).getD i pt
      = fs.getD i pt := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hD := hf.ctor.2.2
  have hDJ := (hrepJ.ctors J cA hJ).2.2
  have hj' : j' < st.pins.length := by
    have := R.transport_lt hj hJ i
    rw [htgt] at this
    omega
  have hg' := R.groupFacts hj'
  have hk : p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i := by rw [htgt]; exact Nat.le_add_right _ _
  -- the bits
  have hwA : d.w ψ ≠ 0 := fun h => hbA (R.bbA_iff.mpr h)
  have hbJ : (cd j).dJ.bb (cd j).ψ' ≠ 0 := fun h => hbA ((R.bb_iff hj).mpr h)
  have hz : d.bb ψ = 0 ↔ d.w ψ = 0 := R.bbA_iff
  -- the frames
  have hσ₀ : consList ((paramBvarsAt d.nP d.nP).map (interp V ρ)) ρ = consList (paramVals d.nP ρ) ρ := rfl
  have hsat₀ : Sat V (d.params ψ).reverse (consList (paramVals d.nP ρ) ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hρ
    rwa [List.append_nil] at h
  have hDsLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := by
    rw [List.length_map, hg.len]
  have hlenDJ : ((cd j).dJ.dsF J (cd j).ψ').length = (cd j).dJ.nP + cA.2 := hDJ.len (cd j).ψ'
  have hlenDA : (d.dsF (auxOfsOf st p.k cd j J) ψ).length = d.nP + cA'.2 := hD.len ψ
  have hksLenA : (d.ksR (auxOfsOf st p.k cd j J)).length = cA'.2 := by
    rw [hf.view.1]; exact hf.ctor.2.2.ksLen
  have hfsN : fs.length = cA.2 := by
    rw [hfit.length_eq, (cd j).dJ.Fss_getD (cd j).ψ' hJ, List.length_map, List.length_drop, hlenDJ]; omega
  have hifs : i < fs.length := by rw [hfsN]; exact hi
  have htake : (fs.take i).length = i := by rw [List.length_take]; omega
  have hAF : i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) := by rw [← hf.view.1]; exact hA
  have htssRF : d.tssR (auxOfsOf st p.k cd j J) ψ = d.tssF (auxOfsOf st p.k cd j J) ψ := by rw [hf.view.2.2.2]
  have heissRF : d.eissR (auxOfsOf st p.k cd j J) ψ = d.eissF (auxOfsOf st p.k cd j J) ψ := by rw [hf.view.2.2.1]
  -- ψ's values
  obtain ⟨VS, hVS⟩ : ∃ VS, VS = d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
    (consList (paramVals d.nP ρ) ρ) j J fs := ⟨_, rfl⟩
  have hVSlen : VS.length = fs.length := by rw [hVS]; unfold IndRepData.psiValsAt; rw [psiVals_length]
  have hiVS : i < VS.length := by rw [hVSlen]; exact hifs
  have htakeV : (VS.take i).length = i := by rw [List.length_take]; omega
  have hsh : ShadowRel d.nP (d.ksF (auxOfsOf st p.k cd j J)) fs VS := by
    rw [hVS, ← hf.view.1]; exact R.psiVals_shadowRel tbl₀ hj hJ fs
  have hpush : ∀ (as : List V) (n : Nat), n < as.length + i + d.nP →
      consList as (consList (VS.take i) ρ) n = consList as (consList (VS.take i) (consList (paramVals d.nP ρ) ρ)) n :=
    fun as n hn => consList_agree_below (n := i + d.nP)
      (fun l' hl' => consList_agree_below (n := d.nP) (fun l'' hl'' => (push_agree ρ ρ l'' hl'').symm) (VS.take i) l'
        (by rw [htakeV]; omega)) as n (by omega)
  obtain ⟨-, hnbT, hnbE, -⟩ := FixCtorDataI.noBVar_entries hD hf.cf hf.cb ψ
  -- the copy's telescope and readings, at ψ's frame and at the fields' frame
  have hdomA : ∀ (k : Nat) (dA : Nat × Nat × AnnotTerm) (as : List V),
      ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [])[k]? = some dA → as.length = k →
      interp V (consList as (consList (VS.take i) ρ)) dA.2.2
        = interp V (consList as (consList (fs.take i) (consList (paramVals d.nP ρ) ρ))) dA.2.2 := by
    intro k dA as hkA hasLen
    have hbelow : Term.bvarsBelow (d.nP + i + k) dA.2.2.erase :=
      domsBelow_getElem? (hD.tssBelow ψ i) (by rw [← htssRF]; exact hkA)
    rw [interp_congr_below V _ (d.nP + i + k) _ (consList as (consList (VS.take i) (consList (paramVals d.nP ρ) ρ)))
      hbelow (fun l hl => hpush as l (by rw [hasLen]; omega))]
    have hnb := hnbT i (by rw [hf.nF]; exact hi) k dA (by rw [← htssRF]; exact hkA)
    have h := interp_congr_shadowRel (hsh.take i) (consList (paramVals d.nP ρ) ρ) as (E := dA.2.2)
      (by rw [htake, hasLen]; exact hnb)
    exact h.symm
  have hreadA : ∀ bs : List V, bs.length = ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length →
      ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V (consList bs (consList (VS.take i) ρ)))
        = ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (interp V (consList bs (consList (fs.take i) (consList (paramVals d.nP ρ) ρ)))) := by
    intro bs hbsLen
    apply List.map_congr_left
    intro E hE
    have hEb : Term.bvarsBelow (d.nP + i + bs.length) E.erase := by
      have := hD.eissBelow ψ i E (by rw [← heissRF]; exact hE)
      rwa [← htssRF, ← hbsLen] at this
    rw [interp_congr_below V E (d.nP + i + bs.length) _
      (consList bs (consList (VS.take i) (consList (paramVals d.nP ρ) ρ))) hEb (fun l hl => hpush bs l (by omega))]
    have hnb := hnbE i (by rw [hf.nF]; exact hi) E (by rw [← heissRF]; exact hE)
    have h := interp_congr_shadowRel (hsh.take i) (consList (paramVals d.nP ρ) ρ) bs (E := E)
      (by rw [htake, hbsLen, htssRF]; exact hnb)
    exact h.symm
  -- the field in the target pin's carrier, under the telescope
  have hfitPre : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (((((cd j).dJ.dsF J (cd j).ψ').drop (cd j).dJ.nP).take i).map (·.2.2)) (fs.take i) := by
    rw [List.map_take, ← (cd j).dJ.Fss_getD (cd j).ψ' hJ]
    exact spineFit_take' hfit (by rw [← hfit.length_eq, hfsN]; omega)
  obtain ⟨j'', hj''eq, -, hdom, hWD⟩ := d.containerDom_transport mpAux.base2 hg.len (auxOfsOf st p.k cd j) cd
    hf.read hlenDJ (by rw [hlenDA, hf.nF]) (by rw [hksLenA, hf.nF]) hsat₀ hi hT hA hk htake hfitPre
  obtain rfl : j' = j'' := by rw [htgt] at hj''eq; omega
  have hc' : CopyData.Ok mpAux.base2 d ψ p.k j' (cd j') := hg'.ok (R.pins j' hj').1.2.1
  have hkindA := (mem_recIdxOf.mp hAF).2
  have hEl : ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).length = d.nIdxAt (p.k + j') := by
    rw [heissRF]
    rcases hkindA with hk' | hk'
    · rw [hD.eisLen ψ i hk' (by rw [hf.nF]; exact hi)]
      show d.nIdxAt (d.tgts (auxOfsOf st p.k cd j J) i) = _
      rw [← hf.view.2.1, htgt]
    · rw [hD.eisLenRefl ψ i hk' (by rw [hf.nF]; exact hi)]
      show d.nIdxAt (d.tgts (auxOfsOf st p.k cd j J) i) = _
      rw [← hf.view.2.1, htgt]
  have hFeq : (((cd j).dJ.Fss (cd j).ψ').getD J [])[i]?
      = some (((cd j).dJ.dsF J (cd j).ψ').getD ((cd j).dJ.nP + i) default).2.2 := by
    rw [(cd j).dJ.Fss_getD (cd j).ψ' hJ, List.getElem?_map, List.getElem?_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenDJ]; omega)]
    rfl
  have hfi := spineFit_getElem? hfit i (fs.getD i pt) _
    (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hifs]; rfl) hFeq
  rw [hdom, ConLeche.Semantics.interp_mkPisAV_piTele (v := d.w ψ) (acc := [])
    (B := fun bs => interp V (consList bs (consList (fs.take i) (consList (paramVals d.nP ρ) ρ)))
      (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j').dJ.memberName (cd j').mm) (cd j').ψ')
        (((cd j').DsA).map (·.liftN (i + ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length) 0) ++
          (d.eissR (auxOfsOf st p.k cd j J) ψ).getD i [])))
    (fun dd hdd => hD.tssBits ψ i dd (by rw [← htssRF]; exact hdd))
    (fun as _ => by simp only [List.nil_append])] at hfi
  have heta := piTele_eta hwA hfi
  -- ψ's value: the transport's tower
  have hvia := psiVia_transport (d := d) (mpAux := mpAux) (ψ := ψ) (cd := cd) (order := order) tbl₀ hT hA hk
  have hshiftΨ : shiftE (cd j).dJ.nP 0
      (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      = consList (paramVals d.nP ρ) ρ := by
    rw [← hDsLen]; exact shiftE_consList _ _
  have hshiftM : shiftE (cd j).dJ.nP i
      (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
      = consList (fs.take i) (consList (paramVals d.nP ρ) ρ) := by
    have := shiftE_consList_middle (fs.take i) ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
      (consList (paramVals d.nP ρ) ρ)
    rwa [hDsLen, htake] at this
  have hVSi : VS.getD i pt
      = lamTower ((cd j).dJ.bb (cd j).ψ')
          (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
          (rebit ((cd j).dJ.bb (cd j).ψ') (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [])))
          fun σ' =>
          ((((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map
              (·.liftN (cd j).dJ.nP (i + ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length))).map (interp V σ') ++
            [(Semantics.frameIdx (rebit ((cd j).dJ.bb (cd j).ψ')
              (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []))).length σ').foldl
              SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
            (interp V (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
              ((d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j').liftN (cd j).dJ.nP 0)) := by
    rw [hVS]
    unfold IndRepData.psiValsAt
    rw [psiVals_getD _ _ _ _ _ _ _ hifs, hvia, htgt, Nat.add_sub_cancel_left]
    rfl
  -- ψ⁻¹'s mixed value: the tower over the copy telescope
  have huseA : d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true := by
    unfold IndRepData.invUseIh
    exact decide_eq_true ⟨by rw [hf.read.mem]; omega, hA, hk⟩
  have hMIXi : (d.mixedValsAt mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) order s tbl₀ ρ j J fs).getD i pt
      = lamTower (d.bb ψ) (consList (VS.take i) ρ) ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []) fun σ'' =>
          (((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length) σ'').foldl
              SetTheory.app (VS.getD i pt)]).foldl SetTheory.app
            (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j'))) := by
    unfold IndRepData.mixedValsAt
    rw [← hVS, mixedVals_getD _ _ _ _ hiVS, huseA]
    simp only [if_true]
    rw [getD_map_idxOf hA, htgt]
  rw [hMIXi, ← heta, lamTower_bit_agree hz]
  have hdom' : ∀ (k : Nat) (d₁ d₂ : Nat × Nat × AnnotTerm) (as : List V),
      ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [])[k]? = some d₁ →
      ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [])[k]? = some d₂ →
      SpineFit (consList (VS.take i) ρ) ((((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).take k).map (·.2.2)) as →
      interp V (consList as (consList (VS.take i) ρ)) d₁.2.2
        = interp V (consList as (consList (fs.take i) (consList (paramVals d.nP ρ) ρ))) d₂.2.2 := by
    intro k d₁ d₂ as h1 h2 has
    obtain rfl : d₁ = d₂ := Option.some.inj (h1.symm.trans h2)
    have hklt : k < ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length := (List.getElem?_eq_some_iff.mp h1).1
    exact hdomA k d₁ as h1 (by rw [has.length_eq, List.length_map, List.length_take]; omega)
  refine lamTower_congr_tele rfl hdom' ?_
  intro bs hbs
  have hbsF : SpineFit (consList (fs.take i) (consList (paramVals d.nP ρ) ρ))
      (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).map (·.2.2)) bs :=
    (spineFit_congr_tele rfl hdom' bs).mp hbs
  have hbsLen : bs.length = ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length := by
    rw [hbs.length_eq, List.length_map]
  have hfr : Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length) (consList bs (consList (VS.take i) ρ))
      = bs := by rw [← hbsLen]; exact frameIdx_consList' _ _
  have hfr' : Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length)
      (consList bs (consList (fs.take i) (consList (paramVals d.nP ρ) ρ))) = bs := by
    rw [← hbsLen]; exact frameIdx_consList' _ _
  -- ψ's value applied: the target pin's term at the readings and the field's application
  have hbsL : SpineFit (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
      ((rebit ((cd j).dJ.bb (cd j).ψ') (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []))).map (·.2.2)) bs := by
    rw [rebit_map_dom, spineFit_liftDoms, hshiftM]
    exact hbsF
  have hfold : bs.foldl SetTheory.app (VS.getD i pt)
      = (((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (interp V (consList bs (consList (fs.take i) (consList (paramVals d.nP ρ) ρ)))) ++
          [bs.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
          (interp V (consList (paramVals d.nP ρ) ρ) (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j')) := by
    rw [hVSi, lamTower_fold hbJ hbsL]
    have hfrL : Semantics.frameIdx (rebit ((cd j).dJ.bb (cd j).ψ')
        (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []))).length
        (consList bs (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
          (consList (paramVals d.nP ρ) ρ)))) = bs := by
      rw [rebit_length, liftDoms_length, ← hbsLen]; exact frameIdx_consList' _ _
    rw [hfrL, interp_liftN, hshiftΨ, List.map_map]
    congr 2
    apply List.map_congr_left
    intro E _
    simp only [Function.comp_def]
    have hE : E.liftN (cd j).dJ.nP (i + ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length)
        = E.liftN ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length (fs.take i ++ bs).length := by
      rw [hDsLen, List.length_append, htake, hbsLen]
    rw [show consList bs (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
        (consList (paramVals d.nP ρ) ρ)))
      = consList (fs.take i ++ bs) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
        (consList (paramVals d.nP ρ) ρ)) from (consList_append _ _ _).symm,
      hE, interp_liftN_middle, consList_append]
  -- the field's application in the target pin's carrier, the readings fitting
  obtain ⟨-, hbody, -, hisFit⟩ := d.transport_fits mpAux.base2 hc' hEl htake hWD hbsF
  have hfa := piTele_fold hwA hfi (fitsS_teleOfFields.mpr hbsF)
  simp only [List.nil_append] at hfa
  rw [hbody] at hfa
  -- the round trip at the target pin
  have hR2' := hR2 _ (bs.foldl SetTheory.app (fs.getD i pt)) (by rw [hσ₀]; exact hisFit) (by rw [hσ₀]; exact hfa)
  rw [hσ₀] at hR2'
  unfold foldApp at hR2'
  show ((((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V (consList bs (consList (VS.take i) ρ)))) ++
      [(Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length)
        (consList bs (consList (VS.take i) ρ))).foldl SetTheory.app (VS.getD i pt)]).foldl SetTheory.app
      (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j')))
    = (Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length)
        (consList bs (consList (fs.take i) (consList (paramVals d.nP ρ) ρ)))).foldl SetTheory.app (fs.getD i pt)
  rw [hfr, hfr', hfold, hreadA bs hbsLen]
  exact hR2'

/-! ## R2 at the run, every field shape -/

set_option maxHeartbeats 3200000 in
/-- **The per-position facts of `r2_step'`, telescopes included**: a
container-recursive position by `mixed_recJ` (the pointwise induction
hypothesis), a transport by `mixed_transport'` (any telescope), any other
position ordinary on both sides. -/
theorem pos_refl' (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    (hR2 : ∀ j', j' < st.pins.length → ConLeche.CopyRef (ElimState.grp st) p.k st j j' →
      IndRepData.R2At mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j')
        (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j')))
    {fs : List V}
    (hfit : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (((cd j).dJ.Fss (cd j).ψ').getD J []) fs)
    {X : V}
    (hslot : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      fs.getD i pt ∈ˢ slotSet ((cd j).dJ.w (cd j).ψ') ((cd j).dJ.u (cd j).ψ')
        (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        ((((cd j).dJ.tlss (cd j).ψ').getD J []).getD i []) ((((cd j).dJ.Eiss (cd j).ψ').getD J []).getD i []) X)
    (hIH : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) → ∀ bs : List V,
      SpineFit (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        ((((cd j).dJ.tssF J (cd j).ψ').getD i []).map (·.2.2)) bs →
      R2Pred (cd j).dJ (cd j).ψ' ρ (consList (paramVals d.nP ρ) ρ)
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
        (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t))
        ((cd j).dJ.tup (cd j).ψ' ((cd j).dJ.tgts J i)
          ((((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList bs (consList (fs.take i)
            (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))))))
        (bs.foldl SetTheory.app (fs.getD i pt)))
    (hEntryFit : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) → ∀ bs : List V,
      SpineFit (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        ((((cd j).dJ.tssF J (cd j).ψ').getD i []).map (·.2.2)) bs →
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        ((cd j).dJ.IdsM ((cd j).dJ.tgts J i) (cd j).ψ')
        ((((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList bs (consList (fs.take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))))) :
    ∀ i, i < cA.2 →
    (¬ replaced (IndRepData.psiUseIh (cd j).dJ J)
        (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J) i ∧
      d.invUseIh p.k (auxOfsOf st p.k cd j J) i = false) ∨
    (d.mixedValsAt mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) order s tbl₀ ρ j J fs).getD i pt
      = fs.getD i pt := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  have hlen : fs.length = cA.2 := by
    rw [hfit.length_eq, (cd j).dJ.Fss_getD (cd j).ψ' hJ, List.length_map, List.length_drop,
      (hrepJ.ctors J cA hJ).2.2.len (cd j).ψ']
    omega
  intro i hi
  by_cases hA : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J)
  · exact Or.inr (R.mixed_recJ tbl₀ hρ hbA hj hJ hi hA hlen (hslot i hA) (hIH i hA) (hEntryFit i hA))
  · by_cases hTr : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) ∧
        p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i
    · obtain ⟨hAr, hk⟩ := hTr
      have hj' : d.tgtsR (auxOfsOf st p.k cd j J) i - p.k < st.pins.length := R.transport_lt hj hJ i
      have href : ConLeche.CopyRef (ElimState.grp st) p.k st j (d.tgtsR (auxOfsOf st p.k cd j J) i - p.k) :=
        R.bridge j hj J cA hJ i hi hAr hA hk
      exact Or.inr (R.mixed_transport' tbl₀ hρ hbA hj hJ hi hA hAr
        (show d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + (d.tgtsR (auxOfsOf st p.k cd j J) i - p.k) by omega)
        (hR2 _ hj' href) hfit)
    · have hvia : d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J i = none := by
        unfold IndRepData.psiVia
        rw [if_neg]
        rintro ⟨h1, -, h3⟩
        exact hTr ⟨h1, h3⟩
      refine Or.inl ⟨?_, ?_⟩
      · rintro (h | h)
        · unfold IndRepData.psiUseIh at h
          exact hA (of_decide_eq_true h)
        · rw [hvia] at h
          exact nomatch h
      · unfold IndRepData.invUseIh
        apply decide_eq_false
        rintro ⟨-, h2, h3⟩
        exact hTr ⟨h2, h3⟩

set_option maxHeartbeats 6400000 in
/-- **R2 for pin `j`'s group, every field shape** (`r2Grp_refl` with
`pos_refl'`): no restriction on the containers' or the copies' fields;
the bit nonzero. -/
theorem r2Grp_refl' (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    (hbA : d.bb ψ ≠ 0)
    (hR2 : ∀ j', j' < st.pins.length → ConLeche.CopyRef (ElimState.grp st) p.k st j j' →
      IndRepData.R2At mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j')
        (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j'))) :
    R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
      (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  have hbJ : (cd j).dJ.bb (cd j).ψ' ≠ 0 := fun h => hbA ((R.bb_iff hj).mpr h)
  have hw : (cd j).dJ.w (cd j).ψ' ≠ 0 := by
    rw [R.wJ_eq hj]; exact fun h => hbA (R.bbA_iff.mpr h)
  have hg := R.groupFacts hj
  have hpf := (R.pins j hj).1.1
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  have hk : 0 < d.k := by rw [R.dk]; omega
  have hDsFit := R.pinFit hj hρ
  have hDsLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := by
    rw [List.length_map, hg.len]
  have hsat : Sat V ((cd j).dJ.params (cd j).ψ').reverse
      (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hDsFit
    rwa [List.append_nil] at h
  have hrepT : ∀ t, t < (cd j).dJ.k → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IndRep mpAux.base2 ((cd j).dJ.memberName t) cvT cvR mI rP rules (cd j).dJ t := hpf.repAll
  have hps : (paramBvarsAt d.nP d.nP).map (interp V ρ) = paramVals d.nP ρ := rfl
  show ∀ t, t < (cd j).dJ.k → IndRepData.R2At mpAux.base2 ρ (paramBvarsAt d.nP d.nP)
    ⟨(cd j).dJ, t, (cd j).ψ', (cd j).DsA, (cd j).base⟩ _ _
  refine r2Grp_of_step mpAux.base2 (c := cd j) hrepT (by rw [hps]; exact hDsFit) ?_
  simp only [hps]
  intro tup htup J fs hJlt hchain
  obtain ⟨cA, hJ⟩ : ∃ cA, (cd j).dJ.ctorsA[J]? = some cA := ⟨_, List.getElem?_eq_getElem hJlt⟩
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hC := hrepJ.ctors J cA hJ
  have hlenD : ((cd j).dJ.dsF J (cd j).ψ').length = (cd j).dJ.nP + cA.2 := hC.2.2.len (cd j).ψ'
  have hmemJ : (cd j).dJ.mems J < (cd j).dJ.k := by
    have := (hrepJ.memsReal J (by unfold IndRepData.nAll; rw [hg.ctorsC]; simpa using hJlt)).mpr hJlt
    rw [hg.kReal] at this
    exact this
  have htgts : ∀ i, (cd j).dJ.tgts J i < (cd j).dJ.k := by
    intro i
    have := hrepJ.tgtsRLt J i
    rw [(hg.view J).2.1] at this
    exact this
  obtain ⟨hlen, hchainFit, hall⟩ := hchain
  have hX : r2Fam (cd j).dJ (cd j).ψ' ρ (consList (paramVals d.nP ρ) ρ)
      (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t))
      ∈ˢ famSpace ((cd j).dJ.w (cd j).ψ') ((cd j).dJ.idx (cd j).ψ'
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))) :=
    graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpFamSet_mem _ _ _) hi)
  obtain ⟨cvT', cvR', mI', rP', rules', hrep'⟩ := hrepT _ hmemJ
  have hfields := hrep'.chainFit_fields (cd j).ψ' hsat hX htup hJlt ⟨hlen, hchainFit, hall⟩
  have hfacts := R.ctor_facts tbl₀ hρ hj hJ
  have hEntry := R.ctor_facts' tbl₀ hρ hj hJ
  obtain ⟨hfit, hIH⟩ := fieldsFit_of_chainFit' (IndRepData.RepsAt.of_single hrepT) hw hsat hDsFit hDsLen hJ rfl hC
    htgts hEntry hlen hfields
  have hvsN : fs.length = cA.2 := by
    rw [hlen, (cd j).dJ.Fss_getD (cd j).ψ' hJ, List.length_map, List.length_drop, hlenD]; omega
  have hnF : (((cd j).dJ.Fss (cd j).ψ').getD J []).length = cA.2 := by rw [← hlen, hvsN]
  -- the slots and the entries' fits at the fields' prefix
  have hpreI : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      (fs.take i).length = i ∧
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        (((((cd j).dJ.dsF J (cd j).ψ').drop (cd j).dJ.nP).map (·.2.2)).take i) (fs.take i) := by
    intro i hi
    have hilt : i < cA.2 := by
      have := (mem_recIdxOf.mp hi).1
      rw [hC.2.2.ksLen] at this
      exact this
    refine ⟨by rw [List.length_take]; omega, ?_⟩
    rw [← (cd j).dJ.Fss_getD (cd j).ψ' hJ]
    exact spineFit_take' hfit (by rw [hnF]; omega)
  have hslot : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      fs.getD i pt ∈ˢ slotSet ((cd j).dJ.w (cd j).ψ') ((cd j).dJ.u (cd j).ψ')
        (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        ((((cd j).dJ.tlss (cd j).ψ').getD J []).getD i []) ((((cd j).dJ.Eiss (cd j).ψ').getD J []).getD i [])
        (r2Fam (cd j).dJ (cd j).ψ' ρ (consList (paramVals d.nP ρ) ρ)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
          (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
          (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t))) := by
    intro i hi
    have hilt : i < cA.2 := by
      have := (mem_recIdxOf.mp hi).1
      rw [hC.2.2.ksLen] at this
      exact this
    have hrec : ((cd j).dJ.rss.getD J []).getD i false = true :=
      ((cd j).dJ.rss_getD_iff hJlt (by rw [hC.2.2.ksLen]; exact hilt)).mpr hi
    have hiF : i < (((cd j).dJ.Fss (cd j).ψ').getD J []).length := by rw [hnF]; exact hilt
    have hifs : i < fs.length := by rw [hvsN]; exact hilt
    exact (hfields i _ (List.getElem?_eq_getElem hiF) (fs.getD i pt)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hifs]; rfl)).1 hrec
  have hEntryFit : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) → ∀ bs : List V,
      SpineFit (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        ((((cd j).dJ.tssF J (cd j).ψ').getD i []).map (·.2.2)) bs →
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        ((cd j).dJ.IdsM ((cd j).dJ.tgts J i) (cd j).ψ')
        ((((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList bs (consList (fs.take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))))) :=
    fun i hi bs hbs => (hEntry i hi (fs.take i) (hpreI i hi).1 (hpreI i hi).2 bs hbs).2
  have hιΨ := fun (vs : List V)
      (hfitv : SpineFit (consList (paramVals d.nP ρ) ρ) (((cd j).dJ.dsF J (cd j).ψ').map (·.2.2))
        ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) ++ vs)) =>
    R.psi_iota tbl₀ hρ rfl hj hbJ (fun _ => rfl) hJ
      (by have := hfitv.length_eq
          rw [List.length_append, hDsLen, List.length_map, hlenD] at this; omega)
      hfitv
  have hιΦ := fun (vs' : List V)
      (hfitv : SpineFit ρ ((d.dsF (auxOfsOf st p.k cd j J) ψ).map (·.2.2)) (paramVals d.nP ρ ++ vs')) =>
    R.inv_iota hk hρ hbA hget
      (by have := hfitv.length_eq
          rw [List.length_append, paramVals_length, List.length_map, hf.ctor.2.2.len ψ] at this; omega)
      hfitv
  exact r2_step' mpAux.base2 (d := d) (ψ := ψ) (cA' := cA') hrepT hsat rfl hDsFit hDsLen hJ hlenD
    (hrepJ.paramsIff J cA hJ (cd j).ψ') hmemJ hf.read.mem (fun t _ => rfl) hfit
    (hfacts.1 fs hfit).1 (hfacts.1 fs hfit).2 hall hιΨ hιΦ rfl rfl
    (d.psiHead_interp mpAux.base2 ψ (auxOfsOf st p.k cd j) hget hDsLen) (R.headφ_of_run hj hJ).headφ
    (R.fitCopy_of_run tbl₀ hρ hj hJ hfit)
    (R.es_of_record tbl₀ hρ hj hJ hvsN)
    (R.pos_refl' tbl₀ hρ hbA hj hJ hR2 hfit hslot hIH hEntryFit)

/-- **R2 AT EVERY PIN along the order, every field shape**
(`r2Grp_order` with `r2Grp_refl'`). -/
theorem r2Grp_order_refl' (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0)
    :
    ∀ j, j < st.pins.length →
      R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
        (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
        (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  have key : ∀ m, ∀ j, j < st.pins.length → order.idxOf j < m →
      R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
        (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
        (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
    intro m
    induction m with
    | zero => intro j _ h; exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro j hj hidx
      refine R.r2Grp_refl' tbl₀ hρ hj hbA fun j' hj' href => ?_
      obtain ⟨-, hlt⟩ := R.ord.lt_of_ref j j' href
      exact R.r2At_of_grp tbl₀ hj' (ih j' hj' (by omega))
  intro j hj
  exact key order.length j hj (List.idxOf_lt_length_of_mem (R.ord.complete j hj))

/-- **R2 AT EVERY PIN, at ANY bit, every field shape** — M-C′'s R2
with no restriction on the fields (self-nested containers excepted:
`ContainersRep` asks `ctorsC = []`). -/
theorem r2Grp_order_full (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
    :
    ∀ j, j < st.pins.length →
      R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
        (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
        (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  intro j hj
  by_cases hb : d.bb ψ = 0
  · exact R.r2Grp_prop tbl₀ hρ hj hb
  · exact R.r2Grp_order_refl' tbl₀ hρ hb j hj

/-! ## R1: the telescoped transport -/

set_option maxHeartbeats 6400000 in
/-- **ψ's value at the mixed spine at a TRANSPORT is the field,
telescopes included** (the R1 mirror of `mixed_transport'`): ψ's value
is `viaVal`'s tower over the lifted copy telescope at the mixed prefix
whose leaf applies the target pin's term to the copy's readings and
the mixed value's application; the mixed value the tower over the copy
telescope at the fields' prefix whose leaf applies ψ⁻¹'s fold at the
target copy; the telescopes and readings agree across the frames
(`interp_liftN_middle` undoing the lifts, `mixed_shadowA` + the copy's
`noBVar_entries`, the pushed frame); the pointwise induction hypothesis
at the target copy closes each leaf and η on the copy's entry the
tower. -/
theorem pos_inv_transport' (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hbA : d.bb ψ ≠ 0) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    {i : Nat} (hi : i < cA.2) (hT : i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J))
    (hA : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)))
    {j' : Nat} (htgt : d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + j')
    {vs' : List V}
    (hfit : SpineFit (consList (paramVals d.nP ρ) ρ) ((d.Fss ψ).getD (auxOfsOf st p.k cd j J) []) vs')
    (hIH : ∀ bs : List V,
      SpineFit (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))
        (((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).map (·.2.2)) bs →
      R1Pred d ψ ρ (consList (paramVals d.nP ρ) ρ) p.k
        (fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
        (fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t')
        (d.tup ψ (d.tgts (auxOfsOf st p.k cd j J) i)
          (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (interp V (consList bs (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))))))
        (bs.foldl SetTheory.app (vs'.getD i pt)))
    (hEntryFit : ∀ bs : List V,
      SpineFit (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))
        (((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).map (·.2.2)) bs →
      SpineFit (consList (paramVals d.nP ρ) ρ) (d.IdsM (d.tgts (auxOfsOf st p.k cd j J) i) ψ)
        (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList bs (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ)))))) :
    (d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (consList (paramVals d.nP ρ) ρ) j J
        (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs')).getD i pt
      = vs'.getD i pt := by
  have hg := R.groupFacts hj
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hD := hf.ctor.2.2
  have hk : p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i := by rw [htgt]; exact Nat.le_add_right _ _
  -- the bits
  have hwA : d.w ψ ≠ 0 := fun h => hbA (R.bbA_iff.mpr h)
  have hz : (cd j).dJ.bb (cd j).ψ' = 0 ↔ d.w ψ = 0 := by rw [← R.bb_iff hj, R.bbA_iff]
  -- the copy's field
  have hAF : i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) := by rw [← hf.view.1]; exact hA
  have htssRF : d.tssR (auxOfsOf st p.k cd j J) ψ = d.tssF (auxOfsOf st p.k cd j J) ψ := by rw [hf.view.2.2.2]
  have heissRF : d.eissR (auxOfsOf st p.k cd j J) ψ = d.eissF (auxOfsOf st p.k cd j J) ψ := by rw [hf.view.2.2.1]
  have htgtF : d.tgts (auxOfsOf st p.k cd j J) i = d.tgtsR (auxOfsOf st p.k cd j J) i := by rw [hf.view.2.1]
  have huseA : d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true := by
    unfold IndRepData.invUseIh
    exact decide_eq_true ⟨by rw [hf.read.mem]; omega, hA, hk⟩
  have hvia := psiVia_transport (d := d) (mpAux := mpAux) (ψ := ψ) (cd := cd) (order := order) tbl₀ hT hA hk
  -- the lengths and frames
  have hlen : vs'.length = cA.2 := by
    rw [hfit.length_eq, d.Fss_getD ψ hget, List.length_map, List.length_drop, hD.len ψ, hf.nF]; omega
  have hifs : i < vs'.length := by rw [hlen]; exact hi
  have htake : (vs'.take i).length = i := by rw [List.length_take]; omega
  have hMlen : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').length = vs'.length := d.invMixed_length _ _ _ _ _ _ _ _ _ _
  have hiM : i < (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').length := by rw [hMlen]; exact hifs
  have htakeM : ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').take i).length = i := by rw [List.length_take, hMlen]; omega
  have hDsLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := by
    rw [List.length_map, hg.len]
  have hshA := R.mixed_shadowA (ρ := ρ) hj hJ vs'
  obtain ⟨-, hnbT, hnbE, -⟩ := FixCtorDataI.noBVar_entries hD hf.cf hf.cb ψ
  have hpush : ∀ (as : List V) (n : Nat), n < as.length + i + d.nP →
      consList as (consList (vs'.take i) ρ) n = consList as (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ)) n :=
    fun as n hn => consList_agree_below (n := i + d.nP)
      (fun l' hl' => consList_agree_below (n := d.nP) (fun l'' hl'' => (push_agree ρ ρ l'' hl'').symm) (vs'.take i) l'
        (by rw [htake]; omega)) as n (by omega)
  have hshiftΨ : shiftE (cd j).dJ.nP 0
      (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      = consList (paramVals d.nP ρ) ρ := by
    rw [← hDsLen]; exact shiftE_consList _ _
  -- ψ's value: the transport's tower at the mixed prefix
  have hVSi : (d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (consList (paramVals d.nP ρ) ρ) j J
      (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs')).getD i pt
      = lamTower ((cd j).dJ.bb (cd j).ψ')
          (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
            (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
          (rebit ((cd j).dJ.bb (cd j).ψ') (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [])))
          fun σ' =>
          ((((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map
              (·.liftN (cd j).dJ.nP (i + ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length))).map (interp V σ') ++
            [(Semantics.frameIdx (rebit ((cd j).dJ.bb (cd j).ψ')
              (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []))).length σ').foldl
              SetTheory.app ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
                (auxOfsOf st p.k cd j J) vs').getD i pt)]).foldl SetTheory.app
            (interp V (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
              ((d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j').liftN (cd j).dJ.nP 0)) := by
    unfold IndRepData.psiValsAt
    rw [psiVals_getD _ _ _ _ _ _ _ hiM, hvia, htgt, Nat.add_sub_cancel_left]
    rfl
  -- ψ⁻¹'s mixed value: the tower over the copy telescope at the fields' prefix
  have hMIXi : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').getD i pt
      = lamTower (d.bb ψ) (consList (vs'.take i) ρ) ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []) fun σ'' =>
          (((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length) σ'').foldl
              SetTheory.app (vs'.getD i pt)]).foldl SetTheory.app
            (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j'))) := by
    unfold IndRepData.invMixed
    rw [mixedVals_getD _ _ _ _ hifs, huseA]
    simp only [if_true]
    rw [getD_map_idxOf hA, htgt]
  -- η on the field, through the copy's own entry
  have hentryA : ((d.dsF (auxOfsOf st p.k cd j J) ψ).getD (d.nP + i) default).2.2
      = mkPisAV ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [])
          (AnnotTerm.mkAppN (mpAux.base2.acval (d.memberName (d.tgts (auxOfsOf st p.k cd j J) i)) ψ)
            (paramBvarsAt d.nP (d.nP + i + ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).length) ++
              (d.eissF (auxOfsOf st p.k cd j J) ψ).getD i [])) := by
    have hilt : i < cA'.2 := by rw [hf.nF]; exact hi
    rcases (mem_recIdxOf.mp hAF).2 with hk' | hk'
    · have htl : (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = [] := hD.tssNone ψ i (by rw [hk']; decide)
      rw [hD.recEntry ψ i hk' hilt, htl, List.length_nil, Nat.add_zero]
      rfl
    · exact hD.reflEntry ψ i hk' hilt
  have hvi : vs'.getD i pt ∈ˢ interp V (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))
      ((d.dsF (auxOfsOf st p.k cd j J) ψ).getD (d.nP + i) default).2.2 := by
    have hvs' : SpineFit (consList (paramVals d.nP ρ) ρ)
        (((d.dsF (auxOfsOf st p.k cd j J) ψ).drop d.nP).map (·.2.2)) vs' := by
      rw [← d.Fss_getD ψ hget]; exact hfit
    have hlt2 : d.nP + i < (d.dsF (auxOfsOf st p.k cd j J) ψ).length := by rw [hD.len ψ, hf.nF]; omega
    exact spineFit_getElem? hvs' i (vs'.getD i pt) _
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hifs]; rfl)
      (by rw [List.getElem?_map, List.getElem?_drop, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt2]; rfl)
  rw [hentryA, ConLeche.Semantics.interp_mkPisAV_piTele (v := d.w ψ) (acc := [])
    (B := fun bs => interp V (consList bs (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ)))
      (AnnotTerm.mkAppN (mpAux.base2.acval (d.memberName (d.tgts (auxOfsOf st p.k cd j J) i)) ψ)
        (paramBvarsAt d.nP (d.nP + i + ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).length) ++
          (d.eissF (auxOfsOf st p.k cd j J) ψ).getD i [])))
    (fun dd hdd => hD.tssBits ψ i dd hdd) (fun as _ => by simp only [List.nil_append])] at hvi
  have heta := piTele_eta hwA hvi
  rw [hVSi, ← heta, lamTower_bit_agree hz]
  -- the lifted telescope at the mixed prefix reads as the copy's at the fields'
  have hlenT : (rebit ((cd j).dJ.bb (cd j).ψ') (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []))).length
      = ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).length := by
    rw [rebit_length, liftDoms_length, htssRF]
  have hdom : ∀ (k : Nat) (dL dA : Nat × Nat × AnnotTerm) (as : List V),
      (rebit ((cd j).dJ.bb (cd j).ψ') (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [])))[k]? = some dL →
      ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [])[k]? = some dA →
      SpineFit (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        (((rebit ((cd j).dJ.bb (cd j).ψ') (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []))).take k).map (·.2.2)) as →
      interp V (consList as (consList
          ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))) dL.2.2
        = interp V (consList as (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))) dA.2.2 := by
    intro k dL dA as hkL hkA has
    have hkL' : (rebit ((cd j).dJ.bb (cd j).ψ') (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [])))[k]?
        = some (dA.1, (cd j).dJ.bb (cd j).ψ', dA.2.2.liftN (cd j).dJ.nP (i + k)) := by
      simp only [rebit, List.getElem?_map, liftDoms_getElem?, htssRF, hkA, Option.map_some]
    obtain rfl : dL = (dA.1, (cd j).dJ.bb (cd j).ψ', dA.2.2.liftN (cd j).dJ.nP (i + k)) :=
      Option.some.inj (hkL.symm.trans hkL')
    have hklt : k < (((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [])).length := (List.getElem?_eq_some_iff.mp hkA).1
    have hasLen : as.length = k := by
      rw [has.length_eq, List.length_map, List.length_take, hlenT]; omega
    show interp V (consList as (consList
        ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
        (dA.2.2.liftN (cd j).dJ.nP (i + k)) = _
    have hE : dA.2.2.liftN (cd j).dJ.nP (i + k)
        = dA.2.2.liftN ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length
            ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i ++ as).length := by
      rw [hDsLen, List.length_append, htakeM, hasLen]
    rw [show consList as (consList
        ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
      = consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i ++ as)
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        from (consList_append _ _ _).symm, hE, interp_liftN_middle, consList_append]
    have hnb := hnbT i (by rw [hf.nF]; exact hi) k dA hkA
    have h := interp_congr_shadowRel (hshA.take i) (consList (paramVals d.nP ρ) ρ) as (E := dA.2.2)
      (by rw [htake, hasLen]; exact hnb)
    exact h.symm
  refine lamTower_congr_tele hlenT hdom ?_
  intro bs hbs
  have hbsA : SpineFit (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))
      (((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).map (·.2.2)) bs :=
    (spineFit_congr_tele hlenT hdom bs).mp hbs
  have hbsLen : bs.length = ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).length := by
    rw [hbsA.length_eq, List.length_map]
  have hbsLenR : bs.length = ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length := by rw [hbsLen, htssRF]
  have hfrL : Semantics.frameIdx (rebit ((cd j).dJ.bb (cd j).ψ')
      (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []))).length
      (consList bs (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
      = bs := by
    rw [hlenT, ← hbsLen]; exact frameIdx_consList' _ _
  have hfrA : Semantics.frameIdx (((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).length)
      (consList bs (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))) = bs := by
    rw [← hbsLen]; exact frameIdx_consList' _ _
  have hfrR : Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length)
      (consList bs (consList (vs'.take i) ρ)) = bs := by
    rw [← hbsLenR]; exact frameIdx_consList' _ _
  -- the readings: at the mixed prefix (lifted) and at ψ⁻¹'s frame, both the copy's at the fields'
  have hreadL : (((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map
        (·.liftN (cd j).dJ.nP (i + ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length))).map
        (interp V (consList bs (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))))
      = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList bs (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ)))) := by
    rw [List.map_map, heissRF]
    apply List.map_congr_left
    intro E hE
    simp only [Function.comp_def]
    have hE' : E.liftN (cd j).dJ.nP (i + ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length)
        = E.liftN ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length
            ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i ++ bs).length := by
      rw [hDsLen, List.length_append, htakeM, hbsLenR]
    rw [show consList bs (consList
        ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
      = consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i ++ bs)
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        from (consList_append _ _ _).symm, hE', interp_liftN_middle, consList_append]
    have hnb := hnbE i (by rw [hf.nF]; exact hi) E hE
    have h := interp_congr_shadowRel (hshA.take i) (consList (paramVals d.nP ρ) ρ) bs (E := E)
      (by rw [htake, hbsLen]; exact hnb)
    exact h.symm
  have hreadR : ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V (consList bs (consList (vs'.take i) ρ)))
      = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList bs (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ)))) := by
    rw [heissRF]
    apply List.map_congr_left
    intro E hE
    have hEb : Term.bvarsBelow (d.nP + i + bs.length) E.erase := by
      have := hD.eissBelow ψ i E hE
      rwa [← hbsLen] at this
    exact interp_congr_below V E (d.nP + i + bs.length) _ _ hEb (fun l hl => hpush bs l (by omega))
  -- the mixed value applied
  have hbsR : SpineFit (consList (vs'.take i) ρ) (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).map (·.2.2)) bs := by
    rw [htssRF]
    refine spineFit_congr_below (hD.tssBelow ψ i) (fun l hl => ?_) hbsA
    exact (consList_agree_below (n := d.nP) (fun l' hl' => push_agree ρ ρ l' hl') (vs'.take i) l
      (by rw [htake]; omega))
  have hfold : bs.foldl SetTheory.app ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
        (auxOfsOf st p.k cd j J) vs').getD i pt)
      = (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (interp V (consList bs (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ)))) ++
          [bs.foldl SetTheory.app (vs'.getD i pt)]).foldl SetTheory.app
          (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j'))) := by
    rw [hMIXi, lamTower_fold hbA hbsR, hfrR, hreadR]
  show ((((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map
        (·.liftN (cd j).dJ.nP (i + ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length))).map
        (interp V (consList bs (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))) ++
      [(Semantics.frameIdx (rebit ((cd j).dJ.bb (cd j).ψ')
        (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []))).length
        (consList bs (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))).foldl
        SetTheory.app ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
          (auxOfsOf st p.k cd j J) vs').getD i pt)]).foldl SetTheory.app
      (interp V (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        ((d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j').liftN (cd j).dJ.nP 0))
    = (Semantics.frameIdx (((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).length)
        (consList bs (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ)))).foldl SetTheory.app (vs'.getD i pt)
  rw [hfrL, hfrA, hfold, hreadL, interp_liftN, hshiftΨ]
  -- the round trip at the target copy, at the leaf
  have htgtE : d.tgts (auxOfsOf st p.k cd j J) i = p.k + j' := by rw [htgtF, htgt]
  have h := hIH bs hbsA (d.tgts (auxOfsOf st p.k cd j J) i) (by rw [htgtE]; exact Nat.le_add_right _ _)
    (by rw [htgtF]; exact hf.tgts i) _ (hEntryFit bs hbsA) rfl
  unfold foldApp at h
  simp only [] at h
  rw [htgtE, Nat.add_sub_cancel_left] at h
  exact h

/-! ## The mixed values fit, every field shape -/

set_option maxHeartbeats 6400000 in
/-- **ψ⁻¹'s mixed values fit the container constructor's telescope,
EVERY field shape** (`fitMixed_refl` with the transport position at any
telescope: the container's domain at a transport is the nested product
over the copy's telescope of the target pin's carrier
(`containerDom_transport`, `interp_mkPisAV_piTele` at the copy's bits),
the mixed value's tower rewritten at the mixed prefix
(`lamTower_congr_tele`), then `lamTower_mem_piTele` with `invFold_mem`
at the target pin at every leaf — the readings fitting the copy's
telescope through `CopyIdxRead.idxIff`, the field's application in the
copy's entry by `piTele_fold`). -/
theorem fitMixed_full (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    (hbA : d.bb ψ ≠ 0)
    {vs' : List V}
    (hfit : SpineFit (consList (paramVals d.nP ρ) ρ) ((d.Fss ψ).getD (auxOfsOf st p.k cd j J) []) vs') :
    SpineFit (consList (paramVals d.nP ρ) ρ) (((cd j).dJ.dsF J (cd j).ψ').map (·.2.2))
      ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) ++
        d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs') := by
  obtain ⟨lpsI, lpsT', S⟩ := R.invSetup_at hρ
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  obtain ⟨hfindJ, -, hDJ⟩ := hrepJ.ctors J cA hJ
  have hD := hf.ctor.2.2
  have hcff := R.ctorFieldFacts_aux hρ hget
  obtain ⟨hnbA, -, -, -⟩ := FixCtorDataI.noBVar_entries hD hf.cf hf.cb ψ
  have hshA := R.mixed_shadowA (ρ := ρ) hj hJ vs'
  -- the frames, the lengths
  have hσ₀ : consList ((paramBvarsAt d.nP d.nP).map (interp V ρ)) ρ = consList (paramVals d.nP ρ) ρ := rfl
  have hsat₀ : Sat V (d.params ψ).reverse (consList (paramVals d.nP ρ) ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hρ
    rwa [List.append_nil] at h
  have hDsFit := R.pinFit hj hρ
  have hDsLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := by
    rw [List.length_map, hg.len]
  have hlenDJ : ((cd j).dJ.dsF J (cd j).ψ').length = (cd j).dJ.nP + cA.2 := hDJ.len (cd j).ψ'
  have hlenDA : (d.dsF (auxOfsOf st p.k cd j J) ψ).length = d.nP + cA'.2 := hD.len ψ
  have hvsLen : vs'.length = cA.2 := by
    rw [hfit.length_eq, d.Fss_getD ψ hget, List.length_map, List.length_drop, hlenDA, hf.nF]; omega
  have hMlen : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').length = vs'.length := d.invMixed_length _ _ _ _ _ _ _ _ _ _
  have hvs' : SpineFit (consList (paramVals d.nP ρ) ρ)
      (((d.dsF (auxOfsOf st p.k cd j J) ψ).drop d.nP).map (·.2.2)) vs' := by
    rw [← d.Fss_getD ψ hget]; exact hfit
  have hksLenA : (d.ksR (auxOfsOf st p.k cd j J)).length = cA'.2 := by
    rw [hf.view.1]; exact hf.ctor.2.2.ksLen
  have hpvLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := hDsLen
  -- the parameters fit the container constructor's parameter domains
  have hfitP : SpineFit (consList (paramVals d.nP ρ) ρ) ((((cd j).dJ.dsF J (cd j).ψ').take (cd j).dJ.nP).map (·.2.2))
      ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) :=
    spineFit_of_paramsIff hpvLen (by rw [List.length_map, List.length_take, hlenDJ]; omega) hDsFit
      (hrepJ.paramsIff J cA hJ (cd j).ψ')
  rw [← List.take_append_drop (cd j).dJ.nP ((cd j).dJ.dsF J (cd j).ψ'), List.map_append]
  refine hfitP.append ?_
  -- the fields, position by position
  refine spineFit_of_prefix_pointwise (by rw [hMlen, hvsLen, List.length_map, List.length_drop, hlenDJ]; omega) ?_
  intro n F f hF hfn hpre
  have hn : n < cA.2 := by
    have := (List.getElem?_eq_some_iff.mp hF).1
    rw [List.length_map, List.length_drop, hlenDJ] at this; omega
  have hnv : n < vs'.length := by rw [hvsLen]; exact hn
  have hFeq : F = (((cd j).dJ.dsF J (cd j).ψ').getD ((cd j).dJ.nP + n) default).2.2 := by
    have h := hF
    rw [List.getElem?_map, List.getElem?_drop] at h
    obtain ⟨dd, hdd, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [List.getD_eq_getElem?_getD, hdd]
    rfl
  have hfeq : f = (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').getD n pt := by
    rw [List.getD_eq_getElem?_getD, hfn]; rfl
  have htake : (vs'.take n).length = n := by rw [List.length_take]; omega
  have htakeM : ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').take n).length = n := by rw [List.length_take, hMlen]; omega
  have hpre' : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (((((cd j).dJ.dsF J (cd j).ψ').drop (cd j).dJ.nP).take n).map (·.2.2))
      ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n) := by
    rw [List.map_take]; exact hpre
  have hne : (cd j).DsA ≠ [] → (cd j).DsA.length + n = (cd j).dJ.nP + n - 1 + 1 := fun hne => by
    have hpos : 0 < (cd j).DsA.length := List.length_pos_iff.mpr hne
    rw [hg.len] at hpos
    rw [hg.len]; omega
  rw [hfeq, hFeq]
  by_cases hu : d.invUseIh p.k (auxOfsOf st p.k cd j J) n = true
  · -- a hypothesis position: container-recursive (any telescope), or a transport
    have hAr : n ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) := d.invUseIh_mem hu
    have hAF : n ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) := by rw [← hf.view.1]; exact hAr
    have hk : p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) n := by
      unfold IndRepData.invUseIh at hu
      exact (of_decide_eq_true hu).2.2
    have hnlt : n < cA'.2 := by rw [hf.nF]; exact hn
    have heissF : d.eissF (auxOfsOf st p.k cd j J) ψ = d.eissR (auxOfsOf st p.k cd j J) ψ := by rw [hf.view.2.2.1]
    have htssF : d.tssF (auxOfsOf st p.k cd j J) ψ = d.tssR (auxOfsOf st p.k cd j J) ψ := by rw [hf.view.2.2.2]
    have htgtF : d.tgts (auxOfsOf st p.k cd j J) n = d.tgtsR (auxOfsOf st p.k cd j J) n := by rw [hf.view.2.1]
    have hwA : d.w ψ ≠ 0 := fun h => hbA (R.bbA_iff.mpr h)
    -- the mixed value at a hypothesis position: a tower over the copy's telescope
    have hMn : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
        (auxOfsOf st p.k cd j J) vs').getD n pt
        = lamTower (d.bb ψ) (consList (vs'.take n) ρ) ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []) fun σ'' =>
            (((d.eissR (auxOfsOf st p.k cd j J) ψ).getD n []).map (interp V σ'') ++
              [(Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length) σ'').foldl
                SetTheory.app (vs'.getD n pt)]).foldl SetTheory.app
              (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
                (d.tgtsR (auxOfsOf st p.k cd j J) n))) := by
      unfold IndRepData.invMixed
      rw [mixedVals_getD _ _ _ _ hnv, hu]
      simp only [if_true]
      rw [getD_map_idxOf hAr]
    -- the field in the copy's own entry
    have hentryA : ((d.dsF (auxOfsOf st p.k cd j J) ψ).getD (d.nP + n) default).2.2
        = mkPisAV ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n [])
            (AnnotTerm.mkAppN (mpAux.base2.acval (d.memberName (d.tgts (auxOfsOf st p.k cd j J) n)) ψ)
              (paramBvarsAt d.nP (d.nP + n + ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).length) ++
                (d.eissF (auxOfsOf st p.k cd j J) ψ).getD n [])) := by
      rcases (mem_recIdxOf.mp hAF).2 with hk' | hk'
      · have htl : (d.tssF (auxOfsOf st p.k cd j J) ψ).getD n [] = [] := hD.tssNone ψ n (by rw [hk']; decide)
        rw [hD.recEntry ψ n hk' hnlt, htl, List.length_nil, Nat.add_zero]
        rfl
      · exact hD.reflEntry ψ n hk' hnlt
    have hlt2 : d.nP + n < (d.dsF (auxOfsOf st p.k cd j J) ψ).length := by rw [hlenDA, hf.nF]; omega
    have hvn : vs'.getD n pt ∈ˢ interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))
        ((d.dsF (auxOfsOf st p.k cd j J) ψ).getD (d.nP + n) default).2.2 :=
      spineFit_getElem? hvs' n (vs'.getD n pt) _
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnv]; rfl)
        (by rw [List.getElem?_map, List.getElem?_drop, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt2]; rfl)
    rw [hentryA, ConLeche.Semantics.interp_mkPisAV_piTele (v := d.w ψ) (acc := [])
      (B := fun bs => interp V (consList bs (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ)))
        (AnnotTerm.mkAppN (mpAux.base2.acval (d.memberName (d.tgts (auxOfsOf st p.k cd j J) n)) ψ)
          (paramBvarsAt d.nP (d.nP + n + ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).length) ++
            (d.eissF (auxOfsOf st p.k cd j J) ψ).getD n [])))
      (fun dd hdd => hD.tssBits ψ n dd hdd) (fun as _ => by simp only [List.nil_append])] at hvn
    by_cases hA : n ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J)
    · -- container-recursive, any telescope
      obtain ⟨hks, htgt, htss, heiss⟩ := hf.read.kindR n hA
      have htgtJ : (cd j).dJ.tgts J n < (cd j).dJ.k := by
        have := hrepJ.tgtsRLt J n
        rw [(hg.view J).2.1] at this
        exact this
      have htgtE : d.tgts (auxOfsOf st p.k cd j J) n = p.k + (cd j).base + (cd j).dJ.tgts J n := by
        rw [htgtF, htgt]
      have hz : d.bb ψ = 0 ↔ (cd j).dJ.w (cd j).ψ' = 0 := by rw [R.bbA_iff, R.wJ_eq hj]
      have hlenT : (((cd j).dJ.tssF J (cd j).ψ').getD n []).length
          = ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).length := by
        rw [htssF, htss, instSeqDoms_length]
      have hlenTR : ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length
          = (((cd j).dJ.tssF J (cd j).ψ').getD n []).length := by
        rw [htss, instSeqDoms_length]
      have hpush : ∀ (as : List V) (l : Nat), l < as.length + n + d.nP →
          consList as (consList (vs'.take n) ρ) l
            = consList as (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ)) l :=
        fun as l hl => consList_agree_below (n := n + d.nP)
          (fun l' hl' => consList_agree_below (n := d.nP) (fun l'' hl'' => (push_agree ρ ρ l'' hl'').symm)
            (vs'.take n) l' (by rw [htake]; omega)) as l (by omega)
      -- the container's entry: a nested product over its telescope of the target's carrier
      have hentryJ : (((cd j).dJ.dsF J (cd j).ψ').getD ((cd j).dJ.nP + n) default).2.2
          = mkPisAV (((cd j).dJ.tssF J (cd j).ψ').getD n [])
              (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName ((cd j).dJ.tgts J n)) (cd j).ψ')
                (paramBvarsAt (cd j).dJ.nP ((cd j).dJ.nP + n + (((cd j).dJ.tssF J (cd j).ψ').getD n []).length) ++
                  ((cd j).dJ.eissF J (cd j).ψ').getD n [])) := by
        rcases (mem_recIdxOf.mp hA).2 with hk' | hk'
        · have htl : ((cd j).dJ.tssF J (cd j).ψ').getD n [] = [] := hDJ.tssNone (cd j).ψ' n (by rw [hk']; decide)
          rw [hDJ.recEntry (cd j).ψ' n hk' hn, htl, List.length_nil, Nat.add_zero]
          rfl
        · exact hDJ.reflEntry (cd j).ψ' n hk' hn
      rw [hentryJ, ConLeche.Semantics.interp_mkPisAV_piTele (v := (cd j).dJ.w (cd j).ψ') (acc := [])
        (B := fun bs => ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) ++
            (((cd j).dJ.eissF J (cd j).ψ').getD n []).map (interp V (consList bs (consList
              ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
              (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))))).foldl
            SetTheory.app (interp V (consList (paramVals d.nP ρ) ρ)
              (mpAux.base2.acval ((cd j).dJ.memberName ((cd j).dJ.tgts J n)) (cd j).ψ')))
        (fun dd hdd => hDJ.tssBits (cd j).ψ' n dd hdd) ?_]
      · -- the two telescopes read alike
        have hdom₂ : ∀ (k : Nat) (dJ' dA : Nat × Nat × AnnotTerm) (as : List V),
            (((cd j).dJ.tssF J (cd j).ψ').getD n [])[k]? = some dJ' →
            ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n [])[k]? = some dA →
            SpineFit (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
                (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
              (((((cd j).dJ.tssF J (cd j).ψ').getD n []).take k).map (·.2.2)) as →
            interp V (consList as (consList
                ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
                (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))) dJ'.2.2
              = interp V (consList as (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))) dA.2.2 := by
          intro k dJ' dA as hkJ hkA has
          have hklt : k < (((cd j).dJ.tssF J (cd j).ψ').getD n []).length := (List.getElem?_eq_some_iff.mp hkJ).1
          have hasLen : as.length = k := by rw [has.length_eq, List.length_map, List.length_take]; omega
          exact (R.domA_eq_domJ tbl₀ hρ hj hJ hn hA hvsLen k dA dJ' as (by rw [← htssF]; exact hkA) hkJ hasLen).symm
        have hdom₁ : ∀ (k : Nat) (dA dJ' : Nat × Nat × AnnotTerm) (as : List V),
            ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n [])[k]? = some dA →
            (((cd j).dJ.tssF J (cd j).ψ').getD n [])[k]? = some dJ' →
            SpineFit (consList (vs'.take n) ρ) ((((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).take k).map (·.2.2)) as →
            interp V (consList as (consList (vs'.take n) ρ)) dA.2.2
              = interp V (consList as (consList
                  ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
                  (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))) dJ'.2.2 := by
          intro k dA dJ' as hkA hkJ has
          have hklt : k < ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length := (List.getElem?_eq_some_iff.mp hkA).1
          have hasLen : as.length = k := by rw [has.length_eq, List.length_map, List.length_take]; omega
          have hbelow : Term.bvarsBelow (d.nP + n + k) dA.2.2.erase :=
            domsBelow_getElem? (hD.tssBelow ψ n) (by rw [htssF]; exact hkA)
          rw [interp_congr_below V _ (d.nP + n + k) _ (consList as (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ)))
            hbelow (fun l hl => hpush as l (by rw [hasLen]; omega))]
          exact R.domA_eq_domJ tbl₀ hρ hj hJ hn hA hvsLen k dA dJ' as hkA hkJ hasLen
        rw [hMn, lamTower_bit_agree hz,
          lamTower_congr_tele (g₂ := fun σ'' =>
            ((((cd j).dJ.eissF J (cd j).ψ').getD n []).map (interp V σ'') ++
              [(Semantics.frameIdx ((((cd j).dJ.tssF J (cd j).ψ').getD n []).length) σ'').foldl
                SetTheory.app (vs'.getD n pt)]).foldl SetTheory.app
              (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
                (d.tgtsR (auxOfsOf st p.k cd j J) n))))
            hlenTR hdom₁ ?_]
        · refine lamTower_mem_piTele fun bs hbsF => ?_
          have hbs := fitsS_teleOfFields.mp hbsF
          simp only [List.nil_append]
          have hbsA : SpineFit (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))
              (((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).map (·.2.2)) bs :=
            (spineFit_congr_tele hlenT hdom₂ bs).mp hbs
          have hbsLen : bs.length = (((cd j).dJ.tssF J (cd j).ψ').getD n []).length := by
            rw [hbs.length_eq, List.length_map]
          have hfrJ : Semantics.frameIdx ((((cd j).dJ.tssF J (cd j).ψ').getD n []).length)
              (consList bs (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
                (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
              = bs := by
            rw [← hbsLen]; exact frameIdx_consList' _ _
          rw [hfrJ]
          -- the readings at the leaf
          have hread := R.readA_eq_readJ tbl₀ hρ hj hJ hn hA hvsLen hbsLen
          rw [← heissF] at hread
          rw [← hread]
          -- the field's application in the copy's entry
          have hfa := piTele_fold hwA hvn (fitsS_teleOfFields.mpr hbsA)
          simp only [List.nil_append] at hfa
          have hbsLenA : bs.length = ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).length := by
            rw [hbsLen, hlenT]
          rw [interp_mkAppN_map, List.map_append, Nat.add_assoc d.nP n,
            map_paramBvarsAt_interp (e := n + ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).length)
              (ρp := consList (paramVals d.nP ρ) ρ)
              (σ := consList bs (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ)))
              (fun l => by
                rw [← consList_append, show n + ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).length
                  = (vs'.take n ++ bs).length by rw [List.length_append, htake, hbsLenA]]
                exact consList_apply_add _ _ l),
            range_reverse_map_consList' (paramVals_length _ _),
            interp_closed (V := V) (mpAux.base2.cval_closedL _ _) _ ρ, htgtE] at hfa
          -- ψ⁻¹'s fold at the target, typed
          have his := (R.ctor_facts_aux' hρ hget n hAF (vs'.take n) htake
            (spineFit_take' hvs' (by rw [← hvs'.length_eq, hvsLen]; omega)) bs hbsA).2
          rw [htgtE] at his
          rw [← htgtF, htgtE]
          exact R.invFold_mem hρ hj htgtJ his hfa
        · -- the bodies agree at every leaf
          intro bs hbs
          have hbsLenR : bs.length = ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length := by
            rw [hbs.length_eq, List.length_map]
          have hbsLen : bs.length = (((cd j).dJ.tssF J (cd j).ψ').getD n []).length := by
            rw [hbsLenR, hlenTR]
          have hfrA : Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length)
              (consList bs (consList (vs'.take n) ρ)) = bs := by
            rw [← hbsLenR]; exact frameIdx_consList' _ _
          have hfrJ : Semantics.frameIdx ((((cd j).dJ.tssF J (cd j).ψ').getD n []).length)
              (consList bs (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
                (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
              = bs := by
            rw [← hbsLen]; exact frameIdx_consList' _ _
          show ((((d.eissR (auxOfsOf st p.k cd j J) ψ).getD n []).map (interp V (consList bs (consList (vs'.take n) ρ)))) ++
              [(Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length)
                (consList bs (consList (vs'.take n) ρ))).foldl SetTheory.app (vs'.getD n pt)]).foldl SetTheory.app
              (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
                (d.tgtsR (auxOfsOf st p.k cd j J) n)))
            = ((((cd j).dJ.eissF J (cd j).ψ').getD n []).map (interp V (consList bs (consList
                ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
                (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))) ++
              [(Semantics.frameIdx ((((cd j).dJ.tssF J (cd j).ψ').getD n []).length)
                (consList bs (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
                  (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))).foldl
                SetTheory.app (vs'.getD n pt)]).foldl SetTheory.app
              (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
                (d.tgtsR (auxOfsOf st p.k cd j J) n)))
          rw [hfrA, hfrJ]
          congr 2
          -- the copy's readings at `ρ` are its readings at the pushed frame, the container's at the mixed prefix
          rw [← R.readA_eq_readJ tbl₀ hρ hj hJ hn hA hvsLen hbsLen]
          apply List.map_congr_left
          intro E hE
          have hEb : Term.bvarsBelow (d.nP + n + bs.length) E.erase := by
            have := hD.eissBelow ψ n E (by rw [heissF]; exact hE)
            rwa [← hlenT, ← hbsLen] at this
          exact interp_congr_below V E (d.nP + n + bs.length) _ _ hEb (fun l hl => hpush bs l (by omega))
      · -- the container entry's body reads as the target's carrier
        intro bs hbs
        have hbsLen : bs.length = (((cd j).dJ.tssF J (cd j).ψ').getD n []).length := by
          rw [hbs.length_eq, List.length_map]
        simp only [List.nil_append]
        rw [interp_mkAppN_map, List.map_append, Nat.add_assoc (cd j).dJ.nP n,
          map_paramBvarsAt_interp (e := n + (((cd j).dJ.tssF J (cd j).ψ').getD n []).length)
            (ρp := consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
            (σ := consList bs (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
              (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
            (fun l => by
              rw [← consList_append, show n + (((cd j).dJ.tssF J (cd j).ψ').getD n []).length
                = ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n ++ bs).length
                by rw [List.length_append, htakeM, hbsLen]]
              exact consList_apply_add _ _ l),
          range_reverse_map_consList' hDsLen,
          interp_closed (V := V) (mpAux.base2.cval_closedL _ _) _ (consList (paramVals d.nP ρ) ρ)]
    · -- a transport, any telescope: the target pin's carrier under the copy's telescope
      obtain ⟨j', hj'eq, -, hdom, hWD⟩ := d.containerDom_transport mpAux.base2 hg.len (auxOfsOf st p.k cd j) cd
        hf.read hlenDJ (by rw [hlenDA, hf.nF]) (by rw [hksLenA, hf.nF]) hsat₀ hn hA hAr hk htakeM hpre'
      have hj' : j' < st.pins.length := by
        have := R.transport_lt hj hJ n
        rw [hj'eq] at this
        omega
      have hg' := R.groupFacts hj'
      have hc' : CopyData.Ok mpAux.base2 d ψ p.k j' (cd j') := hg'.ok (R.pins j' hj').1.2.1
      have hbm' : (cd j').base + (cd j').mm = j' := (R.pins j' hj').1.2.1
      have hmm' : (cd j').mm < (cd j').dJ.k := hg'.mm
      have htgtE : d.tgtsR (auxOfsOf st p.k cd j J) n = p.k + (cd j').base + (cd j').mm := by
        rw [hj'eq, Nat.add_assoc, hbm']
      have hkindA := (mem_recIdxOf.mp hAF).2
      have hEl : ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD n []).length = d.nIdxAt (p.k + j') := by
        rw [← heissF]
        rcases hkindA with hk' | hk'
        · rw [hD.eisLen ψ n hk' hnlt]
          show d.nIdxAt (d.tgts (auxOfsOf st p.k cd j J) n) = _
          rw [← hf.view.2.1, hj'eq]
        · rw [hD.eisLenRefl ψ n hk' hnlt]
          show d.nIdxAt (d.tgts (auxOfsOf st p.k cd j J) n) = _
          rw [← hf.view.2.1, hj'eq]
      have hshA := R.mixed_shadowA (ρ := ρ) hj hJ vs'
      obtain ⟨-, hnbT, hnbE, -⟩ := FixCtorDataI.noBVar_entries hD hf.cf hf.cb ψ
      have hpush : ∀ (as : List V) (l : Nat), l < as.length + n + d.nP →
          consList as (consList (vs'.take n) ρ) l
            = consList as (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ)) l :=
        fun as l hl => consList_agree_below (n := n + d.nP)
          (fun l' hl' => consList_agree_below (n := d.nP) (fun l'' hl'' => (push_agree ρ ρ l'' hl'').symm)
            (vs'.take n) l' (by rw [htake]; omega)) as l (by omega)
      have hz' : d.bb ψ = 0 ↔ d.w ψ = 0 := R.bbA_iff
      -- the copy's telescope at ψ⁻¹'s frame reads as at the mixed prefix (both the block's frame)
      have hdomM : ∀ (k : Nat) (dA : Nat × Nat × AnnotTerm) (as : List V),
          ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n [])[k]? = some dA → as.length = k →
          interp V (consList as (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))) dA.2.2
            = interp V (consList as (consList
                ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
                (consList (paramVals d.nP ρ) ρ))) dA.2.2 := by
        intro k dA as hkA hasLen
        have hnb := hnbT n (by rw [hf.nF]; exact hn) k dA (by rw [htssF]; exact hkA)
        exact interp_congr_shadowRel (hshA.take n) (consList (paramVals d.nP ρ) ρ) as (E := dA.2.2)
          (by rw [htake, hasLen]; exact hnb)
      have hdom₁ : ∀ (k : Nat) (dA dA' : Nat × Nat × AnnotTerm) (as : List V),
          ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n [])[k]? = some dA →
          ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n [])[k]? = some dA' →
          SpineFit (consList (vs'.take n) ρ) ((((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).take k).map (·.2.2)) as →
          interp V (consList as (consList (vs'.take n) ρ)) dA.2.2
            = interp V (consList as (consList
                ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
                (consList (paramVals d.nP ρ) ρ))) dA'.2.2 := by
        intro k dA dA' as hkA hkA' has
        obtain rfl : dA = dA' := Option.some.inj (hkA.symm.trans hkA')
        have hklt : k < ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length := (List.getElem?_eq_some_iff.mp hkA).1
        have hasLen : as.length = k := by rw [has.length_eq, List.length_map, List.length_take]; omega
        have hbelow : Term.bvarsBelow (d.nP + n + k) dA.2.2.erase :=
          domsBelow_getElem? (hD.tssBelow ψ n) (by rw [htssF]; exact hkA)
        rw [interp_congr_below V _ (d.nP + n + k) _ (consList as (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ)))
          hbelow (fun l hl => hpush as l (by rw [hasLen]; omega))]
        exact hdomM k dA as hkA hasLen
      have hdom₂ : ∀ (k : Nat) (dA dA' : Nat × Nat × AnnotTerm) (as : List V),
          ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n [])[k]? = some dA →
          ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n [])[k]? = some dA' →
          SpineFit (consList ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
              (consList (paramVals d.nP ρ) ρ))
            ((((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).take k).map (·.2.2)) as →
          interp V (consList as (consList
              ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
              (consList (paramVals d.nP ρ) ρ))) dA.2.2
            = interp V (consList as (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))) dA'.2.2 := by
        intro k dA dA' as hkA hkA' has
        obtain rfl : dA = dA' := Option.some.inj (hkA.symm.trans (by rw [← htssF]; exact hkA'))
        have hklt : k < ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length := (List.getElem?_eq_some_iff.mp hkA).1
        have hasLen : as.length = k := by rw [has.length_eq, List.length_map, List.length_take]; omega
        exact (hdomM k dA as hkA hasLen).symm
      -- the container's entry at the transport: a nested product over the copy's telescope
      rw [hdom, ConLeche.Semantics.interp_mkPisAV_piTele (v := d.w ψ) (acc := [])
        (B := fun bs => interp V (consList bs (consList
            ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
            (consList (paramVals d.nP ρ) ρ)))
          (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j').dJ.memberName (cd j').mm) (cd j').ψ')
            (((cd j').DsA).map (·.liftN (n + ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length) 0) ++
              (d.eissR (auxOfsOf st p.k cd j J) ψ).getD n [])))
        (fun dd hdd => hD.tssBits ψ n dd (by rw [htssF]; exact hdd))
        (fun as _ => by simp only [List.nil_append]),
        hMn, lamTower_bit_agree hz',
        lamTower_congr_tele (g₂ := fun σ'' =>
          (((d.eissR (auxOfsOf st p.k cd j J) ψ).getD n []).map (interp V σ'') ++
            [(Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length) σ'').foldl
              SetTheory.app (vs'.getD n pt)]).foldl SetTheory.app
            (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
              (d.tgtsR (auxOfsOf st p.k cd j J) n))))
          rfl hdom₁ ?_]
      · refine lamTower_mem_piTele fun bs hbsF => ?_
        have hbs := fitsS_teleOfFields.mp hbsF
        simp only [List.nil_append]
        have hbsA : SpineFit (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))
            (((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).map (·.2.2)) bs :=
          (spineFit_congr_tele (by rw [htssF]) hdom₂ bs).mp hbs
        have hbsLen : bs.length = ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length := by
          rw [hbs.length_eq, List.length_map]
        have hfrM : Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length)
            (consList bs (consList
              ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
              (consList (paramVals d.nP ρ) ρ))) = bs := by
          rw [← hbsLen]; exact frameIdx_consList' _ _
        rw [hfrM]
        -- the readings at the mixed prefix are the copy's at the fields'
        have hreadM : ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD n []).map (interp V (consList bs (consList
              ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
              (consList (paramVals d.nP ρ) ρ))))
            = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
                (interp V (consList bs (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ)))) := by
          rw [← heissF]
          apply List.map_congr_left
          intro E hE
          have hnb := hnbE n (by rw [hf.nF]; exact hn) E hE
          rw [htssF] at hnb
          have h := interp_congr_shadowRel (hshA.take n) (consList (paramVals d.nP ρ) ρ) bs (E := E)
            (by rw [htake, hbsLen]; exact hnb)
          exact h.symm
        obtain ⟨-, hbody, -, hisFit⟩ := d.transport_fits mpAux.base2 hc' hEl htakeM hWD hbs
        rw [hbody, hreadM]
        -- the readings fit the target copy's telescope (`CopyIdxRead.idxIff`)
        rw [hreadM] at hisFit
        have his : SpineFit (consList (paramVals d.nP ρ) ρ) (d.IdsM (p.k + (cd j').base + (cd j').mm) ψ)
            (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
              (interp V (consList bs (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))))) := by
          have h := ((hg'.grp (cd j').mm hmm').idx.idxIff _ hsat₀ _).mpr hisFit
          rw [Nat.add_assoc]
          exact h
        -- the field's application in the copy's entry
        have hfa := piTele_fold hwA hvn (fitsS_teleOfFields.mpr hbsA)
        simp only [List.nil_append] at hfa
        have hbsLenA : bs.length = ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).length := by
          rw [hbsLen, htssF]
        rw [interp_mkAppN_map, List.map_append, Nat.add_assoc d.nP n,
          map_paramBvarsAt_interp (e := n + ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).length)
            (ρp := consList (paramVals d.nP ρ) ρ)
            (σ := consList bs (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ)))
            (fun l => by
              rw [← consList_append, show n + ((d.tssF (auxOfsOf st p.k cd j J) ψ).getD n []).length
                = (vs'.take n ++ bs).length by rw [List.length_append, htake, hbsLenA]]
              exact consList_apply_add _ _ l),
          range_reverse_map_consList' (paramVals_length _ _),
          interp_closed (V := V) (mpAux.base2.cval_closedL _ _) _ ρ, htgtF, htgtE] at hfa
        rw [htgtE]
        exact R.invFold_mem hρ hj' hmm' his hfa
      · -- the bodies agree at every leaf
        intro bs hbs
        have hbsLen : bs.length = ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length := by
          rw [hbs.length_eq, List.length_map]
        have hfrA : Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length)
            (consList bs (consList (vs'.take n) ρ)) = bs := by
          rw [← hbsLen]; exact frameIdx_consList' _ _
        have hfrM : Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length)
            (consList bs (consList
              ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
              (consList (paramVals d.nP ρ) ρ))) = bs := by
          rw [← hbsLen]; exact frameIdx_consList' _ _
        show ((((d.eissR (auxOfsOf st p.k cd j J) ψ).getD n []).map (interp V (consList bs (consList (vs'.take n) ρ)))) ++
            [(Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length)
              (consList bs (consList (vs'.take n) ρ))).foldl SetTheory.app (vs'.getD n pt)]).foldl SetTheory.app
            (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
              (d.tgtsR (auxOfsOf st p.k cd j J) n)))
          = ((((d.eissR (auxOfsOf st p.k cd j J) ψ).getD n []).map (interp V (consList bs (consList
              ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
              (consList (paramVals d.nP ρ) ρ))))) ++
            [(Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD n []).length)
              (consList bs (consList
                ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
                (consList (paramVals d.nP ρ) ρ)))).foldl SetTheory.app (vs'.getD n pt)]).foldl SetTheory.app
            (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
              (d.tgtsR (auxOfsOf st p.k cd j J) n)))
        rw [hfrA, hfrM]
        congr 2
        apply List.map_congr_left
        intro E hE
        have hEb : Term.bvarsBelow (d.nP + n + bs.length) E.erase := by
          have := hD.eissBelow ψ n E (by rw [heissF]; exact hE)
          rwa [htssF, ← hbsLen] at this
        rw [interp_congr_below V E (d.nP + n + bs.length) _
          (consList bs (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))) hEb (fun l hl => hpush bs l (by omega))]
        have hnb := hnbE n (by rw [hf.nF]; exact hn) E (by rw [heissF]; exact hE)
        rw [htssF] at hnb
        exact interp_congr_shadowRel (hshA.take n) (consList (paramVals d.nP ρ) ρ) bs (E := E)
          (by rw [htake, hbsLen]; exact hnb)
  · -- a field passing its value: ordinary on the container's side
    have hu' : d.invUseIh p.k (auxOfsOf st p.k cd j J) n = false := by
      cases h : d.invUseIh p.k (auxOfsOf st p.k cd j J) n
      · rfl
      · exact absurd h hu
    have hnotJ : n ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) := fun h => hu (R.recJ_useIh hj hJ h)
    have hcase : n ∉ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) ∨
        d.tgtsR (auxOfsOf st p.k cd j J) n < p.k := by
      by_cases hA : n ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J))
      · refine Or.inr (Nat.lt_of_not_le fun hk => hu ?_)
        unfold IndRepData.invUseIh
        exact decide_eq_true ⟨by rw [hf.read.mem]; omega, hA, hk⟩
      · exact Or.inl hA
    have hord := hf.read.ord n hn hnotJ hcase
    -- the mixed value is the field
    have hMn : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
        (auxOfsOf st p.k cd j J) vs').getD n pt = vs'.getD n pt := by
      unfold IndRepData.invMixed
      rw [mixedVals_getD _ _ _ _ hnv, hu']
      simp only [Bool.false_eq_true, if_false]
    rw [hMn]
    -- the field is in the copy's own domain at the fields' prefix
    have hlt2 : d.nP + n < (d.dsF (auxOfsOf st p.k cd j J) ψ).length := by rw [hlenDA, hf.nF]; omega
    have hvn : vs'.getD n pt ∈ˢ interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))
        ((d.dsF (auxOfsOf st p.k cd j J) ψ).getD (d.nP + n) default).2.2 :=
      spineFit_getElem? hvs' n (vs'.getD n pt) _
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnv]; rfl)
        (by rw [List.getElem?_map, List.getElem?_drop, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt2]; rfl)
    -- the copy's domain mentions no recursive position: the same at the mixed prefix
    have hshift := interp_congr_shadowRel (hshA.take n) (consList (paramVals d.nP ρ) ρ) []
      (E := ((d.dsF (auxOfsOf st p.k cd j J) ψ).getD (d.nP + n) default).2.2)
      (by rw [htake, List.length_nil, Nat.add_zero]; exact hnbA n (by rw [hf.nF]; exact hn))
    simp only [consList_nil] at hshift
    rw [hshift] at hvn
    -- the record's `ord` at the mixed prefix, which fits the container's earlier domains
    rw [hord (consList (paramVals d.nP ρ) ρ) _ htakeM hsat₀ hpre',
      interp_instSeq_under (consList (paramVals d.nP ρ) ρ) (cd j).DsA _ _ _ (fun hne' => by
        have := hne hne'; rw [htakeM]; exact this)] at hvn
    exact hvn



/-! ## R1 at the run, every field shape -/

set_option maxHeartbeats 3200000 in
/-- **The per-position facts of `r1_step'`, telescopes included**: a
container-recursive position by `pos_inv_recJ` (the pointwise
induction hypothesis), a transport by `pos_inv_transport'` (any telescope), any other
position ordinary on both sides. -/
theorem pos_inv_full (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    {vs' : List V}
    (hfit : SpineFit (consList (paramVals d.nP ρ) ρ) ((d.Fss ψ).getD (auxOfsOf st p.k cd j J) []) vs')
    (hIH : ∀ i, i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) → ∀ bs : List V,
      SpineFit (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))
        (((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).map (·.2.2)) bs →
      R1Pred d ψ ρ (consList (paramVals d.nP ρ) ρ) p.k
        (fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
        (fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t')
        (d.tup ψ (d.tgts (auxOfsOf st p.k cd j J) i)
          (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (interp V (consList bs (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))))))
        (bs.foldl SetTheory.app (vs'.getD i pt)))
    (hEntryFit : ∀ i, i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) → ∀ bs : List V,
      SpineFit (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))
        (((d.tssF (auxOfsOf st p.k cd j J) ψ).getD i []).map (·.2.2)) bs →
      SpineFit (consList (paramVals d.nP ρ) ρ) (d.IdsM (d.tgts (auxOfsOf st p.k cd j J) i) ψ)
        (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList bs (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ)))))) :
    ∀ i, i < cA.2 →
    (¬ replaced (IndRepData.psiUseIh (cd j).dJ J)
        (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J) i ∧
      d.invUseIh p.k (auxOfsOf st p.k cd j J) i = false) ∨
    (d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (consList (paramVals d.nP ρ) ρ) j J
        (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs')).getD i pt
      = vs'.getD i pt := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hD := hf.ctor.2.2
  have hlen : vs'.length = cA.2 := by
    rw [hfit.length_eq, d.Fss_getD ψ hget, List.length_map, List.length_drop, hD.len ψ, hf.nF]; omega
  have hMlen : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').length = vs'.length := d.invMixed_length _ _ _ _ _ _ _ _ _ _
  intro i hi
  by_cases hA : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J)
  · have hAF : i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) := by
      obtain ⟨hks, -, -, -⟩ := hf.read.kindR i hA
      have hksLenA : (d.ksF (auxOfsOf st p.k cd j J)).length = cA'.2 := hf.ctor.2.2.ksLen
      exact mem_recIdxOf.mpr ⟨by rw [hksLenA, hf.nF]; exact hi,
        by rw [← hf.view.1, hks]; exact (mem_recIdxOf.mp hA).2⟩
    exact Or.inr (R.pos_inv_recJ tbl₀ hρ hbA hj hJ hi hA hfit (hIH i hAF) (hEntryFit i hAF))
  · by_cases hTr : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) ∧
        p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i
    · -- a transport, any telescope
      obtain ⟨hAr, hk⟩ := hTr
      exact Or.inr (R.pos_inv_transport' tbl₀ hbA hj hJ hi hA hAr
        (show d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + (d.tgtsR (auxOfsOf st p.k cd j J) i - p.k) by omega)
        hfit (hIH i (by rw [← hf.view.1]; exact hAr)) (hEntryFit i (by rw [← hf.view.1]; exact hAr)))
    · -- container-ordinary, no transport: ordinary on both sides
      have hvia : d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J i = none := by
        unfold IndRepData.psiVia
        rw [if_neg]
        rintro ⟨h1, -, h3⟩
        exact hTr ⟨h1, h3⟩
      refine Or.inl ⟨?_, ?_⟩
      · rintro (h | h)
        · unfold IndRepData.psiUseIh at h
          exact hA (of_decide_eq_true h)
        · rw [hvia] at h
          exact nomatch h
      · unfold IndRepData.invUseIh
        apply decide_eq_false
        rintro ⟨-, h2, h3⟩
        exact hTr ⟨h2, h3⟩

set_option maxHeartbeats 3200000 in
/-- **R1's STEP at the run, EVERY field shape** (`r1_hstep_refl` with
`fitMixed_full`, `pos_inv_full`): no restriction on the fields; the bit
nonzero. -/
theorem r1_hstep_full (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0)
    :
    ∀ tup, tup ∈ˢ d.idx ψ (consList (paramVals d.nP ρ) ρ) →
      ∀ (J' : Nat) (fs : List V), J' < d.ctorsA.length →
      d.ChainFit ψ (consList (paramVals d.nP ρ) ρ)
        (r1Fam d ψ ρ (consList (paramVals d.nP ρ) ρ) p.k
          (fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
          (fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t')) tup J' fs →
      R1Pred d ψ ρ (consList (paramVals d.nP ρ) ρ) p.k
        (fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
        (fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t')
        tup (d.inj ψ J' fs) := by
  have hbJ : ∀ j, j < st.pins.length → (cd j).dJ.bb (cd j).ψ' ≠ 0 :=
    fun j hj h => hbA ((R.bb_iff hj).mpr h)
  have hwA : d.w ψ ≠ 0 := fun h => hbA (R.bbA_iff.mpr h)
  intro tup htup J' fs hJ'lt hchain
  obtain ⟨cA', hJ'⟩ : ∃ cA', d.ctorsA[J']? = some cA' := ⟨_, List.getElem?_eq_getElem hJ'lt⟩
  obtain ⟨lpsI, lpsT', S⟩ := R.invSetup_at hρ
  have hsat₀ : Sat V (d.params ψ).reverse (consList (paramVals d.nP ρ) ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hρ
    rwa [List.append_nil] at h
  have hk : 0 < d.k := S.hk
  obtain ⟨hlen, hchainFit, hall⟩ := hchain
  have hX : r1Fam d ψ ρ (consList (paramVals d.nP ρ) ρ) p.k
      (fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
      (fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t')
      ∈ˢ famSpace (d.w ψ) (d.idx ψ (consList (paramVals d.nP ρ) ρ)) :=
    graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpFamSet_mem _ _ _) hi)
  have hmemJ' : d.mems J' < d.k := S.hmems J' hJ'lt
  obtain ⟨s', cvT', cvR', mI', rP', rules', hs', hrep'⟩ := R.repsAt_of_reps _ hmemJ'
  have hfields := IndRep.chainFit_fields_sorted hs' hrep' ψ hsat₀ hX htup hJ'lt ⟨hlen, hchainFit, hall⟩
  have hC := S.hctors J' cA' hJ'
  have hlenD' : (d.dsF J' ψ).length = d.nP + cA'.2 := hC.2.2.len ψ
  have hfacts := R.ctor_facts_aux hρ hJ'
  have hEntry := R.ctor_facts_aux' hρ hJ'
  have htgts : ∀ i, d.tgts J' i < d.k := S.htgts J'
  obtain ⟨hfit, hIH⟩ := fieldsFit_of_chainFit' (P := R1Pred d ψ ρ (consList (paramVals d.nP ρ) ρ) p.k
      (fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
      (fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t'))
    R.repsAt_of_reps hwA hsat₀ hρ (paramVals_length _ _) hJ' (R.sortEval ψ) hC htgts hEntry hlen hfields
  have hvsN : fs.length = cA'.2 := by
    rw [hlen, d.Fss_getD ψ hJ', List.length_map, List.length_drop, hlenD']; omega
  have hEsOk := (hfacts.1 fs hfit).1
  have hEsFit := (hfacts.1 fs hfit).2
  have hpreI : ∀ i, i ∈ ConLeche.recIdxOf (d.ksF J') →
      (fs.take i).length = i ∧
      SpineFit (consList (paramVals d.nP ρ) ρ) ((((d.dsF J' ψ).drop d.nP).map (·.2.2)).take i) (fs.take i) := by
    intro i hi
    have hksLen : (d.ksF J').length = cA'.2 := hC.2.2.ksLen
    have hilt : i < cA'.2 := by
      have := (mem_recIdxOf.mp hi).1
      rw [hksLen] at this
      exact this
    refine ⟨by rw [List.length_take]; omega, ?_⟩
    rw [← d.Fss_getD ψ hJ']
    exact spineFit_take' hfit (by rw [← hlen, hvsN]; omega)
  have hEntryFit : ∀ i, i ∈ ConLeche.recIdxOf (d.ksF J') → ∀ bs : List V,
      SpineFit (consList (fs.take i) (consList (paramVals d.nP ρ) ρ)) (((d.tssF J' ψ).getD i []).map (·.2.2)) bs →
      SpineFit (consList (paramVals d.nP ρ) ρ) (d.IdsM (d.tgts J' i) ψ)
        (((d.eissF J' ψ).getD i []).map (interp V (consList bs (consList (fs.take i) (consList (paramVals d.nP ρ) ρ))))) :=
    fun i hi bs hbs => (hEntry i hi (fs.take i) (hpreI i hi).1 (hpreI i hi).2 bs hbs).2
  by_cases hge : p.k ≤ d.mems J'
  · -- a copy constructor
    obtain ⟨j, Jc, cAJ, hj, hJc, hE⟩ := copyCtor_repr R.aux R.lenSt R.chk R.pins hJ' hge
    subst hE
    have hg := R.groupFacts hj
    obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
    obtain ⟨cA'', hget, hf⟩ := hg.ctors Jc cAJ hJc
    obtain rfl : cA'' = cA' := Option.some.inj (hget.symm.trans hJ')
    have hJcA : Jc < (cd j).dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJc).1
    have hmemJ : (cd j).dJ.mems Jc < (cd j).dJ.k := by
      have := (hrepJ.memsReal Jc (by unfold IndRepData.nAll; rw [hg.ctorsC]; simpa using hJcA)).mpr hJcA
      rw [hg.kReal] at this
      exact this
    have hDsLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := by
      rw [List.length_map, hg.len]
    have hvsN' : fs.length = cAJ.2 := by rw [hvsN, hf.nF]
    have hιΦ := fun (vs : List V)
        (hfitv : SpineFit ρ ((d.dsF (auxOfsOf st p.k cd j Jc) ψ).map (·.2.2)) (paramVals d.nP ρ ++ vs)) =>
      R.inv_iota hk hρ hbA hJ'
        (by have := hfitv.length_eq
            rw [List.length_append, paramVals_length, List.length_map, hlenD'] at this; omega)
        hfitv
    have hιΨ := fun (vs : List V)
        (hfitv : SpineFit (consList (paramVals d.nP ρ) ρ) (((cd j).dJ.dsF Jc (cd j).ψ').map (·.2.2))
          ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) ++ vs)) =>
      R.psi_iota tbl₀ hρ rfl hj (hbJ j hj) (fun _ => rfl) hJc
        (by have := hfitv.length_eq
            rw [List.length_append, hDsLen, List.length_map, (hrepJ.ctors Jc cAJ hJc).2.2.len (cd j).ψ'] at this
            omega)
        hfitv
    exact r1_step' mpAux.base2 (dJ := (cd j).dJ) (ψ' := (cd j).ψ') (cA := cAJ)
      (σ := consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (Ψ := fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (Ψ' := fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
      (Φ' := fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t')
      R.repsAt_of_reps hsat₀ rfl hρ hJ' hlenD' hf.pIff hf.read.mem hf.mem hmemJ
      (fun t _ => by
        show d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (p.k + (cd j).base + t - p.k)
          = d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t)
        rw [show p.k + (cd j).base + t - p.k = (cd j).base + t by omega])
      hfit hEsOk hEsFit hall hιΦ hιΨ rfl rfl
      (d.psiHead_interp mpAux.base2 ψ (auxOfsOf st p.k cd j) hJ' hDsLen)
      (R.headφ_of_run (ρ := ρ) hj hJc).headφ
      (R.fitMixed_full tbl₀ hρ hj hJc hbA hfit)
      (R.es_inv' tbl₀ hρ hj hJc hvsN')
      (fun i hi => R.pos_inv_full tbl₀ hρ hbA hj hJc hfit hIH hEntryFit i
        (by rw [← hf.nF]; exact hi))
  · -- a real member's constructor: the predicate speaks of copies
    intro t' hk₀ ht' is' his' htupE
    obtain ⟨s'', cvT'', cvR'', mI'', rP'', rules'', -, hrep''⟩ := R.repsAt_of_reps t' ht'
    rw [htupE] at hall
    have h := hrep''.idxRecover ψ (consList (paramVals d.nP ρ) ρ) hsat₀ is' his' _ J' fs hJ'lt hlen
      hEsOk hEsFit hall
    have hmem : d.mems J' = t' := h.1
    omega

/-- **R1 AT THE RUN, every field shape** (`r1At_of_run` with
`r1_hstep_full`); the bit nonzero (`hbA`). -/
theorem r1At_full (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0)
    {j : Nat} (hj : j < st.pins.length) {t : Nat} (ht : t < (cd j).dJ.k) :
    d.R1At mpAux.base2 ψ ρ (paramBvarsAt d.nP d.nP) (p.k + (cd j).base + t)
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  have hg := R.groupFacts hj
  have hlt : p.k + (cd j).base + t < d.k := hg.kA t ht
  obtain ⟨s', cvT', cvR', mI', rP', rules', hs', hrep'⟩ := R.repsAt_of_reps _ hlt
  have h := r1At_of_step mpAux.base2 (k₀ := p.k) (ps := paramBvarsAt d.nP d.nP)
    (Ψ' := fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
    (Φ' := fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t')
    hs' hrep' (Nat.le_add_right_of_le (Nat.le_add_right _ _)) hlt hρ
    (R.r1_hstep_full tbl₀ hρ hbA)
  rw [show p.k + (cd j).base + t - p.k = (cd j).base + t by omega] at h
  exact h

/-- **R1 AT THE RUN, at ANY bit, every field shape** — M-C′'s R1 with
no restriction on the fields. -/
theorem r1At_full_all (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
    {j : Nat} (hj : j < st.pins.length) {t : Nat} (ht : t < (cd j).dJ.k) :
    d.R1At mpAux.base2 ψ ρ (paramBvarsAt d.nP d.nP) (p.k + (cd j).base + t)
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  by_cases hb : d.bb ψ = 0
  · exact R.r1At_prop tbl₀ hρ hb hj ht
  · exact R.r1At_full tbl₀ hρ hb hj ht

end NestedRunFacts

end ConLeche.Model
