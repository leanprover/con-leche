module

public import ConLeche.Model.Inductives.RoundTripProp
public section

/-!
# The TRANSPORT arm of R2 (task #279 M-C′, DESIGN §M.38)

`RoundTripRun.lean` proves R2 at the run for groups WITHOUT transports
(`hnoT`): a field the container sees as ordinary and the copy as
recursive had to target a block member.  A TRANSPORT is such a field
targeting another COPY — an earlier pin along the kernel's order
(`CopyRef`, `TopoOrder`): at `J α := mk : List α → J α` copied at the
pin `J T`, the copy's field is the copy of `List T`.  ψ carries the
field's value through the earlier pin's term (`viaVal`, the
`psiVia` transport) and ψ⁻¹ through its fold at the target copy (a
hypothesis position, `invUseIh`); their composition at the position is
R2 at the EARLIER pin, so R2 is proved along the order.

This module, at a FINITARY scratch block (`hfinA`: a transport has no
telescope — the reflexive arm lifts it):

* **`psiVia_transport`** — the transport's specification at the final
  table, read off `psiVia`;
* **`psiVals_shadowRel`** — ψ's values shadow the fields off the copy's
  recursive positions (a replaced position is one);
* **`mixed_transport`** — THE POSITION: ψ⁻¹'s mixed value at a transport
  is the field, given R2 at the target pin (`containerDom_transport` +
  `transport_fits` place the field in the target pin's carrier at the
  copy's index readings; the readings read alike at ψ's frame and at
  ψ⁻¹'s);
* **`pos_transport`** — the per-position facts of `r2_step` with the
  third arm PROVED at transports;
* **`r2Grp_of_r2`** — R2 for pin `j`'s group from R2 at every pin it
  references;
* **`r2Grp_order`** — R2 at EVERY pin, by induction along the order.

Remaining restrictions: the containers finitary (`hfin`) and the
scratch block finitary (`hfinA`) — the reflexive arm.
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

/-! ## The transport's specification -/

omit R in
/-- **A transport's specification** at the final table: the target
copy's entry lifted over the pin's readings, the copy's index readings
lifted at the field's depth, the copy's telescope lifted and rebitted. -/
theorem psiVia_transport (tbl₀ : Nat → AnnotTerm) {j J i : Nat}
    (hT : i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J))
    (hA : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)))
    (hk : p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i) :
    d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J i
      = some ((d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
            (d.tgtsR (auxOfsOf st p.k cd j J) i - p.k)).liftN (cd j).dJ.nP 0,
          ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (·.liftN (cd j).dJ.nP (i + ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length)),
          rebit ((cd j).dJ.bb (cd j).ψ')
            (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []))) := by
  unfold IndRepData.psiVia
  rw [if_pos ⟨hA, hT, hk⟩]

/-- **A replaced position is a recursive position of the copy**: a
hypothesis position is container-recursive, hence copy-recursive
(`kindR`); a transport is copy-recursive by `psiVia`'s guard. -/
theorem replaced_recIdx (tbl₀ : Nat → AnnotTerm) {j : Nat} (hj : j < st.pins.length) {J : Nat}
    {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) {l : Nat}
    (hr : replaced (IndRepData.psiUseIh (cd j).dJ J)
      (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J) l) :
    l ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hksLenA : (d.ksR (auxOfsOf st p.k cd j J)).length = cA'.2 := by
    rw [hf.view.1]; exact hf.ctor.2.2.ksLen
  rcases hr with hu | hv
  · unfold IndRepData.psiUseIh at hu
    have hJr := of_decide_eq_true hu
    obtain ⟨hks, -, -, -⟩ := hf.read.kindR l hJr
    have hlt : l < cA.2 := by
      have := (mem_recIdxOf.mp hJr).1
      rw [(hrepJ.ctors J cA hJ).2.2.ksLen] at this
      exact this
    exact mem_recIdxOf.mpr ⟨by rw [hksLenA, hf.nF]; exact hlt, by rw [hks]; exact (mem_recIdxOf.mp hJr).2⟩
  · unfold IndRepData.psiVia at hv
    split at hv
    · rename_i hcond
      exact hcond.1
    · exact nomatch hv

/-- **ψ's values shadow the fields off the copy's recursive positions**
(`ShadowRel` at the copy's kinds, from `psiVals_shadowRelP` and
`replaced_recIdx`). -/
theorem psiVals_shadowRel (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V} {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) (fs : List V) :
    ShadowRel d.nP (d.ksR (auxOfsOf st p.k cd j J)) fs
      (d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (consList (paramVals d.nP ρ) ρ) j J fs) := by
  have hsh := psiVals_shadowRelP ((cd j).dJ.bb (cd j).ψ')
    (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
    (ConLeche.recIdxOf ((cd j).dJ.ksR J)) (IndRepData.psiUseIh (cd j).dJ J)
    (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J) fs
    ((ConLeche.recIdxOf ((cd j).dJ.ksR J)).map fun i =>
      lamTower ((cd j).dJ.bb (cd j).ψ')
        (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        (((cd j).dJ.tssR J (cd j).ψ').getD i []) fun σ'' =>
        ((((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V σ'') ++
          [(Semantics.frameIdx ((((cd j).dJ.tssR J (cd j).ψ').getD i []).length) σ'').foldl
            SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
          (interp V (consList (paramVals d.nP ρ) ρ) (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
            ((cd j).base + (cd j).dJ.tgtsR J i))))
  refine ⟨hsh.1, fun l hl hr => hsh.2 l hl fun hrep => hr ?_⟩
  have hmem := R.replaced_recIdx tbl₀ hj hJ hrep
  exact ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact (mem_recIdxOf.mp hmem).2⟩

/-! ## The position -/

set_option maxHeartbeats 3200000 in
/-- **ψ⁻¹'s mixed value at a TRANSPORT is the field** (task #279 M-C′,
the transport arm of R2): at pin `j`, container constructor `J`, a
position `i` the container sees as ordinary and the copy as recursive
into the copy of pin `j'` (`tgtsR = p.k + j'`), with the copy's field
finitary (`hfin'`), ψ's value is the target pin's term at the copy's
index readings and the field (`psiVia_transport`, `viaVal` at an empty
telescope, the lifts undone), ψ⁻¹'s mixed value is its fold at the
target copy at the same readings and that (`mixedVals` at a hypothesis
position; the readings read alike at the two frames: ψ's values shadow
the fields off the copy's recursive positions, which the readings do
not mention, `noBVar_entries`, and the pushed frame agrees with `ρ`
below the parameters), and the field lies in the target pin's carrier
at those readings (`containerDom_transport`, `transport_fits`), so R2
at the target pin (`hR2`) closes the position. -/
theorem mixed_transport (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    {i : Nat} (hi : i < cA.2) (hT : i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J))
    (hA : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)))
    {j' : Nat} (htgt : d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + j')
    (hfin' : (d.ksF (auxOfsOf st p.k cd j J)).getD i .ordinary = .recursive ∧
      (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = [])
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
  -- the telescope is empty, the kind recursive
  obtain ⟨hkind, htssF⟩ := hfin'
  have htssA : (d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [] = [] := by rw [hf.view.2.2.2]; exact htssF
  have heissA : d.eissR (auxOfsOf st p.k cd j J) ψ = d.eissF (auxOfsOf st p.k cd j J) ψ :=
    congrFun hf.view.2.2.1 ψ
  -- ψ's values
  obtain ⟨VS, hVS⟩ : ∃ VS, VS = d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
    (consList (paramVals d.nP ρ) ρ) j J fs := ⟨_, rfl⟩
  have hVSlen : VS.length = fs.length := by rw [hVS]; unfold IndRepData.psiValsAt; rw [psiVals_length]
  have hiVS : i < VS.length := by rw [hVSlen]; exact hifs
  have htakeV : (VS.take i).length = i := by rw [List.length_take]; omega
  have hsh : ShadowRel d.nP (d.ksR (auxOfsOf st p.k cd j J)) fs VS := by
    rw [hVS]; exact R.psiVals_shadowRel tbl₀ hj hJ fs
  -- ψ's value at the position: the target pin's term at the readings and the field
  have hvia := psiVia_transport (d := d) (mpAux := mpAux) (ψ := ψ) (cd := cd) (order := order) tbl₀ hT hA hk
  have hshiftΨ : shiftE (cd j).dJ.nP 0
      (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      = consList (paramVals d.nP ρ) ρ := by
    rw [← hDsLen]; exact shiftE_consList _ _
  have hVSi : VS.getD i pt
      = ((((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (interp V (consList (fs.take i) (consList (paramVals d.nP ρ) ρ)))) ++ [fs.getD i pt]).foldl
          SetTheory.app
          (interp V (consList (paramVals d.nP ρ) ρ)
            (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j')) := by
    rw [hVS]
    unfold IndRepData.psiValsAt
    rw [psiVals_getD _ _ _ _ _ _ _ hifs, hvia]
    simp only [htssA, liftDoms, rebit, List.map_nil, List.length_nil, Nat.add_zero, viaVal, lamTower,
      Semantics.frameIdx, List.range_zero, List.foldl_nil, htgt, Nat.add_sub_cancel_left]
    rw [interp_liftN, hshiftΨ, List.map_map, heissA]
    congr 2
    apply List.map_congr_left
    intro E _
    simp only [Function.comp_def]
    have hE : E.liftN (cd j).dJ.nP i
        = E.liftN ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length (fs.take i).length := by
      rw [hDsLen, htake]
    rw [hE, interp_liftN_middle]
  -- the copy's readings at ψ's frame are its readings at the fields' frame
  obtain ⟨-, -, hnbE, -⟩ := FixCtorDataI.noBVar_entries hD hf.cf hf.cb ψ
  have hread : ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V (consList (VS.take i) ρ))
      = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList (fs.take i) (consList (paramVals d.nP ρ) ρ))) := by
    apply List.map_congr_left
    intro E hE
    have hEb : Term.bvarsBelow (d.nP + i) E.erase := by
      have := hD.eissBelow ψ i E hE
      rwa [htssF, List.length_nil, Nat.add_zero] at this
    have h1 : interp V (consList (VS.take i) ρ) E
        = interp V (consList (VS.take i) (consList (paramVals d.nP ρ) ρ)) E := by
      refine interp_congr_below V E (d.nP + i) _ _ hEb ?_
      intro l hl
      exact (consList_agree_below (n := d.nP) (fun l' hl' => (push_agree ρ ρ l' hl').symm) (VS.take i) l
        (by rw [htakeV]; omega))
    have h2 := interp_congr_shadowRel (hsh.take i) (consList (paramVals d.nP ρ) ρ) [] (E := E)
      (by rw [htake, List.length_nil, Nat.add_zero]
          have hnb := hnbE i (by rw [hf.nF]; exact hi) E hE
          rw [htssF, List.length_nil, Nat.add_zero] at hnb
          refine NoBVar_mono ?_ _ hnb
          intro q hq
          obtain ⟨q', ⟨hr, hlt⟩, hq'⟩ := hq
          refine ⟨q', ⟨?_, hlt⟩, hq'⟩
          rw [hf.view.1] at hr
          exact hr)
    simp only [consList_nil] at h2
    rw [h1, ← h2]
  -- the mixed value at the position
  have huseA : d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true := by
    unfold IndRepData.invUseIh
    exact decide_eq_true ⟨by rw [hf.read.mem]; omega, hA, hk⟩
  have hMIXi : (d.mixedValsAt mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) order s tbl₀ ρ j J fs).getD i pt
      = ((((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (interp V (consList (fs.take i) (consList (paramVals d.nP ρ) ρ)))) ++ [VS.getD i pt]).foldl
          SetTheory.app
          (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j'))) := by
    unfold IndRepData.mixedValsAt
    rw [← hVS, mixedVals_getD _ _ _ _ hiVS, huseA]
    simp only [if_true]
    rw [getD_map_idxOf hA, htssA, htgt]
    simp only [lamTower, List.length_nil, Semantics.frameIdx, List.range_zero, List.map_nil,
      List.foldl_nil]
    rw [heissA, hread]
  -- the field lies in the target pin's carrier at the readings
  have hc' : CopyData.Ok mpAux.base2 d ψ p.k j' (cd j') := hg'.ok (R.pins j' hj').1.2.1
  have hfitPre : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (((((cd j).dJ.dsF J (cd j).ψ').drop (cd j).dJ.nP).take i).map (·.2.2)) (fs.take i) := by
    rw [List.map_take, ← (cd j).dJ.Fss_getD (cd j).ψ' hJ]
    exact spineFit_take' hfit (by rw [← hfit.length_eq, hfsN]; omega)
  obtain ⟨j'', hj''eq, -, hdom, hWD⟩ := d.containerDom_transport mpAux.base2 hg.len (auxOfsOf st p.k cd j) cd
    hf.read hlenDJ (by rw [hlenDA, hf.nF]) (by rw [hksLenA, hf.nF]) hsat₀ hi hT hA hk htake hfitPre
  obtain rfl : j' = j'' := by rw [htgt] at hj''eq; omega
  have hEl : ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).length = d.nIdxAt (p.k + j') := by
    rw [heissA, hD.eisLen ψ i hkind (by rw [hf.nF]; exact hi)]
    show d.nIdxAt (d.tgts (auxOfsOf st p.k cd j J) i) = _
    rw [← hf.view.2.1, htgt]
  obtain ⟨-, hbody, -, hisFit⟩ := d.transport_fits mpAux.base2 hc' hEl htake hWD (as := [])
    (by rw [htssA]; trivial)
  simp only [consList_nil, htssA, List.length_nil, Nat.add_zero] at hbody hisFit
  -- the field's membership in the container's domain at the position
  have hFeq : (((cd j).dJ.Fss (cd j).ψ').getD J [])[i]?
      = some (((cd j).dJ.dsF J (cd j).ψ').getD ((cd j).dJ.nP + i) default).2.2 := by
    rw [(cd j).dJ.Fss_getD (cd j).ψ' hJ, List.getElem?_map, List.getElem?_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenDJ]; omega)]
    rfl
  have hfi := spineFit_getElem? hfit i (fs.getD i pt) _
    (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hifs]; rfl) hFeq
  rw [hdom, htssA] at hfi
  simp only [mkPisAV, List.length_nil, Nat.add_zero] at hfi
  rw [hbody] at hfi
  -- R2 at the target pin
  have hR2' := hR2 _ (fs.getD i pt) (by rw [hσ₀]; rw [heissA] at hisFit; exact hisFit)
    (by rw [hσ₀]; rw [heissA] at hfi; exact hfi)
  rw [hσ₀] at hR2'
  unfold foldApp at hR2'
  rw [hMIXi, hVSi]
  exact hR2'

/-! ## The per-position facts, transports included -/

/-- **The per-position facts at a finitary container, TRANSPORTS
INCLUDED** (`r2_step`'s `hpos`): a container-recursive position by
`pos_recJ`; a container-ordinary position that is a transport
(copy-recursive into a copy) by `mixed_transport` — the THIRD arm,
given R2 at the target pin (`hR2`); any other container-ordinary
position is ordinary on ψ's side and passes its value on ψ⁻¹'s. -/
theorem pos_transport (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    (hfin : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hfinA : ∀ i, i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) →
      (d.ksF (auxOfsOf st p.k cd j J)).getD i .ordinary = .recursive ∧
      (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = [])
    (hR2 : ∀ j', j' < st.pins.length → ConLeche.CopyRef (ElimState.grp st) p.k st j j' →
      IndRepData.R2At mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j')
        (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j')))
    {fs : List V}
    (hfit : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (((cd j).dJ.Fss (cd j).ψ').getD J []) fs) :
    ∀ i, i < cA.2 →
    (¬ replaced (IndRepData.psiUseIh (cd j).dJ J)
        (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J) i ∧
      d.invUseIh p.k (auxOfsOf st p.k cd j J) i = false) ∨
    (IndRepData.psiUseIh (cd j).dJ J i = true ∧
      d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J i = none ∧
      d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true ∧
      i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) ∧ i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) ∧
      ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [] ∧ (d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [] = [] ∧
      d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + (cd j).base + (cd j).dJ.tgts J i ∧
      ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList ((d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
            (consList (paramVals d.nP ρ) ρ) j J fs).take i) ρ))
        = (((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList (fs.take i)
            (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))) ∨
    (d.mixedValsAt mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) order s tbl₀ ρ j J fs).getD i pt
      = fs.getD i pt := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hlen : fs.length = cA.2 := by
    rw [hfit.length_eq, (cd j).dJ.Fss_getD (cd j).ψ' hJ, List.length_map, List.length_drop,
      (hrepJ.ctors J cA hJ).2.2.len (cd j).ψ']
    omega
  intro i hi
  by_cases hA : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J)
  · exact Or.inr (Or.inl (R.pos_recJ tbl₀ hρ hj hJ hlen hi hA (hfin i hA)))
  · by_cases hTr : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) ∧
        p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i
    · -- a transport
      obtain ⟨hAr, hk⟩ := hTr
      have hj' : d.tgtsR (auxOfsOf st p.k cd j J) i - p.k < st.pins.length := R.transport_lt hj hJ i
      have href : ConLeche.CopyRef (ElimState.grp st) p.k st j (d.tgtsR (auxOfsOf st p.k cd j J) i - p.k) :=
        R.bridge j hj J cA hJ i hi hAr hA hk
      have hAF : i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) := by
        rw [← hf.view.1]; exact hAr
      exact Or.inr (Or.inr (R.mixed_transport tbl₀ hρ hj hJ hi hA hAr
        (show d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + (d.tgtsR (auxOfsOf st p.k cd j J) i - p.k) by omega)
        (hfinA i hAF) (hR2 _ hj' href) hfit))
    · -- ordinary on the container's side, no transport
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

/-! ## R2 along the order -/

set_option maxHeartbeats 3200000 in
/-- **R2 for pin `j`'s group from R2 at the pins it references** (task
#279 M-C′, the transport arm): `r2Grp_of_owed`'s assembly with
`pos_transport` in place of `pos_noTransport` — for a FINITARY
container (`hfin`) and a FINITARY scratch block (`hfinA`), the bits
nonzero. -/
theorem r2Grp_of_r2 (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    (hbA : d.bb ψ ≠ 0)
    (hfin : ∀ J, ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hfinA : ∀ J' i, i ∈ ConLeche.recIdxOf (d.ksF J') →
      (d.ksF J').getD i .ordinary = .recursive ∧ (d.tssF J' ψ).getD i [] = [])
    (hR2 : ∀ j', j' < st.pins.length → ConLeche.CopyRef (ElimState.grp st) p.k st j j' →
      IndRepData.R2At mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j')
        (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j'))) :
    R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
      (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  have hbJ : (cd j).dJ.bb (cd j).ψ' ≠ 0 := fun h => hbA ((R.bb_iff hj).mpr h)
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
  obtain ⟨hfit, hIH⟩ := fieldsFit_of_chainFit (IndRepData.RepsAt.of_single hrepT) hsat rfl hDsFit hDsLen hJ hC
    htgts (hfin J)
    (fun i hi => hfacts.2 i (hfin J i hi).1) hlen hfields
  have hvsN : fs.length = cA.2 := by
    rw [hlen, (cd j).dJ.Fss_getD (cd j).ψ' hJ, List.length_map, List.length_drop, hlenD]; omega
  have hEntryFit : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        ((cd j).dJ.IdsM ((cd j).dJ.tgts J i) (cd j).ψ')
        ((((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList (fs.take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))) := by
    intro i hi
    have hilt : i < cA.2 := by
      have := (mem_recIdxOf.mp hi).1
      rw [hC.2.2.ksLen] at this
      exact this
    have htake : (fs.take i).length = i := by rw [List.length_take]; omega
    have hpre : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
        (consList (paramVals d.nP ρ) ρ))
        (((((cd j).dJ.dsF J (cd j).ψ').drop (cd j).dJ.nP).map (·.2.2)).take i) (fs.take i) := by
      rw [← (cd j).dJ.Fss_getD (cd j).ψ' hJ]
      exact spineFit_take' hfit (by rw [← hlen, hvsN]; omega)
    exact (hfacts.2 i (hfin J i hi).1 (fs.take i) htake hpre).2
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
  exact r2_step mpAux.base2 (d := d) (ψ := ψ) (cA' := cA') hrepT hsat rfl hDsFit hDsLen hJ hlenD
    (hrepJ.paramsIff J cA hJ (cd j).ψ') hmemJ htgts (hg.view J) hf.read.mem (fun t _ => rfl) hfit hIH
    (hfacts.1 fs hfit).1 (hfacts.1 fs hfit).2 hEntryFit hall hιΨ hιΦ rfl rfl
    (d.psiHead_interp mpAux.base2 ψ (auxOfsOf st p.k cd j) hget hDsLen) (R.headφ_of_run hj hJ).headφ
    (R.fitCopy_of_run tbl₀ hρ hj hJ hfit)
    (R.es_of_record tbl₀ hρ hj hJ hvsN)
    (R.pos_transport tbl₀ hρ hj hJ (hfin J) (hfinA (auxOfsOf st p.k cd j J)) hR2 hfit)

/-- **R2 at a pin from R2 for its group**: pin `j'` is member `mm` of
its own group (`base + mm = j'`). -/
theorem r2At_of_grp (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V} {j' : Nat} (hj' : j' < st.pins.length)
    (h : R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j')
      (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j').base + t))
      (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j').base + t))) :
    IndRepData.R2At mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j')
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j')
      (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + j')) := by
  have hbm : (cd j').base + (cd j').mm = j' := (R.pins j' hj').1.2.1
  have hmm : (cd j').mm < (cd j').dJ.k := (R.groupFacts hj').mm
  have h' : IndRepData.R2At mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j')
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j').base + (cd j').mm))
      (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j').base + (cd j').mm)) :=
    h (cd j').mm hmm
  rw [Nat.add_assoc, hbm] at h'
  exact h'

/-- **R2 AT EVERY PIN, along the order** (task #279 M-C′, the transport
arm): by induction on the position in the kernel's topological order,
a pin's transports target pins earlier in the order
(`TopoOrder.lt_of_ref` through the bridge), so `r2Grp_of_r2` applies.
Restrictions: every container finitary (`hfin`), the scratch block
finitary (`hfinA`), the bit nonzero (`hbA`). -/
theorem r2Grp_order (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0)
    (hfin : ∀ j, j < st.pins.length → ∀ J i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hfinA : ∀ J' i, i ∈ ConLeche.recIdxOf (d.ksF J') →
      (d.ksF J').getD i .ordinary = .recursive ∧ (d.tssF J' ψ).getD i [] = []) :
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
      refine R.r2Grp_of_r2 tbl₀ hρ hj hbA (hfin j hj) hfinA fun j' hj' href => ?_
      obtain ⟨-, hlt⟩ := R.ord.lt_of_ref j j' href
      exact R.r2At_of_grp tbl₀ hj' (ih j' hj' (by omega))
  intro j hj
  exact key order.length j hj (List.idxOf_lt_length_of_mem (R.ord.complete j hj))

/-- **R2 at every pin, at ANY elimination bit**: the nonzero arm along
the order (`r2Grp_order`) or the `Prop` arm (`r2Grp_prop`).  Remaining
restrictions: the containers and the scratch block finitary. -/
theorem r2Grp_order_all (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
    (hfin : ∀ j, j < st.pins.length → ∀ J i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hfinA : ∀ J' i, i ∈ ConLeche.recIdxOf (d.ksF J') →
      (d.ksF J').getD i .ordinary = .recursive ∧ (d.tssF J' ψ).getD i [] = []) :
    ∀ j, j < st.pins.length →
      R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
        (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
        (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  intro j hj
  by_cases hb : d.bb ψ = 0
  · exact R.r2Grp_prop tbl₀ hρ hj hb
  · exact R.r2Grp_order tbl₀ hρ hb hfin hfinA j hj

end NestedRunFacts

end ConLeche.Model
