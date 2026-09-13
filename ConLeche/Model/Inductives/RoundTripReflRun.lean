module

public import ConLeche.Model.Inductives.RoundTripRefl
public section

/-!
# The REFLEXIVE arm at the run: R2 with telescoped container fields (task #279 M-C′, DESIGN §M.39)

`RoundTripRefl.lean` generalised the datum-level pieces.  This module
lifts `hfin` (the containers' recursive fields finitary) from R2 at
the run:

* **`ctor_facts'`** — a container constructor's recursive entries are
  graded and fit the target's telescope UNDER the field's telescope
  (`recEntry`/`reflEntry`, `wellDenoted_mkPisAV_dom` then `_body`,
  `idxFit_of_entry` at the telescope's depth);
* **`mixed_recJ`** — THE POSITION: at a container-recursive position
  with a telescope, ψ⁻¹'s mixed value is the field: the mixed value is
  a λ-tower over the copy's telescope (the container's instantiated,
  `kindR`) whose leaves are ψ⁻¹'s fold at the target of ψ's fold at
  the target of the field's application — the round trip inside,
  pointwise (`fieldsFit_of_chainFit'`'s induction hypothesis) — so it
  is the tower of the field's applications, which is the field by η
  (`piTele_eta`; the two towers compared by `lamTower_congr_tele`, the
  copy's telescope and readings read as the container's through
  `interp_instSeq_under`, the shadows and the pushed frame);
* **`pos_refl`** — `r2_step'`'s per-position facts: a container-recursive
  position by `mixed_recJ`, a transport by `mixed_transport` (still
  finitary, `hfinT`), any other ordinary on both sides;
* **`r2Grp_refl`/`r2Grp_order_refl`/`r2Grp_order_refl_all`** — R2 at
  the run with `hfin` gone.
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

/-! ## The entries under their telescopes -/

set_option maxHeartbeats 1600000 in
/-- **A container constructor's recursive entries, graded and fitting
under the telescope** (`ctor_facts`'s second half at any recursive
position): at a recursive position and any fitting prefix and
telescope spine, the entry's readings are graded and fit the target's
telescope. -/
theorem ctor_facts' (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) :
    ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) → ∀ ws : List V, ws.length = i →
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        (((((cd j).dJ.dsF J (cd j).ψ').drop (cd j).dJ.nP).map (·.2.2)).take i) ws →
      ∀ bs : List V,
        SpineFit (consList ws (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
          ((((cd j).dJ.tssF J (cd j).ψ').getD i []).map (·.2.2)) bs →
        (∀ E ∈ ((cd j).dJ.eissF J (cd j).ψ').getD i [],
          WellDenoted V (consList bs (consList ws (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
            (consList (paramVals d.nP ρ) ρ)))) E) ∧
        SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
          ((cd j).dJ.IdsM ((cd j).dJ.tgts J i) (cd j).ψ')
          ((((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList bs (consList ws
            (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))))) := by
  obtain ⟨lps, S⟩ := R.psiSetup_final (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) (paramBvarsAt_length _ _) hρ
    tbl₀ hj
  have hg := R.groupFacts hj
  have hC := S.hctors J cA hJ
  have hD := hC.2.2
  have hlenD : ((cd j).dJ.dsF J (cd j).ψ').length = (cd j).dJ.nP + cA.2 := hD.len (cd j).ψ'
  have hDsLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := by
    rw [List.length_map, hg.len]
  have hDsFit := R.pinFit hj hρ
  have hfitP : SpineFit (consList (paramVals d.nP ρ) ρ) ((((cd j).dJ.dsF J (cd j).ψ').take (cd j).dJ.nP).map (·.2.2))
      ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) :=
    spineFit_of_paramsIff hDsLen (by rw [List.length_map, List.length_take, hlenD]; omega) hDsFit
      (S.hpIff J cA hJ)
  intro i hi ws hws hpre bs hbs
  obtain ⟨hklt, hkind⟩ := mem_recIdxOf.mp hi
  have hilt : i < cA.2 := by rw [← hD.ksLen]; exact hklt
  -- the entry's shape and its readings' count, at both kinds
  have hentry : (((cd j).dJ.dsF J (cd j).ψ').getD ((cd j).dJ.nP + i) default).2.2
      = mkPisAV (((cd j).dJ.tssF J (cd j).ψ').getD i [])
          (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName ((cd j).dJ.tgts J i)) (cd j).ψ')
            (paramBvarsAt (cd j).dJ.nP ((cd j).dJ.nP + i + (((cd j).dJ.tssF J (cd j).ψ').getD i []).length) ++
              ((cd j).dJ.eissF J (cd j).ψ').getD i [])) ∧
      (((cd j).dJ.eissF J (cd j).ψ').getD i []).length = (cd j).dJ.nIdxAt ((cd j).dJ.tgts J i) := by
    rcases hkind with hk | hk
    · have htl : ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [] := hD.tssNone (cd j).ψ' i (by rw [hk]; decide)
      refine ⟨?_, hD.eisLen (cd j).ψ' i hk hilt⟩
      rw [hD.recEntry (cd j).ψ' i hk hilt, htl, List.length_nil, Nat.add_zero]
      rfl
    · exact ⟨hD.reflEntry (cd j).ψ' i hk hilt, hD.eisLenRefl (cd j).ψ' i hk hilt⟩
  obtain ⟨hentry, hEl⟩ := hentry
  have hlt2 : (cd j).dJ.nP + i < ((cd j).dJ.dsF J (cd j).ψ').length := by rw [hlenD]; omega
  have hentryE : ((cd j).dJ.dsF J (cd j).ψ')[(cd j).dJ.nP + i]?
      = some (((cd j).dJ.dsF J (cd j).ψ').getD ((cd j).dJ.nP + i) default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2]; rfl
  have hfitPre : SpineFit (consList (paramVals d.nP ρ) ρ)
      ((((cd j).dJ.dsF J (cd j).ψ').take ((cd j).dJ.nP + i)).map (·.2.2))
      ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) ++ ws) := by
    rw [List.take_add, List.map_append]
    refine hfitP.append ?_
    rw [List.map_take]
    exact hpre
  have hok := wellDenoted_mkPisAV_dom (hD.okTy (cd j).ψ' (consList (paramVals d.nP ρ) ρ)).1 _ _ _ hentryE hfitPre
  rw [consList_append, hentry] at hok
  have hokB := wellDenoted_mkPisAV_body hok bs hbs
  refine ⟨fun E hE => wellDenoted_mkAppN_args hokB E (List.mem_append_right _ hE), ?_⟩
  have hbsLen : bs.length = (((cd j).dJ.tssF J (cd j).ψ').getD i []).length := by
    rw [hbs.length_eq, List.length_map]
  have hfr : consList bs (consList ws (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
        (consList (paramVals d.nP ρ) ρ)))
      = consList (ws ++ bs) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
        (consList (paramVals d.nP ρ) ρ)) := (consList_append _ _ _).symm
  rw [hfr] at hokB ⊢
  rw [Nat.add_assoc] at hokB
  exact (cd j).dJ.idxFit_of_entry (ρ₀ := consList (paramVals d.nP ρ) ρ) (psA := (cd j).DsA) S.hps
    (S.hFF _ (S.htgts J i)) (S.hLS _ (S.htgts J i))
    (by rw [List.length_append, hws, hbsLen]) hokB hEl

/-! ## The position -/

set_option maxHeartbeats 6400000 in
/-- **ψ⁻¹'s mixed value at a container-recursive position is the field,
telescopes included** (task #279 M-C′, the reflexive arm of R2): the
mixed value is a λ-tower over the copy's telescope whose leaf at `bs`
is ψ⁻¹'s fold at the target applied to the copy's readings and ψ's
value applied to `bs` — ψ's value being a λ-tower over the container's
telescope whose leaf is ψ's fold at the target applied to the
container's readings and the field applied to `bs`; the copy's
telescope and readings are the container's instantiated at the pin
(`kindR`), read alike at the two frames (`interp_instSeq_under`, the
shadows off the replaced positions, the pushed frame); the induction
hypothesis pointwise (`hIH`) collapses the leaf to the field's
application, and η (`piTele_eta` on the slot) collapses the tower to
the field. -/
theorem mixed_recJ (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    {i : Nat} (hi : i < cA.2) (hA : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J))
    {fs : List V} (hlen : fs.length = cA.2) {X : V}
    (hslot : fs.getD i pt ∈ˢ slotSet ((cd j).dJ.w (cd j).ψ') ((cd j).dJ.u (cd j).ψ')
      (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
      ((((cd j).dJ.tlss (cd j).ψ').getD J []).getD i []) ((((cd j).dJ.Eiss (cd j).ψ').getD J []).getD i []) X)
    (hIH : ∀ bs : List V,
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
    (hEntryFit : ∀ bs : List V,
      SpineFit (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        ((((cd j).dJ.tssF J (cd j).ψ').getD i []).map (·.2.2)) bs →
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        ((cd j).dJ.IdsM ((cd j).dJ.tgts J i) (cd j).ψ')
        ((((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList bs (consList (fs.take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))))) :
    (d.mixedValsAt mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) order s tbl₀ ρ j J fs).getD i pt
      = fs.getD i pt := by
  obtain ⟨lps, S⟩ := R.psiSetup_final (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) (paramBvarsAt_length _ _) hρ
    tbl₀ hj
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hD := hf.ctor.2.2
  obtain ⟨hnbT, hnbE, -, -⟩ := S.hnbP J cA hJ _ _ _ _ _ _ _ ((cd j).dJ.cdsR_getElem?_of hg.ctorsC hJ)
  -- the bits
  have hw : (cd j).dJ.w (cd j).ψ' ≠ 0 := by
    rw [R.wJ_eq hj]; exact fun h => hbA (R.bbA_iff.mpr h)
  have hbJ : (cd j).dJ.bb (cd j).ψ' ≠ 0 := fun h => hbA ((R.bb_iff hj).mpr h)
  have hz : d.bb ψ = 0 ↔ (cd j).dJ.w (cd j).ψ' = 0 := by rw [R.bbA_iff, R.wJ_eq hj]
  -- the copy's field: the container's instantiated
  obtain ⟨hks, htgt, htss, heiss⟩ := hf.read.kindR i hA
  have hksLenA : (d.ksR (auxOfsOf st p.k cd j J)).length = cA'.2 := by
    rw [hf.view.1]; exact hf.ctor.2.2.ksLen
  have hkindJ := (mem_recIdxOf.mp hA).2
  have hrecA : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) :=
    mem_recIdxOf.mpr ⟨by rw [hksLenA, hf.nF]; exact hi, by rw [hks]; exact hkindJ⟩
  have hrJR : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksR J) := by rw [(hg.view J).1]; exact hA
  have huse : IndRepData.psiUseIh (cd j).dJ J i = true := by
    unfold IndRepData.psiUseIh; exact decide_eq_true hA
  have huseA : d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true := by
    unfold IndRepData.invUseIh
    exact decide_eq_true ⟨by rw [hf.read.mem]; omega, hrecA, by rw [htgt]; omega⟩
  have hvia : d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J i = none := by
    unfold IndRepData.psiVia
    rw [if_neg]
    intro h
    exact h.2.1 hA
  have htgts : (cd j).dJ.tgts J i < (cd j).dJ.k := by
    have := hrepJ.tgtsRLt J i
    rw [(hg.view J).2.1] at this
    exact this
  have htgtE : d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + (cd j).base + (cd j).dJ.tgts J i := htgt
  -- the lengths and frames
  have hifs : i < fs.length := by rw [hlen]; exact hi
  have htake : (fs.take i).length = i := by rw [List.length_take]; omega
  obtain ⟨VS, hVS⟩ : ∃ VS, VS = d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
    (consList (paramVals d.nP ρ) ρ) j J fs := ⟨_, rfl⟩
  have hVSlen : VS.length = fs.length := by rw [hVS]; unfold IndRepData.psiValsAt; rw [psiVals_length]
  have hiVS : i < VS.length := by rw [hVSlen]; exact hifs
  have htakeV : (VS.take i).length = i := by rw [List.length_take]; omega
  have hDsLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := by
    rw [List.length_map, hg.len]
  have hsh : ShadowRelP (replaced (IndRepData.psiUseIh (cd j).dJ J)
      (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J)) fs VS := by
    rw [hVS]; unfold IndRepData.psiValsAt; exact psiVals_shadowRelP _ _ _ _ _ _ _
  have hlenT : ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length
      = (((cd j).dJ.tssF J (cd j).ψ').getD i []).length := by
    rw [htss, instSeqDoms_length]
  have hpush : ∀ (as : List V) (n : Nat), n < as.length + i + d.nP →
      consList as (consList (VS.take i) ρ) n = consList as (consList (VS.take i) (consList (paramVals d.nP ρ) ρ)) n :=
    fun as n hn => consList_agree_below (n := i + d.nP)
      (fun l' hl' => consList_agree_below (n := d.nP) (fun l'' hl'' => (push_agree ρ ρ l'' hl'').symm) (VS.take i) l'
        (by rw [htakeV]; omega)) as n (by omega)
  have hDsNe : ∀ (as : List V), (cd j).DsA ≠ [] →
      (cd j).DsA.length + (VS.take i ++ as).length = (cd j).dJ.nP + i - 1 + as.length + 1 := by
    intro as hne
    have hpos : 0 < (cd j).DsA.length := List.length_pos_iff.mpr hne
    rw [hg.len] at hpos
    rw [hg.len, List.length_append, htakeV]; omega
  -- ψ's value at the position: a tower over the container's telescope
  have hVSi : VS.getD i pt
      = lamTower ((cd j).dJ.bb (cd j).ψ')
          (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
          (((cd j).dJ.tssF J (cd j).ψ').getD i []) fun σ'' =>
          ((((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx ((((cd j).dJ.tssF J (cd j).ψ').getD i []).length) σ'').foldl
              SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
            (interp V (consList (paramVals d.nP ρ) ρ)
              (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + (cd j).dJ.tgts J i))) := by
    rw [hVS]
    unfold IndRepData.psiValsAt
    rw [psiVals_getD _ _ _ _ _ _ _ hifs, hvia]
    simp only [huse, if_true]
    rw [getD_map_idxOf hrJR, (hg.view J).2.2.2, (hg.view J).2.2.1, (hg.view J).2.1]
  -- ψ⁻¹'s mixed value at the position: a tower over the copy's telescope
  have hMIXi : (d.mixedValsAt mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) order s tbl₀ ρ j J fs).getD i pt
      = lamTower (d.bb ψ) (consList (VS.take i) ρ) ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []) fun σ'' =>
          (((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length) σ'').foldl
              SetTheory.app (VS.getD i pt)]).foldl SetTheory.app
            (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
              (d.tgtsR (auxOfsOf st p.k cd j J) i))) := by
    unfold IndRepData.mixedValsAt
    rw [← hVS, mixedVals_getD _ _ _ _ hiVS, huseA]
    simp only [if_true]
    rw [getD_map_idxOf hrecA]
  -- η on the field: the tower of its applications
  have hslot' : fs.getD i pt ∈ˢ piTele ((cd j).dJ.w (cd j).ψ')
      (teleOfFields (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        ((((cd j).dJ.tssF J (cd j).ψ').getD i []).map (·.2.2)))
      (fun bs => SetTheory.app X (tupW ((cd j).dJ.u (cd j).ψ')
        (((((cd j).dJ.Eiss (cd j).ψ').getD J []).getD i []).map (interp V (consList bs
          (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))))))) [] := by
    rw [(cd j).dJ.tlss_getD (cd j).ψ' hJ] at hslot
    exact hslot
  have heta := piTele_eta hw hslot'
  rw [hMIXi, ← heta, lamTower_bit_agree hz]
  -- the copy's telescope reads as the container's
  have hdom : ∀ (k : Nat) (dA dJ' : Nat × Nat × AnnotTerm) (as : List V),
      ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [])[k]? = some dA →
      (((cd j).dJ.tssF J (cd j).ψ').getD i [])[k]? = some dJ' →
      SpineFit (consList (VS.take i) ρ) ((((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).take k).map (·.2.2)) as →
      interp V (consList as (consList (VS.take i) ρ)) dA.2.2
        = interp V (consList as (consList (fs.take i)
            (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))) dJ'.2.2 := by
    intro k dA dJ' as hkA hkJ has
    have hkA' : ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [])[k]?
        = some (dJ'.1, dJ'.2.1, ConLeche.Model.AnnotTerm.instSeq (cd j).DsA ((cd j).dJ.nP + i - 1 + k) dJ'.2.2) := by
      rw [htss, instSeqDoms_getElem?, hkJ]; rfl
    obtain rfl : dA = (dJ'.1, dJ'.2.1, ConLeche.Model.AnnotTerm.instSeq (cd j).DsA ((cd j).dJ.nP + i - 1 + k) dJ'.2.2) :=
      Option.some.inj (hkA.symm.trans hkA')
    have hklt : k < ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length := (List.getElem?_eq_some_iff.mp hkA).1
    have hasLen : as.length = k := by
      rw [has.length_eq, List.length_map, List.length_take]; omega
    show interp V (consList as (consList (VS.take i) ρ))
        (ConLeche.Model.AnnotTerm.instSeq (cd j).DsA ((cd j).dJ.nP + i - 1 + k) dJ'.2.2) = _
    have hbelow : Term.bvarsBelow (d.nP + i + k)
        (ConLeche.Model.AnnotTerm.instSeq (cd j).DsA ((cd j).dJ.nP + i - 1 + k) dJ'.2.2).erase := by
      have := domsBelow_getElem? (hD.tssBelow ψ i) (by rw [← hf.view.2.2.2]; exact hkA)
      exact this
    rw [interp_congr_below V _ (d.nP + i + k) _ (consList as (consList (VS.take i) (consList (paramVals d.nP ρ) ρ)))
      hbelow (fun l hl => hpush as l (by rw [hasLen]; omega)),
      show consList as (consList (VS.take i) (consList (paramVals d.nP ρ) ρ))
        = consList (VS.take i ++ as) (consList (paramVals d.nP ρ) ρ) from (consList_append _ _ _).symm,
      interp_instSeq_under (consList (paramVals d.nP ρ) ρ) (cd j).DsA (VS.take i ++ as) _ _
        (fun hne => by rw [hDsNe as hne, hasLen]),
      consList_append]
    have hnb : NoBVar (exclP (replP (cd j).dJ.nP (replaced (IndRepData.psiUseIh (cd j).dJ J)
        (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J)) (fs.take i).length)
        ((cd j).dJ.nP + (fs.take i).length + as.length)) dJ'.2.2 := by
      rw [htake, hasLen]
      exact hnbT i hi k dJ' (by rw [(S.hview J).2.2.2]; exact hkJ)
    exact (interp_congr_shadowRelP (hsh.take i) _ as hnb).symm
  refine lamTower_congr_tele hlenT hdom ?_
  intro bs hbs
  have hbsJ : SpineFit (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
      ((((cd j).dJ.tssF J (cd j).ψ').getD i []).map (·.2.2)) bs :=
    (spineFit_congr_tele hlenT hdom bs).mp hbs
  have hbsLen : bs.length = (((cd j).dJ.tssF J (cd j).ψ').getD i []).length := by
    rw [hbsJ.length_eq, List.length_map]
  have hbsLenA : bs.length = ((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length := by rw [hbsLen, hlenT]
  have hfrA : Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length)
      (consList bs (consList (VS.take i) ρ)) = bs := by
    rw [← hbsLenA]; exact frameIdx_consList' _ _
  have hfrJ : Semantics.frameIdx ((((cd j).dJ.tssF J (cd j).ψ').getD i []).length)
      (consList bs (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
      = bs := by
    rw [← hbsLen]; exact frameIdx_consList' _ _
  -- ψ's value applied: ψ's fold at the target of the field's application
  have hfold : bs.foldl SetTheory.app (VS.getD i pt)
      = ((((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList bs (consList (fs.take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))) ++
          [bs.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
          (interp V (consList (paramVals d.nP ρ) ρ)
            (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + (cd j).dJ.tgts J i))) := by
    rw [hVSi, lamTower_fold hbJ hbsJ, hfrJ]
  -- the copy's readings under `bs` are the container's
  have hread : ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V (consList bs (consList (VS.take i) ρ)))
      = (((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList bs (consList (fs.take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))) := by
    rw [heiss, List.map_map]
    apply List.map_congr_left
    intro E hE
    simp only [Function.comp_def]
    have hEb : Term.bvarsBelow (d.nP + i + bs.length)
        (ConLeche.Model.AnnotTerm.instSeq (cd j).DsA ((cd j).dJ.nP + i + (((cd j).dJ.tssF J (cd j).ψ').getD i []).length - 1) E).erase := by
      have := hD.eissBelow ψ i _ (by
        rw [← congrFun hf.view.2.2.1 ψ, heiss]
        exact List.mem_map_of_mem hE)
      rw [← congrFun hf.view.2.2.2 ψ, hlenT] at this
      rw [hbsLen]
      exact this
    rw [interp_congr_below V _ (d.nP + i + bs.length) _
        (consList bs (consList (VS.take i) (consList (paramVals d.nP ρ) ρ))) hEb
        (fun l hl => hpush bs l (by omega)),
      show consList bs (consList (VS.take i) (consList (paramVals d.nP ρ) ρ))
        = consList (VS.take i ++ bs) (consList (paramVals d.nP ρ) ρ) from (consList_append _ _ _).symm,
      interp_instSeq_under (consList (paramVals d.nP ρ) ρ) (cd j).DsA (VS.take i ++ bs) _ _
        (fun hne => by
          have hpos := List.length_pos_iff.mpr hne
          rw [hg.len] at hpos
          rw [hDsNe bs hne, hbsLen]; omega),
      consList_append]
    have hnb : NoBVar (exclP (replP (cd j).dJ.nP (replaced (IndRepData.psiUseIh (cd j).dJ J)
        (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J)) (fs.take i).length)
        ((cd j).dJ.nP + (fs.take i).length + bs.length)) E := by
      rw [htake, hbsLen]
      have := hnbE i hi E (by rw [(S.hview J).2.2.1]; exact hE)
      rwa [(S.hview J).2.2.2] at this
    exact (interp_congr_shadowRelP (hsh.take i) _ bs hnb).symm
  show ((((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V (consList bs (consList (VS.take i) ρ)))) ++
      [(Semantics.frameIdx (((d.tssR (auxOfsOf st p.k cd j J) ψ).getD i []).length)
        (consList bs (consList (VS.take i) ρ))).foldl SetTheory.app (VS.getD i pt)]).foldl SetTheory.app
      (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
        (d.tgtsR (auxOfsOf st p.k cd j J) i)))
    = (Semantics.frameIdx ((((cd j).dJ.tssF J (cd j).ψ').getD i []).length)
        (consList bs (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
          (consList (paramVals d.nP ρ) ρ))))).foldl SetTheory.app (fs.getD i pt)
  rw [hfrA, hfrJ, hfold, hread, htgtE]
  -- the round trip inside, at the leaf
  have h := hIH bs hbsJ ((cd j).dJ.tgts J i) htgts _ (hEntryFit bs hbsJ) rfl
  unfold foldApp at h
  exact h

/-! ## The per-position facts and the assembly -/

set_option maxHeartbeats 3200000 in
/-- **The per-position facts of `r2_step'`, telescopes included**: a
container-recursive position by `mixed_recJ` (the pointwise induction
hypothesis), a transport by `mixed_transport` (finitary, `hfinT`), any
other position ordinary on both sides. -/
theorem pos_refl (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    (hfinT : ∀ i, i < cA.2 → i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) → p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i →
      (d.ksF (auxOfsOf st p.k cd j J)).getD i .ordinary = .recursive ∧
      (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = [])
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
      exact Or.inr (R.mixed_transport tbl₀ hρ hj hJ hi hA hAr
        (show d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + (d.tgtsR (auxOfsOf st p.k cd j J) i - p.k) by omega)
        (hfinT i hi hA hAr hk) (hR2 _ hj' href) hfit)
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
/-- **R2 for pin `j`'s group, telescoped container fields included**
(`r2Grp_of_r2` with `fieldsFit_of_chainFit'`, `r2_step'` and
`pos_refl`): the containers' recursive fields may be reflexive; the
transports are still finitary (`hfinT`); the bit nonzero. -/
theorem r2Grp_refl (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    (hbA : d.bb ψ ≠ 0)
    (hfinT : ∀ J cA, (cd j).dJ.ctorsA[J]? = some cA → ∀ i, i < cA.2 →
      i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) → i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) →
      p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i →
      (d.ksF (auxOfsOf st p.k cd j J)).getD i .ordinary = .recursive ∧
      (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = [])
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
    (R.pos_refl tbl₀ hρ hbA hj hJ (hfinT J cA hJ) hR2 hfit hslot hIH hEntryFit)

/-- **R2 AT EVERY PIN along the order, telescoped container fields
included** (`r2Grp_order` with `r2Grp_refl`). -/
theorem r2Grp_order_refl (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0)
    (hfinT : ∀ j, j < st.pins.length → ∀ J cA, (cd j).dJ.ctorsA[J]? = some cA → ∀ i, i < cA.2 →
      i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) → i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) →
      p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i →
      (d.ksF (auxOfsOf st p.k cd j J)).getD i .ordinary = .recursive ∧
      (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = []) :
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
      refine R.r2Grp_refl tbl₀ hρ hj hbA (hfinT j hj) fun j' hj' href => ?_
      obtain ⟨-, hlt⟩ := R.ord.lt_of_ref j j' href
      exact R.r2At_of_grp tbl₀ hj' (ih j' hj' (by omega))
  intro j hj
  exact key order.length j hj (List.idxOf_lt_length_of_mem (R.ord.complete j hj))

/-- **R2 at every pin, telescoped container fields included, at ANY
bit** — the remaining restriction: the transports finitary (`hfinT`). -/
theorem r2Grp_order_refl_all (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
    (hfinT : ∀ j, j < st.pins.length → ∀ J cA, (cd j).dJ.ctorsA[J]? = some cA → ∀ i, i < cA.2 →
      i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) → i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) →
      p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i →
      (d.ksF (auxOfsOf st p.k cd j J)).getD i .ordinary = .recursive ∧
      (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = []) :
    ∀ j, j < st.pins.length →
      R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
        (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
        (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  intro j hj
  by_cases hb : d.bb ψ = 0
  · exact R.r2Grp_prop tbl₀ hρ hj hb
  · exact R.r2Grp_order_refl tbl₀ hρ hb hfinT j hj

end NestedRunFacts

end ConLeche.Model
