module

public import ConLeche.Model.Inductives.NestedCtorViaRun
public import ConLeche.Model.Inductives.RoundTripProp
import ConLeche.Semantics.Tower.FixRecCoreI
import ConLeche.Semantics.Tower.FixSquashI
import ConLeche.Model.Inductives.InvFold
import ConLeche.Model.Inductives.FixRuleKit
import ConLeche.Model.Inductives.DeclMutual

public section

/-!
# The restored constructor's leaf, typed at the run (task #279 M-D′ D3, DESIGN §M.54)

`restoredCtor_typed` (`NestedCtorLeaf.lean`) types the leaf
`λ p⃗ f⃗, ⟦T.c⟧_aux p⃗ (ψ* f⃗)` under six facts stated in the currency the
run delivers.  This module discharges them off the run's core facts
`NestedRunCore` (ψ's side of the run, at EVERY level assignment):

* the telescope bits (`hbits`) are the family's regime bit
  (`FixCtorDataI.tssBits`/`tssPiBits`);
* ψ's terms at the copy targets are bounded at the parameters (`hΨB`,
  `NestedRunCore.final_below`);
* the restored domains are bounded at their own depth (`hbelowR`: the
  auxiliary entries by the datum, the `restoreAV` arms from the pins'
  readings bounded at the parameters, `DsA_below`);
* at a zero sort the body is a truth value (`hzero`: the member's
  leaf applied to fitting parameters and index values lands in its
  universe, `IndRep.app_mem_univ`, the fits from the restored tower's
  grading and the leaf's λ-shape, `leafSpineFit_full`);
* the ONE fact of ψ (`hΨ`): `psiFinal_mem` at the target pin, its
  index fit and container membership read off the restored domain at
  the copy position (`restoreAV`'s fired arm, a Π-tower over the
  telescope eliminated by `piTele_fold`/`piTele_fold_zero`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType AuxStored NestedPin ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The leaf, typed at the run -/

set_option maxHeartbeats 3200000 in
/-- **The restored constructor's leaf is typed at the run** (M-D′ D3):
`restoredCtor_typed`'s six facts off the run's core facts (see the
module docstring), for the leaf at ψ's final table
(`psiFinal`, from any initial table `tbl₀`). -/
theorem restoredCtorLeaf_of_run {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V} {lpsT : List Name} {order : List Nat}
    (R : NestedRunCore F env p st b params pbs mpAux d ψ cd lpsT order)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : d.ctorsA[J]? = some cA) (hmemJ : d.mems J < p.k)
    {lpsT' : List Name}
    (hD : FixCtorDataI mpAux.base2 d.env₀ (d.memberName (d.mems J)) lpsT' cA.1 d.nP cA.2
      (d.nIdxAt (d.mems J)) d.resSort d.isProp d.large (d.idxF J) (d.dsF J) (d.esF J)
      (d.srcsF J) (d.ksF J) (d.fvsPF J) (d.xFvsF J) (d.xrestF J) (d.eissF J) (d.tssF J)
      (fun i => d.memberName (d.tgts J i)) (fun i => d.nIdxAt (d.tgts J i)))
    (hstoredC : envAux.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2))
    (hokTy : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV
      (d.dsRestored mpAux.base2 ψ p.k J (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
        (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA))
      (ctorBodyAVI mpAux.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))))
    (tbl₀ : Nat → AnnotTerm) :
    Term.bvarsBelow 0
      (d.restoredCtorAV mpAux.base2 (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀)
        ψ p.k J cA.2 cA.1.name (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
        (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA)).erase ∧
    ∀ ρ : Nat → V,
      WellDenoted V ρ
        (d.restoredCtorAV mpAux.base2 (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀)
          ψ p.k J cA.2 cA.1.name (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
          (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA)) ∧
      AnnotValid V ρ
        (d.restoredCtorAV mpAux.base2 (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀)
          ψ p.k J cA.2 cA.1.name (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
          (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA)) ∧
      interp V ρ
        (d.restoredCtorAV mpAux.base2 (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀)
          ψ p.k J cA.2 cA.1.name (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
          (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA))
        ∈ˢ interp V ρ (mkPisAV
          (d.dsRestored mpAux.base2 ψ p.k J (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
            (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA))
          (ctorBodyAVI mpAux.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))) := by
  -- ## names
  obtain ⟨Ψ, hΨdef⟩ : ∃ x, x = d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ :=
    ⟨_, rfl⟩
  obtain ⟨tgtCont, htgtCont⟩ : ∃ x : Nat → Name, x = fun j'' => (cd j'').dJ.memberName (cd j'').mm :=
    ⟨_, rfl⟩
  obtain ⟨tgtLps, htgtLps⟩ : ∃ x : Nat → Name → Nat, x = fun j'' => (cd j'').ψ' := ⟨_, rfl⟩
  obtain ⟨tgtDsA, htgtDsA⟩ : ∃ x : Nat → List AnnotTerm, x = fun j'' => (cd j'').DsA := ⟨_, rfl⟩
  obtain ⟨dsR, hdsR⟩ : ∃ x, x = d.dsRestored mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA := ⟨_, rfl⟩
  obtain ⟨body, hbody⟩ : ∃ x, x = ctorBodyAVI mpAux.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ) :=
    ⟨_, rfl⟩
  rw [← hΨdef, ← htgtCont, ← htgtLps, ← htgtDsA, ← hdsR, ← hbody]
  rw [← htgtCont, ← htgtLps, ← htgtDsA, ← hdsR, ← hbody] at hokTy
  -- ## the block's facts
  have hreps := R.reps
  obtain ⟨-, hkb, hkRb, hnPb, -, -, -, hall⟩ := R.reps
  have hdk := R.dk
  have hk0 : 0 < d.k := by omega
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, hsv₀, hrep₀⟩ :=
    hall 0 (by rw [← hkb]; exact hk0)
  obtain ⟨sT, cvTT, cvRT, capsT, mIT, rPT, rulesT, -, -, -, hsvT, hrepT⟩ :=
    hall (d.mems J) (by rw [← hkb]; omega)
  have hview := R.viewA J
  have hcWF := mpAux.base2.wf _ (List.mem_of_find?_eq_some hstoredC)
  have hcf : cA.1.type.hasFvar = false := hcWF.1
  have hcb : cA.1.type.looseBVarsBounded 0 = true := hcWF.2.2.2.1
  -- the datum's projections at the block's datum
  have hlenD : (d.dsF J ψ).length = d.nP + cA.2 := hD.len ψ
  have hlenE : (d.esF J ψ).length = d.nIdxAt (d.mems J) := hD.lenE ψ
  have htssBits : ∀ i, ∀ dd ∈ (d.tssF J ψ).getD i [], (dd.2.1 = 0 ↔ d.resSort.eval ψ = 0) :=
    hD.tssBits ψ
  have htssPi : ∀ i, ∀ dd ∈ (d.tssF J ψ).getD i [], dd.1 = 0 ∧ dd.2.1 ≤ 1 := hD.tssPiBits ψ
  have htssBelow : ∀ i, DomsBelow (d.nP + i) ((d.tssF J ψ).getD i []) := hD.tssBelow ψ
  have heissBelow : ∀ i, ∀ E ∈ (d.eissF J ψ).getD i [],
      Term.bvarsBelow (d.nP + i + ((d.tssF J ψ).getD i []).length) E.erase := hD.eissBelow ψ
  have hbelowD : DomsBelow 0 (d.dsF J ψ) := hD.below ψ
  have hlenR : dsR.length = d.nP + cA.2 := by rw [hdsR, d.dsRestored_length, hlenD]
  have hppsLen : (d.ppsM 0 ψ).length = d.nP + d.nIdxAt 0 := hrep₀.former.len ψ
  have hppsTlen : (d.ppsM (d.mems J) ψ).length = d.nP + d.nIdxAt (d.mems J) := hrepT.former.len ψ
  have hppsTbelow : DomsBelow 0 (d.ppsM (d.mems J) ψ) := hrepT.former.below ψ
  have hpsLen : (d.params ψ).length = d.nP := by
    unfold IndRepData.params
    rw [List.length_map, List.length_take, hppsLen]
    omega
  have hppsBelow : DomsBelow 0 ((d.ppsM 0 ψ).take d.nP) := domsBelow_take (R.ppsM_below hk0)
  have hpIff : ∀ ρ : Nat → V, Sat V (d.params ψ).reverse ρ ↔
      Sat V (((d.dsF J ψ).take d.nP).map (·.2.2)).reverse ρ := hrep₀.paramsIff J cA hJ ψ
  -- the parameter entries of the restored domains are the auxiliary ones
  have htake : (dsR.take d.nP).map (·.2.2) = ((d.dsF J ψ).take d.nP).map (·.2.2) := by
    apply List.ext_getElem?
    intro l
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_take, List.getElem?_take]
    split
    · next hl => rw [hdsR, d.dsRestored_getElem?_lt mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA hl]
    · rfl
  -- ## the regime bit
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Nat, b₀ = if d.resSort.eval ψ = 0 then 0 else 1 := ⟨_, rfl⟩
  have hb₀le : b₀ ≤ 1 := by rw [hb₀]; split <;> omega
  have hb₀iff : b₀ = 0 ↔ d.resSort.eval ψ = 0 := by
    rw [hb₀]; split
    · next h => exact ⟨fun _ => h, fun _ => rfl⟩
    · next h => exact ⟨fun h1 => absurd h1 (by omega), fun h1 => absurd h1 h⟩
  have hbits : ∀ i, d.copyPos p.k J i → ∀ dd ∈ (d.tssR J ψ).getD i [], dd.2.1 = b₀ := by
    intro i _ dd hdd
    rw [hview.2.2.2] at hdd
    exact bit_eq_of_le_one (htssPi i dd hdd).2 hb₀le ((htssBits i dd hdd).trans hb₀iff.symm)
  -- ## copy positions target pins
  have hcopyPin : ∀ i, d.copyPos p.k J i → d.tgtsR J i - p.k < st.pins.length := by
    intro i hc
    have := R.tgtsA hk0 J i
    obtain ⟨-, hk⟩ := hc
    omega
  -- ## ψ's terms at the copy targets are bounded at the parameters
  have hΨB : ∀ i, i < cA.2 → d.copyPos p.k J i →
      Term.bvarsBelow d.nP (Ψ (d.tgtsR J i - p.k)).erase := by
    intro i _ hc
    rw [hΨdef]
    exact R.final_below tbl₀ (hcopyPin i hc)
  -- ## the restored domains are bounded at their own depth
  have hbelowR : DomsBelow 0 dsR := by
    refine domsBelow_of_getD fun k hk => ?_
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hdsR, d.dsRestored_getElem?]
    have hkD : k < (d.dsF J ψ).length := by rw [hlenR] at hk; omega
    obtain ⟨e, he⟩ : ∃ e, (d.dsF J ψ)[k]? = some e := ⟨_, List.getElem?_eq_getElem hkD⟩
    have heB : Term.bvarsBelow k e.2.2.erase := by
      have := hbelowD.getD_below k hkD
      rwa [Nat.zero_add, List.getD_eq_getElem?_getD, he] at this
    rw [he]
    simp only [Option.map_some, Option.getD_some]
    split
    · exact heB
    · next hge =>
      unfold IndRepData.restoreAV
      split
      · next harm =>
        obtain ⟨i, rfl⟩ : ∃ i, k = d.nP + i := ⟨k - d.nP, by omega⟩
        rw [Nat.add_sub_cancel_left] at harm ⊢
        have hc : d.copyPos p.k J i := harm
        have hj := hcopyPin i hc
        refine bvarsBelow_mkPisAV (by rw [hview.2.2.2]; exact htssBelow i) ?_
        rw [AnnotTerm.erase_mkAppN]
        refine VExprAux.bvarsBelow_mkAppN
          (Term.bvarsBelow.mono (Nat.zero_le _) (mpAux.base2.cval_closedL _ _)) fun a ha => ?_
        obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
        rcases List.mem_append.mp ha' with h | h
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
          rw [AnnotTerm.erase_liftN]
          have hqB : Term.bvarsBelow d.nP q.erase := by
            rw [htgtDsA] at hq
            exact R.DsA_below hj q hq
          have := VExprAux.bvarsBelow_liftN (i + ((d.tssR J ψ).getD i []).length) _ _ 0 hqB
          rwa [show d.nP + (i + ((d.tssR J ψ).getD i []).length)
            = d.nP + i + ((d.tssR J ψ).getD i []).length from by omega] at this
        · rw [hview.2.2.1] at h
          rw [hview.2.2.2]
          exact heissBelow i a' h
      · rw [show d.nP + (k - d.nP) = k from by omega, List.getD_eq_getElem?_getD, he]
        exact heB
  -- ## at a zero sort the body is a truth value
  have hzero : d.resSort.eval ψ = 0 → ∀ (ρ : Nat → V) (as : List V),
      SpineFit ρ (dsR.map (·.2.2)) as → interp V (consList as ρ) body ∈ˢ (univZero : V) := by
    intro h0 ρ as hfit
    have hfit' : SpineFit ρ ((dsR.take d.nP).map (·.2.2) ++ (dsR.drop d.nP).map (·.2.2)) as := by
      rw [← List.map_append, List.take_append_drop]; exact hfit
    obtain ⟨ps, fs, rfl, hps, hfs⟩ := spineFit_append_inv hfit'
    have hpsLen' : ps.length = d.nP := by
      rw [hps.length_eq, List.length_map, List.length_take, hlenR]; omega
    have hfsLen : fs.length = cA.2 := by
      rw [hfs.length_eq, List.length_map, List.length_drop, hlenR]; omega
    rw [htake] at hps
    have hsatP : Sat V (d.params ψ).reverse (consList ps ρ) := by
      refine (hpIff _).mpr ?_
      have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hps
      rwa [List.append_nil] at h
    have hpsFit : SpineFit ρ (d.params ψ) ps := by
      have h := spineFit_params_of_sat hpsLen hppsBelow hsatP
      rw [paramVals_push hpsLen'] at h
      unfold IndRepData.params at h ⊢
      exact spineFit_congr_below hppsBelow (fun i hi => absurd hi (Nat.not_lt_zero _)) h
    -- the body, graded at the leaf frame
    have hokB : WellDenoted V (consList fs (consList ps ρ)) body := by
      rw [← consList_append]
      exact wellDenoted_mkPisAV_body (hokTy ρ).1 (ps ++ fs) hfit
    -- the index readings fit the member's telescope
    have hfitAll := leafSpineFit_full (nP := d.nP) (nIdx := d.nIdxAt (d.mems J)) (w := sT.eval ψ)
      (ρp := consList ps ρ) (σas := fs) (e := cA.2) hppsTlen
      (mpAux.base2.cval_closedL _ ψ)
      (hrepT.leafShape (d.mems J) (by show d.mems J < d.kReal; rw [hkRb]; omega) ψ)
      hfsLen hlenE (by rw [hbody, ctorBodyAVI, paramBvars_eq_paramBvarsAt] at hokB; exact hokB)
    have hshift : (fun j => consList ps ρ (j + d.nP)) = ρ := by
      funext j; rw [← hpsLen', consList_apply_add]
    rw [hshift, paramVals_consList hpsLen'] at hfitAll
    have hsplit : (d.ppsM (d.mems J) ψ).map (·.2.2)
        = ((d.ppsM (d.mems J) ψ).take d.nP).map (·.2.2) ++
          ((d.ppsM (d.mems J) ψ).drop d.nP).map (·.2.2) := by
      rw [← List.map_append, List.take_append_drop]
    rw [hsplit] at hfitAll
    obtain ⟨as₁, as₂, heq, h₁, h₂⟩ := spineFit_append_inv hfitAll
    have hlen₁ : as₁.length = d.nP := by
      rw [h₁.length_eq, List.length_map, List.length_take, hppsTlen]; omega
    obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁, hpsLen'])
    have his : SpineFit (consList ps ρ) (d.IdsM (d.mems J) ψ)
        ((d.esF J ψ).map (interp V (consList fs (consList ps ρ)))) := h₂
    have hmem := IndRep.app_mem_univ hrepT ψ hpsFit his
    have hw0 : ({ d with resSort := sT } : IndRepData V).w ψ = 0 := by
      show sT.eval ψ = 0
      rw [hsvT ψ]; exact h0
    rw [hw0, univ_zero] at hmem
    rw [hbody, ctorBodyAVI, consList_append, interp_mkAppN_map, List.map_append,
      paramBvars_eq_paramBvarsAt, ← hfsLen, interp_paramBvarsAt_consList, paramVals_push hpsLen',
      interp_closed (V := V) (mpAux.base2.cval_closedL _ ψ) _ ρ]
    exact hmem
  -- ## the ONE fact of ψ
  have hΨ : ∀ (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ (i : Nat), i < cA.2 → d.copyPos p.k J i → ∀ fs : List V, fs.length = cA.2 →
      SpineFit ρp ((dsR.drop d.nP).map (·.2.2)) fs →
      ∀ as, SpineFit (consList (fs.take i) ρp) (((d.tssR J ψ).getD i []).map (·.2.2)) as →
        (((d.eissR J ψ).getD i []).map (interp V (consList as (consList (fs.take i) ρp))) ++
          [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
            (interp V ρp (Ψ (d.tgtsR J i - p.k)))
          ∈ˢ (paramVals d.nP ρp ++
              ((d.eissR J ψ).getD i []).map (interp V (consList as (consList (fs.take i) ρp)))).foldl
              SetTheory.app (interp V ρp (mpAux.base2.acval (d.memberName (d.tgtsR J i)) ψ)) := by
    intro ρp hsat i hi hc fs hfs hfit as has
    obtain ⟨j, hjdef⟩ : ∃ j, j = d.tgtsR J i - p.k := ⟨_, rfl⟩
    have hj : j < st.pins.length := by rw [hjdef]; exact hcopyPin i hc
    have hρ : SpineFit ρp (d.params ψ) (paramVals d.nP ρp) :=
      spineFit_params_of_sat hpsLen hppsBelow hsat
    obtain ⟨pf, hbm, -⟩ := (R.pins j hj).1
    have hmm : (cd j).mm < (cd j).dJ.k := pf.mm
    have hpkj : p.k + j = d.tgtsR J i := by obtain ⟨-, hk⟩ := hc; omega
    -- the container's group facts at the pin's member
    have hokJ := pf.grp (cd j).mm hmm
    obtain ⟨cvTJ, cvRJ, mIJ, rPJ, rulesJ, hrepJ⟩ := pf.repAll (cd j).mm hmm
    have hlsJ := hrepJ.leafShape (cd j).mm (by rw [pf.kReal]; exact hmm) (cd j).ψ'
    have hppsJlen : ((cd j).dJ.ppsM (cd j).mm (cd j).ψ').length
        = (cd j).dJ.nP + (cd j).dJ.nIdxAt (cd j).mm := hokJ.ff.1
    have hDsAlen : (cd j).DsA.length = (cd j).dJ.nP := pf.len
    have hDsAbelow : ∀ q ∈ (cd j).DsA, Term.bvarsBelow d.nP q.erase := R.DsA_below hj
    have hwJ : (cd j).dJ.w (cd j).ψ' = d.w ψ := hokJ.idx.sort
    have hnIdxJ : (cd j).dJ.nIdxAt (cd j).mm = d.nIdxAt (d.tgts J i) := by
      rw [hokJ.idx.nIdx, hbm, hpkj, hview.2.1]
    -- the copy field's index readings, counted
    have heissLen : ((d.eissR J ψ).getD i []).length = d.nIdxAt (d.tgts J i) := by
      rw [hview.2.2.1]
      obtain ⟨hmemR, -⟩ := hc
      rw [hview.1] at hmemR
      rcases (mem_recIdxOf.mp hmemR).2 with h | h
      · exact hD.eisLen ψ i h hi
      · exact hD.eisLenRefl ψ i h hi
    -- ## the field's value in the restored domain's reading
    have hlenDrop : ((dsR.drop d.nP).map (·.2.2)).length = cA.2 := by
      rw [List.length_map, List.length_drop, hlenR]; omega
    have hmemF := FixKI.spineFit_getD_mem' hfit (by rw [hlenDrop]; exact hi)
    have hentryR : ((dsR.drop d.nP).map (·.2.2)).getD i default
        = d.restoreAV mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA i := by
      rw [List.getD_eq_getElem?_getD, hdsR,
        d.dsRestored_drop_getElem? mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA hlenD hi]
      rfl
    rw [hentryR] at hmemF
    have hc' : i ∈ ConLeche.recIdxOf (d.ksR J) ∧ p.k ≤ d.tgtsR J i := hc
    unfold IndRepData.restoreAV at hmemF
    rw [if_pos hc', ← hjdef] at hmemF
    simp only [htgtCont, htgtLps, htgtDsA] at hmemF
    -- the frames
    obtain ⟨σ₁, hσ₁⟩ : ∃ x, x = consList (fs.take i) ρp := ⟨_, rfl⟩
    rw [← hσ₁] at hmemF has ⊢
    have hfsTake : (fs.take i).length = i := by rw [List.length_take, hfs]; omega
    obtain ⟨args, hargs⟩ : ∃ x, x = (cd j).DsA.map (·.liftN (i + ((d.tssR J ψ).getD i []).length) 0)
        ++ (d.eissR J ψ).getD i [] := ⟨_, rfl⟩
    rw [← hargs] at hmemF
    have hbitsT : ∀ dd ∈ (d.tssR J ψ).getD i [], (dd.2.1 = 0 ↔ b₀ = 0) :=
      fun dd hdd => by rw [hbits i hc dd hdd]
    rw [interp_mkPisAV_piTele (B := fun as' => interp V (consList as' σ₁)
        (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ') args))
      (acc := []) hbitsT (fun as' _ => rfl)] at hmemF
    -- ## the restored entry is graded at the telescope frame: the
    -- restored tower's grading at the frame reconstructed from ρp
    have hvalsEq : (List.range d.nP).reverse.map ρp = paramVals d.nP ρp := by
      unfold paramVals
      have h0 := map_paramBvarsAt_interp (nP := d.nP) (e := 0) (ρp := ρp) (σ := ρp)
        (fun j => by rw [Nat.add_zero])
      rw [Nat.add_zero] at h0
      exact h0.symm
    have hρp : consList (paramVals d.nP ρp) (fun j => ρp (j + d.nP)) = ρp := by
      rw [← hvalsEq]; exact consList_range_reverse d.nP ρp
    have hpvLen : (paramVals d.nP ρp).length = d.nP := by
      unfold paramVals paramBvarsAt; simp
    have hps' : SpineFit (fun j => ρp (j + d.nP)) ((dsR.take d.nP).map (·.2.2)) (paramVals d.nP ρp) := by
      have h := spineFit_of_sat (Δ₀ := []) (by rw [List.append_nil]; exact (hpIff ρp).mp hsat)
      rw [List.length_map, List.length_take, hlenD, show min d.nP (d.nP + cA.2) = d.nP from by omega,
        hvalsEq, ← htake] at h
      exact h
    have hfitFull : SpineFit (fun j => ρp (j + d.nP)) (dsR.map (·.2.2)) (paramVals d.nP ρp ++ fs) := by
      rw [← List.take_append_drop d.nP dsR, List.map_append]
      refine SpineFit.append hps' ?_
      rw [hρp]
      exact hfit
    obtain ⟨e, he⟩ : ∃ e, (d.dsF J ψ)[d.nP + i]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hget : dsR[d.nP + i]? = some (e.1, e.2.1,
        d.restoreAV mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA i) := by
      rw [hdsR, d.dsRestored_getElem?, he]
      simp only [Option.map_some, Option.some.injEq]
      rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)), Nat.add_sub_cancel_left]
    have hfitPre : SpineFit (fun j => ρp (j + d.nP)) ((dsR.take (d.nP + i)).map (·.2.2))
        (paramVals d.nP ρp ++ fs.take i) := by
      have h := hfitFull
      rw [← List.take_append_drop (d.nP + i) dsR, List.map_append] at h
      obtain ⟨as₁, as₂, heq, h₁, -⟩ := spineFit_append_inv h
      have heq' : (paramVals d.nP ρp ++ fs.take i) ++ fs.drop i = as₁ ++ as₂ := by
        rw [List.append_assoc, List.take_append_drop]; exact heq
      have hlen₁ : as₁.length = d.nP + i := by
        rw [h₁.length_eq, List.length_map, List.length_take, hlenR]; omega
      obtain ⟨rfl, -⟩ := List.append_inj heq' (by
        rw [hlen₁, List.length_append, hpvLen, hfsTake])
      exact h₁
    have hokEntry : WellDenoted V σ₁ (d.restoreAV mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA i) := by
      have h := wellDenoted_mkPisAV_dom (hokTy (fun j => ρp (j + d.nP))).1
        (paramVals d.nP ρp ++ fs.take i) (d.nP + i) _ hget hfitPre
      rw [consList_append, hρp, ← hσ₁] at h
      exact h
    unfold IndRepData.restoreAV at hokEntry
    rw [if_pos hc', ← hjdef] at hokEntry
    simp only [htgtCont, htgtLps, htgtDsA] at hokEntry
    rw [← hargs] at hokEntry
    -- the container application under the telescope, graded and fitting
    have hokApp : ∀ as', SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as' →
        WellDenoted V (consList as' σ₁)
          (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ') args) :=
      fun as' has' => wellDenoted_mkPisAV_body hokEntry as' has'
    -- the lifted readings read the pin's readings at the block's parameter frame
    have hargsRead : ∀ as', as'.length = ((d.tssR J ψ).getD i []).length →
        args.map (interp V (consList as' σ₁))
          = (cd j).DsA.map (interp V ρp) ++
            ((d.eissR J ψ).getD i []).map (interp V (consList as' σ₁)) := by
      intro as' hlen'
      rw [hargs, List.map_append, List.map_map]
      congr 1
      refine List.map_congr_left fun q _ => ?_
      simp only [Function.comp]
      rw [interp_liftN, hσ₁, ← consList_append,
        show i + ((d.tssR J ψ).getD i []).length = (fs.take i ++ as').length from by
          rw [List.length_append, hfsTake, hlen'],
        shiftE_consList]
    have hargsLen : args.length = ((cd j).dJ.ppsM (cd j).mm (cd j).ψ').length := by
      rw [hargs, List.length_append, List.length_map, hDsAlen, heissLen, hppsJlen, hnIdxJ]
    -- the fits: the pin's readings at the container's parameters, the
    -- index readings at its index telescope
    have hfits : ∀ as', SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as' →
        SpineFit (consList as' σ₁) ((cd j).dJ.params (cd j).ψ') ((cd j).DsA.map (interp V ρp)) ∧
        SpineFit (consList ((cd j).DsA.map (interp V ρp)) (consList as' σ₁))
          ((cd j).dJ.IdsM (cd j).mm (cd j).ψ')
          (((d.eissR J ψ).getD i []).map (interp V (consList as' σ₁))) := by
      intro as' has'
      have hlen' : as'.length = ((d.tssR J ψ).getD i []).length := by
        rw [has'.length_eq, List.length_map]
      obtain ⟨B, hB⟩ := hlsJ
      have hsp := spineFit_of_wellDenoted_lams (Nat.succ_ne_zero ((cd j).dJ.w (cd j).ψ'))
        (args := args) (ds := (cd j).dJ.ppsM (cd j).mm (cd j).ψ') (σ := consList as' σ₁)
        (ρ := consList as' σ₁) (b := B)
        (f := mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ')
        (by rw [hargsLen]; exact Nat.le_refl _) (hokApp as' has') (by rw [hB])
      rw [hargsLen, List.take_of_length_le (Nat.le_refl _), hargsRead as' hlen'] at hsp
      have hsplitJ : ((cd j).dJ.ppsM (cd j).mm (cd j).ψ').map (·.2.2)
          = (((cd j).dJ.ppsM (cd j).mm (cd j).ψ').take (cd j).dJ.nP).map (·.2.2) ++
            (((cd j).dJ.ppsM (cd j).mm (cd j).ψ').drop (cd j).dJ.nP).map (·.2.2) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplitJ] at hsp
      obtain ⟨as₁, as₂, heq, h₁, h₂⟩ := spineFit_append_inv hsp
      have hlen₁ : as₁.length = (cd j).dJ.nP := by
        rw [h₁.length_eq, List.length_map, List.length_take, hppsJlen]; omega
      obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁, List.length_map, hDsAlen])
      refine ⟨?_, h₂⟩
      -- member `mm`'s parameter telescope is the container's, as frames
      have hsat₁ : Sat V ((((cd j).dJ.ppsM (cd j).mm (cd j).ψ').take (cd j).dJ.nP).map (·.2.2)).reverse
          (consList ((cd j).DsA.map (interp V ρp)) (consList as' σ₁)) := by
        have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) h₁
        rwa [List.append_nil] at h
      have hsat₂ := (hokJ.pIffM _).mpr hsat₁
      have h := spineFit_of_sat (Δ₀ := []) (by rw [List.append_nil]; exact hsat₂)
      have hppsJ0 : ((cd j).dJ.ppsM 0 (cd j).ψ').length = (cd j).dJ.nP + (cd j).dJ.nIdxAt 0 :=
        (pf.grp 0 (by omega)).ff.1
      have hlenP : ((cd j).dJ.params (cd j).ψ').length = (cd j).dJ.nP := by
        unfold IndRepData.params
        rw [List.length_map, List.length_take, hppsJ0]
        omega
      rw [hlenP, paramVals_consList (by rw [List.length_map, hDsAlen])] at h
      have hshift' : (fun j' => consList ((cd j).DsA.map (interp V ρp)) (consList as' σ₁) (j' + (cd j).dJ.nP))
          = consList as' σ₁ := by
        funext j'
        rw [show (cd j).dJ.nP = ((cd j).DsA.map (interp V ρp)).length from by
          rw [List.length_map, hDsAlen], consList_apply_add]
      rw [hshift'] at h
      exact h
    -- ## the container application is a truth value at a zero sort
    have hzeroJ : b₀ = 0 → ∀ as', SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as' →
        interp V (consList as' σ₁)
          (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ') args)
          ∈ˢ (univZero : V) := by
      intro hb0 as' has'
      obtain ⟨hfit₁, hfit₂⟩ := hfits as' has'
      have hmem := IndRep.app_mem_univ hrepJ (cd j).ψ' hfit₁ hfit₂
      rw [interp_mkAppN_map, hargsRead as' (by rw [has'.length_eq, List.length_map])]
      have hw : (cd j).dJ.w (cd j).ψ' = 0 := by
        rw [hwJ]; show d.resSort.eval ψ = 0; exact hb₀iff.mp hb0
      rw [hw, univ_zero] at hmem
      exact hmem
    -- ## the field applied to the telescope lands in the container at the pin
    have hxfold : as.foldl SetTheory.app (fs.getD i pt) ∈ˢ interp V (consList as σ₁)
        (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ') args) := by
      by_cases hb0 : b₀ = 0
      · rw [hb0] at hmemF
        have := piTele_fold_zero hmemF (fun as' hfit' => by
            rw [List.nil_append]; exact hzeroJ hb0 as' (fitsS_teleOfFields.mp hfit'))
          as (fitsS_teleOfFields.mpr has)
        rwa [List.nil_append] at this
      · have := piTele_fold hb0 hmemF (fitsS_teleOfFields.mpr has)
        rwa [List.nil_append] at this
    -- ## `psiFinal_mem` at the target pin
    obtain ⟨-, hfit₂⟩ := hfits as has
    obtain ⟨σ₀, hσ₀⟩ : ∃ x, x = consList (paramVals d.nP ρp) ρp := ⟨_, rfl⟩
    have hDsAσ : (cd j).DsA.map (interp V σ₀) = (cd j).DsA.map (interp V ρp) := by
      refine List.map_congr_left fun q hq => ?_
      rw [hσ₀]
      exact interp_paramFrame (hDsAbelow q hq) ρp ρp
    have hIdsBelow : DomsBelow (cd j).dJ.nP
        (((cd j).dJ.ppsM (cd j).mm (cd j).ψ').drop (cd j).dJ.nP) := by
      have := DomsBelow.drop (cd j).dJ.nP (hrepJ.former.below (cd j).ψ')
      rwa [Nat.zero_add] at this
    have his : SpineFit (consList ((cd j).DsA.map (interp V σ₀)) σ₀)
        ((cd j).dJ.IdsM (cd j).mm (cd j).ψ')
        (((d.eissR J ψ).getD i []).map (interp V (consList as σ₁))) := by
      rw [hDsAσ]
      unfold IndRepData.IdsM at hfit₂ ⊢
      refine spineFit_congr_below hIdsBelow (fun k hk => ?_) hfit₂
      rw [consList_apply_lt' _ _ (by rw [List.length_map, hDsAlen]; exact hk),
        consList_apply_lt' _ _ (by rw [List.length_map, hDsAlen]; exact hk)]
    have hx : as.foldl SetTheory.app (fs.getD i pt)
        ∈ˢ ((cd j).DsA.map (interp V σ₀) ++
            ((d.eissR J ψ).getD i []).map (interp V (consList as σ₁))).foldl SetTheory.app
            (interp V σ₀ (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ')) := by
      rw [hDsAσ]
      have h := hxfold
      rw [interp_mkAppN_map, hargsRead as (by rw [has.length_eq, List.length_map]),
        interp_closed (V := V) (mpAux.base2.cval_closedL _ _) _ σ₀] at h
      exact h
    rw [hσ₀] at his hx
    have hmain := R.psiFinal_mem tbl₀ hρ hj hmm his hx
    rw [hbm, Nat.add_assoc, hbm, hpkj, ← hΨdef] at hmain
    unfold foldApp at hmain
    rw [hjdef] at hmain
    rw [interp_paramFrame (hΨB i hi hc) ρp ρp] at hmain
    exact hmain
  -- ## the leaf, typed
  subst hdsR hbody hΨdef htgtCont htgtLps htgtDsA
  -- the transports, graded at the leaf frame (`NestedCtorViaRun`)
  have hviaWD := restoredCtorVia_of_run R hJ hmemJ hD hokTy hbelowR tbl₀ hΨ
  exact d.restoredCtor_typed mpAux hD hview.1 hview.2.1 hview.2.2.1 hview.2.2.2 hstoredC hcf
    hcb hbits hpIff hΨ hviaWD hokTy hzero hbelowR hΨB

end ConLeche.Model
