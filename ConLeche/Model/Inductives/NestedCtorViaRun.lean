module

public import ConLeche.Model.Inductives.NestedCtorRun
public import ConLeche.Model.Inductives.RoundTripProp
import ConLeche.Semantics.Tower.FixRecCoreI
import ConLeche.Semantics.Tower.FixSquashI
import ConLeche.Model.Inductives.InvFold
import ConLeche.Model.Inductives.FixRuleKit
import ConLeche.Model.Inductives.FoldBelow
import ConLeche.Model.Inductives.DeclMutual

public section

/-!
# The transports, graded at the restored constructor's leaf frame (task #279 M-D′ D3, DESIGN §M.56)

`restoredCtor_typed` (`NestedCtorLeaf.lean`) types the restored
constructor's leaf under, among others, the fact that ψ*'s transports
are GRADED at the leaf frame (`hviaWD`): at a spine `p⃗ ++ f⃗` fitting
the restored domains, the entry

    viaEntryAV Ψⱼ nF 0 i 0 tssᵢ eisᵢ  =  λ a⃗, Ψⱼ e⃗ᵢ(a⃗) (fᵢ a⃗)

is `WellDenotedV` at every copy-recursive position `i`.  This module
discharges it off the run's core facts (`NestedRunCore`), the ONE fact
of ψ (`hΨ`, proved beside it in `NestedCtorTypedRun.lean`) and the
restored tower's grading.

The proof is `viaWD_psi`'s at the leaf frame (`o = l = 0`: no motives,
minors or hypotheses; the frame under the telescope values is
`consList a⃗ (consList f⃗ ρp)`):

* the λ-tower's laws are `mkLamsAV_bits_wellDenoted`/`_validV` at
  `UnderTowerOk`/`UnderTowerValid`; the telescope's entries are the
  RESTORED field entry's own (`restoreAV`'s fired arm is a Π-tower over
  the very same telescope), lifted past the remaining fields —
  `ihTeleAtR nF 0 i 0 = liftDoms (nF - i) 0` at the leaf frame — so
  their grading is `wellDenoted_mkPisAV_dom` at the lifted entry;
* the tower's target `T` is the COPY member's leaf at the block's
  parameters and the field's index readings (`hentry`), graded and
  landing in the copy's universe by `wellDenotedV_mkAppN_of_spineFit`
  at the member's `FormerFacts` — which is also the zero clause
  (`univ_zero`), the copy's index telescope being the container's at
  the pin (`CopyIdxRead.idxIff`);
* the body is `wellDenotedV_mkAppN_of_spineFit` at ψ's Π-type
  (`PsiTypedPi` from `NestedRunCore.final_typed`, a literal `mkPisAV`
  by `instSeq_mkPisAV`), at the fit of the index readings and the
  field applied to the telescope (the latter in the CONTAINER's carrier
  at the pin, `piTele_fold`/`piTele_fold_zero` at the restored entry's
  reading); its membership in `T` is `hΨ` itself.

ψ's Π-type holds at the frame `consList (paramVals nP ρp) ρp` (that is
what `final_typed` delivers at `ρp`), so the whole argument runs there
and the conclusion is moved back to `ρp` at the end: the entry is
bounded at `nP + nF` (`viaEntryAV_below`) and the two frames agree
below it.
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

/-! ## Kit: the ih-moved telescope at a leaf frame -/

/-- At a constructor's own leaf frame (`o = l = 0`) moving a field's
telescope to the ih frame is lifting it past the remaining fields. -/
theorem ihTeleAtGo_leaf (nF i : Nat) :
    ∀ (k : Nat) (tl : List (Nat × Nat × AnnotTerm)),
      ihTeleAtGo nF 0 i 0 k tl = liftDoms (nF - i) k tl
  | _, [] => rfl
  | k, dd :: tl => by
    simp only [ihTeleAtGo, liftDoms, ihTeleAtGo_leaf nF i (k + 1) tl, ihIdxAtM,
      AnnotTerm.liftN_zero, Nat.add_zero]

theorem ihTeleAtR_leaf (nF i : Nat) (tl : List (Nat × Nat × AnnotTerm)) :
    ihTeleAtR nF 0 i 0 tl = liftDoms (nF - i) 0 tl :=
  ihTeleAtGo_leaf nF i 0 tl

/-! ## Kit: towers, the parameter frame -/

omit [SetTheory V] in
/-- A Π-tower over domains bounded at their depths, with a body bounded
under them, is bounded (the converse of `bvarsBelow_mkPisAV_inv`). -/
theorem bvarsBelow_mkPisAV {b : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {k : Nat}, DomsBelow k ds →
      Term.bvarsBelow (k + ds.length) b.erase → Term.bvarsBelow k (mkPisAV ds b).erase
  | [], _, _, hb => by simpa [mkPisAV] using hb
  | d :: ds, k, hds, hb => by
    simp only [mkPisAV, AnnotTerm.erase_pi]
    refine ⟨hds.1, bvarsBelow_mkPisAV (k := k + 1) hds.2 ?_⟩
    rw [List.length_cons] at hb
    rwa [show k + 1 + ds.length = k + (ds.length + 1) from by omega]

/-- **A member of a zero-level nested product folds along a fitting
tuple into the body** when the bodies are truth values: the member and
every partial application are the point (`piR_zero`, `app_pt`), and
the point inhabits an inhabited truth value. -/
theorem piTele_fold_zero {B : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V} {x : V}, x ∈ˢ piTele 0 T B acc →
      (∀ as, FitsS T as → B (acc ++ as) ∈ˢ (univZero : V)) →
      ∀ as, FitsS T as → as.foldl SetTheory.app x ∈ˢ B (acc ++ as)
  | _, .nil, acc, x, hx, _, [], _ => by simpa [piTele] using hx
  | _, .nil, _, _, _, _, _ :: _, hfit => hfit.elim
  | _, .cons _ _, _, _, _, _, [], hfit => hfit.elim
  | _, .cons A T, acc, x, hx, hB, a :: as, hfit => by
    have hx' : x ∈ˢ piR 0 A (fun a => piTele 0 (T a) B (acc ++ [a])) := hx
    rw [piR_zero] at hx'
    obtain ⟨hall, rfl⟩ := mem_truthVal.mp hx'
    obtain ⟨y, hy⟩ := hall a hfit.1
    have hzero : piTele 0 (T a) B (acc ++ [a]) ∈ˢ (univZero : V) :=
      piTele_zero_mem_univZero fun as' hfit' => by
        have := hB (a :: as') ⟨hfit.1, hfit'⟩
        rwa [List.append_cons] at this
    have hy' : y = pt := eq_pt_of_mem_univZero hzero hy
    rw [hy'] at hy
    have := piTele_fold_zero (T := T a) (acc := acc ++ [a]) hy
      (fun as' hfit' => by
        have := hB (a :: as') ⟨hfit.1, hfit'⟩
        rwa [List.append_cons] at this) as hfit.2
    rw [List.foldl_cons, app_pt]
    rwa [List.append_assoc, List.singleton_append] at this

/-- The block's parameters fit their own telescope at a frame
satisfying it (`spineFit_of_sat`, the frame shifted back by the
domains' closedness). -/
theorem spineFit_params_of_sat {d : IndRepData V} {ψ : Name → Nat}
    (hlen : (d.params ψ).length = d.nP) (hbelow : DomsBelow 0 ((d.ppsM 0 ψ).take d.nP))
    {ρ : Nat → V} (hsat : Sat V (d.params ψ).reverse ρ) :
    SpineFit ρ (d.params ψ) (paramVals d.nP ρ) := by
  have h := spineFit_of_sat (Δ₀ := []) (by rw [List.append_nil]; exact hsat)
  rw [hlen] at h
  have hvals : (List.range d.nP).reverse.map ρ = paramVals d.nP ρ := by
    unfold paramVals
    have h0 := map_paramBvarsAt_interp (nP := d.nP) (e := 0) (ρp := ρ) (σ := ρ)
      (fun j => by rw [Nat.add_zero])
    rw [Nat.add_zero] at h0
    exact h0.symm
  rw [hvals] at h
  have hshift : ∀ i, i < 0 → (fun j => ρ (j + d.nP)) i = ρ i := fun i hi => absurd hi (Nat.not_lt_zero _)
  unfold IndRepData.params at h ⊢
  exact spineFit_congr_below hbelow hshift h

/-- The parameter values pushed back onto their frame agree with it
below the parameter count. -/
theorem consList_paramVals_lt {nP : Nat} (ρ ρ' : Nat → V) {k : Nat} (hk : k < nP) :
    consList (paramVals nP ρ) ρ' k = ρ k := by
  have hlen : (paramVals nP ρ).length = nP := by
    unfold paramVals paramBvarsAt; simp
  rw [consList_apply_lt' _ _ (by rw [hlen]; exact hk), hlen]
  unfold paramVals paramBvarsAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
    List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some, interp_bvar]
  congr 1
  omega

/-- A term bounded at the parameters reads alike at a frame and at the
frame with its parameter values pushed back. -/
theorem interp_paramFrame {nP : Nat} {E : AnnotTerm} (hE : Term.bvarsBelow nP E.erase)
    (ρ ρ' : Nat → V) :
    interp V (consList (paramVals nP ρ) ρ') E = interp V ρ E :=
  interp_congr_noBVar E (NoBVar_of_bvarsBelow hE fun _ hi => hi)
    (fun _ hk => consList_paramVals_lt ρ ρ' (Nat.lt_of_not_le hk))

/-! ## The transports, graded at the leaf frame -/

set_option maxHeartbeats 3200000 in
/-- **ψ*'s transports are graded at the restored constructor's leaf
frame** (M-D′ D3): `restoredCtor_typed`'s `hviaWD` off the run's core
facts, the ONE fact of ψ and the restored tower's grading (see the
module docstring). -/
theorem restoredCtorVia_of_run {μ : CheckMode} {F : Nat} {env envAux : Env}
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
    (hokTy : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV
      (d.dsRestored mpAux.base2 ψ p.k J (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
        (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA))
      (ctorBodyAVI mpAux.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))))
    (hbelowR : DomsBelow 0
      (d.dsRestored mpAux.base2 ψ p.k J (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
        (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA)))
    (tbl₀ : Nat → AnnotTerm)
    (hΨ : ∀ (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ (i : Nat), i < cA.2 → d.copyPos p.k J i → ∀ fs : List V, fs.length = cA.2 →
      SpineFit ρp (((d.dsRestored mpAux.base2 ψ p.k J (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
        (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA)).drop d.nP).map (·.2.2)) fs →
      ∀ as, SpineFit (consList (fs.take i) ρp) (((d.tssR J ψ).getD i []).map (·.2.2)) as →
        (((d.eissR J ψ).getD i []).map (interp V (consList as (consList (fs.take i) ρp))) ++
          [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
            (interp V ρp (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
              (d.tgtsR J i - p.k)))
          ∈ˢ (paramVals d.nP ρp ++
              ((d.eissR J ψ).getD i []).map (interp V (consList as (consList (fs.take i) ρp)))).foldl
              SetTheory.app (interp V ρp (mpAux.base2.acval (d.memberName (d.tgtsR J i)) ψ))) :
    ∀ (ρ : Nat → V) (ps fs : List V), ps.length = d.nP → fs.length = cA.2 →
      SpineFit ρ ((d.dsRestored mpAux.base2 ψ p.k J (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
        (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA)).map (·.2.2)) (ps ++ fs) →
      ∀ i, i < cA.2 → d.copyPos p.k J i →
        WellDenotedV V (consList (ps ++ fs) ρ)
          (viaEntryAV (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
            (d.tgtsR J i - p.k)) cA.2 0 i 0 ((d.tssR J ψ).getD i []) ((d.eissR J ψ).getD i [])) := by
  -- ## names
  obtain ⟨Ψ, hΨdef⟩ : ∃ x, x = d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ :=
    ⟨_, rfl⟩
  obtain ⟨tgtCont, htgtCont⟩ : ∃ x : Nat → Name, x = fun j'' => (cd j'').dJ.memberName (cd j'').mm :=
    ⟨_, rfl⟩
  obtain ⟨tgtLps, htgtLps⟩ : ∃ x : Nat → Name → Nat, x = fun j'' => (cd j'').ψ' := ⟨_, rfl⟩
  obtain ⟨tgtDsA, htgtDsA⟩ : ∃ x : Nat → List AnnotTerm, x = fun j'' => (cd j'').DsA := ⟨_, rfl⟩
  obtain ⟨dsR, hdsR⟩ : ∃ x, x = d.dsRestored mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA := ⟨_, rfl⟩
  rw [← hΨdef, ← htgtCont, ← htgtLps, ← htgtDsA, ← hdsR]
  rw [← htgtCont, ← htgtLps, ← htgtDsA, ← hdsR] at hokTy hbelowR
  rw [← hΨdef, ← htgtCont, ← htgtLps, ← htgtDsA, ← hdsR] at hΨ
  -- ## the block's facts
  obtain ⟨-, hkb, hkRb, hnPb, -, -, -, hall⟩ := R.reps
  have hdk := R.dk
  have hk0 : 0 < d.k := by omega
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, hsv₀, hrep₀⟩ :=
    hall 0 (by rw [← hkb]; exact hk0)
  have hview := R.viewA J
  obtain ⟨hpinsA, hFFA, hLSA, hpIffMA⟩ := auxFacts_of_blockReps R.reps ψ
  have hlenD : (d.dsF J ψ).length = d.nP + cA.2 := hD.len ψ
  have htssBits : ∀ i, ∀ dd ∈ (d.tssF J ψ).getD i [], (dd.2.1 = 0 ↔ d.resSort.eval ψ = 0) :=
    hD.tssBits ψ
  have htssPi : ∀ i, ∀ dd ∈ (d.tssF J ψ).getD i [], dd.1 = 0 ∧ dd.2.1 ≤ 1 := hD.tssPiBits ψ
  have htssBelow : ∀ i, DomsBelow (d.nP + i) ((d.tssF J ψ).getD i []) := hD.tssBelow ψ
  have heissBelow : ∀ i, ∀ E ∈ (d.eissF J ψ).getD i [],
      Term.bvarsBelow (d.nP + i + ((d.tssF J ψ).getD i []).length) E.erase := hD.eissBelow ψ
  have hlenR : dsR.length = d.nP + cA.2 := by rw [hdsR, d.dsRestored_length, hlenD]
  have hppsLen : (d.ppsM 0 ψ).length = d.nP + d.nIdxAt 0 := hrep₀.former.len ψ
  have hparamsLen : (d.params ψ).length = d.nP := by
    unfold IndRepData.params
    rw [List.length_map, List.length_take, hppsLen]
    omega
  have hppsBelow : DomsBelow 0 ((d.ppsM 0 ψ).take d.nP) := domsBelow_take (R.ppsM_below hk0)
  have hpIff : ∀ ρ : Nat → V, Sat V (d.params ψ).reverse ρ ↔
      Sat V (((d.dsF J ψ).take d.nP).map (·.2.2)).reverse ρ := hrep₀.paramsIff J cA hJ ψ
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
  have hcopyPin : ∀ i, d.copyPos p.k J i → d.tgtsR J i - p.k < st.pins.length := by
    intro i hc
    have := R.tgtsA hk0 J i
    obtain ⟨-, hk⟩ := hc
    omega
  have hbelowDrop : DomsBelow d.nP (dsR.drop d.nP) := by
    have := DomsBelow.drop d.nP hbelowR
    rwa [Nat.zero_add] at this
  -- ## the spine, split at the parameters
  intro ρ ps fs hpsLen hfsLen hfit i hi hc
  have hfit' : SpineFit ρ ((dsR.take d.nP).map (·.2.2) ++ (dsR.drop d.nP).map (·.2.2)) (ps ++ fs) := by
    rw [← List.map_append, List.take_append_drop]; exact hfit
  obtain ⟨ps', fs', heq, hps, hfs⟩ := spineFit_append_inv hfit'
  have hps'len : ps'.length = d.nP := by
    rw [hps.length_eq, List.length_map, List.length_take, hlenR]; omega
  obtain ⟨hpe, hfe⟩ := List.append_inj heq (by rw [hpsLen, hps'len])
  rw [← hpe] at hps hfs
  rw [← hfe] at hfs
  -- ## the parameter frames
  have hsat : Sat V (d.params ψ).reverse (consList ps ρ) := by
    refine (hpIff _).mpr ?_
    rw [htake] at hps
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hps
    rwa [List.append_nil] at h
  have hρfit : SpineFit (consList ps ρ) (d.params ψ) (paramVals d.nP (consList ps ρ)) :=
    spineFit_params_of_sat hparamsLen hppsBelow hsat
  obtain ⟨τp, hτp⟩ : ∃ x, x = consList (paramVals d.nP (consList ps ρ)) (consList ps ρ) := ⟨_, rfl⟩
  have hτlt : ∀ k, k < d.nP → τp k = consList ps ρ k := by
    intro k hk; rw [hτp]; exact consList_paramVals_lt _ _ hk
  have hsatτ : Sat V (d.params ψ).reverse τp := by
    rw [hτp]
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V (consList ps ρ)) hρfit
    rwa [List.append_nil] at h
  have hfsτ : SpineFit τp ((dsR.drop d.nP).map (·.2.2)) fs :=
    spineFit_congr_below hbelowDrop (fun k hk => (hτlt k hk).symm) hfs
  -- ## the main work, at the frame ψ's Π-type lives on
  have hmain : WellDenotedV V (consList fs τp)
      (viaEntryAV (Ψ (d.tgtsR J i - p.k)) cA.2 0 i 0 ((d.tssR J ψ).getD i [])
        ((d.eissR J ψ).getD i [])) := by
    -- ## the target pin, and the container at it
    obtain ⟨j, hjdef⟩ : ∃ j, j = d.tgtsR J i - p.k := ⟨_, rfl⟩
    have hj : j < st.pins.length := by rw [hjdef]; exact hcopyPin i hc
    obtain ⟨pf, hbm, -⟩ := (R.pins j hj).1
    have hmm : (cd j).mm < (cd j).dJ.k := pf.mm
    have hpkj : p.k + j = d.tgtsR J i := by obtain ⟨-, hk⟩ := hc; omega
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
    have hmemF0 := FixKI.spineFit_getD_mem' hfsτ (by rw [hlenDrop]; exact hi)
    have hentryR : ((dsR.drop d.nP).map (·.2.2)).getD i default
        = d.restoreAV mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA i := by
      rw [List.getD_eq_getElem?_getD, hdsR,
        d.dsRestored_drop_getElem? mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA hlenD hi]
      rfl
    rw [hentryR] at hmemF0
    have hc' : i ∈ ConLeche.recIdxOf (d.ksR J) ∧ p.k ≤ d.tgtsR J i := hc
    unfold IndRepData.restoreAV at hmemF0
    rw [if_pos hc', ← hjdef] at hmemF0
    simp only [htgtCont, htgtLps, htgtDsA] at hmemF0
    obtain ⟨σ₁, hσ₁⟩ : ∃ x, x = consList (fs.take i) τp := ⟨_, rfl⟩
    rw [← hσ₁] at hmemF0
    have hfsTake : (fs.take i).length = i := by rw [List.length_take, hfsLen]; omega
    obtain ⟨args, hargs⟩ : ∃ x, x = (cd j).DsA.map (·.liftN (i + ((d.tssR J ψ).getD i []).length) 0)
        ++ (d.eissR J ψ).getD i [] := ⟨_, rfl⟩
    rw [← hargs] at hmemF0
    have hbitsT : ∀ dd ∈ (d.tssR J ψ).getD i [], (dd.2.1 = 0 ↔ b₀ = 0) :=
      fun dd hdd => by rw [hbits i hc dd hdd]
    have hmemF := hmemF0
    rw [interp_mkPisAV_piTele (B := fun as' => interp V (consList as' σ₁)
        (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ') args))
      (acc := []) hbitsT (fun as' _ => rfl)] at hmemF
    -- ## the restored entry, graded at the field's own frame
    have hvalsEq : (List.range d.nP).reverse.map τp = paramVals d.nP τp := by
      unfold paramVals
      have h0 := map_paramBvarsAt_interp (nP := d.nP) (e := 0) (ρp := τp) (σ := τp)
        (fun k => by rw [Nat.add_zero])
      rw [Nat.add_zero] at h0
      exact h0.symm
    have hρpush : consList (paramVals d.nP τp) (fun k => τp (k + d.nP)) = τp := by
      rw [← hvalsEq]; exact consList_range_reverse d.nP τp
    have hpvLen : (paramVals d.nP τp).length = d.nP := by
      unfold paramVals paramBvarsAt; simp
    have hps' : SpineFit (fun k => τp (k + d.nP)) ((dsR.take d.nP).map (·.2.2))
        (paramVals d.nP τp) := by
      have h := spineFit_of_sat (Δ₀ := []) (by rw [List.append_nil]; exact (hpIff τp).mp hsatτ)
      rw [List.length_map, List.length_take, hlenD,
        show min d.nP (d.nP + cA.2) = d.nP from by omega, hvalsEq, ← htake] at h
      exact h
    have hfitFull : SpineFit (fun k => τp (k + d.nP)) (dsR.map (·.2.2))
        (paramVals d.nP τp ++ fs) := by
      rw [← List.take_append_drop d.nP dsR, List.map_append]
      refine SpineFit.append hps' ?_
      rw [hρpush]
      exact hfsτ
    obtain ⟨e, he⟩ : ∃ e, (d.dsF J ψ)[d.nP + i]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hget : dsR[d.nP + i]? = some (e.1, e.2.1,
        d.restoreAV mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA i) := by
      rw [hdsR, d.dsRestored_getElem?, he]
      simp only [Option.map_some, Option.some.injEq]
      rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)), Nat.add_sub_cancel_left]
    have hfitPre : SpineFit (fun k => τp (k + d.nP)) ((dsR.take (d.nP + i)).map (·.2.2))
        (paramVals d.nP τp ++ fs.take i) := by
      have h := hfitFull
      rw [← List.take_append_drop (d.nP + i) dsR, List.map_append] at h
      obtain ⟨as₁, as₂, heq', h₁, -⟩ := spineFit_append_inv h
      have heq'' : (paramVals d.nP τp ++ fs.take i) ++ fs.drop i = as₁ ++ as₂ := by
        rw [List.append_assoc, List.take_append_drop]; exact heq'
      have hlen₁ : as₁.length = d.nP + i := by
        rw [h₁.length_eq, List.length_map, List.length_take, hlenR]; omega
      obtain ⟨hpe', -⟩ := List.append_inj heq'' (by
        rw [hlen₁, List.length_append, hpvLen, hfsTake])
      rw [hpe']
      exact h₁
    have hokEntry : WellDenoted V σ₁ (d.restoreAV mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA i) := by
      have h := wellDenoted_mkPisAV_dom (hokTy (fun k => τp (k + d.nP))).1
        (paramVals d.nP τp ++ fs.take i) (d.nP + i) _ hget hfitPre
      rw [consList_append, hρpush, ← hσ₁] at h
      exact h
    have hokEntryV : AnnotValid V σ₁ (d.restoreAV mpAux.base2 ψ p.k J tgtCont tgtLps tgtDsA i) := by
      have h := annotValid_mkPisAV_dom (hokTy (fun k => τp (k + d.nP))).2
        (paramVals d.nP τp ++ fs.take i) (d.nP + i) _ hget hfitPre
      rw [consList_append, hρpush, ← hσ₁] at h
      exact h
    unfold IndRepData.restoreAV at hokEntry hokEntryV
    rw [if_pos hc', ← hjdef] at hokEntry hokEntryV
    simp only [htgtCont, htgtLps, htgtDsA] at hokEntry hokEntryV
    rw [← hargs] at hokEntry hokEntryV
    -- ## the container application under the telescope, graded and fitting
    have hokApp : ∀ as', SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as' →
        WellDenotedV V (consList as' σ₁)
          (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ') args) :=
      fun as' has' => ⟨wellDenoted_mkPisAV_body hokEntry as' has',
        annotValid_mkPisAV_body hokEntryV as' has'⟩
    have hargsRead : ∀ as', as'.length = ((d.tssR J ψ).getD i []).length →
        args.map (interp V (consList as' σ₁))
          = (cd j).DsA.map (interp V τp) ++
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
    have hfits : ∀ as', SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as' →
        SpineFit (consList as' σ₁) ((cd j).dJ.params (cd j).ψ') ((cd j).DsA.map (interp V τp)) ∧
        SpineFit (consList ((cd j).DsA.map (interp V τp)) (consList as' σ₁))
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
        (by rw [hargsLen]; exact Nat.le_refl _) (hokApp as' has').1 (by rw [hB])
      rw [hargsLen, List.take_of_length_le (Nat.le_refl _), hargsRead as' hlen'] at hsp
      have hsplitJ : ((cd j).dJ.ppsM (cd j).mm (cd j).ψ').map (·.2.2)
          = (((cd j).dJ.ppsM (cd j).mm (cd j).ψ').take (cd j).dJ.nP).map (·.2.2) ++
            (((cd j).dJ.ppsM (cd j).mm (cd j).ψ').drop (cd j).dJ.nP).map (·.2.2) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplitJ] at hsp
      obtain ⟨as₁, as₂, heq', h₁, h₂⟩ := spineFit_append_inv hsp
      have hlen₁ : as₁.length = (cd j).dJ.nP := by
        rw [h₁.length_eq, List.length_map, List.length_take, hppsJlen]; omega
      obtain ⟨rfl, rfl⟩ := List.append_inj heq' (by rw [hlen₁, List.length_map, hDsAlen])
      refine ⟨?_, h₂⟩
      have hsat₁ : Sat V ((((cd j).dJ.ppsM (cd j).mm (cd j).ψ').take (cd j).dJ.nP).map (·.2.2)).reverse
          (consList ((cd j).DsA.map (interp V τp)) (consList as' σ₁)) := by
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
      have hshift' : (fun k => consList ((cd j).DsA.map (interp V τp)) (consList as' σ₁)
            (k + (cd j).dJ.nP)) = consList as' σ₁ := by
        funext k
        rw [show (cd j).dJ.nP = ((cd j).DsA.map (interp V τp)).length from by
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
    have hxfold : ∀ as', SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as' →
        as'.foldl SetTheory.app (fs.getD i pt) ∈ˢ interp V (consList as' σ₁)
          (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ') args) := by
      intro as' has'
      by_cases hb0 : b₀ = 0
      · rw [hb0] at hmemF
        have := piTele_fold_zero hmemF (fun as'' hfit'' => by
            rw [List.nil_append]; exact hzeroJ hb0 as'' (fitsS_teleOfFields.mp hfit''))
          as' (fitsS_teleOfFields.mpr has')
        rwa [List.nil_append] at this
      · have := piTele_fold hb0 hmemF (fitsS_teleOfFields.mpr has')
        rwa [List.nil_append] at this
    -- ## the COPY member at the block's parameters and the field's index readings
    have htgtLt : d.tgtsR J i < d.k := R.tgtsA hk0 J i
    obtain ⟨sT, cvTT, cvRT, capsT, mIT, rPT, rulesT, -, -, -, hsvT, hrepT⟩ :=
      hall (d.tgtsR J i) (by rw [← hkb]; exact htgtLt)
    have hppsTbelow : DomsBelow 0 (d.ppsM (d.tgtsR J i) ψ) := hrepT.former.below ψ
    have hppsTlen : (d.ppsM (d.tgtsR J i) ψ).length = d.nP + d.nIdxAt (d.tgtsR J i) :=
      hrepT.former.len ψ
    have htEq : p.k + ((cd j).base + (cd j).mm) = d.tgtsR J i := by rw [hbm]; exact hpkj
    have hIdsBelow : DomsBelow (cd j).dJ.nP
        (((cd j).dJ.ppsM (cd j).mm (cd j).ψ').drop (cd j).dJ.nP) := by
      have := DomsBelow.drop (cd j).dJ.nP (hrepJ.former.below (cd j).ψ')
      rwa [Nat.zero_add] at this
    have hIdsTbelow : DomsBelow d.nP ((d.ppsM (d.tgtsR J i) ψ).drop d.nP) := by
      have := DomsBelow.drop d.nP hppsTbelow
      rwa [Nat.zero_add] at this
    obtain ⟨Ebody, hEbody⟩ : ∃ x, x = AnnotTerm.mkAppN
      (mpAux.base2.acval (d.memberName (d.tgtsR J i)) ψ)
      (paramBvarsAt d.nP (d.nP + i + ((d.tssR J ψ).getD i []).length) ++
        (d.eissR J ψ).getD i []) := ⟨_, rfl⟩
    have hisAt : ∀ as' : List V, SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as' →
        SpineFit (consList ((cd j).DsA.map (interp V τp)) τp)
          ((cd j).dJ.IdsM (cd j).mm (cd j).ψ')
          (((d.eissR J ψ).getD i []).map (interp V (consList as' σ₁))) := by
      intro as' has'
      obtain ⟨-, hfit₂⟩ := hfits as' has'
      unfold IndRepData.IdsM at hfit₂ ⊢
      refine spineFit_congr_below hIdsBelow (fun k hk => ?_) hfit₂
      rw [consList_apply_lt' _ _ (by rw [List.length_map, hDsAlen]; exact hk),
        consList_apply_lt' _ _ (by rw [List.length_map, hDsAlen]; exact hk)]
    have hpreadAt : ∀ as' : List V, as'.length = ((d.tssR J ψ).getD i []).length →
        (paramBvarsAt d.nP (d.nP + i + ((d.tssR J ψ).getD i []).length)).map
          (interp V (consList as' σ₁)) = paramVals d.nP τp := by
      intro as' hlen'
      rw [hσ₁, ← consList_append, show d.nP + i + ((d.tssR J ψ).getD i []).length
          = d.nP + (fs.take i ++ as').length from by
        rw [List.length_append, hfsTake, hlen']; omega, interp_paramBvarsAt_consList]
    have hTfacts : ∀ as', SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as' →
        WellDenotedV V (consList as' σ₁) Ebody ∧
        interp V (consList as' σ₁) Ebody ∈ˢ (univ (d.w ψ) : V) := by
      intro as' has'
      have hlen' : as'.length = ((d.tssR J ψ).getD i []).length := by
        rw [has'.length_eq, List.length_map]
      have hpread := hpreadAt as' hlen'
      have hfitP : SpineFit (consList as' σ₁)
          (((d.ppsM (d.tgtsR J i) ψ).take d.nP).map (·.2.2)) (paramVals d.nP τp) := by
        have h := spineFit_of_sat (Δ₀ := [])
          (by rw [List.append_nil]; exact (hpIffMA (d.tgtsR J i) htgtLt τp).mp hsatτ)
        rw [List.length_map, List.length_take, hppsTlen,
          show min d.nP (d.nP + d.nIdxAt (d.tgtsR J i)) = d.nP from by omega, hvalsEq] at h
        exact spineFit_congr_below (domsBelow_take hppsTbelow)
          (fun k hk => absurd hk (Nat.not_lt_zero _)) h
      have his := hisAt as' has'
      have hidxA : SpineFit τp (d.IdsM (d.tgtsR J i) ψ)
          (((d.eissR J ψ).getD i []).map (interp V (consList as' σ₁))) := by
        rw [← htEq]
        exact (hokJ.idx.idxIff τp hsatτ _).mpr his
      have hidxF : SpineFit (consList (paramVals d.nP τp) (consList as' σ₁))
          (((d.ppsM (d.tgtsR J i) ψ).drop d.nP).map (·.2.2))
          (((d.eissR J ψ).getD i []).map (interp V (consList as' σ₁))) := by
        unfold IndRepData.IdsM at hidxA
        exact spineFit_congr_below hIdsTbelow
          (fun k hk => (consList_paramVals_lt τp (consList as' σ₁) hk).symm) hidxA
      have hfitAll : SpineFit (consList as' σ₁) ((d.ppsM (d.tgtsR J i) ψ).map (·.2.2))
          ((paramBvarsAt d.nP (d.nP + i + ((d.tssR J ψ).getD i []).length) ++
            (d.eissR J ψ).getD i []).map (interp V (consList as' σ₁))) := by
        rw [List.map_append, hpread,
          show (d.ppsM (d.tgtsR J i) ψ).map (·.2.2)
            = ((d.ppsM (d.tgtsR J i) ψ).take d.nP).map (·.2.2) ++
              ((d.ppsM (d.tgtsR J i) ψ).drop d.nP).map (·.2.2) from by
            rw [← List.map_append, List.take_append_drop]]
        exact SpineFit.append hfitP hidxF
      have h := wellDenotedV_mkAppN_of_spineFit (σ := consList as' σ₁)
        (ds := d.ppsM (d.tgtsR J i) ψ) (C := .sort (d.w ψ))
        (f := mpAux.base2.acval (d.memberName (d.tgtsR J i)) ψ)
        (as := paramBvarsAt d.nP (d.nP + i + ((d.tssR J ψ).getD i []).length) ++
          (d.eissR J ψ).getD i [])
        ((hFFA (d.tgtsR J i) htgtLt).2.2.2 _)
        ⟨mpAux.base2.acval_wellDenoted _ ψ _, mpAux.acval_validV _ ψ _⟩
        (fun a ha => by
          rcases List.mem_append.mp ha with h' | h'
          · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h'
            exact wellDenotedV_bvar _ _
          · exact (WellDenotedV.mkAppN_args (hokApp as' has')).2 a
              (by rw [hargs]; exact List.mem_append_right _ h'))
        ((hFFA (d.tgtsR J i) htgtLt).2.2.1 _)
        hfitAll
      rw [← hEbody] at h
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [interp_sort] at h2
      exact h2
    -- ## the towers at the leaf frame
    have htl : ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i [])
        = liftDoms (cA.2 - i) 0 ((d.tssR J ψ).getD i []) := ihTeleAtR_leaf _ _ _
    have hshiftF : shiftE (cA.2 - i) 0 (consList fs τp) = σ₁ := by
      have h := shiftE_fieldsFrame (nF := cA.2) (i := i) (ρp := τp) hfsLen ([] : List V)
      simp only [List.length_nil, consList_nil] at h
      rw [hσ₁]; exact h
    have hfitBridge : ∀ as : List V,
        SpineFit (consList fs τp) ((ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i [])).map (·.2.2)) as ↔
          SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as := by
      intro as
      rw [htl, spineFit_liftDoms, hshiftF]
    have htowerJeq : mkPisAV (ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i []))
        ((AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ') args).liftN
          (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length))
        = (mkPisAV ((d.tssR J ψ).getD i [])
            (AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ')
              args)).liftN (cA.2 - i) 0 := by
      rw [liftN_mkPisAV, htl]
    have hTowerJWD : WellDenotedV V (consList fs τp)
        (mkPisAV (ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i []))
          ((AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ') args).liftN
            (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length))) := by
      rw [htowerJeq, WellDenotedV_liftN, hshiftF]
      exact ⟨hokEntry, hokEntryV⟩
    have hTowerJMem : fs.getD i pt ∈ˢ interp V (consList fs τp)
        (mkPisAV (ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i []))
          ((AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ') args).liftN
            (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length))) := by
      rw [htowerJeq, interp_liftN, hshiftF]
      exact hmemF0
    have hentryWD : ∀ (k : Nat) (dd : Nat × Nat × AnnotTerm),
        (ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i []))[k]? = some dd →
        ∀ as : List V, SpineFit (consList fs τp)
          (((ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i [])).take k).map (·.2.2)) as →
        WellDenotedV V (consList as (consList fs τp)) dd.2.2 :=
      fun k dd hk as hsp => ⟨wellDenoted_mkPisAV_dom hTowerJWD.1 as k dd hk hsp,
        annotValid_mkPisAV_dom hTowerJWD.2 as k dd hk hsp⟩
    -- the copy's carrier, at the leaf frame
    have hTbody : ∀ as : List V,
        SpineFit (consList fs τp) ((ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i [])).map (·.2.2)) as →
        WellDenotedV V (consList as (consList fs τp))
          (Ebody.liftN (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length)) ∧
        interp V (consList as (consList fs τp))
          (Ebody.liftN (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length)) ∈ˢ (univ (d.w ψ) : V) := by
      intro as hsp
      have has' := (hfitBridge as).mp hsp
      have hasLen : as.length = ((d.tssR J ψ).getD i []).length := by
        rw [has'.length_eq, List.length_map]
      have hsh : shiftE (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length)
          (consList as (consList fs τp)) = consList as σ₁ := by
        rw [Nat.zero_add, ← hasLen, hσ₁]
        exact shiftE_fieldsFrame hfsLen as
      rw [WellDenotedV_liftN, interp_liftN, hsh]
      exact hTfacts as has'
    have hTowerCopy : WellDenoted V (consList fs τp)
        (mkPisAV (ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i []))
          (Ebody.liftN (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length))) :=
      wellDenoted_mkPisAV_of (fun k dd hk as hsp => (hentryWD k dd hk as hsp).1)
        (fun as hsp => (hTbody as hsp).1.1)
    -- ## ψ's Π-type at the parameter frame
    have hτpsA : (paramBvarsAt d.nP d.nP).map (interp V (consList ps ρ))
        = paramVals d.nP (consList ps ρ) := rfl
    have htyped := R.final_typed (ρ₀ := consList ps ρ) (psA := paramBvarsAt d.nP d.nP)
      (paramBvarsAt_length _ _) hρfit tbl₀ hj
    rw [hτpsA, ← hτp, ← hΨdef] at htyped
    obtain ⟨hΨwd0, hTyWd, hΨmem0⟩ := htyped
    have hΨwd : WellDenotedV V τp (Ψ (d.tgtsR J i - p.k)) := by rw [← hjdef]; exact hΨwd0
    have hΨmem : interp V τp (Ψ (d.tgtsR J i - p.k)) ∈ˢ interp V τp
        ((cd j).dJ.psiTyAV mpAux.base2 (cd j).ψ' (cd j).DsA
          (d.psiL mpAux.base2 ψ p.k (cd j).base) (d.psiPinsT (cd j).dJ.nP) (cd j).mm) := by
      rw [← hjdef]; exact hΨmem0
    have hTy : (cd j).dJ.psiTyAV mpAux.base2 (cd j).ψ' (cd j).DsA
          (d.psiL mpAux.base2 ψ p.k (cd j).base) (d.psiPinsT (cd j).dJ.nP) (cd j).mm
        = mkPisAV (instSeqDoms (cd j).DsA ((cd j).DsA.length - 1)
            (rebit ((cd j).dJ.bb (cd j).ψ')
              ((cd j).dJ.motDataAV mpAux.base2 (cd j).ψ' (cd j).mm)))
            (ConLeche.Model.AnnotTerm.instSeq (cd j).DsA
              ((cd j).DsA.length - 1 +
                (rebit ((cd j).dJ.bb (cd j).ψ')
                  ((cd j).dJ.motDataAV mpAux.base2 (cd j).ψ' (cd j).mm)).length)
              ((famAppAV (d.psiL mpAux.base2 ψ p.k (cd j).base (cd j).mm)
                (d.psiPinsT (cd j).dJ.nP (cd j).mm) (cd j).dJ.nP
                ((cd j).dJ.nP + (cd j).dJ.nIdxs.getD (cd j).mm 0)
                ((cd j).dJ.nIdxs.getD (cd j).mm 0)).liftN 1 0)) := by
      unfold IndRepData.psiTyAV
      rw [instSeq_mkPisAV _ _ _ _ (by omega)]
    -- ## the motive spine: the index readings and the field applied
    have hDsLenτ : ((cd j).DsA.map (interp V τp)).length = (cd j).dJ.nP := by
      rw [List.length_map, hDsAlen]
    have hxAt : ∀ as' : List V, SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as' →
        as'.foldl SetTheory.app (fs.getD i pt) ∈ˢ ((cd j).DsA.map (interp V τp) ++
          ((d.eissR J ψ).getD i []).map (interp V (consList as' σ₁))).foldl SetTheory.app
            (interp V τp (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ')) := by
      intro as' has'
      have h := hxfold as' has'
      rw [interp_mkAppN_map, hargsRead as' (by rw [has'.length_eq, List.length_map]),
        interp_closed (V := V) (mpAux.base2.cval_closedL _ _) _ τp] at h
      exact h
    have hisLenM : ∀ as' : List V,
        (((d.eissR J ψ).getD i []).map (interp V (consList as' σ₁))).length
          = (cd j).dJ.nIdxs.getD (cd j).mm 0 := by
      intro as'
      rw [List.length_map, heissLen, ← hnIdxJ]
      rfl
    have hfitM : ∀ as' : List V, SpineFit σ₁ (((d.tssR J ψ).getD i []).map (·.2.2)) as' →
        SpineFit (consList ((cd j).DsA.map (interp V τp)) τp)
          (((cd j).dJ.motDataAV mpAux.base2 (cd j).ψ' (cd j).mm).map (·.2.2))
          (((d.eissR J ψ).getD i []).map (interp V (consList as' σ₁)) ++
            [as'.foldl SetTheory.app (fs.getD i pt)]) := by
      intro as' has'
      have hsplit : ((cd j).dJ.motDataAV mpAux.base2 (cd j).ψ' (cd j).mm).map (·.2.2)
          = (rebit (pwBit (cd j).ψ' ConLeche.PropWhen.never)
              (((cd j).dJ.ipss (cd j).ψ').getD (cd j).mm [])).map (·.2.2) ++
            [famAppAV (((cd j).dJ.Ls mpAux.base2 (cd j).ψ').getD (cd j).mm default)
              ((cd j).dJ.pinsOf (cd j).ψ' (cd j).mm) (cd j).dJ.nP
              ((cd j).dJ.nP + (cd j).dJ.nIdxs.getD (cd j).mm 0)
              ((cd j).dJ.nIdxs.getD (cd j).mm 0)] := by
        simp [IndRepData.motDataAV]
      rw [hsplit]
      refine SpineFit.append ?_ ⟨?_, trivial⟩
      · rw [rebit_map_dom, (cd j).dJ.ipss_getD (cd j).ψ' hmm]
        exact hisAt as' has'
      · rw [(cd j).dJ.Ls_getD_eq mpAux.base2 (cd j).ψ' hmm,
          interp_famAppAV_pins (mpAux.base2.cval_closedL _ _) _ _ (hisLenM as')]
        unfold IndRepData.pinsOf
        rw [hokJ.pins, interp_paramBvarsAt_self hDsLenτ,
          interp_closed (V := V) (mpAux.base2.cval_closedL _ _) _ τp]
        exact hxAt as' has'
    -- ## the field applied to the telescope's variables, graded
    have hxWD : ∀ as : List V,
        SpineFit (consList fs τp) ((ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i [])).map (·.2.2)) as →
        WellDenotedV V (consList as (consList fs τp))
          (AnnotTerm.mkAppN (.bvar (cA.2 - 1 - i + 0 + ((d.tssR J ψ).getD i []).length))
            (teleVarsAV ((d.tssR J ψ).getD i []).length)) := by
      intro as hsp
      have has' := (hfitBridge as).mp hsp
      have hasLen : as.length = ((d.tssR J ψ).getD i []).length := by
        rw [has'.length_eq, List.length_map]
      have hshiftM : shiftE ((d.tssR J ψ).getD i []).length 0 (consList as (consList fs τp))
          = consList fs τp := by
        rw [← hasLen]; exact shiftE_consList _ _
      have hbv : consList as (consList fs τp)
          (cA.2 - 1 - i + 0 + ((d.tssR J ψ).getD i []).length) = fs.getD i pt := by
        rw [Nat.add_zero, ← hasLen, consList_apply_add, consList_apply_lt' fs _ (by omega),
          show fs.length - 1 - (cA.2 - 1 - i) = i from by omega]
      have h := wellDenotedV_mkAppN_of_spineFit (σ := consList as (consList fs τp))
        (ds := liftDoms ((d.tssR J ψ).getD i []).length 0
          (ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i [])))
        (C := ((AnnotTerm.mkAppN (mpAux.base2.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ')
            args).liftN (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length)).liftN
          ((d.tssR J ψ).getD i []).length
          (0 + (ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i [])).length))
        (f := .bvar (cA.2 - 1 - i + 0 + ((d.tssR J ψ).getD i []).length))
        (as := teleVarsAV ((d.tssR J ψ).getD i []).length)
        (by rw [← liftN_mkPisAV, WellDenotedV_liftN, hshiftM]; exact hTowerJWD)
        ⟨by simp, by simp⟩
        (fun a ha => by obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; exact ⟨by simp, by simp⟩)
        (by
          rw [← liftN_mkPisAV, interp_liftN, hshiftM, interp_bvar, hbv]
          exact hTowerJMem)
        (by rw [spineFit_liftDoms, hshiftM, map_teleVarsAV_interp' hasLen]; exact hsp)
      exact h.1
    -- ## the transport's body
    have hEisRead : ∀ as : List V, as.length = ((d.tssR J ψ).getD i []).length →
        ((d.eissR J ψ).getD i []).map (fun E => interp V (consList as (consList fs τp))
            (ihIdxAtM cA.2 0 i 0 ((d.tssR J ψ).getD i []).length E))
          = ((d.eissR J ψ).getD i []).map (interp V (consList as σ₁)) := by
      intro as hasLen
      refine List.map_congr_left fun E _ => ?_
      rw [← hasLen, interp_ihIdxAtM_leaf hfsLen as E, hσ₁]
    have hxVal : ∀ as : List V, as.length = ((d.tssR J ψ).getD i []).length →
        interp V (consList as (consList fs τp))
          (AnnotTerm.mkAppN (.bvar (cA.2 - 1 - i + 0 + ((d.tssR J ψ).getD i []).length))
            (teleVarsAV ((d.tssR J ψ).getD i []).length))
          = as.foldl SetTheory.app (fs.getD i pt) := by
      intro as hasLen
      have hbv : consList as (consList fs τp)
          (cA.2 - 1 - i + 0 + ((d.tssR J ψ).getD i []).length) = fs.getD i pt := by
        rw [Nat.add_zero, ← hasLen, consList_apply_add, consList_apply_lt' fs _ (by omega),
          show fs.length - 1 - (cA.2 - 1 - i) = i from by omega]
      rw [interp_mkAppN_map, interp_bvar, map_teleVarsAV_interp' hasLen, hbv]
    have hbodyFacts : ∀ as : List V,
        SpineFit (consList fs τp) ((ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i [])).map (·.2.2)) as →
        WellDenotedV V (consList as (consList fs τp))
          (viaBodyAV (Ψ (d.tgtsR J i - p.k)) cA.2 0 i 0 ((d.tssR J ψ).getD i []).length
            ((d.eissR J ψ).getD i [])) ∧
        interp V (consList as (consList fs τp))
          (viaBodyAV (Ψ (d.tgtsR J i - p.k)) cA.2 0 i 0 ((d.tssR J ψ).getD i []).length
            ((d.eissR J ψ).getD i []))
          ∈ˢ interp V (consList as (consList fs τp))
              (Ebody.liftN (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length)) := by
      intro as hsp
      have has' := (hfitBridge as).mp hsp
      have hasLen : as.length = ((d.tssR J ψ).getD i []).length := by
        rw [has'.length_eq, List.length_map]
      have hshiftLeaf : shiftE (0 + cA.2 + 0 + ((d.tssR J ψ).getD i []).length) 0
          (consList as (consList fs τp)) = τp := by
        rw [← hasLen]; exact shiftE_leafFrame hfsLen as
      have hshT : shiftE (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length)
          (consList as (consList fs τp)) = consList as σ₁ := by
        rw [Nat.zero_add, ← hasLen, hσ₁]
        exact shiftE_fieldsFrame hfsLen as
      constructor
      · unfold viaBodyAV
        have h := wellDenotedV_mkAppN_of_spineFit (σ := consList as (consList fs τp))
          (ds := liftDoms (0 + cA.2 + 0 + ((d.tssR J ψ).getD i []).length) 0
            (instSeqDoms (cd j).DsA ((cd j).DsA.length - 1)
              (rebit ((cd j).dJ.bb (cd j).ψ')
                ((cd j).dJ.motDataAV mpAux.base2 (cd j).ψ' (cd j).mm))))
          (C := (ConLeche.Model.AnnotTerm.instSeq (cd j).DsA
              ((cd j).DsA.length - 1 +
                (rebit ((cd j).dJ.bb (cd j).ψ')
                  ((cd j).dJ.motDataAV mpAux.base2 (cd j).ψ' (cd j).mm)).length)
              ((famAppAV (d.psiL mpAux.base2 ψ p.k (cd j).base (cd j).mm)
                (d.psiPinsT (cd j).dJ.nP (cd j).mm) (cd j).dJ.nP
                ((cd j).dJ.nP + (cd j).dJ.nIdxs.getD (cd j).mm 0)
                ((cd j).dJ.nIdxs.getD (cd j).mm 0)).liftN 1 0)).liftN
            (0 + cA.2 + 0 + ((d.tssR J ψ).getD i []).length)
            (0 + (instSeqDoms (cd j).DsA ((cd j).DsA.length - 1)
              (rebit ((cd j).dJ.bb (cd j).ψ')
                ((cd j).dJ.motDataAV mpAux.base2 (cd j).ψ' (cd j).mm))).length))
          (f := (Ψ (d.tgtsR J i - p.k)).liftN (0 + cA.2 + 0 + ((d.tssR J ψ).getD i []).length) 0)
          (as := ((d.eissR J ψ).getD i []).map
              (ihIdxAtM cA.2 0 i 0 ((d.tssR J ψ).getD i []).length) ++
            [AnnotTerm.mkAppN (.bvar (cA.2 - 1 - i + 0 + ((d.tssR J ψ).getD i []).length))
              (teleVarsAV ((d.tssR J ψ).getD i []).length)])
          (by rw [← liftN_mkPisAV, ← hTy, WellDenotedV_liftN, hshiftLeaf]; exact hTyWd)
          (by rw [WellDenotedV_liftN, hshiftLeaf]; exact hΨwd)
          (fun a ha => by
            rcases List.mem_append.mp ha with h' | h'
            · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp h'
              unfold ihIdxAtM
              rw [AnnotTerm.liftN_zero, Nat.add_zero, ← hasLen, WellDenotedV_liftN,
                shiftE_fieldsFrame hfsLen as, ← hσ₁]
              exact (WellDenotedV.mkAppN_args (hokApp as has')).2 E
                (by rw [hargs]; exact List.mem_append_right _ hE)
            · rw [List.mem_singleton] at h'
              rw [h']; exact hxWD as hsp)
          (by rw [← liftN_mkPisAV, ← hTy, interp_liftN, interp_liftN, hshiftLeaf]; exact hΨmem)
          (by
            rw [spineFit_liftDoms, hshiftLeaf, List.map_append, List.map_singleton,
              hxVal as hasLen]
            simp only [List.map_map, Function.comp_def]
            rw [hEisRead as hasLen]
            refine (spineFit_instSeqDoms_iff (xs := []) _ _ _ (fun hne => by
                rw [hDsAlen, List.length_nil]
                have h1 : 1 ≤ (cd j).dJ.nP := by
                  rw [← hDsAlen]
                  exact Nat.pos_of_ne_zero (fun h0 => hne (List.eq_nil_of_length_eq_zero h0))
                omega)).mpr ?_
            simp only [consList_nil, rebit_map_dom]
            exact hfitM as has')
        exact h.1
      · rw [interp_liftN, hshT, hEbody, interp_mkAppN_map, List.map_append,
          hpreadAt as hasLen, interp_closed (V := V) (mpAux.base2.cval_closedL _ _) _ τp,
          ← hasLen, interp_viaBodyAV_leaf hfsLen hi as _ _, hσ₁]
        exact hΨ τp hsatτ i hi hc fs hfsLen hfsτ as (by rw [← hσ₁]; exact has')
    -- ## the λ-tower
    have hzb : ∀ dd ∈ ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i []), (b₀ = 0 ↔ dd.2.1 = 0) := by
      intro dd hdd
      obtain ⟨dd', hdd', he⟩ := mem_ihTeleAtGo hdd
      rw [he, hbits i hc dd' hdd']
    have hzeroT : ∀ as : List V,
        SpineFit (consList fs τp) ((ihTeleAtR cA.2 0 i 0 ((d.tssR J ψ).getD i [])).map (·.2.2)) as →
        b₀ = 0 → interp V (consList as (consList fs τp))
          (Ebody.liftN (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length)) ∈ˢ (univZero : V) := by
      intro as hsp h0
      have h := (hTbody as hsp).2
      have hw0 : d.w ψ = 0 := by show d.resSort.eval ψ = 0; exact hb₀iff.mp h0
      rw [hw0, univ_zero] at h
      exact h
    unfold viaEntryAV
    exact ⟨mkLamsAV_bits_wellDenoted (m := b₀)
        (T := Ebody.liftN (cA.2 - i) (0 + ((d.tssR J ψ).getD i []).length)) hzb
        (underTowerOk_of_wellDenoted hTowerCopy
          (fun as hsp => ⟨(hbodyFacts as hsp).1.1, (hbodyFacts as hsp).2, hzeroT as hsp⟩)),
      mkLamsAV_bits_validV (underTowerValid_of
        (fun k dd hk as hsp => (hentryWD k dd hk as hsp).2)
        (fun as hsp => (hbodyFacts as hsp).1.2))⟩
  -- ## back to the leaf frame: the entry is bounded at the parameters and
  -- the fields, and the two frames agree there
  have hbelowΨ : Term.bvarsBelow d.nP (Ψ (d.tgtsR J i - p.k)).erase := by
    rw [hΨdef]; exact R.final_below tbl₀ (hcopyPin i hc)
  have hbelowV : Term.bvarsBelow (d.nP + cA.2)
      (viaEntryAV (Ψ (d.tgtsR J i - p.k)) cA.2 0 i 0 ((d.tssR J ψ).getD i [])
        ((d.eissR J ψ).getD i [])).erase := by
    have h := viaEntryAV_below (nP := d.nP) (mm := 0) (o := 0) (l := 0) (nF := cA.2)
      (Ψ := Ψ (d.tgtsR J i - p.k)) (tl := (d.tssR J ψ).getD i [])
      (Eis := (d.eissR J ψ).getD i []) hi
      (by rw [Nat.add_zero]; exact hbelowΨ)
      (by rw [Nat.add_zero, hview.2.2.2]; exact htssBelow i)
      (fun E hE => by
        rw [hview.2.2.1] at hE
        rw [Nat.add_zero, hview.2.2.2]
        exact heissBelow i E hE)
    simpa using h
  have hagree : AgreeOff (fun k => d.nP + cA.2 ≤ k) (consList fs τp) (consList fs (consList ps ρ)) := by
    intro k hk
    by_cases h : k < fs.length
    · rw [consList_apply_lt' _ _ h, consList_apply_lt' _ _ h]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + fs.length := ⟨k - fs.length, by omega⟩
      rw [consList_apply_add, consList_apply_add]
      exact hτlt k' (by omega)
  rw [consList_append]
  exact ⟨(WellDenoted_congr_noBVar _ (NoBVar_of_bvarsBelow hbelowV (fun _ h => h)) hagree).mp hmain.1,
    (AnnotValid_congr_noBVar _ (NoBVar_of_bvarsBelow hbelowV (fun _ h => h)) hagree).mp hmain.2⟩

end ConLeche.Model
