module

public import ConLeche.Model.Inductives.RoundTripTransport
public section

/-!
# The TRANSPORT arm of R1 (task #279 M-C′, DESIGN §M.38)

`RoundTripRunR1.lean` proves R1 at the run for groups WITHOUT
transports (`hnoT`).  At a transport — a copy's field recursive into
the copy of another pin, ordinary for the container — ψ⁻¹'s mixed
value is its fold at the target copy and ψ's value the target pin's
term at that: their composition is R1 at the TARGET COPY, which is the
SAME induction's hypothesis (R1 is one induction over the scratch
block, DESIGN §M.32), so no order is needed on this side.

This module, at a FINITARY scratch block (`hfinA`), replaces the
`hnoT`-premised pieces of `r1_hstep`:

* **`mixed_shadowP`** — the mixed values shadow the fields off the
  REPLACED positions (a hypothesis position is replaced);
* **`readA_agree`/`readM_agree`/`readJ_agree`** — the copy's readings
  at a position read alike at ψ⁻¹'s frame `ρ` and at the pushed frame,
  and under the fields' prefix and the mixed prefix (they mention no
  recursive position); the container's at the mixed prefix are the
  copy's at the fields' (`kindR`, `hnbP`);
* **`es_inv'`** — the container's index readings at the mixed values
  are the copy's at the fields (`hnbP`'s result clause: no replaced
  position is mentioned);
* **`pos_inv'`** — the per-position facts of `r1_step` with the third
  arm PROVED at a transport from the induction hypothesis at the
  target copy;
* **`fitMixed_transport`** — the mixed values fit the container's
  telescope, a transport position by `invFold_mem` at the target pin
  (`containerDom_transport` + `transport_fits`);
* **`r1_hstep'`/`r1At_transport`/`r1At_transport_all`** — R1 at the
  run with `hnoT` gone.

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

/-! ## Shadows and readings -/

omit R in
/-- **The mixed values shadow the fields off the REPLACED positions**:
a hypothesis position of ψ⁻¹ is container-recursive (a hypothesis
position of ψ) or a transport. -/
theorem mixed_shadowP (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V} {j J : Nat} (vs' : List V) :
    ShadowRelP (replaced (IndRepData.psiUseIh (cd j).dJ J)
        (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J))
      vs' (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs') := by
  refine ⟨d.invMixed_length _ _ _ _ _ _ _ _ _ _, fun l hl hr => ?_⟩
  unfold IndRepData.invMixed
  rw [mixedVals_getD _ _ _ _ hl, if_neg]
  intro hu
  apply hr
  unfold IndRepData.invUseIh at hu
  obtain ⟨-, hA, hk⟩ := of_decide_eq_true hu
  by_cases hJr : l ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J)
  · exact Or.inl (by unfold IndRepData.psiUseIh; exact decide_eq_true hJr)
  · refine Or.inr ?_
    unfold IndRepData.psiVia
    rw [if_pos ⟨hA, hJr, hk⟩]
    rfl

/-- **The copy's readings at a position read alike at `ρ` and at the
pushed frame** (they are bounded at the position's depth). -/
theorem readA_agree {ρ : Nat → V} {j : Nat} (hj : j < st.pins.length) {J : Nat}
    {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) {i : Nat} (hi : i < cA.2)
    (htssF : (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = []) {vs' : List V}
    (hlen : vs'.length = cA.2) :
    ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V (consList (vs'.take i) ρ))
      = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))) := by
  have hg := R.groupFacts hj
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hD := hf.ctor.2.2
  have htake : (vs'.take i).length = i := by rw [List.length_take]; omega
  rw [← hf.view.2.2.1]
  apply List.map_congr_left
  intro E hE
  have hEb : Term.bvarsBelow (d.nP + i) E.erase := by
    have := hD.eissBelow ψ i E (by rw [← hf.view.2.2.1]; exact hE)
    rwa [htssF, List.length_nil, Nat.add_zero] at this
  exact interp_congr_below V E (d.nP + i) _ _ hEb (fun l hl =>
    consList_agree_below (n := d.nP) (fun l' hl' => (push_agree ρ ρ l' hl').symm) _ l
      (by rw [htake]; omega))

/-- **The copy's readings under the mixed prefix are its readings under
the fields' prefix** (the mixed values shadow the fields off the copy's
recursive positions, which the readings do not mention). -/
theorem readM_agree {ρ : Nat → V} {j : Nat} (hj : j < st.pins.length) {J : Nat}
    {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) {i : Nat} (hi : i < cA.2)
    (htssF : (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = []) {vs' : List V}
    (hlen : vs'.length = cA.2) :
    ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V (consList
        ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
        (consList (paramVals d.nP ρ) ρ)))
      = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))) := by
  have hg := R.groupFacts hj
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hD := hf.ctor.2.2
  have htake : (vs'.take i).length = i := by rw [List.length_take]; omega
  obtain ⟨-, -, hnbE, -⟩ := FixCtorDataI.noBVar_entries hD hf.cf hf.cb ψ
  have hsh := R.mixed_shadowA (ρ := ρ) hj hJ vs'
  apply List.map_congr_left
  intro E hE
  have h := interp_congr_shadowRel (hsh.take i) (consList (paramVals d.nP ρ) ρ) [] (E := E)
    (by rw [htake, List.length_nil, Nat.add_zero]
        have hnb := hnbE i (by rw [hf.nF]; exact hi) E hE
        rwa [htssF, List.length_nil, Nat.add_zero] at hnb)
  simp only [consList_nil] at h
  exact h.symm

set_option maxHeartbeats 1600000 in
/-- **The container's readings at a container-recursive position, at
the mixed prefix, are the copy's at the fields' prefix** (`kindR`
through `interp_instSeq_under`; the mixed values shadow the fields off
the replaced positions, which the container's readings do not mention,
`hnbP`). -/
theorem readJ_agree (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length) {J : Nat}
    {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) {i : Nat} (hi : i < cA.2)
    (hA : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J))
    (htl : ((cd j).dJ.tssF J (cd j).ψ').getD i [] = []) {vs' : List V} (hlen : vs'.length = cA.2) :
    (((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V (consList
        ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
      = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))) := by
  obtain ⟨lps, S⟩ := R.psiSetup_final (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) (paramBvarsAt_length _ _) hρ
    tbl₀ hj
  have hg := R.groupFacts hj
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  obtain ⟨-, hnbE, -, -⟩ := S.hnbP J cA hJ _ _ _ _ _ _ _ ((cd j).dJ.cdsR_getElem?_of hg.ctorsC hJ)
  have hsh := mixed_shadowP (p := p) (st := st) (d := d) (mpAux := mpAux) (ψ := ψ) (cd := cd)
    (order := order) (s := s) tbl₀ (ρ := ρ) (j := j) (J := J) vs'
  obtain ⟨-, -, -, heiss⟩ := hf.read.kindR i hA
  have htake : (vs'.take i).length = i := by rw [List.length_take]; omega
  have hMlen : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').length = vs'.length := d.invMixed_length _ _ _ _ _ _ _ _ _ _
  have htakeM : ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').take i).length = i := by rw [List.length_take, hMlen]; omega
  rw [← hf.view.2.2.1, heiss, htl, List.length_nil, Nat.add_zero, List.map_map, (hg.view J).2.2.1]
  apply List.map_congr_left
  intro E hE
  simp only [Function.comp_def]
  rw [interp_instSeq_under (consList (paramVals d.nP ρ) ρ) (cd j).DsA (vs'.take i) _ E
    (fun hne => by
      have hpos : 0 < (cd j).DsA.length := List.length_pos_iff.mpr hne
      rw [hg.len] at hpos
      rw [hg.len, htake]; omega)]
  have h := interp_congr_shadowRelP_at hsh
    (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
    (n := i) (by rw [hlen]; omega) (E := E)
    (by have := hnbE i hi E (by rw [(S.hview J).2.2.1]; exact hE)
        rwa [(S.hview J).2.2.2, htl, List.length_nil, Nat.add_zero] at this)
  exact h.symm

set_option maxHeartbeats 1600000 in
/-- **The container's index readings at the mixed values are the
copy's at the fields** (`r1_step`'s `hEs`), transports included: the
record's `es`, `interp_instSeq_under`, and the mixed values shadow the
fields off the REPLACED positions, which the container's result
readings do not mention (`hnbP`). -/
theorem es_inv' (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length) {J : Nat}
    {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) {vs' : List V} (hlen : vs'.length = cA.2) :
    ((cd j).dJ.esF J (cd j).ψ').map (interp V (consList
        (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs')
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
      = (d.esF (auxOfsOf st p.k cd j J) ψ).map (interp V (consList vs' (consList (paramVals d.nP ρ) ρ))) := by
  obtain ⟨lps, S⟩ := R.psiSetup_final (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) (paramBvarsAt_length _ _) hρ
    tbl₀ hj
  have hg := R.groupFacts hj
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  obtain ⟨-, -, hnbEs, -⟩ := S.hnbP J cA hJ _ _ _ _ _ _ _ ((cd j).dJ.cdsR_getElem?_of hg.ctorsC hJ)
  have hsh := mixed_shadowP (p := p) (st := st) (d := d) (mpAux := mpAux) (ψ := ψ) (cd := cd)
    (order := order) (s := s) tbl₀ (ρ := ρ) (j := j) (J := J) vs'
  rw [hf.read.es, List.map_map]
  apply List.map_congr_left
  intro E hE
  simp only [Function.comp_def]
  rw [interp_instSeq_under (consList (paramVals d.nP ρ) ρ) (cd j).DsA vs' _ E
    (fun hne => by
      have hpos : 0 < (cd j).DsA.length := List.length_pos_iff.mpr hne
      rw [hg.len] at hpos
      rw [hg.len, hlen]; omega)]
  have h := interp_congr_shadowRelP hsh
    (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)) []
    (E := E) (by rw [hlen, List.length_nil, Nat.add_zero]; exact hnbEs E hE)
  simp only [consList_nil] at h
  exact h.symm

/-! ## The per-position facts -/

set_option maxHeartbeats 3200000 in
/-- **The per-position facts for R1 at a finitary container, TRANSPORTS
INCLUDED** (`r1_step`'s `hpos`): a container-recursive position is a
hypothesis position on both sides with the readings agreeing
(`readA_agree`, `readJ_agree`); a TRANSPORT's third arm — ψ's value at
the mixed spine is the field — is the induction hypothesis at the
target copy (`hIH`): ψ's value is the target pin's term at the copy's
readings and ψ⁻¹'s mixed value, the latter ψ⁻¹'s fold at the target
copy at the readings and the field; any other container-ordinary
position is ordinary on both sides. -/
theorem pos_inv' (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    (hfin : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hfinA : ∀ i, i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) →
      (d.ksF (auxOfsOf st p.k cd j J)).getD i .ordinary = .recursive ∧
      (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = [])
    {vs' : List V} (hlen : vs'.length = cA.2)
    (hIH : ∀ i, i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) →
      R1Pred d ψ ρ (consList (paramVals d.nP ρ) ρ) p.k
        (fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
        (fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t')
        (d.tup ψ (d.tgts (auxOfsOf st p.k cd j J) i)
          (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (interp V (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ)))))
        (vs'.getD i pt))
    (hEntryFit : ∀ i, i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) →
      SpineFit (consList (paramVals d.nP ρ) ρ) (d.IdsM (d.tgts (auxOfsOf st p.k cd j J) i) ψ)
        (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))))) :
    ∀ i, i < cA.2 →
    (¬ replaced (IndRepData.psiUseIh (cd j).dJ J)
        (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J) i ∧
      d.invUseIh p.k (auxOfsOf st p.k cd j J) i = false) ∨
    (IndRepData.psiUseIh (cd j).dJ J i = true ∧
      d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J i = none ∧
      d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true ∧
      i ∈ ConLeche.recIdxOf ((cd j).dJ.ksR J) ∧ i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) ∧
      i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) ∧
      ((cd j).dJ.tssR J (cd j).ψ').getD i [] = [] ∧ (d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [] = [] ∧
      d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + (cd j).base + (cd j).dJ.tgtsR J i ∧
      (cd j).dJ.tgtsR J i < (cd j).dJ.k ∧
      ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map (interp V (consList (vs'.take i) ρ))
        = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (interp V (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))) ∧
      (((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V (consList
          ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
        = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
            (interp V (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ)))) ∨
    (d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (consList (paramVals d.nP ρ) ρ) j J
        (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs')).getD i pt
      = vs'.getD i pt := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hD := hf.ctor.2.2
  have hksLenA : (d.ksR (auxOfsOf st p.k cd j J)).length = cA'.2 := by
    rw [hf.view.1]; exact hf.ctor.2.2.ksLen
  have hMlen : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
      (auxOfsOf st p.k cd j J) vs').length = vs'.length := d.invMixed_length _ _ _ _ _ _ _ _ _ _
  intro i hi
  by_cases hA : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J)
  · -- container-recursive
    obtain ⟨hkind, htl⟩ := hfin i hA
    obtain ⟨hks, htgt, htss, -⟩ := hf.read.kindR i hA
    have hrecA : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) :=
      mem_recIdxOf.mpr ⟨by rw [hksLenA, hf.nF]; exact hi, Or.inl (by rw [hks]; exact hkind)⟩
    have htssA : (d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [] = [] := by rw [htss, htl]; rfl
    have htssF : (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = [] := by
      rw [← hf.view.2.2.2]; exact htssA
    refine Or.inr (Or.inl ⟨?_, ?_, R.recJ_useIh hj hJ hA, by rw [(hg.view J).1]; exact hA, hrecA,
      by rw [← hf.view.1]; exact hrecA, by rw [(hg.view J).2.2.2]; exact htl, htssA,
      by rw [htgt, (hg.view J).2.1], hrepJ.tgtsRLt J i, R.readA_agree hj hJ hi htssF hlen,
      R.readJ_agree tbl₀ hρ hj hJ hi hA htl hlen⟩)
    · unfold IndRepData.psiUseIh; exact decide_eq_true hA
    · unfold IndRepData.psiVia
      rw [if_neg]
      intro h
      exact h.2.1 hA
  · by_cases hTr : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) ∧
        p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) i
    · -- a transport: the induction hypothesis at the target copy
      obtain ⟨hAr, hk⟩ := hTr
      have hAF : i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) := by
        rw [← hf.view.1]; exact hAr
      obtain ⟨hkindA, htssF⟩ := hfinA i hAF
      have htssA : (d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [] = [] := by
        rw [hf.view.2.2.2]; exact htssF
      have heissA : d.eissR (auxOfsOf st p.k cd j J) ψ = d.eissF (auxOfsOf st p.k cd j J) ψ :=
        congrFun hf.view.2.2.1 ψ
      have htgtF : d.tgts (auxOfsOf st p.k cd j J) i = d.tgtsR (auxOfsOf st p.k cd j J) i := by
        rw [hf.view.2.1]
      have hifs : i < vs'.length := by rw [hlen]; exact hi
      have hiM : i < (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
          (auxOfsOf st p.k cd j J) vs').length := by rw [hMlen]; exact hifs
      have htakeM : ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
          (auxOfsOf st p.k cd j J) vs').take i).length = i := by rw [List.length_take, hMlen]; omega
      have hDsLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := by
        rw [List.length_map, hg.len]
      have huseA : d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true := by
        unfold IndRepData.invUseIh
        exact decide_eq_true ⟨by rw [hf.read.mem]; omega, hAr, hk⟩
      -- the mixed value: ψ⁻¹'s fold at the target at the readings and the field
      have hMIXi : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
          (auxOfsOf st p.k cd j J) vs').getD i pt
          = (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
              (interp V (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))) ++ [vs'.getD i pt]).foldl
              SetTheory.app
              (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
                (d.tgtsR (auxOfsOf st p.k cd j J) i))) := by
        unfold IndRepData.invMixed
        rw [mixedVals_getD _ _ _ _ hifs, huseA]
        simp only [if_true]
        rw [getD_map_idxOf hAr, htssA]
        simp only [lamTower, List.length_nil, Semantics.frameIdx, List.range_zero, List.map_nil,
          List.foldl_nil]
        rw [R.readA_agree hj hJ hi htssF hlen]
      -- ψ's value at the mixed spine: the target pin's term at the readings and that
      have hvia := psiVia_transport (d := d) (mpAux := mpAux) (ψ := ψ) (cd := cd) (order := order) tbl₀ hA
        hAr hk
      have hshiftΨ : shiftE (cd j).dJ.nP 0
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
          = consList (paramVals d.nP ρ) ρ := by
        rw [← hDsLen]; exact shiftE_consList _ _
      have hVSi : (d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (consList (paramVals d.nP ρ) ρ) j J
          (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs')).getD i pt
          = (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD i []).map
              (interp V (consList (vs'.take i) (consList (paramVals d.nP ρ) ρ))) ++
              [(d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
                (auxOfsOf st p.k cd j J) vs').getD i pt]).foldl SetTheory.app
              (interp V (consList (paramVals d.nP ρ) ρ)
                (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
                  (d.tgtsR (auxOfsOf st p.k cd j J) i - p.k))) := by
        unfold IndRepData.psiValsAt
        rw [psiVals_getD _ _ _ _ _ _ _ hiM, hvia]
        simp only [htssA, liftDoms, rebit, List.map_nil, List.length_nil, Nat.add_zero, viaVal, lamTower,
          Semantics.frameIdx, List.range_zero, List.foldl_nil]
        rw [interp_liftN, hshiftΨ, List.map_map, heissA]
        congr 2
        rw [← R.readM_agree hj hJ hi htssF hlen]
        apply List.map_congr_left
        intro E _
        simp only [Function.comp_def]
        have hE : E.liftN (cd j).dJ.nP i
            = E.liftN ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length
                ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
                  (auxOfsOf st p.k cd j J) vs').take i).length := by
          rw [hDsLen, htakeM]
        rw [hE, interp_liftN_middle]
      -- the induction hypothesis at the target copy
      have htgtA : d.tgts (auxOfsOf st p.k cd j J) i < d.k := by rw [htgtF]; exact hf.tgts i
      have h := hIH i hAF (d.tgts (auxOfsOf st p.k cd j J) i) (by rw [htgtF]; exact hk) htgtA _
        (hEntryFit i hAF) rfl
      unfold foldApp at h
      rw [htgtF] at h
      refine Or.inr (Or.inr ?_)
      rw [hVSi, hMIXi]
      exact h
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

/-! ## The mixed values fit, transports included -/

set_option maxHeartbeats 6400000 in
/-- **ψ⁻¹'s mixed values fit the container constructor's telescope**,
TRANSPORTS INCLUDED (`r1_step`'s `hfitMixed`): `fitMixed_of_run`'s
position-by-position argument, with a hypothesis position that is a
transport placed in the container's domain — the target pin's carrier
at the copy's readings (`containerDom_transport`, `transport_fits`) —
by ψ⁻¹'s typing at the target copy (`invFold_mem`), the field being in
the copy's recursive entry (`interp_recEntry`). -/
theorem fitMixed_transport (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    (hfin : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hfinA : ∀ i, i ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) →
      (d.ksF (auxOfsOf st p.k cd j J)).getD i .ordinary = .recursive ∧
      (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = [])
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
  · -- a hypothesis position: container-recursive, or a transport
    have hAr : n ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) := d.invUseIh_mem hu
    have hAF : n ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) := by rw [← hf.view.1]; exact hAr
    have hk : p.k ≤ d.tgtsR (auxOfsOf st p.k cd j J) n := by
      unfold IndRepData.invUseIh at hu
      exact (of_decide_eq_true hu).2.2
    obtain ⟨hkindA, htssF⟩ := hfinA n hAF
    have htssA : (d.tssR (auxOfsOf st p.k cd j J) ψ).getD n [] = [] := by rw [hf.view.2.2.2]; exact htssF
    have heissA : d.eissR (auxOfsOf st p.k cd j J) ψ = d.eissF (auxOfsOf st p.k cd j J) ψ :=
      congrFun hf.view.2.2.1 ψ
    have hnlt : n < cA'.2 := by rw [hf.nF]; exact hn
    -- the mixed value at a hypothesis position
    have hMn : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
        (auxOfsOf st p.k cd j J) vs').getD n pt
        = (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
              (interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))) ++ [vs'.getD n pt]).foldl
            SetTheory.app
            (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
              (d.tgtsR (auxOfsOf st p.k cd j J) n))) := by
      unfold IndRepData.invMixed
      rw [mixedVals_getD _ _ _ _ hnv, hu]
      simp only [if_true]
      rw [getD_map_idxOf hAr, htssA]
      simp only [lamTower, List.length_nil, Semantics.frameIdx, List.range_zero, List.map_nil,
        List.foldl_nil]
      rw [R.readA_agree hj hJ hn htssF hvsLen]
    -- the copy's recursive entry: the field's readings graded and fitting
    obtain ⟨hE, hx⟩ := hcff.1 n hAF vs' (by rw [hσ₀]; exact hvs') []
      (by rw [htssF]; trivial)
    simp only [consList_nil, List.foldl_nil, hσ₀] at hE hx
    have hfitM : SpineFit (consList (paramVals d.nP ρ) ρ)
        ((d.motDataAV mpAux.base2 ψ (d.tgtsR (auxOfsOf st p.k cd j J) n)).map (·.2.2))
        (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
          (interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))) ++ [vs'.getD n pt]) := by
      have hsplit : (d.motDataAV mpAux.base2 ψ (d.tgtsR (auxOfsOf st p.k cd j J) n)).map (·.2.2)
          = (rebit (pwBit ψ ConLeche.PropWhen.never)
              ((d.ipss ψ).getD (d.tgtsR (auxOfsOf st p.k cd j J) n) [])).map (·.2.2) ++
            [famAppAV ((d.Ls mpAux.base2 ψ).getD (d.tgtsR (auxOfsOf st p.k cd j J) n) default)
              (d.pinsOf ψ (d.tgtsR (auxOfsOf st p.k cd j J) n)) d.nP
              (d.nP + d.nIdxs.getD (d.tgtsR (auxOfsOf st p.k cd j J) n) 0)
              (d.nIdxs.getD (d.tgtsR (auxOfsOf st p.k cd j J) n) 0)] := by
        simp [IndRepData.motDataAV]
      rw [hsplit]
      exact SpineFit.append hE ⟨hx, trivial⟩
    have htgtA : d.tgtsR (auxOfsOf st p.k cd j J) n < d.k := hf.tgts n
    have hmem := IndRepData.InvSetup.fold_mem_vals (d.withSort s) S htgtA hfitM
    have hisLen : (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
        (interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ)))).length
        = d.nIdxs.getD (d.tgtsR (auxOfsOf st p.k cd j J) n) 0 := by
      rw [hE.length_eq, List.length_map, rebit_length]
      exact S.hipsLen _ htgtA
    by_cases hA : n ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J)
    · -- container-recursive
      obtain ⟨hkind, htl⟩ := hfin n hA
      obtain ⟨hks, htgt, htss, heiss⟩ := hf.read.kindR n hA
      have hreadJ := R.readJ_agree tbl₀ hρ hj hJ hn hA htl hvsLen
      have htgtJ : (cd j).dJ.tgtsR J n < (cd j).dJ.k := hrepJ.tgtsRLt J n
      -- the container's recursive entry at the mixed prefix
      rw [(hg.view J).2.2.1] at hreadJ
      rw [hMn, interp_recEntry hDJ (cd j).ψ' hkind hn htakeM hDsLen (consList (paramVals d.nP ρ) ρ),
        hreadJ]
      -- the target copy's leaf and pins are the container member's at the pin
      have htgtE : d.tgtsR (auxOfsOf st p.k cd j J) n = p.k + (cd j).base + (cd j).dJ.tgtsR J n := by
        rw [htgt, (hg.view J).2.1]
      obtain ⟨hL, hpins⟩ := invChoice_group R.pins hj htgtJ
      rw [← htgtE] at hL hpins
      have hmem' : (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
            (interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))) ++ [vs'.getD n pt]).foldl
            SetTheory.app
            (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
              (d.tgtsR (auxOfsOf st p.k cd j J) n)))
          ∈ˢ interp V (consList (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
                (interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))))
                (consList (paramVals d.nP ρ) ρ))
              (famAppAV (d.invL mpAux.base2 ψ p.k cd (d.tgtsR (auxOfsOf st p.k cd j J) n))
                (d.invPinsT p.k cd (d.tgtsR (auxOfsOf st p.k cd j J) n)) d.nP
                (d.nP + d.nIdxs.getD (d.tgtsR (auxOfsOf st p.k cd j J) n) 0)
                (d.nIdxs.getD (d.tgtsR (auxOfsOf st p.k cd j J) n) 0)) := hmem
      rw [hL, hpins, interp_famAppAV_pins (mpAux.base2.cval_closedL _ _) _ _ hisLen] at hmem'
      rw [← (hg.view J).2.1]
      exact hmem'
    · -- a transport: the target pin's carrier at the copy's readings
      obtain ⟨j', hj'eq, -, hdom, hWD⟩ := d.containerDom_transport mpAux.base2 hg.len (auxOfsOf st p.k cd j) cd
        hf.read hlenDJ (by rw [hlenDA, hf.nF]) (by rw [hksLenA, hf.nF]) hsat₀ hn hA hAr hk htakeM hpre'
      have hj' : j' < st.pins.length := by
        have := R.transport_lt hj hJ n
        rw [hj'eq] at this
        omega
      have hg' := R.groupFacts hj'
      have hc' : CopyData.Ok mpAux.base2 d ψ p.k j' (cd j') := hg'.ok (R.pins j' hj').1.2.1
      have hEl : ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD n []).length = d.nIdxAt (p.k + j') := by
        rw [heissA, hD.eisLen ψ n hkindA hnlt]
        show d.nIdxAt (d.tgts (auxOfsOf st p.k cd j J) n) = _
        rw [← hf.view.2.1, hj'eq]
      obtain ⟨-, hbody, -, -⟩ := d.transport_fits mpAux.base2 hc' hEl htakeM hWD (as := [])
        (by rw [htssA]; trivial)
      simp only [consList_nil, htssA, List.length_nil, Nat.add_zero] at hbody
      rw [hdom, htssA]
      simp only [mkPisAV, List.length_nil, Nat.add_zero]
      rw [hbody, heissA, R.readM_agree hj hJ hn htssF hvsLen, hMn]
      -- ψ⁻¹'s fold at the target copy, typed into the target pin's carrier
      have hbm' : (cd j').base + (cd j').mm = j' := (R.pins j' hj').1.2.1
      have htgtE : d.tgtsR (auxOfsOf st p.k cd j J) n = p.k + (cd j').base + (cd j').mm := by
        rw [hj'eq, Nat.add_assoc, hbm']
      have hmm' : (cd j').mm < (cd j').dJ.k := hg'.mm
      obtain ⟨hL, hpins⟩ := invChoice_group R.pins hj' hmm'
      rw [← htgtE] at hL hpins
      have hmem' : (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
            (interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))) ++ [vs'.getD n pt]).foldl
            SetTheory.app
            (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
              (d.tgtsR (auxOfsOf st p.k cd j J) n)))
          ∈ˢ interp V (consList (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
                (interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))))
                (consList (paramVals d.nP ρ) ρ))
              (famAppAV (d.invL mpAux.base2 ψ p.k cd (d.tgtsR (auxOfsOf st p.k cd j J) n))
                (d.invPinsT p.k cd (d.tgtsR (auxOfsOf st p.k cd j J) n)) d.nP
                (d.nP + d.nIdxs.getD (d.tgtsR (auxOfsOf st p.k cd j J) n) 0)
                (d.nIdxs.getD (d.tgtsR (auxOfsOf st p.k cd j J) n) 0)) := hmem
      rw [hL, hpins, interp_famAppAV_pins (mpAux.base2.cval_closedL _ _) _ _ hisLen] at hmem'
      exact hmem'
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

/-! ## R1 at the run, transports included -/

set_option maxHeartbeats 3200000 in
/-- **R1's STEP at the run, TRANSPORTS INCLUDED** (`r1_hstep` with
`hnoT` gone: `fitMixed_transport`, `es_inv'`, `pos_inv'` in place of
their transport-free forms).  Restrictions: every container finitary
(`hfin`), the scratch block finitary (`hfinA`), the bit nonzero
(`hbA`). -/
theorem r1_hstep' (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0)
    (hfin : ∀ j, j < st.pins.length → ∀ J i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hfinA : ∀ J' i, i ∈ ConLeche.recIdxOf (d.ksF J') →
      (d.ksF J').getD i .ordinary = .recursive ∧ (d.tssF J' ψ).getD i [] = []) :
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
  have htgts : ∀ i, d.tgts J' i < d.k := S.htgts J'
  obtain ⟨hfit, hIH⟩ := fieldsFit_of_chainFit (P := R1Pred d ψ ρ (consList (paramVals d.nP ρ) ρ) p.k
      (fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
      (fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t'))
    R.repsAt_of_reps hsat₀ rfl hρ (paramVals_length _ _) hJ' hC htgts (hfinA J')
    (fun i hi => hfacts.2 i (hfinA J' i hi).1) hlen hfields
  have hvsN : fs.length = cA'.2 := by
    rw [hlen, d.Fss_getD ψ hJ', List.length_map, List.length_drop, hlenD']; omega
  have hEsOk := (hfacts.1 fs hfit).1
  have hEsFit := (hfacts.1 fs hfit).2
  have hEntryFit : ∀ i, i ∈ ConLeche.recIdxOf (d.ksF J') →
      SpineFit (consList (paramVals d.nP ρ) ρ) (d.IdsM (d.tgts J' i) ψ)
        (((d.eissF J' ψ).getD i []).map (interp V (consList (fs.take i) (consList (paramVals d.nP ρ) ρ)))) := by
    intro i hi
    have hksLen : (d.ksF J').length = cA'.2 := hC.2.2.ksLen
    have hilt : i < cA'.2 := by
      have := (mem_recIdxOf.mp hi).1
      rw [hksLen] at this
      exact this
    have htake : (fs.take i).length = i := by rw [List.length_take]; omega
    have hpre : SpineFit (consList (paramVals d.nP ρ) ρ) ((((d.dsF J' ψ).drop d.nP).map (·.2.2)).take i)
        (fs.take i) := by
      rw [← d.Fss_getD ψ hJ']
      exact spineFit_take' hfit (by rw [← hlen, hvsN]; omega)
    exact (hfacts.2 i (hfinA J' i hi).1 (fs.take i) htake hpre).2
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
    -- ψ⁻¹'s ι at values
    have hιΦ := fun (vs : List V)
        (hfitv : SpineFit ρ ((d.dsF (auxOfsOf st p.k cd j Jc) ψ).map (·.2.2)) (paramVals d.nP ρ ++ vs)) =>
      R.inv_iota hk hρ hbA hJ'
        (by have := hfitv.length_eq
            rw [List.length_append, paramVals_length, List.length_map, hlenD'] at this; omega)
        hfitv
    -- ψ's ι at values
    have hιΨ := fun (vs : List V)
        (hfitv : SpineFit (consList (paramVals d.nP ρ) ρ) (((cd j).dJ.dsF Jc (cd j).ψ').map (·.2.2))
          ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) ++ vs)) =>
      R.psi_iota tbl₀ hρ rfl hj (hbJ j hj) (fun _ => rfl) hJc
        (by have := hfitv.length_eq
            rw [List.length_append, hDsLen, List.length_map, (hrepJ.ctors Jc cAJ hJc).2.2.len (cd j).ψ'] at this
            omega)
        hfitv
    exact r1_step mpAux.base2 (dJ := (cd j).dJ) (ψ' := (cd j).ψ') (cA := cAJ)
      (σ := consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (Ψ := fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (Ψ' := fun t' => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (t' - p.k))
      (Φ' := fun t' => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t')
      R.repsAt_of_reps hsat₀ rfl hρ hJ' hlenD' hf.pIff hf.read.mem hf.mem hmemJ hf.view.2.1
      (fun t _ => by
        show d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (p.k + (cd j).base + t - p.k)
          = d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t)
        rw [show p.k + (cd j).base + t - p.k = (cd j).base + t by omega])
      hfit hIH hEsOk hEsFit hEntryFit hall hιΦ hιΨ rfl rfl
      (d.psiHead_interp mpAux.base2 ψ (auxOfsOf st p.k cd j) hJ' hDsLen)
      (R.headφ_of_run (ρ := ρ) hj hJc).headφ
      (R.fitMixed_transport tbl₀ hρ hj hJc (hfin j hj Jc) (hfinA _) hfit)
      (R.es_inv' tbl₀ hρ hj hJc hvsN')
      (fun i hi => R.pos_inv' tbl₀ hρ hj hJc (hfin j hj Jc) (hfinA _) hvsN' hIH hEntryFit i
        (by rw [← hf.nF]; exact hi))
  · -- a real member's constructor: the predicate speaks of copies
    intro t' hk₀ ht' is' his' htupE
    obtain ⟨s'', cvT'', cvR'', mI'', rP'', rules'', -, hrep''⟩ := R.repsAt_of_reps t' ht'
    rw [htupE] at hall
    have h := hrep''.idxRecover ψ (consList (paramVals d.nP ρ) ρ) hsat₀ is' his' _ J' fs hJ'lt hlen
      hEsOk hEsFit hall
    have hmem : d.mems J' = t' := h.1
    omega

/-- **R1 AT THE RUN, TRANSPORTS INCLUDED** (task #279 M-C′, the
transport arm of R1): `r1At_of_run` with `r1_hstep'`.  Restrictions:
every container finitary (`hfin`), the scratch block finitary
(`hfinA`), the bit nonzero (`hbA`). -/
theorem r1At_transport (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0)
    (hfin : ∀ j, j < st.pins.length → ∀ J i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hfinA : ∀ J' i, i ∈ ConLeche.recIdxOf (d.ksF J') →
      (d.ksF J').getD i .ordinary = .recursive ∧ (d.tssF J' ψ).getD i [] = [])
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
    (R.r1_hstep' tbl₀ hρ hbA hfin hfinA)
  rw [show p.k + (cd j).base + t - p.k = (cd j).base + t by omega] at h
  exact h

/-- **R1 at the run, transports included, at ANY elimination bit**: the
nonzero arm (`r1At_transport`) or the `Prop` arm (`r1At_prop`).
Remaining restrictions: the containers and the scratch block finitary. -/
theorem r1At_transport_all (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
    (hfin : ∀ j, j < st.pins.length → ∀ J i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hfinA : ∀ J' i, i ∈ ConLeche.recIdxOf (d.ksF J') →
      (d.ksF J').getD i .ordinary = .recursive ∧ (d.tssF J' ψ).getD i [] = [])
    {j : Nat} (hj : j < st.pins.length) {t : Nat} (ht : t < (cd j).dJ.k) :
    d.R1At mpAux.base2 ψ ρ (paramBvarsAt d.nP d.nP) (p.k + (cd j).base + t)
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  by_cases hb : d.bb ψ = 0
  · exact R.r1At_prop tbl₀ hρ hb hj ht
  · exact R.r1At_transport tbl₀ hρ hb hfin hfinA hj ht

end NestedRunFacts

end ConLeche.Model
