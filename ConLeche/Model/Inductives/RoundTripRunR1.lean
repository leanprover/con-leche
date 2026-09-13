module

public import ConLeche.Model.Inductives.RoundTripRun
public section

/-!
# R1 at the RUN level (task #279 M-C′ step 5, DESIGN §M.36)

`RoundTripRun.lean` assembles R2 at the run.  This module assembles
R1 — the COPY-side round trip, ONE induction over the scratch block's
carriers (`r1At_of_step`, `r1_step`) — from the same run facts
(`NestedRunFacts`):

* the scratch block's representations at the members' OWN spellings
  of the sort (`repsAt_of_reps`: `MutualBlockReps` gives `IndRep` at
  `{d with resSort := s_t}`; `IndRep.congr_sort` as a full transfer is
  FALSE — `strip`, `former`, `ctors` pin the syntactic sort — so the
  inductions consume the clauses that depend on the sort through its
  VALUE only, at `RepsAt`);
* the scratch constructors' facts (`ctorFieldFacts_aux`, `ctor_facts_aux`:
  the result readings graded and fitting, a recursive entry's readings
  graded and fitting the target's telescope — off ψ⁻¹'s setup at the
  parameter variables, `invSetup_at`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock ElimState
  NestedPin ContainerInfo ContainerMember)

universe w

variable {V : Type w} [SetTheory V]

namespace NestedRunFacts

variable {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState}
  {b : MutualBlock} {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)}
  {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
  {lpsT : List Name} {order : List Nat} {s : Level}
  (R : NestedRunFacts F env p st b params pbs mpAux d ψ cd lpsT order s)

include R

/-! ## The scratch block's representations, at the members' own sorts -/

/-- **The scratch block's members are represented at their own
spellings of the sort** (`MutualBlockReps`, in `RepsAt`'s shape). -/
theorem repsAt_of_reps : d.RepsAt mpAux.base2 := by
  obtain ⟨-, hkb, -, -, -, -, -, hall⟩ := R.reps
  intro t ht
  obtain ⟨s', cvT, cvR, caps, mI, rP, rules, -, -, -, hsv, hrep⟩ := hall t (by rw [← hkb]; exact ht)
  exact ⟨s', cvT, cvR, mI, rP, rules, hsv, hrep⟩

theorem kReal : d.kReal = d.k := by
  obtain ⟨-, hkb, hkRb, -⟩ := R.reps
  rw [hkb, hkRb]

/-- ψ⁻¹'s setup at the parameter variables, at any frame whose
parameters fit (`inv` at `ρ`). -/
theorem invSetup_at {ρ : Nat → V} (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) :
    ∃ lpsI lpsT' : List Name,
      (d.withSort s).InvSetup mpAux lpsI lpsT' ψ ρ (paramBvarsAt d.nP d.nP)
        (d.invL mpAux.base2 ψ p.k cd) (d.invPinsT p.k cd)
        (d.invHead mpAux.base2 ψ st.pins.length cd (auxOfsOf st p.k cd)) (d.invUseIh p.k) := by
  obtain ⟨lpsI, lpsT', hinv⟩ := R.inv
  exact ⟨lpsI, lpsT', hinv ρ _ (paramBvarsAt_length _ _) (wellDenotedV_paramBvarsAt _ _ _) hρ⟩

/-! ## The scratch constructors' facts -/

/-- **A scratch constructor's field-side facts** (`ctorFieldFacts_of` at
ψ⁻¹'s setup, read at the datum: the facts mention the sort only
through data). -/
theorem ctorFieldFacts_aux {ρ : Nat → V} (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
    {J' : Nat} {cA' : ConstantVal × Nat} (hJ' : d.ctorsA[J']? = some cA') :
    d.CtorFieldFacts mpAux.base2 ψ ρ (paramBvarsAt d.nP d.nP) J' cA'.1.name (d.dsF J' ψ) (d.esF J' ψ)
      (ConLeche.recIdxOf (d.ksF J')) (d.eissF J' ψ) (d.tssF J' ψ) := by
  obtain ⟨lpsI, lpsT', S⟩ := R.invSetup_at hρ
  have hJA : J' < d.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ').1
  exact (d.withSort s).ctorFieldFacts_of mpAux S.hps S.hpins S.hLS S.hFF S.hparams
    (S.hctors J' cA' hJ') (S.hpIff J' cA' hJ') (S.hmems J' hJA) (S.htgts J')
    (fun i => by rw [(S.hview J').2.1])

set_option maxHeartbeats 1600000 in
/-- **A scratch constructor's readings, graded and fitting** (the
mirror of `ctor_facts` at the scratch block, at the block's parameter
frame): at a spine fitting the real domains the result readings are
graded and fit the member's telescope; at a recursive position and any
fitting prefix the entry's readings are graded and fit the target's
telescope. -/
theorem ctor_facts_aux {ρ : Nat → V} (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
    {J' : Nat} {cA' : ConstantVal × Nat} (hJ' : d.ctorsA[J']? = some cA') :
    (∀ vs' : List V, SpineFit (consList (paramVals d.nP ρ) ρ) ((d.Fss ψ).getD J' []) vs' →
      (∀ E ∈ d.esF J' ψ, WellDenoted V (consList vs' (consList (paramVals d.nP ρ) ρ)) E) ∧
      SpineFit (consList (paramVals d.nP ρ) ρ) (d.IdsM (d.mems J') ψ)
        ((d.esF J' ψ).map (interp V (consList vs' (consList (paramVals d.nP ρ) ρ))))) ∧
    (∀ i, (d.ksF J').getD i .ordinary = .recursive → ∀ ws : List V, ws.length = i →
      SpineFit (consList (paramVals d.nP ρ) ρ) ((((d.dsF J' ψ).drop d.nP).map (·.2.2)).take i) ws →
      (∀ E ∈ (d.eissF J' ψ).getD i [], WellDenoted V (consList ws (consList (paramVals d.nP ρ) ρ)) E) ∧
      SpineFit (consList (paramVals d.nP ρ) ρ) (d.IdsM (d.tgts J' i) ψ)
        (((d.eissF J' ψ).getD i []).map (interp V (consList ws (consList (paramVals d.nP ρ) ρ))))) := by
  obtain ⟨lpsI, lpsT', S⟩ := R.invSetup_at hρ
  have hC := S.hctors J' cA' hJ'
  have hD := hC.2.2
  have hJA : J' < d.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ').1
  have hmemJ : d.mems J' < d.k := S.hmems J' hJA
  have hlenD : (d.dsF J' ψ).length = d.nP + cA'.2 := hD.len ψ
  have hpvLen : (paramVals d.nP ρ).length = d.nP := paramVals_length _ _
  have hpIff' : ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.dsF J' ψ).take d.nP).map (·.2.2)).reverse ρ' := S.hpIff J' cA' hJ'
  have hfitP : SpineFit ρ (((d.dsF J' ψ).take d.nP).map (·.2.2)) (paramVals d.nP ρ) :=
    spineFit_of_paramsIff hpvLen (by rw [List.length_map, List.length_take, hlenD]; omega) hρ hpIff'
  have cff := R.ctorFieldFacts_aux hρ hJ'
  have hps : (paramBvarsAt d.nP d.nP).map (interp V ρ) = paramVals d.nP ρ := rfl
  refine ⟨fun vs' hvs => ?_, fun i hrec ws hws hpre => ?_⟩
  · have hvs' : SpineFit (consList (paramVals d.nP ρ) ρ) (((d.dsF J' ψ).drop d.nP).map (·.2.2)) vs' := by
      rw [← d.Fss_getD ψ hJ']; exact hvs
    have hfitAll : SpineFit ρ ((d.dsF J' ψ).map (·.2.2)) (paramVals d.nP ρ ++ vs') := by
      rw [← List.take_append_drop d.nP (d.dsF J' ψ), List.map_append]
      exact hfitP.append hvs'
    refine ⟨?_, ?_⟩
    · have hwd := wellDenoted_mkPisAV_body (hD.okTy ψ ρ).1 _ hfitAll
      rw [consList_append] at hwd
      unfold ctorBodyAVI at hwd
      intro E hE
      exact wellDenoted_mkAppN_args hwd E (List.mem_append_right _ hE)
    · have h := (cff.2 vs' (by rw [hps]; exact hvs')).1
      rw [hps, d.ipss_getD ψ hmemJ, rebit_map_dom] at h
      exact h
  · have hklt : i < (d.ksF J').length := by
      rcases Nat.lt_or_ge i (d.ksF J').length with h | h
      · exact h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h] at hrec
        exact absurd hrec (by simp)
    have hilt : i < cA'.2 := by rw [← hD.ksLen]; exact hklt
    have hlt2 : d.nP + i < (d.dsF J' ψ).length := by rw [hlenD]; omega
    have hentryE : (d.dsF J' ψ)[d.nP + i]? = some ((d.dsF J' ψ).getD (d.nP + i) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt2]; rfl
    have hfitPre : SpineFit ρ (((d.dsF J' ψ).take (d.nP + i)).map (·.2.2)) (paramVals d.nP ρ ++ ws) := by
      rw [List.take_add, List.map_append]
      refine hfitP.append ?_
      rw [List.map_take]
      exact hpre
    have hok := wellDenoted_mkPisAV_dom (hD.okTy ψ ρ).1 _ _ _ hentryE hfitPre
    have hrecE : ((d.dsF J' ψ).getD (d.nP + i) default).2.2
        = AnnotTerm.mkAppN (mpAux.base2.acval (d.memberName (d.tgts J' i)) ψ)
            (paramBvarsAt d.nP (d.nP + i) ++ (d.eissF J' ψ).getD i []) := hD.recEntry ψ i hrec hilt
    rw [consList_append, hrecE] at hok
    refine ⟨fun E hE => wellDenoted_mkAppN_args hok E (List.mem_append_right _ hE), ?_⟩
    exact (d.withSort s).idxFit_of_entry (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) S.hps
      (S.hFF _ (S.htgts J' i)) (S.hLS _ (S.htgts J' i)) hws hok (hD.eisLen ψ i hrec hilt)

end NestedRunFacts

/-! ## ψ⁻¹'s mixed values at the run -/

/-- **ψ⁻¹'s mixed values** at aux constructor `J'` at the fields `vs'`
over the frame `ρ` (`r1_step`'s `MIXED`): the fields, with the
hypotheses' positions replaced by ψ⁻¹'s fold term at the target
applied to the field's readings and value. -/
@[expose] noncomputable def IndRepData.invMixed (d : IndRepData V) (m : EnvModel V env) (ψ : Name → Nat)
    (k₀ n : Nat) (cd : Nat → CopyData V) (auxOfs : Nat → Nat → Nat) (s : Level) (ρ : Nat → V)
    (J' : Nat) (vs' : List V) : List V :=
  mixedVals (ConLeche.recIdxOf (d.ksR J')) (d.invUseIh k₀ J') vs'
    ((ConLeche.recIdxOf (d.ksR J')).map fun i =>
      lamTower (d.bb ψ) (consList (vs'.take i) ρ) ((d.tssR J' ψ).getD i []) fun σ'' =>
        (((d.eissR J' ψ).getD i []).map (interp V σ'') ++
          [(Semantics.frameIdx (((d.tssR J' ψ).getD i []).length) σ'').foldl SetTheory.app
            (vs'.getD i pt)]).foldl SetTheory.app
          (interp V ρ (d.invFold m ψ k₀ n cd auxOfs s (d.tgtsR J' i))))

theorem IndRepData.invMixed_length (d : IndRepData V) (m : EnvModel V env) (ψ : Name → Nat)
    (k₀ n : Nat) (cd : Nat → CopyData V) (auxOfs : Nat → Nat → Nat) (s : Level) (ρ : Nat → V)
    (J' : Nat) (vs' : List V) : (d.invMixed m ψ k₀ n cd auxOfs s ρ J' vs').length = vs'.length := by
  unfold IndRepData.invMixed; exact mixedVals_length _ _ _ _

namespace NestedRunFacts

variable {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState}
  {b : MutualBlock} {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)}
  {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
  {lpsT : List Name} {order : List Nat} {s : Level}
  (R : NestedRunFacts F env p st b params pbs mpAux d ψ cd lpsT order s)

include R

omit [SetTheory V] R in
/-- **A hypothesis position is container-recursive** at a group
without transports: the copy's field is recursive into a copy, so
(no transport) the container sees it as recursive. -/
theorem useIh_recJ {j J : Nat} {cA : ConstantVal × Nat}
    (hnoT : ∀ i, i < cA.2 → i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) → d.tgtsR (auxOfsOf st p.k cd j J) i < p.k)
    {i : Nat} (hi : i < cA.2) (hu : d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true) :
    i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) := by
  unfold IndRepData.invUseIh at hu
  obtain ⟨-, hA, hk⟩ := of_decide_eq_true hu
  refine Classical.byContradiction fun hJr => ?_
  exact absurd hk (Nat.not_le.mpr (hnoT i hi hJr hA))

/-- **A container-recursive position is a hypothesis position** of the
copy constructor (`kindR`: the copy's field is recursive into the
group-mate's copy). -/
theorem recJ_useIh {j : Nat} (hj : j < st.pins.length) {J : Nat} {cA : ConstantVal × Nat}
    (hJ : (cd j).dJ.ctorsA[J]? = some cA) {i : Nat}
    (hJr : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J)) :
    d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  obtain ⟨hks, htgt, -, -⟩ := hf.read.kindR i hJr
  have hksLenA : (d.ksR (auxOfsOf st p.k cd j J)).length = cA'.2 := by
    rw [hf.view.1]; exact hf.ctor.2.2.ksLen
  have hilt : i < cA.2 := by
    have := (mem_recIdxOf.mp hJr).1
    rw [(hrepJ.ctors J cA hJ).2.2.ksLen] at this
    exact this
  have hrecA : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) :=
    mem_recIdxOf.mpr ⟨by rw [hksLenA, hf.nF]; exact hilt, by rw [hks]; exact (mem_recIdxOf.mp hJr).2⟩
  unfold IndRepData.invUseIh
  exact decide_eq_true ⟨by rw [hf.read.mem]; omega, hrecA, by rw [htgt]; omega⟩

omit R in
/-- **The mixed values shadow the fields off the container-recursive
positions** (no transports). -/
theorem mixed_shadow {ρ : Nat → V} {j J : Nat} {cA : ConstantVal × Nat}
    (hnoT : ∀ i, i < cA.2 → i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) → d.tgtsR (auxOfsOf st p.k cd j J) i < p.k)
    {vs' : List V} (hlen : vs'.length = cA.2) :
    ShadowRel (cd j).dJ.nP ((cd j).dJ.ksF J) vs'
      (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs') := by
  refine ⟨d.invMixed_length _ _ _ _ _ _ _ _ _ _, fun l hl hr => ?_⟩
  unfold IndRepData.invMixed
  rw [mixedVals_getD _ _ _ _ hl, if_neg]
  intro hu
  have hJr := useIh_recJ (d := d) hnoT (by rw [← hlen]; exact hl) hu
  exact hr ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact (mem_recIdxOf.mp hJr).2⟩

set_option maxHeartbeats 1600000 in
/-- **The container's index readings at the mixed values are the
copy's at the fields** (`r1_step`'s `hEs`): the record's `es` (the
copy's readings are the container's instantiated at the pin, under the
fields), `interp_instSeq_under`, and the mixed values shadow the fields
off the container-recursive positions, which the container's readings
do not mention (`noBVar_entries`, `interp_congr_shadowRel`). -/
theorem es_inv {ρ : Nat → V} {j : Nat} (hj : j < st.pins.length) {J : Nat} {cA : ConstantVal × Nat}
    (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    (hnoT : ∀ i, i < cA.2 → i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) → d.tgtsR (auxOfsOf st p.k cd j J) i < p.k)
    {vs' : List V} (hlen : vs'.length = cA.2) :
    ((cd j).dJ.esF J (cd j).ψ').map (interp V (consList
        (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs')
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
      = (d.esF (auxOfsOf st p.k cd j J) ψ).map (interp V (consList vs' (consList (paramVals d.nP ρ) ρ))) := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  obtain ⟨hfindJ, -, hDJ⟩ := hrepJ.ctors J cA hJ
  have hwfJ := mpAux.base2.wf _ (Env.find?_mem hfindJ)
  obtain ⟨-, -, -, hnbEsJ⟩ := FixCtorDataI.noBVar_entries hDJ hwfJ.1 hwfJ.2.2.2.1 (cd j).ψ'
  have hsh := mixed_shadow (d := d) (mpAux := mpAux) (ψ := ψ) (s := s) (ρ := ρ) hnoT hlen
  rw [hf.read.es, List.map_map]
  apply List.map_congr_left
  intro E hE
  simp only [Function.comp_def]
  rw [interp_instSeq_under (consList (paramVals d.nP ρ) ρ) (cd j).DsA vs' _ E
    (fun hne => by
      have hpos : 0 < (cd j).DsA.length := List.length_pos_iff.mpr hne
      rw [hg.len] at hpos
      rw [hg.len, hlen]; omega)]
  have h := interp_congr_shadowRel hsh
    (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)) []
    (E := E) (by rw [hlen, List.length_nil, Nat.add_zero]; exact hnbEsJ E hE)
  simp only [consList_nil] at h
  exact h.symm

set_option maxHeartbeats 3200000 in
/-- **The per-position facts for R1 at a finitary container without
transports** (`r1_step`'s `hpos`, the first two arms; the third is
never needed, so it is any `P`): a container-recursive position is a
hypothesis position on both sides, finitary, with the copy's readings
alike at `ρ` and at the pushed frame and the container's at the mixed
values the copy's at the fields; a container-ordinary position is
ordinary on both sides. -/
theorem pos_inv (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V} {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    (hfin : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hnoT : ∀ i, i < cA.2 → i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) → d.tgtsR (auxOfsOf st p.k cd j J) i < p.k)
    {vs' : List V} (hlen : vs'.length = cA.2) (P : Nat → Prop) :
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
    P i := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  obtain ⟨hfindJ, -, hDJ⟩ := hrepJ.ctors J cA hJ
  have hD := hf.ctor.2.2
  have hwfJ := mpAux.base2.wf _ (Env.find?_mem hfindJ)
  obtain ⟨-, -, hnbEJ, -⟩ := FixCtorDataI.noBVar_entries hDJ hwfJ.1 hwfJ.2.2.2.1 (cd j).ψ'
  have hsh := mixed_shadow (d := d) (mpAux := mpAux) (ψ := ψ) (s := s) (ρ := ρ) hnoT hlen
  have hksLenA : (d.ksR (auxOfsOf st p.k cd j J)).length = cA'.2 := by
    rw [hf.view.1]; exact hf.ctor.2.2.ksLen
  intro i hi
  by_cases hA : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J)
  · -- container-recursive
    obtain ⟨hkind, htl⟩ := hfin i hA
    obtain ⟨hks, htgt, htss, heiss⟩ := hf.read.kindR i hA
    have hrecA : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) :=
      mem_recIdxOf.mpr ⟨by rw [hksLenA, hf.nF]; exact hi, Or.inl (by rw [hks]; exact hkind)⟩
    have htssA : (d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [] = [] := by rw [htss, htl]; rfl
    have htssF : (d.tssF (auxOfsOf st p.k cd j J) ψ).getD i [] = [] := by
      rw [← hf.view.2.2.2]; exact htssA
    have htake : (vs'.take i).length = i := by rw [List.length_take]; omega
    refine Or.inr (Or.inl ⟨?_, ?_, R.recJ_useIh hj hJ hA, by rw [(hg.view J).1]; exact hA, hrecA,
      by rw [← hf.view.1]; exact hrecA, by rw [(hg.view J).2.2.2]; exact htl, htssA,
      by rw [htgt, (hg.view J).2.1], hrepJ.tgtsRLt J i, ?_, ?_⟩)
    · unfold IndRepData.psiUseIh; exact decide_eq_true hA
    · unfold IndRepData.psiVia
      rw [if_neg]
      intro h
      exact h.2.1 hA
    · -- the copy's readings, alike at the two frames
      rw [← hf.view.2.2.1]
      apply List.map_congr_left
      intro E hE
      have hEb : Term.bvarsBelow (d.nP + i) E.erase := by
        have := hD.eissBelow ψ i E (by rw [← hf.view.2.2.1]; exact hE)
        rwa [htssF, List.length_nil, Nat.add_zero] at this
      exact interp_congr_below V E (d.nP + i) _ _ hEb (fun l hl =>
        consList_agree_below (n := d.nP) (fun l' hl' => (push_agree ρ ρ l' hl').symm) _ l
          (by rw [htake]; omega))
    · -- the container's readings at the mixed values are the copy's
      rw [← hf.view.2.2.1, heiss, htl, List.length_nil, Nat.add_zero, List.map_map, (hg.view J).2.2.1]
      apply List.map_congr_left
      intro E hE
      simp only [Function.comp_def]
      rw [interp_instSeq_under (consList (paramVals d.nP ρ) ρ) (cd j).DsA (vs'.take i) _ E
        (fun hne => by
          have hpos : 0 < (cd j).DsA.length := List.length_pos_iff.mpr hne
          rw [hg.len] at hpos
          rw [hg.len, htake]; omega)]
      have h := interp_congr_shadowRel (hsh.take i)
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)) []
        (E := E) (by
          rw [htake, List.length_nil, Nat.add_zero]
          have := hnbEJ i hi E hE
          rwa [htl, List.length_nil, Nat.add_zero] at this)
      simp only [consList_nil] at h
      exact h.symm
  · -- container-ordinary: ordinary or into a block member on the copy's side
    have hvia : d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J i = none := by
      unfold IndRepData.psiVia
      rw [if_neg]
      rintro ⟨h1, -, h3⟩
      exact absurd h3 (Nat.not_le.mpr (hnoT i hi hA h1))
    refine Or.inl ⟨?_, ?_⟩
    · rintro (h | h)
      · unfold IndRepData.psiUseIh at h
        exact hA (of_decide_eq_true h)
      · rw [hvia] at h
        exact nomatch h
    · unfold IndRepData.invUseIh
      apply decide_eq_false
      rintro ⟨-, h2, h3⟩
      exact absurd h3 (Nat.not_le.mpr (hnoT i hi hA h2))

/-- **The mixed values shadow the fields off the copy's recursive
positions** (the aux datum's kinds). -/
theorem mixed_shadowA {ρ : Nat → V} {j : Nat} (hj : j < st.pins.length) {J : Nat} {cA : ConstantVal × Nat}
    (hJ : (cd j).dJ.ctorsA[J]? = some cA) (vs' : List V) :
    ShadowRel d.nP (d.ksF (auxOfsOf st p.k cd j J)) vs'
      (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs') := by
  have hg := R.groupFacts hj
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  refine ⟨d.invMixed_length _ _ _ _ _ _ _ _ _ _, fun l hl hr => ?_⟩
  unfold IndRepData.invMixed
  rw [mixedVals_getD _ _ _ _ hl, if_neg]
  intro hu
  have hA := d.invUseIh_mem hu
  rw [hf.view.1] at hA
  exact hr ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact (mem_recIdxOf.mp hA).2⟩

set_option maxHeartbeats 6400000 in
/-- **ψ⁻¹'s mixed values fit the container constructor's telescope**
(`r1_step`'s `hfitMixed`; the mirror of `fitCopy_of_run`), at a
finitary container without transports: position by position
(`spineFit_of_prefix_pointwise`) — at a hypothesis position the value
is ψ⁻¹'s fold at the target applied to the field's readings and value,
in the target copy's container carrier at the pin's readings by ψ⁻¹'s
typing (`InvSetup.fold_mem_vals` at the copy's recursive-entry facts,
`invChoice_group` for the target's leaf and pins), which is the
container's recursive entry read at the mixed prefix (`interp_recEntry`
with the readings agreeing, `pos_inv`); at a field passing its value
the copy's own domain at the fields' prefix (the mixed prefix, the
domain mentioning no recursive position) is the container's under the
substitution (the record's `ord` at the mixed prefix, which fits the
container's earlier domains). -/
theorem fitMixed_of_run (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    (hfin : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hnoT : ∀ i, i < cA.2 → i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) → d.tgtsR (auxOfsOf st p.k cd j J) i < p.k)
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
  · -- a hypothesis position: container-recursive, finitary
    have hJr := useIh_recJ (d := d) hnoT hn hu
    obtain ⟨hkind, htl⟩ := hfin n hJr
    obtain ⟨hks, htgt, htss, heiss⟩ := hf.read.kindR n hJr
    have hrecA : n ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) :=
      mem_recIdxOf.mpr ⟨by rw [hksLenA, hf.nF]; exact hn, Or.inl (by rw [hks]; exact hkind)⟩
    have hrecAF : n ∈ ConLeche.recIdxOf (d.ksF (auxOfsOf st p.k cd j J)) := by rw [← hf.view.1]; exact hrecA
    have htssA : (d.tssR (auxOfsOf st p.k cd j J) ψ).getD n [] = [] := by rw [htss, htl]; rfl
    have htssF : (d.tssF (auxOfsOf st p.k cd j J) ψ).getD n [] = [] := by rw [← hf.view.2.2.2]; exact htssA
    -- the readings' agreements (`pos_inv`'s second arm)
    obtain ⟨hreadA, hreadJ⟩ :
        ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD n []).map (interp V (consList (vs'.take n) ρ))
          = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
              (interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))) ∧
        (((cd j).dJ.eissR J (cd j).ψ').getD n []).map (interp V (consList
            ((d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ (auxOfsOf st p.k cd j J) vs').take n)
            (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))
          = ((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
              (interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ))) := by
      rcases R.pos_inv tbl₀ hj hJ hfin hnoT hvsLen (fun _ => False) n hn with ⟨-, hu'⟩ |
        ⟨-, -, -, -, -, -, -, -, -, -, hreadA, hreadJ⟩ | h
      · rw [hu] at hu'; exact absurd hu' (by simp)
      · exact ⟨hreadA, hreadJ⟩
      · exact h.elim
    -- the mixed value at a hypothesis position
    have hMn : (d.invMixed mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s ρ
        (auxOfsOf st p.k cd j J) vs').getD n pt
        = (((d.eissR (auxOfsOf st p.k cd j J) ψ).getD n []).map (interp V (consList (vs'.take n) ρ)) ++
            [vs'.getD n pt]).foldl SetTheory.app
            (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
              (d.tgtsR (auxOfsOf st p.k cd j J) n))) := by
      unfold IndRepData.invMixed
      rw [mixedVals_getD _ _ _ _ hnv, hu]
      simp only [if_true]
      rw [getD_map_idxOf hrecA, htssA]
      simp only [lamTower, List.length_nil, Semantics.frameIdx, List.range_zero, List.map_nil,
        List.foldl_nil]
    -- the container's recursive entry at the mixed prefix
    have hnlt : n < cA.2 := hn
    rw [(hg.view J).2.2.1] at hreadJ
    rw [hMn, interp_recEntry hDJ (cd j).ψ' hkind hnlt htakeM hDsLen (consList (paramVals d.nP ρ) ρ),
      hreadJ, ← hreadA]
    -- ψ⁻¹'s fold at the target, typed
    have htgtA : d.tgtsR (auxOfsOf st p.k cd j J) n < d.k := hf.tgts n
    have htgtJ : (cd j).dJ.tgtsR J n < (cd j).dJ.k := hrepJ.tgtsRLt J n
    obtain ⟨hE, hx⟩ := hcff.1 n hrecAF vs' (by rw [hσ₀]; exact hvs') []
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
    have hmem := IndRepData.InvSetup.fold_mem_vals (d.withSort s) S htgtA hfitM
    have hisLen : (((d.eissF (auxOfsOf st p.k cd j J) ψ).getD n []).map
        (interp V (consList (vs'.take n) (consList (paramVals d.nP ρ) ρ)))).length
        = d.nIdxs.getD (d.tgtsR (auxOfsOf st p.k cd j J) n) 0 := by
      rw [hE.length_eq, List.length_map, rebit_length]
      exact S.hipsLen _ htgtA
    -- the target copy's leaf and pins are the container member's at the pin
    have htgtE : d.tgtsR (auxOfsOf st p.k cd j J) n = p.k + (cd j).base + (cd j).dJ.tgtsR J n := by
      rw [htgt, (hg.view J).2.1]
    obtain ⟨hL, hpins⟩ := invChoice_group R.pins hj htgtJ
    rw [← htgtE] at hL hpins
    -- the fold term and the target, at the datum
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
    rw [hL, hpins, interp_famAppAV_pins (mpAux.base2.cval_closedL _ _) _ _ hisLen, ← hreadA] at hmem'
    rw [← (hg.view J).2.1]
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

end NestedRunFacts

/-! ## The sort transfer of `chainFit_fields` -/

/-- `IndRep.chainFit_fields` at a representation at another spelling
of the sort, read at the datum (the family space and the slot set
mention the sort through `w`). -/
theorem IndRep.chainFit_fields_sorted {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : IndRepData V} {mm : Nat} {s : Level}
    (hs : ∀ φ : Name → Nat, s.eval φ = d.resSort.eval φ)
    (hrep : IndRep m T cvT cvR mI rP rules (d.withSort s) mm) (ψ : Name → Nat) {ρp : Nat → V}
    (hsat : Sat V (d.params ψ).reverse ρp) {X t : V}
    (hX : X ∈ˢ famSpace (d.w ψ) (d.idx ψ ρp)) (ht : t ∈ˢ d.idx ψ ρp) {j : Nat}
    (hj : j < d.ctorsA.length) {fs : List V} (hfit : d.ChainFit ψ ρp X t j fs) :
    ∀ (i : Nat) (F : AnnotTerm), ((d.Fss ψ).getD j [])[i]? = some F → ∀ f, fs[i]? = some f →
      ((d.rss.getD j []).getD i false = true →
        f ∈ˢ slotSet (d.w ψ) (d.u ψ) (consList (fs.take i) ρp) (((d.tlss ψ).getD j []).getD i [])
          (((d.Eiss ψ).getD j []).getD i []) X) ∧
      ((d.rss.getD j []).getD i false = false → f ∈ˢ interp V (consList (fs.take i) ρp) F) := by
  have h := hrep.chainFit_fields ψ hsat (by rw [d.withSort_w, hs ψ]; exact hX) ht hj hfit
  rw [d.withSort_w, hs ψ] at h
  exact h

namespace NestedRunFacts

variable {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState}
  {b : MutualBlock} {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)}
  {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
  {lpsT : List Name} {order : List Nat} {s : Level}
  (R : NestedRunFacts F env p st b params pbs mpAux d ψ cd lpsT order s)

include R

/-! ## R1's step at the run -/

set_option maxHeartbeats 6400000 in
/-- **R1's STEP at the run** (task #279 M-C′ step 5, DESIGN §M.36): at
every scratch constructor `J'` and spine `fs` chain-fitting at the
carrier restricted to R1's predicate, the predicate holds of `inj J'
fs` — at a copy constructor by `r1_step` with every hypothesis derived
(`copyCtor_repr` names the pin and the container constructor; the ι
laws `inv_iota`/`psi_iota`; the heads `psiHead_interp`/`headφ_of_run`;
`fitMixed_of_run`, `es_inv`, `pos_inv`; the readings' facts
`ctor_facts_aux`; the fields' fit and the induction hypotheses
`fieldsFit_of_chainFit` at the sorted representations); at a REAL
member's constructor vacuously (the terminator recovers a real member,
`idxRecover`, while the predicate speaks of copies).  Restrictions:
every container finitary without transports and with a nonzero
elimination bit (`hfin`, `hnoT`, `hbJ`), the scratch block's own bit
nonzero (`hbA`), and the scratch block FINITARY (`hfinA`: no reflexive
field anywhere — a copy's field into a block member may be reflexive,
the REFLEXIVE arm). -/
theorem r1_hstep (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0)
    (hbJ : ∀ j, j < st.pins.length → (cd j).dJ.bb (cd j).ψ' ≠ 0)
    (hfin : ∀ j, j < st.pins.length → ∀ J i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hnoT : ∀ j, j < st.pins.length → ∀ J cA, (cd j).dJ.ctorsA[J]? = some cA → ∀ i, i < cA.2 →
      i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) → i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) →
      d.tgtsR (auxOfsOf st p.k cd j J) i < p.k)
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
      (R.fitMixed_of_run tbl₀ hρ hj hJc (hfin j hj Jc) (hnoT j hj Jc cAJ hJc) hfit)
      (R.es_inv (ρ := ρ) hj hJc (hnoT j hj Jc cAJ hJc) hvsN')
      (fun i hi => (R.pos_inv tbl₀ (ρ := ρ) hj hJc (hfin j hj Jc) (hnoT j hj Jc cAJ hJc) hvsN'
        (fun _ => False) i (by rw [← hf.nF]; exact hi)).imp_right (Or.imp_right False.elim))
  · -- a real member's constructor: the predicate speaks of copies
    intro t' hk₀ ht' is' his' htupE
    obtain ⟨s'', cvT'', cvR'', mI'', rP'', rules'', -, hrep''⟩ := R.repsAt_of_reps t' ht'
    rw [htupE] at hall
    have h := hrep''.idxRecover ψ (consList (paramVals d.nP ρ) ρ) hsat₀ is' his' _ J' fs hJ'lt hlen
      hEsOk hEsFit hall
    have hmem : d.mems J' = t' := h.1
    omega

/-- **R1 AT THE RUN** (task #279 M-C′ step 5, DESIGN §M.36): at pin
`j`'s group member `t` (the copy `p.k + base + t`), at any parameter
frame `ρ` (the parameter variables as the parameters), ψ⁻¹'s fold term
then ψ's final table's entry is the identity on the copy's carrier —
`r1At_of_step` at the copy's representation with the step `r1_hstep`
(the induction runs over the whole scratch block: a transport's target
would be the same induction's hypothesis; none here). -/
theorem r1At_of_run (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hbA : d.bb ψ ≠ 0)
    (hbJ : ∀ j, j < st.pins.length → (cd j).dJ.bb (cd j).ψ' ≠ 0)
    (hfin : ∀ j, j < st.pins.length → ∀ J i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hnoT : ∀ j, j < st.pins.length → ∀ J cA, (cd j).dJ.ctorsA[J]? = some cA → ∀ i, i < cA.2 →
      i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) → i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) →
      d.tgtsR (auxOfsOf st p.k cd j J) i < p.k)
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
    (R.r1_hstep tbl₀ hρ hbA hbJ hfin hnoT hfinA)
  rw [show p.k + (cd j).base + t - p.k = (cd j).base + t by omega] at h
  exact h

end NestedRunFacts

end ConLeche.Model
