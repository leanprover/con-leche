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

end ConLeche.Model
