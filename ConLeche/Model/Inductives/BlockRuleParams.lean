module

public import ConLeche.Model.Inductives.BlockRecData

public section

/-!
# The equation list's LEVEL-PARAMETER invariance

`heqP` — the equation list reads alike at two level valuations that
agree on a recursor's own `levelParams` — needs each of its six
components ψ-congruent there.  This file has the recursors' pinned
level parameters, the congruence of `pdoms`, and the equation list's
congruence in its components.  The opened residue `Rb0` carries `fvar`
openers, whose type annotations `denoteMeta` never reads; its
congruence goes through `lpDefF` (`Model/Annot/LpDefF.lean`), the
`allLevelParamsDefined` footprint with `fvar` types ignored. -/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}


/-! ## The six components, ψ-congruent at a recursor's parameters -/

section Components

open ConLeche (BlockParts)

variable {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **A recursor's level parameters ARE the pinned list** — stage (a)'s
`blockRecLpsOk`, carried to the stored record by `checkConstantVal`. -/
theorem recStage_lpsPin
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) :
    r.1.levelParams = if p.toBlockShape.large then p.elim :: p.lps else p.lps := by
  obtain ⟨hpins, hlenR, hall⟩ := recStageG_recNames h
  have hnl : i < p.recs.length := by
    have hql := (List.getElem?_eq_some_iff.mp hr).1
    omega
  obtain ⟨rc, q', hrc, hq', -, hcv, -, -⟩ := hall i hnl
  obtain rfl := Option.some.inj (hr.symm.trans hq')
  obtain ⟨-, -, -, -, -, -, type, -, -, -, -, -, -, -, hcv'⟩ :=
    ConLeche.checkConstantVal_inv hcv
  have hlps := List.all_eq_true.mp hpins.1 rc (List.mem_of_getElem? hrc)
  rw [show r.1.levelParams = rc.cvR.levelParams by rw [hcv']]
  by_cases hb : p.toBlockShape.large = true
  · rw [if_pos hb] at hlps ⊢
    exact eq_of_beq hlps
  · rw [if_neg hb] at hlps ⊢
    exact eq_of_beq hlps

/-- The block's own parameters are among every recursor's. -/
theorem recStage_lps_sub
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) : ∀ q ∈ p.lps, q ∈ r.1.levelParams := by
  intro q hq
  rw [recStage_lpsPin h hr]
  split
  · exact List.mem_cons_of_mem _ hq
  · exact hq

/-- **`pdoms`** — the recursor type's binder data, off its reading
(`recStage_tyPis`), which is ψ-congruent at any recursor's
parameters (`blockRecTyAV_params_ext`). -/
theorem blockRulePdomsAV_params (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) {ψ₁ ψ₂ : Name → Nat} (hq : ∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q)
    {c : Nat} (hc : c < rs.length) :
    blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ₁ c
      = blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ₂ c := by
  have hrc : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  obtain ⟨-, -, -, -, hM₁, hN₁, -⟩ := recStage_tyPis hμ mpC h hrc ψ₁
  obtain ⟨-, -, -, -, hM₂, hN₂, -⟩ := recStage_tyPis hμ mpC h hrc ψ₂
  have hT := blockRecTyAV_params_ext hμ mpC h hr hq hc
  have hs₁ := stripPisAV_mkPisAV (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ₁ c)
    (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ₁ c)
  have hs₂ := stripPisAV_mkPisAV (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ₂ c)
    (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ₂ c)
  rw [← hM₁, hT, hM₂, hN₁, ← hN₂, hs₂] at hs₁
  have hR : blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ₂ c
      = blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ₁ c :=
    congrArg Prod.fst (Option.some.inj hs₁)
  simp only [blockRulePdomsAV, hR]


omit [SetTheory V] in
/-- Every member of a successful opening is an `fvar`. -/
theorem openPisAtFvars_mem_fvar {n E : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : ConLeche.openPisAtFvars n e E = some (fvs, o)) :
    ∀ x ∈ fvs, ∃ (i : Nat) (t : Expr), x = .fvar i t := by
  intro x hx
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index n e E hop j x hj
  exact ⟨_, ty, hty⟩

/-- **The equation list is congruent in its six components** below
`K` and the rule counts. -/
theorem blockIotaEqsAV_congr {K : Nat} {nCt : Nat → Nat}
    {pdoms pdoms' : Nat → List AnnotTerm} {fdoms fdoms' es es' ihs ihs' : Nat → Nat → List AnnotTerm}
    {mk mk' Rb Rb' : Nat → Nat → AnnotTerm}
    (hp : ∀ c, c < K → pdoms c = pdoms' c)
    (hrest : ∀ c, c < K → ∀ j, j < nCt c →
      fdoms c j = fdoms' c j ∧ es c j = es' c j ∧ ihs c j = ihs' c j ∧ mk c j = mk' c j ∧
        Rb c j = Rb' c j) :
    blockIotaEqsAV K nCt pdoms fdoms es ihs mk Rb
      = blockIotaEqsAV K nCt pdoms' fdoms' es' ihs' mk' Rb' := by
  rw [blockIotaEqsAV, blockIotaEqsAV]
  show (List.range K).flatMap _ = (List.range K).flatMap _
  rw [List.flatMap, List.flatMap]
  refine congrArg List.flatten (List.map_congr_left fun c hc => ?_)
  have hcK := List.mem_range.mp hc
  refine List.map_congr_left fun j hj => ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := hrest c hcK j (List.mem_range.mp hj)
  simp only [hp c hcK, h1, h2, h3, h4, h5]

end Components

end ConLeche.Model
