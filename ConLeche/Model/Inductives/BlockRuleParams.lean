module

public import ConLeche.Model.Inductives.BlockRecData

public section

/-!
# The equation list's LEVEL-PARAMETER invariance

`heqP` — the equation list reads alike at two level valuations that
agree on a recursor's own `levelParams` — needs every one of the six
components to be ψ-congruent there.  Five of them are readings of
stored data whose parameter-invariance is already in the tree (the
recursor types' readings, the constructors' record `params`,
`tssParams`, `eissParams`, the leaves' `acval_params`); the sixth,
`Rb0`, is the reading of the residue OPENED at the rule's whole frame,
and the opening puts `fvar` openers into the term.

`denoteMeta_params_ext` asks `allLevelParamsDefined` of the read term,
and that predicate looks INSIDE an `fvar`'s type annotation — which
`denoteMeta` never reads (an opener reads as its de Bruijn slot).  So
the kit here is `lpDefF`, the same footprint with the `fvar` types
ignored: the residue has it (it is fvar-free and its parameters are
the stored rule's), an opening at fvars keeps it, and the reading is
ψ-congruent under it (`Model/Annot/LpDefF.lean`).  No opener TYPE has
to be tracked, so no level-parameter twin of the `ConstsBound` kit (over `blockIhPis`, the
openers' types and the binder datum) is needed. -/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}


/-! ## 3. The six components, ψ-congruent at a recursor's parameters -/

section Components

open ConLeche (BlockParts)

variable {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **A recursor's level parameters ARE the pinned list** — stage (a)'s
`blockRecLpsOk`, carried to the stored record by `checkConstantVal`
(`recStage_lps`' own two steps, kept). -/
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

/-- **`fdoms`** — the constructor's field domains, through the record's
`params` (`blockRuleFdomsAV_eq`). -/
theorem blockRuleFdomsAV_params {mpC : EnvModelM V μ envC}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {T : Name} {lps : List Name}
    {nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr}
    (hcd : BlockCtorDataI mpC.base2 T lps cA.1 p.nP cA.2 nIdx resSort
      isProp large idxArgs ds Es srcs fvsP xFvs xrest)
    (hCf : cA.1.type.hasFvar = false)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) {ψ₁ ψ₂ : Name → Nat}
    (hq : ∀ q ∈ cA.1.levelParams, ψ₁ q = ψ₂ q) :
    blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ₁ c i
      = blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ₂ c i := by
  rw [(blockRuleFdomsAV_eq (hm := hm) h hr hcA hrhs hcd hCf hnP ψ₁).1,
    (blockRuleFdomsAV_eq (hm := hm) h hr hcA hrhs hcd hCf hnP ψ₂).1, (hcd.params ψ₁ ψ₂ hq).1]

/-- **`es`** — the constructor's index readings, through the record's
`params` (`blockRuleEsAV_eq`). -/
theorem blockRuleEsAV_params {mpC : EnvModelM V μ envC}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {T : Name} {lps : List Name}
    {nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr}
    (hcd : BlockCtorDataI mpC.base2 T lps cA.1 p.nP cA.2 nIdx resSort
      isProp large idxArgs ds Es srcs fvsP xFvs xrest)
    (hCf : cA.1.type.hasFvar = false)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) {ψ₁ ψ₂ : Name → Nat}
    (hq : ∀ q ∈ cA.1.levelParams, ψ₁ q = ψ₂ q) :
    blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ₁ c i
      = blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ₂ c i := by
  rw [blockRuleEsAV_eq (hm := hm) h hr hcA hrhs hcd hCf hnP ψ₁,
    blockRuleEsAV_eq (hm := hm) h hr hcA hrhs hcd hCf hnP ψ₂, (hcd.params ψ₁ ψ₂ hq).2]

/-- **`mk`** — the constructor's leaf at the identity instantiation,
through the leaf's `acval_params` (`blockRuleMkAV_eq`). -/
theorem blockRuleMkAV_params {mpC : EnvModelM V μ envC}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {ci : ConstantInfo} (hfind : envC.find? cA.1.name = some ci)
    (hlps : ci.toConstantVal.levelParams = p.lps)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) {ψ₁ ψ₂ : Name → Nat}
    (hq : ∀ q ∈ p.lps, ψ₁ q = ψ₂ q) :
    blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ₁ c i
      = blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ₂ c i := by
  rw [blockRuleMkAV_eq (hm := hm) h hr hcA hrhs hfind hlps hnP ψ₁,
    blockRuleMkAV_eq (hm := hm) h hr hcA hrhs hfind hlps hnP ψ₂]
  have hq' : ∀ q ∈ p.lps, Level.substFn ψ₁ p.lps (p.lps.map Level.param) q
      = Level.substFn ψ₂ p.lps (p.lps.map Level.param) q :=
    Level.substFn_ext hq (fun u hu => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hu
      simp [Level.allParamsDefined, hq]) (List.length_map _)
  rw [mpC.base2.acval_params _ ci hfind _ _ (fun q hqm => hq' q (hlps ▸ hqm))]

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
