module

public import ConLeche.Model.Inductives.FoldBelow
public import ConLeche.Model.Inductives.InvCopy
import ConLeche.Model.Inductives.FixCtorReads

public section

/-!
# The folds are closed above the parameters, and fire at VALUES (task #279 M-C′ step 2 (i), DESIGN §M.33)

`FoldBelow.lean` bounds the fold term of a choice.  This module
instantiates the bound at the two folds and draws the consequence the
round trips need:

* **ψ⁻¹** (`InvSetup.foldTerm_below`, with `invL_below`/`invPinsT_below`/
  `invHead_below`): at the parameter variables `paramBvarsAt d.nP d.nP`
  the fold term is `Term.bvarsBelow d.nP` — it reads a frame only
  through the block's parameters;
* **ψ** (`psiTerm_below`, `psiFold_below`): ψ's term at a copy is
  `bvarsBelow d.nP` at the SCRATCH block's parameter frame when the
  table's terms it transports through are, and along the kernel order
  every table entry is (`TopoOrder.orderFold_all` with the bound as the
  invariant — the same induction as `psiFold_typed`);
* **the "double push"** (`push_agree`, `map_liftBvars_push`): the
  frame `consList psvals (consList vs σ)` — the parameter values
  `psvals = paramVals nP σ` pushed above the field values `vs` — agrees
  with `σ` below `nP`, so a `bvarsBelow nP` term reads alike at both
  (`interp_congr_below`), while the lifted field variables
  `(fieldBvars nF).map (·.liftN nP 0)` read `vs`;
* **ι at values** (`InvSetup.fold_iota_vals`, `PsiSetup.fold_iota_vals`):
  the kit's ι fired at the pushed frame, with the setup there (the
  run level's `∀ ρ ps`), the field variables as the field terms and the
  parameter variables as the parameters, restated over `σ`: the fold
  term at a constructor's index readings and the constructor at the
  VALUES is the head at the mixed values, every hypothesis the fold at
  the target member applied under the field's telescope.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Frames -/

/-- The parameter values of a parameter frame: the parameter variables
read there (outermost first). -/
noncomputable def paramVals (nP : Nat) (σ : Nat → V) : List V :=
  (paramBvarsAt nP nP).map (interp V σ)

theorem paramVals_length (nP : Nat) (σ : Nat → V) : (paramVals nP σ).length = nP := by
  simp [paramVals, paramBvarsAt]

omit [SetTheory V] in
/-- Two frames agreeing below `n` still agree below `xs.length + n`
under a common spine. -/
theorem consList_agree_below {n : Nat} {ρ₁ ρ₂ : Nat → V} (h : ∀ i, i < n → ρ₁ i = ρ₂ i) :
    ∀ (xs : List V) (i : Nat), i < xs.length + n → consList xs ρ₁ i = consList xs ρ₂ i
  | [], i, hi => h i (by simpa using hi)
  | x :: xs, i, hi => by
    rw [consList_cons, consList_cons]
    refine consList_agree_below (n := n + 1) (ρ₁ := cons x ρ₁) (ρ₂ := cons x ρ₂) ?_ xs i
      (by simp only [List.length_cons] at hi; omega)
    intro j hj
    cases j with
    | zero => rfl
    | succ j => exact h j (by omega)

/-- **The push**: the parameter values of `σ` pushed on ANY frame agree
with `σ` below `nP`. -/
theorem push_agree {nP : Nat} (σ ρ' : Nat → V) :
    ∀ i, i < nP → consList (paramVals nP σ) ρ' i = σ i := by
  intro i hi
  have hlen := paramVals_length nP σ
  rw [consList_getD_lt _ _ _ (by omega), hlen]
  have : (paramVals nP σ)[nP - 1 - i]? = some (σ i) := by
    unfold paramVals paramBvarsAt
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, interp_bvar]
    rw [show nP - 1 - (nP - 1 - i) = i by omega]
  rw [List.getD_eq_getElem?_getD, this]
  rfl

/-- The lifted field variables read the field values under the pushed
parameters. -/
theorem map_liftBvars_push {nP nF : Nat} {psv vs : List V} (hp : psv.length = nP)
    (hv : vs.length = nF) (σ : Nat → V) :
    ((fieldBvars nF).map (·.liftN nP 0)).map (interp V (consList psv (consList vs σ))) = vs := by
  apply List.ext_getElem
  · simp [fieldBvars, hv]
  · intro k h1 h2
    have hk : k < nF := by simpa [fieldBvars] using h1
    simp only [List.getElem_map, fieldBvars, List.getElem_range, AnnotTerm.liftN_bvar, interp_bvar]
    rw [if_neg (Nat.not_lt_zero _), ← hp, consList_apply_add, consList_getD_lt _ _ _ (by omega), hv,
      show nF - 1 - (nF - 1 - k) = k by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]

/-- A tower reads alike at two bottoms agreeing below `n` when its
domains are bounded at `n` plus their depth and the bodies agree at
every fitting spine (`lamTower_congr_bottom` with a margin). -/
theorem lamTower_congr_agree {m n : Nat} {g₁ g₂ : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {as : List V} {ρ₁ ρ₂ : Nat → V},
      (∀ i, i < n → ρ₁ i = ρ₂ i) →
      (∀ k d, ds[k]? = some d → Term.bvarsBelow (n + as.length + k) d.2.2.erase) →
      (∀ bs, SpineFit (consList as ρ₁) (ds.map (·.2.2)) bs →
        g₁ (consList (as ++ bs) ρ₁) = g₂ (consList (as ++ bs) ρ₂)) →
      lamTower m (consList as ρ₁) ds g₁ = lamTower m (consList as ρ₂) ds g₂
  | [], as, ρ₁, ρ₂, _, _, hg => by
    show g₁ (consList as ρ₁) = g₂ (consList as ρ₂)
    have := hg [] trivial
    simpa using this
  | d :: ds, as, ρ₁, ρ₂, hρ, hcl, hg => by
    show lamR m (interp V (consList as ρ₁) d.2.2) (fun a => lamTower m (cons a (consList as ρ₁)) ds g₁)
      = lamR m (interp V (consList as ρ₂) d.2.2) (fun a => lamTower m (cons a (consList as ρ₂)) ds g₂)
    have hdom : interp V (consList as ρ₁) d.2.2 = interp V (consList as ρ₂) d.2.2 :=
      interp_congr_below V d.2.2 (n + as.length) _ _
        (by have := hcl 0 d rfl; simpa using this)
        (fun i hi => consList_agree_below hρ as i (by omega))
    rw [hdom]
    refine lamR_congr fun a ha => ?_
    rw [consList_snoc', consList_snoc']
    refine lamTower_congr_agree (as := as ++ [a]) hρ ?_ ?_
    · intro k d' hd'
      have := hcl (k + 1) d' (by simpa using hd')
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    · intro bs hbs
      have := hg (a :: bs) ⟨by show a ∈ˢ interp V (consList as ρ₁) d.2.2; rw [hdom]; exact ha,
        by rw [consList_snoc']; exact hbs⟩
      simpa [List.append_assoc] using this

namespace IndRepData

variable (d : IndRepData V)

/-! ## The minor data of a real constructor is bounded -/

omit [SetTheory V] in
/-- The recursor-view datum of constructor `J` of a block without copies. -/
theorem cdsR_getD_of {ψ : Name → Nat} (hctorsC : d.ctorsC = []) {J : Nat} {cA : ConstantVal × Nat}
    (hj : d.ctorsA[J]? = some cA) :
    (d.cdsR ψ).getD J default
      = (cA.1.name, cA.2, d.dsF J ψ, d.esF J ψ, ConLeche.recIdxOf (d.ksR J), d.eissR J ψ,
          d.tssR J ψ) := by
  unfold IndRepData.cdsR IndRepData.ctorsAll
  rw [List.getD_eq_getElem?_getD, fixCtorDataList_getElem?, Nat.zero_add, hctorsC, List.append_nil,
    hj]
  rfl

omit [SetTheory V] in
theorem ctorsAll_getD_of (hctorsC : d.ctorsC = []) {J : Nat} {cA : ConstantVal × Nat}
    (hj : d.ctorsA[J]? = some cA) : d.ctorsAll.getD J default = cA := by
  unfold IndRepData.ctorsAll
  rw [List.getD_eq_getElem?_getD, hctorsC, List.append_nil, hj]
  rfl

/-- **The minor data of a real constructor is bounded** at the minor's
frame, from the constructor's data (`FixCtorDataI.below`/`tssBelow`/
`eissBelow`) through the recursor view. -/
theorem minorData_below_of {lpsT : List Name} (m : EnvModel V env) {ψ : Name → Nat}
    (hctorsC : d.ctorsC = [])
    (hview : ∀ J, d.ksR J = d.ksF J ∧ d.tgtsR J = d.tgts J ∧ d.eissR J = d.eissF J ∧
      d.tssR J = d.tssF J)
    {J : Nat} {cA : ConstantVal × Nat} (hj : d.ctorsA[J]? = some cA)
    (hC : FixCtorFactsAt m d.env₀ (d.memberName (d.mems J)) lpsT d.nP (d.nIdxAt (d.mems J))
      d.resSort d.isProp d.large d.idxF d.dsF d.esF d.srcsF d.ksF d.fvsPF d.xFvsF d.xrestF d.eissF
      d.tssF J cA (fun i => d.memberName (d.tgts J i)) (fun i => d.nIdxAt (d.tgts J i)))
    (mm : Nat) :
    DomsBelow (d.nP + mm + (d.k + J))
      (minorDataAV (d.tgtsR J) d.nP ((d.cdsR ψ).getD J default).2.1 (d.bb ψ) (d.k + J)
        ((d.cdsR ψ).getD J default).2.2.1 ((d.cdsR ψ).getD J default).2.2.2.2.1
        ((d.cdsR ψ).getD J default).2.2.2.2.2.2 ((d.cdsR ψ).getD J default).2.2.2.2.2.1) := by
  rw [d.cdsR_getD_of hctorsC hj]
  dsimp only
  have hD := hC.2.2
  obtain ⟨hks, -, heiss, htss⟩ := hview J
  refine minorDataAV_below (hD.below ψ) (hD.len ψ) ?_
  intro i hi
  rw [hks] at hi
  obtain ⟨hlt, -⟩ := mem_recIdxOf.mp hi
  rw [hD.ksLen] at hlt
  refine ⟨hlt, ?_, ?_⟩
  · rw [htss]; exact domsBelow_mono (by omega) (hD.tssBelow ψ i)
  · rw [heiss, htss]
    intro E hE
    exact Term.bvarsBelow.mono (by omega) (hD.eissBelow ψ i E hE)

/-- The minor data's length at a real constructor. -/
theorem minorData_length_of {lpsT : List Name} (m : EnvModel V env) {ψ : Name → Nat}
    (hctorsC : d.ctorsC = []) {J : Nat} {cA : ConstantVal × Nat} (hj : d.ctorsA[J]? = some cA)
    (hC : FixCtorFactsAt m d.env₀ (d.memberName (d.mems J)) lpsT d.nP (d.nIdxAt (d.mems J))
      d.resSort d.isProp d.large d.idxF d.dsF d.esF d.srcsF d.ksF d.fvsPF d.xFvsF d.xrestF d.eissF
      d.tssF J cA (fun i => d.memberName (d.tgts J i)) (fun i => d.nIdxAt (d.tgts J i))) :
    (minorDataAV (d.tgtsR J) d.nP ((d.cdsR ψ).getD J default).2.1 (d.bb ψ) (d.k + J)
        ((d.cdsR ψ).getD J default).2.2.1 ((d.cdsR ψ).getD J default).2.2.2.2.1
        ((d.cdsR ψ).getD J default).2.2.2.2.2.2 ((d.cdsR ψ).getD J default).2.2.2.2.2.1).length
      = (d.ctorsAll.getD J default).2 + (ConLeche.recIdxOf (d.ksR J)).length := by
  rw [d.cdsR_getD_of hctorsC hj, d.ctorsAll_getD_of hctorsC hj]
  dsimp only
  exact minorDataAV_length (hC.2.2.len ψ)

/-- A member's index binder data are bounded at the parameters (the
former's data, `FormerData.below`). -/
theorem ipss_below_of_indRep {μ : CheckMode} {mp : EnvModelM V μ env} {T : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {t₀ : Nat}
    (hrep : IndRep mp.base2 T cvT cvR mI rP rules d t₀) (hkR : d.kReal = d.k) (ψ : Name → Nat)
    {t : Nat} (ht : t < d.k) : DomsBelow d.nP ((d.ipss ψ).getD t []) := by
  obtain ⟨cv, capsT, hf⟩ := hrep.membersFound t ht
  have hFD := hrep.formersRead t (by rw [hkR]; exact ht) cv capsT hf
  have hget : (d.ipss ψ).getD t [] = (d.ppsM t ψ).drop d.nP := by
    simp [IndRepData.ipss, List.getD_eq_getElem?_getD, List.getElem?_range ht]
  rw [hget]
  have := DomsBelow.drop d.nP (hFD.below ψ)
  simpa using this

/-! ## ψ⁻¹'s fold term is closed above the parameters -/

namespace InvSetup

variable {μ : CheckMode} {mp : EnvModelM V μ env} {lps lpsT : List Name} {ψ : Name → Nat}
  {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm}
  {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool}

/-- **ψ⁻¹'s fold term is bounded at the outer margin** when the
parameters, the leaves, the pins and the heads are (the datum's own
parts are bounded by the setup's constructor facts). -/
theorem foldTerm_below (S : d.InvSetup mp lps lpsT ψ ρ ps L pinsT head useIh) {mm t : Nat}
    (hpsB : ∀ p ∈ ps, Term.bvarsBelow mm p.erase)
    (hips : ∀ t, t < d.k → DomsBelow d.nP ((d.ipss ψ).getD t []))
    (hL : ∀ t, t < d.k → Term.bvarsBelow 0 (L t).erase)
    (hpinsT : ∀ t, t < d.k → ∀ p ∈ pinsT t, Term.bvarsBelow (d.nP + mm) p.erase)
    (hhead : ∀ J, J < d.nAll → Term.bvarsBelow (d.nP + mm) (head J).erase) :
    Term.bvarsBelow mm (d.foldTermAV mp.base2 ψ ps L pinsT (d.invBodyAV head useIh) t).erase := by
  refine d.foldTermAV_below mp.base2 S.hps hpsB hips S.hipsLen hL hpinsT ?_ ?_ ?_
  · intro t _ p hp
    rw [S.hpins t] at hp
    exact Term.bvarsBelow.mono (by omega) (paramBvarsAt_below (Nat.le_refl _) p hp)
  · intro J hJ
    have hJA : J < d.ctorsA.length := by rw [← S.nAll_eq]; exact hJ
    exact d.minorData_below_of mp.base2 S.hctorsC S.hview (List.getElem?_eq_getElem hJA)
      (S.hctors J _ (List.getElem?_eq_getElem hJA)) mm
  · intro J hJ
    have hJA : J < d.ctorsA.length := by rw [← S.nAll_eq]; exact hJ
    rw [d.minorData_length_of mp.base2 S.hctorsC (List.getElem?_eq_getElem hJA)
      (S.hctors J _ (List.getElem?_eq_getElem hJA))]
    exact d.invBodyAV_below (hhead J hJ)

end InvSetup

/-! ## ψ's fold term is closed above the parameters -/

namespace PsiSetup

variable {μ : CheckMode} {mp : EnvModelM V μ env} {lps lpsT : List Name} {ψ : Name → Nat}
  {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm}
  {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {via : Nat → Nat → Option ViaSpec}
  {TgV domA : Nat → Nat → AnnotTerm}

/-- **ψ's fold term is bounded at the outer margin** when the
parameters, the leaves, the pins, the heads and the transports are. -/
theorem foldTerm_below (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV domA)
    {mm t : Nat} (hpsB : ∀ p ∈ ps, Term.bvarsBelow mm p.erase)
    (hips : ∀ t, t < d.k → DomsBelow d.nP ((d.ipss ψ).getD t []))
    (hL : ∀ t, t < d.k → Term.bvarsBelow 0 (L t).erase)
    (hpinsT : ∀ t, t < d.k → ∀ p ∈ pinsT t, Term.bvarsBelow (d.nP + mm) p.erase)
    (hhead : ∀ J, J < d.nAll → Term.bvarsBelow (d.nP + mm) (head J).erase)
    (hvia : ∀ J, J < d.nAll → ∀ i, i < (d.ctorsAll.getD J default).2 → ∀ Ψ Eis tl,
      via J i = some (Ψ, Eis, tl) →
      Term.bvarsBelow (d.nP + mm) Ψ.erase ∧ DomsBelow (d.nP + i + mm) tl ∧
      ∀ E ∈ Eis, Term.bvarsBelow (d.nP + i + tl.length + mm) E.erase) :
    Term.bvarsBelow mm (d.foldTermAV mp.base2 ψ ps L pinsT (d.psiBodyAV head useIh via) t).erase := by
  refine d.foldTermAV_below mp.base2 S.hps hpsB hips S.hipsLen hL hpinsT ?_ ?_ ?_
  · intro t _ p hp
    rw [S.hpins t] at hp
    exact Term.bvarsBelow.mono (by omega) (paramBvarsAt_below (Nat.le_refl _) p hp)
  · intro J hJ
    have hJA : J < d.ctorsA.length := by rw [← S.nAll_eq]; exact hJ
    exact d.minorData_below_of mp.base2 S.hctorsC S.hview (List.getElem?_eq_getElem hJA)
      (S.hctors J _ (List.getElem?_eq_getElem hJA)) mm
  · intro J hJ
    have hJA : J < d.ctorsA.length := by rw [← S.nAll_eq]; exact hJ
    rw [d.minorData_length_of mp.base2 S.hctorsC (List.getElem?_eq_getElem hJA)
      (S.hctors J _ (List.getElem?_eq_getElem hJA))]
    exact d.psiBodyAV_below (hhead J hJ) (hvia J hJ)

end PsiSetup

/-! ## The ψ⁻¹ choice is bounded -/

/-- The leaves of the ψ⁻¹ choice are closed. -/
theorem invL_below (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (cd : Nat → CopyData V) :
    ∀ t, Term.bvarsBelow 0 (d.invL m ψ k₀ cd t).erase := by
  intro t
  unfold IndRepData.invL
  split
  · exact m.cval_closedL _ ψ
  · exact m.cval_closedL _ _

omit [SetTheory V] in
/-- The pins of the ψ⁻¹ choice are bounded at the parameters when the
copies' pin readings are. -/
theorem invPinsT_below {k₀ : Nat} {cd : Nat → CopyData V}
    (hDsA : ∀ j, ∀ q ∈ (cd j).DsA, Term.bvarsBelow d.nP q.erase) :
    ∀ t, ∀ p ∈ d.invPinsT k₀ cd t, Term.bvarsBelow d.nP p.erase := by
  intro t p hp
  unfold IndRepData.invPinsT at hp
  split at hp
  · exact paramBvarsAt_below (Nat.le_refl _) p hp
  · exact hDsA _ p hp

/-- The heads of the ψ⁻¹ choice are bounded at the parameters when the
copies' pin readings are. -/
theorem invHead_below (m : EnvModel V env) (ψ : Name → Nat) (n : Nat) {cd : Nat → CopyData V}
    (auxOfs : Nat → Nat → Nat) (hDsA : ∀ j, ∀ q ∈ (cd j).DsA, Term.bvarsBelow d.nP q.erase) :
    ∀ J, Term.bvarsBelow d.nP (d.invHead m ψ n cd auxOfs J).erase := by
  intro J
  unfold IndRepData.invHead
  split
  · rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le _) (m.cval_closedL _ _)) ?_
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    exact hDsA _ a' ha'
  · rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le _) (m.cval_closedL _ _)) ?_
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    exact paramBvarsAt_below (Nat.le_refl _) a' ha'

/-! ## ψ's terms are bounded, along the order -/

omit [SetTheory V] in
/-- The block's parameters seen from under a container's pin readings
are bounded at the two parameter counts. -/
theorem psiPinsT_below (nPJ : Nat) :
    ∀ t, ∀ p ∈ d.psiPinsT nPJ t, Term.bvarsBelow (nPJ + d.nP) p.erase := by
  intro t p hp
  unfold IndRepData.psiPinsT at hp
  have := paramBvarsAt_below (D := d.nP + nPJ) (by omega) p hp
  rwa [Nat.add_comm] at this

theorem psiHead_below (m : EnvModel V env) (ψ : Name → Nat) (nPJ : Nat) (auxOf : Nat → Nat) :
    ∀ Jc, Term.bvarsBelow (nPJ + d.nP) (d.psiHead m ψ nPJ auxOf Jc).erase := by
  intro Jc
  unfold IndRepData.psiHead
  rw [AnnotTerm.erase_liftN]
  have : Term.bvarsBelow d.nP
      (AnnotTerm.mkAppN (m.acval (d.ctorsA.getD (auxOf Jc) default).1.name ψ)
        (paramBvarsAt d.nP d.nP)).erase := by
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le _) (m.cval_closedL _ _)) ?_
    intro a ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    exact paramBvarsAt_below (Nat.le_refl _) a' ha'
  have := VExprAux.bvarsBelow_liftN nPJ _ _ 0 this
  rwa [Nat.add_comm] at this

/-- **ψ's term at a copy is bounded at the scratch block's parameters**
when the copy's pin readings and the table's terms it transports
through are. -/
theorem psiTerm_below {μ : CheckMode} {mp : EnvModelM V μ env} {ψ : Name → Nat} {k₀ : Nat}
    {lpsT : List Name} {cd : Nat → CopyData V} {c : CopyData V} {auxOf : Nat → Nat}
    (hg : GroupFacts mp d ψ k₀ lpsT cd c auxOf)
    (hviewA : ∀ J, d.ksR J = d.ksF J ∧ d.tgtsR J = d.tgts J ∧ d.eissR J = d.eissF J ∧
      d.tssR J = d.tssF J)
    (hDsA : ∀ q ∈ c.DsA, Term.bvarsBelow d.nP q.erase) (tbl : Nat → AnnotTerm)
    (htbl : ∀ Jc cAJ, c.dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) → i ∉ ConLeche.recIdxOf (c.dJ.ksF Jc) →
      k₀ ≤ d.tgtsR (auxOf Jc) i → Term.bvarsBelow d.nP (tbl (d.tgtsR (auxOf Jc) i - k₀)).erase) :
    Term.bvarsBelow d.nP (d.psiTerm mp.base2 ψ k₀ c auxOf tbl).erase := by
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  have hnAll : c.dJ.nAll = c.dJ.ctorsA.length := by
    unfold IndRepData.nAll; rw [hg.ctorsC]; rfl
  show Term.bvarsBelow d.nP (c.dJ.foldTermAV mp.base2 c.ψ' c.DsA (d.psiL mp.base2 ψ k₀ c.base)
    (d.psiPinsT c.dJ.nP) (c.dJ.psiBodyAV (d.psiHead mp.base2 ψ c.dJ.nP auxOf) (psiUseIh c.dJ)
      (d.psiVia c.dJ ψ k₀ c.dJ.nP auxOf (c.dJ.bb c.ψ') tbl)) c.mm).erase
  refine c.dJ.foldTermAV_below mp.base2 hg.len hDsA
    (fun t ht => c.dJ.ipss_below_of_indRep hrepJ hg.kReal c.ψ' ht) ?_
    (fun t _ => mp.base2.cval_closedL _ _) (fun t _ => d.psiPinsT_below c.dJ.nP t) ?_ ?_ ?_
  · intro t ht
    have hFF := c.dJ.formerFacts_of_indRep hrepJ hg.kReal c.ψ' ht
    have hget : (c.dJ.ipss c.ψ').getD t [] = (c.dJ.ppsM t c.ψ').drop c.dJ.nP := by
      simp [IndRepData.ipss, List.getD_eq_getElem?_getD, List.getElem?_range ht]
    rw [hget, List.length_drop, hFF.1, Nat.add_sub_cancel_left]
    rfl
  · intro t _ p hp
    unfold IndRepData.pinsOf at hp
    rw [hg.pinsAV] at hp
    exact Term.bvarsBelow.mono (by omega) (paramBvarsAt_below (Nat.le_refl _) p hp)
  · intro J hJ
    have hJA : J < c.dJ.ctorsA.length := by rw [← hnAll]; exact hJ
    exact c.dJ.minorData_below_of mp.base2 hg.ctorsC hg.view (List.getElem?_eq_getElem hJA)
      (hrepJ.ctors J _ (List.getElem?_eq_getElem hJA)) d.nP
  · intro J hJ
    have hJA : J < c.dJ.ctorsA.length := by rw [← hnAll]; exact hJ
    have hj : c.dJ.ctorsA[J]? = some c.dJ.ctorsA[J] := List.getElem?_eq_getElem hJA
    rw [c.dJ.minorData_length_of mp.base2 hg.ctorsC hj (hrepJ.ctors J _ hj)]
    refine c.dJ.psiBodyAV_below (d.psiHead_below mp.base2 ψ c.dJ.nP auxOf J) ?_
    intro i hi Ψ Eis tl hv
    rw [c.dJ.ctorsAll_getD_of hg.ctorsC hj] at hi
    unfold IndRepData.psiVia at hv
    split at hv
    · rename_i hcond
      obtain ⟨hrec, hnotJ, hk₀⟩ := hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      obtain ⟨cAa, hJa, hf⟩ := hg.ctors J _ hj
      have hD := hf.ctor.2.2
      obtain ⟨-, -, heissA, htssA⟩ := hviewA (auxOf J)
      have hlen : (rebit (c.dJ.bb c.ψ') (liftDoms c.dJ.nP i ((d.tssR (auxOf J) ψ).getD i []))).length
          = ((d.tssR (auxOf J) ψ).getD i []).length := by
        rw [rebit_length, liftDoms_length]
      refine ⟨?_, ?_, ?_⟩
      · rw [AnnotTerm.erase_liftN]
        have := VExprAux.bvarsBelow_liftN c.dJ.nP _ _ 0 (htbl J _ hj i hi hrec hnotJ hk₀)
        rwa [Nat.add_comm] at this
      · refine (rebit_below _ _).mpr ?_
        have := liftDoms_below (n := c.dJ.nP) (k := i) (htssA ▸ hD.tssBelow ψ i)
        rwa [show d.nP + i + c.dJ.nP = c.dJ.nP + i + d.nP by omega] at this
      · intro E' hE'
        obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hE'
        rw [AnnotTerm.erase_liftN, hlen]
        rw [heissA] at hE
        rw [htssA]
        have := VExprAux.bvarsBelow_liftN c.dJ.nP _ _ (i + ((d.tssF (auxOf J) ψ).getD i []).length)
          (hD.eissBelow ψ i E hE)
        rwa [show d.nP + i + ((d.tssF (auxOf J) ψ).getD i []).length + c.dJ.nP
          = c.dJ.nP + i + ((d.tssF (auxOf J) ψ).getD i []).length + d.nP by omega] at this
    · exact nomatch hv

/-- **Along the kernel order every table entry of ψ is bounded** at the
scratch block's parameters (`TopoOrder.orderFold_all` with the bound
as the invariant, `psiFold_typed`'s shape). -/
theorem psiFold_below {μ : CheckMode} {mp : EnvModelM V μ env} {ψ : Name → Nat} {k₀ n : Nat}
    {lpsT : List Name} {cd : Nat → CopyData V} {auxOfs : Nat → Nat → Nat} (hkn : d.k ≤ k₀ + n)
    (hall : ∀ j', j' < n → GroupFacts mp d ψ k₀ lpsT cd (cd j') (auxOfs j'))
    (hviewA : ∀ J, d.ksR J = d.ksF J ∧ d.tgtsR J = d.tgts J ∧ d.eissR J = d.eissF J ∧
      d.tssR J = d.tssF J)
    (htgtsA : ∀ J i, d.tgtsR J i < d.k)
    (hDsA : ∀ j, ∀ q ∈ (cd j).DsA, Term.bvarsBelow d.nP q.erase)
    {R : Nat → Nat → Prop}
    (href : ∀ j', j' < n → ∀ Jc cAJ, (cd j').dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfs j' Jc)) → i ∉ ConLeche.recIdxOf ((cd j').dJ.ksF Jc) →
      k₀ ≤ d.tgtsR (auxOfs j' Jc) i → R j' (d.tgtsR (auxOfs j' Jc) i - k₀))
    {order : List Nat} (hord : TopoOrder R n order) (tbl₀ : Nat → AnnotTerm) :
    ∀ j', j' < n →
      Term.bvarsBelow d.nP (ConLeche.orderFold (d.psiStep mp.base2 ψ k₀ cd auxOfs) order tbl₀ j').erase := by
  intro j' hj'
  refine hord.orderFold_all (d.psiStep mp.base2 ψ k₀ cd auxOfs)
    (fun j Ψ => j < n → Term.bvarsBelow d.nP Ψ.erase) ?_ tbl₀ j' hj' hj'
  intro tbl j ih hj
  unfold IndRepData.psiStep
  refine d.psiTerm_below (hall j hj) hviewA (hDsA j) tbl ?_
  intro Jc cAJ hJc i hi hrec hnotJ hk₀
  have hR := href j hj Jc cAJ hJc i hi hrec hnotJ hk₀
  exact ih _ hR (by have := htgtsA (auxOfs j Jc) i; omega)

end IndRepData

end ConLeche.Model
