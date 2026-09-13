module

public import ConLeche.Model.Inductives.RoundTripR2
public section

/-!
# The round trips at the RUN level (task #279 M-C′ step 4, DESIGN §M.35)

`RoundTripR2.lean` proves R2's and R1's steps at the datum level under
named hypotheses in the shapes the existing facts deliver.  This
module instantiates those hypotheses off `DeclNestedRun`, piece by
piece:

* **the table's entries at a group** — the fold's term at pin `base + t`
  is `psiStep` at the table current when that pin was folded; with the
  step reading only the entries the reference relation names
  (`psiTerm_congr_tbl`) it is the step at the FINAL table
  (`TopoOrder.orderFold_eq_step`), and with the run's group clause
  (`PinRunFacts`: the group-mates' data are the pin's own) it is the
  step at the pin's VIEW of the group at member `t` (`psiFinal_group`);
* **ψ's setup at the final table** — `psiSetup_final`, the group's
  `PsiSetup` with the transports at the FINAL table's terms (the shape
  `psiStep_typed` builds, at a table every referenced entry of which is
  typed);
* **the ι laws at values, at the run** — ψ's (`psi_iota_run`) and ψ⁻¹'s
  (`inv_iota_run`) in the shapes `r2_step`/`r1_step` take them, with
  the fold terms the run's own: `Ψ t` the final table's entry at pin
  `base + t`, `Φ' t` ψ⁻¹'s fold term at aux member `t`.
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

/-! ## The step reads the table only at the transports' targets -/

omit [SetTheory V] in
/-- `psiVarsAV` reads the transports below `nF` only. -/
theorem psiVarsAV_congr {recIdx : List Nat} {useIh : Nat → Bool} {via via' : Nat → Option ViaSpec}
    {nF o : Nat} (h : ∀ i, i < nF → via i = via' i) :
    psiVarsAV recIdx useIh via nF o = psiVarsAV recIdx useIh via' nF o := by
  unfold psiVarsAV
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

namespace IndRepData

variable (d : IndRepData V)

omit [SetTheory V] in
/-- ψ's body at constructor `J` reads the transports at `J`'s fields only. -/
theorem psiBodyAV_congr {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool}
    {via via' : Nat → Nat → Option ViaSpec} {J : Nat}
    (h : ∀ i, i < (d.ctorsAll.getD J default).2 → via J i = via' J i) :
    d.psiBodyAV head useIh via J = d.psiBodyAV head useIh via' J := by
  unfold IndRepData.psiBodyAV
  rw [psiVarsAV_congr h]

omit [SetTheory V] in
/-- The minors read the bodies below the count only. -/
theorem minChoiceAVs_congr {ψ : Name → Nat} {ps Ms : List AnnotTerm} {bodies bodies' : Nat → AnnotTerm} :
    ∀ n, (∀ J, J < n → bodies J = bodies' J) →
      d.minChoiceAVs ψ ps Ms bodies n = d.minChoiceAVs ψ ps Ms bodies' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [IndRepData.minChoiceAVs]
    rw [minChoiceAVs_congr n (fun J hJ => h J (Nat.lt_succ_of_lt hJ)), h n (Nat.lt_succ_self n)]

/-- **The step reads the table only at the transports' targets** of
the copy's real constructors: two tables agreeing there give the same
term (`psiVia` is the only reader of the table). -/
theorem psiTerm_congr_tbl (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (c : CopyData V)
    (auxOf : Nat → Nat) {tbl tbl' : Nat → AnnotTerm} (hctorsC : c.dJ.ctorsC = [])
    (h : ∀ Jc cAJ, c.dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) → i ∉ ConLeche.recIdxOf (c.dJ.ksF Jc) →
      k₀ ≤ d.tgtsR (auxOf Jc) i →
      tbl (d.tgtsR (auxOf Jc) i - k₀) = tbl' (d.tgtsR (auxOf Jc) i - k₀)) :
    d.psiTerm m ψ k₀ c auxOf tbl = d.psiTerm m ψ k₀ c auxOf tbl' := by
  unfold IndRepData.psiTerm
  congr 2
  apply c.dJ.minChoiceAVs_congr
  intro J hJ
  have hJA : J < c.dJ.ctorsA.length := by
    unfold IndRepData.nAll at hJ; rw [hctorsC] at hJ; simpa using hJ
  have hj : c.dJ.ctorsA[J]? = some c.dJ.ctorsA[J] := List.getElem?_eq_getElem hJA
  apply c.dJ.psiBodyAV_congr
  intro i hi
  rw [c.dJ.ctorsAll_getD_of hctorsC hj] at hi
  unfold IndRepData.psiVia
  by_cases hc : i ∈ ConLeche.recIdxOf (d.ksR (auxOf J)) ∧ i ∉ ConLeche.recIdxOf (c.dJ.ksF J) ∧
      k₀ ≤ d.tgtsR (auxOf J) i
  · rw [if_pos hc, if_pos hc, h J _ hj i hi hc.1 hc.2.1 hc.2.2]
  · rw [if_neg hc, if_neg hc]

end IndRepData

/-! ## The final table at a group -/

/-- The group's constructor indices are the pin's: `auxOfsOf` at a
group-mate is `auxOfsOf` at the pin (the run's group clause). -/
theorem auxOfsOf_group {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts}
    {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hcd : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    {j : Nat} (hj : j < st.pins.length) {t : Nat} (ht : t < (cd j).dJ.k) :
    auxOfsOf st p.k cd ((cd j).base + t) = auxOfsOf st p.k cd j := by
  funext Jc
  unfold auxOfsOf
  rw [(hcd j hj).2 t ht]

/-- **The final table's entry at a pin is the step at the final table**
(`orderFold_eq_step` with the step's dependence on the table
restricted to the transports' targets, which the bridge relates). -/
theorem psiFinal_eq {μ : CheckMode} {mpAux : EnvModelM V μ env} {d : IndRepData V} {ψ : Name → Nat}
    {st : ElimState} {k₀ n : Nat} {cd : Nat → CopyData V} {auxOfs : Nat → Nat → Nat}
    (hctorsC : ∀ j, j < n → (cd j).dJ.ctorsC = [])
    (hbridge : BridgeOfRun d st k₀ n cd auxOfs) {order : List Nat}
    (hord : TopoOrder (ConLeche.CopyRef (ElimState.grp st) k₀ st) n order) (tbl₀ : Nat → AnnotTerm)
    {j : Nat} (hj : j < n) :
    ConLeche.orderFold (d.psiStep mpAux.base2 ψ k₀ cd auxOfs) order tbl₀ j
      = d.psiTerm mpAux.base2 ψ k₀ (cd j) (auxOfs j)
          (ConLeche.orderFold (d.psiStep mpAux.base2 ψ k₀ cd auxOfs) order tbl₀) := by
  refine hord.orderFold_eq_step (d.psiStep mpAux.base2 ψ k₀ cd auxOfs) tbl₀ hj ?_
  intro tbl tbl' hagree
  unfold IndRepData.psiStep
  refine d.psiTerm_congr_tbl mpAux.base2 ψ k₀ (cd j) (auxOfs j) (hctorsC j hj) ?_
  intro Jc cAJ hJc i hi hA hT hk
  exact hagree _ (hbridge j hj Jc cAJ hJc i hi hA hT hk)

/-- **The final table's entry at a group-mate is the step at the pin's
VIEW of the group**: the term for member `t` of pin `j`'s container at
pin `j`'s data (the run's group clause), at the final table. -/
theorem psiFinal_group {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts}
    {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hcd : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    (hbridge : BridgeOfRun d st p.k st.pins.length cd (auxOfsOf st p.k cd)) {order : List Nat}
    (hord : TopoOrder (ConLeche.CopyRef (ElimState.grp st) p.k st) st.pins.length order)
    (tbl₀ : Nat → AnnotTerm) {j : Nat} (hj : j < st.pins.length) {t : Nat} (ht : t < (cd j).dJ.k) :
    ConLeche.orderFold (d.psiStep mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd)) order tbl₀ ((cd j).base + t)
      = d.psiTerm mpAux.base2 ψ p.k ⟨(cd j).dJ, t, (cd j).ψ', (cd j).DsA, (cd j).base⟩
          (auxOfsOf st p.k cd j)
          (ConLeche.orderFold (d.psiStep mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd)) order tbl₀) := by
  have hjt : (cd j).base + t < st.pins.length := by
    have := (hcd j hj).1.1.kA t ht
    obtain ⟨⟨-, hbm, -⟩, -⟩ := hcd j hj
    -- the group-mate's pin exists: it carries the group's facts
    obtain ⟨⟨-, -, q, I, ci, J, lvls, Ds, cvTJ, capsJ, -, -, -, -, -, hlenM, hgrp, -⟩, -⟩ := hcd j hj
    obtain ⟨J', hJ'⟩ : ∃ J', ci.members[t]? = some J' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact ht)⟩
    obtain ⟨q', hq', -⟩ := hgrp t J' hJ'
    exact (List.getElem?_eq_some_iff.mp hq').1
  rw [psiFinal_eq (fun j hj => (hcd j hj).1.1.ctorsC) hbridge hord tbl₀ hjt, (hcd j hj).2 t ht,
    auxOfsOf_group hcd hj ht]

/-! ## Parameter frames -/

/-- The parameter variables seen from under `as` read the frame's
parameter values. -/
theorem interp_paramBvarsAt_consList {nP : Nat} (as : List V) (σ : Nat → V) :
    (paramBvarsAt nP (nP + as.length)).map (interp V (consList as σ)) = paramVals nP σ := by
  unfold paramVals paramBvarsAt
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  simp only [Function.comp, interp_bvar]
  rw [show nP + as.length - 1 - k = (nP - 1 - k) + as.length by omega, consList_apply_add]

/-- The parameter values of a frame pushed on itself are its own. -/
theorem paramVals_push {nP : Nat} {pv : List V} (hlen : pv.length = nP) (ρ : Nat → V) :
    paramVals nP (consList pv ρ) = pv := by
  unfold paramVals
  exact interp_paramBvarsAt_self hlen ρ

theorem wellDenotedV_bvar (ρ : Nat → V) (i : Nat) : WellDenotedV V ρ (.bvar i) :=
  ⟨by rw [WellDenoted_bvar]; trivial, by rw [AnnotValid_bvar]; trivial⟩

theorem wellDenotedV_paramBvarsAt (ρ : Nat → V) (nP D : Nat) :
    ∀ q ∈ paramBvarsAt nP D, WellDenotedV V ρ q := by
  intro q hq
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hq
  exact wellDenotedV_bvar ρ _

omit [SetTheory V] in
theorem paramBvarsAt_length (nP D : Nat) : (paramBvarsAt nP D).length = nP := by
  simp [paramBvarsAt]

namespace IndRepData

variable (d : IndRepData V)

/-- **A parameter frame's values fit the parameters at ANY frame**: the
parameter domains are bounded at their own depth. -/
theorem paramVals_fit {ψ : Name → Nat} {ρ ρ' : Nat → V} (hbelow : DomsBelow 0 (d.ppsM 0 ψ))
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) :
    SpineFit ρ' (d.params ψ) (paramVals d.nP ρ) := by
  unfold IndRepData.params at hρ ⊢
  exact spineFit_congr_below (domsBelow_take hbelow) (fun i hi => absurd hi (Nat.not_lt_zero _)) hρ

end IndRepData

/-! ## The run's facts, bundled -/

/-- **The run's facts the round trips consume**, at one level
assignment `ψ` and the run's pin data `cd`: the scratch block's
representations, the pins' facts with the group clause, the
constructor side (`CopyCtorsOfRun`, from the record), the bridge and
the kernel's order — everything `psiFold_typed_of_read`,
`invSetup_of_run` and the ι laws are assembled from. -/
structure NestedRunFacts {μ : CheckMode} (F : Nat) (env : Env) {envAux : Env}
    (p : ConLeche.NestedParts) (st : ElimState) (b : MutualBlock) (params : List Expr)
    (pbs : List (Expr × ConLeche.BinderMeta)) (mpAux : EnvModelM V μ envAux) (d : IndRepData V)
    (ψ : Name → Nat) (cd : Nat → CopyData V) (lpsT : List Name) (order : List Nat) : Prop where
  reps : MutualBlockReps mpAux.base2 b d
  aux : ConLeche.auxBlock p st = some b
  lenSt : st.types.length = p.k + st.pins.length
  pins : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j
  ctors : CopyCtorsOfRun mpAux d ψ p.k st.pins.length lpsT cd (auxOfsOf st p.k cd)
  bridge : BridgeOfRun d st p.k st.pins.length cd (auxOfsOf st p.k cd)
  ord : TopoOrder (ConLeche.CopyRef (ElimState.grp st) p.k st) st.pins.length order

/-- **ψ's FINAL table**: the fold of the copies' terms along the
kernel's order from the initial table `tbl₀`. -/
@[expose] def IndRepData.psiFinal (d : IndRepData V) (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat)
    (cd : Nat → CopyData V) (auxOfs : Nat → Nat → Nat) (order : List Nat) (tbl₀ : Nat → AnnotTerm) :
    Nat → AnnotTerm :=
  ConLeche.orderFold (d.psiStep m ψ k₀ cd auxOfs) order tbl₀

/-- Pin `j`'s view of member `t` of its group. -/
@[expose] def CopyData.at (c : CopyData V) (t : Nat) : CopyData V := ⟨c.dJ, t, c.ψ', c.DsA, c.base⟩

namespace NestedRunFacts

variable {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState}
  {b : MutualBlock} {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)}
  {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
  {lpsT : List Name} {order : List Nat}
  (R : NestedRunFacts F env p st b params pbs mpAux d ψ cd lpsT order)

include R

theorem ctorsC : d.ctorsC = [] := R.reps.1

theorem dk : d.k = p.k + st.pins.length := by
  obtain ⟨-, hkb, -⟩ := R.reps
  rw [hkb, ConLeche.auxBlock_k R.aux, R.lenSt]

theorem dnP : d.nP = p.nP := by
  obtain ⟨-, -, -, hnP, -⟩ := R.reps
  rw [hnP, (ConLeche.auxBlock_inv R.aux).1]

theorem viewA : ∀ J, d.ksR J = d.ksF J ∧ d.tgtsR J = d.tgts J ∧ d.eissR J = d.eissF J ∧
    d.tssR J = d.tssF J := by
  obtain ⟨-, -, -, -, -, hview, -⟩ := R.reps
  exact hview

/-- Every field's target in the recursor's view is a member. -/
theorem tgtsA (hk : 0 < d.k) : ∀ J i, d.tgtsR J i < d.k := by
  obtain ⟨-, hkb, -, -, -, -, -, hall⟩ := R.reps
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, -, hrep₀⟩ := hall 0 (by rw [← hkb]; exact hk)
  intro J i
  exact hrep₀.tgtsRLt J i

theorem groupFacts {j : Nat} (hj : j < st.pins.length) :
    GroupFacts mpAux d ψ p.k lpsT cd (cd j) (auxOfsOf st p.k cd j) :=
  GroupFacts.of_pinFacts (R.pins j hj).1.1 (R.ctors j hj)

/-- A group-mate's pin is listed. -/
theorem mate_lt {j : Nat} (hj : j < st.pins.length) {t : Nat} (ht : t < (cd j).dJ.k) :
    (cd j).base + t < st.pins.length := by
  obtain ⟨⟨-, -, q, I, ci, J, lvls, Ds, cvTJ, capsJ, -, -, -, -, -, hlenM, hgrp, -⟩, -⟩ := R.pins j hj
  obtain ⟨J', hJ'⟩ : ∃ J', ci.members[t]? = some J' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact ht)⟩
  obtain ⟨q', hq', -⟩ := hgrp t J' hJ'
  exact (List.getElem?_eq_some_iff.mp hq').1

/-- The group's facts at pin `j`'s view of member `t` (the run's group
clause: the group-mate's data are the pin's own). -/
theorem groupFacts_at {j : Nat} (hj : j < st.pins.length) {t : Nat} (ht : t < (cd j).dJ.k) :
    GroupFacts mpAux d ψ p.k lpsT cd ((cd j).at t) (auxOfsOf st p.k cd j) := by
  have h := R.groupFacts (R.mate_lt hj ht)
  rw [(R.pins j hj).2 t ht, auxOfsOf_group R.pins hj ht] at h
  exact h

/-- The pins' readings are bounded at the block's parameters
(`DenoteMetaSpine.bvarsBelow` at K.3's guards). -/
theorem DsA_below {j : Nat} (hj : j < st.pins.length) :
    ∀ q ∈ (cd j).DsA, Term.bvarsBelow d.nP q.erase := by
  obtain ⟨⟨-, -, q, I, ci, J, lvls, Ds, cvTJ, capsJ, -, -, -, -, -, -, -, -, -, -, -, hargs, hsp, -⟩,
    -⟩ := R.pins j hj
  rw [R.dnP]
  exact DenoteMetaSpine.bvarsBelow hsp hargs

/-- Every entry of the final table is bounded at the block's
parameters (`psiFold_below`). -/
theorem final_below (tbl₀ : Nat → AnnotTerm) {j : Nat} (hj : j < st.pins.length) :
    Term.bvarsBelow d.nP (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j).erase :=
  d.psiFold_below (by rw [R.dk]; exact Nat.le_refl _) (fun j hj => R.groupFacts hj) R.viewA
    (R.tgtsA (by rw [R.dk]; omega)) (fun j hj => R.DsA_below hj) R.bridge R.ord tbl₀ j hj

/-- Every entry of the final table is typed (`psiFold_typed`). -/
theorem final_typed {ρ₀ : Nat → V} {psA : List AnnotTerm} (hpsA : psA.length = d.nP)
    (hparamsA : SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀))) (tbl₀ : Nat → AnnotTerm)
    {j : Nat} (hj : j < st.pins.length) :
    d.PsiP mpAux.base2 ψ p.k (consList (psA.map (interp V ρ₀)) ρ₀) cd j
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ j) := by
  obtain ⟨hpinsA, hFFA, hLSA, hpIffMA⟩ := auxFacts_of_blockReps R.reps ψ
  exact d.psiFold_typed mpAux hpsA hparamsA hpinsA hFFA hLSA hpIffMA (by rw [R.dk]; exact Nat.le_refl _)
    (fun j hj => ⟨R.groupFacts hj, (R.pins j hj).1.2.1⟩) R.bridge R.ord tbl₀ j hj

/-- **ψ's setup at the FINAL table** (the shape `psiStep_typed` builds,
with the transports at the final table's terms, every referenced entry
of which is typed). -/
theorem psiSetup_final {ρ₀ : Nat → V} {psA : List AnnotTerm} (hpsA : psA.length = d.nP)
    (hparamsA : SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀))) (tbl₀ : Nat → AnnotTerm)
    {j : Nat} (hj : j < st.pins.length) :
    ∃ lps : List Name,
      (cd j).dJ.PsiSetup mpAux lps lps (cd j).ψ' (consList (psA.map (interp V ρ₀)) ρ₀) (cd j).DsA
        (d.psiL mpAux.base2 ψ p.k (cd j).base) (d.psiPinsT (cd j).dJ.nP)
        (d.psiHead mpAux.base2 ψ (cd j).dJ.nP (auxOfsOf st p.k cd j)) (IndRepData.psiUseIh (cd j).dJ)
        (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀))
        (d.psiTgV mpAux.base2 ψ p.k (auxOfsOf st p.k cd j) cd)
        (d.psiDomA ψ (cd j).dJ.nP (auxOfsOf st p.k cd j)) := by
  obtain ⟨hpinsA, hFFA, hLSA, hpIffMA⟩ := auxFacts_of_blockReps R.reps ψ
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, hrules, hfR, hrepJ⟩ := hg.rep
  have htgt : ∀ Jc cAJ, (cd j).dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j Jc)) → i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF Jc) →
      p.k ≤ d.tgtsR (auxOfsOf st p.k cd j Jc) i → d.tgtsR (auxOfsOf st p.k cd j Jc) i - p.k < st.pins.length := by
    intro Jc cAJ hJc i hi hA hT hk
    obtain ⟨cAa, -, hf⟩ := hg.ctors Jc cAJ hJc
    have := hf.tgts i
    rw [R.dk] at this
    omega
  refine ⟨cvT.levelParams, d.psiSetup_of_group mpAux hpsA hparamsA hpinsA hFFA hLSA hpIffMA hg.ctorsC
    hg.kReal hg.pinsAV hg.view ht₀ hrules hfR hrepJ hg.len hg.lev hg.kA hg.grp (auxOfsOf st p.k cd j) cd _
    hg.ctors ?_ ?_ ?_⟩
  · intro Jc cAJ hJc i hi hA hT hk
    exact (R.groupFacts (htgt Jc cAJ hJc i hi hA hT hk)).ok (R.pins _ (htgt Jc cAJ hJc i hi hA hT hk)).1.2.1
  · intro Jc cAJ hJc i hi hA hT hk
    exact R.final_typed hpsA hparamsA tbl₀ (htgt Jc cAJ hJc i hi hA hT hk)
  · intro Jc cAJ hJc i hi hA hT hk
    exact ⟨(R.groupFacts (htgt Jc cAJ hJc i hi hA hT hk)).targetOk hpsA hparamsA hFFA hpIffMA,
      (R.groupFacts (htgt Jc cAJ hJc i hi hA hT hk)).lev⟩

/-- **The final table at a group-mate is the pin's view** (the run's
group clause): member `t`'s term is ψ's fold term at pin `j`'s data. -/
theorem final_group (tbl₀ : Nat → AnnotTerm) {j : Nat} (hj : j < st.pins.length) {t : Nat}
    (ht : t < (cd j).dJ.k) :
    d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t)
      = (cd j).dJ.foldTermAV mpAux.base2 (cd j).ψ' (cd j).DsA (d.psiL mpAux.base2 ψ p.k (cd j).base)
          (d.psiPinsT (cd j).dJ.nP)
          ((cd j).dJ.psiBodyAV (d.psiHead mpAux.base2 ψ (cd j).dJ.nP (auxOfsOf st p.k cd j))
            (IndRepData.psiUseIh (cd j).dJ)
            (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
              (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀))) t := by
  unfold IndRepData.psiFinal
  rw [psiFinal_group R.pins R.bridge R.ord tbl₀ hj ht]
  rfl

end NestedRunFacts

end ConLeche.Model
