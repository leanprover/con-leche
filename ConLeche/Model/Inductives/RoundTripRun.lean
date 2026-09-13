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
    (ψ : Name → Nat) (cd : Nat → CopyData V) (lpsT : List Name) (order : List Nat) (s : Level) :
    Prop where
  reps : MutualBlockReps mpAux.base2 b d
  aux : ConLeche.auxBlock p st = some b
  /-- the datum's constructors are the constructor stage's (R1 at the
  run: every scratch constructor is a real member's or a copy's,
  `copyCtor_repr`) -/
  chk : CtorsChecked μ F env b true d
  lenSt : st.types.length = p.k + st.pins.length
  pins : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j
  ctors : CopyCtorsOfRun mpAux d ψ p.k st.pins.length lpsT cd (auxOfsOf st p.k cd)
  bridge : BridgeOfRun d st p.k st.pins.length cd (auxOfsOf st p.k cd)
  ord : TopoOrder (ConLeche.CopyRef (ElimState.grp st) p.k st) st.pins.length order
  /-- the block's sort `s` (the member with rules') evaluates as the
  datum's -/
  sortEval : ∀ φ : Name → Nat, s.eval φ = d.resSort.eval φ
  /-- the block's elimination level evaluates as its sort (the `Prop`
  arm reads the elimination bit off it) -/
  lev : d.elimL.eval ψ = d.w ψ
  /-- ψ⁻¹'s setup at every parameter frame (`invSetup_of_pinFacts`), at
  the datum re-sorted to `s` -/
  inv : ∃ lpsI lpsT' : List Name, ∀ (ρ : Nat → V) (ps : List AnnotTerm), ps.length = d.nP →
    (∀ q ∈ ps, WellDenotedV V ρ q) → SpineFit ρ (d.params ψ) (ps.map (interp V ρ)) →
    ({d with resSort := s} : IndRepData V).InvSetup mpAux lpsI lpsT' ψ ρ ps
      (d.invL mpAux.base2 ψ p.k cd) (d.invPinsT p.k cd)
      (d.invHead mpAux.base2 ψ st.pins.length cd (auxOfsOf st p.k cd)) (d.invUseIh p.k)

/-- **ψ⁻¹'s fold term** at aux member `t`: the member's recursor at the
choice `invL`/`invPinsT`/`invHead`/`invUseIh`, the parameters the
parameter variables, at the datum re-sorted to `s`. -/
@[expose] noncomputable def IndRepData.invFold (d : IndRepData V) (m : EnvModel V env) (ψ : Name → Nat) (k₀ n : Nat)
    (cd : Nat → CopyData V) (auxOfs : Nat → Nat → Nat) (s : Level) (t : Nat) : AnnotTerm :=
  (d.withSort s).foldTermAV m ψ (paramBvarsAt d.nP d.nP) (d.invL m ψ k₀ cd) (d.invPinsT k₀ cd)
    ((d.withSort s).invBodyAV (d.invHead m ψ n cd auxOfs) (d.invUseIh k₀)) t

/-- **The run's facts from the pins' facts**: the constructor side from
the record (`copyCtorsOfRun_of_read`), the bridge from its syntactic
half (`bridgeOfRun_of_syntax`), the order from the kernel's
(`topoOrder_of_run`), ψ⁻¹'s setup (`invSetup_of_pinFacts`). -/
theorem nestedRunFacts_of_pinFacts {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V} {order : List Nat}
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d)
    (hb : ConLeche.auxBlock p st = some b) (hlenSt : st.types.length = p.k + st.pins.length)
    (hord : ConLeche.nestedTopoOrder (ElimState.grp st) p.k st = .ok order)
    (hcd : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    (hread : CopyCtorsRead mpAux d ψ st p.k st.pins.length cd)
    (hsyn : BridgeSyntax d st p.k st.pins.length cd (auxOfsOf st p.k cd))
    (hlev : d.elimL.eval ψ = d.w ψ) {t₀ : Nat} (ht₀ : t₀ < b.k) (hct₀ : d.memberCtors t₀ ≠ []) :
    ∃ (lpsT : List Name) (s : Level), NestedRunFacts F env p st b params pbs mpAux d ψ cd lpsT order s := by
  obtain ⟨lpsT, hctors⟩ := copyCtorsOfRun_of_read hreps hchk hcd hread
  have hkn : d.k ≤ p.k + st.pins.length := by
    obtain ⟨-, hkb, -⟩ := hreps
    rw [hkb, ConLeche.auxBlock_k hb, hlenSt]
    exact Nat.le_refl _
  have hgrp : ∀ j, j < st.pins.length → ElimState.grp st j = ((cd j).base, (cd j).dJ.k) := by
    intro j hj
    obtain ⟨⟨-, -, q, I, ci, J, lvls, Ds, cvTJ, capsJ, -, -, -, -, -, -, -, -, hg, -⟩, -⟩ := hcd j hj
    exact hg
  obtain ⟨s, lps, lpsT', hsv, hinv⟩ := invSetup_of_pinFacts hreps hchk hb hlenSt hcd hread hlev ht₀ hct₀
  exact ⟨lpsT, s, hreps, hb, hchk, hlenSt, hcd, hctors, bridgeOfRun_of_syntax rfl hlenSt hkn hgrp hctors hsyn,
    ConLeche.topoOrder_of_run hlenSt hord, hsv, hlev, lps, lpsT', hinv⟩

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
  {lpsT : List Name} {order : List Nat} {s : Level}
  (R : NestedRunFacts F env p st b params pbs mpAux d ψ cd lpsT order s)

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

/-- The parameter domains are bounded at their own depth (member `0`'s
former). -/
theorem ppsM_below (hk : 0 < d.k) : DomsBelow 0 (d.ppsM 0 ψ) := by
  obtain ⟨-, hkb, -, -, -, -, -, hall⟩ := R.reps
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, -, hrep₀⟩ := hall 0 (by rw [← hkb]; exact hk)
  exact hrep₀.former.below ψ

/-- A transport's target is a listed pin. -/
theorem transport_lt {j : Nat} (hj : j < st.pins.length) {Jc : Nat} {cAJ : ConstantVal × Nat}
    (hJc : (cd j).dJ.ctorsA[Jc]? = some cAJ) (i : Nat) :
    d.tgtsR (auxOfsOf st p.k cd j Jc) i - p.k < st.pins.length := by
  obtain ⟨cAa, -, hf⟩ := (R.groupFacts hj).ctors Jc cAJ hJc
  have := hf.tgts i
  rw [R.dk] at this
  omega

/-- **The transports at the final table are bounded** at the two
parameter counts (the shape `PsiSetup.fold_iota_vals` asks). -/
theorem psiVia_below (tbl₀ : Nat → AnnotTerm) {j : Nat} (hj : j < st.pins.length) {Jc : Nat}
    {cAJ : ConstantVal × Nat} (hJc : (cd j).dJ.ctorsA[Jc]? = some cAJ) :
    ∀ i, i < cAJ.2 → ∀ Ψ Eis tl,
      d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) Jc i = some (Ψ, Eis, tl) →
      Term.bvarsBelow ((cd j).dJ.nP + d.nP) Ψ.erase ∧ DomsBelow ((cd j).dJ.nP + i + d.nP) tl ∧
      ∀ E ∈ Eis, Term.bvarsBelow ((cd j).dJ.nP + i + tl.length + d.nP) E.erase := by
  intro i hi Ψ Eis tl hv
  unfold IndRepData.psiVia at hv
  split at hv
  · rename_i hcond
    obtain ⟨hrec, hnotJ, hk₀⟩ := hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    obtain ⟨cAa, hJa, hf⟩ := (R.groupFacts hj).ctors Jc cAJ hJc
    have hD := hf.ctor.2.2
    obtain ⟨-, -, heissA, htssA⟩ := R.viewA (auxOfsOf st p.k cd j Jc)
    have hlen : (rebit ((cd j).dJ.bb (cd j).ψ')
        (liftDoms (cd j).dJ.nP i ((d.tssR (auxOfsOf st p.k cd j Jc) ψ).getD i []))).length
        = ((d.tssR (auxOfsOf st p.k cd j Jc) ψ).getD i []).length := by
      rw [rebit_length, liftDoms_length]
    refine ⟨?_, ?_, ?_⟩
    · rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (cd j).dJ.nP _ _ 0 (R.final_below tbl₀ (R.transport_lt hj hJc i))
      rwa [Nat.add_comm] at this
    · refine (rebit_below _ _).mpr ?_
      have := liftDoms_below (n := (cd j).dJ.nP) (k := i) (htssA ▸ hD.tssBelow ψ i)
      rwa [show d.nP + i + (cd j).dJ.nP = (cd j).dJ.nP + i + d.nP by omega] at this
    · intro E' hE'
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hE'
      rw [AnnotTerm.erase_liftN, hlen]
      rw [heissA] at hE
      rw [htssA]
      have := VExprAux.bvarsBelow_liftN (cd j).dJ.nP _ _
        (i + ((d.tssF (auxOfsOf st p.k cd j Jc) ψ).getD i []).length) (hD.eissBelow ψ i E hE)
      rwa [show d.nP + i + ((d.tssF (auxOfsOf st p.k cd j Jc) ψ).getD i []).length + (cd j).dJ.nP
        = (cd j).dJ.nP + i + ((d.tssF (auxOfsOf st p.k cd j Jc) ψ).getD i []).length + d.nP by omega]
        at this
  · exact nomatch hv

set_option maxHeartbeats 1600000 in
/-- **ψ's ι at values, at the run** (the shape `r2_step`/`r1_step` take
it): at pin `j`, container constructor `J` and field values `fs`
fitting its telescope under the pin's readings (at the block's
parameter frame `σ₀`, the parameters pushed), the final table's entry
at the group-mate of the constructor's member, at the constructor's
index readings and value, is the head at ψ's values — with the entries
at the fields' targets inside.  `PsiSetup.fold_iota_vals` at the
group's setup at the final table (`psiSetup_final`), the fold terms
the final table's entries (`final_group`). -/
theorem psi_iota (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {σ₀ : Nat → V}
    (hσ₀ : σ₀ = consList (paramVals d.nP ρ) ρ) {j : Nat} (hj : j < st.pins.length)
    (hb : (cd j).dJ.bb (cd j).ψ' ≠ 0) {Ψ : Nat → AnnotTerm}
    (hΨ : ∀ t, Ψ t = d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    {fs : List V} (hvs : fs.length = cA.2)
    (hfit : SpineFit σ₀ (((cd j).dJ.dsF J (cd j).ψ').map (·.2.2)) ((cd j).DsA.map (interp V σ₀) ++ fs)) :
    (((cd j).dJ.esF J (cd j).ψ').map (interp V (consList fs (consList ((cd j).DsA.map (interp V σ₀)) σ₀))) ++
        [((cd j).DsA.map (interp V σ₀) ++ fs).foldl SetTheory.app
          (interp V σ₀ (mpAux.base2.acval cA.1.name (cd j).ψ'))]).foldl SetTheory.app
        (interp V σ₀ (Ψ ((cd j).dJ.mems J)))
      = (psiVals ((cd j).dJ.bb (cd j).ψ') (consList ((cd j).DsA.map (interp V σ₀)) σ₀)
          (ConLeche.recIdxOf ((cd j).dJ.ksR J)) (IndRepData.psiUseIh (cd j).dJ J)
          (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
            (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J) fs
          ((ConLeche.recIdxOf ((cd j).dJ.ksR J)).map fun i =>
            lamTower ((cd j).dJ.bb (cd j).ψ') (consList (fs.take i) (consList ((cd j).DsA.map (interp V σ₀)) σ₀))
              (((cd j).dJ.tssR J (cd j).ψ').getD i []) fun σ'' =>
              ((((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V σ'') ++
                [(Semantics.frameIdx ((((cd j).dJ.tssR J (cd j).ψ').getD i []).length) σ'').foldl
                  SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
                (interp V σ₀ (Ψ ((cd j).dJ.tgtsR J i))))).foldl
          SetTheory.app (interp V (consList ((cd j).DsA.map (interp V σ₀)) σ₀)
            (d.psiHead mpAux.base2 ψ (cd j).dJ.nP (auxOfsOf st p.k cd j) J)) := by
  subst hσ₀
  have hk : 0 < d.k := by rw [R.dk]; omega
  have hpsB := R.DsA_below hj
  have hpv : paramVals d.nP (consList (paramVals d.nP ρ) ρ) = paramVals d.nP ρ :=
    paramVals_push (paramVals_length _ _) ρ
  have hparamsA : SpineFit (consList fs (consList (paramVals d.nP ρ) ρ)) (d.params ψ)
      ((paramBvarsAt d.nP (d.nP + fs.length)).map (interp V (consList fs (consList (paramVals d.nP ρ) ρ)))) := by
    rw [interp_paramBvarsAt_consList, hpv]
    exact d.paramVals_fit (R.ppsM_below hk) hρ
  obtain ⟨lps, S⟩ := R.psiSetup_final (paramBvarsAt_length _ _) hparamsA tbl₀ hj
  rw [interp_paramBvarsAt_consList] at S
  have hJA : J < (cd j).dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  -- the fold terms are bounded at the block's parameters
  have hΦ : ∀ t, t < (cd j).dJ.k → Term.bvarsBelow d.nP
      ((cd j).dJ.foldTermAV mpAux.base2 (cd j).ψ' (cd j).DsA (d.psiL mpAux.base2 ψ p.k (cd j).base)
        (d.psiPinsT (cd j).dJ.nP)
        ((cd j).dJ.psiBodyAV (d.psiHead mpAux.base2 ψ (cd j).dJ.nP (auxOfsOf st p.k cd j))
          (IndRepData.psiUseIh (cd j).dJ)
          (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
            (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀))) t).erase := by
    intro t ht
    exact d.psiTerm_below (R.groupFacts_at hj ht) R.viewA hpsB _
      (fun Jc cAJ hJc i hi hA hT hk => R.final_below tbl₀ (R.transport_lt hj hJc i))
  have h := IndRepData.PsiSetup.fold_iota_vals (cd j).dJ S hb hJ hvs hfit hpsB hΦ
    (d.psiHead_below mpAux.base2 ψ (cd j).dJ.nP (auxOfsOf st p.k cd j) J) (R.psiVia_below tbl₀ hj hJ)
  -- the fold terms are the final table's entries
  have hΨm : ∀ t, t < (cd j).dJ.k → interp V (consList (paramVals d.nP ρ) ρ) (Ψ t)
      = interp V (consList (paramVals d.nP ρ) ρ)
          ((cd j).dJ.foldTermAV mpAux.base2 (cd j).ψ' (cd j).DsA (d.psiL mpAux.base2 ψ p.k (cd j).base)
            (d.psiPinsT (cd j).dJ.nP)
            ((cd j).dJ.psiBodyAV (d.psiHead mpAux.base2 ψ (cd j).dJ.nP (auxOfsOf st p.k cd j))
              (IndRepData.psiUseIh (cd j).dJ)
              (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
                (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀))) t) := by
    intro t ht
    rw [hΨ, R.final_group tbl₀ hj ht]
  rw [hΨm _ (S.hmems J hJA)]
  have hmap : ∀ (g : Nat → AnnotTerm) (f : Nat → V → (Nat → V) → V → V),
      (∀ t, t < (cd j).dJ.k → interp V (consList (paramVals d.nP ρ) ρ) (g t)
        = interp V (consList (paramVals d.nP ρ) ρ) (Ψ t)) →
      ((ConLeche.recIdxOf ((cd j).dJ.ksR J)).map fun i =>
        lamTower ((cd j).dJ.bb (cd j).ψ')
          (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
            (consList (paramVals d.nP ρ) ρ)))
          (((cd j).dJ.tssR J (cd j).ψ').getD i []) fun σ'' =>
          ((((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx ((((cd j).dJ.tssR J (cd j).ψ').getD i []).length) σ'').foldl
              SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
            (interp V (consList (paramVals d.nP ρ) ρ) (g ((cd j).dJ.tgtsR J i))))
      = ((ConLeche.recIdxOf ((cd j).dJ.ksR J)).map fun i =>
        lamTower ((cd j).dJ.bb (cd j).ψ')
          (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
            (consList (paramVals d.nP ρ) ρ)))
          (((cd j).dJ.tssR J (cd j).ψ').getD i []) fun σ'' =>
          ((((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx ((((cd j).dJ.tssR J (cd j).ψ').getD i []).length) σ'').foldl
              SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
            (interp V (consList (paramVals d.nP ρ) ρ) (Ψ ((cd j).dJ.tgtsR J i)))) := by
    intro g _ hg
    apply List.map_congr_left
    intro i _
    rw [hg _ (by rw [(S.hview J).2.1]; exact S.htgts J i)]
  rw [← hmap _ (fun _ _ _ x => x) (fun t ht => (hΨm t ht).symm)]
  exact h

set_option maxHeartbeats 1600000 in
/-- **ψ⁻¹'s ι at values, at the run** (the shape `r2_step`/`r1_step`
take it): at aux constructor `J'` and field values `vs'` fitting its
telescope under the block's parameters (the frame `ρ`, its parameter
values pushed), ψ⁻¹'s fold term at the constructor's member, at its
index readings and value, is the head at the MIXED values — with the
fold terms at the fields' targets inside.  `InvSetup.fold_iota_vals`
at the run's setup (`NestedRunFacts.inv`) at the pushed frame. -/
theorem inv_iota (hk : 0 < d.k) {ρ : Nat → V} (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
    (hb : d.bb ψ ≠ 0) {J' : Nat} {cA' : ConstantVal × Nat} (hJ' : d.ctorsA[J']? = some cA') {vs' : List V}
    (hvs : vs'.length = cA'.2)
    (hfit : SpineFit ρ ((d.dsF J' ψ).map (·.2.2)) (paramVals d.nP ρ ++ vs')) :
    ((d.esF J' ψ).map (interp V (consList (paramVals d.nP ρ ++ vs') ρ)) ++
        [(paramVals d.nP ρ ++ vs').foldl SetTheory.app (interp V ρ (mpAux.base2.acval cA'.1.name ψ))]).foldl
        SetTheory.app
        (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (d.mems J')))
      = (mixedVals (ConLeche.recIdxOf (d.ksR J')) (d.invUseIh p.k J') vs'
          ((ConLeche.recIdxOf (d.ksR J')).map fun i =>
            lamTower (d.bb ψ) (consList (vs'.take i) ρ) ((d.tssR J' ψ).getD i []) fun σ'' =>
              (((d.eissR J' ψ).getD i []).map (interp V σ'') ++
                [(Semantics.frameIdx (((d.tssR J' ψ).getD i []).length) σ'').foldl SetTheory.app
                  (vs'.getD i pt)]).foldl SetTheory.app
                (interp V ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
                  (d.tgtsR J' i))))).foldl
          SetTheory.app (interp V ρ (d.invHead mpAux.base2 ψ st.pins.length cd (auxOfsOf st p.k cd) J')) := by
  obtain ⟨lpsI, lpsT', hinv⟩ := R.inv
  have hparams : SpineFit (consList (paramVals d.nP ρ) (consList vs' ρ)) (d.params ψ)
      ((paramBvarsAt d.nP d.nP).map (interp V (consList (paramVals d.nP ρ) (consList vs' ρ)))) := by
    unfold paramBvarsAt
    rw [map_fieldBvars_interp (paramVals_length _ _)]
    exact d.paramVals_fit (R.ppsM_below hk) hρ
  have S := hinv (consList (paramVals d.nP ρ) (consList vs' ρ)) (paramBvarsAt d.nP d.nP)
    (paramBvarsAt_length _ _) (wellDenotedV_paramBvarsAt _ _ _) hparams
  obtain ⟨-, hkb, -, -, -, -, -, hall⟩ := R.reps
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, -, hrep₀⟩ := hall 0 (by rw [← hkb]; exact hk)
  have hkR : d.kReal = d.k := by
    obtain ⟨-, hkb, hkRb, -⟩ := R.reps
    rw [hkb, hkRb]
  have hDsA : ∀ j, j < st.pins.length → ∀ q ∈ (cd j).DsA, Term.bvarsBelow d.nP q.erase :=
    fun j hj => R.DsA_below hj
  have hhead : ∀ J, Term.bvarsBelow d.nP
      (d.invHead mpAux.base2 ψ st.pins.length cd (auxOfsOf st p.k cd) J).erase :=
    d.invHead_below mpAux.base2 ψ st.pins.length (auxOfsOf st p.k cd) hDsA
  have hΦ : ∀ t, t < d.k → Term.bvarsBelow d.nP
      (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s t).erase := by
    intro t ht
    refine IndRepData.InvSetup.foldTerm_below (d.withSort s) S (mm := d.nP)
      (paramBvarsAt_below (Nat.le_refl _)) ?_ (fun t _ => d.invL_below mpAux.base2 ψ p.k cd t) ?_ ?_
    · intro t ht
      have h := IndRepData.ipss_below_of_indRep _ hrep₀ hkR ψ ht
      exact h
    · intro t ht q hq
      exact Term.bvarsBelow.mono (Nat.le_add_right _ _)
        (d.invPinsT_below hDsA t (by rw [← R.dk]; exact ht) q hq)
    · intro J _
      exact Term.bvarsBelow.mono (Nat.le_add_right _ _) (hhead J)
  exact IndRepData.InvSetup.fold_iota_vals (d.withSort s) S hb hJ' hvs hfit hΦ (hhead J')

end NestedRunFacts

/-! ## Small facts -/

/-- A graded application spine's head is graded. -/
theorem wellDenoted_mkAppN_head {ρ : Nat → V} :
    ∀ {as : List AnnotTerm} {f : AnnotTerm}, WellDenoted V ρ (AnnotTerm.mkAppN f as) → WellDenoted V ρ f
  | [], _, h => h
  | _ :: as, f, h => by
    have := wellDenoted_mkAppN_head (as := as) h
    rw [WellDenoted_app] at this
    exact this.1

/-- A graded application spine's arguments are graded. -/
theorem wellDenoted_mkAppN_args {ρ : Nat → V} :
    ∀ {as : List AnnotTerm} {f : AnnotTerm}, WellDenoted V ρ (AnnotTerm.mkAppN f as) →
      ∀ a ∈ as, WellDenoted V ρ a
  | [], _, _, _, ha => nomatch ha
  | a :: as, f, h, a', ha' => by
    rcases List.mem_cons.mp ha' with rfl | ha'
    · have := wellDenoted_mkAppN_head (as := as) h
      rw [WellDenoted_app] at this
      exact this.2.1
    · exact wellDenoted_mkAppN_args (as := as) h a' ha'

/-- **ψ's values shadow the fields off the replaced positions** (no fit
needed: `psiVals` is the field itself there). -/
theorem psiVals_shadowRelP (b : Nat) (ρp : Nat → V) (recIdx : List Nat) (useIh : Nat → Bool)
    (via : Nat → Option ViaSpec) (fs ihs : List V) :
    ShadowRelP (replaced useIh via) fs (psiVals b ρp recIdx useIh via fs ihs) := by
  refine ⟨psiVals_length _ _ _ _ _ _ _, fun l hl hnr => ?_⟩
  rw [psiVals_getD _ _ _ _ _ _ _ hl]
  have hnu : useIh l = false := by
    cases h : useIh l
    · rfl
    · exact absurd (Or.inl h) hnr
  have hnv : via l = none := by
    cases h : via l with
    | none => rfl
    | some v => exact absurd (Or.inr (by rw [h]; rfl)) hnr
  rw [hnv]
  simp only [hnu, Bool.false_eq_true, if_false]

omit [SetTheory V] in
/-- The constructor data of a real constructor, in the recursor's view. -/
theorem IndRepData.cdsR_getElem?_of (d : IndRepData V) {ψ : Name → Nat} (hctorsC : d.ctorsC = [])
    {J : Nat} {cA : ConstantVal × Nat} (hJ : d.ctorsA[J]? = some cA) :
    (d.cdsR ψ)[J]? = some (cA.1.name, cA.2, d.dsF J ψ, d.esF J ψ, ConLeche.recIdxOf (d.ksR J),
      d.eissR J ψ, d.tssR J ψ) := by
  unfold IndRepData.cdsR IndRepData.ctorsAll
  rw [fixCtorDataList_getElem?, Nat.zero_add, hctorsC, List.append_nil, hJ]
  rfl

/-! ## The ι-side spine fits the minor's telescope

`psiVals_fit` (the fit of ψ's values at the transported domains) takes
the fit of the fields and the hypotheses at the minor's TARGET-form
telescope.  At the ι law the hypotheses are the λ-towers of the fold at
the fields' targets, and each lies in its target-form ih domain: the
domain reads as the nested product over the field's telescope of the
target at the field's index values (`interp_tgIhDomAV`), and the fold
at the target lands there (`fold_mem_vals` + `invTg_fold`). -/

/-- **λ-towers whose bodies land in the target fit the target-form ih
binders**, entry by entry along the recursive positions. -/
theorem spineFit_ihDataTg_of {Tg : Nat → AnnotTerm} {moti : Nat → Nat} {nP nF o b : Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)} {ρ : Nat → V}
    {psv Msv ms fs : List V} (hps : psv.length = nP) (hms : ms.length + Msv.length = o)
    (hk : 0 < Msv.length) (hfs : fs.length = nF) (g : Nat → (Nat → V) → V) :
    ∀ (is : List Nat) (l : Nat) (ihs0 : List V), ihs0.length = l →
      (∀ i ∈ is, i < nF ∧
        ∀ as, SpineFit (consList (fs.take i) (consList psv ρ)) ((tls.getD i []).map (·.2.2)) as →
          g i (consList as (consList (fs.take i) (consList psv ρ)))
            ∈ˢ ((Eiss.getD i []).map (interp V (consList as (consList (fs.take i) (consList psv ρ))))).foldl
                SetTheory.app (interp V ρ (Tg (moti i)))) →
      SpineFit (consList ihs0 (consList fs (consList ms (consList Msv (consList psv ρ)))))
        ((ihDataTg Tg moti nP nF o b tls Eiss is l).map (·.2.2))
        (is.map fun i => lamTower b (consList (fs.take i) (consList psv ρ)) (tls.getD i []) (g i))
  | [], _, _, _, _ => trivial
  | i :: is, l, ihs0, hl, h => by
    obtain ⟨hi, hmem⟩ := h i List.mem_cons_self
    simp only [ihDataTg, List.map_cons, SpineFit]
    refine ⟨?_, ?_⟩
    · rw [interp_tgIhDomAV hps hms hk hfs hl hi (fun x hx => by rw [mem_rebit hx]) Tg (moti i)
        (Eiss.getD i []), rebit_map_dom]
      refine lamTower_mem_piTele fun as hfit => ?_
      rw [List.nil_append]
      exact hmem as (fitsS_teleOfFields.mp hfit)
    · rw [consList_snoc']
      exact spineFit_ihDataTg_of hps hms hk hfs g is (l + 1) (ihs0 ++ [_]) (by simp [hl])
        (fun i' hi' => h i' (List.mem_cons_of_mem _ hi'))

namespace IndRepData

variable (d : IndRepData V)

namespace PsiSetup

variable {μ : CheckMode} {mp : EnvModelM V μ env} {lps lpsT : List Name} {ψ : Name → Nat}
  {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm}
  {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {via : Nat → Nat → Option ViaSpec}
  {TgV domA : Nat → Nat → AnnotTerm}

set_option maxHeartbeats 1600000 in
/-- **The ι-side spine fits the minor's target-form telescope**: the
fields (fitting the real domains, lifted over the choice's prefix) and
the fold's λ-towers at the fields' targets (`spineFit_ihDataTg_of`,
the bodies landing in the target by `fold_mem_vals` at the field's
own typing, `ctorFieldFacts_of`). -/
theorem minor_fit (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV domA)
    {J : Nat} {cA : ConstantVal × Nat} (hj : d.ctorsA[J]? = some cA) {fs : List V}
    (hfs : SpineFit (consList (ps.map (interp V ρ)) ρ) (((d.dsF J ψ).drop d.nP).map (·.2.2)) fs) :
    SpineFit (consList ((ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
        d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
          (d.psiBodyAV head useIh via) J).map (interp V ρ)) ρ)
      ((minorDataTg (d.invTgAV ψ ps L pinsT) (d.tgtsR J) d.nP cA.2 (d.bb ψ) (d.k + J) (d.dsF J ψ)
        (ConLeche.recIdxOf (d.ksR J)) (d.tssR J ψ) (d.eissR J ψ)).map (·.2.2))
      (fs ++ (ConLeche.recIdxOf (d.ksR J)).map fun i =>
        lamTower (d.bb ψ) (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)) ((d.tssR J ψ).getD i [])
          fun σ'' =>
          (((d.eissR J ψ).getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx (((d.tssR J ψ).getD i []).length) σ'').foldl SetTheory.app
              (fs.getD i pt)]).foldl SetTheory.app
            (interp V ρ (d.foldTermAV mp.base2 ψ ps L pinsT (d.psiBodyAV head useIh via) (d.tgtsR J i)))) := by
  have hJA : J < d.ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have hC := S.hctors J cA hj
  have hD := hC.2.2
  obtain ⟨hks, htgtR, heiss, htss⟩ := S.hview J
  have hlenD : (d.dsF J ψ).length = d.nP + cA.2 := hD.len ψ
  have hfsLen : fs.length = cA.2 := by
    rw [hfs.length_eq, List.length_map, List.length_drop, hlenD]; omega
  have cff := d.ctorFieldFacts_of mp S.hps S.hpins S.hLS S.hFF S.hparams hC (S.hpIff J cA hj)
    (S.hmems J hJA) (S.htgts J) (fun i => by rw [htgtR])
  -- the frame: the parameters, the motives, the earlier minors
  have hσJ : consList ((ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
      d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
        (d.psiBodyAV head useIh via) J).map (interp V ρ)) ρ
      = consList ((d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
          (d.psiBodyAV head useIh via) J).map (interp V ρ))
          (consList ((d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT)).map (interp V ρ))
            (consList (ps.map (interp V ρ)) ρ)) := by
    rw [List.map_append, List.map_append, consList_append, consList_append]
  rw [hσJ]
  have hMsLen : ((d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT)).map (interp V ρ)).length = d.k := by
    rw [List.length_map]; exact d.motChoiceAVs_length _ _ _ _
  have hpriorLen : ((d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
      (d.psiBodyAV head useIh via) J).map (interp V ρ)).length = J := by
    rw [List.length_map]; exact d.minChoiceAVs_length _ _ _ _ _
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by rw [List.length_map, S.hps]
  have hshiftO : shiftE (d.k + J) 0
      (consList ((d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
        (d.psiBodyAV head useIh via) J).map (interp V ρ))
        (consList ((d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT)).map (interp V ρ))
          (consList (ps.map (interp V ρ)) ρ)))
      = consList (ps.map (interp V ρ)) ρ := by
    rw [← consList_append, show d.k + J = ((d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT)).map (interp V ρ) ++
      (d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
        (d.psiBodyAV head useIh via) J).map (interp V ρ)).length from by
      rw [List.length_append, hMsLen, hpriorLen]]
    exact shiftE_consList _ _
  unfold minorDataTg
  rw [List.map_append]
  refine SpineFit.append ?_ ?_
  · -- the fields, lifted over the prefix
    rw [rebit_map_dom, spineFit_liftDoms, hshiftO]
    exact hfs
  · -- the hypotheses
    refine spineFit_ihDataTg_of hpsLen (by rw [hMsLen, hpriorLen]; omega) (by rw [hMsLen]; exact S.hk)
      hfsLen _ (ConLeche.recIdxOf (d.ksR J)) 0 [] rfl ?_
    intro i hi
    obtain ⟨hlt, -⟩ := mem_recIdxOf.mp hi
    rw [hks, hD.ksLen] at hlt
    refine ⟨hlt, fun as has => ?_⟩
    have hasLen : as.length = ((d.tssR J ψ).getD i []).length := by
      rw [has.length_eq, List.length_map]
    have hiF : i ∈ ConLeche.recIdxOf (d.ksF J) := by rw [← hks]; exact hi
    rw [htss] at has
    obtain ⟨hE, hx⟩ := cff.1 i hiF fs hfs as has
    rw [← htss] at has
    -- the body is the fold at the target applied
    show ((((d.eissR J ψ).getD i []).map (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))) ++
      [(Semantics.frameIdx (((d.tssR J ψ).getD i []).length)
        (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))).foldl SetTheory.app
          (fs.getD i pt)]).foldl SetTheory.app
      (interp V ρ (d.foldTermAV mp.base2 ψ ps L pinsT (d.psiBodyAV head useIh via) (d.tgtsR J i)))) ∈ˢ _
    rw [← consList_append, frameIdx_of _ hasLen, consList_append]
    have htgt : d.tgtsR J i < d.k := by rw [htgtR]; exact S.htgts J i
    rw [heiss]
    have hfitM : SpineFit (consList (ps.map (interp V ρ)) ρ)
        ((d.motDataAV mp.base2 ψ (d.tgtsR J i)).map (·.2.2))
        ((((d.eissF J ψ).getD i []).map (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ))))) ++
          [as.foldl SetTheory.app (fs.getD i pt)]) := by
      have hsplit : (d.motDataAV mp.base2 ψ (d.tgtsR J i)).map (·.2.2)
          = (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.tgtsR J i) [])).map (·.2.2) ++
            [famAppAV ((d.Ls mp.base2 ψ).getD (d.tgtsR J i) default) (d.pinsOf ψ (d.tgtsR J i)) d.nP
              (d.nP + d.nIdxs.getD (d.tgtsR J i) 0) (d.nIdxs.getD (d.tgtsR J i) 0)] := by
        simp [IndRepData.motDataAV]
      rw [hsplit]
      exact SpineFit.append hE ⟨hx, trivial⟩
    have hmem := IndRepData.PsiSetup.fold_mem_vals d S htgt hfitM
    rw [d.invTg_fold ψ hE]
    exact hmem

/-- **ψ's values fit the transported domains** at the ι-side spine
(`psiVals_fit` at `minor_fit`). -/
theorem psiVals_fit_of (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV domA)
    {J : Nat} {cA : ConstantVal × Nat} (hj : d.ctorsA[J]? = some cA) {fs : List V}
    (hfs : SpineFit (consList (ps.map (interp V ρ)) ρ) (((d.dsF J ψ).drop d.nP).map (·.2.2)) fs) :
    SpineFit (consList (ps.map (interp V ρ)) ρ)
      (psiDomsAV (d.invTgAV ψ ps L pinsT) (TgV J) (domA J) (useIh J) (via J) d.nP (d.bb ψ) (d.tgtsR J)
        (d.dsF J ψ) (d.eissR J ψ) (d.tssR J ψ) cA.2)
      (psiVals (d.bb ψ) (consList (ps.map (interp V ρ)) ρ) (ConLeche.recIdxOf (d.ksR J)) (useIh J) (via J) fs
        ((ConLeche.recIdxOf (d.ksR J)).map fun i =>
          lamTower (d.bb ψ) (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)) ((d.tssR J ψ).getD i [])
            fun σ'' =>
            (((d.eissR J ψ).getD i []).map (interp V σ'') ++
              [(Semantics.frameIdx (((d.tssR J ψ).getD i []).length) σ'').foldl SetTheory.app
                (fs.getD i pt)]).foldl SetTheory.app
              (interp V ρ (d.foldTermAV mp.base2 ψ ps L pinsT (d.psiBodyAV head useIh via) (d.tgtsR J i))))) := by
  have hcd := d.cdsR_getElem?_of (ψ := ψ) S.hctorsC hj
  have hD := (S.hctors J cA hj).2.2
  obtain ⟨hnbT, hnbE, -, hnbV⟩ := S.hnbP J cA hj _ _ _ _ _ _ _ hcd
  have hfsLen : fs.length = cA.2 := by
    rw [hfs.length_eq, List.length_map, List.length_drop, hD.len ψ]; omega
  have h := d.psiVals_fit S.hps (d.motChoiceAVs_length _ _ _ _) S.hk (d.minChoiceAVs_length _ _ _ _ _)
    (hD.len ψ) (S.hnbA J cA hj) (S.hord J cA hj) hnbT hnbE hnbV (S.huse J)
    (S.hvia J cA hj _ _ _ _ _ _ _ hcd) fs _ hfsLen (by rw [List.length_map])
    (IndRepData.PsiSetup.minor_fit d S hj hfs)
  exact h.2.2

end PsiSetup

end IndRepData

/-! ## The heads -/

/-- **ψ's head reads as the copy constructor at the block's parameters**:
`psiHead` is the copy constructor at the parameter variables lifted
over the pin's readings, so at the container's parameter frame over
the pushed frame it is the constructor at the frame's parameter
values. -/
theorem IndRepData.psiHead_interp (d : IndRepData V) (m : EnvModel V env) (ψ : Name → Nat)
    {nPJ : Nat} (auxOf : Nat → Nat) {J : Nat} {cA' : ConstantVal × Nat}
    (hget : d.ctorsA[auxOf J]? = some cA') {ρ : Nat → V} {DsAv : List V} (hlen : DsAv.length = nPJ) :
    interp V (consList DsAv (consList (paramVals d.nP ρ) ρ)) (d.psiHead m ψ nPJ auxOf J)
      = (paramVals d.nP ρ).foldl SetTheory.app (interp V ρ (m.acval cA'.1.name ψ)) := by
  unfold IndRepData.psiHead
  rw [interp_liftN, ← hlen, shiftE_consList, interp_mkAppN_map, List.getD_eq_getElem?_getD, hget,
    Option.getD_some, interp_closed (V := V) (m.cval_closedL _ ψ) _ ρ]
  show (paramVals d.nP (consList (paramVals d.nP ρ) ρ)).foldl _ _ = _
  rw [paramVals_push (paramVals_length _ _)]

/-! ## R2 at the run: the assembly

`r2_step` takes the constructor's bookkeeping facts as hypotheses; the
run derives them one by one.  `R2Owed` names the ones still owed at
a constructor `J` of pin `j`'s container and a spine `fs` fitting its
real domains — each in the exact shape `r2_step` consumes. -/

namespace NestedRunFacts

variable {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState}
  {b : MutualBlock} {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)}
  {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
  {lpsT : List Name} {order : List Nat} {s : Level}
  (R : NestedRunFacts F env p st b params pbs mpAux d ψ cd lpsT order s)

end NestedRunFacts

/-- ψ's values at container constructor `J` of pin `j`'s container at
the fields `fs`, over the block's parameter frame `σ₀` (the transports
and the hypotheses at the final table's entries). -/
@[expose] noncomputable def IndRepData.psiValsAt (d : IndRepData V) (m : EnvModel V env) (ψ : Name → Nat)
    (k₀ : Nat) (cd : Nat → CopyData V) (auxOfs : Nat → Nat → Nat) (order : List Nat)
    (tbl₀ : Nat → AnnotTerm) (σ₀ : Nat → V) (j J : Nat) (fs : List V) : List V :=
  psiVals ((cd j).dJ.bb (cd j).ψ') (consList ((cd j).DsA.map (interp V σ₀)) σ₀)
    (ConLeche.recIdxOf ((cd j).dJ.ksR J)) (IndRepData.psiUseIh (cd j).dJ J)
    (d.psiVia (cd j).dJ ψ k₀ (cd j).dJ.nP (auxOfs j) ((cd j).dJ.bb (cd j).ψ')
      (d.psiFinal m ψ k₀ cd auxOfs order tbl₀) J) fs
    ((ConLeche.recIdxOf ((cd j).dJ.ksR J)).map fun i =>
      lamTower ((cd j).dJ.bb (cd j).ψ') (consList (fs.take i) (consList ((cd j).DsA.map (interp V σ₀)) σ₀))
        (((cd j).dJ.tssR J (cd j).ψ').getD i []) fun σ'' =>
        ((((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V σ'') ++
          [(Semantics.frameIdx ((((cd j).dJ.tssR J (cd j).ψ').getD i []).length) σ'').foldl
            SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
          (interp V σ₀ (d.psiFinal m ψ k₀ cd auxOfs order tbl₀ ((cd j).base + (cd j).dJ.tgtsR J i))))

/-- ψ⁻¹'s mixed values at the copy constructor of `J` at ψ's values,
over the frame `ρ`. -/
@[expose] noncomputable def IndRepData.mixedValsAt (d : IndRepData V) (m : EnvModel V env) (ψ : Name → Nat)
    (k₀ n : Nat) (cd : Nat → CopyData V) (auxOfs : Nat → Nat → Nat) (order : List Nat) (s : Level)
    (tbl₀ : Nat → AnnotTerm) (ρ : Nat → V) (j J : Nat) (fs : List V) : List V :=
  mixedVals (ConLeche.recIdxOf (d.ksR (auxOfs j J))) (d.invUseIh k₀ (auxOfs j J))
    (d.psiValsAt m ψ k₀ cd auxOfs order tbl₀ (consList (paramVals d.nP ρ) ρ) j J fs)
    ((ConLeche.recIdxOf (d.ksR (auxOfs j J))).map fun i =>
      lamTower (d.bb ψ)
        (consList ((d.psiValsAt m ψ k₀ cd auxOfs order tbl₀ (consList (paramVals d.nP ρ) ρ) j J fs).take i) ρ)
        ((d.tssR (auxOfs j J) ψ).getD i []) fun σ'' =>
        (((d.eissR (auxOfs j J) ψ).getD i []).map (interp V σ'') ++
          [(Semantics.frameIdx (((d.tssR (auxOfs j J) ψ).getD i []).length) σ'').foldl
            SetTheory.app
            ((d.psiValsAt m ψ k₀ cd auxOfs order tbl₀ (consList (paramVals d.nP ρ) ρ) j J fs).getD i pt)]).foldl
          SetTheory.app (interp V ρ (d.invFold m ψ k₀ n cd auxOfs s (d.tgtsR (auxOfs j J) i))))

namespace NestedRunFacts

variable {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState}
  {b : MutualBlock} {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)}
  {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
  {lpsT : List Name} {order : List Nat} {s : Level}

/-- **The fact still owed at a constructor** (task #279 M-C′ step 4),
at pin `j`, container constructor `J` (its copy `auxOfsOf st p.k cd j J`)
and the frame `ρ` — in `r2_step`'s shape: ψ⁻¹'s head at the copy is
`invHead`'s REPRESENTATIVE's container constructor at the
representative's readings, and every representative of the copy
constructor is THIS container constructor at THIS pin's readings (the
mint's injectivity: `ctorBase` + `posIn` recover the pin's group member
and the constructor's position, the group clause makes the
representative's data the pin's). -/
structure R2Owed (mpAux : EnvModelM V μ envAux) (d : IndRepData V) (ψ : Name → Nat) (cd : Nat → CopyData V)
    (ρ : Nat → V) (j J : Nat) (cA : ConstantVal × Nat) : Prop where
  /-- ψ⁻¹'s head at the copy reads as the container constructor at the
  pin's readings (the representative's reading: every representative
  of the copy constructor is this container constructor at this pin's
  readings) -/
  headφ : interp V ρ (d.invHead mpAux.base2 ψ st.pins.length cd (auxOfsOf st p.k cd) (auxOfsOf st p.k cd j J))
    = ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).foldl SetTheory.app
        (interp V (consList (paramVals d.nP ρ) ρ) (mpAux.base2.acval cA.1.name (cd j).ψ'))

variable (R : NestedRunFacts F env p st b params pbs mpAux d ψ cd lpsT order s)

include R

/-- The pin's readings fit the container's parameters at the block's
parameter frame (`pinFit_of_leafShape` at the group's member `0`). -/
theorem pinFit {j : Nat} (hj : j < st.pins.length) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) :
    SpineFit (consList (paramVals d.nP ρ) ρ) ((cd j).dJ.params (cd j).ψ')
      ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  have hk : 0 < (cd j).dJ.k := Nat.lt_of_le_of_lt (Nat.zero_le _) ht₀
  have hsatA : Sat V (d.params ψ).reverse (consList (paramVals d.nP ρ) ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hρ
    rwa [List.append_nil] at h
  have hc0 := hg.grp 0 hk
  exact d.pinFit_of_leafShape rfl ((cd j).dJ.formerFacts_of_indRep hrepJ hg.kReal (cd j).ψ' hk)
    (hrepJ.leafShape 0 (by rw [hg.kReal]; exact hk) (cd j).ψ') hc0.pin hsatA

set_option maxHeartbeats 1600000 in
/-- **A container constructor's readings, graded and fitting** (task
#279 M-C′ step 4 — the owed `esOk`/`esFit`/`entry`): at pin `j`,
constructor `J`, at the container's parameter frame over the block's:
at a spine fitting the real domains the result readings are graded
(the tower's body is, `wellDenoted_mkPisAV_body`) and fit the member's
telescope (`ctorFieldFacts_of`); at a recursive position and any
fitting prefix the entry's readings are graded (the entry's domain is,
`wellDenoted_mkPisAV_dom` + `recEntry`) and fit the target's telescope
(`idxFit_of_entry`). -/
theorem ctor_facts (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) :
    (∀ fs : List V,
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        (((cd j).dJ.Fss (cd j).ψ').getD J []) fs →
      (∀ E ∈ (cd j).dJ.esF J (cd j).ψ',
        WellDenoted V (consList fs (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
          (consList (paramVals d.nP ρ) ρ))) E) ∧
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        ((cd j).dJ.IdsM ((cd j).dJ.mems J) (cd j).ψ')
        (((cd j).dJ.esF J (cd j).ψ').map (interp V (consList fs
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))))) ∧
    (∀ i, ((cd j).dJ.ksF J).getD i .ordinary = .recursive → ∀ ws : List V, ws.length = i →
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        (((((cd j).dJ.dsF J (cd j).ψ').drop (cd j).dJ.nP).map (·.2.2)).take i) ws →
      (∀ E ∈ ((cd j).dJ.eissF J (cd j).ψ').getD i [],
        WellDenoted V (consList ws (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
          (consList (paramVals d.nP ρ) ρ))) E) ∧
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        ((cd j).dJ.IdsM ((cd j).dJ.tgts J i) (cd j).ψ')
        ((((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList ws
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))))) := by
  obtain ⟨lps, S⟩ := R.psiSetup_final (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) (paramBvarsAt_length _ _) hρ
    tbl₀ hj
  have hg := R.groupFacts hj
  have hC := S.hctors J cA hJ
  have hD := hC.2.2
  have hJA : J < (cd j).dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  have hmemJ := S.hmems J hJA
  have hlenD : ((cd j).dJ.dsF J (cd j).ψ').length = (cd j).dJ.nP + cA.2 := hD.len (cd j).ψ'
  have hDsLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := by
    rw [List.length_map, hg.len]
  have hDsFit := R.pinFit hj hρ
  have hfitP : SpineFit (consList (paramVals d.nP ρ) ρ) ((((cd j).dJ.dsF J (cd j).ψ').take (cd j).dJ.nP).map (·.2.2))
      ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) :=
    spineFit_of_paramsIff hDsLen (by rw [List.length_map, List.length_take, hlenD]; omega) hDsFit
      (S.hpIff J cA hJ)
  have cff := (cd j).dJ.ctorFieldFacts_of mpAux S.hps S.hpins S.hLS S.hFF S.hparams hC (S.hpIff J cA hJ)
    hmemJ (S.htgts J) (fun i => by rw [(S.hview J).2.1])
  refine ⟨fun fs hfs => ?_, fun i hrec ws hws hpre => ?_⟩
  · have hfs' : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        ((((cd j).dJ.dsF J (cd j).ψ').drop (cd j).dJ.nP).map (·.2.2)) fs := by
      rw [← (cd j).dJ.Fss_getD (cd j).ψ' hJ]; exact hfs
    have hfitAll : SpineFit (consList (paramVals d.nP ρ) ρ) (((cd j).dJ.dsF J (cd j).ψ').map (·.2.2))
        ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) ++ fs) := by
      rw [← List.take_append_drop (cd j).dJ.nP ((cd j).dJ.dsF J (cd j).ψ'), List.map_append]
      exact hfitP.append hfs'
    refine ⟨?_, ?_⟩
    · have hwd := wellDenoted_mkPisAV_body (hD.okTy (cd j).ψ' (consList (paramVals d.nP ρ) ρ)).1 _ hfitAll
      rw [consList_append] at hwd
      unfold ctorBodyAVI at hwd
      intro E hE
      exact wellDenoted_mkAppN_args hwd E (List.mem_append_right _ hE)
    · have h := (cff.2 fs hfs').1
      rw [(cd j).dJ.ipss_getD (cd j).ψ' hmemJ, rebit_map_dom] at h
      exact h
  · have hklt : i < ((cd j).dJ.ksF J).length := by
      rcases Nat.lt_or_ge i ((cd j).dJ.ksF J).length with h | h
      · exact h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h] at hrec
        exact absurd hrec (by simp)
    have hilt : i < cA.2 := by rw [← hD.ksLen]; exact hklt
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
    rw [consList_append, hD.recEntry (cd j).ψ' i hrec hilt] at hok
    refine ⟨fun E hE => wellDenoted_mkAppN_args hok E (List.mem_append_right _ hE), ?_⟩
    exact (cd j).dJ.idxFit_of_entry (ρ₀ := consList (paramVals d.nP ρ) ρ) (psA := (cd j).DsA) S.hps
      (S.hFF _ (S.htgts J i)) (S.hLS _ (S.htgts J i)) hws hok (hD.eisLen (cd j).ψ' i hrec hilt)

set_option maxHeartbeats 1600000 in
/-- **The copy constructor's index readings at ψ's values are the
container's at the fields** (the owed `es`): the record's `es` (the
copy's readings are the container's instantiated at the pin, under
the fields), `interp_instSeq_under`, and ψ's values shadow the fields
off the replaced positions, which the readings do not mention
(`hnbP`, `interp_congr_shadowRelP`). -/
theorem es_of_record (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) {fs : List V}
    (hlen : fs.length = cA.2) :
    (d.esF (auxOfsOf st p.k cd j J) ψ).map
        (interp V (consList (paramVals d.nP ρ ++
          d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (consList (paramVals d.nP ρ) ρ) j J fs) ρ))
      = ((cd j).dJ.esF J (cd j).ψ').map (interp V (consList fs
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))) := by
  obtain ⟨lps, S⟩ := R.psiSetup_final (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) (paramBvarsAt_length _ _) hρ
    tbl₀ hj
  have hg := R.groupFacts hj
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hVSlen : (d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (consList (paramVals d.nP ρ) ρ) j J fs).length
      = fs.length := by
    unfold IndRepData.psiValsAt; rw [psiVals_length]
  obtain ⟨-, -, hnbEs, -⟩ := S.hnbP J cA hJ _ _ _ _ _ _ _ ((cd j).dJ.cdsR_getElem?_of hg.ctorsC hJ)
  have hsh := psiVals_shadowRelP ((cd j).dJ.bb (cd j).ψ')
    (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
    (ConLeche.recIdxOf ((cd j).dJ.ksR J)) (IndRepData.psiUseIh (cd j).dJ J)
    (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J) fs
    ((ConLeche.recIdxOf ((cd j).dJ.ksR J)).map fun i =>
      lamTower ((cd j).dJ.bb (cd j).ψ')
        (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        (((cd j).dJ.tssR J (cd j).ψ').getD i []) fun σ'' =>
        ((((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V σ'') ++
          [(Semantics.frameIdx ((((cd j).dJ.tssR J (cd j).ψ').getD i []).length) σ'').foldl
            SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
          (interp V (consList (paramVals d.nP ρ) ρ) (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
            ((cd j).base + (cd j).dJ.tgtsR J i))))
  rw [hf.read.es, List.map_map]
  apply List.map_congr_left
  intro E hE
  simp only [Function.comp_def]
  rw [consList_append, interp_instSeq_under (consList (paramVals d.nP ρ) ρ) (cd j).DsA _ _ E
    (fun hne => by
      have hpos : 0 < (cd j).DsA.length := List.length_pos_iff.mpr hne
      rw [hg.len] at hpos
      rw [hg.len, hVSlen, hlen]; omega)]
  have h := interp_congr_shadowRelP hsh
    (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)) []
    (E := E) (by rw [hlen, List.length_nil, Nat.add_zero]; exact hnbEs E hE)
  simp only [consList_nil] at h
  exact h.symm

set_option maxHeartbeats 1600000 in
/-- **A container-recursive position** (the second arm of `r2_step`'s
`hpos`, at a FINITARY container field): recursive on both sides with
the same readings — the record's `kindR`, the readings shadowed off the
replaced positions (`psiVals_shadowRelP`, `hnbP`'s `Eiss` clause) and
the pin's readings read alike at the two frames. -/
theorem pos_recJ (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    {fs : List V} (hlen : fs.length = cA.2) {i : Nat} (hi : i < cA.2)
    (hA : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J))
    (hfin : ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = []) :
    IndRepData.psiUseIh (cd j).dJ J i = true ∧
      d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J i = none ∧
      d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true ∧
      i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) ∧ i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) ∧
      ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [] ∧ (d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [] = [] ∧
      d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + (cd j).base + (cd j).dJ.tgts J i ∧
      ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList ((d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
            (consList (paramVals d.nP ρ) ρ) j J fs).take i) ρ))
        = (((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList (fs.take i)
            (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))) := by
  obtain ⟨lps, S⟩ := R.psiSetup_final (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) (paramBvarsAt_length _ _) hρ
    tbl₀ hj
  have hg := R.groupFacts hj
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  have hD := (S.hctors J cA hJ).2.2
  have hVSlen : (d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (consList (paramVals d.nP ρ) ρ) j J fs).length
      = fs.length := by
    unfold IndRepData.psiValsAt; rw [psiVals_length]
  obtain ⟨-, hnbE, -, -⟩ := S.hnbP J cA hJ _ _ _ _ _ _ _ ((cd j).dJ.cdsR_getElem?_of hg.ctorsC hJ)
  have hsh := psiVals_shadowRelP ((cd j).dJ.bb (cd j).ψ')
    (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
    (ConLeche.recIdxOf ((cd j).dJ.ksR J)) (IndRepData.psiUseIh (cd j).dJ J)
    (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J) fs
    ((ConLeche.recIdxOf ((cd j).dJ.ksR J)).map fun i =>
      lamTower ((cd j).dJ.bb (cd j).ψ')
        (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
        (((cd j).dJ.tssR J (cd j).ψ').getD i []) fun σ'' =>
        ((((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V σ'') ++
          [(Semantics.frameIdx ((((cd j).dJ.tssR J (cd j).ψ').getD i []).length) σ'').foldl
            SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
          (interp V (consList (paramVals d.nP ρ) ρ) (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
            ((cd j).base + (cd j).dJ.tgtsR J i))))
  have hksLenA : (d.ksR (auxOfsOf st p.k cd j J)).length = cA'.2 := by
    rw [hf.view.1]; exact hf.ctor.2.2.ksLen
  -- the pin's readings read alike at the two frames
  have hDsA : (cd j).DsA.map (interp V ρ) = (cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) := by
    apply List.map_congr_left
    intro q hq
    exact interp_congr_below V q d.nP _ _ (R.DsA_below hj q hq) (fun i hi => (push_agree ρ ρ i hi).symm)
  obtain ⟨hkind, htl⟩ := hfin
  obtain ⟨hks, htgt, htss, heiss⟩ := hf.read.kindR i hA
  have hrecA : i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) :=
    mem_recIdxOf.mpr ⟨by rw [hksLenA, hf.nF]; exact hi, Or.inl (by rw [hks]; exact hkind)⟩
  refine ⟨?_, ?_, ?_, hA, hrecA, htl, ?_, htgt, ?_⟩
  · unfold IndRepData.psiUseIh; exact decide_eq_true hA
  · unfold IndRepData.psiVia
    rw [if_neg]
    intro h
    exact h.2.1 hA
  · unfold IndRepData.invUseIh
    exact decide_eq_true ⟨by rw [hf.read.mem]; omega, hrecA, by rw [htgt]; omega⟩
  · rw [htss, htl]; rfl
  · rw [heiss, htl, List.length_nil, Nat.add_zero, List.map_map]
    apply List.map_congr_left
    intro E hE
    simp only [Function.comp_def]
    rw [interp_instSeq_under ρ (cd j).DsA _ _ E
      (fun hne => by
        have hpos : 0 < (cd j).DsA.length := List.length_pos_iff.mpr hne
        rw [hg.len] at hpos
        rw [hg.len, List.length_take, hVSlen, hlen]; omega), hDsA]
    have hEb : Term.bvarsBelow ((cd j).dJ.nP + i) E.erase := by
      have := hD.eissBelow (cd j).ψ' i E hE
      rwa [htl, List.length_nil, Nat.add_zero] at this
    have htake : ((d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
        (consList (paramVals d.nP ρ) ρ) j J fs).take i).length = i := by
      rw [List.length_take, hVSlen, hlen]; omega
    rw [interp_congr_below V E ((cd j).dJ.nP + i) _
      (consList ((d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
        (consList (paramVals d.nP ρ) ρ) j J fs).take i)
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ)))
      hEb ?_]
    · have h := interp_congr_shadowRelP_at hsh
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        (n := i) (by rw [hlen]; omega) (E := E)
        (by have := hnbE i hi E (by rw [(S.hview J).2.2.1]; exact hE)
            rwa [(S.hview J).2.2.2, htl, List.length_nil, Nat.add_zero] at this)
      exact h.symm
    · intro l hl
      refine consList_agree_below (n := (cd j).dJ.nP) ?_ _ l (by rw [htake]; omega)
      intro l' hl'
      refine consList_agree_below (n := 0) (fun _ h => absurd h (Nat.not_lt_zero _)) _ l' ?_
      rw [List.length_map, hg.len]; omega

/-- **The per-position facts at a finitary container without
transports** (the owed `pos`): a container-recursive position is
recursive on both sides with the same readings (`pos_recJ`), an
ordinary one on the container's side is ordinary or into a block
member on the copy's (no transport, `hnoT`) — the first two arms of
`r2_step`'s `hpos`; the third arm is never needed. -/
theorem pos_noTransport (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA)
    (hfin : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hnoT : ∀ i, i < cA.2 → i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) → d.tgtsR (auxOfsOf st p.k cd j J) i < p.k)
    {fs : List V} (hlen : fs.length = cA.2) :
    ∀ i, i < cA.2 →
    (¬ replaced (IndRepData.psiUseIh (cd j).dJ J)
        (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
          (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J) i ∧
      d.invUseIh p.k (auxOfsOf st p.k cd j J) i = false) ∨
    (IndRepData.psiUseIh (cd j).dJ J i = true ∧
      d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀) J i = none ∧
      d.invUseIh p.k (auxOfsOf st p.k cd j J) i = true ∧
      i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) ∧ i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) ∧
      ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [] ∧ (d.tssR (auxOfsOf st p.k cd j J) ψ).getD i [] = [] ∧
      d.tgtsR (auxOfsOf st p.k cd j J) i = p.k + (cd j).base + (cd j).dJ.tgts J i ∧
      ((d.eissR (auxOfsOf st p.k cd j J) ψ).getD i []).map
          (interp V (consList ((d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
            (consList (paramVals d.nP ρ) ρ) j J fs).take i) ρ))
        = (((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList (fs.take i)
            (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))) ∨
    (d.mixedValsAt mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) order s tbl₀ ρ j J fs).getD i pt
      = fs.getD i pt := by
  intro i hi
  by_cases hA : i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J)
  · exact Or.inr (Or.inl (R.pos_recJ tbl₀ hρ hj hJ hlen hi hA (hfin i hA)))
  · -- ordinary on the container's side: ordinary or into a block member
    -- on the copy's (no transport)
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

/-- **ψ's values fit the copy constructor's telescope** (the owed
`fitCopy`): the transported domains at the group's setup
(`psiVals_fit_of` at the final table) are the copy's own field
telescope lifted over the pin's readings (`psiVals_fit_copy`), the
parameters fit the copy's parameter domains (`spineFit_of_paramsIff`). -/
theorem fitCopy_of_run (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) {fs : List V}
    (hfs : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (((cd j).dJ.Fss (cd j).ψ').getD J []) fs) :
    SpineFit ρ ((d.dsF (auxOfsOf st p.k cd j J) ψ).map (·.2.2))
      (paramVals d.nP ρ ++
        d.psiValsAt mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ (consList (paramVals d.nP ρ) ρ) j J fs) := by
  obtain ⟨lps, S⟩ := R.psiSetup_final (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) (paramBvarsAt_length _ _) hρ
    tbl₀ hj
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  obtain ⟨cA', hget, hf⟩ := hg.ctors J cA hJ
  obtain ⟨hpinsA, hFFA, hLSA, hpIffMA⟩ := auxFacts_of_blockReps R.reps ψ
  have hDJ := (hrepJ.ctors J cA hJ).2.2
  have hJA : J < (cd j).dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  have hmemJ := S.hmems J hJA
  have hfs' : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      ((((cd j).dJ.dsF J (cd j).ψ').drop (cd j).dJ.nP).map (·.2.2)) fs := by
    rw [← (cd j).dJ.Fss_getD (cd j).ψ' hJ]; exact hfs
  -- ψ's values at the transported domains
  have hvals := IndRepData.PsiSetup.psiVals_fit_of (cd j).dJ S hJ hfs'
  -- the fold terms are the final table's entries
  have hmap : ((ConLeche.recIdxOf ((cd j).dJ.ksR J)).map fun i =>
      lamTower ((cd j).dJ.bb (cd j).ψ') (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList ((paramBvarsAt d.nP d.nP).map (interp V ρ)) ρ))) (consList ((paramBvarsAt d.nP d.nP).map (interp V ρ)) ρ)))
        (((cd j).dJ.tssR J (cd j).ψ').getD i []) fun σ'' =>
        ((((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V σ'') ++
          [(Semantics.frameIdx ((((cd j).dJ.tssR J (cd j).ψ').getD i []).length) σ'').foldl
            SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
          (interp V (consList ((paramBvarsAt d.nP d.nP).map (interp V ρ)) ρ)
            ((cd j).dJ.foldTermAV mpAux.base2 (cd j).ψ' (cd j).DsA (d.psiL mpAux.base2 ψ p.k (cd j).base)
              (d.psiPinsT (cd j).dJ.nP)
              ((cd j).dJ.psiBodyAV (d.psiHead mpAux.base2 ψ (cd j).dJ.nP (auxOfsOf st p.k cd j))
                (IndRepData.psiUseIh (cd j).dJ)
                (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
                  (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀))) ((cd j).dJ.tgtsR J i))))
      = ((ConLeche.recIdxOf ((cd j).dJ.ksR J)).map fun i =>
      lamTower ((cd j).dJ.bb (cd j).ψ') (consList (fs.take i) (consList ((cd j).DsA.map (interp V (consList ((paramBvarsAt d.nP d.nP).map (interp V ρ)) ρ))) (consList ((paramBvarsAt d.nP d.nP).map (interp V ρ)) ρ)))
        (((cd j).dJ.tssR J (cd j).ψ').getD i []) fun σ'' =>
        ((((cd j).dJ.eissR J (cd j).ψ').getD i []).map (interp V σ'') ++
          [(Semantics.frameIdx ((((cd j).dJ.tssR J (cd j).ψ').getD i []).length) σ'').foldl
            SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
          (interp V (consList ((paramBvarsAt d.nP d.nP).map (interp V ρ)) ρ) (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀
            ((cd j).base + (cd j).dJ.tgtsR J i)))) := by
    apply List.map_congr_left
    intro i _
    rw [R.final_group tbl₀ hj (by rw [(S.hview J).2.1]; exact S.htgts J i)]
  rw [hmap] at hvals
  -- the transported domains are the copy's own telescope
  have htgtLt : ∀ Jc cAJ, (cd j).dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j Jc)) → i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF Jc) →
      p.k ≤ d.tgtsR (auxOfsOf st p.k cd j Jc) i → d.tgtsR (auxOfsOf st p.k cd j Jc) i - p.k < st.pins.length := by
    intro Jc cAJ hJc i hi hA hT hk
    obtain ⟨cAa, -, hf'⟩ := hg.ctors Jc cAJ hJc
    have := hf'.tgts i
    rw [R.dk] at this
    omega
  have hcopy := d.psiVals_fit_copy mpAux (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) (paramBvarsAt_length _ _) hρ
    hg.len hg.lev (auxOfsOf st p.k cd j) cd (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀)
    hf.nF hf.read hf.ctor hf.pIff hf.view hf.tgts hFFA hLSA
    ⟨(hg.view J).2.1, (hg.view J).2.2.1, (hg.view J).2.2.2⟩ (S.htgts J)
    (fun i dd hd => hDJ.tssBits (cd j).ψ' i dd hd) hg.grp
    (fun i hi hA hT hk => (R.groupFacts (htgtLt J cA hJ i hi hA hT hk)).ok
      (R.pins _ (htgtLt J cA hJ i hi hA hT hk)).1.2.1)
    _ hvals
  -- the parameters
  have hfitP : SpineFit ρ (((d.dsF (auxOfsOf st p.k cd j J) ψ).take d.nP).map (·.2.2)) (paramVals d.nP ρ) :=
    spineFit_of_paramsIff (paramVals_length _ _)
      (by rw [List.length_map, List.length_take, hf.ctor.2.2.len ψ]; omega) hρ hf.pIff
  rw [← List.take_append_drop d.nP (d.dsF (auxOfsOf st p.k cd j J) ψ), List.map_append]
  exact hfitP.append hcopy

/-- **A container constructor's position is below its copy's
constructor count** (task #279 M-C′ step 5): at pin `j`, constructor
`J` of member `mems J`, the group-mate's pin `base + mems J` names the
member (`ContainerCtorsAt.fwd` at that pin lists `J` at position
`posIn`), and the copy's type has the member's constructor count
(`CopyCtorsStored`). -/
theorem posIn_lt_ctors {j : Nat} (hj : j < st.pins.length) {J : Nat} {cA : ConstantVal × Nat}
    (hJ : (cd j).dJ.ctorsA[J]? = some cA) :
    ∃ tyA : AuxType, st.types[p.k + ((cd j).base + (cd j).dJ.mems J)]? = some tyA ∧
      posIn (cd j).dJ J < tyA.ctors.length := by
  have hg := R.groupFacts hj
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  have hJlt : J < (cd j).dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  have hmemJ : (cd j).dJ.mems J < (cd j).dJ.k := by
    have := (hrepJ.memsReal J (by unfold IndRepData.nAll; rw [hg.ctorsC]; simpa using hJlt)).mpr hJlt
    rw [hg.kReal] at this
    exact this
  have hj₂ := R.mate_lt hj hmemJ
  have hc₂ := (R.pins j hj).2 _ hmemJ
  obtain ⟨⟨-, -, q₂, I₂, ci₂, J₂, lvls₂, Ds₂, cvTJ₂, capsJ₂, -, -, hJ₂, -, -, -, -, -, -, -, -, -, -,
    hcat₂, hcst₂, -⟩, -⟩ := R.pins _ hj₂
  rw [hc₂] at hJ₂ hcat₂
  obtain ⟨tyA, htyA, -, hlenA, -⟩ := hcst₂
  obtain ⟨J', c, hJ', hc, -⟩ := hcat₂.fwd J cA hJ
  have hJ₂' : ci₂.members[(cd j).dJ.mems J]? = some J₂ := hJ₂
  obtain rfl : J' = J₂ := Option.some.inj (hJ'.symm.trans hJ₂')
  refine ⟨tyA, htyA, ?_⟩
  rw [hlenA]
  exact (List.getElem?_eq_some_iff.mp hc).1

/-- **The copy constructor's index recovers the pin's data and the
container constructor** (task #279 M-C′ step 5, `R2Owed.headφ`'s
recipe): two representatives of one auxiliary constructor index have
the same container datum, assignment, readings and constructor —
`ctorBase` is injective on (type, position) (`ctorBase_inj`), so both
name the pin `base + mems` and the position; the group clause at both
pins identifies the group-mate's data with each pin's own; `posIn` is
injective within a member. -/
theorem auxOfsOf_inj {j : Nat} (hj : j < st.pins.length) {J : Nat} {cA : ConstantVal × Nat}
    (hJ : (cd j).dJ.ctorsA[J]? = some cA) {j' : Nat} (hj' : j' < st.pins.length) {Jc : Nat}
    {cAJ : ConstantVal × Nat} (hJc : (cd j').dJ.ctorsA[Jc]? = some cAJ)
    (hE : auxOfsOf st p.k cd j' Jc = auxOfsOf st p.k cd j J) :
    (cd j').dJ = (cd j).dJ ∧ (cd j').ψ' = (cd j).ψ' ∧ (cd j').DsA = (cd j).DsA ∧ Jc = J ∧ cAJ = cA := by
  obtain ⟨tyA, hty, hlt⟩ := R.posIn_lt_ctors hj hJ
  obtain ⟨tyA', hty', hlt'⟩ := R.posIn_lt_ctors hj' hJc
  unfold auxOfsOf at hE
  obtain ⟨h1, h2⟩ := ConLeche.ctorBase_inj hty' hty hlt' hlt hE
  have hpin : (cd j').base + (cd j').dJ.mems Jc = (cd j).base + (cd j).dJ.mems J := by omega
  -- the members are real
  have hmem : ∀ {j : Nat}, j < st.pins.length → ∀ {J : Nat} {cA : ConstantVal × Nat},
      (cd j).dJ.ctorsA[J]? = some cA → (cd j).dJ.mems J < (cd j).dJ.k := by
    intro j hj J cA hJ
    have hg := R.groupFacts hj
    obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
    have hJlt : J < (cd j).dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    have := (hrepJ.memsReal J (by unfold IndRepData.nAll; rw [hg.ctorsC]; simpa using hJlt)).mpr hJlt
    rw [hg.kReal] at this
    exact this
  have hc := (R.pins j hj).2 _ (hmem hj hJ)
  have hc' := (R.pins j' hj').2 _ (hmem hj' hJc)
  rw [hpin, hc] at hc'
  obtain ⟨hdJ, hmm, hψ, hDsA, -⟩ := CopyData.mk.inj hc'.symm
  rw [hdJ] at hmm h2 hJc
  have hJcJ : Jc = J := posIn_inj _ hmm h2
  subst hJcJ
  exact ⟨hdJ, hψ, hDsA, rfl, Option.some.inj (hJc.symm.trans hJ)⟩

/-- **ψ⁻¹'s head at a copy constructor is THIS container constructor
at THIS pin's readings** (task #279 M-C′ step 5 — `R2Owed.headφ`
DERIVED): `invHead`'s representative has the pin's data and the
constructor (`auxOfsOf_inj`); the constructor's value is closed and
the readings are bounded at the parameters, so both read alike at the
frame and at the pushed frame. -/
theorem headφ_of_run {ρ : Nat → V} {j : Nat} (hj : j < st.pins.length) {J : Nat}
    {cA : ConstantVal × Nat} (hJ : (cd j).dJ.ctorsA[J]? = some cA) :
    R2Owed (p := p) (st := st) mpAux d ψ cd ρ j J cA := by
  refine ⟨?_⟩
  obtain ⟨j', Jc, cAJ, hj', hJc, hE, hhead⟩ := d.invHead_copy mpAux.base2 ψ st.pins.length cd
    (auxOfsOf st p.k cd) ⟨(j, J, cA), hj, hJ, rfl⟩
  obtain ⟨-, hψ, hDsA, hJcJ, hcA⟩ := R.auxOfsOf_inj hj hJ hj' hJc hE
  subst hJcJ hcA
  rw [hhead, hψ, hDsA, interp_mkAppN_map,
    interp_closed (V := V) (mpAux.base2.cval_closedL _ _) ρ (consList (paramVals d.nP ρ) ρ)]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact interp_congr_below V q d.nP _ _ (R.DsA_below hj q hq) (fun i hi => (push_agree ρ ρ i hi).symm)

set_option maxHeartbeats 3200000 in
/-- **R2 at the run, per group, modulo the owed facts** (task #279 M-C′
step 4, DESIGN §M.35): at pin `j`'s group, at any parameter frame `ρ`
(the parameter variables as the parameters), R2 holds of ψ's final
table (at the group-mates) and ψ⁻¹'s fold terms (at the copies) — for
a FINITARY container without transports (`hfin`, `hnoT`; the
container's and the block's elimination bits nonzero), given the owed
fact at every constructor (`R2Owed`: ψ⁻¹'s head). -/
theorem r2Grp_of_owed (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    (hbJ : (cd j).dJ.bb (cd j).ψ' ≠ 0) (hbA : d.bb ψ ≠ 0)
    (hfin : ∀ J, ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    -- no transports: a field the container sees as ordinary and the
    -- copy as recursive targets a block member
    (hnoT : ∀ J cA, (cd j).dJ.ctorsA[J]? = some cA → ∀ i, i < cA.2 →
      i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) → i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) →
      d.tgtsR (auxOfsOf st p.k cd j J) i < p.k)
    (howed : ∀ J cA, (cd j).dJ.ctorsA[J]? = some cA → R2Owed (p := p) (st := st) mpAux d ψ cd ρ j J cA) :
    R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
      (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
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
  -- the parameter variables read to the parameter values
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
  -- the restricted family is in the family space
  have hX : r2Fam (cd j).dJ (cd j).ψ' ρ (consList (paramVals d.nP ρ) ρ)
      (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t))
      ∈ˢ famSpace ((cd j).dJ.w (cd j).ψ') ((cd j).dJ.idx (cd j).ψ'
        (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))) :=
    graph_mem_famSpace fun i hi => univ_sep_mem (famSpace_app (lfpFamSet_mem _ _ _) hi)
  obtain ⟨cvT', cvR', mI', rP', rules', hrep'⟩ := hrepT _ hmemJ
  have hfields := hrep'.chainFit_fields (cd j).ψ' hsat hX htup hJlt ⟨hlen, hchainFit, hall⟩
  -- the fields fit the real domains, with the induction hypotheses
  have hfacts := R.ctor_facts tbl₀ hρ hj hJ
  obtain ⟨hfit, hIH⟩ := fieldsFit_of_chainFit (IndRepData.RepsAt.of_single hrepT) hsat rfl hDsFit hDsLen hJ hC
    htgts (hfin J)
    (fun i hi => hfacts.2 i (hfin J i hi).1) hlen hfields
  have hO := howed J cA hJ
  have hvsN : fs.length = cA.2 := by
    rw [hlen, (cd j).dJ.Fss_getD (cd j).ψ' hJ, List.length_map, List.length_drop, hlenD]; omega
  -- the entries' fits at the fields
  have hEntryFit : ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
        ((cd j).dJ.IdsM ((cd j).dJ.tgts J i) (cd j).ψ')
        ((((cd j).dJ.eissF J (cd j).ψ').getD i []).map (interp V (consList (fs.take i)
          (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))))) := by
    intro i hi
    have hilt : i < cA.2 := by
      have := (mem_recIdxOf.mp hi).1
      rw [hC.2.2.ksLen] at this
      exact this
    have htake : (fs.take i).length = i := by rw [List.length_take]; omega
    have hpre : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
        (consList (paramVals d.nP ρ) ρ))
        (((((cd j).dJ.dsF J (cd j).ψ').drop (cd j).dJ.nP).map (·.2.2)).take i) (fs.take i) := by
      rw [← (cd j).dJ.Fss_getD (cd j).ψ' hJ]
      exact spineFit_take' hfit (by rw [← hlen, hvsN]; omega)
    exact (hfacts.2 i (hfin J i hi).1 (fs.take i) htake hpre).2
  -- ψ's ι at values
  have hιΨ := fun (vs : List V)
      (hfitv : SpineFit (consList (paramVals d.nP ρ) ρ) (((cd j).dJ.dsF J (cd j).ψ').map (·.2.2))
        ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) ++ vs)) =>
    R.psi_iota tbl₀ hρ rfl hj hbJ (fun _ => rfl) hJ
      (by have := hfitv.length_eq
          rw [List.length_append, hDsLen, List.length_map, hlenD] at this; omega)
      hfitv
  -- ψ⁻¹'s ι at values
  have hιΦ := fun (vs' : List V)
      (hfitv : SpineFit ρ ((d.dsF (auxOfsOf st p.k cd j J) ψ).map (·.2.2)) (paramVals d.nP ρ ++ vs')) =>
    R.inv_iota hk hρ hbA hget
      (by have := hfitv.length_eq
          rw [List.length_append, paramVals_length, List.length_map, hf.ctor.2.2.len ψ] at this; omega)
      hfitv
  exact r2_step mpAux.base2 (d := d) (ψ := ψ) (cA' := cA') hrepT hsat rfl hDsFit hDsLen hJ hlenD
    (hrepJ.paramsIff J cA hJ (cd j).ψ') hmemJ htgts (hg.view J) hf.read.mem (fun t _ => rfl) hfit hIH
    (hfacts.1 fs hfit).1 (hfacts.1 fs hfit).2 hEntryFit hall hιΨ hιΦ rfl rfl
    (d.psiHead_interp mpAux.base2 ψ (auxOfsOf st p.k cd j) hget hDsLen) hO.headφ
    (R.fitCopy_of_run tbl₀ hρ hj hJ hfit)
    (R.es_of_record tbl₀ hρ hj hJ hvsN) (R.pos_noTransport tbl₀ hρ hj hJ (hfin J) (hnoT J cA hJ) hvsN)

/-- **R2 AT THE RUN, per group** (task #279 M-C′ step 5): `r2Grp_of_owed`
with the owed fact derived (`headφ_of_run`) — for a FINITARY container
without transports, both elimination bits nonzero. -/
theorem r2Grp (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    (hbJ : (cd j).dJ.bb (cd j).ψ' ≠ 0) (hbA : d.bb ψ ≠ 0)
    (hfin : ∀ J, ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hnoT : ∀ J cA, (cd j).dJ.ctorsA[J]? = some cA → ∀ i, i < cA.2 →
      i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) → i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) →
      d.tgtsR (auxOfsOf st p.k cd j J) i < p.k) :
    R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
      (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) :=
  R.r2Grp_of_owed tbl₀ hρ hj hbJ hbA hfin hnoT fun _ _ hJ => R.headφ_of_run hj hJ

end NestedRunFacts

end ConLeche.Model
