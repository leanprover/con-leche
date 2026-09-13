module

public import ConLeche.Model.Inductives.RoundTripRunR1
public section

/-!
# The `Prop` arm of the round trips, and the folds typed at values (task #279 M-C′, DESIGN §M.37)

`RoundTripRun.lean`/`RoundTripRunR1.lean` prove R2 and R1 at the run
for groups whose elimination bits are NONZERO (`hbJ`, `hbA`): the ι
laws at values (`fold_iota_vals`) are stated at a nonzero bit.  At a
`Prop`-valued group (`bb = 0`, equivalently the block's sort evaluates
to `0` — the copies' sorts are the containers', `CopyIdxRead.sort`)
every carrier is a member of `univ 0`, so it has at most the point as
element, and the round trips hold by TYPING alone: both folds land in
the carriers.  This module provides

* **`IndRep.eq_pt_of_mem`** — an element of a member's carrier at a
  zero sort is the point (`leaf`, `famSpace_app`, `mem_univ_zero`);
* **`invFold_mem`** — ψ⁻¹'s fold term at a copy, applied to index
  values and an element of the copy's carrier, lands in the container
  member's carrier at the pin's readings (`InvSetup.fold_mem_vals` at
  the run's setup, the target read through `invChoice_group`);
* **`psiFinal_mem`** — ψ's final table's entry at a group-mate, applied
  to index values and an element of the container's carrier at the
  pin, lands in the copy's carrier at the block's parameters
  (`PsiSetup.fold_mem_vals` at the group's setup at the final table);
* **`bb_iff`** — the block's elimination bit is zero iff the group's
  container's is;
* **`r2Grp_prop`/`r1At_prop`** — the round trips at a zero bit;
* **`r2Grp_all`/`r1At_all`** — the round trips with the bit
  restrictions DROPPED (the nonzero arm `r2Grp`/`r1At_of_run`, the
  zero arm above).  The remaining restrictions are the finitary and
  transport-free ones.

The two typing lemmas are also what `coherence` asks of ψ⁻¹ (`hΦ`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A carrier at a zero sort is the point -/

namespace IndRep

/-- **An element of a member's carrier at a zero sort is the point**:
the carrier is the least fixed point's fibre (`leaf`), a member of
`univ 0` (`famSpace_app`), whose only possible element is `pt`
(`mem_univ_zero`). -/
theorem eq_pt_of_mem {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : IndRepData V} {mm : Nat}
    (hrep : IndRep m T cvT cvR mI rP rules d mm) (ψ : Name → Nat) (hw : d.w ψ = 0) {ρ : Nat → V}
    {as is : List V} (has : SpineFit ρ (d.params ψ) as) (his : SpineFit (consList as ρ) (d.IdsM mm ψ) is)
    {x : V} (hx : x ∈ˢ (as ++ is).foldl SetTheory.app (interp V ρ (m.acval T ψ))) : x = pt := by
  rw [hrep.leaf ψ ρ as is has his] at hx
  have hsat : Sat V (d.params ψ).reverse (consList as ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) has
    rwa [List.append_nil] at h
  have htup : d.tup ψ mm is ∈ˢ d.idx ψ (consList as ρ) := hrep.tupMem ψ _ hsat is his
  have h := famSpace_app (lfpFamSet_mem (d.w ψ) (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) htup
  rw [hw] at h hx
  exact mem_univ_zero h hx

end IndRep

namespace NestedRunFacts

variable {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState}
  {b : MutualBlock} {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)}
  {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
  {lpsT : List Name} {order : List Nat} {s : Level}
  (R : NestedRunFacts F env p st b params pbs mpAux d ψ cd lpsT order s)

include R

/-! ## The bits -/

/-- The block's elimination bit is zero iff its sort evaluates to zero. -/
theorem bbA_iff : d.bb ψ = 0 ↔ d.w ψ = 0 := by
  unfold IndRepData.bb
  rw [pwBit_zeronessOf, R.lev]

/-- A container's elimination bit is zero iff its sort evaluates to zero. -/
theorem bbJ_iff {j : Nat} (hj : j < st.pins.length) :
    (cd j).dJ.bb (cd j).ψ' = 0 ↔ (cd j).dJ.w (cd j).ψ' = 0 := by
  unfold IndRepData.bb
  rw [pwBit_zeronessOf, (R.groupFacts hj).lev]

/-- The container's sort at the pin's assignment evaluates as the
block's (`CopyIdxRead.sort` at any member of the group). -/
theorem wJ_eq {j : Nat} (hj : j < st.pins.length) : (cd j).dJ.w (cd j).ψ' = d.w ψ := by
  have hg := R.groupFacts hj
  obtain ⟨-, -, -, -, -, -, t₀, ht₀, -⟩ := hg.rep
  exact (hg.grp t₀ ht₀).idx.sort

/-- **The block's bit is zero iff the group's container's is.** -/
theorem bb_iff {j : Nat} (hj : j < st.pins.length) :
    d.bb ψ = 0 ↔ (cd j).dJ.bb (cd j).ψ' = 0 := by
  rw [R.bbA_iff, R.bbJ_iff hj, R.wJ_eq hj]

/-! ## The folds, typed at values -/

/-- **ψ⁻¹'s fold at a copy is typed at values**: at the copy
`p.k + base + t` of pin `j`'s group member `t`, index values fitting
the copy's telescope at the block's parameter frame and an element of
the copy's carrier, the fold term applied lands in the container
member's carrier at the pin's readings (`InvSetup.fold_mem_vals` at
the run's setup; the target's leaf and pins by `invChoice_group`). -/
theorem invFold_mem {ρ : Nat → V} (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
    {j : Nat} (hj : j < st.pins.length) {t : Nat} (ht : t < (cd j).dJ.k) {is : List V}
    (his : SpineFit (consList (paramVals d.nP ρ) ρ) (d.IdsM (p.k + (cd j).base + t) ψ) is) {a : V}
    (ha : a ∈ˢ (paramVals d.nP ρ ++ is).foldl SetTheory.app
      (interp V ρ (mpAux.base2.acval (d.memberName (p.k + (cd j).base + t)) ψ))) :
    foldApp ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) is a
      ∈ˢ ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) ++ is).foldl SetTheory.app
          (interp V (consList (paramVals d.nP ρ) ρ) (mpAux.base2.acval ((cd j).dJ.memberName t) (cd j).ψ')) := by
  obtain ⟨lpsI, lpsT', S⟩ := R.invSetup_at hρ
  have hg := R.groupFacts hj
  have hlt : p.k + (cd j).base + t < d.k := hg.kA t ht
  obtain ⟨hpinsA, -, -, -⟩ := auxFacts_of_blockReps R.reps ψ
  have hσ₀ : consList ((paramBvarsAt d.nP d.nP).map (interp V ρ)) ρ = consList (paramVals d.nP ρ) ρ := rfl
  have hisLen : is.length = d.nIdxs.getD (p.k + (cd j).base + t) 0 := by
    rw [his.length_eq]
    unfold IndRepData.IdsM
    rw [List.length_map, ← d.ipss_getD ψ hlt]
    exact S.hipsLen _ hlt
  -- the motive binder's spine: the indices and the major
  have hfitM : SpineFit (consList (paramVals d.nP ρ) ρ)
      ((d.motDataAV mpAux.base2 ψ (p.k + (cd j).base + t)).map (·.2.2)) (is ++ [a]) := by
    have hsplit : (d.motDataAV mpAux.base2 ψ (p.k + (cd j).base + t)).map (·.2.2)
        = (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (p.k + (cd j).base + t) [])).map (·.2.2) ++
          [famAppAV ((d.Ls mpAux.base2 ψ).getD (p.k + (cd j).base + t) default)
            (d.pinsOf ψ (p.k + (cd j).base + t)) d.nP (d.nP + d.nIdxs.getD (p.k + (cd j).base + t) 0)
            (d.nIdxs.getD (p.k + (cd j).base + t) 0)] := by
      simp [IndRepData.motDataAV]
    rw [hsplit]
    refine SpineFit.append ?_ ⟨?_, trivial⟩
    · rw [rebit_map_dom, d.ipss_getD ψ hlt]
      exact his
    · rw [d.Ls_getD_eq mpAux.base2 ψ hlt, interp_famAppAV_pins (mpAux.base2.cval_closedL _ _) _ _ hisLen,
        hpinsA, interp_paramBvarsAt_self (paramVals_length _ _),
        interp_closed (V := V) (mpAux.base2.cval_closedL _ _) _ ρ]
      exact ha
  have hmem := IndRepData.InvSetup.fold_mem_vals (d.withSort s) S hlt hfitM
  rw [hσ₀] at hmem
  obtain ⟨hL, hpins⟩ := invChoice_group R.pins hj ht
  have hmem' : foldApp ρ (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s
        (p.k + (cd j).base + t)) is a
      ∈ˢ interp V (consList is (consList (paramVals d.nP ρ) ρ))
          (famAppAV (d.invL mpAux.base2 ψ p.k cd (p.k + (cd j).base + t))
            (d.invPinsT p.k cd (p.k + (cd j).base + t)) d.nP
            (d.nP + d.nIdxs.getD (p.k + (cd j).base + t) 0) (d.nIdxs.getD (p.k + (cd j).base + t) 0)) := hmem
  rw [hL, hpins, interp_famAppAV_pins (mpAux.base2.cval_closedL _ _) _ _ hisLen] at hmem'
  exact hmem'

/-- **ψ's final table's entry at a group-mate is typed at values**: at
pin `j`'s group member `t`, index values fitting the container's
telescope at the pin's frame and an element of the container's carrier
there, the entry applied lands in the copy `p.k + base + t`'s carrier
at the block's parameters (`PsiSetup.fold_mem_vals` at the group's
setup at the final table, the entry the group's fold term by
`final_group`). -/
theorem psiFinal_mem (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    {t : Nat} (ht : t < (cd j).dJ.k) {is : List V}
    (his : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      ((cd j).dJ.IdsM t (cd j).ψ') is) {x : V}
    (hx : x ∈ˢ ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)) ++ is).foldl SetTheory.app
      (interp V (consList (paramVals d.nP ρ) ρ) (mpAux.base2.acval ((cd j).dJ.memberName t) (cd j).ψ'))) :
    foldApp (consList (paramVals d.nP ρ) ρ)
        (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t)) is x
      ∈ˢ (paramVals d.nP ρ ++ is).foldl SetTheory.app
          (interp V ρ (mpAux.base2.acval (d.memberName (p.k + (cd j).base + t)) ψ)) := by
  obtain ⟨lps, S⟩ := R.psiSetup_final (ρ₀ := ρ) (psA := paramBvarsAt d.nP d.nP) (paramBvarsAt_length _ _) hρ
    tbl₀ hj
  have hg := R.groupFacts hj
  have hσ₀ : consList ((paramBvarsAt d.nP d.nP).map (interp V ρ)) ρ = consList (paramVals d.nP ρ) ρ := rfl
  rw [hσ₀] at S
  have hDsLen : ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))).length = (cd j).dJ.nP := by
    rw [List.length_map, hg.len]
  have hisLen : is.length = (cd j).dJ.nIdxs.getD t 0 := by
    rw [his.length_eq]
    unfold IndRepData.IdsM
    rw [List.length_map, ← (cd j).dJ.ipss_getD (cd j).ψ' ht]
    exact S.hipsLen _ ht
  -- the motive binder's spine: the indices and the major
  have hfitM : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      (((cd j).dJ.motDataAV mpAux.base2 (cd j).ψ' t).map (·.2.2)) (is ++ [x]) := by
    have hsplit : ((cd j).dJ.motDataAV mpAux.base2 (cd j).ψ' t).map (·.2.2)
        = (rebit (pwBit (cd j).ψ' ConLeche.PropWhen.never) (((cd j).dJ.ipss (cd j).ψ').getD t [])).map (·.2.2) ++
          [famAppAV (((cd j).dJ.Ls mpAux.base2 (cd j).ψ').getD t default)
            ((cd j).dJ.pinsOf (cd j).ψ' t) (cd j).dJ.nP ((cd j).dJ.nP + (cd j).dJ.nIdxs.getD t 0)
            ((cd j).dJ.nIdxs.getD t 0)] := by
      simp [IndRepData.motDataAV]
    rw [hsplit]
    refine SpineFit.append ?_ ⟨?_, trivial⟩
    · rw [rebit_map_dom, (cd j).dJ.ipss_getD (cd j).ψ' ht]
      exact his
    · rw [(cd j).dJ.Ls_getD_eq mpAux.base2 (cd j).ψ' ht,
        interp_famAppAV_pins (mpAux.base2.cval_closedL _ _) _ _ hisLen]
      unfold IndRepData.pinsOf
      rw [hg.pinsAV, interp_paramBvarsAt_self hDsLen,
        interp_closed (V := V) (mpAux.base2.cval_closedL _ _) _ (consList (paramVals d.nP ρ) ρ)]
      exact hx
  have hmem := IndRepData.PsiSetup.fold_mem_vals (cd j).dJ S ht hfitM
  have hmem' : foldApp (consList (paramVals d.nP ρ) ρ)
        ((cd j).dJ.foldTermAV mpAux.base2 (cd j).ψ' (cd j).DsA (d.psiL mpAux.base2 ψ p.k (cd j).base)
          (d.psiPinsT (cd j).dJ.nP)
          ((cd j).dJ.psiBodyAV (d.psiHead mpAux.base2 ψ (cd j).dJ.nP (auxOfsOf st p.k cd j))
            (IndRepData.psiUseIh (cd j).dJ)
            (d.psiVia (cd j).dJ ψ p.k (cd j).dJ.nP (auxOfsOf st p.k cd j) ((cd j).dJ.bb (cd j).ψ')
              (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀))) t) is x
      ∈ˢ interp V (consList is (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ)))
            (consList (paramVals d.nP ρ) ρ)))
          (famAppAV (d.psiL mpAux.base2 ψ p.k (cd j).base t) (d.psiPinsT (cd j).dJ.nP t) (cd j).dJ.nP
            ((cd j).dJ.nP + (cd j).dJ.nIdxs.getD t 0) ((cd j).dJ.nIdxs.getD t 0)) := hmem
  rw [← R.final_group tbl₀ hj ht] at hmem'
  unfold IndRepData.psiPinsT IndRepData.psiL at hmem'
  rw [interp_famAppAV_aux (mpAux.base2.cval_closedL _ _) hDsLen hisLen,
    range_reverse_map_consList' (paramVals_length _ _),
    interp_closed (V := V) (mpAux.base2.cval_closedL _ _) _ ρ] at hmem'
  exact hmem'

/-! ## The round trips at a zero bit -/

/-- **R2 at a `Prop`-valued group** (task #279 M-C′ step 6, the `Prop`
arm): at pin `j`'s group, when the block's bit is zero, every element
of a container member's carrier at the pin is the point, and so is
the round trip's result (typed into the same carrier by `psiFinal_mem`
then `invFold_mem`). -/
theorem r2Grp_prop (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    (hb : d.bb ψ = 0) :
    R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
      (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  have hg := R.groupFacts hj
  have hpf := (R.pins j hj).1.1
  have hwJ : (cd j).dJ.w (cd j).ψ' = 0 := by rw [R.wJ_eq hj, ← R.bbA_iff]; exact hb
  have hDsFit := R.pinFit hj hρ
  have hsat₀ : Sat V (d.params ψ).reverse (consList (paramVals d.nP ρ) ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hρ
    rwa [List.append_nil] at h
  intro t ht
  obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := hpf.repAll t ht
  show ∀ (is : List V) (x : V), SpineFit _ ((cd j).dJ.IdsM t (cd j).ψ') is → x ∈ˢ _ → _
  intro is x his hx
  have hps : (paramBvarsAt d.nP d.nP).map (interp V ρ) = paramVals d.nP ρ := rfl
  simp only [hps] at his hx ⊢
  have hx' : x = pt := hrep.eq_pt_of_mem (cd j).ψ' hwJ hDsFit his hx
  have hy := R.psiFinal_mem tbl₀ hρ hj ht his hx
  have his' : SpineFit (consList (paramVals d.nP ρ) ρ) (d.IdsM (p.k + (cd j).base + t) ψ) is := by
    have h := ((hg.grp t ht).idx.idxIff _ hsat₀ is).mpr his
    rwa [← Nat.add_assoc] at h
  have hz := R.invFold_mem hρ hj ht his' hy
  have hz' := hrep.eq_pt_of_mem (cd j).ψ' hwJ hDsFit his hz
  rw [hz', hx']

/-- **R1 at a `Prop`-valued block** (the `Prop` arm): at the copy
`p.k + base + t` of pin `j`'s group member `t`, every element of the
copy's carrier is the point, and so is the round trip's result
(`invFold_mem` then `psiFinal_mem`). -/
theorem r1At_prop (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) (hb : d.bb ψ = 0)
    {j : Nat} (hj : j < st.pins.length) {t : Nat} (ht : t < (cd j).dJ.k) :
    d.R1At mpAux.base2 ψ ρ (paramBvarsAt d.nP d.nP) (p.k + (cd j).base + t)
      (d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  have hg := R.groupFacts hj
  have hwA : d.w ψ = 0 := R.bbA_iff.mp hb
  have hlt : p.k + (cd j).base + t < d.k := hg.kA t ht
  obtain ⟨s', cvT', cvR', mI', rP', rules', hs', hrep'⟩ := R.repsAt_of_reps _ hlt
  have hw' : (d.withSort s').w ψ = 0 := by rw [d.withSort_w, hs' ψ]; exact hwA
  have hsat₀ : Sat V (d.params ψ).reverse (consList (paramVals d.nP ρ) ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hρ
    rwa [List.append_nil] at h
  intro is a his ha
  have hps : (paramBvarsAt d.nP d.nP).map (interp V ρ) = paramVals d.nP ρ := rfl
  simp only [hps] at his ha ⊢
  have ha' : a = pt := hrep'.eq_pt_of_mem ψ hw' hρ his ha
  have hz := R.invFold_mem hρ hj ht his ha
  have hisJ : SpineFit (consList ((cd j).DsA.map (interp V (consList (paramVals d.nP ρ) ρ))) (consList (paramVals d.nP ρ) ρ))
      ((cd j).dJ.IdsM t (cd j).ψ') is := by
    exact ((hg.grp t ht).idx.idxIff _ hsat₀ is).mp (by rw [← Nat.add_assoc]; exact his)
  have hy := R.psiFinal_mem tbl₀ hρ hj ht hisJ hz
  have hy' := hrep'.eq_pt_of_mem ψ hw' hρ his hy
  rw [hy', ha']

/-! ## The bit restrictions dropped -/

/-- **R2 at the run, per group, at ANY elimination bit**: the nonzero
arm (`r2Grp`) or the `Prop` arm (`r2Grp_prop`).  Remaining
restrictions: the container finitary (`hfin`) and the group without
transports (`hnoT`). -/
theorem r2Grp_all (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ)) {j : Nat} (hj : j < st.pins.length)
    (hfin : ∀ J, ∀ i, i ∈ ConLeche.recIdxOf ((cd j).dJ.ksF J) →
      ((cd j).dJ.ksF J).getD i .ordinary = .recursive ∧ ((cd j).dJ.tssF J (cd j).ψ').getD i [] = [])
    (hnoT : ∀ J cA, (cd j).dJ.ctorsA[J]? = some cA → ∀ i, i < cA.2 →
      i ∉ ConLeche.recIdxOf ((cd j).dJ.ksF J) → i ∈ ConLeche.recIdxOf (d.ksR (auxOfsOf st p.k cd j J)) →
      d.tgtsR (auxOfsOf st p.k cd j J) i < p.k) :
    R2Grp mpAux.base2 ρ (paramBvarsAt d.nP d.nP) (cd j)
      (fun t => d.psiFinal mpAux.base2 ψ p.k cd (auxOfsOf st p.k cd) order tbl₀ ((cd j).base + t))
      (fun t => d.invFold mpAux.base2 ψ p.k st.pins.length cd (auxOfsOf st p.k cd) s (p.k + (cd j).base + t)) := by
  by_cases hb : d.bb ψ = 0
  · exact R.r2Grp_prop tbl₀ hρ hj hb
  · exact R.r2Grp tbl₀ hρ hj (fun h => hb ((R.bb_iff hj).mpr h)) hb hfin hnoT

/-- **R1 at the run at ANY elimination bit**: the nonzero arm
(`r1At_of_run`) or the `Prop` arm (`r1At_prop`).  Remaining
restrictions: every container finitary without transports (`hfin`,
`hnoT`) and the scratch block finitary (`hfinA`). -/
theorem r1At_all (tbl₀ : Nat → AnnotTerm) {ρ : Nat → V}
    (hρ : SpineFit ρ (d.params ψ) (paramVals d.nP ρ))
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
  by_cases hb : d.bb ψ = 0
  · exact R.r1At_prop tbl₀ hρ hb hj ht
  · exact R.r1At_of_run tbl₀ hρ hb (fun j' hj' h => hb ((R.bb_iff hj').mpr h)) hfin hnoT hfinA hj ht

end NestedRunFacts

end ConLeche.Model
