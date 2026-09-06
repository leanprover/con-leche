import Setlec.SetP.DirectSum.SumRecDataP
import Setlec.SetP.DirectSum.SumStageFormerP
import Setlec.SetP.Direct.DirectRecFramesP

/-!
# The sum recursor's frames (task #175 sum-types)

`sumRecFrames`: at a parameter frame, the generated sum recursor's
entries read to the recursor leaf's premise `RecBaseS` — the motive
entry to the Π over the carrier into the elimination sort, minor
entry `j` (at the frame under the motive and the earlier minors) to
constructor `j`'s minor space `minorSpC`, the major entry to the
carrier.  `recFrames` at a constructor list: one walk down the minor
chain (`sumMinorsTail`).
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectSumParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The field chains of a data list -/

/-- The field chains of the constructor data (at the parameter
frame). -/
def fssOf (nP : Nat) (cds : List (Name × Nat × List (Nat × Nat × AVExpr))) :
    List (List AVExpr) :=
  cds.map fun cd => (cd.2.2.drop nP).map (·.2.2)

theorem fssOf_length (nP : Nat) (cds : List (Name × Nat × List (Nat × Nat × AVExpr))) :
    (fssOf nP cds).length = cds.length := by simp [fssOf]

theorem fssOf_getElem? (nP : Nat) (cds : List (Name × Nat × List (Nat × Nat × AVExpr)))
    (j : Nat) : (fssOf nP cds)[j]? = cds[j]?.map fun cd => (cd.2.2.drop nP).map (·.2.2) := by
  simp [fssOf]

theorem sumMinorsData_getElem? {m : EnvS2Core V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (cds : List (Name × Nat × List (Nat × Nat × AVExpr))) (o j : Nat),
      (sumMinorsData m ψ nP b cds o)[j]?
        = cds[j]?.map fun cd => (0, b, minorAVAt m cd.1 ψ nP cd.2.1 b (o + j) cd.2.2)
  | [], _, _ => by simp [sumMinorsData]
  | (C, nF, ds) :: cs, o, 0 => by simp [sumMinorsData]
  | (C, nF, ds) :: cs, o, j + 1 => by
    simp only [sumMinorsData, List.getElem?_cons_succ]
    rw [sumMinorsData_getElem? cs (o + 1) j, show o + 1 + j = o + (j + 1) from by omega]

/-! ## The recursor data's entries -/

section Entries

variable {pds dms : List (Nat × Nat × AVExpr)} {dM dt : Nat × Nat × AVExpr}

theorem rds_getElem?_M {i : Nat} (hi : i = pds.length) :
    (pds ++ [dM] ++ dms ++ [dt])[i]? = some dM := by
  subst hi
  rw [List.getElem?_append_left (by simp), List.getElem?_append_left (by simp),
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem rds_getElem?_minor {i j : Nat} (hj : j < dms.length) (hi : i = pds.length + 1 + j) :
    (pds ++ [dM] ++ dms ++ [dt])[i]? = dms[j]? := by
  subst hi
  rw [List.getElem?_append_left (by simp <;> omega),
    List.getElem?_append_right (by simp <;> omega)]
  simp

theorem rds_getElem?_t {i : Nat} (hi : i = pds.length + 1 + dms.length) :
    (pds ++ [dM] ++ dms ++ [dt])[i]? = some dt := by
  subst hi
  rw [List.getElem?_append_right (by simp; omega), List.length_append, List.length_append,
    List.length_singleton, Nat.sub_self]
  rfl

theorem rds_length : (pds ++ [dM] ++ dms ++ [dt]).length = pds.length + dms.length + 2 := by
  simp; omega

/-- The reversed context below the motive is the parameters'. -/
theorem rds_drop_params :
    (((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).reverse).drop (dms.length + 2)
      = (pds.map (·.2.2)).reverse := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc]
  rw [show dms.length + 2 = ((dms.map (·.2.2)).reverse.length + 1) + 1 from by simp,
    List.drop_succ_cons, ← List.singleton_append, ← List.append_assoc,
    List.drop_left' (by simp)]

end Entries

/-! ## The minor space, read -/

/-- **The minor space with an explicit conclusion is the interpreted
Π-tower** over field domains agreeing with the chain's. -/
theorem interp_minorSpC_of_tele {ℓ : Nat} {M : V} {c : List V → V} :
    ∀ {Fs : List AVExpr} {gds : List (Nat × Nat × AVExpr)} {Rm : AVExpr}
      {σ ρf : Nat → V} {acc : List V},
      gds.length = Fs.length →
      (∀ d ∈ gds, (ℓ = 0 ↔ d.2.1 = 0)) →
      (∀ (j : Nat) (as : List V), j < Fs.length → SpineFit ρf (Fs.take j) as →
        interp2 V (consList as σ) ((gds.getD j default).2.2)
          = interp2 V (consList as ρf) (Fs.getD j default)) →
      (∀ as : List V, SpineFit ρf Fs as →
        interp2 V (consList as σ) Rm = SetTheory.app M (c (acc ++ as))) →
      interp2 V σ (mkPisAV gds Rm) = minorSpC ℓ M c Fs ρf acc
  | [], [], Rm, σ, ρf, acc, _, _, _, hbase => by
    have := hbase [] trivial
    simp only [consList, List.append_nil] at this
    simpa [mkPisAV, minorSpC] using this
  | [], _ :: _, _, _, _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _, _, _ => by simp at hlen
  | F :: Fs, d :: gds, Rm, σ, ρf, acc, hlen, hbits, hdom, hbase => by
    simp only [mkPisAV, interp2_pi, minorSpC]
    have hd0 : interp2 V σ d.2.2 = interp2 V ρf F := by
      have := hdom 0 [] (by simp) trivial
      simpa [consList] using this
    rw [hd0, piR_congr_bit (v := d.2.1) (v' := ℓ) (hbits d List.mem_cons_self).symm]
    apply piR_congr
    intro a ha
    refine interp_minorSpC_of_tele (by simpa using hlen)
      (fun d' hd' => hbits d' (List.mem_cons_of_mem _ hd')) ?_ ?_
    · intro j as hj hsp
      have := hdom (j + 1) (a :: as) (by simpa using hj)
        (by simp only [List.take_succ_cons, SpineFit]; exact ⟨ha, hsp⟩)
      simpa [consList_cons] using this
    · intro as hsp
      have := hbase (a :: as) ⟨ha, hsp⟩
      rw [consList_cons] at this
      rw [this, List.append_cons]

/-! ## The family spine -/

/-- The former's parameter walk, folded along a fitting spine: the
chains are graded at the spine's frame. -/
theorem paramsOkS_fold {w : Nat} {Fss : List (List AVExpr)} :
    ∀ {pps : List (Nat × Nat × AVExpr)} {ρ : Nat → V} {as : List V},
      ParamsOkS w ρ Fss pps → SpineFit ρ (pps.map (·.2.2)) as →
      SumFieldsOkB w (consList as ρ) Fss
  | [], _, [], h, _ => h
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | _ :: _, ρ, a :: as, h, hsp =>
    paramsOkS_fold (ρ := cons a ρ) (as := as) (h.2.2 a hsp.1) hsp.2

/-- **The family spine's value and grading** at any frame `σ` whose
`e`-th tail is a parameter valuation: the instantiated carrier, graded. -/
theorem sumFamSpine_val {w : Nat} {Fss : List (List AVExpr)}
    {pps : List (Nat × Nat × AVExpr)} {nP : Nat}
    (hbits : ∀ d ∈ pps, d.2.1 ≠ 0) (hbelow : DomsBelow 0 pps) (hlen : pps.length = nP)
    (hok : ∀ ρ : Nat → V, ParamsOkS w ρ Fss pps)
    (hval : ∀ ρ : Nat → V, UnderTowerValid ρ (sumBodyAV w Fss) pps)
    (hcl : VExpr.bvarsBelow 0 (directSumTyAV w pps Fss).erase)
    {ρp σ : Nat → V} {e : Nat} (hσ : ∀ j, σ (j + e) = ρp j)
    (hsat : Sat2 V ((pps.map (·.2.2)).reverse) ρp) :
    AnnotOkP V σ (AVExpr.mkAppN (directSumTyAV w pps Fss) (paramBvarsAt nP (nP + e))) ∧
      interp2 V σ (AVExpr.mkAppN (directSumTyAV w pps Fss) (paramBvarsAt nP (nP + e)))
        = sumSet w (sumFibre w ρp Fss) := by
  have hspP := spineFit_of_sat2 (Δ₀ := []) (Ds := pps.map (·.2.2))
    (by rw [List.append_nil]; exact hsat)
  simp only [List.length_map, hlen] at hspP
  have hmap := map_paramBvarsAt_interp (V := V) (nP := nP) hσ
  have hspσ : SpineFit σ (pps.map (·.2.2)) ((paramBvarsAt nP (nP + e)).map (interp2 V σ)) := by
    rw [hmap]
    exact spineFit_congr_below hbelow (fun i hi => absurd hi (Nat.not_lt_zero i)) hspP
  refine ⟨(mkAppN_okP_of_spineFit (b := .sort w) hbits (directSumTyAV_okP (hok σ) (hval σ))
    (fun a ha => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
      exact ⟨by rw [AnnotOk2_bvar]; trivial, by rw [AnnotValidV_bvar]; trivial⟩)
    (directSumTyAV_mem (hok σ)) hspσ).1, ?_⟩
  rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V σ) (g := SetTheory.app), hmap,
    interp2_closed (V := V) hcl σ (fun j => ρp (j + nP)),
    directSumTyAV_fold hspP (paramsOkS_fold (hok _) hspP), consList_range_reverse]

/-! ## The minor chain -/

/-- **The walk down the minor chain**: at the frame under the motive
and the first `j` minors, the remaining minor entries read to their
spaces and the major entry to the carrier. -/
theorem sumMinorsTail {m : EnvS2Core V env} {ψ : Name → Nat} {nP ℓ w b : Nat}
    {ρp : Nat → V} {M : V} {pps : List (Nat × Nat × AVExpr)}
    {cds : List (Name × Nat × List (Nat × Nat × AVExpr))} {dM dt : Nat × Nat × AVExpr}
    (hlenP : pps.length = nP)
    (hokΓ : ∀ i, i < nP + cds.length + 2 → ∀ σ : Nat → V,
      Sat2 V ((((rebit b pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ [dt]).map (·.2.2)).reverse).drop
        (nP + cds.length + 2 - i)) σ →
      AnnotOkP V σ ((((rebit b pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ [dt]).map (·.2.2)).reverse).getD
        (nP + cds.length + 2 - 1 - i) default))
    (hmajor : ∀ σ : Nat → V, shiftE (cds.length + 1) 0 σ = ρp →
      interp2 V σ dt.2.2 = sumSet w (sumFibre w ρp (fssOf nP cds)))
    (hctor : ∀ (i : Nat) (cd : Name × Nat × List (Nat × Nat × AVExpr)), cds[i]? = some cd →
      ∀ σ : Nat → V, shiftE (i + 1) 0 σ = ρp → σ i = M →
      interp2 V σ (minorAVAt m cd.1 ψ nP cd.2.1 b (1 + i) cd.2.2)
        = minorSpC ℓ M (ctorVal w i) ((fssOf nP cds).getD i []) ρp []) :
    ∀ (k j : Nat) (σ : Nat → V), cds.length - j = k → j ≤ cds.length → TailFrame ρp M j σ →
      Sat2 V ((((rebit b pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ [dt]).map (·.2.2)).reverse).drop
        (nP + cds.length + 2 - (nP + 1 + j))) σ →
      RecTailS ℓ w ρp (fssOf nP cds) M dt (sumMinorsData m ψ nP b (cds.drop j) (1 + j)) j σ := by
  have hlenR : (rebit b pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ [dt]).length
      = nP + cds.length + 2 := by
    rw [rds_length, rebit_length, hlenP, sumMinorsData_length]
  have hlenΓ : ((((rebit b pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ [dt]).map (·.2.2)).reverse)).length
      = nP + cds.length + 2 := by rw [List.length_reverse, List.length_map, hlenR]
  intro k
  induction k with
  | zero =>
    intro j σ hk hj hfr hsat
    have hjn : j = cds.length := by omega
    subst hjn
    rw [List.drop_eq_nil_of_le (Nat.le_refl _)]
    show AnnotOk2 V σ dt.2.2 ∧ interp2 V σ dt.2.2 = _
    refine ⟨?_, hmajor σ hfr.sh⟩
    have h := (hokΓ (nP + 1 + cds.length) (by omega) σ hsat).1
    have hent := getD_reverse_of_peel hlenR (i := nP + 1 + cds.length) (by omega)
      (rds_getElem?_t (by rw [rebit_length, hlenP, sumMinorsData_length]))
    rw [hent] at h
    exact h
  | succ k ih =>
    intro j σ hk hj hfr hsat
    have hjn : j < cds.length := by omega
    obtain ⟨cd, hcd⟩ : ∃ cd, cds[j]? = some cd := ⟨_, List.getElem?_eq_getElem hjn⟩
    rw [List.drop_eq_getElem_cons hjn, Option.some.inj ((List.getElem?_eq_getElem hjn).symm.trans hcd)]
    obtain ⟨C, nF, ds⟩ := cd
    show AnnotOk2 V σ (minorAVAt m C ψ nP nF b (1 + j) ds) ∧
      interp2 V σ (minorAVAt m C ψ nP nF b (1 + j) ds) = _ ∧
      ∀ mv, mv ∈ˢ interp2 V σ (minorAVAt m C ψ nP nF b (1 + j) ds) →
        RecTailS ℓ w ρp (fssOf nP cds) M dt (sumMinorsData m ψ nP b (cds.drop (j + 1)) (1 + j + 1))
          (j + 1) (cons mv σ)
    have hentj : ((((rebit b pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ [dt]).map (·.2.2)).reverse)).getD
        (nP + cds.length + 2 - 1 - (nP + 1 + j)) default
        = minorAVAt m C ψ nP nF b (1 + j) ds := by
      have := getD_reverse_of_peel hlenR (i := nP + 1 + j) (by omega)
        (p := (0, b, minorAVAt m C ψ nP nF b (1 + j) ds))
        (by rw [rds_getElem?_minor (by rw [sumMinorsData_length]; exact hjn)
                (by rw [rebit_length, hlenP]),
              sumMinorsData_getElem?, hcd]
            rfl)
      exact this
    have hokj := (hokΓ (nP + 1 + j) (by omega) σ hsat).1
    rw [hentj] at hokj
    refine ⟨hokj, hctor j (C, nF, ds) hcd σ hfr.sh hfr.hM, fun mv hmv => ?_⟩
    have hsat' : Sat2 V ((((rebit b pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ [dt]).map (·.2.2)).reverse).drop
        (nP + cds.length + 2 - (nP + 1 + (j + 1)))) (cons mv σ) := by
      have h := drop_succ_eq_getD_cons hlenΓ (i := nP + 1 + j) (by omega)
      rw [show nP + 1 + (j + 1) = nP + 1 + j + 1 from by omega, h, hentj]
      exact Sat2_cons V hsat hmv
    have := ih (j + 1) (cons mv σ) (by omega) (by omega) (hfr.push mv) hsat'
    rwa [show 1 + (j + 1) = 1 + j + 1 from by omega] at this

set_option maxHeartbeats 6400000 in
/-- **The sum recursor's frames, by computation.** -/
theorem sumRecFrames {m : EnvS2Core V env} {p : DirectSumParts} {cvTa cvRa : ConstantVal}
    {ctorsA : List (ConstantVal × Nat)}
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData m cvTa p.nP p.resSort pps)
    (hcf : ∀ j cA, ctorsA[j]? = some cA →
      CtorFactsAt m p.cvT.name p.cvT.levelParams p.nP p.resSort dsF j cA)
    (hleafT : ∀ ψ, m.acval p.cvT.name ψ
      = directSumTyAV (p.resSort.eval ψ) (pps ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, m.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)))
    (hwl : p.large = true → p.resSort.isNeverZero = true ∨ ctorsA.length < 2)
    (hn1 : ctorsA.length ≠ 1)
    (ψ : Name → Nat) {fvsR : List Expr} {oR : Expr}
    (hR : OpenedP m ψ (p.nP + ctorsA.length + 2) cvRa.type fvsR oR
      (((sumRdsAV m p pps dsF ctorsA ψ).map (·.2.2)).reverse)
      (.app (.bvar (ctorsA.length + 1)) (.bvar 0))) :
    ∀ ρp : Nat → V, Sat2 V (((pps ψ).map (·.2.2)).reverse) ρp →
      RecBaseS ((sumElimLevel p).eval ψ) (p.resSort.eval ψ) ρp
        (fssOf p.nP (ctorDataList dsF ψ ctorsA 0))
        (0, pwBit ψ (Level.zeronessOf (sumElimLevel p)), motiveAV m p.cvT.name ψ p.nP (sumElimLevel p))
        (sumMinorsData m ψ p.nP (pwBit ψ (Level.zeronessOf (sumElimLevel p)))
          (ctorDataList dsF ψ ctorsA 0) 1)
        (0, pwBit ψ (Level.zeronessOf (sumElimLevel p)),
          majorAVAt m p.cvT.name ψ p.nP (ctorDataList dsF ψ ctorsA 0).length) := by
  intro ρp hsatP
  -- the facts at `ψ`
  have hleafTψ := hleafT ψ
  have hleafCψ : ∀ j cA, ctorsA[j]? = some cA → m.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)) := fun j cA h => hleafC j cA h ψ
  have hiffψ : ∀ j cA, ctorsA[j]? = some cA → ∀ ρ : Nat → V,
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ := fun j cA h ρ => hiff j cA h ψ ρ
  have hfieldsψ : ∀ j cA, ctorsA[j]? = some cA → ∀ ρ : Nat → V,
      Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)) := fun j cA h ρ => hfields j cA h ψ ρ
  have hlenΓ0 : ((((sumRdsAV m p pps dsF ctorsA ψ).map (·.2.2)).reverse)).length
      = p.nP + ctorsA.length + 2 := by
    simp only [List.length_reverse, List.length_map, sumRdsAV, sumRecDataAV, List.length_append,
      rebit_length, hFD.len ψ, List.length_singleton, sumMinorsData_length, ctorDataList_length]
    omega
  -- the former's walks (at the un-generalized names)
  have hFssOk : ∀ (ψ' : Name → Nat) (ρ : Nat → V), Sat2 V ((pps ψ').map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ') ρ (fssOf p.nP (ctorDataList dsF ψ' ctorsA 0)) ∧
      SumFieldsValid ρ (fssOf p.nP (ctorDataList dsF ψ' ctorsA 0)) := by
    intro ψ' ρ hρ
    constructor
    · intro Fs hFs
      obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      rw [ctorDataList_getElem?, Nat.zero_add] at hi
      cases h : ctorsA[i]? with
      | none => rw [h] at hi; exact nomatch hi
      | some cA =>
        rw [h] at hi
        obtain rfl := Option.some.inj hi
        exact (hfields i cA h ψ' ρ ((hiff i cA h ψ' ρ).mp hρ)).1
    · intro Fs hFs
      obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      rw [ctorDataList_getElem?, Nat.zero_add] at hi
      cases h : ctorsA[i]? with
      | none => rw [h] at hi; exact nomatch hi
      | some cA =>
        rw [h] at hi
        obtain rfl := Option.some.inj hi
        exact (hfields i cA h ψ' ρ ((hiff i cA h ψ' ρ).mp hρ)).2
  have hwalks := formerWalksS hFD (fun ψ' ρ h => hFssOk ψ' ρ h) ψ
  have hclT := m.cval_closedL p.cvT.name ψ
  -- names
  generalize hcds : ctorDataList dsF ψ ctorsA 0 = cds at hleafTψ hleafCψ hR hwalks ⊢
  generalize hb : pwBit ψ (Level.zeronessOf (sumElimLevel p)) = b at hR ⊢
  generalize hℓ : (sumElimLevel p).eval ψ = ℓ
  generalize hw : p.resSort.eval ψ = w at hleafTψ hleafCψ hfieldsψ hwalks ⊢
  have hn : cds.length = ctorsA.length := by rw [← hcds, ctorDataList_length]
  rw [← hn] at hR
  have hbz : ℓ = 0 ↔ b = 0 := by
    rw [← hb, ← hℓ, pwBit_eq_zero_iff, Setlec.PropWhen.zeronessOf_sound, beq_iff_eq]
  have hrds : sumRdsAV m p pps dsF ctorsA ψ
      = rebit b (pps ψ) ++ [(0, b, motiveAV m p.cvT.name ψ p.nP (sumElimLevel p))] ++
        sumMinorsData m ψ p.nP b cds 1 ++ [(0, b, majorAVAt m p.cvT.name ψ p.nP cds.length)] := by
    rw [sumRdsAV, sumRecDataAV, hcds, hb]
  rw [hrds] at hR
  -- the per-constructor facts, positionally on `cds`
  have hcd : ∀ i cd, cds[i]? = some cd → ∃ cA, ctorsA[i]? = some cA ∧
      cd = (cA.1.name, cA.2, dsF i ψ) := by
    intro i cd hi
    rw [← hcds, ctorDataList_getElem?, Nat.zero_add] at hi
    cases h : ctorsA[i]? with
    | none => rw [h] at hi; exact nomatch hi
    | some cA => rw [h] at hi; exact ⟨cA, rfl, (Option.some.inj hi).symm⟩
  have hFsj : ∀ i cA, ctorsA[i]? = some cA →
      (fssOf p.nP cds)[i]? = some (((dsF i ψ).drop p.nP).map (·.2.2)) := by
    intro i cA hi
    rw [fssOf_getElem?, ← hcds, ctorDataList_getElem?, hi, Nat.zero_add]
    rfl
  have hokB : SumFieldsOkB w ρp (fssOf p.nP cds) := by
    intro Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    obtain ⟨cA, hiA, rfl⟩ := hcd i cd hi
    exact (hfieldsψ i cA hiA ρp ((hiffψ i cA hiA ρp).mp hsatP)).1
  have hok : ∀ ρ : Nat → V, ParamsOkS w ρ (fssOf p.nP cds) (pps ψ) := fun ρ => (hwalks ρ).1
  have hval : ∀ ρ : Nat → V, UnderTowerValid ρ (sumBodyAV w (fssOf p.nP cds)) (pps ψ) :=
    fun ρ => (hwalks ρ).2
  have hcl : VExpr.bvarsBelow 0 (directSumTyAV w (pps ψ) (fssOf p.nP cds)).erase := by
    rwa [hleafTψ] at hclT
  -- the family spine at any frame over the parameters
  have hfam : ∀ (e : Nat) (σ : Nat → V), (∀ j, σ (j + e) = ρp j) →
      AnnotOkP V σ (AVExpr.mkAppN (m.acval p.cvT.name ψ) (paramBvarsAt p.nP (p.nP + e))) ∧
      interp2 V σ (AVExpr.mkAppN (m.acval p.cvT.name ψ) (paramBvarsAt p.nP (p.nP + e)))
        = sumSet w (sumFibre w ρp (fssOf p.nP cds)) := by
    intro e σ hσ
    rw [hleafTψ]
    exact sumFamSpine_val (hFD.bits ψ) (hFD.below ψ) (hFD.len ψ) hok hval hcl hσ hsatP
  -- the frame's context
  have hlenR : (rebit b (pps ψ) ++ [(0, b, motiveAV m p.cvT.name ψ p.nP (sumElimLevel p))] ++
      sumMinorsData m ψ p.nP b cds 1 ++ [(0, b, majorAVAt m p.cvT.name ψ p.nP cds.length)]).length
      = p.nP + cds.length + 2 := by
    rw [rds_length, rebit_length, hFD.len ψ, sumMinorsData_length]
  have hlenΓ : ((((rebit b (pps ψ) ++ [(0, b, motiveAV m p.cvT.name ψ p.nP (sumElimLevel p))] ++
      sumMinorsData m ψ p.nP b cds 1 ++ [(0, b, majorAVAt m p.cvT.name ψ p.nP cds.length)]).map
        (fun d : Nat × Nat × AVExpr => d.2.2)).reverse)).length = p.nP + cds.length + 2 := by
    rw [List.length_reverse, List.length_map, hlenR]
  have hsatΓ : Sat2 V (((((rebit b (pps ψ) ++ [(0, b, motiveAV m p.cvT.name ψ p.nP (sumElimLevel p))] ++
      sumMinorsData m ψ p.nP b cds 1 ++ [(0, b, majorAVAt m p.cvT.name ψ p.nP cds.length)]).map
        (fun d : Nat × Nat × AVExpr => d.2.2)).reverse)).drop (p.nP + cds.length + 2 - p.nP)) ρp := by
    rw [show p.nP + cds.length + 2 - p.nP = (sumMinorsData m ψ p.nP b cds 1).length + 2 from by
        rw [sumMinorsData_length]; omega,
      rds_drop_params, rebit_map_dom]
    exact hsatP
  have hentM : ((((rebit b (pps ψ) ++ [(0, b, motiveAV m p.cvT.name ψ p.nP (sumElimLevel p))] ++
      sumMinorsData m ψ p.nP b cds 1 ++ [(0, b, majorAVAt m p.cvT.name ψ p.nP cds.length)]).map
        (fun d : Nat × Nat × AVExpr => d.2.2)).reverse)).getD (p.nP + cds.length + 2 - 1 - p.nP) default
      = motiveAV m p.cvT.name ψ p.nP (sumElimLevel p) := by
    have := getD_reverse_of_peel hlenR (i := p.nP) (by omega)
      (p := (0, b, motiveAV m p.cvT.name ψ p.nP (sumElimLevel p)))
      (rds_getElem?_M (by rw [rebit_length, hFD.len ψ]))
    exact this
  -- `RecBaseS`
  refine ⟨hokB, ?_, ?_, ?_, ?_, ?_⟩
  · -- the elimination restriction
    intro hw0
    by_cases hl0 : ℓ = 0
    · exact Or.inr hl0
    · left
      have hlarge : p.large = true := by
        cases hpl : p.large
        · exfalso; apply hl0
          rw [← hℓ]; simp [sumElimLevel, Setlec.directElimLevel, hpl, Level.eval]
        · rfl
      rcases hwl hlarge with hnz | hlt
      · exfalso
        exact Setlec.Level.isNeverZero_sound ψ _ hnz (by rw [hw]; exact hw0)
      · rw [fssOf_length, hn]; omega
  · rw [sumMinorsData_length, fssOf_length]
  · -- the motive's grading
    have h := (hR.okΓ p.nP (by omega) ρp hsatΓ).1
    rw [hentM] at h
    exact h
  · -- the motive's reading
    show interp2 V ρp (motiveAV m p.cvT.name ψ p.nP (sumElimLevel p)) = _
    unfold motiveAV
    rw [interp2_pi]
    have hfam0 := (hfam 0 ρp (fun j => rfl)).2
    rw [Nat.add_zero] at hfam0
    rw [hfam0, hℓ, piR_congr_bit (v' := ℓ + 1)
      ⟨fun h => absurd h (pwBit_ne_zero_of_isNever rfl ψ), fun h => absurd h (Nat.succ_ne_zero _)⟩]
    rfl
  · intro M hM
    have hsatM : Sat2 V (((((rebit b (pps ψ) ++ [(0, b, motiveAV m p.cvT.name ψ p.nP (sumElimLevel p))] ++
        sumMinorsData m ψ p.nP b cds 1 ++ [(0, b, majorAVAt m p.cvT.name ψ p.nP cds.length)]).map
          (fun d : Nat × Nat × AVExpr => d.2.2)).reverse)).drop (p.nP + cds.length + 2 - (p.nP + 1 + 0))) (cons M ρp) := by
      have h := drop_succ_eq_getD_cons hlenΓ (i := p.nP) (by omega)
      rw [Nat.add_zero, h, hentM]
      exact Sat2_cons V hsatΓ hM
    have hfr : TailFrame ρp M 0 (cons M ρp) :=
      { sh := by rw [show (0 : Nat) + 1 = 1 from rfl, shiftE_one_cons]
        hM := rfl }
    have htail := sumMinorsTail (m := m) (ψ := ψ) (nP := p.nP) (ℓ := ℓ) (w := w) (b := b)
      (ρp := ρp) (M := M) (pps := pps ψ) (cds := cds)
      (dM := (0, b, motiveAV m p.cvT.name ψ p.nP (sumElimLevel p)))
      (dt := (0, b, majorAVAt m p.cvT.name ψ p.nP cds.length)) (hFD.len ψ)
      hR.okΓ ?_ ?_ cds.length 0 (cons M ρp) (by omega) (Nat.zero_le _) hfr hsatM
    · rw [List.drop_zero, Nat.add_zero] at htail
      exact htail
    · -- the major's reading
      intro σ hσ
      show interp2 V σ (majorAVAt m p.cvT.name ψ p.nP cds.length) = _
      unfold majorAVAt
      have hσ' : ∀ j, σ (j + (1 + cds.length)) = ρp j := by
        intro j
        rw [← hσ]
        show σ (j + (1 + cds.length)) = σ (j + (cds.length + 1))
        rw [Nat.add_comm 1]
      have := (hfam (1 + cds.length) σ hσ').2
      rwa [show p.nP + (1 + cds.length) = p.nP + 1 + cds.length from by omega] at this
    · -- minor `i`'s reading: the minor space
      intro i cd hi σ hsh hσi
      obtain ⟨cA, hiA, rfl⟩ := hcd i cd hi
      obtain ⟨-, -, -, hCD⟩ := hcf i cA hiA
      have hsatC := (hiffψ i cA hiA ρp).mp hsatP
      have hlenFs : ((((dsF i ψ).drop p.nP).map (·.2.2))).length = cA.2 := by simp [hCD.len ψ]
      have hlenFds : (((dsF i ψ).drop p.nP)).length = cA.2 := by simp [hCD.len ψ]
      have hFsi : (fssOf p.nP cds).getD i [] = ((dsF i ψ).drop p.nP).map (·.2.2) := by
        rw [List.getD_eq_getElem?_getD, hFsj i cA hiA]; rfl
      rw [hFsi]
      show interp2 V σ (minorAVAt m cA.1.name ψ p.nP cA.2 b (1 + i) (dsF i ψ)) = _
      unfold minorAVAt
      refine interp_minorSpC_of_tele
        (by simp only [rebit_length, liftDoms_length, List.length_map]) ?_ ?_ ?_
      · intro d hd
        rw [mem_rebit hd]; exact hbz
      · -- the field domains agree along a fitting chain
        intro j as hj hsp
        rw [hlenFs] at hj
        have hlenAs : as.length = j := by
          rw [hsp.length_eq, List.length_take, hlenFs]; omega
        rw [rebit_getD _ _ _ (by rw [liftDoms_length]; omega)]
        show interp2 V (consList as σ)
          ((liftDoms (1 + i) 0 ((dsF i ψ).drop p.nP)).getD j default).2.2 = _
        obtain ⟨q, hq⟩ : ∃ q, ((dsF i ψ).drop p.nP)[j]? = some q :=
          ⟨_, List.getElem?_eq_getElem (by rw [hlenFds]; exact hj)⟩
        have hsh' : shiftE (1 + i) j (consList as σ) = consList as ρp := by
          rw [← hlenAs, shiftE_consList_len, Nat.add_comm 1 i, hsh]
        rw [List.getD_eq_getElem?_getD, liftDoms_getElem?, hq, Option.map_some, Option.getD_some]
        show interp2 V (consList as σ) (q.2.2.liftN (1 + i) (0 + j)) = _
        rw [interp2_liftN, Nat.zero_add, hsh', fields_getD (by rw [hlenFds]; exact hj),
          List.getD_eq_getElem?_getD, hq, Option.getD_some]
      · -- the core: the motive at the constructor leaf's fold
        intro as hsp
        have hlenAs : as.length = cA.2 := by rw [hsp.length_eq, hlenFs]
        have hMval : consList as σ (cA.2 + (1 + i) - 1) = M := by
          rw [show cA.2 + (1 + i) - 1 = i + as.length from by omega, consList_apply_add]
          exact hσi
        have hσ : ∀ j, consList as σ (j + ((1 + i) + cA.2)) = ρp j := by
          intro j
          rw [show j + ((1 + i) + cA.2) = (j + (i + 1)) + as.length from by omega,
            consList_apply_add, ← hsh]
          rfl
        have hleafC' : m.acval cA.1.name ψ
            = directSumMkAV w i ((dsF i ψ).take p.nP ++ (dsF i ψ).drop p.nP)
                (((dsF i ψ).drop p.nP).map (·.2.2)) (fssOf p.nP cds) := by
          rw [hleafCψ i cA hiA, List.take_append_drop]
        rw [interp2_app, interp2_bvar, hMval, interp2_mkAppN,
          ← List.foldl_map (f := interp2 V (consList as σ)) (g := SetTheory.app),
          List.map_append, show p.nP + (1 + i) + cA.2 = p.nP + ((1 + i) + cA.2) from by omega,
          map_paramBvarsAt_interp hσ]
        show SetTheory.app M ((List.map ρp (List.range p.nP).reverse ++
            List.map (interp2 V (consList as σ)) (fieldBvars cA.2)).foldl SetTheory.app
            (interp2 V (consList as σ) (m.acval cA.1.name ψ))) = _
        rw [show fieldBvars cA.2 = (List.range cA.2).map (fun k => AVExpr.bvar (cA.2 - 1 - k)) from rfl,
          map_fieldBvars_interp hlenAs,
          interp2_closed (V := V) (m.cval_closedL cA.1.name ψ) _ (fun j => ρp (j + p.nP)),
          hleafC']
        have hlenP : ((((dsF i ψ).take p.nP).map (·.2.2))).length = p.nP := by simp [hCD.len ψ]
        have hsp₁ := spineFit_of_sat2 (Δ₀ := []) (Ds := ((dsF i ψ).take p.nP).map (·.2.2))
          (by rw [List.append_nil]; exact hsatC)
        rw [hlenP] at hsp₁
        unfold ctorVal
        rw [List.nil_append]
        rcases Nat.eq_zero_or_pos w with hw0 | hwpos
        · rw [hw0, directSumMkAV_zero, foldl_app_pt_sum, if_pos rfl]
        · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
          rw [directSumMkAV_fold hw' hsp₁ (by rw [consList_range_reverse]; exact hsp)
            (by rw [consList_range_reverse]; exact hokB) (hFsj i cA hiA), if_neg hw']

end Setlec.SetP
