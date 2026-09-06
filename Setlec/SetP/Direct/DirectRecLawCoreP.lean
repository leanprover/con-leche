import Setlec.SetP.Direct.DirectRecLawFitsP

/-!
# The recursor rule's law, semantically (task #175 W4c, P3 module 6, part 18)

`recLawCore`: the recursor leaf applied to a fitting spine ending in
the constructor leaf applied to fitting arguments interprets as the
rule's right-hand side applied to the parameters, motive, minor and
fields — both sides fold, by `mkLamsAV_fold_graded`, to the minor
applied to the fields (the major's projections in the graph regime;
at squash the minor is the point when the elimination level is zero,
and the fields are points otherwise).  The application of the
right-hand side is graded (`mkAppN_okP_of_lam`).
-/

namespace Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Kit -/

omit [SetTheory V] in
/-- The frame values of a consed spine are the spine. -/
theorem frameVals_consList (as : List V) (σ : Nat → V) :
    frameVals (consList as σ) as.length as.length = as := by
  apply List.ext_getElem
  · simp [frameVals]
  · intro i h1 h2
    simp only [frameVals, List.getElem_map, List.getElem_range]
    have hi : i < as.length := by simpa [frameVals] using h1
    rw [consList_apply_lt as σ (as.length - 1 - i) (by omega),
      show as.length - 1 - (as.length - 1 - i) = i from by omega, List.getElem?_eq_getElem h2,
      Option.getD_some]

omit [SetTheory V] in
/-- A consed spine's last element sits at index `0`. -/
theorem consList_apply_last (as : List V) (a : V) (σ : Nat → V) :
    consList (as ++ [a]) σ 0 = a := by
  rw [consList_append]
  rfl

/-- A spine fitting a chain of truth values is all points. -/
theorem spineFit_bound_zero :
    ∀ {Fs : List AVExpr} {ρ : Nat → V} {as : List V},
      FieldsBound 0 ρ Fs → SpineFit ρ Fs as → ∀ a ∈ as, a = pt
  | [], _, [], _, _, _, ha => nomatch ha
  | [], _, _ :: _, _, hsp, _, _ => hsp.elim
  | _ :: _, _, [], _, hsp, _, _ => hsp.elim
  | F :: Fs, ρ, a :: as, hb, hsp, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · have h1 := hb.1
      rw [univ_zero] at h1
      exact eq_pt_of_mem_univZero h1 hsp.1
    · exact spineFit_bound_zero (hb.2 a hsp.1) hsp.2 x hx

/-! ## The law -/

set_option maxHeartbeats 6400000 in
/-- **The recursor rule's law at the readings.** -/
theorem recLawCore {ℓ w nP nF : Nat} {rds ds : List (Nat × Nat × AVExpr)}
    (hlenR : rds.length = nP + 3) (hlenDs : ds.length = nP + nF)
    (hokR : ∀ ρ : Nat → V, AnnotOk2 V ρ (directRecAV ℓ rds nF))
    (hbase : ∀ ρp : Nat → V, Sat2 V ((((rds.take nP).map (·.2.2)).reverse)) ρp →
      RecBase ℓ w ρp ((ds.drop nP).map (·.2.2)) (rds.getD nP default)
        (rds.getD (nP + 1) default) (rds.getD (nP + 2) default))
    (hfieldsB : ∀ ρ : Nat → V, Sat2 V ((((ds.take nP).map (·.2.2)).reverse)) ρ →
      FieldsOkB w ρ ((ds.drop nP).map (·.2.2)))
    (hbound0 : ℓ ≠ 0 → w = 0 → ∀ ρ : Nat → V,
      Sat2 V ((((ds.take nP).map (·.2.2)).reverse)) ρ →
      FieldsBound 0 ρ ((ds.drop nP).map (·.2.2)))
    {lds : List (Nat × AVExpr)} (hlenL : lds.length = nP + 2 + nF)
    {Ra : AVExpr}
    (hRa : Ra = mkLamsAV lds
      (AVExpr.mkAppN (.bvar nF) ((List.range nF).map fun k => AVExpr.bvar (nF - 1 - k))))
    (hokRa : ∀ ρ : Nat → V, AnnotOkP V ρ Ra)
    (hfitsL : ∀ ρ'' : Nat → V,
      Sat2 V ((((liftDoms 2 0 (ds.drop nP)).map (·.2.2)).reverse) ++
        (((rds.map (·.2.2)).reverse).getD 1 default :: ((rds.map (·.2.2)).reverse).drop 2)) ρ'' →
      SpineFit (fun k => ρ'' (k + (nP + 2 + nF))) (lds.map (·.2))
        (frameVals ρ'' (nP + 2 + nF) (nP + 2 + nF)))
    {ρ : Nat → V} {xs ys : List AVExpr} (hxl : xs.length = nP + 2) (hyl : ys.length = nP + nF)
    (hspR : SpineFit ρ (rds.map (·.2.2))
      ((xs ++ [AVExpr.mkAppN (directMkAV w ds ((ds.drop nP).map (·.2.2))) ys]).map (interp2 V ρ)))
    (hspC : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp2 V ρ)))
    (hplain : ∀ i, i < nP →
      interp2 V ρ (ys.getD i default) = interp2 V ρ (xs.getD i default)) :
    interp2 V ρ (AVExpr.mkAppN (directRecAV ℓ rds nF)
        (xs ++ [AVExpr.mkAppN (directMkAV w ds ((ds.drop nP).map (·.2.2))) ys]))
      = interp2 V ρ (AVExpr.mkAppN Ra (xs.take (nP + 2) ++ ys.drop nP)) ∧
    ((∀ a ∈ xs, AnnotOkP V ρ a) → (∀ b ∈ ys, AnnotOkP V ρ b) →
      AnnotOkP V ρ (AVExpr.mkAppN Ra (xs.take (nP + 2) ++ ys.drop nP))) := by
  -- names and lengths
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hlenΓ : ((rds.map (·.2.2)).reverse).length = nP + 3 := by simp [hlenR]
  have hxtake : xs.take (nP + 2) = xs := List.take_of_length_le (by omega)
  rw [hxtake]
  -- the constructor's fit, split at the parameters
  have hdsSplit : ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hdsSplit] at hspC
  obtain ⟨as₁, as₂, hys, hsp₁, hsp₂⟩ := spineFit_append_inv hspC
  have hlen₁ : as₁.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlen₂ : as₂.length = nF := by rw [hsp₂.length_eq, hlenFs]
  have hsatC₁ : Sat2 V ((((ds.take nP).map (·.2.2)).reverse)) (consList as₁ ρ) := by
    have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  -- the recursor's fit: the parameters, the motive, the minor, the major
  have hrdsSplit : rds.map (·.2.2)
      = (rds.take nP).map (·.2.2) ++ [(rds.getD nP default).2.2, (rds.getD (nP + 1) default).2.2,
          (rds.getD (nP + 2) default).2.2] := by
    conv => lhs; rw [rec_split hlenR]
    simp only [List.map_append, List.map_cons, List.map_nil]
  have hspR' := hspR
  rw [hrdsSplit, List.map_append, List.map_cons, List.map_nil] at hspR'
  obtain ⟨bs₁, bs₂, hxs, hspP, hspRest⟩ := spineFit_append_inv hspR'
  have hlenb₁ : bs₁.length = nP := by rw [hspP.length_eq]; simp [hlenR]
  have hlenb₂ : bs₂.length = 3 := by rw [hspRest.length_eq]; rfl
  obtain ⟨M, m, t, rfl⟩ : ∃ M m t, bs₂ = [M, m, t] := by
    match bs₂, hlenb₂ with
    | [M, m, t], _ => exact ⟨M, m, t, rfl⟩
  obtain ⟨hM, hm, ht', -⟩ := hspRest
  -- the argument values
  have hxsv : xs.map (interp2 V ρ) = bs₁ ++ [M, m] ∧
      interp2 V ρ (AVExpr.mkAppN (directMkAV w ds ((ds.drop nP).map (·.2.2))) ys) = t := by
    have h := hxs
    rw [show bs₁ ++ [M, m, t] = (bs₁ ++ [M, m]) ++ [t] from by simp] at h
    have h1 := List.append_inj_right' h (by simp)
    have h2 := List.append_inj_left' h (by simp)
    exact ⟨h2, by simpa using h1⟩
  obtain ⟨hxsv, ht⟩ := hxsv
  have hρp : Sat2 V ((((rds.take nP).map (·.2.2)).reverse)) (consList bs₁ ρ) := by
    have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) hspP
    rwa [List.append_nil] at this
  obtain ⟨-, -, -, hMeq, hMcont⟩ := hbase _ hρp
  obtain ⟨-, hmeq, -⟩ := hMcont M hM
  -- the parameters, identified
  have hparams : as₁ = bs₁ := by
    have h1 : as₁ = (ys.map (interp2 V ρ)).take nP := by
      rw [hys, List.take_left' hlen₁]
    have h2 : bs₁ = (xs.map (interp2 V ρ)).take nP := by
      rw [hxsv, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [h1, h2]
    apply List.ext_getElem
    · simp only [List.length_take, List.length_map, hxl, hyl]; omega
    · intro i h1' h2'
      have hi : i < nP := by simpa [hyl] using h1'
      simp only [List.getElem_take, List.getElem_map]
      have := hplain i hi
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
      simpa using this
  subst hparams
  have hsatC₁' : Sat2 V ((((ds.take nP).map (·.2.2)).reverse)) (consList as₁ ρ) := hsatC₁
  -- the constructor leaf's value
  have hleafC' : directMkAV w ds ((ds.drop nP).map (·.2.2))
      = directMkAV w (ds.take nP ++ ds.drop nP) ((ds.drop nP).map (·.2.2)) := by
    rw [List.take_append_drop]
  have hmkv : t = if w = 0 then (pt : V) else mkTower as₂ := by
    rw [← ht, interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app), hys,
      hleafC']
    rcases Nat.eq_zero_or_pos w with hw0 | hwpos
    · rw [hw0, directMkAV_zero, foldl_app_pt, if_pos rfl]
    · have hw : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
      rw [directMkAV_fold hw hsp₁ hsp₂ ((hfieldsB _ hsatC₁).toBound hw), if_neg hw]
  -- the left-hand side: the recursor leaf's fold
  have hLHS : interp2 V ρ (AVExpr.mkAppN (directRecAV ℓ rds nF)
        (xs ++ [AVExpr.mkAppN (directMkAV w ds ((ds.drop nP).map (·.2.2))) ys]))
      = ((List.range nF).map fun i => projS i t).foldl SetTheory.app m := by
    rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app),
      List.map_append, List.map_cons, List.map_nil, hxs]
    unfold directRecAV mkLamsC
    have hsp : SpineFit ρ ((rds.map fun d => (ℓ, d.2.2)).map (·.2)) (as₁ ++ [M, m, t]) := by
      rw [List.map_map]
      show SpineFit ρ (rds.map (·.2.2)) _
      rw [hrdsSplit]
      exact SpineFit.append hspP ⟨hM, hm, ht', trivial⟩
    rw [mkLamsAV_fold_graded (hokR ρ) hsp, recBodyAV_interp]
    rw [show as₁ ++ [M, m, t] = (as₁ ++ [M, m]) ++ [t] from by simp, consList_apply_last,
      consList_append,
      show consList [t] (consList (as₁ ++ [M, m]) ρ) 1 = consList (as₁ ++ [M, m]) ρ 0 from rfl,
      show as₁ ++ [M, m] = (as₁ ++ [M]) ++ [m] from by simp, consList_apply_last]
  -- the frame of the right-hand side
  have hdrop1 : ((rds.map (·.2.2)).reverse).drop 1
      = ((rds.map (·.2.2)).reverse).getD 1 default :: ((rds.map (·.2.2)).reverse).drop 2 := by
    have h := drop_succ_eq_getD_cons hlenΓ (i := nP + 1) (by omega)
    rwa [show nP + 3 - (nP + 1 + 1) = 1 from by omega, show nP + 3 - 1 - (nP + 1) = 1 from by omega,
      show nP + 3 - (nP + 1) = 2 from by omega] at h
  have hdrop1' : ((rds.map (·.2.2)).reverse).drop 1 = ((rds.take (nP + 2)).map (·.2.2)).reverse := by
    rw [reverse_map_take_drop rds (nP + 2), List.drop_left' (by simp [hlenR])]
  have hrdsTake : (rds.take (nP + 2)).map (·.2.2)
      = (rds.take nP).map (·.2.2) ++ [(rds.getD nP default).2.2, (rds.getD (nP + 1) default).2.2] := by
    conv => lhs; rw [rec_split hlenR]
    rw [List.take_append, List.take_of_length_le (by simp [hlenR]),
      List.length_take_of_le (by omega), show nP + 2 - nP = 2 from by omega]
    simp only [List.map_append, List.map_cons, List.map_nil, List.take_succ_cons, List.take_zero]
  have hys₂ : (ys.map (interp2 V ρ)).drop nP = as₂ := by rw [hys, List.drop_left' hlen₁]
  have hρ'' : Sat2 V ((((liftDoms 2 0 (ds.drop nP)).map (·.2.2)).reverse) ++
      (((rds.map (·.2.2)).reverse).getD 1 default :: ((rds.map (·.2.2)).reverse).drop 2))
      (consList ((xs ++ ys.drop nP).map (interp2 V ρ)) ρ) := by
    rw [← hdrop1, hdrop1', List.map_append, List.map_drop, hys₂, hxsv, consList_append]
    refine sat2_of_spineFit ?_ ?_
    · have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ)
        (SpineFit.append hspP (show SpineFit (consList as₁ ρ)
          [(rds.getD nP default).2.2, (rds.getD (nP + 1) default).2.2] [M, m] from
          ⟨hM, hm, trivial⟩))
      rwa [List.append_nil, ← hrdsTake] at this
    · rw [spineFit_liftDoms, consList_append, show consList [M, m] (consList as₁ ρ)
        = cons m (cons M (consList as₁ ρ)) from rfl, shiftE_cons_cons]
      exact hsp₂
  have hfit := hfitsL _ hρ''
  have hlenArgs : ((xs ++ ys.drop nP).map (interp2 V ρ)).length = nP + 2 + nF := by
    rw [List.map_append, List.map_drop, hys₂, hxsv]; simp [hlen₂]; omega
  rw [← hlenArgs, frameVals_consList] at hfit
  have hρtail : (fun k => consList ((xs ++ ys.drop nP).map (interp2 V ρ)) ρ
      (k + ((xs ++ ys.drop nP).map (interp2 V ρ)).length)) = ρ := by
    funext k; rw [consList_apply_add]
  rw [hρtail] at hfit
  -- the right-hand side: the rule's fold
  have hRHS : interp2 V ρ (AVExpr.mkAppN Ra (xs ++ ys.drop nP)) = as₂.foldl SetTheory.app m := by
    rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app), hRa,
      mkLamsAV_fold_graded (by rw [← hRa]; exact (hokRa ρ).1) hfit, interp2_mkAppN,
      ← List.foldl_map (f := interp2 V (consList ((xs ++ ys.drop nP).map (interp2 V ρ)) ρ))
        (g := SetTheory.app),
      List.map_append, List.map_drop, hys₂, hxsv, consList_append, map_fieldBvars_interp hlen₂,
      interp2_bvar, show nF = 0 + as₂.length from by omega, consList_apply_add,
      show as₁ ++ [M, m] = (as₁ ++ [M]) ++ [m] from by simp, consList_apply_last]
  refine ⟨?_, ?_⟩
  · rw [hLHS, hRHS, hmkv]
    rcases Nat.eq_zero_or_pos w with hw0 | hwpos
    · rw [if_pos hw0]
      simp only [projS_pt]
      rw [List.map_const', List.length_range]
      rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓpos
      · have hmpt : m = pt := by
          refine minor_pt_of_zero hℓ0 (A := towerSet w (teleOfFields (consList as₁ ρ)
            ((ds.drop nP).map (·.2.2)))) ?_ (by rw [← hmeq]; exact hm)
          rw [← hMeq]; exact hM
        rw [hmpt, foldl_app_pt, foldl_app_pt]
      · have hall := spineFit_bound_zero
          (hbound0 (Nat.pos_iff_ne_zero.mp hℓpos) hw0 _ hsatC₁) hsp₂
        rw [(List.eq_replicate_iff.mpr ⟨hlen₂, hall⟩ : as₂ = List.replicate nF pt)]
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hwpos), map_range_projS_mkTower hlen₂]
  · intro hxs_ok hys_ok
    refine mkAppN_okP_of_lam (hokRa ρ) ?_ (by rw [← hRa]; exact (hokRa ρ).1)
      (Or.inr (by rw [hRa])) hfit
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hxs_ok a h
    · exact hys_ok a (List.mem_of_mem_drop h)

end Setlec.Semantics
