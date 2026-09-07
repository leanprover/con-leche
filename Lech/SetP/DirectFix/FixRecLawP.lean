import Lech.SetP.DirectFix.FixRecPreP
import Lech.SetP.DirectFix.FixIntroP

/-!
# The recursive recursor's rule law, at the readings (task #188)

The sum route's `sumRecLawCore` (`SumRecLawP.lean`) for the recursive
route: at a frame where the recursor's arguments fit its binder data
and the constructor's arguments fit the constructor's, the recursor at
the constructor value is the rule's right-hand side — the minor at the
fields and at the inductive hypotheses — at the block's arguments and
the fields.  The inductive hypotheses in the rule (`ihAppAV`) read to
the recursor at the block, the field's index values and the field,
exactly the recursor's iota (`directFixRecAVI_iota`).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Frames -/

omit [SetTheory V] in
/-- A block of length `nP + 1 + n` splits into parameters, a motive and
minors. -/
theorem block_split {as₀ : List V} {nP n : Nat} (hlen : as₀.length = nP + 1 + n) :
    ∃ (as₁ : List V) (M : V) (ms : List V),
      as₀ = (as₁ ++ [M]) ++ ms ∧ as₁.length = nP ∧ ms.length = n := by
  have hsplit := (List.take_append_drop nP as₀).symm
  have hlenD : (as₀.drop nP).length = 1 + n := by rw [List.length_drop]; omega
  cases hd : as₀.drop nP with
  | nil => rw [hd, List.length_nil] at hlenD; omega
  | cons M ms =>
    refine ⟨as₀.take nP, M, ms, ?_, by rw [List.length_take]; omega, ?_⟩
    · rw [List.append_assoc, List.singleton_append, ← hd, ← hsplit]
    · rw [hd] at hlenD; simp at hlenD; omega

/-- The rule's leading spine reads to the block. -/
theorem map_recPrefixBvars_interp {nP n nF : Nat} {as₁ ms as₂ : List V} {M : V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenM : ms.length = n) (hlenF : as₂.length = nF) :
    (recPrefixBvars nP n nF).map (interp2 V (consList as₂ (consList ms (cons M (consList as₁ ρ)))))
      = (as₁ ++ [M]) ++ ms := by
  unfold recPrefixBvars
  rw [List.map_append, List.map_append]
  congr 1
  congr 1
  · rw [show nP + nF + n + 1 = nP + (nF + n + 1) from by omega,
      map_paramBvarsAt_interp (ρp := consList as₁ ρ) (fun k => by
        rw [show k + (nF + n + 1) = (k + (n + 1)) + as₂.length from by omega, consList_apply_add,
          show k + (n + 1) = (k + 1) + ms.length from by omega, consList_apply_add]
        rfl), ← hlenP, range_reverse_map_consList]
  · simp only [List.map_cons, List.map_nil, interp2_bvar]
    rw [show nF + n = n + as₂.length from by omega, consList_apply_add,
      show n = 0 + ms.length from by omega, consList_apply_add]
    rfl
  · apply List.ext_getElem
    · simp [hlenM]
    · intro l h1 h2
      have hl : l < n := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, interp2_bvar]
      rw [show nF + n - 1 - l = (n - 1 - l) + as₂.length from by omega,
        consList_apply_add, consList_apply_lt' ms _ (by omega),
        show ms.length - 1 - (n - 1 - l) = l from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- The recursor's leading spine under `bs` telescope binders reads to
the block (task #202). -/
theorem map_recPrefixBvarsM_interp {nP n nF : Nat} {as₁ ms as₂ : List V} {M : V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenM : ms.length = n) (hlenF : as₂.length = nF) (bs : List V) :
    (recPrefixBvarsM nP n nF bs.length).map
        (interp2 V (consList bs (consList as₂ (consList ms (cons M (consList as₁ ρ))))))
      = (as₁ ++ [M]) ++ ms := by
  unfold recPrefixBvarsM
  rw [List.map_append, List.map_append]
  congr 1
  congr 1
  · rw [show nP + nF + n + 1 + bs.length = nP + (nF + n + 1 + bs.length) from by omega,
      map_paramBvarsAt_interp (ρp := consList as₁ ρ) (fun k => by
        rw [show k + (nF + n + 1 + bs.length) = (k + (nF + n + 1)) + bs.length from by omega,
          consList_apply_add,
          show k + (nF + n + 1) = (k + (n + 1)) + as₂.length from by omega, consList_apply_add,
          show k + (n + 1) = (k + 1) + ms.length from by omega, consList_apply_add]
        rfl), ← hlenP, range_reverse_map_consList]
  · simp only [List.map_cons, List.map_nil, interp2_bvar]
    rw [consList_apply_add, show nF + n = n + as₂.length from by omega, consList_apply_add,
      show n = 0 + ms.length from by omega, consList_apply_add]
    rfl
  · apply List.ext_getElem
    · simp [hlenM]
    · intro l h1 h2
      have hl : l < n := by simpa using h1
      simp only [List.getElem_map, List.getElem_range, interp2_bvar]
      rw [consList_apply_add, show nF + n - 1 - l = (n - 1 - l) + as₂.length from by omega,
        consList_apply_add, consList_apply_lt' ms _ (by omega),
        show ms.length - 1 - (n - 1 - l) = l from by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

theorem recPrefixBvarsM_ok2 {nP n nF m : Nat} {σ : Nat → V} {a : AVExpr}
    (ha : a ∈ recPrefixBvarsM nP n nF m) : AnnotOk2 V σ a := by
  unfold recPrefixBvarsM at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; trivial
    · rw [List.mem_singleton] at ha; subst ha; trivial
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial

theorem recPrefixBvarsM_validV {nP n nF m : Nat} {σ : Nat → V} {a : AVExpr}
    (ha : a ∈ recPrefixBvarsM nP n nF m) : AnnotValidV V σ a := by
  unfold recPrefixBvarsM at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha; trivial
    · rw [List.mem_singleton] at ha; subst ha; trivial
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial

/-! ## The rule's ih applications at the re-bit telescopes (task #202 A2) -/

omit [SetTheory V] in
theorem ihTeleAtGo_rebit (nF o i l b : Nat) :
    ∀ (k : Nat) (tl : List (Nat × Nat × AVExpr)),
      ihTeleAtGo nF o i l k (rebit b tl) = rebit b (ihTeleAtGo nF o i l k tl)
  | _, [] => rfl
  | k, d :: tl => by
    simp only [rebit_cons, ihTeleAtGo, ihTeleAtGo_rebit nF o i l b (k + 1) tl]

omit [SetTheory V] in
/-- The rule's ih application at a re-bit telescope is the semantic
spelling `ihAppAVb` at the elimination bit with no extras. -/
theorem ihAppAV_rebit (b : Nat) (R : AVExpr) (nP n nF i : Nat) (tl : List (Nat × Nat × AVExpr))
    (Eis : List AVExpr) :
    ihAppAV R nP n nF i (rebit b tl) Eis = ihAppAVb b (fun _ => R) nP n nF 0 i tl Eis := by
  unfold ihAppAV ihAppAVb ihTeleAtR mkLamsC
  rw [ihTeleAtGo_rebit, rebit_map_lam, rebit_length]
  rfl

/-- **The rule's core reads to the minor's fold** at the fields and the
inductive-hypothesis values — the λ-towers over the recursive fields'
telescopes of the leaf at the block, the calls' index values and the
field along the telescope (`sqIhValsK`; a finitary field: the leaf at
the block, the index values and the field). -/
theorem interp_fixRuleCoreAV {ℓ b nP n nF j : Nat} (hbz : ℓ = 0 ↔ b = 0) {as₁ ms as₂ : List V}
    {M : V} {ρ : Nat → V}
    (hlenP : as₁.length = nP) (hlenM : ms.length = n) (hlenF : as₂.length = nF) (hjn : j < n)
    {R : AVExpr} (hRcl : VExpr.bvarsBelow 0 R.erase) {rs : List Bool}
    {tls : List (List (Nat × Nat × AVExpr))} {Eis : List (List AVExpr)} :
    interp2 V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
        (fixRuleCoreAV b R nP nF n j (recIdx rs nF) tls Eis)
      = (as₂ ++ sqIhValsK ℓ (consList as₁ ρ) as₁ ms M (interp2 V ρ R) rs tls Eis nF as₂).foldl
          SetTheory.app (ms.getD j pt) := by
  unfold fixRuleCoreAV
  rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V (consList as₂ (consList ms (cons M (consList as₁ ρ)))))
    (g := SetTheory.app), List.map_append, List.map_map, interp2_bvar,
    show fieldBvars nF = (List.range nF).map (fun k => AVExpr.bvar (nF - 1 - k)) from rfl,
    map_fieldBvars_interp hlenF,
    show nF + n - 1 - j = (n - 1 - j) + as₂.length from by omega, consList_apply_add,
    consList_apply_lt' ms _ (by omega), show ms.length - 1 - (n - 1 - j) = j from by omega]
  congr 2
  unfold sqIhValsK
  apply List.map_congr_left
  intro i hi
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  simp only [Function.comp]
  rw [ihAppAV_rebit]
  have h := interp_ihAppAVb (b := b) (M := M) (ρ := ρ) (ex := []) (Rm := fun _ => R)
    (rV := interp2 V ρ R) hlenP hlenM rfl hlenF hik (fun bs => interp2_closed (V := V) hRcl _ ρ)
    (tls.getD i []) (Eis.getD i [])
  simp only [consList_nil, List.length_nil] at h
  rw [h, lamTower_bit_agree hbz.symm]

/-! ## The law -/

set_option maxHeartbeats 6400000 in
/-- **The recursive recursor rule's law at the readings.** -/
theorem fixRecLawCore {ℓ b w u s nP nF nIdx n j : Nat} (hbz : ℓ = 0 ↔ b = 0)
    {rds ds : List (Nat × Nat × AVExpr)}
    {Fss₀ Fss Ess : List (List AVExpr)} {Ids : List AVExpr} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AVExpr)))} {Eiss : List (List (List AVExpr))} {Es : List AVExpr}
    (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx)
    (hlenDs : ds.length = nP + nF) (hjn : j < n)
    (hFsj : Fss[j]? = some ((ds.drop nP).map (·.2.2))) (hEsj : Ess[j]? = some Es)
    (hEs : Es.length = nIdx)
    {R : AVExpr} (hR : R = directFixRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s)
    (hRcl : VExpr.bvarsBelow 0 R.erase)
    (hokFss : ∀ ρp : Nat → V, Sat2 V (((rds.take nP).map (·.2.2)).reverse) ρp →
      SumFieldsOkB w ρp Fss)
    {lds : List (Nat × AVExpr)}
    (hldsDom : lds.map (·.2) = (rds.take (nP + 1 + n)).map (·.2.2) ++
      (liftDoms (n + 1) 0 (ds.drop nP)).map (·.2.2))
    {Ra : AVExpr}
    (hRa : Ra = mkLamsAV lds (fixRuleCoreAV b R nP nF n j (recIdx (rss.getD j []) nF) (tlss.getD j [])
      (Eiss.getD j [])))
    (hokRa : ∀ ρ : Nat → V, AnnotOkP V ρ Ra)
    {ρ : Nat → V} {xs ys : List AVExpr} (hxl : xs.length = nP + 1 + n + nIdx) (hyl : ys.length = nP + nF)
    (hspR : SpineFit ρ (rds.map (·.2.2))
      ((xs ++ [AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys]).map
        (interp2 V ρ)))
    (hspC : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp2 V ρ)))
    (hplain : ∀ i, i < nP →
      interp2 V ρ (ys.getD i default) = interp2 V ρ (xs.getD i default))
    (hpin : ∀ i, i < nIdx →
      interp2 V (consList (ys.map (interp2 V ρ)) ρ) (Es.getD i default)
        = interp2 V ρ (xs.getD (nP + 1 + n + i) default)) :
    interp2 V ρ (AVExpr.mkAppN R
        (xs ++ [AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys]))
      = interp2 V ρ (AVExpr.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP)) ∧
    ((∀ a ∈ xs, AnnotOkP V ρ a) → (∀ b ∈ ys, AnnotOkP V ρ b) →
      AnnotOkP V ρ (AVExpr.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP))) := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hFsjD : Fss.getD j [] = (ds.drop nP).map (·.2.2) := by
    rw [List.getD_eq_getElem?_getD, hFsj]; rfl
  have hEsjD : Ess.getD j [] = Es := by
    rw [List.getD_eq_getElem?_getD, hEsj]; rfl
  have hjF : j < Fss.length := by rw [hFss]; exact hjn
  -- the constructor's fit, split at the parameters
  have hdsSplit : ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hdsSplit] at hspC
  obtain ⟨as₁, as₂, hys, hsp₁, hsp₂⟩ := spineFit_append_inv hspC
  have hlen₁ : as₁.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlen₂ : as₂.length = nF := by rw [hsp₂.length_eq, hlenFs]
  -- the recursor's fit: the block, the indices, the major
  have hspR' := hspR
  rw [List.map_append, List.map_cons, List.map_nil] at hspR'
  generalize hvs : xs.map (interp2 V ρ) = vs at hspR'
  generalize htv : interp2 V ρ
    (AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys) = t at hspR'
  have hlenvs : vs.length = nP + 1 + n + nIdx := by rw [← hvs, List.length_map, hxl]
  obtain ⟨as₀, is, rfl, hl₀, hli⟩ := kframe_split h hspR'
  rw [hFss] at hl₀
  rw [hIds] at hli
  obtain ⟨bs₁, M, ms, rfl, hlenb₁, hlenm⟩ := block_split hl₀
  -- the K-frame
  have hK := (h.hK ρ _ t hspR').1
  have hKfr : consList (((bs₁ ++ [M]) ++ ms) ++ is) ρ = consList is (consList ms (cons M (consList bs₁ ρ))) :=
    consList_kframe bs₁ M ms is ρ
  have hlenIs' : is.length = Ids.length := by rw [hIds]; exact hli
  have hlenMs' : ms.length = Fss.length := by rw [hFss]; exact hlenm
  have hfrP : frP Fss.length Ids.length (consList is (consList ms (cons M (consList bs₁ ρ))))
      = consList bs₁ ρ := kframe_frP hlenIs' hlenMs'
  have hfrIdx : frameIdx Ids.length (consList is (consList ms (cons M (consList bs₁ ρ)))) = is :=
    kframe_frameIdx hlenIs'
  have hfrMs : frMs Fss.length Ids.length (consList is (consList ms (cons M (consList bs₁ ρ)))) j
      = ms.getD j pt := kframe_frMs hlenIs' hlenMs' hjF
  have hfrK : frKSpine nP Fss.length Ids.length (consList is (consList ms (cons M (consList bs₁ ρ))))
      = (bs₁ ++ [M]) ++ ms := by
    rw [← hKfr]
    exact frKSpine_of nP Fss.length Ids.length (by simp [hlenb₁, hlenMs']; omega) hlenIs' ρ
  -- the parameters, identified
  have hxsv : xs.map (interp2 V ρ) = ((bs₁ ++ [M]) ++ ms) ++ is := hvs
  have hparams : as₁ = bs₁ := by
    have h1 : as₁ = (ys.map (interp2 V ρ)).take nP := by
      rw [hys, List.take_left' hlen₁]
    have h2 : bs₁ = (xs.map (interp2 V ρ)).take nP := by
      rw [hxsv, List.append_assoc, List.append_assoc, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
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
  -- the index values, identified
  have hidxEq : idxValsAt (consList as₁ ρ) Es as₂ = is := by
    apply List.ext_getElem
    · simp [idxValsAt, hEs, hli]
    · intro i h1 h2
      have hi : i < nIdx := by simpa [idxValsAt, hEs] using h1
      simp only [idxValsAt, List.getElem_map]
      have h := hpin i hi
      rw [hys, consList_append, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some] at h
      rw [h]
      have hx : (xs.map (interp2 V ρ))[nP + 1 + n + i]? = is[i]? := by
        rw [hxsv]
        simp only [List.append_assoc]
        rw [List.getElem?_append_right (by simp [hlen₁]; omega),
          List.getElem?_append_right (by simp [hlen₁]; omega),
          List.getElem?_append_right (by simp [hlen₁, hlenm]; omega)]
        congr 1
        simp [hlen₁, hlenm]
        omega
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega), Option.map_some,
        List.getElem?_eq_getElem (by omega)] at hx
      exact Option.some.inj hx
  -- the parameter frame satisfies the parameters
  have hsatP : Sat2 V (((rds.take nP).map (·.2.2)).reverse) (consList as₁ ρ) := by
    have hpre := spineFit_prefix (as := as₁) (bs := [M] ++ ms ++ is ++ [t]) (by
      rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]; exact hspR')
    rw [hlen₁, ← List.map_take] at hpre
    have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) hpre
    rwa [List.append_nil] at this
  -- the constructor leaf's value
  have hleafC' : directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)
      = directSumMkAV w j (ds.take nP ++ ds.drop nP) ((ds.drop nP).map (·.2.2)) (uChains Fss) := by
    rw [List.take_append_drop]
  have hokU : SumFieldsOkB w (consList as₁ ρ) (uChains Fss) := SumFieldsOkB_uChains (hokFss _ hsatP)
  have hjU : (uChains Fss)[j]? = some ((ds.drop nP).map (·.2.2) ++ [idxEqAV []]) := by
    rw [uChains_getElem?, hFsj]; rfl
  have hmkv : t = if w = 0 then (pt : V) else inj j (mkTower (as₂ ++ [pt])) := by
    rw [← htv, interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app), hys,
      hleafC']
    rcases Nat.eq_zero_or_pos w with hw0 | hwpos
    · rw [hw0, directSumMkAV_zero, foldl_app_pt_sum, if_pos rfl]
    · have hw : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
      rw [directSumMkAV_fold hw hsp₁ hsp₂ hokU hjU, if_neg hw]
  -- the right-hand side's fit
  have hys₂ : (ys.map (interp2 V ρ)).drop nP = as₂ := by rw [hys, List.drop_left' hlen₁]
  have hxs₁ : (xs.take (nP + 1 + n)).map (interp2 V ρ) = (as₁ ++ [M]) ++ ms := by
    rw [List.map_take, hxsv, List.take_append_of_le_length (by simp [hlen₁, hlenm]; omega),
      List.take_of_length_le (by simp [hlen₁, hlenm]; omega)]
  have hfit : SpineFit ρ (lds.map (·.2)) ((xs.take (nP + 1 + n) ++ ys.drop nP).map (interp2 V ρ)) := by
    rw [hldsDom, List.map_append (f := interp2 V ρ) (l₁ := xs.take (nP + 1 + n)) (l₂ := ys.drop nP),
      List.map_drop, hys₂, hxs₁]
    refine SpineFit.append ?_ ?_
    · have hpre := spineFit_prefix (as := (as₁ ++ [M]) ++ ms) (bs := is ++ [t]) (by
        rw [← List.append_assoc]; exact hspR')
      rw [show ((as₁ ++ [M]) ++ ms).length = nP + 1 + n from by simp [hlen₁, hlenm]; omega,
        ← List.map_take] at hpre
      exact hpre
    · rw [spineFit_liftDoms, consList_append, consList_append, consList_cons, consList_nil,
        show n + 1 = ms.length + 1 from by omega, shiftE_consList_add ms 1, shiftE_succ_cons,
        shiftE_zero_zero]
      exact hsp₂
  -- the right-hand side's frame
  have hframeR : consList ((xs.take (nP + 1 + n) ++ ys.drop nP).map (interp2 V ρ)) ρ
      = consList as₂ (consList ms (cons M (consList as₁ ρ))) := by
    rw [List.map_append (f := interp2 V ρ) (l₁ := xs.take (nP + 1 + n)) (l₂ := ys.drop nP),
      List.map_drop, hys₂, hxs₁, consList_append, consList_append, consList_append, consList_cons,
      consList_nil]
  -- the right-hand side: the rule's fold to the core
  have hRHS : interp2 V ρ (AVExpr.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP))
      = interp2 V (consList as₂ (consList ms (cons M (consList as₁ ρ))))
          (fixRuleCoreAV b R nP nF n j (recIdx (rss.getD j []) nF) (tlss.getD j []) (Eiss.getD j [])) := by
    rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app), hRa,
      mkLamsAV_fold_graded (by rw [← hRa]; exact (hokRa ρ).1) hfit, hframeR]
  -- the left-hand side: the recursor's fold
  have hLHS : interp2 V ρ (AVExpr.mkAppN R
        (xs ++ [AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys]))
      = ((((as₁ ++ [M]) ++ ms) ++ is) ++ [t]).foldl SetTheory.app (interp2 V ρ R) := by
    rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app),
      List.map_append, List.map_cons, List.map_nil, hxsv, htv]
  -- the minor at the leaf frame
  have hminor : consList as₂ (consList ms (cons M (consList as₁ ρ))) (nF + n - 1 - j) = ms.getD j pt := by
    rw [show nF + n - 1 - j = (n - 1 - j) + as₂.length from by omega, consList_apply_add,
      consList_apply_lt' ms _ (by omega), show ms.length - 1 - (n - 1 - j) = j from by omega]
  refine ⟨?_, ?_⟩
  · rw [hLHS, hRHS]
    by_cases hℓ0 : ℓ = 0
    · -- both sides are the point: the minor's and the recursor's values are
      have hmpt : ms.getD j pt = pt := by
        have := hK.hyp.minor_pt hℓ0 hjF
        rw [hKfr] at this
        rw [← hfrMs]
        exact this
      have hRpt : interp2 V ρ R = pt := by
        rw [hR]
        have hmem := directFixRecAVI_mem h ρ
        refine eq_pt_of_mem_univZero ?_ hmem
        cases hrds : rds with
        | nil => have := h.hlen; rw [hrds] at this; simp at this
        | cons d rest =>
          rw [hrds] at h
          show piR d.2.1 _ _ ∈ˢ _
          rw [(h.hz d List.mem_cons_self).mp hℓ0]
          exact piR_zero_mem_univZero
      unfold fixRuleCoreAV
      rw [interp2_mkAppN, interp2_bvar, hminor, hmpt, hRpt, foldl_app_pt_sum,
        ← List.foldl_map (f := interp2 V (consList as₂ (consList ms (cons M (consList as₁ ρ)))))
          (g := SetTheory.app), foldl_app_pt_sum]
    · by_cases hw : w = 0
      · -- the squash regime (task #202 A2): the recursor's iota at the
        -- proof point, the fields the source spine
        subst hw
        have htpt : t = pt := by rw [hmkv, if_pos rfl]
        subst htpt
        have hiota := directFixRecAVI_iota_sq h rfl hℓ0 ρ hlen₁ hlenMs' hlenIs' hspR'
        rw [← hR] at hiota
        obtain ⟨hsingle, -, hprop⟩ := hK.hsq rfl hℓ0
        rw [hKfr, hfrP] at hprop
        have hj0 : j = 0 := by omega
        subst hj0
        have has₂ : as₂ = srcVals is (srcList (Ess.getD 0 []) (Fss.getD 0 []).length) :=
          Lech.Semantics.srcVals_of_fit hprop (by rw [hFsjD]; exact hsp₂) (by rw [hEsjD]; exact hidxEq)
        rw [hiota, interp_fixRuleCoreAV hbz hlen₁ hlenm hlen₂ hjn hRcl, ← has₂, hFsjD, hlenFs]
      · have hfin := h.hfin.resolve_right hw
        have hmaj : t = inj j (mkTower (as₂ ++ [pt])) := by rw [hmkv, if_neg hw]
        have hiota := directFixRecAVI_iota h hw hℓ0 ρ hspR' hjF
          (fs := as₂) (by rw [hFsjD, hlen₂, hlenFs]) hmaj
        rw [← hR] at hiota
        rw [hiota, hKfr, hfrMs, hfrK, hfrP, hFsjD, hlenFs,
          interp_fixRuleCoreAV hbz hlen₁ hlenm hlen₂ hjn hRcl, sqIhValsK_fin (fun i => hfin j i)]
  · intro hxs_ok hys_ok
    refine mkAppN_okP_of_lam (hokRa ρ) ?_ (by rw [← hRa]; exact (hokRa ρ).1)
      (Or.inr (by rw [hRa])) hfit
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hxs_ok a (List.mem_of_mem_take h)
    · exact hys_ok a (List.mem_of_mem_drop h)

end Lech.SetP
