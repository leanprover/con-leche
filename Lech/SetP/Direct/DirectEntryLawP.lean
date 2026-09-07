import Lech.SetP.Direct.DirectBodyFramesP

/-!
# The projection entry's law (task #175 W4c, P3 module 7, part 5)

The three clauses of `TowerEntryLawP`, semantically (at one
assignment, over the block's data alone):

* **(A) the typing law** (`entryTypingCore`): a member of the family
  instance projects into the body's residual at the parameters and
  the member — the graph regime by the tower's projection membership,
  the squash regime by the point's membership in the proof field at
  the point prefix (the coarse guard's content).  The residual's
  facts are premised on the **frame** (the subject a member of the
  family at the parameters; task #175 S1: the body is read under
  dummy binders, so no binder context is available to satisfy);
* **(B) the iota law** (`entryIotaCore`): the projection of a graded
  constructor application is the selected field — the application's
  grading fits the constructor leaf, whose fold is the tupler;
* **(C) the η law** (`entryEtaCore`): a member is the constructor at
  the parameters and its own projections (`towerSet_elim`), the point
  at squash.

`stageTable` (`DirectStageTableP.lean`) assembles them into
`TowerEntryLawP` at the table's extension.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta ProjEntry projFnName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## (A) the typing law -/

theorem entryTypingCore {w nP nF i : Nat} {pps ds eds : List (Nat × Nat × AVExpr)}
    {R : AVExpr} {sorts : List Level} {ψ : Name → Nat}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP) (hlenEds : eds.length = nP + 1)
    (hpok : ∀ ρ : Nat → V, ParamsOkT w ρ ((ds.drop nP).map (·.2.2)) pps)
    (hiff : ∀ ρ : Nat → V, Sat2 V (pps.map (·.2.2)).reverse ρ ↔
      Sat2 V ((ds.take nP).map (·.2.2)).reverse ρ)
    (hbound : ∀ ρ : Nat → V, Sat2 V ((ds.take nP).map (·.2.2)).reverse ρ → w ≠ 0 →
      FieldsBound w ρ ((ds.drop nP).map (·.2.2)))
    (hsorts : ∀ ρ : Nat → V, Sat2 V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp2 V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    {used : Nat → Bool}
    (hguard : w = 0 → (sorts.getD i .zero).eval ψ = 0 ∧
      ∀ j, j < i → used j = true → (sorts.getD j .zero).eval ψ = 0)
    (hfree : ∀ j, j < i → used j = false →
      ∃ X : AVExpr, ((ds.drop nP).map (·.2.2)).getD i default = X.liftN 1 (i - 1 - j))
    (hi : i < nF)
    (hres : ∀ ρ : Nat → V,
      ρ 0 ∈ˢ towerSet w (teleOfFields (fun j => ρ (j + 1)) ((ds.drop nP).map (·.2.2))) →
      Sat2 V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
      interp2 V ρ R
        = interp2 V (consList (projList i (ρ 0)) (fun j => ρ (j + 1)))
            (((ds.drop nP).map (·.2.2)).getD i default))
    (hokR : ∀ ρ : Nat → V,
      ρ 0 ∈ˢ towerSet w (teleOfFields (fun j => ρ (j + 1)) ((ds.drop nP).map (·.2.2))) →
      Sat2 V ((ds.take nP).map (·.2.2)).reverse (fun j => ρ (j + 1)) →
      AnnotOkP V ρ R) :
    ∀ (ρ : Nat → V) (vs : List AVExpr) (x rest : AVExpr),
      vs.length = nP →
      AnnotOkP V ρ (AVExpr.mkAppN (directTyAV w pps ((ds.drop nP).map (·.2.2))) vs) →
      AnnotOkP V ρ x →
      interp2 V ρ x ∈ˢ interp2 V ρ
        (AVExpr.mkAppN (directTyAV w pps ((ds.drop nP).map (·.2.2))) vs) →
      Lech.SetP.AVExpr.peelPis (mkPisAV eds R) (vs ++ [x]) = some rest →
      AnnotOkP V ρ (projAV i x) ∧ AnnotOkP V ρ rest ∧
        interp2 V ρ (projAV i x) ∈ˢ interp2 V ρ rest := by
  intro ρ vs x rest hlenVs hokApp hokx hmem hpeel
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  -- the parameter fit
  have hsp : SpineFit ρ (pps.map (·.2.2)) (vs.map (interp2 V ρ)) := by
    have h := spineFit_of_okP_mkAppN_lam (lds := pps.map fun d => (w + 1, d.2.2))
      (b := towerBodyAV w ((ds.drop nP).map (·.2.2))) (σ := ρ)
      (fun d hd => by obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd; exact Nat.succ_ne_zero w)
      hokApp rfl (by simp [hlenVs, hlenPps])
    simpa [List.map_map, Function.comp_def] using h
  have hlenAs : (vs.map (interp2 V ρ)).length = nP := by simp [hlenVs]
  -- the member of the carrier
  have hx : interp2 V ρ x ∈ˢ towerSet w
      (teleOfFields (consList (vs.map (interp2 V ρ)) ρ) ((ds.drop nP).map (·.2.2))) := by
    rw [interp2_mkAppN_foldl, formerFold (hpok ρ) hsp] at hmem
    exact hmem
  -- the constructor's parameter frame
  have hspC : SpineFit ρ ((ds.take nP).map (·.2.2)) (vs.map (interp2 V ρ)) :=
    (spineFit_iff_of_sat2_iff (by simp [hlenPps, hlenDs]) hiff ρ _ (by simp [hlenVs, hlenPps])).mp hsp
  have hsatC : Sat2 V ((ds.take nP).map (·.2.2)).reverse (consList (vs.map (interp2 V ρ)) ρ) := by
    have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) hspC
    rwa [List.append_nil] at this
  -- the frame at the subject's chain
  have hchain : chainP V ρ (vs ++ [x]) = cons (interp2 V ρ x) (consList (vs.map (interp2 V ρ)) ρ) := by
    unfold chainP
    rw [consN_eq_consList, List.map_append, consList_append]
    rfl
  have hframeX : (cons (interp2 V ρ x) (consList (vs.map (interp2 V ρ)) ρ)) 0 ∈ˢ towerSet w
      (teleOfFields (fun j => (cons (interp2 V ρ x) (consList (vs.map (interp2 V ρ)) ρ)) (j + 1))
        ((ds.drop nP).map (·.2.2))) := hx
  have hframeS : Sat2 V ((ds.take nP).map (·.2.2)).reverse
      (fun j => (cons (interp2 V ρ x) (consList (vs.map (interp2 V ρ)) ρ)) (j + 1)) := hsatC
  -- the residual
  have hrest : rest = Lech.SetP.AVExpr.instSeq (vs ++ [x]) nP R := by
    have h := peelPis_of_piTeleP (nP + 1) (by rw [← hlenEds]; exact piTeleP_mkPisAV eds R)
      (ws := vs ++ [x]) (by simp [hlenVs])
    rw [hpeel] at h
    have := Option.some.inj h
    rwa [Nat.add_sub_cancel] at this
  have hlen' : Lech.SetP.AVExpr.instSeq (vs ++ [x]) nP R
      = Lech.SetP.AVExpr.instSeq (vs ++ [x]) ((vs ++ [x]).length - 1) R := by
    simp [hlenVs]
  have hinterpRest : interp2 V ρ rest
      = interp2 V (consList (projList i (interp2 V ρ x)) (consList (vs.map (interp2 V ρ)) ρ))
          (((ds.drop nP).map (·.2.2)).getD i default) := by
    rw [hrest, hlen', interp2_instSeq, hchain, hres _ hframeX hframeS]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · -- the projection's grading
    refine ⟨?_, projAV_validV hokx.2⟩
    by_cases hw : w = 0
    · subst hw
      obtain ⟨hpt, -⟩ := towerSet_zero_elim _ hx
      exact annotOk2_projAV_pt hokx.1 hpt
    · exact annotOk2_projAV_tower (hbound _ hsatC hw) hx hokx.1 rfl (by rw [hlenFs]; exact hi)
  · -- the residual's grading
    rw [hrest, hlen']
    refine annotOkP_instSeq _ ?_ ?_
    · intro w' hw'
      rcases List.mem_append.mp hw' with h | h
      · exact AnnotOkP_mkAppN_args vs hokApp w' h
      · rw [List.mem_singleton] at h; subst h; exact hokx
    · rw [hchain]; exact hokR _ hframeX hframeS
  · -- the membership
    rw [hinterpRest, projAV_interp]
    by_cases hw : w = 0
    · -- squash: the point in the proof field at the point prefix,
      -- which agrees with a fitting prefix at every used slot
      subst hw
      obtain ⟨hpt, as', hfits⟩ := towerSet_zero_elim _ hx
      have hspAs := fitsS_teleOfFields.mp hfits
      obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hspAs (by rw [hlenFs]; exact hi)
      have hz := hsorts _ hsatC i hi _ hpre
      rw [(hguard rfl).1] at hz
      have hval := mem_univ_zero hz hnext
      rw [hval] at hnext
      rw [hpt, projS_pt, projList_pt]
      have hlenTake : (as'.take i).length = i := spineFit_take_length hspAs (by rw [hlenFs]; omega)
      rw [interp2_congr_lifts i
        (free_of_diff hlenDs hi (hsorts _ hsatC) (hguard rfl).2 hfree hspAs)
        (consList_prefix_agree hlenTake _).2]
      exact hnext
    · -- graph: the tower's projection membership
      have h := projS_mem_teleOfFields (fun h0 => absurd h0 hw) hx (i := i) (by rw [hlenFs]; exact hi)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenFs]; exact hi)]
      exact h

/-! ## (B) the iota law -/

theorem entryIotaCore {w nP nF i : Nat} {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V}
    (hw : w ≠ 0) (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hbound : ∀ ρ : Nat → V, Sat2 V ((ds.take nP).map (·.2.2)).reverse ρ → w ≠ 0 →
      FieldsBound w ρ ((ds.drop nP).map (·.2.2)))
    (ys : List AVExpr) (hlen : ys.length = nP + nF)
    (hok : AnnotOkP V ρ (AVExpr.mkAppN (directMkAV w ds ((ds.drop nP).map (·.2.2))) ys)) :
    interp2 V ρ (projAV i (AVExpr.mkAppN (directMkAV w ds ((ds.drop nP).map (·.2.2))) ys))
      = interp2 V ρ (ys.getD (nP + i) default) := by
  have hsp : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp2 V ρ)) := by
    have h := spineFit_of_okP_mkAppN_lam (lds := ds.map fun d => (w, d.2.2))
      (b := mkTowerGo w ((ds.drop nP).map (·.2.2))) (σ := ρ)
      (fun d hd => by obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd; exact hw)
      hok rfl (by simp [hlen, hlenDs])
    simpa [List.map_map, Function.comp_def] using h
  rw [show ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) from by
    rw [← List.map_append, List.take_append_drop]] at hsp
  obtain ⟨as, bs, heq, hsp₁, hsp₂⟩ := spineFit_append_inv hsp
  have hlenAs : as.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlenBs : bs.length = nF := by rw [hsp₂.length_eq]; simp [hlenDs]
  have hsat : Sat2 V ((ds.take nP).map (·.2.2)).reverse (consList as ρ) := by
    have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  have hfold := directMkAV_fold hw hsp₁ hsp₂ (hbound _ hsat hw)
  rw [List.take_append_drop] at hfold
  rw [projAV_interp, interp2_mkAppN_foldl, heq, hfold,
    projS_mkTower i bs (by rw [hlenBs]; exact hi)]
  -- the selected argument
  have hlt : nP + i < ys.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  have h1 : (ys.map (interp2 V ρ))[nP + i]? = some (interp2 V ρ ys[nP + i]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
  rw [heq, List.getElem?_append_right (by omega), hlenAs, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)] at h1
  exact Option.some.inj h1

/-- **The iota law at a squash instantiation** (task #175 W6): the
constructor application is the point, so its projection is the point
(`projS_pt`); the selected field inhabits its domain by the certified
spine's fit, and that domain is a proposition (its sort is `0`, from
the guard), so the field is the point too. -/
theorem entryIotaCoreZero {nP nF i : Nat} {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V}
    {sorts : List Level} {ψ : Name → Nat}
    (hlenDs : ds.length = nP + nF) (hi : i < nF)
    (hsorts : ∀ ρ : Nat → V, Sat2 V ((ds.take nP).map (·.2.2)).reverse ρ →
      ∀ j, j < nF → ∀ as : List V,
        SpineFit ρ (((ds.drop nP).map (·.2.2)).take j) as →
        interp2 V (consList as ρ) (((ds.drop nP).map (·.2.2)).getD j default)
          ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V))
    (hz : (sorts.getD i .zero).eval ψ = 0)
    (ys : List AVExpr) (hlen : ys.length = nP + nF)
    (hsp : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp2 V ρ))) :
    interp2 V ρ (projAV i (AVExpr.mkAppN (directMkAV 0 ds ((ds.drop nP).map (·.2.2))) ys))
      = interp2 V ρ (ys.getD (nP + i) default) := by
  -- the projection of the point
  rw [projAV_interp, interp2_mkAppN_foldl, directMkAV_zero, foldl_app_pt, projS_pt]
  -- the selected field: a member of a proposition's domain
  rw [show ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) from by
    rw [← List.map_append, List.take_append_drop]] at hsp
  obtain ⟨as, bs, heq, hsp₁, hsp₂⟩ := spineFit_append_inv hsp
  have hlenAs : as.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlenBs : bs.length = nF := by rw [hsp₂.length_eq]; simp [hlenDs]
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hsat : Sat2 V ((ds.take nP).map (·.2.2)).reverse (consList as ρ) := by
    have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) hsp₁
    rwa [List.append_nil] at this
  obtain ⟨hpre, hnext⟩ := spineFit_prefix_next hsp₂ (by rw [hlenFs]; exact hi)
  have hz' := hsorts _ hsat i hi _ hpre
  rw [hz] at hz'
  have hval : bs.getD i pt = pt := mem_univ_zero hz' hnext
  -- the selected argument is `bs[i]`
  have hlt : nP + i < ys.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  have h1 : (ys.map (interp2 V ρ))[nP + i]? = some (interp2 V ρ ys[nP + i]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
  rw [heq, List.getElem?_append_right (by omega), hlenAs, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)] at h1
  have h2 : bs[i] = bs.getD i pt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenBs]; exact hi)]
    rfl
  rw [← Option.some.inj h1, h2, hval]

/-! ## (C) the η law -/

theorem entryEtaCore {w nP nF : Nat} {pps ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V}
    (hlenDs : ds.length = nP + nF) (hlenPps : pps.length = nP)
    (hpok : ∀ ρ : Nat → V, ParamsOkT w ρ ((ds.drop nP).map (·.2.2)) pps)
    (hiff : ∀ ρ : Nat → V, Sat2 V (pps.map (·.2.2)).reverse ρ ↔
      Sat2 V ((ds.take nP).map (·.2.2)).reverse ρ)
    (hbound : ∀ ρ : Nat → V, Sat2 V ((ds.take nP).map (·.2.2)).reverse ρ → w ≠ 0 →
      FieldsBound w ρ ((ds.drop nP).map (·.2.2)))
    (ts : List V) (x : V) (hlen : ts.length = nP)
    (hsp : SpineFit ρ (pps.map (·.2.2)) ts)
    (hx : x ∈ˢ ts.foldl SetTheory.app (interp2 V ρ (directTyAV w pps ((ds.drop nP).map (·.2.2))))) :
    x = (ts ++ (List.range nF).map fun j => projS j x).foldl SetTheory.app
      (interp2 V ρ (directMkAV w ds ((ds.drop nP).map (·.2.2)))) := by
  rw [formerFold (hpok ρ) hsp] at hx
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  by_cases hw : w = 0
  · subst hw
    obtain ⟨hpt, -⟩ := towerSet_zero_elim _ hx
    rw [hpt, directMkAV_zero, foldl_app_pt]
  · obtain ⟨hspF, heta⟩ := towerSet_elim_teleOfFields hw hx
    rw [hlenFs] at hspF heta
    have hsp₁ : SpineFit ρ ((ds.take nP).map (·.2.2)) ts :=
      (spineFit_iff_of_sat2_iff (by simp [hlenPps, hlenDs]) hiff ρ ts (by simp [hlen, hlenPps])).mp hsp
    have hsat : Sat2 V ((ds.take nP).map (·.2.2)).reverse (consList ts ρ) := by
      have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) hsp₁
      rwa [List.append_nil] at this
    have hfold := directMkAV_fold hw hsp₁ hspF (hbound _ hsat hw)
    rw [List.take_append_drop] at hfold
    rw [← projList_eq_map_range, hfold]
    exact heta

end Lech.SetP
