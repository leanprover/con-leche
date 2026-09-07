import Lech.SetP.Direct.DirectEntryKitP

/-!
# The projection entry's kit, continued (task #175 W4c, P3 module 7, part 3)

* the grading is a congruence below a variable bound
  (`AnnotOkP_congr_below`, `interp2_congr_below`'s twin for the two
  truthfulness halves);
* the field chain's per-field grading at a fitting prefix
  (`fieldsOkB_getD`, `fieldsValid_getD`);
* the entry residual's chain frame: the readings of the opened
  parameters and the earlier projections, and their value chain
  against the subject's projection spine (`chainP_entry_agree`).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.Verify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Grading below a bound -/

omit [SetTheory V] in
theorem cons_agree_below {k : Nat} {ρ ρ' : Nat → V} (hag : ∀ i, i < k → ρ i = ρ' i)
    (x : V) : ∀ i, i < k + 1 → cons x ρ i = cons x ρ' i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi)

theorem AnnotOk2_congr_below :
    ∀ (e : AVExpr) (k : Nat) (ρ ρ' : Nat → V),
      VExpr.bvarsBelow k e.erase → (∀ i, i < k → ρ i = ρ' i) →
      (AnnotOk2 V ρ e ↔ AnnotOk2 V ρ' e) := by
  intro e
  induction e with
  | bvar i => intros; simp
  | sort u => intros; simp
  | const c us => intros; simp
  | prf => intros; simp
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    rw [AnnotOk2_app, AnnotOk2_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag,
      interp2_congr_below V f k ρ ρ' hb.1 hag, interp2_congr_below V a k ρ ρ' hb.2 hag]
  | lam v A b ihA ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotOk2_lam, AnnotOk2_lam, ihA k ρ ρ' hb.1 hag,
      interp2_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2, B, hB, hB0⟩
      refine ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx),
        B, fun x hx => ?_, hB0⟩
      rw [← interp2_congr_below V b (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact hB x hx
    · rintro ⟨h1, h2, B, hB, hB0⟩
      refine ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx),
        B, fun x hx => ?_, hB0⟩
      rw [interp2_congr_below V b (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact hB x hx
  | pi u v A B ihA ihB =>
    intro k ρ ρ' hb hag
    rw [AnnotOk2_pi, AnnotOk2_pi, ihA k ρ ρ' hb.1 hag,
      interp2_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx)⟩
  | letE T v b ihT ihv ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotOk2_letE, AnnotOk2_letE, ihT k ρ ρ' hb.1 hag, ihv k ρ ρ' hb.2.1 hag,
      interp2_congr_below V v k ρ ρ' hb.2.1 hag,
      ihb (k + 1) _ _ hb.2.2 (cons_agree_below hag _)]
  | eqE T a b ihT iha ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotOk2_eqE, AnnotOk2_eqE, iha k ρ ρ' hb.2.1 hag, ihb k ρ ρ' hb.2.2 hag]
  | proj i e ihe =>
    intro k ρ ρ' hb hag
    rw [AnnotOk2_proj, AnnotOk2_proj, ihe k ρ ρ' hb hag, interp2_congr_below V e k ρ ρ' hb hag]

theorem AnnotValidV_congr_below :
    ∀ (e : AVExpr) (k : Nat) (ρ ρ' : Nat → V),
      VExpr.bvarsBelow k e.erase → (∀ i, i < k → ρ i = ρ' i) →
      (AnnotValidV V ρ e ↔ AnnotValidV V ρ' e) := by
  intro e
  induction e with
  | bvar i => intros; simp [AnnotValidV]
  | sort u => intros; simp [AnnotValidV]
  | const c us => intros; simp [AnnotValidV]
  | prf => intros; simp [AnnotValidV]
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    rw [AnnotValidV_app, AnnotValidV_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag]
  | lam v A b ihA ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotValidV_lam, AnnotValidV_lam, ihA k ρ ρ' hb.1 hag,
      interp2_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (ihb (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx)⟩
  | pi u v A B ihA ihB =>
    intro k ρ ρ' hb hag
    rw [AnnotValidV_pi, AnnotValidV_pi, ihA k ρ ρ' hb.1 hag,
      interp2_congr_below V A k ρ ρ' hb.1 hag]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mp (h2 x hx),
        fun h0 x hx => ?_⟩
      rw [← interp2_congr_below V B (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact h3 h0 x hx
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun x hx => (ihB (k + 1) _ _ hb.2 (cons_agree_below hag x)).mpr (h2 x hx),
        fun h0 x hx => ?_⟩
      rw [interp2_congr_below V B (k + 1) _ _ hb.2 (cons_agree_below hag x)]
      exact h3 h0 x hx
  | letE T v b ihT ihv ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotValidV_letE, AnnotValidV_letE, ihT k ρ ρ' hb.1 hag, ihv k ρ ρ' hb.2.1 hag,
      interp2_congr_below V v k ρ ρ' hb.2.1 hag,
      ihb (k + 1) _ _ hb.2.2 (cons_agree_below hag _)]
  | eqE T a b ihT iha ihb =>
    intro k ρ ρ' hb hag
    rw [AnnotValidV_eqE, AnnotValidV_eqE, iha k ρ ρ' hb.2.1 hag, ihb k ρ ρ' hb.2.2 hag]
  | proj i e ihe =>
    intro k ρ ρ' hb hag
    rw [AnnotValidV_proj, AnnotValidV_proj, ihe k ρ ρ' hb hag]

theorem AnnotOkP_congr_below (e : AVExpr) (k : Nat) (ρ ρ' : Nat → V)
    (hb : VExpr.bvarsBelow k e.erase) (hag : ∀ i, i < k → ρ i = ρ' i) :
    AnnotOkP V ρ e ↔ AnnotOkP V ρ' e := by
  unfold AnnotOkP
  rw [AnnotOk2_congr_below e k ρ ρ' hb hag, AnnotValidV_congr_below e k ρ ρ' hb hag]

/-! ## The field chain, indexed -/

theorem fieldsValid_drop :
    ∀ {Fs₁ : List AVExpr} {as : List V} {Fs₂ : List AVExpr} {ρ : Nat → V},
      FieldsValid ρ (Fs₁ ++ Fs₂) → SpineFit ρ Fs₁ as →
      FieldsValid (consList as ρ) Fs₂
  | [], [], _, _, h, _ => h
  | [], _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, [], _, _, _, hsp => hsp.elim
  | F :: Fs₁, a :: as, Fs₂, ρ, h, hsp => by
    rw [consList_cons]
    exact fieldsValid_drop (h.2 a hsp.1) hsp.2

/-- Field `j`'s domain is graded at every fitting prefix. -/
theorem fieldsOkB_getD {w : Nat} {Fs : List AVExpr} {ρ : Nat → V}
    (h : FieldsOkB w ρ Fs) {j : Nat} (hj : j < Fs.length) {bs : List V}
    (hsp : SpineFit ρ (Fs.take j) bs) :
    AnnotOk2 V (consList bs ρ) (Fs.getD j default) := by
  have hsplit : Fs = Fs.take j ++ Fs.drop j := (List.take_append_drop j Fs).symm
  rw [hsplit] at h
  have h2 := FieldsOkB.drop h hsp
  rw [List.drop_eq_getElem_cons hj] at h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact h2.1

theorem fieldsValid_getD {Fs : List AVExpr} {ρ : Nat → V}
    (h : FieldsValid ρ Fs) {j : Nat} (hj : j < Fs.length) {bs : List V}
    (hsp : SpineFit ρ (Fs.take j) bs) :
    AnnotValidV V (consList bs ρ) (Fs.getD j default) := by
  have hsplit : Fs = Fs.take j ++ Fs.drop j := (List.take_append_drop j Fs).symm
  rw [hsplit] at h
  have h2 := fieldsValid_drop h hsp
  rw [List.drop_eq_getElem_cons hj] at h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact h2.1

/-! ## The residual's chain frame -/

/-- The readings of the opened parameters at the entry's full depth. -/
def entryParamBvars (nP : Nat) : List AVExpr :=
  (List.range nP).map fun k => AVExpr.bvar (nP - k)

/-- The readings of the earlier projections of the subject. -/
def entryProjAVs (i : Nat) : List AVExpr :=
  (List.range i).map fun j => projAV j (.bvar 0)

omit [SetTheory V] in
theorem entryParamBvars_length (nP : Nat) : (entryParamBvars nP).length = nP := by
  simp [entryParamBvars]

omit [SetTheory V] in
theorem entryProjAVs_length (i : Nat) : (entryProjAVs i).length = i := by
  simp [entryProjAVs]

/-- The opened parameters read to `entryParamBvars` at depth `nP + 1`. -/
theorem denoteSpineP_entryParams {acval : Name → (Name → Nat) → AVExpr} {env : Env}
    {φ : Name → Nat} {nP : Nat} {fvsP : List Expr}
    (hidx : ∀ (k : Nat) (x : Expr), fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty)
    (hlen : fvsP.length = nP) :
    DenoteSpineP acval env φ (nP + 1) fvsP (entryParamBvars nP) := by
  have h := denoteSpineP_fvars (acval := acval) (env := env) (φ := φ) (nP + 1) fvsP 0
    (fun k x hx => by obtain ⟨ty, rfl⟩ := hidx k x hx; exact ⟨ty, by rw [Nat.zero_add]⟩)
  rw [hlen] at h
  have e : ((List.range nP).map fun k => AVExpr.bvar (nP + 1 - 1 - (0 + k)))
      = entryParamBvars nP := by
    unfold entryParamBvars
    apply List.map_congr_left
    intro k _
    congr 1
    omega
  rw [e] at h
  exact h

/-- The earlier projections of the subject read to `entryProjAVs` at
depth `nP + 1`, through the stored tower entries. -/
theorem denoteSpineP_entryProjs {acval : Name → (Name → Nat) → AVExpr} {env : Env}
    {φ : Name → Nat} {nP : Nat} {T : Name} {sdom : Expr}
    (hprev : ∀ j, j < i → ∃ entry, env.findProj? T j = some entry) :
    DenoteSpineP acval env φ (nP + 1)
      ((List.range i).map fun j => Expr.proj T j (.fvar nP sdom)) (entryProjAVs i) := by
  unfold entryProjAVs
  suffices ∀ (l : List Nat), (∀ j ∈ l, j < i) →
      DenoteSpineP acval env φ (nP + 1)
        (l.map fun j => Expr.proj T j (.fvar nP sdom))
        (l.map fun j => projAV j (.bvar 0)) from
    this (List.range i) (fun j hj => List.mem_range.mp hj)
  intro l
  induction l with
  | nil => intro _; exact .nil
  | cons j l ih =>
    intro hl
    obtain ⟨entry, hfe⟩ := hprev j (hl j List.mem_cons_self)
    simp only [List.map_cons]
    refine .cons ?_ (ih fun j' hj' => hl j' (List.mem_cons_of_mem _ hj'))
    rw [denoteP_proj_tower hfe (denoteP_fvar acval (nP + 1) nP sdom),
      show nP + 1 - 1 - nP = 0 from by omega]

/-- **The chain frame agrees with the projection spine's frame** below
the field's depth: the parameter readings pick the frame's parameter
values, the projection readings the subject's projections. -/
theorem chainP_entry_agree (nP i : Nat) (ρ : Nat → V) :
    ∀ n, n < nP + i →
      chainP V ρ (entryParamBvars nP ++ entryProjAVs i) n
        = consList (projList i (ρ 0)) (fun j => ρ (j + 1)) n := by
  intro n hn
  have hlen : (entryParamBvars nP ++ entryProjAVs i).length = nP + i := by
    simp [entryParamBvars_length, entryProjAVs_length]
  rw [chainP_lt (by rw [hlen]; exact hn), hlen]
  rcases Nat.lt_or_ge n i with hni | hni
  · -- a projection slot
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by rw [entryParamBvars_length]; omega), entryParamBvars_length]
    unfold entryProjAVs
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, projAV_interp, interp2_bvar]
    rw [consList_apply_lt _ _ _ (by rw [projList_length]; exact hni), projList_length,
      projList_eq_map_range, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    congr 1
    omega
  · -- a parameter slot
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left
      (by rw [entryParamBvars_length]; omega)]
    unfold entryParamBvars
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, interp2_bvar]
    have := consList_apply_add (projList i (ρ 0)) (fun j => ρ (j + 1)) (n - i)
    rw [projList_length, show n - i + i = n from by omega] at this
    rw [this]
    congr 1
    omega

end Lech.SetP
