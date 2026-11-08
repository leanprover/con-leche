module

public import InLeanProof.PassTail
import InLeanProof.DeclGuards

/-!
# O7-classes: the recursor stage's pieces (task #451, lane O7-classes)

The generated recursor stage (`genRecCheck`) against master's, bottom-up:

* `fvarB_trR`: InLean's variable bound is master's range of the reading
  (the converse of `fvarB_le_tr`: the stage's range tests decide branches).
* `targetAbsI_tr`: the member abstraction (`targetAbs`, `EO.replace`) is
  master's on the reading.
* `isEquivList_tr`: the levels' comparison.

The proofs are functional, as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-! ## The variable bound, exactly -/

/-- A variable of a term with a reading lies below the reading's range. -/
theorem occF_le_fvarRange {s : InLean.CState} {id : FVarId} : ∀ {e : Lean.Expr}, OkS s e = true →
    OccF id e → ∀ d, EO.fvDepth? id = some d → d + 1 ≤ (TrS s e).fvarRange := by
  intro e
  induction e with
  | fvar x =>
    intro h ho d hd
    simp only [OccF] at ho
    subst ho
    obtain ⟨d', ty, ht, hd'⟩ := TrS_stripTop_fvar h rfl
    rw [hd] at hd'
    cases hd'
    rw [ht]; exact Nat.le_refl _
  | app f a ihf iha =>
    intro h ho d hd; simp only [OkS_app, Bool.and_eq_true] at h
    simp only [TrS_app, ConLeche.Expr.fvarRange]
    rcases ho with ho | ho
    · exact Nat.le_trans (ihf h.1 ho d hd) (Nat.le_max_left _ _)
    · exact Nat.le_trans (iha h.2 ho d hd) (Nat.le_max_right _ _)
  | lam _ t b _ iht ihb =>
    intro h ho d hd; simp only [OkS_lam, Bool.and_eq_true] at h
    simp only [TrS_lam, ConLeche.Expr.fvarRange]
    rcases ho with ho | ho
    · exact Nat.le_trans (iht h.1 ho d hd) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihb h.2 ho d hd) (Nat.le_max_right _ _)
  | forallE _ t b _ iht ihb =>
    intro h ho d hd; simp only [OkS_forallE, Bool.and_eq_true] at h
    simp only [TrS_forallE, ConLeche.Expr.fvarRange]
    rcases ho with ho | ho
    · exact Nat.le_trans (iht h.1 ho d hd) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ihb h.2 ho d hd) (Nat.le_max_right _ _)
  | letE _ t v b _ iht ihv ihb =>
    intro h ho d hd; simp only [OkS_letE, Bool.and_eq_true] at h
    simp only [TrS_letE, ConLeche.Expr.fvarRange]
    rcases ho with ho | ho | ho
    · exact Nat.le_trans (iht h.1.1 ho d hd)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    · exact Nat.le_trans (ihv h.1.2 ho d hd)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
    · exact Nat.le_trans (ihb h.2 ho d hd) (Nat.le_max_right _ _)
  | mdata _ x ih => intro h ho d hd; rw [OkS_mdata] at h; rw [TrS_mdata]; exact ih h ho d hd
  | proj _ _ x ih =>
    intro h ho d hd; rw [OkS_proj] at h
    simp only [TrS_proj, ConLeche.Expr.fvarRange]; exact ih h ho d hd
  | bvar _ | sort _ | const _ _ | lit _ | mvar _ => intro _ ho; simp only [OccF] at ho

/-- **InLean's variable bound is the reading's range.** -/
theorem fvarB_trR {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) :
    InLean.fvarB e = (TrS s e).fvarRange := by
  have hr := RangeOk_of_OkS h
  unfold InLean.fvarB
  cases hf : e.hasFVar with
  | false =>
    have : (TrS s e).hasFvar = false := by rw [← hasFVar_TrS (s := s) h, hf]
    rw [ConLeche.Expr.hasFvar_eq_false_iff.1 this]
    rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [← Array.foldl_toList]
    refine Nat.le_antisymm ?_ ?_
    · refine fvbFold_le _ 0 (Nat.zero_le _) fun id hid d hd => ?_
      have ho := (mem_fvarIds hr id).1 (Array.mem_toList_iff.1 hid)
      exact occF_le_fvarRange h ho d hd
    · refine fvarRange_TrS_le_of h fun id ho d hd => ?_
      have hmem : id ∈ (EO.fvarIds e).toList :=
        Array.mem_toList_iff.2 ((mem_fvarIds hr id).2 ho)
      exact (fvbFold_ge _ 0).2 id hmem d hd

/-! ## The member abstraction and the levels -/

/-- The callback of InLean's `targetAbs`. -/
@[expose] def taF (names : List Lean.Name) (lvls : List Lean.Level) (holes : List Lean.Expr)
    (x : Lean.Expr) : Option Lean.Expr :=
  match x with
  | x@(.const n us) =>
    if us == lvls then
      match names.findIdx? (· == n) with
      | some t => some (holes.getD t x)
      | none => some x
    else some x
  | _ => none

theorem targetAbs_eq (names : List Lean.Name) (lvls : List Lean.Level) (holes : List Lean.Expr)
    (e : Lean.Expr) :
    InLean.targetAbs names lvls holes e = mapSpec (fun x _ => taF names lvls holes x) e 0 := by
  unfold InLean.targetAbs EO.replace
  rw [mapOff_fresh]; rfl

/-- **The member abstraction, read** (`targetAbs`). -/
theorem targetAbsI_tr {s : InLean.CState} (names : List Lean.Name) {lvls : List Lean.Level}
    {holes : List Lean.Expr} (hlv : lvls.all okLv = true) (hh : OkSL s holes = true) :
    ∀ (e : Lean.Expr) (k : Nat), OkS s e = true →
      OkS s (mapSpec (fun x _ => taF names lvls holes x) e k) = true ∧
        TrS s (mapSpec (fun x _ => taF names lvls holes x) e k) =
          ConLeche.targetAbs (names.map toName) (lvls.map trL) (TrSL s holes) (TrS s e) := by
  intro e
  induction e with
  | const n us =>
    intro k h
    have hus : us.all okLv = true := by rwa [OkS_const] at h
    simp only [mapSpec, taF, TrS_const, ConLeche.targetAbs, map_trL_beq hus hlv,
      findIdx?_map_toName]
    cases us == lvls with
    | false => exact ⟨h, rfl⟩
    | true =>
      simp only [↓reduceIte]
      cases names.findIdx? (· == n) with
      | none => exact ⟨h, rfl⟩
      | some t =>
        simp only [Option.getD_some]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        have hm : (TrSL s holes)[t]? = (holes[t]?).map (TrS s) := by simp [TrSL]
        rw [hm]
        cases hx : holes[t]? with
        | none => exact ⟨h, rfl⟩
        | some y => exact ⟨okS_getElem? hh hx, rfl⟩
  | app f a ihf iha =>
    intro k h
    have hF : taF names lvls holes (.app f a) = none := rfl
    simp only [OkS_app, Bool.and_eq_true] at h
    simp only [mapSpec, hF, Option.getD_none, OkS_app, TrS_app, ConLeche.targetAbs,
      (ihf k h.1).1, (iha k h.2).1, (ihf k h.1).2, (iha k h.2).2, Bool.and_self, true_and]
  | lam nm t b bi iht ihb =>
    intro k h
    have hF : taF names lvls holes (.lam nm t b bi) = none := rfl
    simp only [OkS_lam, Bool.and_eq_true] at h
    simp only [mapSpec, hF, Option.getD_none, OkS_lam, TrS_lam, ConLeche.targetAbs,
      (iht k h.1).1, (ihb (k + 1) h.2).1, (iht k h.1).2, (ihb (k + 1) h.2).2, Bool.and_self,
      true_and]
  | forallE nm t b bi iht ihb =>
    intro k h
    have hF : taF names lvls holes (.forallE nm t b bi) = none := rfl
    simp only [OkS_forallE, Bool.and_eq_true] at h
    simp only [mapSpec, hF, Option.getD_none, OkS_forallE, TrS_forallE, ConLeche.targetAbs,
      (iht k h.1).1, (ihb (k + 1) h.2).1, (iht k h.1).2, (ihb (k + 1) h.2).2, Bool.and_self,
      true_and]
  | letE nm t v b nd iht ihv ihb =>
    intro k h
    have hF : taF names lvls holes (.letE nm t v b nd) = none := rfl
    simp only [OkS_letE, Bool.and_eq_true] at h
    simp only [mapSpec, hF, Option.getD_none, OkS_letE, TrS_letE, ConLeche.targetAbs,
      (iht k h.1.1).1, (ihv k h.1.2).1, (ihb (k + 1) h.2).1, (iht k h.1.1).2, (ihv k h.1.2).2,
      (ihb (k + 1) h.2).2, Bool.and_self, true_and]
  | proj sn i x ih =>
    intro k h
    have hF : taF names lvls holes (.proj sn i x) = none := rfl
    rw [OkS_proj] at h
    simp only [mapSpec, hF, Option.getD_none, OkS_proj, TrS_proj, ConLeche.targetAbs,
      (ih k h).1, (ih k h).2, true_and]
  | mdata m x ih =>
    intro k h
    have hF : taF names lvls holes (.mdata m x) = none := rfl
    rw [OkS_mdata] at h
    simp only [mapSpec, hF, Option.getD_none, OkS_mdata, TrS_mdata]
    exact ih k h
  | fvar id =>
    intro k h
    have hF : taF names lvls holes (.fvar id) = none := rfl
    simp only [mapSpec, hF, Option.getD_none]
    refine ⟨h, ?_⟩
    rw [TrS_fvar h]; rfl
  | bvar i => intro k h; exact ⟨h, rfl⟩
  | sort u => intro k h; exact ⟨h, rfl⟩
  | lit l => intro k h; exact ⟨h, rfl⟩
  | mvar i => intro k h; simp [OkS, okE] at h

/-- **The levels' comparison** (`isEquivList`), read. -/
theorem isEquivList_tr : ∀ {us vs : List Lean.Level}, us.all okLv = true → vs.all okLv = true →
    InLean.isEquivList us vs = ConLeche.Level.isEquivList (us.map trL) (vs.map trL)
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ | _ :: _, [], _, _ => rfl
  | u :: us, v :: vs, hu, hv => by
    simp only [List.all_cons, Bool.and_eq_true] at hu hv
    have hu1 : okL u = true := by simp only [okLv, Bool.and_eq_true] at hu; exact hu.1.1
    have hv1 : okL v = true := by simp only [okLv, Bool.and_eq_true] at hv; exact hv.1.1
    simp only [InLean.isEquivList, List.map_cons, ConLeche.Level.isEquivList,
      ← isEquiv_trL hu1 hv1, isEquivList_tr hu.2 hv.2]
    cases Lvl.isEquiv u v with
    | none => rfl
    | some b => cases b <;> rfl

end InLeanProof
