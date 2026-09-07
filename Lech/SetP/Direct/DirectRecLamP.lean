import Lech.SetP.Direct.DirectRecWalksP

/-!
# λ-towers fold to their body (task #175 W4c, P3 module 6, part 15)

A **graded** λ-tower applied along a fitting spine computes its body
at the spine's frame — whatever its bits.  A nonzero bit steps by
β (`app_lamR_pos`); a zero bit collapses the layer to the proof point,
but the grading's package puts the layer's body values in truth
values, so the body is the point too (`eq_pt_of_mem_univZero`), and the
fold of the point is the point.  This is what lets the recursor rule's
law read the rule's right-hand side without any bit correspondence
between the rule's λ-annotations and the recursor's elimination level.
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

/-- A graded λ-tower whose value is the point has body value the point
along any fitting spine. -/
theorem mkLamsAV_pt_body :
    ∀ {lds : List (Nat × AVExpr)} {b : AVExpr} {ρ : Nat → V} {as : List V},
      AnnotOk2 V ρ (mkLamsAV lds b) → SpineFit ρ (lds.map (·.2)) as →
      interp2 V ρ (mkLamsAV lds b) = (pt : V) →
      interp2 V (consList as ρ) b = (pt : V)
  | [], _, _, [], _, _, h => h
  | [], _, _, _ :: _, _, hsp, _ => hsp.elim
  | _ :: _, _, _, [], _, hsp, _ => hsp.elim
  | d :: lds, b, ρ, a :: as, hok, hsp, hpt => by
    simp only [List.map_cons, SpineFit] at hsp
    have hok' := hok
    simp only [mkLamsAV, AnnotOk2_lam] at hok'
    obtain ⟨-, hrest, B, hB, hB0⟩ := hok'
    rw [consList_cons]
    refine mkLamsAV_pt_body (hrest a hsp.1) hsp.2 ?_
    rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
    · exact eq_pt_of_mem_univZero (hB0 h0 a hsp.1) (hB a hsp.1)
    · have := app_lamR_pos (Nat.pos_iff_ne_zero.mp hpos)
        (A := interp2 V ρ d.2) (F := fun x => interp2 V (cons x ρ) (mkLamsAV lds b)) hsp.1
      simp only [mkLamsAV, interp2_lam] at hpt
      rw [hpt, app_pt] at this
      exact this.symm

/-- **A graded λ-tower folds to its body** along any fitting spine. -/
theorem mkLamsAV_fold_graded :
    ∀ {lds : List (Nat × AVExpr)} {b : AVExpr} {ρ : Nat → V} {as : List V},
      AnnotOk2 V ρ (mkLamsAV lds b) → SpineFit ρ (lds.map (·.2)) as →
      as.foldl SetTheory.app (interp2 V ρ (mkLamsAV lds b))
        = interp2 V (consList as ρ) b
  | [], _, _, [], _, _ => rfl
  | [], _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, hsp => hsp.elim
  | d :: lds, b, ρ, a :: as, hok, hsp => by
    simp only [List.map_cons, SpineFit] at hsp
    have hok' := hok
    simp only [mkLamsAV, AnnotOk2_lam] at hok'
    obtain ⟨-, hrest, B, hB, hB0⟩ := hok'
    rw [consList_cons, List.foldl_cons]
    rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
    · -- a zero bit: the layer is the point, and so is the body
      have hpt : interp2 V ρ (mkLamsAV (d :: lds) b) = (pt : V) := by
        simp only [mkLamsAV, interp2_lam]
        rw [h0]
        exact lamR_zero
      rw [hpt, app_pt, foldl_app_pt]
      exact (mkLamsAV_pt_body (hrest a hsp.1) hsp.2
        (eq_pt_of_mem_univZero (hB0 h0 a hsp.1) (hB a hsp.1))).symm
    · simp only [mkLamsAV, interp2_lam]
      rw [app_lamR_pos (Nat.pos_iff_ne_zero.mp hpos) hsp.1]
      exact mkLamsAV_fold_graded (hrest a hsp.1) hsp.2

/-- The layers of a graded λ-tower are graded along any fitting prefix
of a spine. -/
theorem mkLamsAV_layers_ok :
    ∀ {lds : List (Nat × AVExpr)} {b : AVExpr} {ρ : Nat → V} {as : List V},
      AnnotOk2 V ρ (mkLamsAV lds b) → SpineFit ρ (lds.map (·.2)) as →
      ∀ i, i < lds.length →
        AnnotOk2 V (consList (as.take i) ρ) ((lds.getD i default).2)
  | [], _, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, _, [], _, hsp, _, _ => hsp.elim
  | d :: lds, b, ρ, a :: as, hok, hsp, i, hi => by
    simp only [List.map_cons, SpineFit] at hsp
    have hok' := hok
    simp only [mkLamsAV, AnnotOk2_lam] at hok'
    obtain ⟨hA, hrest, -⟩ := hok'
    cases i with
    | zero => simpa using hA
    | succ i =>
      simp only [List.take_succ_cons, consList_cons, List.getD_cons_succ]
      exact mkLamsAV_layers_ok (hrest a hsp.1) hsp.2 i (by simpa using hi)

/-- A λ telescope's peel: the binder data with bits, whose reversed
domains are the telescope's context. -/
theorem stripLamsAV_of_lamTeleP :
    ∀ {k : Nat} {T : AVExpr} {Γ : List AVExpr} {C : AVExpr},
      LamTeleP k T Γ C →
      ∃ lds : List (Nat × AVExpr), T = mkLamsAV lds C ∧ (lds.map (·.2)).reverse = Γ ∧
        lds.length = k := by
  intro k T Γ C h
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | @cons k v A B R Γ' _ ih =>
    obtain ⟨lds, rfl, hΓ, hlen⟩ := ih
    exact ⟨(v, A) :: lds, rfl, by simp [hΓ], by simp [hlen]⟩

/-- **A graded λ-tower applied along a fitting spine is graded**: each
step's Π-package is the layer's own (`lamR_mem` over the grading's
fibre family), or — once a zero layer has collapsed the value to the
point — the trivial one. -/
theorem mkAppN_okP_of_lam :
    ∀ {lds : List (Nat × AVExpr)} {b f : AVExpr} {args : List AVExpr} {ρ σ : Nat → V},
      AnnotOkP V ρ f → (∀ a ∈ args, AnnotOkP V ρ a) →
      AnnotOk2 V σ (mkLamsAV lds b) →
      (interp2 V ρ f = (pt : V) ∨ interp2 V ρ f = interp2 V σ (mkLamsAV lds b)) →
      SpineFit σ (lds.map (·.2)) (args.map (interp2 V ρ)) →
      AnnotOkP V ρ (AVExpr.mkAppN f args)
  | [], _, _, [], _, _, hf, _, _, _, _ => hf
  | [], _, _, _ :: _, _, _, _, _, _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, _, hf, _, _, _, _ => hf
  | d :: lds, b, f, a :: args, ρ, σ, hf, hargs, hok, hval, hsp => by
    simp only [List.map_cons, SpineFit] at hsp
    have hok' := hok
    simp only [mkLamsAV, AnnotOk2_lam] at hok'
    obtain ⟨-, hrest, B, hB, hB0⟩ := hok'
    have ha := hargs a List.mem_cons_self
    rw [AVExpr.mkAppN_cons]
    -- the application's package
    have hokApp : AnnotOkP V ρ (.app f a) := by
      refine ⟨?_, by rw [AnnotValidV_app]; exact ⟨hf.2, ha.2⟩⟩
      rw [AnnotOk2_app]
      rcases hval with hpt | heq
      · exact ⟨hf.1, ha.1, 0, interp2 V σ d.2, fun _ => unitSet,
          by rw [hpt, piR_zero]; exact pt_mem_truthVal fun x _ => ⟨pt, pt_mem_unitSet⟩,
          hsp.1, fun _ _ _ => mem_univZero.mpr (Subset.refl _)⟩
      · refine ⟨hf.1, ha.1, d.1, interp2 V σ d.2, B, ?_, hsp.1, fun h0 x hx => hB0 h0 x hx⟩
        rw [heq]
        simp only [mkLamsAV, interp2_lam]
        exact lamR_mem hB
    refine mkAppN_okP_of_lam hokApp (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))
      (hrest _ hsp.1) ?_ hsp.2
    -- the continuation's value
    rw [interp2_app]
    rcases hval with hpt | heq
    · left; rw [hpt, app_pt]
    · rw [heq]
      simp only [mkLamsAV, interp2_lam]
      rcases Nat.eq_zero_or_pos d.1 with h0 | hpos
      · left; rw [h0, lamR_zero, app_pt]
      · right; rw [app_lamR_pos (Nat.pos_iff_ne_zero.mp hpos) hsp.1]

end Lech.SetP
