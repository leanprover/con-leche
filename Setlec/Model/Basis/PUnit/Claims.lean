import Setlec.Model.Basis.PUnit.Iota
import Setlec.Model.Basis.Glue

/-!
# Claims glue for the `PUnit.rec` rule
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-- Claims glue for the `PUnit.rec` rule. -/
theorem punitIota_claims {cval : ConstVal V}
    (hfindP : env.find? punitName = some punitA)
    (hvalP : ∀ ψ' : Name → Nat, cval punitName ψ' = unitSet)
    (hfindU : env.find? punitUnitName = some punitUnitA)
    (hvalU : ∀ ψ' : Name → Nat, cval punitUnitName ψ' = pt)
    {Mv mv tv : V} {vE1 vE2 : Nat} {A1 A2 : V} {B1 B2 : V → V}
    (h1 : (punitRecVal V ψ : V) ∈ˢ pi vE1 A1 B1) (hM : Mv ∈ˢ A1)
    (h2 : SetTheory.app (punitRecVal V ψ) Mv ∈ˢ pi vE2 A2 B2)
    (hm : mv ∈ˢ A2)
    (htv : tv = pt) :
    ∃ R, interpClosed V cval env ψ punitRecRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (punitRecVal V ψ) Mv) mv)
        tv = SetTheory.app (SetTheory.app R Mv) mv ∧
      AppSlot (V := V) R Mv ∧ AppSlot (V := V) (SetTheory.app R Mv) mv := by
  by_cases h0 : ψ u1N = 0
  · -- Prop collapse: recursor and reduct values are the proof point
    refine ⟨_, interp_punitRec_rhs hfindP hvalP hfindU hvalU, ?_, ?_, ?_⟩
    · rw [show (punitRecVal V ψ : V) = pt from by
        simp only [punitRecVal, h0, reduceIte]; exact lam_zero]
      rw [show (SetTheory.lam (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) = pt from by
        rw [if_pos h0]; exact lam_zero]
      simp only [app_pt]
    · refine ⟨0, A1, fun _ => unitSet, ?_, hM, fun _ _ => unitSet_mem_univ 0⟩
      rw [show (SetTheory.lam (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) = pt from by
        rw [if_pos h0]; exact lam_zero]
      exact pt_mem_pi_unit (V := V)
    · refine ⟨0, A2, fun _ => unitSet, ?_, hm, fun _ _ => unitSet_mem_univ 0⟩
      rw [show (SetTheory.lam (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) = pt from by
        rw [if_pos h0]; exact lam_zero]
      rw [app_pt]
      exact pt_mem_pi_unit (V := V)
  · -- data: recover the canonical memberships and fold
    have hwne : Nat.max (ψ uN) (ψ u1N) ≠ 0 := max_ne_zero_r' h0
    have h1' := h1
    rw [show (punitRecVal V ψ : V) = SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
        (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) (fun M =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app M pt)
            fun m => SetTheory.lam (ψ u1N) unitSet fun _ => m) from by
      simp only [punitRecVal, if_neg h0]] at h1'
    have hMc : Mv ∈ˢ pi (ψ u1N + 1) unitSet (fun _ => univ (ψ u1N)) :=
      lam_dom_of_ne h1' hwne Mv hM
    have hMpt : SetTheory.app Mv pt ∈ˢ univ (ψ u1N) :=
      app_mem hMc pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
    have hspace : ∀ M : V, SetTheory.app M pt ∈ˢ univ (ψ u1N) →
        (pi (ψ u1N) unitSet fun _ => SetTheory.app M pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro M hMpt'
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N)) (v := ψ u1N)
        (B := fun _ => SetTheory.app M pt)
        (unitSet_mem_univ _) (fun _ _ => hMpt')
      rw [if_neg h0, show Nat.max (Nat.max (ψ uN) (ψ u1N)) (ψ u1N) =
        Nat.max (ψ uN) (ψ u1N) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
          (Nat.le_max_left _ _)] at this
      exact this
    have happ1 : SetTheory.app (punitRecVal V ψ) Mv =
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app Mv pt)
          fun m => SetTheory.lam (ψ u1N) unitSet fun _ => m := by
      rw [show (punitRecVal V ψ : V) = SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) (fun M =>
            SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app M pt)
              fun m => SetTheory.lam (ψ u1N) unitSet fun _ => m) from by
        simp only [punitRecVal, if_neg h0]]
      refine app_lam hMc
        (B := fun M => pi (Nat.max (ψ uN) (ψ u1N)) (SetTheory.app M pt)
          fun _ => pi (ψ u1N) unitSet fun _ => SetTheory.app M pt)
        (fun M hM' => lam_mem (V := V)
          (B := fun _ => pi (ψ u1N) unitSet fun _ => SetTheory.app M pt)
          fun m hm' => lam_mem (V := V)
            (B := fun _ => SetTheory.app M pt) fun _ _ => hm')
        (fun M hM' => ?_)
      have hMpt' : SetTheory.app M pt ∈ˢ univ (ψ u1N) :=
        app_mem hM' pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
      have := pi_mem_univ (u := ψ u1N) (v := Nat.max (ψ uN) (ψ u1N))
        (B := fun _ => pi (ψ u1N) unitSet fun _ => SetTheory.app M pt)
        hMpt' (fun _ _ => hspace M hMpt')
      rw [if_neg hwne, show Nat.max (ψ u1N) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_max_right _ _, Nat.le_refl _⟩)
          (Nat.le_max_right _ _)] at this
      exact this
    have h2' := h2
    rw [happ1] at h2'
    have hmc : mv ∈ˢ SetTheory.app Mv pt :=
      lam_dom_of_ne h2' hwne mv hm
    obtain ⟨R', hR'i, hfold⟩ := punitRec_iota hfindP hvalP hfindU hvalU
      hMc hmc (htv.symm ▸ pt_mem_unitSet)
    rw [interp_punitRec_rhs hfindP hvalP hfindU hvalU] at hR'i
    obtain rfl := Option.some.inj hR'i
    refine ⟨_, interp_punitRec_rhs hfindP hvalP hfindU hvalU, hfold, ?_, ?_⟩
    · refine ⟨if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N),
        pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N),
        fun M => pi (ψ u1N) (SetTheory.app M pt) fun _ =>
          SetTheory.app M pt,
        ?_, hMc, ?_⟩
      · exact lam_mem (V := V)
          (B := fun M => pi (ψ u1N) (SetTheory.app M pt) fun _ =>
            SetTheory.app M pt)
          fun M hM' => lam_mem (V := V)
            (B := fun _ => SetTheory.app M pt) fun m hm' => hm'
      · intro M hM'
        have hMpt' : SetTheory.app M pt ∈ˢ univ (ψ u1N) :=
          app_mem hM' pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
        have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
          (B := fun _ => SetTheory.app M pt) hMpt' (fun _ _ => hMpt')
        rw [if_neg h0, show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from
          Nat.max_self _] at this
        rw [if_neg h0, show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from
          Nat.max_self _]
        exact this
    · have happR : SetTheory.app (SetTheory.lam
          (if ψ u1N = 0 then 0 else Nat.max (ψ u1N) (ψ u1N))
          (pi (ψ u1N + 1) unitSet fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N) (SetTheory.app M pt) fun m => m) Mv =
          SetTheory.lam (ψ u1N) (SetTheory.app Mv pt) fun m => m := by
        refine app_lam hMc
          (B := fun M => pi (ψ u1N) (SetTheory.app M pt) fun _ =>
            SetTheory.app M pt)
          (fun M hM' => lam_mem (V := V)
            (B := fun _ => SetTheory.app M pt) fun m hm' => hm')
          (fun M hM' => ?_)
        have hMpt' : SetTheory.app M pt ∈ˢ univ (ψ u1N) :=
          app_mem hM' pt_mem_unitSet (fun _ _ => univ_mem_univ (ψ u1N))
        have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
          (B := fun _ => SetTheory.app M pt) hMpt' (fun _ _ => hMpt')
        rw [if_neg h0, show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from
          Nat.max_self _] at this
        rw [if_neg h0, show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from
          Nat.max_self _]
        exact this
      refine ⟨ψ u1N, SetTheory.app Mv pt, fun _ => SetTheory.app Mv pt,
        ?_, hmc, fun _ _ => hMpt⟩
      rw [happR]
      exact lam_mem (V := V) (B := fun _ => SetTheory.app Mv pt)
        fun m hm' => hm'

end Setlec
