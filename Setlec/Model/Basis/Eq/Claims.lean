import Setlec.Model.Basis.Eq.Iota
import Setlec.Model.Basis.Glue

/-!
# Claims glue for the `Eq.rec` rule
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-- Claims glue for the `Eq.rec` rule. -/
theorem eqIota_claims {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindR : env.find? eqReflName = some eqReflA)
    (hvalR : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ')
    {Av av Mv rv bv tv : V} {vE1 vE2 vE3 vE4 vE5 vE6 : Nat}
    {A1 A2 A3 A4 A5 A6 : V} {B1 B2 B3 B4 B5 B6 : V → V}
    (h1 : (eqRecVal V ψ : V) ∈ˢ pi vE1 A1 B1) (hA : Av ∈ˢ A1)
    (h2 : SetTheory.app (eqRecVal V ψ) Av ∈ˢ pi vE2 A2 B2) (ha : av ∈ˢ A2)
    (h3 : SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av ∈ˢ pi vE3 A3 B3)
    (hM : Mv ∈ˢ A3)
    (h4 : SetTheory.app (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av)
      av) Mv ∈ˢ pi vE4 A4 B4)
    (hr : rv ∈ˢ A4)
    (h5 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (eqRecVal V ψ) Av) av) Mv) rv ∈ˢ pi vE5 A5 B5)
    (hb : bv ∈ˢ A5)
    (h6 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) bv ∈ˢ pi vE6 A6 B6)
    (hh : tv ∈ˢ A6) :
    ∃ R, interpClosed V cval env ψ eqRecRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) bv)
        tv =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app R Av) av)
        Mv) rv ∧
      AppSlot (V := V) R Av ∧
      AppSlot (V := V) (SetTheory.app R Av) av ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app R Av) av) Mv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app (SetTheory.app R Av)
        av) Mv) rv := by
  by_cases h0 : ψ u1N = 0
  · -- Prop collapse
    refine ⟨_, interp_eqRec_rhs hfindE hvalE hfindR hvalR, ?_⟩
    have hRpt : (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN))
        fun A => SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r) = (pt : V) := by
      rw [show eqRhsAl' (ψ uN) (ψ u1N) = 0 from by
        rw [eqRhsAl'_eq, if_pos h0]]
      exact lam_zero
    have hrec_pt : (eqRecVal V ψ : V) = pt := by
      simp only [eqRecVal, h0, reduceIte]
      exact lam_zero
    rw [hRpt, hrec_pt]
    simp only [app_pt]
    exact ⟨trivial,
      ⟨0, A1, fun _ => unitSet, pt_mem_pi_unit (V := V), hA,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A2, fun _ => unitSet, pt_mem_pi_unit (V := V), ha,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A3, fun _ => unitSet, pt_mem_pi_unit (V := V), hM,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A4, fun _ => unitSet, pt_mem_pi_unit (V := V), hr,
        fun _ _ => unitSet_mem_univ 0⟩⟩
  · -- data levels
    have hsne : Nat.max (ψ uN) (ψ u1N + 1) ≠ 0 :=
      max_ne_zero_r' (Nat.succ_ne_zero _)
    have hwne : Nat.max (ψ uN) (ψ u1N) ≠ 0 := max_ne_zero_r' h0
    have hrec_lam : (eqRecVal V ψ : V) =
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N + 1)) (univ (ψ uN)) fun A =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
            SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
              (eqRecMSpace V (ψ u1N) A a) fun M =>
              SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
                (SetTheory.app (SetTheory.app M a) pt) fun r =>
                SetTheory.lam (ψ u1N) A fun _b =>
                  SetTheory.lam (ψ u1N) (eqv a _b) fun _h => r := by
      simp only [eqRecVal, if_neg h0]
    have h1' := h1
    rw [hrec_lam] at h1'
    have hAc : Av ∈ˢ univ (ψ uN) := lam_dom_of_ne h1' hsne Av hA
    -- parametric universe facts (as in the fold equation)
    have hMS : ∀ A : V, A ∈ˢ univ (ψ uN) → ∀ a : V, a ∈ˢ A →
        eqRecMSpace V (ψ u1N) A a ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      unfold eqRecMSpace
      exact pi_mem_univ (u := ψ uN) (v := ψ u1N + 1) hA'
        (fun b hb' => pi_mem_univ (u := 0) (v := ψ u1N + 1)
          (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N)))
    have hMapt' : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        SetTheory.app (SetTheory.app M a) pt ∈ˢ univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      simp only [eqRecMSpace] at hM'
      have hMa' : SetTheory.app M a ∈ˢ pi (ψ u1N + 1) (eqv a a)
          (fun _ => univ (ψ u1N)) :=
        app_mem hM' ha' (fun b hb' => pi_mem_univ (u := 0) (v := ψ u1N + 1)
          (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N)))
      exact app_mem hMa' (pt_mem_eqv_self a)
        (fun _ _ => univ_mem_univ (ψ u1N))
    have hT5 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        (pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro A hA' a ha' M hM'
      have h5 : ∀ b, b ∈ˢ A →
          (pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt) ∈ˢ univ (ψ u1N) := by
        intro b hb'
        have := pi_mem_univ (u := 0) (v := ψ u1N)
          (B := fun _ => SetTheory.app (SetTheory.app M a) pt)
          (eqv_mem_univ a b) (fun _ _ => hMapt' A hA' a ha' M hM')
        rw [if_neg h0] at this
        exact this
      have := pi_mem_univ (u := ψ uN) (v := ψ u1N)
        (B := fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt) hA' h5
      rw [if_neg h0] at this
      exact this
    have hT4 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        (pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a) pt) fun _ =>
          pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N)) := by
      intro A hA' a ha' M hM'
      have := pi_mem_univ (u := ψ u1N) (v := Nat.max (ψ uN) (ψ u1N))
        (B := fun _ => pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
          SetTheory.app (SetTheory.app M a) pt)
        (hMapt' A hA' a ha' M hM') (fun _ _ => hT5 A hA' a ha' M hM')
      rw [if_neg hwne] at this
      rw [show Nat.max (ψ u1N) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_max_right _ _, Nat.le_refl _⟩)
          (Nat.le_max_right _ _)] at this
      exact this
    have hT3 : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
        (v := Nat.max (ψ uN) (ψ u1N))
        (B := fun M => pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a) pt) fun _ =>
          pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt)
        (hMS A hA' a ha') (fun M hM' => hT4 A hA' a ha' M hM')
      rw [if_neg hwne] at this
      rw [show Nat.max (Nat.max (ψ uN) (ψ u1N + 1)) (Nat.max (ψ uN) (ψ u1N)) =
        Nat.max (ψ uN) (ψ u1N + 1) from Nat.le_antisymm
          (Nat.max_le.mpr ⟨Nat.le_refl _,
            Nat.max_le.mpr ⟨Nat.le_max_left _ _,
              Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)⟩⟩)
          (Nat.le_max_left _ _)] at this
      exact this
    have hT2 : ∀ (A : V), A ∈ˢ univ (ψ uN) →
        (pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
            pi (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun _ =>
              pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
                SetTheory.app (SetTheory.app M a) pt) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) (ψ u1N + 1))
        (B := fun a => pi (Nat.max (ψ uN) (ψ u1N))
          (eqRecMSpace V (ψ u1N) A a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt)
        hA' (fun a ha' => hT3 A hA' a ha')
      rw [if_neg hsne, max_absorb_l'] at this
      exact this
    -- fold the original chain to recover canonical memberships
    have happ1 : SetTheory.app (eqRecVal V ψ) Av =
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N + 1)) Av fun a =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
            (eqRecMSpace V (ψ u1N) Av a) fun M =>
            SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun r =>
              SetTheory.lam (ψ u1N) Av fun _b =>
                SetTheory.lam (ψ u1N) (eqv a _b) fun _h => r := by
      rw [hrec_lam]
      exact app_lam hAc
        (B := fun A => pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
            pi (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun _ =>
              pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
                SetTheory.app (SetTheory.app M a) pt)
        (fun A hA' => lam_mem (V := V) fun a ha' =>
          lam_mem (V := V) fun M hM' =>
            lam_mem (V := V) fun r hr' =>
              lam_mem (V := V) fun b hb' =>
                lam_mem (V := V) fun h hh' => hr')
        (fun A hA' => hT2 A hA')
    have h2' := h2
    rw [happ1] at h2'
    have hac : av ∈ˢ Av := lam_dom_of_ne h2' hsne av ha
    have happ2 : SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av =
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (eqRecMSpace V (ψ u1N) Av av) fun M =>
          SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M av) pt) fun r =>
            SetTheory.lam (ψ u1N) Av fun _b =>
              SetTheory.lam (ψ u1N) (eqv av _b) fun _h => r := by
      rw [happ1]
      exact app_lam hac
        (B := fun a => pi (Nat.max (ψ uN) (ψ u1N))
          (eqRecMSpace V (ψ u1N) Av a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt)
        (fun a ha' => lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' =>
            lam_mem (V := V) fun b hb' =>
              lam_mem (V := V) fun h hh' => hr')
        (fun a ha' => hT3 Av hAc a ha')
    have h3' := h3
    rw [happ2] at h3'
    have hMc : Mv ∈ˢ eqRecMSpace V (ψ u1N) Av av :=
      lam_dom_of_ne h3' hwne Mv hM
    have happ3 : SetTheory.app (SetTheory.app (SetTheory.app (eqRecVal V ψ)
        Av) av) Mv =
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app Mv av) pt) fun r =>
          SetTheory.lam (ψ u1N) Av fun _b =>
            SetTheory.lam (ψ u1N) (eqv av _b) fun _h => r := by
      rw [happ2]
      exact app_lam hMc
        (B := fun M => pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M av) pt) fun _ =>
          pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv av b) fun _ =>
            SetTheory.app (SetTheory.app M av) pt)
        (fun M hM' => lam_mem (V := V) fun r hr' =>
          lam_mem (V := V) fun b hb' =>
            lam_mem (V := V) fun h hh' => hr')
        (fun M hM' => hT4 Av hAc av hac M hM')
    have h4' := h4
    rw [happ3] at h4'
    have hrc : rv ∈ˢ SetTheory.app (SetTheory.app Mv av) pt :=
      lam_dom_of_ne h4' hwne rv hr
    have happ4 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (eqRecVal V ψ) Av) av) Mv) rv =
        SetTheory.lam (ψ u1N) Av fun _b =>
          SetTheory.lam (ψ u1N) (eqv av _b) fun _h => rv := by
      rw [happ3]
      exact app_lam hrc
        (B := fun _ => pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv av b) fun _ =>
          SetTheory.app (SetTheory.app Mv av) pt)
        (fun r hr' => lam_mem (V := V) fun b hb' =>
          lam_mem (V := V) fun h hh' => hr')
        (fun _ _ => hT5 Av hAc av hac Mv hMc)
    have h5' := h5
    rw [happ4] at h5'
    have hbc : bv ∈ˢ Av := lam_dom_of_ne h5' h0 bv hb
    have happ5 : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) bv =
        SetTheory.lam (ψ u1N) (eqv av bv) fun _h => rv := by
      rw [happ4]
      refine app_lam hbc
        (B := fun b => pi (ψ u1N) (eqv av b) fun _ =>
          SetTheory.app (SetTheory.app Mv av) pt)
        (fun b hb' => lam_mem (V := V) fun h hh' => hrc)
        (fun b hb' => ?_)
      have := pi_mem_univ (u := 0) (v := ψ u1N)
        (B := fun _ => SetTheory.app (SetTheory.app Mv av) pt)
        (eqv_mem_univ av b)
        (fun _ _ => hMapt' Av hAc av hac Mv hMc)
      rw [if_neg h0] at this
      exact this
    have h6' := h6
    rw [happ5] at h6'
    have hhc : tv ∈ˢ eqv av bv := lam_dom_of_ne h6' h0 tv hh
    obtain ⟨R', hR'i, hfold⟩ := eqRec_iota hfindE hvalE hfindR hvalR
      hAc hac hMc hrc hbc hhc
    rw [interp_eqRec_rhs hfindE hvalE hfindR hvalR] at hR'i
    obtain rfl := Option.some.inj hR'i
    -- the reduct chain facts
    have heqAl : eqRhsAl' (ψ uN) (ψ u1N) = Nat.max (ψ uN) (ψ u1N + 1) := by
      rw [eqRhsAl'_eq, if_neg h0]
    have heqA' : eqRhsA' (ψ uN) (ψ u1N) = Nat.max (ψ uN) (ψ u1N + 1) := by
      rw [eqRhsA'_eq, if_neg h0]
    have herB : erB (ψ u1N) = ψ u1N := erB_eq _
    have hMSeqP : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a := by
      intro A hA' a ha'
      unfold eqRecMSpace
      exact pi_congr fun b hb' => by rw [eqVal_app₃ hA' ha' hb']
    have hrdP : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) →
        SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a) ∈ˢ
          univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      rw [eqReflVal_app₂ hA' ha']
      refine hMapt' A hA' a ha' M ?_
      rw [← hMSeqP A hA' a ha']
      exact hM'
    have hrfibP : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) →
        (pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) ∈ˢ
          univ (ψ u1N) := by
      intro A hA' a ha' M hM'
      have := pi_mem_univ (u := ψ u1N) (v := ψ u1N)
        (B := fun _ => SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        (hrdP A hA' a ha' M hM') (fun _ _ => hrdP A hA' a ha' M hM')
      rw [if_neg h0,
        show Nat.max (ψ u1N) (ψ u1N) = ψ u1N from Nat.max_self _] at this
      exact this
    have hT3r : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        (pi (erB (ψ u1N))
          (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) ∈ˢ
          univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      rw [herB]
      have hMSi : (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N)) ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
        rw [hMSeqP A hA' a ha']
        exact hMS A hA' a ha'
      have := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1)) (v := ψ u1N)
        (B := fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        hMSi (fun M hM' => hrfibP A hA' a ha' M hM')
      rw [if_neg h0, max_eqrec_b] at this
      exact this
    have hMvraw : Mv ∈ˢ (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) Av) av) b)
        fun _ => univ (ψ u1N)) := by
      rw [hMSeqP Av hAc av hac]
      exact hMc
    have hrvraw : rv ∈ˢ SetTheory.app (SetTheory.app Mv av)
        (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av) := by
      rw [eqReflVal_app₂ hAc hac]
      exact hrc
    have happR1 : SetTheory.app (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N))
        (univ (ψ uN)) fun A =>
        SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r) Av =
        SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) Av fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) Av fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) Av) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
              fun r => r := by
      rw [heqAl, heqA']
      exact app_lam hAc
        (B := fun A => pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          pi (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        (fun A hA' => lam_mem (V := V) fun a ha' => by
          rw [herB]
          exact lam_mem (V := V) fun M hM' =>
            lam_mem (V := V) fun r hr' => hr')
        (fun A hA' => by
          have := pi_mem_univ (u := ψ uN)
            (v := Nat.max (ψ uN) (ψ u1N + 1))
            (B := fun a => pi (erB (ψ u1N))
              (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
              pi (ψ u1N)
                (SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
                fun _ => SetTheory.app (SetTheory.app M a)
                  (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
            hA' (fun a ha' => hT3r A hA' a ha')
          rw [if_neg hsne, max_absorb_l'] at this
          exact this)
    have happR2 : SetTheory.app (SetTheory.app
        (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
        SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r) Av) av =
        SetTheory.lam (erB (ψ u1N))
          (pi (ψ u1N + 1) Av fun b =>
            pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) Av) av) b)
              fun _ => univ (ψ u1N)) fun M =>
          SetTheory.lam (ψ u1N)
            (SetTheory.app (SetTheory.app M av)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
            fun r => r := by
      rw [happR1, heqA']
      exact app_lam hac
        (B := fun a => pi (erB (ψ u1N))
          (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app
              (SetTheory.app (eqVal V ψ) Av) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
        (fun a ha' => by
          rw [herB]
          exact lam_mem (V := V) fun M hM' =>
            lam_mem (V := V) fun r hr' => hr')
        (fun a ha' => hT3r Av hAc a ha')
    have happR3 : SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (eqRhsAl' (ψ uN) (ψ u1N)) (univ (ψ uN)) fun A =>
        SetTheory.lam (eqRhsA' (ψ uN) (ψ u1N)) A fun a =>
          SetTheory.lam (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b =>
              pi (ψ u1N + 1)
                (SetTheory.app (SetTheory.app
                  (SetTheory.app (eqVal V ψ) A) a) b)
                fun _ => univ (ψ u1N)) fun M =>
            SetTheory.lam (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun r => r) Av) av) Mv =
        SetTheory.lam (ψ u1N)
          (SetTheory.app (SetTheory.app Mv av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
          fun r => r := by
      rw [happR2, herB]
      exact app_lam hMvraw
        (B := fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
          fun _ => SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
        (fun M hM' => lam_mem (V := V) fun r hr' => hr')
        (fun M hM' => hrfibP Av hAc av hac M hM')
    refine ⟨_, interp_eqRec_rhs hfindE hvalE hfindR hvalR, hfold,
      ?_, ?_, ?_, ?_⟩
    · refine ⟨Nat.max (ψ uN) (ψ u1N + 1), univ (ψ uN),
        fun A => pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
          pi (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a),
        ?_, hAc, ?_⟩
      · rw [heqAl, heqA']
        refine lam_mem (V := V) fun A hA' => ?_
        refine lam_mem (V := V) fun a ha' => ?_
        rw [herB]
        exact lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' => hr'
      · intro A hA'
        have := pi_mem_univ (u := ψ uN)
          (v := Nat.max (ψ uN) (ψ u1N + 1))
          (B := fun a => pi (erB (ψ u1N))
            (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
              (SetTheory.app (SetTheory.app
                (SetTheory.app (eqVal V ψ) A) a) b)
              fun _ => univ (ψ u1N)) fun M =>
            pi (ψ u1N)
              (SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
              fun _ => SetTheory.app (SetTheory.app M a)
                (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          hA' (fun a ha' => hT3r A hA' a ha')
        rw [if_neg hsne, max_absorb_l'] at this
        exact this
    · refine ⟨Nat.max (ψ uN) (ψ u1N + 1), Av,
        fun a => pi (erB (ψ u1N))
          (pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
            (SetTheory.app (SetTheory.app
              (SetTheory.app (eqVal V ψ) Av) a) b)
            fun _ => univ (ψ u1N)) fun M =>
          pi (ψ u1N)
            (SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a))
            fun _ => SetTheory.app (SetTheory.app M a)
              (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) a),
        ?_, hac, ?_⟩
      · rw [happR1, heqA']
        refine lam_mem (V := V) fun a ha' => ?_
        rw [herB]
        exact lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' => hr'
      · intro a ha'
        exact hT3r Av hAc a ha'
    · refine ⟨ψ u1N,
        pi (ψ u1N + 1) Av fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app
            (SetTheory.app (eqVal V ψ) Av) av) b)
          fun _ => univ (ψ u1N),
        fun M => pi (ψ u1N)
          (SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av))
          fun _ => SetTheory.app (SetTheory.app M av)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av),
        ?_, hMvraw, ?_⟩
      · rw [happR2, herB]
        exact lam_mem (V := V) fun M hM' =>
          lam_mem (V := V) fun r hr' => hr'
      · intro M hM'
        exact hrfibP Av hAc av hac M hM'
    · refine ⟨ψ u1N,
        SetTheory.app (SetTheory.app Mv av)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av),
        fun _ => SetTheory.app (SetTheory.app Mv av)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) Av) av),
        ?_, hrvraw, fun _ _ => hrdP Av hAc av hac Mv hMvraw⟩
      rw [happR3]
      exact lam_mem (V := V) fun r hr' => hr'

end Setlec
