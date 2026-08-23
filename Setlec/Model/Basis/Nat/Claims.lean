import Setlec.Model.Basis.Nat.AnnotOk
import Setlec.Model.Basis.Nat.RuleOk
import Setlec.Model.Basis.Glue

/-!
# Claims glue for the `Nat.rec` rules
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-- Claims glue for the `Nat.rec` zero rule. -/
theorem natZeroIota_claims {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    {Mv zv sv tv : V} {vE1 vE2 vE3 : Nat} {A1 A2 A3 : V} {B1 B2 B3 : V → V}
    (h1 : (natRecVal V ψ : V) ∈ˢ pi vE1 A1 B1) (hM : Mv ∈ˢ A1)
    (h2 : SetTheory.app (natRecVal V ψ) Mv ∈ˢ pi vE2 A2 B2) (hz : zv ∈ˢ A2)
    (h3 : SetTheory.app (SetTheory.app (natRecVal V ψ) Mv) zv ∈ˢ pi vE3 A3 B3)
    (hs : sv ∈ˢ A3)
    (htv : tv = natzero) :
    ∃ R, interpClosed V cval env ψ natRecZeroRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ) Mv) zv) sv) tv =
      SetTheory.app (SetTheory.app (SetTheory.app R Mv) zv) sv ∧
      AppSlot (V := V) R Mv ∧
      AppSlot (V := V) (SetTheory.app R Mv) zv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app R Mv) zv) sv := by
  subst htv
  by_cases h0 : ψ uN = 0
  · -- Prop collapse
    refine ⟨_, interp_natRecZero_rhs hfindN hvalN hfindZ hvalZ hfindSc
      hvalSc, ?_⟩
    have hRpt : (SetTheory.lam (nrM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _s => z) = (pt : V) := by
      rw [show nrM (ψ uN) = 0 from by rw [nrM_eq, if_pos h0]]
      exact lam_zero
    have hrec_pt : (natRecVal V ψ : V) = pt := by
      simp only [natRecVal, h0, reduceIte]
      exact lam_zero
    rw [hRpt, hrec_pt]
    simp only [app_pt]
    exact ⟨trivial,
      ⟨0, A1, fun _ => unitSet, pt_mem_pi_unit (V := V), hM,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A2, fun _ => unitSet, pt_mem_pi_unit (V := V), hz,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A3, fun _ => unitSet, pt_mem_pi_unit (V := V), hs,
        fun _ _ => unitSet_mem_univ 0⟩⟩
  · -- data levels
    have hwne : Nat.max 1 (ψ uN) ≠ 0 := max_ne_zero_l (by decide)
    have hrec_lam : (natRecVal V ψ : V) = SetTheory.lam (Nat.max 1 (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun s =>
            SetTheory.lam (ψ uN) omega fun t => natrec z s t := by
      simp only [natRecVal, if_neg h0]
    have h1' := h1
    rw [hrec_lam] at h1'
    have hMc : Mv ∈ˢ pi (ψ uN + 1) omega (fun _ => univ (ψ uN)) :=
      lam_dom_of_ne h1' hwne Mv hM
    have hMfib : ∀ n, n ∈ˢ omega → SetTheory.app Mv n ∈ˢ univ (ψ uN) :=
      fun n hn' => app_mem hMc hn' (fun _ _ => univ_mem_univ (ψ uN))
    have hsfib : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro M hM' n hn'
      have hMfib' : ∀ k, k ∈ˢ omega → SetTheory.app M k ∈ˢ univ (ψ uN) :=
        fun k hk => app_mem hM' hk (fun _ _ => univ_mem_univ (ψ uN))
      have := pi_mem_univ (u := ψ uN) (v := ψ uN) (hMfib' n hn')
        (fun _ _ => hMfib' (natsucc n) (natsucc_mem hn'))
      rw [if_neg h0,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
      exact this
    have hSsp : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M n) fun _ =>
          SetTheory.app M (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfib M hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hT4 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun t => SetTheory.app M t)
        (omega_mem_univ (V := V))
        (fun t ht => app_mem hM' ht (fun _ _ => univ_mem_univ (ψ uN)))
      rw [if_neg h0] at this
      exact this
    have hT3 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := Nat.max 1 (ψ uN))
        (hSsp M hM') (fun _ _ => hT4 M hM')
      rw [if_neg hwne, show Nat.max (Nat.max 1 (ψ uN)) (Nat.max 1 (ψ uN)) =
        Nat.max 1 (ψ uN) from Nat.max_self _] at this
      exact this
    have hT2 : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M t)
        (app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN)))
        (fun _ _ => hT3 M hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have hrecmem : ∀ M : V, M ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ z, z ∈ˢ SetTheory.app M natzero →
        ∀ s, s ∈ˢ (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M n) fun _ =>
            SetTheory.app M (natsucc n)) →
        ∀ t, t ∈ˢ omega → natrec z s t ∈ˢ SetTheory.app M t := by
      intro M hM' z hz' s hs' t ht'
      refine natrec_mem hz' ?_ ht'
      intro k hk ih hih
      exact app_mem (app_mem hs' hk (hsfib M hM')) hih
        (fun _ _ => app_mem hM' (natsucc_mem hk)
          (fun _ _ => univ_mem_univ (ψ uN)))
    have happ1 : SetTheory.app (natRecVal V ψ) Mv =
        SetTheory.lam (Nat.max 1 (ψ uN)) (SetTheory.app Mv natzero) fun z =>
          SetTheory.lam (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                SetTheory.app Mv (natsucc n)) fun s =>
            SetTheory.lam (ψ uN) omega fun t => natrec z s t := by
      rw [hrec_lam]
      exact app_lam hMc
        (B := fun M => pi (Nat.max 1 (ψ uN))
          (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M t)
        (fun M hM' => lam_mem (V := V) fun z hz' =>
          lam_mem (V := V) fun s hs' =>
            lam_mem (V := V) fun t ht' => hrecmem M hM' z hz' s hs' t ht')
        (fun M hM' => hT2 M hM')
    have h2' := h2
    rw [happ1] at h2'
    have hzc : zv ∈ˢ SetTheory.app Mv natzero :=
      lam_dom_of_ne h2' hwne zv hz
    have happ2 : SetTheory.app (SetTheory.app (natRecVal V ψ) Mv) zv =
        SetTheory.lam (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) fun s =>
          SetTheory.lam (ψ uN) omega fun t => natrec zv s t := by
      rw [happ1]
      exact app_lam hzc
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app Mv t)
        (fun z hz' => lam_mem (V := V) fun s hs' =>
          lam_mem (V := V) fun t ht' => hrecmem Mv hMc z hz' s hs' t ht')
        (fun _ _ => hT3 Mv hMc)
    have h3' := h3
    rw [happ2] at h3'
    have hsc : sv ∈ˢ (pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) :=
      lam_dom_of_ne h3' hwne sv hs
    obtain ⟨R', hR'i, hfold⟩ := natZero_iota hfindN hvalN hfindZ hvalZ
      hfindSc hvalSc hMc hzc hsc
    rw [interp_natRecZero_rhs hfindN hvalN hfindZ hvalZ hfindSc hvalSc]
      at hR'i
    obtain rfl := Option.some.inj hR'i
    refine ⟨_, interp_natRecZero_rhs hfindN hvalN hfindZ hvalZ hfindSc
      hvalSc, hfold, ?_, ?_, ?_⟩
    · -- R applied to the motive
      refine ⟨Nat.max 1 (ψ uN),
        pi (ψ uN + 1) omega fun _ => univ (ψ uN),
        fun M => pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero,
        ?_, hMc, ?_⟩
      · rw [show nrM (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrM_eq, if_neg h0]]
        refine lam_mem (V := V) fun M hM' => ?_
        rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrZ_eq, if_neg h0]]
        refine lam_mem (V := V) fun z hz' => ?_
        exact lam_mem (V := V) fun _s _ => hz'
      · intro M hM'
        have hSspEq : (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) :=
          pi_congr fun n hn' => by rw [natSuccVal_app hn']
        have hMz' : SetTheory.app M natzero ∈ˢ univ (ψ uN) :=
          app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN))
        have hin : (pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero) ∈ˢ
            univ (Nat.max 1 (ψ uN)) := by
          rw [hSspEq, enUU_eq]
          have hSsp' := hSsp M hM'
          have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
            (B := fun _ => SetTheory.app M natzero)
            hSsp' (fun _ _ => hMz')
          rw [if_neg h0,
            show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
              Nat.le_antisymm
                (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
                (Nat.le_max_left _ _)] at this
          exact this
        have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
          (B := fun _ => pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero)
          hMz' (fun _ _ => hin)
        rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
        exact this
    · -- R Mv applied to the base case
      have hSspEqv : (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n)) =
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) :=
        pi_congr fun n hn' => by rw [natSuccVal_app hn']
      have hMz : SetTheory.app Mv natzero ∈ˢ univ (ψ uN) :=
        hMfib natzero natzero_mem
      have hinv : (pi (ψ uN)
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
          fun _ => SetTheory.app Mv natzero) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
        rw [hSspEqv, enUU_eq]
        have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
          (B := fun _ => SetTheory.app Mv natzero)
          (hSsp Mv hMc) (fun _ _ => hMz)
        rw [if_neg h0,
          show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
            Nat.le_antisymm
              (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
              (Nat.le_max_left _ _)] at this
        exact this
      have happR : SetTheory.app (SetTheory.lam (nrM (ψ uN))
          (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z) Mv =
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app Mv natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                  SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z := by
        rw [show nrM (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrM_eq, if_neg h0]]
        refine app_lam hMc
          (B := fun M => pi (nrZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
            pi (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _ => SetTheory.app M natzero)
          (fun M hM' => lam_mem (V := V) fun z hz' =>
            lam_mem (V := V) fun _s _ => hz')
          (fun M hM' => ?_)
        rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrZ_eq, if_neg h0]]
        have hSspEq : (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) :=
          pi_congr fun n hn' => by rw [natSuccVal_app hn']
        have hMz' : SetTheory.app M natzero ∈ˢ univ (ψ uN) :=
          app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN))
        have hin : (pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero) ∈ˢ
            univ (Nat.max 1 (ψ uN)) := by
          rw [hSspEq, enUU_eq]
          have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
            (B := fun _ => SetTheory.app M natzero)
            (hSsp M hM') (fun _ _ => hMz')
          rw [if_neg h0,
            show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
              Nat.le_antisymm
                (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
                (Nat.le_max_left _ _)] at this
          exact this
        have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
          (B := fun _ => pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero)
          hMz' (fun _ _ => hin)
        rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
        exact this
      refine ⟨Nat.max 1 (ψ uN), SetTheory.app Mv natzero,
        fun _ => pi (ψ uN)
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
          fun _ => SetTheory.app Mv natzero,
        ?_, hzc, fun _ _ => hinv⟩
      rw [happR]
      rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
        rw [nrZ_eq, if_neg h0]]
      refine lam_mem (V := V) fun z hz' => ?_
      exact lam_mem (V := V) fun _s _ => hz'
    · -- R Mv zv applied to the step case
      have hSspEqv : (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n)) =
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) :=
        pi_congr fun n hn' => by rw [natSuccVal_app hn']
      have hMz : SetTheory.app Mv natzero ∈ˢ univ (ψ uN) :=
        hMfib natzero natzero_mem
      have happR : SetTheory.app (SetTheory.lam (nrM (ψ uN))
          (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z) Mv =
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app Mv natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                  SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z := by
        rw [show nrM (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrM_eq, if_neg h0]]
        refine app_lam hMc
          (B := fun M => pi (nrZ (ψ uN)) (SetTheory.app M natzero) fun _ =>
            pi (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _ => SetTheory.app M natzero)
          (fun M hM' => lam_mem (V := V) fun z hz' =>
            lam_mem (V := V) fun _s _ => hz')
          (fun M hM' => ?_)
        rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrZ_eq, if_neg h0]]
        have hSspEq : (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M n) fun _ =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n)) =
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) :=
          pi_congr fun n hn' => by rw [natSuccVal_app hn']
        have hMz' : SetTheory.app M natzero ∈ˢ univ (ψ uN) :=
          app_mem hM' natzero_mem (fun _ _ => univ_mem_univ (ψ uN))
        have hin : (pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero) ∈ˢ
            univ (Nat.max 1 (ψ uN)) := by
          rw [hSspEq, enUU_eq]
          have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
            (B := fun _ => SetTheory.app M natzero)
            (hSsp M hM') (fun _ _ => hMz')
          rw [if_neg h0,
            show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
              Nat.le_antisymm
                (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
                (Nat.le_max_left _ _)] at this
          exact this
        have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
          (B := fun _ => pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app M natzero)
          hMz' (fun _ _ => hin)
        rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
        exact this
      have happR2 : SetTheory.app (SetTheory.app (SetTheory.lam (nrM (ψ uN))
          (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
          SetTheory.lam (nrZ (ψ uN)) (SetTheory.app M natzero) fun z =>
            SetTheory.lam (ψ uN)
              (pi (enUU (ψ uN)) omega fun n =>
                pi (ψ uN) (SetTheory.app M n) fun _ =>
                  SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
              fun _s => z) Mv) zv =
          SetTheory.lam (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
            fun _s => zv := by
        rw [happR]
        rw [show nrZ (ψ uN) = Nat.max 1 (ψ uN) from by
          rw [nrZ_eq, if_neg h0]]
        refine app_lam hzc
          (B := fun _ => pi (ψ uN)
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
            fun _ => SetTheory.app Mv natzero)
          (fun z hz' => lam_mem (V := V) fun _s _ => hz')
          (fun _ _ => ?_)
        rw [hSspEqv, enUU_eq]
        have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := ψ uN)
          (B := fun _ => SetTheory.app Mv natzero)
          (hSsp Mv hMc) (fun _ _ => hMz)
        rw [if_neg h0,
          show Nat.max (Nat.max 1 (ψ uN)) (ψ uN) = Nat.max 1 (ψ uN) from
            Nat.le_antisymm
              (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_max_right _ _⟩)
              (Nat.le_max_left _ _)] at this
        exact this
      refine ⟨ψ uN,
        pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n),
        fun _ => SetTheory.app Mv natzero,
        ?_, ?_, fun _ _ => hMz⟩
      · rw [happR2]
        exact lam_mem (V := V) fun _s _ => hzc
      · rw [hSspEqv, enUU_eq]
        exact hsc


/-- Claims glue for the `Nat.rec` successor rule. -/
theorem natSuccIota_claims {cval : ConstVal V}
    (hfindN : env.find? natName = some natA)
    (hvalN : ∀ ψ' : Name → Nat, cval natName ψ' = omega)
    (hfindZ : env.find? natZeroName = some natZeroA)
    (hvalZ : ∀ ψ' : Name → Nat, cval natZeroName ψ' = natzero)
    (hfindSc : env.find? natSuccName = some natSuccA)
    (hvalSc : ∀ ψ' : Name → Nat, cval natSuccName ψ' = natSuccVal V ψ')
    (hfindR : env.find? (natName.str "rec") = some natRecA)
    (hvalR : ∀ ψ' : Name → Nat, cval (natName.str "rec") ψ' = natRecVal V ψ')
    {Mv zv sv tv nv : V} {vE1 vE2 vE3 vE' : Nat} {A1 A2 A3 A' : V}
    {B1 B2 B3 B' : V → V}
    (h1 : (natRecVal V ψ : V) ∈ˢ pi vE1 A1 B1) (hM : Mv ∈ˢ A1)
    (h2 : SetTheory.app (natRecVal V ψ) Mv ∈ˢ pi vE2 A2 B2) (hz : zv ∈ˢ A2)
    (h3 : SetTheory.app (SetTheory.app (natRecVal V ψ) Mv) zv ∈ˢ pi vE3 A3 B3)
    (hs : sv ∈ˢ A3)
    (hmaj : (natSuccVal V ψ : V) ∈ˢ pi vE' A' B') (hn : nv ∈ˢ A')
    (htv : tv = SetTheory.app (natSuccVal V ψ) nv) :
    ∃ R, interpClosed V cval env ψ natRecSuccRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (natRecVal V ψ) Mv) zv) sv) tv =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app R Mv) zv)
        sv) nv ∧
      AppSlot (V := V) R Mv ∧
      AppSlot (V := V) (SetTheory.app R Mv) zv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app R Mv) zv) sv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app (SetTheory.app R Mv)
        zv) sv) nv := by
  have hnc : nv ∈ˢ omega := by
    have hmaj' := hmaj
    rw [show (natSuccVal V ψ : V) = SetTheory.lam 1 omega natsucc from by
      simp only [natSuccVal]] at hmaj'
    exact lam_dom_of_ne hmaj' (by decide) nv hn
  subst htv
  rw [natSuccVal_app hnc]
  by_cases h0 : ψ uN = 0
  · -- Prop collapse
    refine ⟨_, interp_natRecSucc_rhs hfindN hvalN hfindZ hvalZ hfindSc
      hvalSc hfindR hvalR, ?_⟩
    have hRpt : (SetTheory.lam (enM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n)) = (pt : V) := by
      rw [show enM (ψ uN) = 0 from by rw [enM_eq, if_pos h0]]
      exact lam_zero
    have hrec_pt : (natRecVal V ψ : V) = pt := by
      simp only [natRecVal, h0, reduceIte]
      exact lam_zero
    rw [hRpt, hrec_pt]
    simp only [app_pt]
    exact ⟨trivial,
      ⟨0, A1, fun _ => unitSet, pt_mem_pi_unit (V := V), hM,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A2, fun _ => unitSet, pt_mem_pi_unit (V := V), hz,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, A3, fun _ => unitSet, pt_mem_pi_unit (V := V), hs,
        fun _ _ => unitSet_mem_univ 0⟩,
      ⟨0, omega, fun _ => unitSet, pt_mem_pi_unit (V := V), hnc,
        fun _ _ => unitSet_mem_univ 0⟩⟩
  · -- data levels
    have hwne : Nat.max 1 (ψ uN) ≠ 0 := max_ne_zero_l (by decide)
    -- parametric facts (raw fibre forms)
    have hMfibP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega → SetTheory.app M' n ∈ˢ univ (ψ uN) :=
      fun M' hM' n hn' => app_mem hM' hn' (fun _ _ => univ_mem_univ (ψ uN))
    have hrawP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n) ∈ˢ
          univ (ψ uN) := by
      intro M' hM' n hn'
      rw [natSuccVal_app hn']
      exact hMfibP M' hM' (natsucc n) (natsucc_mem hn')
    have hsfibP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ n, n ∈ˢ omega →
        (pi (ψ uN) (SetTheory.app M' n) fun _ =>
          SetTheory.app M' (natsucc n)) ∈ˢ univ (ψ uN) := by
      intro M' hM' n hn'
      have := pi_mem_univ (u := ψ uN) (v := ψ uN)
        (B := fun _ => SetTheory.app M' (natsucc n))
        (hMfibP M' hM' n hn')
        (fun _ _ => hMfibP M' hM' (natsucc n) (natsucc_mem hn'))
      rw [if_neg h0,
        show Nat.max (ψ uN) (ψ uN) = ψ uN from Nat.max_self _] at this
      exact this
    have hSspEqP : ∀ M' : V,
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) =
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (natsucc n)) := fun M' =>
      pi_congr fun n hn' => by rw [natSuccVal_app hn']
    have hSspP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      rw [hSspEqP M', enUU_eq]
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M' n) fun _ =>
          SetTheory.app M' (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfibP M' hM' n hn')
      rw [if_neg h0] at this
      exact this
    have htTP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => SetTheory.app M'
          (SetTheory.app (natSuccVal V ψ) n))
        (omega_mem_univ (V := V))
        (fun n hn' => hrawP M' hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hs2P : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M' n) fun _ =>
              SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun n =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (ψ uN) omega fun n =>
          SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
        (hSspP M' hM') (fun _ _ => htTP M' hM')
      rw [if_neg hwne, show Nat.max (Nat.max 1 (ψ uN)) (Nat.max 1 (ψ uN)) =
        Nat.max 1 (ψ uN) from Nat.max_self _] at this
      exact this
    have hzTP : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M' natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M' n) fun _ =>
                SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
            fun _ => pi (ψ uN) omega fun n =>
              SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app M' n) fun _ =>
              SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun n =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n))
        (hMfibP M' hM' natzero natzero_mem)
        (fun _ _ => hs2P M' hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have hbody : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ z, z ∈ˢ SetTheory.app M' natzero →
        ∀ s, s ∈ˢ (pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n)) →
        ∀ n, n ∈ˢ omega →
        SetTheory.app (SetTheory.app s n)
          (SetTheory.app (SetTheory.app (SetTheory.app
            (SetTheory.app (natRecVal V ψ) M') z) s) n) ∈ˢ
          SetTheory.app M' (SetTheory.app (natSuccVal V ψ) n) := by
      intro M' hM' z hz' s hs' n hn'
      rw [hSspEqP M', enUU_eq] at hs'
      rw [natRecVal_fold hM' hz' hs' hn', natSuccVal_app hn']
      have hstep' : ∀ k, k ∈ˢ omega → ∀ ih, ih ∈ˢ SetTheory.app M' k →
          SetTheory.app (SetTheory.app s k) ih ∈ˢ
            SetTheory.app M' (natsucc k) := by
        intro k hk ih hih
        exact app_mem (app_mem hs' hk (hsfibP M' hM')) hih
          (fun _ _ => hMfibP M' hM' (natsucc k) (natsucc_mem hk))
      exact hstep' n hn' _ (natrec_mem hz' hstep' hn')
    -- canonical memberships from the original chain
    have hrec_lam : (natRecVal V ψ : V) = SetTheory.lam (Nat.max 1 (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun s =>
            SetTheory.lam (ψ uN) omega fun t => natrec z s t := by
      simp only [natRecVal, if_neg h0]
    have h1' := h1
    rw [hrec_lam] at h1'
    have hMc : Mv ∈ˢ pi (ψ uN + 1) omega (fun _ => univ (ψ uN)) :=
      lam_dom_of_ne h1' hwne Mv hM
    have hrecmem : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        ∀ z, z ∈ˢ SetTheory.app M' natzero →
        ∀ s, s ∈ˢ (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (natsucc n)) →
        ∀ t, t ∈ˢ omega → natrec z s t ∈ˢ SetTheory.app M' t := by
      intro M' hM' z hz' s hs' t ht'
      refine natrec_mem hz' ?_ ht'
      intro k hk ih hih
      exact app_mem (app_mem hs' hk (hsfibP M' hM')) hih
        (fun _ _ => hMfibP M' hM' (natsucc k) (natsucc_mem hk))
    have hT4n : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun t => SetTheory.app M' t)
        (omega_mem_univ (V := V))
        (fun t ht => hMfibP M' hM' t ht)
      rw [if_neg h0] at this
      exact this
    have hSspN : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (ψ uN) omega fun n =>
          pi (ψ uN) (SetTheory.app M' n) fun _ =>
            SetTheory.app M' (natsucc n)) ∈ˢ univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := 1) (v := ψ uN)
        (B := fun n => pi (ψ uN) (SetTheory.app M' n) fun _ =>
          SetTheory.app M' (natsucc n))
        (omega_mem_univ (V := V))
        (fun n hn' => hsfibP M' hM' n hn')
      rw [if_neg h0] at this
      exact this
    have hT3n : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M' n) fun _ =>
              SetTheory.app M' (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := Nat.max 1 (ψ uN)) (v := Nat.max 1 (ψ uN))
        (hSspN M' hM') (fun _ _ => hT4n M' hM')
      rw [if_neg hwne, show Nat.max (Nat.max 1 (ψ uN)) (Nat.max 1 (ψ uN)) =
        Nat.max 1 (ψ uN) from Nat.max_self _] at this
      exact this
    have hT2n : ∀ M' : V, M' ∈ˢ (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) →
        (pi (Nat.max 1 (ψ uN)) (SetTheory.app M' natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M' n) fun _ =>
                SetTheory.app M' (natsucc n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M' t) ∈ˢ
          univ (Nat.max 1 (ψ uN)) := by
      intro M' hM'
      have := pi_mem_univ (u := ψ uN) (v := Nat.max 1 (ψ uN))
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app M' n) fun _ =>
              SetTheory.app M' (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app M' t)
        (hMfibP M' hM' natzero natzero_mem)
        (fun _ _ => hT3n M' hM')
      rw [if_neg hwne, max_absorb_r' 1 (ψ uN)] at this
      exact this
    have happ1 : SetTheory.app (natRecVal V ψ) Mv =
        SetTheory.lam (Nat.max 1 (ψ uN)) (SetTheory.app Mv natzero) fun z =>
          SetTheory.lam (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                SetTheory.app Mv (natsucc n)) fun s =>
            SetTheory.lam (ψ uN) omega fun t => natrec z s t := by
      rw [hrec_lam]
      exact app_lam hMc
        (B := fun M => pi (Nat.max 1 (ψ uN))
          (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (ψ uN) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (natsucc n)) fun _ =>
            pi (ψ uN) omega fun t => SetTheory.app M t)
        (fun M hM' => lam_mem (V := V) fun z hz' =>
          lam_mem (V := V) fun s hs' =>
            lam_mem (V := V) fun t ht' => hrecmem M hM' z hz' s hs' t ht')
        (fun M hM' => hT2n M hM')
    have h2' := h2
    rw [happ1] at h2'
    have hzc : zv ∈ˢ SetTheory.app Mv natzero :=
      lam_dom_of_ne h2' hwne zv hz
    have happ2 : SetTheory.app (SetTheory.app (natRecVal V ψ) Mv) zv =
        SetTheory.lam (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) fun s =>
          SetTheory.lam (ψ uN) omega fun t => natrec zv s t := by
      rw [happ1]
      exact app_lam hzc
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (ψ uN) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (natsucc n)) fun _ =>
          pi (ψ uN) omega fun t => SetTheory.app Mv t)
        (fun z hz' => lam_mem (V := V) fun s hs' =>
          lam_mem (V := V) fun t ht' => hrecmem Mv hMc z hz' s hs' t ht')
        (fun _ _ => hT3n Mv hMc)
    have h3' := h3
    rw [happ2] at h3'
    have hsc : sv ∈ˢ (pi (ψ uN) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (natsucc n)) :=
      lam_dom_of_ne h3' hwne sv hs
    obtain ⟨R', hR'i, hfold⟩ := natSucc_iota hfindN hvalN hfindZ hvalZ
      hfindSc hvalSc hfindR hvalR hMc hzc hsc hnc
    rw [interp_natRecSucc_rhs hfindN hvalN hfindZ hvalZ hfindSc hvalSc
      hfindR hvalR] at hR'i
    obtain rfl := Option.some.inj hR'i
    have henM : enM (ψ uN) = Nat.max 1 (ψ uN) := by rw [enM_eq, if_neg h0]
    have henZ : enZ (ψ uN) = Nat.max 1 (ψ uN) := by rw [enZ_eq, if_neg h0]
    have hen1U : en1U (ψ uN) = Nat.max 1 (ψ uN) := by
      rw [en1U_eq, if_neg h0]
    -- fold applications of R
    have hsc' : sv ∈ˢ (pi (enUU (ψ uN)) omega fun n =>
        pi (ψ uN) (SetTheory.app Mv n) fun _ =>
          SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n)) := by
      rw [hSspEqP Mv, enUU_eq]
      exact hsc
    have happR1 : SetTheory.app (SetTheory.lam (enM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n)) Mv =
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app Mv natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app Mv n) fun _ =>
                SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) Mv) z) s) n) := by
      rw [henM, henZ, hen1U]
      exact app_lam hMc
        (B := fun M => pi (Nat.max 1 (ψ uN))
          (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => pi (ψ uN) omega fun n =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
        (fun M hM' => lam_mem (V := V) fun z hz' =>
          lam_mem (V := V) fun s hs' =>
            lam_mem (V := V) fun n hn' =>
              hbody M hM' z hz' s hs' n hn')
        (fun M hM' => hzTP M hM')
    have happR2 : SetTheory.app (SetTheory.app (SetTheory.lam (enM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n)) Mv) zv =
        SetTheory.lam (en1U (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
          fun s =>
          SetTheory.lam (ψ uN) omega fun n =>
            SetTheory.app (SetTheory.app s n)
              (SetTheory.app (SetTheory.app (SetTheory.app
                (SetTheory.app (natRecVal V ψ) Mv) zv) s) n) := by
      rw [happR1, henZ]
      refine app_lam hzc
        (B := fun _ => pi (Nat.max 1 (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun n =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
        (fun z hz' => by
          rw [hen1U]
          exact lam_mem (V := V) fun s hs' =>
            lam_mem (V := V) fun n hn' =>
              hbody Mv hMc z hz' s hs' n hn')
        (fun _ _ => hs2P Mv hMc)
    have happR3 : SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.lam (enM (ψ uN))
        (pi (ψ uN + 1) omega fun _ => univ (ψ uN)) fun M =>
        SetTheory.lam (enZ (ψ uN)) (SetTheory.app M natzero) fun z =>
          SetTheory.lam (en1U (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun s =>
            SetTheory.lam (ψ uN) omega fun n =>
              SetTheory.app (SetTheory.app s n)
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (natRecVal V ψ) M) z) s) n)) Mv) zv) sv =
        SetTheory.lam (ψ uN) omega fun n =>
          SetTheory.app (SetTheory.app sv n)
            (SetTheory.app (SetTheory.app (SetTheory.app
              (SetTheory.app (natRecVal V ψ) Mv) zv) sv) n) := by
      rw [happR2]
      exact app_lam hsc'
        (B := fun _ => pi (ψ uN) omega fun n =>
          SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
        (fun s hs'' => lam_mem (V := V) fun n hn' =>
          hbody Mv hMc zv hzc s hs'' n hn')
        (fun _ _ => by
          rw [hen1U]
          exact htTP Mv hMc)
    refine ⟨_, interp_natRecSucc_rhs hfindN hvalN hfindZ hvalZ hfindSc
      hvalSc hfindR hvalR, hfold, ?_, ?_, ?_, ?_⟩
    · refine ⟨Nat.max 1 (ψ uN),
        pi (ψ uN + 1) omega fun _ => univ (ψ uN),
        fun M => pi (Nat.max 1 (ψ uN)) (SetTheory.app M natzero) fun _ =>
          pi (Nat.max 1 (ψ uN))
            (pi (enUU (ψ uN)) omega fun n =>
              pi (ψ uN) (SetTheory.app M n) fun _ =>
                SetTheory.app M (SetTheory.app (natSuccVal V ψ) n))
            fun _ => pi (ψ uN) omega fun n =>
              SetTheory.app M (SetTheory.app (natSuccVal V ψ) n),
        ?_, hMc, ?_⟩
      · rw [henM]
        refine lam_mem (V := V) fun M hM' => ?_
        rw [henZ]
        refine lam_mem (V := V) fun z hz' => ?_
        rw [hen1U]
        refine lam_mem (V := V) fun s hs' => ?_
        exact lam_mem (V := V) fun n hn' => hbody M hM' z hz' s hs' n hn'
      · intro M hM'
        exact hzTP M hM'
    · refine ⟨Nat.max 1 (ψ uN), SetTheory.app Mv natzero,
        fun _ => pi (Nat.max 1 (ψ uN))
          (pi (enUU (ψ uN)) omega fun n =>
            pi (ψ uN) (SetTheory.app Mv n) fun _ =>
              SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n))
          fun _ => pi (ψ uN) omega fun n =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n),
        ?_, hzc, ?_⟩
      · rw [happR1, henZ]
        refine lam_mem (V := V) fun z hz' => ?_
        rw [hen1U]
        refine lam_mem (V := V) fun s hs' => ?_
        exact lam_mem (V := V) fun n hn' => hbody Mv hMc z hz' s hs' n hn'
      · intro _ _
        exact hs2P Mv hMc
    · refine ⟨Nat.max 1 (ψ uN),
        pi (enUU (ψ uN)) omega fun n =>
          pi (ψ uN) (SetTheory.app Mv n) fun _ =>
            SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n),
        fun _ => pi (ψ uN) omega fun n =>
          SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n),
        ?_, hsc', ?_⟩
      · rw [happR2]
        rw [hen1U]
        refine lam_mem (V := V) fun s hs'' => ?_
        exact lam_mem (V := V) fun n hn' => hbody Mv hMc zv hzc s hs'' n hn'
      · intro _ _
        exact htTP Mv hMc
    · refine ⟨ψ uN, omega,
        fun n => SetTheory.app Mv (SetTheory.app (natSuccVal V ψ) n),
        ?_, hnc, fun n hn' => hrawP Mv hMc n hn'⟩
      rw [happR3]
      exact lam_mem (V := V) fun n hn' =>
        hbody Mv hMc zv hzc sv hsc' n hn'

end Setlec
