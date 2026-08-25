import Setlec.Model.Basis.Eq.Iota
import Setlec.Model.RuleFold

/-!
# `Eq.rec`: the total λ-equality clause of `RecRulesOk`

The canonical iota left-hand side of the single rule (with its one
index argument, the reflexivity point) interprets, for every level
assignment, to the same set as the stored right-hand side; the fold is
the value-level identity transport `eqRecVal_fold`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-! ## The canonical frame components (computed from the pinned data) -/

/-- The `α` frame variable. -/
def eqFrA : Expr :=
  .fvar 0 (Name.anonymous.str "α") (.sort (.param (Name.anonymous.str "u")))

/-- The `a` frame variable. -/
def eqFra : Expr := .fvar 1 (Name.anonymous.str "a") eqFrA

/-- The `Eq` head. -/
def eqFrEqC : Expr :=
  .const (Name.anonymous.str "Eq") [.param (Name.anonymous.str "u")]

/-- The motive annotation. -/
def eqFrTyM : Expr :=
  .forallE (Name.anonymous.str "b") eqFrA
    (.forallE (Name.anonymous.str "t")
      (.app (.app (.app eqFrEqC eqFrA) eqFra) (.bvar 0))
      (.sort (.param (Name.anonymous.str "u_1")))
      ⟨.default, some (.succ (.param (Name.anonymous.str "u_1")))⟩)
    ⟨.default, some (.imax .zero (.succ (.param (Name.anonymous.str "u_1"))))⟩

/-- The motive frame variable. -/
def eqFrM : Expr := .fvar 2 (Name.anonymous.str "motive") eqFrTyM

/-- The `Eq.refl` head. -/
def eqFrReflC : Expr :=
  .const ((Name.anonymous.str "Eq").str "refl")
    [.param (Name.anonymous.str "u")]

/-- The minor-premise annotation. -/
def eqFrTyRefl : Expr :=
  .app (.app eqFrM eqFra) (.app (.app eqFrReflC eqFrA) eqFra)

/-- The minor-premise frame variable. -/
def eqFrRefl : Expr := .fvar 3 (Name.anonymous.str "refl") eqFrTyRefl

/-- The recursor head of the canonical left-hand side. -/
def eqFrRec : Expr :=
  .const ((Name.anonymous.str "Eq").str "rec")
    [.param (Name.anonymous.str "u_1"), .param (Name.anonymous.str "u")]

/-! ## The value-level fold -/

/-- `Eq.rec`'s value applied through its telescope at the reflexivity
point returns the minor premise (the Prop collapse is
self-handling). -/
theorem eqRecVal_fold {Av av Mv rv : V}
    (hA : Av ∈ˢ univ (ψ uN)) (ha : av ∈ˢ Av)
    (hM : Mv ∈ˢ eqRecMSpace V (ψ u1N) Av av)
    (hr : rv ∈ˢ SetTheory.app (SetTheory.app Mv av) pt) :
    SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
      (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) av)
      pt = rv := by
  have hMv := hM
  simp only [eqRecMSpace] at hMv
  have hMafib : ∀ b', b' ∈ˢ Av →
      (pi (ψ u1N + 1) (eqv av b') fun _ => univ (ψ u1N)) ∈ˢ
        univ (ψ u1N + 1) :=
    fun b' _ => pi_mem_univ (u := 0) (v := ψ u1N + 1)
      (B := fun _ => univ (ψ u1N))
      (eqv_mem_univ av b') (fun _ _ => univ_mem_univ (ψ u1N))
  have hMa : SetTheory.app Mv av ∈ˢ pi (ψ u1N + 1) (eqv av av)
      (fun _ => univ (ψ u1N)) := app_mem hMv ha hMafib
  have hMapt : SetTheory.app (SetTheory.app Mv av) pt ∈ˢ univ (ψ u1N) :=
    app_mem hMa (pt_mem_eqv_self av) (fun _ _ => univ_mem_univ (ψ u1N))
  by_cases h0 : ψ u1N = 0
  · -- Prop collapse
    have hL : SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (eqRecVal V ψ) Av) av) Mv) rv) av)
        pt = pt := by
      have hval : eqRecVal V ψ = (pt : V) := by
        simp only [eqRecVal]
        refine lamC_of_forall fun A hA' => ?_
        refine lamC_of_forall fun a ha' => ?_
        refine lamC_of_forall fun M hM' => ?_
        have hM'' := hM'
        simp only [eqRecMSpace] at hM''
        have hMapt0 : SetTheory.app (SetTheory.app M a) pt ∈ˢ
            univ (ψ u1N) :=
          app_mem_piC (app_mem_piC hM'' ha') (pt_mem_eqv_self a)
        refine lamC_of_forall fun r hr' => ?_
        refine lamC_of_forall fun b hb' => ?_
        exact lamC_of_forall fun h hh' =>
          mem_univ_zero (h0 ▸ hMapt0) hr'
      rw [hval]
      simp only [app_pt]
    rw [hL]
    exact (mem_univ_zero (h0 ▸ hMapt) hr).symm
  · -- data levels
    have hMS : ∀ A : V, A ∈ˢ univ (ψ uN) → ∀ a : V, a ∈ˢ A →
        eqRecMSpace V (ψ u1N) A a ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
      intro A hA' a ha'
      unfold eqRecMSpace
      exact pi_mem_univ (u := ψ uN) (v := ψ u1N + 1) hA'
        (fun b _ => pi_mem_univ (u := 0) (v := ψ u1N + 1)
          (B := fun _ => univ (ψ u1N))
          (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N)))
    have hMapt' : ∀ (A : V), A ∈ˢ univ (ψ uN) → ∀ a, a ∈ˢ A →
        ∀ M, M ∈ˢ eqRecMSpace V (ψ u1N) A a →
        SetTheory.app (SetTheory.app M a) pt ∈ˢ univ (ψ u1N) := by
      intro A _ a ha' M hM'
      simp only [eqRecMSpace] at hM'
      have hMa' : SetTheory.app M a ∈ˢ pi (ψ u1N + 1) (eqv a a)
          (fun _ => univ (ψ u1N)) :=
        app_mem hM' ha' (fun b _ => pi_mem_univ (u := 0) (v := ψ u1N + 1)
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
        intro b _
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
    have hwne : Nat.max (ψ uN) (ψ u1N) ≠ 0 :=
      max_ne_zero_r' h0
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
    simp only [eqRecVal, if_neg h0]
    have h1 := app_lam (v := Nat.max (ψ uN) (ψ u1N + 1)) (a := Av)
      (A := univ (ψ uN)) hA
      (B := fun A => pi (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
        pi (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a) fun M =>
          pi (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun _ =>
            pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
              SetTheory.app (SetTheory.app M a) pt)
      (F := fun A => SetTheory.lam (Nat.max (ψ uN) (ψ u1N + 1)) A fun a =>
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N)) (eqRecMSpace V (ψ u1N) A a)
          fun M => SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
            (SetTheory.app (SetTheory.app M a) pt) fun r =>
            SetTheory.lam (ψ u1N) A fun _b =>
              SetTheory.lam (ψ u1N) (eqv a _b) fun _h => r)
      (fun A _ => lam_mem (V := V) fun a _ =>
        lam_mem (V := V) fun M _ =>
          lam_mem (V := V) fun r hr' =>
            lam_mem (V := V) fun b _ =>
              lam_mem (V := V) fun h _ => hr')
      (fun A hA' => by
        have := pi_mem_univ (u := ψ uN) (v := Nat.max (ψ uN) (ψ u1N + 1))
          (B := fun a => pi (Nat.max (ψ uN) (ψ u1N))
            (eqRecMSpace V (ψ u1N) A a) fun M =>
            pi (Nat.max (ψ uN) (ψ u1N))
              (SetTheory.app (SetTheory.app M a) pt) fun _ =>
              pi (ψ u1N) A fun b => pi (ψ u1N) (eqv a b) fun _ =>
                SetTheory.app (SetTheory.app M a) pt)
          hA' (fun a ha' => hT3 A hA' a ha')
        rw [if_neg (max_ne_zero_r' (Nat.succ_ne_zero _)),
          max_absorb_l'] at this
        exact this)
    rw [h1]
    have h2 := app_lam (v := Nat.max (ψ uN) (ψ u1N + 1)) (a := av)
      (A := Av) ha
      (B := fun a => pi (Nat.max (ψ uN) (ψ u1N))
        (eqRecMSpace V (ψ u1N) Av a) fun M =>
        pi (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a) pt) fun _ =>
          pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv a b) fun _ =>
            SetTheory.app (SetTheory.app M a) pt)
      (F := fun a => SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
        (eqRecMSpace V (ψ u1N) Av a) fun M =>
        SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a) pt) fun r =>
          SetTheory.lam (ψ u1N) Av fun _b =>
            SetTheory.lam (ψ u1N) (eqv a _b) fun _h => r)
      (fun a _ => lam_mem (V := V) fun M _ =>
        lam_mem (V := V) fun r hr' =>
          lam_mem (V := V) fun b _ =>
            lam_mem (V := V) fun h _ => hr')
      (fun a ha' => hT3 Av hA a ha')
    rw [h2]
    have h3 := app_lam (v := Nat.max (ψ uN) (ψ u1N)) (a := Mv)
      (A := eqRecMSpace V (ψ u1N) Av av) hM
      (B := fun M => pi (Nat.max (ψ uN) (ψ u1N))
        (SetTheory.app (SetTheory.app M av) pt) fun _ =>
        pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv av b) fun _ =>
          SetTheory.app (SetTheory.app M av) pt)
      (F := fun M => SetTheory.lam (Nat.max (ψ uN) (ψ u1N))
        (SetTheory.app (SetTheory.app M av) pt) fun r =>
        SetTheory.lam (ψ u1N) Av fun _b =>
          SetTheory.lam (ψ u1N) (eqv av _b) fun _h => r)
      (fun M _ => lam_mem (V := V) fun r hr' =>
        lam_mem (V := V) fun b _ =>
          lam_mem (V := V) fun h _ => hr')
      (fun M hM' => hT4 Av hA av ha M hM')
    rw [h3]
    have h4 := app_lam (v := Nat.max (ψ uN) (ψ u1N)) (a := rv)
      (A := SetTheory.app (SetTheory.app Mv av) pt) hr
      (B := fun _ => pi (ψ u1N) Av fun b => pi (ψ u1N) (eqv av b) fun _ =>
        SetTheory.app (SetTheory.app Mv av) pt)
      (F := fun r => SetTheory.lam (ψ u1N) Av fun _b =>
        SetTheory.lam (ψ u1N) (eqv av _b) fun _h => r)
      (fun r hr' => lam_mem (V := V) fun b _ =>
        lam_mem (V := V) fun h _ => hr')
      (fun _ _ => hT5 Av hA av ha Mv hM)
    rw [h4]
    have h5 := app_lam (v := ψ u1N) (a := av) (A := Av) ha
      (B := fun b => pi (ψ u1N) (eqv av b) fun _ =>
        SetTheory.app (SetTheory.app Mv av) pt)
      (F := fun _b => SetTheory.lam (ψ u1N) (eqv av _b) fun _h => rv)
      (fun b _ => lam_mem (V := V) fun h _ => hr)
      (fun b _ => by
        have := pi_mem_univ (u := 0) (v := ψ u1N)
          (B := fun _ => SetTheory.app (SetTheory.app Mv av) pt)
          (eqv_mem_univ av b) (fun _ _ => hMapt)
        rw [if_neg h0] at this
        exact this)
    rw [h5]
    exact app_lam (v := ψ u1N) (a := pt) (A := eqv av av)
      (pt_mem_eqv_self av)
      (B := fun _ => SetTheory.app (SetTheory.app Mv av) pt)
      (F := fun _h => rv)
      (fun _ _ => hr)
      (fun _ _ => hMapt)

/-! ## The interp-form motive space and the tower fibre facts -/

/-- The interp-form motive space folds to `eqRecMSpace`. -/
theorem eqFr_MSpI_eq {A a : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
      fun _ => univ (ψ u1N)) = eqRecMSpace V (ψ u1N) A a := by
  unfold eqRecMSpace
  exact pi_congr fun b hb => by rw [eqVal_app₃ hA ha hb]

/-- Membership of the interp-form motive space in its universe. -/
theorem eqFr_MSpI_mem {A a : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
      fun _ => univ (ψ u1N)) ∈ˢ univ (Nat.max (ψ uN) (ψ u1N + 1)) := by
  rw [eqFr_MSpI_eq hA ha]
  unfold eqRecMSpace
  exact pi_mem_univ (u := ψ uN) (v := ψ u1N + 1) hA
    (fun b _ => pi_mem_univ (u := 0) (v := ψ u1N + 1)
      (B := fun _ => univ (ψ u1N))
      (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N)))

/-- Each interp-form motive fibre space lives in its universe. -/
theorem eqFr_Mfib_mem {A a b : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A)
    (hb : b ∈ˢ A) :
    (pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
      fun _ => univ (ψ u1N)) ∈ˢ univ (ψ u1N + 1) := by
  rw [eqVal_app₃ hA ha hb]
  exact pi_mem_univ (u := 0) (v := ψ u1N + 1) (B := fun _ => univ (ψ u1N))
    (eqv_mem_univ a b) (fun _ _ => univ_mem_univ (ψ u1N))

/-- The minor premise's space is in the motive universe. -/
theorem eqFr_reflv_mem {A a M : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A)
    (hM : M ∈ˢ pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
      fun _ => univ (ψ u1N)) :
    SetTheory.app (SetTheory.app M a)
      (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a) ∈ˢ
      univ (ψ u1N) := by
  rw [eqReflVal_app₂ hA ha]
  have hMa : SetTheory.app M a ∈ˢ pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a)
      (fun _ => univ (ψ u1N)) :=
    app_mem hM ha (fun b hb => eqFr_Mfib_mem hA ha hb)
  refine app_mem hMa ?_ (fun _ _ => univ_mem_univ (ψ u1N))
  rw [eqVal_app₃ hA ha ha]
  exact pt_mem_eqv_self a

/-- The residual motive value at an index and proof. -/
theorem eqFr_E6 {A a b M : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A)
    (hb : b ∈ˢ A)
    (hM : M ∈ˢ pi (ψ u1N + 1) A fun b' => pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b')
      fun _ => univ (ψ u1N)) :
    ∀ h, h ∈ˢ SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a)
        b →
      SetTheory.app (SetTheory.app M b) h ∈ˢ univ (ψ u1N) := by
  intro h hh
  exact app_mem (app_mem hM hb (fun b' hb' => eqFr_Mfib_mem hA ha hb')) hh
    (fun _ _ => univ_mem_univ (ψ u1N))

theorem eqFr_E5 {A a b M : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A)
    (hb : b ∈ˢ A)
    (hM : M ∈ˢ pi (ψ u1N + 1) A fun b' => pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b')
      fun _ => univ (ψ u1N)) :
    (pi (ψ u1N)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
      fun h => SetTheory.app (SetTheory.app M b) h) ∈ˢ
      univ (erB (ψ u1N)) := by
  have hdom : SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a)
      b ∈ˢ univ 0 := by
    rw [eqVal_app₃ hA ha hb]
    exact eqv_mem_univ a b
  have := pi_mem_univ (u := 0) (v := ψ u1N) hdom (eqFr_E6 hA ha hb hM)
  rw [erB_eq]
  by_cases h0 : ψ u1N = 0
  · simpa [h0] using this
  · simpa [h0, Nat.zero_max] using this

theorem eqFr_E4 {A a M : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A)
    (hM : M ∈ˢ pi (ψ u1N + 1) A fun b' => pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b')
      fun _ => univ (ψ u1N)) :
    (pi (erB (ψ u1N)) A fun b => pi (ψ u1N)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
      fun h => SetTheory.app (SetTheory.app M b) h) ∈ˢ
      univ (erRefl (ψ uN) (ψ u1N)) :=
  pi_mem_univ (u := ψ uN) (v := erB (ψ u1N)) hA
    (fun _b hb => eqFr_E5 hA ha hb hM)

theorem eqFr_E3 {A a M : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A)
    (hM : M ∈ˢ pi (ψ u1N + 1) A fun b' => pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b')
      fun _ => univ (ψ u1N)) :
    (pi (erRefl (ψ uN) (ψ u1N))
      (SetTheory.app (SetTheory.app M a)
        (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
      fun _ => pi (erB (ψ u1N)) A fun b => pi (ψ u1N)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
        fun h => SetTheory.app (SetTheory.app M b) h) ∈ˢ
      univ (erM (ψ uN) (ψ u1N)) :=
  pi_mem_univ (u := ψ u1N) (v := erRefl (ψ uN) (ψ u1N))
    (eqFr_reflv_mem hA ha hM) (fun _ _ => eqFr_E4 hA ha hM)

theorem eqFr_E2 {A a : V} (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    (pi (erM (ψ uN) (ψ u1N))
      (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
        fun _ => univ (ψ u1N))
      fun M => pi (erRefl (ψ uN) (ψ u1N))
        (SetTheory.app (SetTheory.app M a)
          (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
        fun _ => pi (erB (ψ u1N)) A fun b => pi (ψ u1N)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun h => SetTheory.app (SetTheory.app M b) h) ∈ˢ
      univ (erA (ψ uN) (ψ u1N)) := by
  have h := pi_mem_univ (u := Nat.max (ψ uN) (ψ u1N + 1))
    (v := erM (ψ uN) (ψ u1N)) (eqFr_MSpI_mem hA ha)
    (fun M hM => eqFr_E3 hA ha hM)
  have hcast : (if erM (ψ uN) (ψ u1N) = 0 then 0
      else Nat.max (Nat.max (ψ uN) (ψ u1N + 1)) (erM (ψ uN) (ψ u1N))) =
      erA (ψ uN) (ψ u1N) := by
    unfold erA
    by_cases h' : erM (ψ uN) (ψ u1N) = 0
    · simp [h']
    · rw [if_neg h', if_neg h']
      exact Nat.max_assoc _ _ _
  rw [hcast] at h
  exact h

theorem eqFr_E1 {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    (pi (erA (ψ uN) (ψ u1N)) A fun a =>
      pi (erM (ψ uN) (ψ u1N))
        (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
          (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
          fun _ => univ (ψ u1N))
        fun M => pi (erRefl (ψ uN) (ψ u1N))
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a))
          fun _ => pi (erB (ψ u1N)) A fun b => pi (ψ u1N)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a)
              b)
            fun h => SetTheory.app (SetTheory.app M b) h) ∈ˢ
      univ (erAl (ψ uN) (ψ u1N)) :=
  pi_mem_univ (u := ψ uN) (v := erA (ψ uN) (ψ u1N)) hA
    (fun _a ha => eqFr_E2 hA ha)

/-! ## Stage facts -/

theorem eqFr_interp_tyM {cval : ConstVal V} {A a : V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ') :
    interpExpr V cval env ψ 2 (updV V (updV V (rho0 V) 0 A) 1 a) eqFrTyM =
      some (pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
        fun _ => univ (ψ u1N)) := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  simp [eqFrTyM, eqFrEqC, eqFrA, eqFra, interpExpr, Expr.instantiate1, updV,
    hfindE', hvalE', eqA, ConstantInfo.toConstantVal, Level.eval, u1N,
    -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
  try rfl

theorem eqFr_annotOk_tyM {cval : ConstVal V} {A a : V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A) :
    AnnotOk V cval env ψ 2 (updV V (updV V (rho0 V) 0 A) 1 a) eqFrTyM := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  simp only [eqFrTyM, eqFrEqC, eqFrA, eqFra, AnnotOk]
  refine ⟨trivial, ψ u1N + 1, ?_⟩
  refine ⟨?_, ?_⟩
  · first
      | (rintro v ⟨rfl⟩; exact fun z hz => hz)
      | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
      | (rintro v ⟨rfl⟩
         intro z hz
         refine univ_mono ?_ z hz
         simp only [Level.eval, erAl, erA, erA₀, erM, erRefl, erB, uN, u1N]
         by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "u_1") = 0 <;> by_cases h3 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2, h3] <;> omega)
  intro b Sb hSb hb
  have hSb' : Sb = A := by
    simp [interpExpr, updV] at hSb
    exact hSb.symm
  rw [hSb'] at hb
  refine ⟨?_, ?_⟩
  · -- the opened `∀ (t : Eq α a b), Sort u_1`
    try simp only [Expr.instantiate1, reduceIte, AnnotOk]
    refine ⟨⟨⟨⟨trivial, trivial,
        eqVal V ψ, A, Nat.max (ψ uN) (Nat.max (ψ uN) 1), univ (ψ uN),
        (fun X => pi (Nat.max (ψ uN) 1) X fun _ => pi 1 X fun _ => univ 0),
        ?_, ?_, eqVal_mem, hA, fun X hX => eq_fibre_mem hX⟩,
      trivial,
      SetTheory.app (eqVal V ψ) A, a, Nat.max (ψ uN) 1, A,
        (fun _ => pi 1 A fun _ => univ 0),
        ?_, ?_, eqVal_app_mem hA, ha,
        fun _ _ => pi_mem_univ (u := ψ uN) (v := 1)
          (B := fun _ => univ 0) hA (fun _ _ => univ_mem_univ 0)⟩,
      trivial,
      SetTheory.app (SetTheory.app (eqVal V ψ) A) a, b, 1, A,
        (fun _ => univ 0),
        ?_, ?_, eqVal_app₂_mem hA ha, hb,
        fun _ _ => univ_mem_univ 0⟩, ψ u1N + 1, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE', eqA,
        ConstantInfo.toConstantVal]
      try rfl
    · simp [interpExpr, Expr.instantiate1, updV]
    · rw [interpExpr]
      simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE', eqA,
        ConstantInfo.toConstantVal]
      try rfl
    · simp [interpExpr, Expr.instantiate1, updV]
    · rw [interpExpr]
      simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE', eqA,
        ConstantInfo.toConstantVal]
      try rfl
    · simp [interpExpr, Expr.instantiate1, updV]
    · refine ⟨?_, ?_⟩
      · first
          | (rintro v ⟨rfl⟩; exact fun z hz => hz)
          | (rintro v ⟨rfl⟩; exact univ_mono (Nat.zero_le _))
          | (rintro v ⟨rfl⟩
             intro z hz
             refine univ_mono ?_ z hz
             simp only [Level.eval, erAl, erA, erA₀, erM, erRefl, erB, uN, u1N]
             by_cases h1 : ψ (Name.anonymous.str "u") = 0 <;> by_cases h2 : ψ (Name.anonymous.str "u_1") = 0 <;> by_cases h3 : ψ (Name.anonymous.str "v") = 0 <;> simp [h1, h2, h3] <;> omega)
      intro t St hSt ht
      refine ⟨(by simp [Expr.instantiate1, AnnotOk]), ?_⟩
      refine ⟨univ (ψ u1N), ?_, ?_⟩
      · simp [interpExpr, Expr.instantiate1, updV, Level.eval, u1N]
      · exact univ_mem_univ (ψ u1N)
  · refine ⟨pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
      (fun _ => univ (ψ u1N)), ?_, ?_⟩
    · simp [interpExpr, Expr.instantiate1, updV, hfindE', hvalE', eqA,
        ConstantInfo.toConstantVal, Level.eval, u1N,
        -ite_eq_left_iff, -ite_eq_right_iff, -Nat.max_eq_zero_iff]
      try rfl
    · exact eqFr_Mfib_mem hA ha hb

theorem eqFr_interp_tyRefl {cval : ConstVal V} {A a M : V}
    (hfindRe : env.find? eqReflName = some eqReflA)
    (hvalRe : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ') :
    interpExpr V cval env ψ 3
      (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) eqFrTyRefl =
      some (SetTheory.app (SetTheory.app M a)
        (SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a)) := by
  have hfindRe' : env.find? ((Name.anonymous.str "Eq").str "refl") =
      some eqReflA := hfindRe
  have hvalRe' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' :=
    hvalRe
  simp [eqFrTyRefl, eqFrM, eqFrTyM, eqFrEqC, eqFrReflC, eqFrA, eqFra,
    interpExpr, updV, hfindRe', hvalRe', eqReflA,
    ConstantInfo.toConstantVal]
  try rfl

theorem eqFr_annotOk_tyRefl {cval : ConstVal V} {A a M : V}
    (hfindRe : env.find? eqReflName = some eqReflA)
    (hvalRe : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ')
    (hA : A ∈ˢ univ (ψ uN)) (ha : a ∈ˢ A)
    (hM : M ∈ˢ pi (ψ u1N + 1) A fun b => pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
      fun _ => univ (ψ u1N)) :
    AnnotOk V cval env ψ 3
      (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) eqFrTyRefl := by
  have hfindRe' : env.find? ((Name.anonymous.str "Eq").str "refl") =
      some eqReflA := hfindRe
  have hvalRe' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' :=
    hvalRe
  have hMa : SetTheory.app M a ∈ˢ pi (ψ u1N + 1)
      (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a)
      (fun _ => univ (ψ u1N)) :=
    app_mem hM ha (fun b hb => eqFr_Mfib_mem hA ha hb)
  simp only [eqFrTyRefl, eqFrM, eqFrTyM, eqFrEqC, eqFrReflC, eqFrA, eqFra,
    AnnotOk]
  refine ⟨⟨trivial, trivial,
      M, a, ψ u1N + 1, A,
      (fun b => pi (ψ u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) b)
        fun _ => univ (ψ u1N)),
      (by simp [interpExpr, updV]), (by simp [interpExpr, updV]),
      hM, ha, fun b hb => eqFr_Mfib_mem hA ha hb⟩,
    ⟨⟨trivial, trivial,
      eqReflVal V ψ, A, 0, univ (ψ uN), (fun X => pi 0 X fun x => eqv x x),
      (by simp [interpExpr, updV, hfindRe', hvalRe', eqReflA,
        ConstantInfo.toConstantVal]; try rfl),
      (by simp [interpExpr, updV]),
      eqReflVal_mem, hA,
      fun X hX => by
        simpa using pi_mem_univ (u := ψ uN) (v := 0) hX
          (fun x _ => eqv_mem_univ x x)⟩,
    trivial,
    SetTheory.app (eqReflVal V ψ) A, a, 0, A, (fun x => eqv x x),
      (by rw [interpExpr]
          simp [interpExpr, updV, hfindRe', hvalRe', eqReflA,
            ConstantInfo.toConstantVal]
          try rfl),
      (by simp [interpExpr, updV]),
      eqReflVal_app_mem hA, ha, fun x _ => eqv_mem_univ x x⟩,
    SetTheory.app M a,
    SetTheory.app (SetTheory.app (eqReflVal V ψ) A) a,
    ψ u1N + 1,
    SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ) A) a) a,
    (fun _ => univ (ψ u1N)),
    ?_, ?_, hMa, ?_, fun _ _ => univ_mem_univ (ψ u1N)⟩
  · rw [interpExpr]
    simp [interpExpr, updV]
  · rw [interpExpr]
    simp [interpExpr, updV, hfindRe', hvalRe', eqReflA,
      ConstantInfo.toConstantVal]
    try rfl
  · rw [eqReflVal_app₂ hA ha, eqVal_app₃ hA ha ha]
    exact pt_mem_eqv_self a

/-! ## The `RecRulesOk` clause of the rule -/

/-- The `RecRulesOk` clause of `Eq.rec`'s single rule. -/
theorem eqRec_ruleOk {cval : ConstVal V}
    (hfindE : env.find? eqName = some eqA)
    (hvalE : ∀ ψ' : Name → Nat, cval eqName ψ' = eqVal V ψ')
    (hfindRe : env.find? eqReflName = some eqReflA)
    (hvalRe : ∀ ψ' : Name → Nat, cval eqReflName ψ' = eqReflVal V ψ')
    (hfindRc : env.find? (eqName.str "rec") = some eqRecA)
    (hvalRc : ∀ ψ' : Name → Nat,
      cval (eqName.str "rec") ψ' = eqRecVal V ψ') :
    ∃ fvms bL,
      ruleLhsParts (eqName.str "rec") eqRecA.toConstantVal 4
        ((ConstantInfo.recRules eqRecA).getD 0 default)
        eqReflA.toConstantVal = some (fvms, bL) ∧
      FrameWf 0 fvms bL ∧
      fvms.length = 4 +
        RecRule.nfields ((ConstantInfo.recRules eqRecA).getD 0 default) ∧
      (closeLamsAt fvms bL).constsResolve env = true ∧
      ∀ ψ' : Name → Nat,
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' eqRecRhsA = some Rv := by
  have hfindE' : env.find? (Name.anonymous.str "Eq") = some eqA := hfindE
  have hvalE' : ∀ ψ' : Name → Nat,
      cval (Name.anonymous.str "Eq") ψ' = eqVal V ψ' := hvalE
  have hfindRe' : env.find? ((Name.anonymous.str "Eq").str "refl") =
      some eqReflA := hfindRe
  have hvalRe' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "refl") ψ' = eqReflVal V ψ' :=
    hvalRe
  have hfindRc' : env.find? ((Name.anonymous.str "Eq").str "rec") =
      some eqRecA := hfindRc
  have hvalRc' : ∀ ψ' : Name → Nat,
      cval ((Name.anonymous.str "Eq").str "rec") ψ' = eqRecVal V ψ' :=
    hvalRc
  have hparts : ruleLhsParts (eqName.str "rec") eqRecA.toConstantVal 4
      ((ConstantInfo.recRules eqRecA).getD 0 default)
      eqReflA.toConstantVal = some
      ([(eqFrA, ⟨.implicit, some (.imax (.param (Name.anonymous.str "u"))
          (.imax (.imax (.param (Name.anonymous.str "u"))
            (.imax .zero (.succ (.param (Name.anonymous.str "u_1")))))
            (.imax (.param (Name.anonymous.str "u_1"))
              (.param (Name.anonymous.str "u_1")))))⟩),
        (eqFra, ⟨.default, some (.imax
          (.imax (.param (Name.anonymous.str "u"))
            (.imax .zero (.succ (.param (Name.anonymous.str "u_1")))))
          (.imax (.param (Name.anonymous.str "u_1"))
            (.param (Name.anonymous.str "u_1"))))⟩),
        (eqFrM, ⟨.default, some (.imax (.param (Name.anonymous.str "u_1"))
          (.param (Name.anonymous.str "u_1")))⟩),
        (eqFrRefl, ⟨.default,
          some (.param (Name.anonymous.str "u_1"))⟩)],
       .app (.app (.app (.app (.app (.app eqFrRec eqFrA) eqFra) eqFrM)
           eqFrRefl) eqFra)
         (.app (.app eqFrReflC eqFrA) eqFra)) := by rfl
  obtain ⟨hwf, hlen⟩ := ruleLhsParts_frameWf hparts rfl rfl rfl rfl
    (fun _ _ h => nomatch h)
  refine ⟨_, _, hparts, hwf, hlen, ?_, ?_⟩
  · exact ruleLhsParts_resolve hparts
      (by rw [hfindRc]; rfl)
      (show (env.find? ((Name.anonymous.str "Eq").str "refl")).isSome = true
        by rw [hfindRe']; rfl)
      (by simp [ConstantInfo.toConstantVal, eqRecA, Expr.constsResolve,
        hfindE', hfindRe'])
      (by simp [ConstantInfo.toConstantVal, eqReflA, Expr.constsResolve,
        hfindE'])
      (fun _ _ h => nomatch h)
  · intro ψ'
    have hAR : AnnotOk V cval env ψ' 0 (rho0 V) eqRecRhsA :=
      annotOk_eqRec_rhs (cval := cval) (ψ := ψ') hfindE hvalE hfindRe hvalRe
    have hstep : ∀ {fvms : List (Expr × BinderMeta)} {bL : Expr},
        FrameWf 0 fvms bL →
        TowerOk (V := V) cval env ψ' 0 (rho0 V) fvms bL eqRecRhsA →
        AnnotOk V cval env ψ' 0 (rho0 V) (closeLamsAt fvms bL) ∧
        ∃ Rv, interpClosed V cval env ψ' (closeLamsAt fvms bL) = some Rv ∧
          interpClosed V cval env ψ' eqRecRhsA = some Rv := by
      intro fvms bL hwf' ht
      obtain ⟨⟨Rv, hL, hR⟩, hA⟩ := TowerOk.out ht hwf' hAR
      exact ⟨hA, Rv, hL, hR⟩
    refine hstep hwf ?_
    have hityA : interpExpr V cval env ψ' 0 (rho0 V)
        (Expr.sort (Level.param (Name.anonymous.str "u"))) =
        some (univ (ψ' uN)) := by
      simp [interpExpr, Level.eval, uN]
    refine TowerOk.cons (A := univ (ψ' uN)) hityA hityA
      (by simp [AnnotOk]) ?_
    intro A hA
    have hitya : interpExpr V cval env ψ' 1 (updV V (rho0 V) 0 A) eqFrA =
        some A := by
      simp [eqFrA, interpExpr, updV]
    refine TowerOk.cons (A := A) hitya hitya (by simp [eqFrA, AnnotOk]) ?_
    intro a ha
    refine TowerOk.cons (A := pi (ψ' u1N + 1) A fun b => pi (ψ' u1N + 1)
        (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ') A) a) b)
        fun _ => univ (ψ' u1N))
      (eqFr_interp_tyM hfindE hvalE) (eqFr_interp_tyM hfindE hvalE)
      (eqFr_annotOk_tyM hfindE hvalE hA ha) ?_
    intro M hM
    refine TowerOk.cons (A := SetTheory.app (SetTheory.app M a)
        (SetTheory.app (SetTheory.app (eqReflVal V ψ') A) a))
      (eqFr_interp_tyRefl hfindRe hvalRe) (eqFr_interp_tyRefl hfindRe hvalRe)
      (eqFr_annotOk_tyRefl hfindRe hvalRe hA ha hM) ?_
    intro r hr
    -- interpretation of the bottom pieces
    have hsub2 : Level.substFn ψ'
        [Name.anonymous.str "u_1", Name.anonymous.str "u"]
        [Level.param (Name.anonymous.str "u_1"),
         Level.param (Name.anonymous.str "u")] = ψ' :=
      funext fun _ => Level.substFn_map_param
    have hsub1 : Level.substFn ψ' [Name.anonymous.str "u"]
        [Level.param (Name.anonymous.str "u")] = ψ' :=
      funext fun _ => Level.substFn_map_param
    have hirec : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        eqFrRec = some (eqRecVal V ψ') := by
      simp only [eqFrRec, interpExpr, hfindRc', eqRecA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte, hsub2, hvalRc']
    have hireflC : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        eqFrReflC = some (eqReflVal V ψ') := by
      simp only [eqFrReflC, interpExpr, hfindRe', eqReflA,
        ConstantInfo.toConstantVal, List.length_cons, List.length_nil,
        reduceIte, hsub1, hvalRe']
    have hifvA : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        eqFrA = some A := by
      simp [eqFrA, interpExpr, updV]
    have hifva : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        eqFra = some a := by
      simp [eqFra, interpExpr, updV]
    have hifvM : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        eqFrM = some M := by
      simp [eqFrM, interpExpr, updV]
    have hifvRefl : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        eqFrRefl = some r := by
      simp [eqFrRefl, interpExpr, updV]
    have hip1 : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        (.app eqFrRec eqFrA) = some (SetTheory.app (eqRecVal V ψ') A) := by
      rw [interpExpr, hirec, hifvA]
    have hip2 : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        (.app (.app eqFrRec eqFrA) eqFra) =
        some (SetTheory.app (SetTheory.app (eqRecVal V ψ') A) a) := by
      rw [interpExpr, hip1, hifva]
    have hip3 : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        (.app (.app (.app eqFrRec eqFrA) eqFra) eqFrM) =
        some (SetTheory.app (SetTheory.app (SetTheory.app (eqRecVal V ψ') A)
          a) M) := by
      rw [interpExpr, hip2, hifvM]
    have hip4 : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        (.app (.app (.app (.app eqFrRec eqFrA) eqFra) eqFrM) eqFrRefl) =
        some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (eqRecVal V ψ') A) a) M) r) := by
      rw [interpExpr, hip3, hifvRefl]
    have hip5 : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        (.app (.app (.app (.app (.app eqFrRec eqFrA) eqFra) eqFrM) eqFrRefl)
          eqFra) =
        some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (eqRecVal V ψ') A) a) M) r) a) := by
      rw [interpExpr, hip4, hifva]
    have hir1 : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        (.app eqFrReflC eqFrA) = some (SetTheory.app (eqReflVal V ψ') A) := by
      rw [interpExpr, hireflC, hifvA]
    have hir2 : interpExpr V cval env ψ' 4
        (updV V (updV V (updV V (updV V (rho0 V) 0 A) 1 a) 2 M) 3 r)
        (.app (.app eqFrReflC eqFrA) eqFra) =
        some (SetTheory.app (SetTheory.app (eqReflVal V ψ') A) a) := by
      rw [interpExpr, hir1, hifva]
    -- the recursor value's membership in its interpreted type
    obtain ⟨T, hT, hmem⟩ := eqRec_key (cval := cval) (env := env) (ψ := ψ')
      hfindE hvalE hfindRe hvalRe
    rw [interp_eqRec_type hfindE hvalE hfindRe hvalRe] at hT
    obtain rfl := Option.some.inj hT
    have hm1 := app_mem hmem hA (fun A' hA' => eqFr_E1 hA')
    have hm2 := app_mem hm1 ha (fun a' ha' => eqFr_E2 hA ha')
    have hm3 := app_mem hm2 hM (fun M' hM' => eqFr_E3 hA ha hM')
    have hm4 := app_mem hm3 hr (fun _ _ => eqFr_E4 hA ha hM)
    have hm5 := app_mem hm4 ha (fun b hb => eqFr_E5 hA ha hb hM)
    have hreflv : SetTheory.app (SetTheory.app (eqReflVal V ψ') A) a ∈ˢ
        SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ') A) a) a := by
      rw [eqReflVal_app₂ hA ha, eqVal_app₃ hA ha ha]
      exact pt_mem_eqv_self a
    have hM' : M ∈ˢ eqRecMSpace V (ψ' u1N) A a :=
      eqFr_MSpI_eq (V := V) (ψ := ψ') hA ha ▸ hM
    have hr' : r ∈ˢ SetTheory.app (SetTheory.app M a) pt := by
      rw [eqReflVal_app₂ hA ha] at hr
      exact hr
    refine TowerOk.nil (w := r) ?_ ?_ ?_
    · rw [interpExpr, hip5, hir2]
      show some (SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (eqRecVal V ψ') A) a) M) r) a)
        (SetTheory.app (SetTheory.app (eqReflVal V ψ') A) a)) = some r
      rw [eqReflVal_app₂ hA ha, eqRecVal_fold hA ha hM' hr']
    · simp [eqFrRefl, Expr.instantiate1, interpExpr, updV]
    · simp only [AnnotOk, eqFrRec, eqFrReflC, eqFrA, eqFra, eqFrM, eqFrTyM,
        eqFrEqC, eqFrRefl, eqFrTyRefl]
      exact ⟨⟨⟨⟨⟨⟨trivial, trivial,
          eqRecVal V ψ', A, erAl (ψ' uN) (ψ' u1N), univ (ψ' uN), _,
          hirec, hifvA, hmem, hA, fun A' hA' => eqFr_E1 hA'⟩,
        trivial,
        SetTheory.app (eqRecVal V ψ') A, a, erA (ψ' uN) (ψ' u1N), A, _,
          hip1, hifva, hm1, ha, fun a' ha' => eqFr_E2 hA ha'⟩,
        trivial,
        SetTheory.app (SetTheory.app (eqRecVal V ψ') A) a, M,
          erM (ψ' uN) (ψ' u1N),
          (pi (ψ' u1N + 1) A fun b => pi (ψ' u1N + 1)
            (SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ') A) a)
              b) fun _ => univ (ψ' u1N)), _,
          hip2, hifvM, hm2, hM, fun M' hM' => eqFr_E3 hA ha hM'⟩,
        trivial,
        SetTheory.app (SetTheory.app (SetTheory.app (eqRecVal V ψ') A) a) M,
          r, erRefl (ψ' uN) (ψ' u1N),
          (SetTheory.app (SetTheory.app M a)
            (SetTheory.app (SetTheory.app (eqReflVal V ψ') A) a)), _,
          hip3, hifvRefl, hm3, hr, fun _ _ => eqFr_E4 hA ha hM⟩,
        trivial,
        SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (eqRecVal V ψ') A) a) M) r, a, erB (ψ' u1N), A, _,
          hip4, hifva, hm4, ha, fun b hb => eqFr_E5 hA ha hb hM⟩,
        ⟨⟨trivial, trivial,
          eqReflVal V ψ', A, 0, univ (ψ' uN),
          (fun X => pi 0 X fun x => eqv x x),
          hireflC, hifvA, eqReflVal_mem, hA,
          fun X hX => by
            simpa using pi_mem_univ (u := ψ' uN) (v := 0) hX
              (fun x _ => eqv_mem_univ x x)⟩,
        trivial,
        SetTheory.app (eqReflVal V ψ') A, a, 0, A, (fun x => eqv x x),
          hir1, hifva, eqReflVal_app_mem hA, ha,
          fun x _ => eqv_mem_univ x x⟩,
        SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (eqRecVal V ψ') A) a) M) r) a,
        SetTheory.app (SetTheory.app (eqReflVal V ψ') A) a,
        ψ' u1N,
        SetTheory.app (SetTheory.app (SetTheory.app (eqVal V ψ') A) a) a,
        (fun h => SetTheory.app (SetTheory.app M a) h),
        hip5, hir2, hm5, hreflv,
        fun h hh => eqFr_E6 hA ha ha hM h hh⟩

end Setlec
