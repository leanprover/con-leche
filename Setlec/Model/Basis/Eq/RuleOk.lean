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
      simp only [eqRecVal, h0, reduceIte]
      rw [lam_zero, app_pt, app_pt, app_pt, app_pt, app_pt, app_pt]
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
      (fun r _ => lam_mem (V := V) fun b _ =>
        lam_mem (V := V) fun h _ => rfl ▸ ‹r ∈ˢ _›)
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
    (fun b hb => eqFr_E5 hA ha hb hM)

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
    · rw [if_neg h', if_neg h', Nat.max_assoc]
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
    (fun a ha => eqFr_E2 hA ha)

end Setlec
