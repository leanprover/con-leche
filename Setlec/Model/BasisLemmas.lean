import Setlec.Model.Interp

/-!
# Computation lemmas for the pinned basis values

Constant-headed application spines interpret as `SetTheory.app` folds of
the pinned values; these lemmas compute the folds by `app_lam` (the
values' `lam` tags were chosen so that the fibre-universe side
conditions come out exactly right) and extract the argument memberships
that make them applicable from `pi`-memberships via the tagged proof
point (`lam_pi_dom`).
-/

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory

private theorem max_absorb_r (u v : Nat) : Nat.max v (Nat.max u v) = Nat.max u v :=
  Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_max_right u v, Nat.le_refl _⟩)
    (Nat.le_max_right _ _)

private theorem max_absorb_l (u v : Nat) : Nat.max u (Nat.max u v) = Nat.max u v :=
  Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_max_left u v, Nat.le_refl _⟩)
    (Nat.le_max_right _ _)

private theorem max_absorb_big (u v : Nat) :
    Nat.max (Nat.max u (v + 1)) (Nat.max u v) = Nat.max u (v + 1) := by
  refine Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.max_le.mpr ⟨?_, ?_⟩⟩)
    (Nat.le_max_left _ _)
  · exact Nat.le_max_left _ _
  · exact Nat.le_trans (Nat.le_succ v) (Nat.le_max_right _ _)

private theorem max_absorb_big' (u v : Nat) :
    Nat.max u (Nat.max (v + 1) (Nat.max u v)) = Nat.max u (v + 1) := by
  refine Nat.le_antisymm
    (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.max_le.mpr
      ⟨Nat.le_max_right _ _, Nat.max_le.mpr
        ⟨Nat.le_max_left _ _,
         Nat.le_trans (Nat.le_succ v) (Nat.le_max_right _ _)⟩⟩⟩)
    (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)⟩)

/-- A non-collapsed abstraction's `pi`-membership pins its domain
(task #100: the non-`pt` premise replaces the old nonzero-tag premise —
under the collapse, tags no longer bound values away from `pt`;
non-collapse is certified per value, e.g. by `sigmaSet_ne_pt` /
`lamC_ne_pt_of_witness` witnesses). -/
theorem lam_pi_dom {t vE : Nat} {D A : V} {F B : V → V} {a : V}
    (hmem : SetTheory.lam t D F ∈ˢ pi vE A B)
    (hne : SetTheory.lam t D F ≠ pt) (ha : a ∈ˢ A) :
    a ∈ˢ D :=
  lamC_dom_of_ne hne hmem a ha

/-- The pair-former value never collapses: its innermost values are
pair sets. -/
theorem psigmaVal_ne_pt {ψ : Name → Nat} : psigmaVal V ψ ≠ pt := by
  refine lamC_ne_pt_of_witness (empty_mem_univ (ψ uN)) ?_
  refine lamC_ne_pt_of_witness (x := pt) ?_ sigmaSet_ne_pt
  have h : (pt : V) ∈ˢ piC empty (fun _ => univ (ψ vN)) := by
    rw [piC_empty]
    exact pt_mem_unitSet
  exact h

/-- Nor does its partial application body, at any domain value. -/
theorem psigmaVal_inner_ne_pt {ψ : Name → Nat} {vA : V} {t : Nat} :
    SetTheory.lam t (pi (ψ vN + 1) vA fun _ => univ (ψ vN))
      (fun B => sigmaSet (Nat.max (ψ uN) (ψ vN)) vA fun x => app B x) ≠ pt :=
  lamC_ne_pt_of_witness
    (lamC_mem fun _x _hx => empty_mem_univ (ψ vN)) sigmaSet_ne_pt

theorem pinnedVal_psigma (ψ : Name → Nat) :
    pinnedVal V psigmaName ψ = psigmaVal V ψ := rfl

theorem pinnedVal_psigmaMk (ψ : Name → Nat) :
    pinnedVal V psigmaMkName ψ = psigmaMkVal V ψ := rfl

/-- Fold the pair-former value over a domain and a fibre family. -/
theorem psigmaVal_fold {ψ : Name → Nat} {vA vB : V}
    (hA : vA ∈ˢ univ (ψ uN))
    (hB : vB ∈ˢ pi (ψ vN + 1) vA fun _ => univ (ψ vN)) :
    app (app (psigmaVal V ψ) vA) vB =
      sigmaSet (Nat.max (ψ uN) (ψ vN)) vA fun x => app vB x := by
  have hgen : ∀ u v : Nat, vA ∈ˢ univ u →
      vB ∈ˢ pi (v + 1) vA (fun _ => univ v) →
      app (app (SetTheory.lam (Nat.max (Nat.max u (v + 1)) (Nat.max u v + 1)) (univ u) fun A =>
        SetTheory.lam (Nat.max u v + 1) (pi (v + 1) A fun _ => univ v) fun B =>
          sigmaSet (Nat.max u v) A fun x => app B x) vA) vB =
        sigmaSet (Nat.max u v) vA (fun x => app vB x) := ?_
  · exact hgen (ψ uN) (ψ vN) hA hB
  intro u v hA hB
  have h1 : app (SetTheory.lam (Nat.max (Nat.max u (v + 1)) (Nat.max u v + 1)) (univ u) fun A =>
      SetTheory.lam (Nat.max u v + 1) (pi (v + 1) A fun _ => univ v) fun B =>
        sigmaSet (Nat.max u v) A fun x => app B x) vA =
      SetTheory.lam (Nat.max u v + 1) (pi (v + 1) vA fun _ => univ v) fun B =>
        sigmaSet (Nat.max u v) vA fun x => app B x := by
    exact app_lam hA
      (B := fun A => pi (Nat.max u v + 1) (pi (v + 1) A fun _ => univ v) fun _ =>
        univ (Nat.max u v))
      (fun A hA' => lam_mem fun B hB' =>
        sigma_mem_univ hA' (fun x hx => app_mem hB' hx fun _ _ => univ_mem_univ v))
      (fun A hA' => by
        have hdom : pi (v + 1) A (fun _ => univ v) ∈ˢ univ (Nat.max u (v + 1)) := by
          have := pi_mem_univ (v := v + 1) hA' (fun x _ => univ_mem_univ v)
          simpa using this
        have := pi_mem_univ (v := Nat.max u v + 1) hdom
          (fun _ _ => univ_mem_univ (Nat.max u v))
        simpa [Nat.max_comm, Nat.max_assoc, Nat.max_left_comm] using this)
  rw [h1]
  exact app_lam hB
    (B := fun _ => univ (Nat.max u v))
    (fun B hB' => sigma_mem_univ hA fun x hx => app_mem hB' hx fun _ _ => univ_mem_univ v)
    (fun _ _ => univ_mem_univ (Nat.max u v))

/-- Fold the pair-constructor value over its four arguments. -/
theorem psigmaMkVal_fold {ψ : Name → Nat} {vA vB va vb : V}
    (hA : vA ∈ˢ univ (ψ uN))
    (hB : vB ∈ˢ pi (ψ vN + 1) vA fun _ => univ (ψ vN))
    (ha : va ∈ˢ vA) (hb : vb ∈ˢ app vB va) :
    app (app (app (app (psigmaMkVal V ψ) vA) vB) va) vb =
      (if Nat.max (ψ uN) (ψ vN) = 0 then pt else spair va vb) := by
  have hgen : ∀ u v : Nat, vA ∈ˢ univ u →
      vB ∈ˢ pi (v + 1) vA (fun _ => univ v) → va ∈ˢ vA → vb ∈ˢ app vB va →
      app (app (app (app
        (SetTheory.lam (if Nat.max u v = 0 then 0 else Nat.max u (v + 1)) (univ u) fun A =>
          SetTheory.lam (Nat.max u v) (pi (v + 1) A fun _ => univ v) fun B =>
            SetTheory.lam (Nat.max u v) A fun a =>
              SetTheory.lam (Nat.max u v) (app B a) fun b =>
                if Nat.max u v = 0 then pt else spair a b) vA) vB) va) vb =
        (if Nat.max u v = 0 then pt else spair va vb) := ?_
  · exact hgen (ψ uN) (ψ vN) hA hB ha hb
  intro u v hA hB ha hb
  -- the inner fibre nests are typed by lam_mem / pi_mem_univ; each fold
  -- step is app_lam with those facts
  have hC4 : ∀ A : V, A ∈ˢ univ u → ∀ B, B ∈ˢ pi (v + 1) A (fun _ => univ v) →
      ∀ a, a ∈ˢ A →
      sigmaSet (Nat.max u v) A (fun x => app B x) ∈ˢ univ (Nat.max u v) :=
    fun A hA' B hB' a _ => sigma_mem_univ hA' fun x hx =>
      app_mem hB' hx fun _ _ => univ_mem_univ v
  have hF4 : ∀ A : V, A ∈ˢ univ u → ∀ B, B ∈ˢ pi (v + 1) A (fun _ => univ v) →
      ∀ a, a ∈ˢ A →
      SetTheory.lam (Nat.max u v) (app B a)
          (fun b => if Nat.max u v = 0 then pt else spair a b) ∈ˢ
        pi (Nat.max u v) (app B a) (fun _ => sigmaSet (Nat.max u v) A (fun x => app B x)) :=
    fun A hA' B hB' a ha' => lam_mem fun b hb' => by
      by_cases hw : Nat.max u v = 0
      · simp only [hw, ↓reduceIte]
        exact pt_mem_sigma ha' hb'
      · simp only [if_neg hw]
        exact spair_mem hw ha' hb'
  have h1 : app (SetTheory.lam (if Nat.max u v = 0 then 0 else Nat.max u (v + 1))
        (univ u) fun A =>
        SetTheory.lam (Nat.max u v) (pi (v + 1) A fun _ => univ v) fun B =>
          SetTheory.lam (Nat.max u v) A fun a =>
            SetTheory.lam (Nat.max u v) (app B a) fun b =>
              if Nat.max u v = 0 then pt else spair a b) vA =
      SetTheory.lam (Nat.max u v) (pi (v + 1) vA fun _ => univ v) fun B =>
        SetTheory.lam (Nat.max u v) vA fun a =>
          SetTheory.lam (Nat.max u v) (app B a) fun b =>
            if Nat.max u v = 0 then pt else spair a b := by
    refine app_lam hA
      (B := fun A => pi (Nat.max u v) (pi (v + 1) A fun _ => univ v) fun B =>
        pi (Nat.max u v) A fun a =>
          pi (Nat.max u v) (app B a) fun _ =>
            sigmaSet (Nat.max u v) A fun x => app B x)
      (fun A hA' => lam_mem fun B hB' => lam_mem fun a ha' =>
        hF4 A hA' B hB' a ha')
      (fun A hA' => ?_)
    -- the fibre pi-chain lands in the right universe
    have hdom : pi (v + 1) A (fun _ => univ v) ∈ˢ univ (Nat.max u (v + 1)) := by
      have := pi_mem_univ (v := v + 1) hA' (fun x _ => univ_mem_univ v)
      simpa using this
    have hinner : ∀ B, B ∈ˢ pi (v + 1) A (fun _ => univ v) →
        (pi (Nat.max u v) A fun a => pi (Nat.max u v) (app B a) fun _ =>
          sigmaSet (Nat.max u v) A fun x => app B x) ∈ˢ univ (Nat.max u v) := by
      intro B hB'
      have hfib : ∀ a, a ∈ˢ A →
          (pi (Nat.max u v) (app B a) fun _ =>
            sigmaSet (Nat.max u v) A fun x => app B x) ∈ˢ univ (Nat.max u v) := by
        intro a ha'
        have hBa : app B a ∈ˢ univ v := app_mem hB' ha' fun _ _ => univ_mem_univ v
        have := pi_mem_univ (v := Nat.max u v) hBa
          (fun _ _ => hC4 A hA' B hB' a ha')
        by_cases hw : Nat.max u v = 0
        · simpa [hw] using this
        · simpa [hw, max_absorb_r] using this
      have := pi_mem_univ (v := Nat.max u v) hA' hfib
      by_cases hw : Nat.max u v = 0
      · simpa [hw] using this
      · simpa [hw, max_absorb_l] using this
    have := pi_mem_univ (v := Nat.max u v) hdom hinner
    by_cases hw : Nat.max u v = 0
    · simpa [hw] using this
    · simpa [hw, max_absorb_big, max_absorb_big'] using this
  rw [h1]
  have h2 : app (SetTheory.lam (Nat.max u v) (pi (v + 1) vA fun _ => univ v) fun B =>
      SetTheory.lam (Nat.max u v) vA fun a =>
        SetTheory.lam (Nat.max u v) (app B a) fun b =>
          if Nat.max u v = 0 then pt else spair a b) vB =
      SetTheory.lam (Nat.max u v) vA fun a =>
        SetTheory.lam (Nat.max u v) (app vB a) fun b =>
          if Nat.max u v = 0 then pt else spair a b := by
    refine app_lam hB
      (B := fun B => pi (Nat.max u v) vA fun a =>
        pi (Nat.max u v) (app B a) fun _ =>
          sigmaSet (Nat.max u v) vA fun x => app B x)
      (fun B hB' => lam_mem fun a ha' => hF4 vA hA B hB' a ha')
      (fun B hB' => ?_)
    have hfib : ∀ a, a ∈ˢ vA →
        (pi (Nat.max u v) (app B a) fun _ =>
          sigmaSet (Nat.max u v) vA fun x => app B x) ∈ˢ univ (Nat.max u v) := by
      intro a ha'
      have hBa : app B a ∈ˢ univ v := app_mem hB' ha' fun _ _ => univ_mem_univ v
      have := pi_mem_univ (v := Nat.max u v) hBa
        (fun _ _ => hC4 vA hA B hB' a ha')
      by_cases hw : Nat.max u v = 0
      · simpa [hw] using this
      · simpa [hw, max_absorb_r] using this
    have := pi_mem_univ (v := Nat.max u v) hA hfib
    by_cases hw : Nat.max u v = 0
    · simpa [hw] using this
    · simpa [hw, max_absorb_l] using this
  rw [h2]
  have h3 : app (SetTheory.lam (Nat.max u v) vA fun a =>
      SetTheory.lam (Nat.max u v) (app vB a) fun b =>
        if Nat.max u v = 0 then pt else spair a b) va =
      SetTheory.lam (Nat.max u v) (app vB va) fun b =>
        if Nat.max u v = 0 then pt else spair va b := by
    refine app_lam ha
      (B := fun a => pi (Nat.max u v) (app vB a) fun _ =>
        sigmaSet (Nat.max u v) vA fun x => app vB x)
      (fun a ha' => hF4 vA hA vB hB a ha')
      (fun a ha' => ?_)
    have hBa : app vB a ∈ˢ univ v := app_mem hB ha' fun _ _ => univ_mem_univ v
    have := pi_mem_univ (v := Nat.max u v) hBa
      (fun _ _ => hC4 vA hA vB hB a ha')
    by_cases hw : Nat.max u v = 0
    · simpa [hw] using this
    · simpa [hw, max_absorb_r] using this
  rw [h3]
  exact app_lam hb
    (B := fun _ => sigmaSet (Nat.max u v) vA fun x => app vB x)
    (fun b hb' => by
      by_cases hw : Nat.max u v = 0
      · simp only [hw, ↓reduceIte]
        exact pt_mem_sigma ha hb'
      · simp only [if_neg hw]
        exact spair_mem hw ha hb')
    (fun _ _ => hC4 vA hA vB hB va ha)

end Setlec
