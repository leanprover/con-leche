import Setlec.Kernel.ExprOps
import Setlec.Verify.Shift
import Setlec.Verify.Abstract

/-!
# The free-variable leaf closure

`fvarLeaves e` lists every reachable `fvar` leaf of `e` together with,
hereditarily, the leaves of their type annotations.  The local-context
assumptions (`FvarsOk`) are conditions on exactly this list, so every
syntactic transformation only needs a subset lemma here.
-/

set_option linter.unusedSimpArgs false

namespace Setlec.Expr

/-- All reachable `fvar` leaves, including (hereditarily) those inside
their type annotations. -/
def fvarLeaves : Expr → List (Nat × Name × Expr)
  | .fvar idx n ty => (idx, n, ty) :: fvarLeaves ty
  | .app f a => fvarLeaves f ++ fvarLeaves a
  | .lam _ ty b _ | .forallE _ ty b _ => fvarLeaves ty ++ fvarLeaves b
  | .letE _ t v b => fvarLeaves t ++ fvarLeaves v ++ fvarLeaves b
  | .proj _ _ e => fvarLeaves e
  | _ => []
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- Closed terms have no leaves. -/
theorem fvarLeaves_eq_nil_of_not_hasFvar :
    ∀ {e : Expr}, e.hasFvar = false → e.fvarLeaves = [] := by
  intro e
  induction e <;> simp_all [hasFvar, fvarLeaves]

/-- Instantiation only introduces the substituted term's leaves. -/
theorem fvarLeaves_instantiate1 {a : Expr} :
    ∀ (e : Expr) (k : Nat) {l}, l ∈ (e.instantiate1 a k).fvarLeaves →
      l ∈ e.fvarLeaves ∨ l ∈ a.fvarLeaves := by
  intro e
  induction e with
  | bvar i =>
    intro k l hl
    simp only [instantiate1] at hl
    split at hl
    · exact Or.inr hl
    · split at hl <;> simp [fvarLeaves] at hl
  | fvar idx n ty _ =>
    intro k l hl
    simp only [instantiate1] at hl
    exact Or.inl hl
  | app f b ihf ihb =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihf k hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihb k hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | lam n ty body m ihty ihbody =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihty k hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihbody (k + 1) hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | forallE n ty body m ihty ihbody =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · rcases ihty k hl with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases ihbody (k + 1) hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | letE n ty v body ihty ihv ihbody =>
    intro k l hl
    simp only [instantiate1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · rcases ihty k hl with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    · rcases ihv k hl with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
    · rcases ihbody (k + 1) hl with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | proj s i e ih =>
    intro k l hl
    simp only [instantiate1, fvarLeaves] at hl ⊢
    exact ih k hl
  | sort u => intro k l hl; simp [instantiate1, fvarLeaves] at hl
  | const n us => intro k l hl; simp [instantiate1, fvarLeaves] at hl
  | lit ll => intro k l hl; simp [instantiate1, fvarLeaves] at hl

/-- Abstraction only removes leaves. -/
theorem fvarLeaves_abstract1 {D : Nat} :
    ∀ (e : Expr) (k : Nat) {l}, l ∈ (e.abstract1 D k).fvarLeaves →
      l ∈ e.fvarLeaves := by
  intro e
  induction e with
  | bvar i => intro k l hl; simp [abstract1, fvarLeaves] at hl
  | fvar idx n ty _ =>
    intro k l hl
    simp only [abstract1] at hl
    split at hl
    · simp [fvarLeaves] at hl
    · exact hl
  | app f b ihf ihb =>
    intro k l hl
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihf k hl)
    · exact Or.inr (ihb k hl)
  | lam n ty body m ihty ihbody =>
    intro k l hl
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihty k hl)
    · exact Or.inr (ihbody (k + 1) hl)
  | forallE n ty body m ihty ihbody =>
    intro k l hl
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihty k hl)
    · exact Or.inr (ihbody (k + 1) hl)
  | letE n ty v body ihty ihv ihbody =>
    intro k l hl
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · exact Or.inl (Or.inl (ihty k hl))
    · exact Or.inl (Or.inr (ihv k hl))
    · exact Or.inr (ihbody (k + 1) hl)
  | proj s i e ih =>
    intro k l hl
    simp only [abstract1, fvarLeaves] at hl ⊢
    exact ih k hl
  | sort u => intro k l hl; simp [abstract1, fvarLeaves] at hl
  | const n us => intro k l hl; simp [abstract1, fvarLeaves] at hl
  | lit ll => intro k l hl; simp [abstract1, fvarLeaves] at hl

/-- Leaf-equivalent terms have the same leaves. -/
theorem fvarLeaves_of_leafEquiv : ∀ (e₁ e₂ : Expr), Expr.LeafEquiv e₁ e₂ →
    e₂.fvarLeaves = e₁.fvarLeaves := by
  intro e₁
  induction e₁ with
  | fvar idx n ty _ =>
    intro e₂ hle
    cases e₂ with
    | fvar idx' n' ty' =>
      simp only [Expr.LeafEquiv] at hle
      obtain ⟨rfl, rfl, rfl⟩ := hle
      rfl
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | app f a ihf iha =>
    intro e₂ hle
    cases e₂ with
    | app f' a' =>
      simp only [Expr.LeafEquiv] at hle
      simp only [fvarLeaves, ihf f' hle.1, iha a' hle.2]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | lam n ty body m ihty ihbody =>
    intro e₂ hle
    cases e₂ with
    | lam n' ty' body' m' =>
      simp only [Expr.LeafEquiv] at hle
      simp only [fvarLeaves, ihty ty' hle.1, ihbody body' hle.2]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | forallE n ty body m ihty ihbody =>
    intro e₂ hle
    cases e₂ with
    | forallE n' ty' body' m' =>
      simp only [Expr.LeafEquiv] at hle
      simp only [fvarLeaves, ihty ty' hle.1, ihbody body' hle.2]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | letE n ty val body ihty ihval ihbody =>
    intro e₂ hle
    cases e₂ with
    | letE n' ty' val' body' =>
      simp only [Expr.LeafEquiv] at hle
      simp only [fvarLeaves, ihty ty' hle.1, ihval val' hle.2.1, ihbody body' hle.2.2]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | proj s i e ih =>
    intro e₂ hle
    cases e₂ with
    | proj s' i' e' =>
      simp only [Expr.LeafEquiv] at hle
      simp only [fvarLeaves, ih e' hle]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | bvar i =>
    intro e₂ hle
    cases e₂ with
    | bvar j => simp [fvarLeaves]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | sort u =>
    intro e₂ hle
    cases e₂ with
    | sort u' => simp [fvarLeaves]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | const n us =>
    intro e₂ hle
    cases e₂ with
    | const n' us' => simp [fvarLeaves]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | lit l =>
    intro e₂ hle
    cases e₂ with
    | lit l' => simp [fvarLeaves]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])

/-- Well-scopedness gives bounds and scoping for every closure leaf. -/
theorem WScoped_leaves : ∀ (e : Expr) {d : Nat}, WScoped d e →
    ∀ l ∈ e.fvarLeaves, l.1 < d ∧ WScoped l.1 l.2.2 := by
  intro e
  induction e with
  | fvar idx n ty ih =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact ⟨hw.1, hw.2⟩
    · obtain ⟨h1, h2⟩ := ih hw.2 l hl
      exact ⟨by omega, h2⟩
  | app f a ihf iha =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihf hw.1 l hl
    · exact iha hw.2 l hl
  | lam n ty body m ihty ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hw.1 l hl
    · exact ihbody hw.2 l hl
  | forallE n ty body m ihty ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hw.1 l hl
    · exact ihbody hw.2 l hl
  | letE n ty val body ihty ihval ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact ihty hw.1 l hl
    · exact ihval hw.2.1 l hl
    · exact ihbody hw.2.2 l hl
  | proj s i e ih =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves] at hl
    exact ih hw l hl
  | bvar i => intro d _ l hl; simp [fvarLeaves] at hl
  | sort u => intro d _ l hl; simp [fvarLeaves] at hl
  | const n us => intro d _ l hl; simp [fvarLeaves] at hl
  | lit ll => intro d _ l hl; simp [fvarLeaves] at hl

end Setlec.Expr
