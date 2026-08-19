import Setlec.Model.AnnotOkLemmas
import Setlec.Verify.Abstract
import Setlec.Verify.Leaves

/-!
# Transport lemmas for the local-context assumptions (`FvarsOk`)

With `FvarsOk` defined as a condition on the free-variable leaf closure,
transport under syntactic transformations reduces to leaf-subset
reasoning (`Setlec.Expr.fvarLeaves` lemmas); the context-transport
(weakening) happens once, per leaf.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat} {cval : ConstVal V}

open SetTheory Expr

/-- Leaf-subset monotonicity. -/
theorem FvarsOk.of_subset {e₁ e₂ : Expr} {d : Nat} {ρ : Nat → V}
    (hsub : ∀ l, l ∈ e₁.fvarLeaves → l ∈ e₂.fvarLeaves)
    (h : FvarsOk V cval env φ d ρ e₂) : FvarsOk V cval env φ d ρ e₁ :=
  fun l hl => h l (hsub l hl)

/-- Transport across leaf equivalence. -/
theorem FvarsOk.of_leafEquiv {e₁ e₂ : Expr} {d : Nat} {ρ : Nat → V}
    (hle : Expr.LeafEquiv e₁ e₂)
    (h : FvarsOk V cval env φ d ρ e₁) : FvarsOk V cval env φ d ρ e₂ :=
  fun l hl => h l (by rw [← fvarLeaves_of_leafEquiv e₁ e₂ hle]; exact hl)

/-- Closed expressions vacuously satisfy the assumptions. -/
theorem FvarsOk.of_not_hasFvar {e : Expr} (h : e.hasFvar = false)
    {d : Nat} {ρ : Nat → V} : FvarsOk V cval env φ d ρ e := by
  intro l hl
  rw [fvarLeaves_eq_nil_of_not_hasFvar h] at hl
  cases hl

/-- Structural decomposition (selected shapes used by the proofs). -/
theorem FvarsOk.of_forallE {n : Name} {ty body : Expr} {m : BinderMeta}
    {d : Nat} {ρ : Nat → V} (h : FvarsOk V cval env φ d ρ (.forallE n ty body m)) :
    FvarsOk V cval env φ d ρ ty ∧ FvarsOk V cval env φ d ρ body :=
  ⟨fun l hl => h l (by simp [fvarLeaves, hl]),
   fun l hl => h l (by simp [fvarLeaves, hl])⟩

theorem FvarsOk.of_lam {n : Name} {ty body : Expr} {m : BinderMeta}
    {d : Nat} {ρ : Nat → V} (h : FvarsOk V cval env φ d ρ (.lam n ty body m)) :
    FvarsOk V cval env φ d ρ ty ∧ FvarsOk V cval env φ d ρ body :=
  ⟨fun l hl => h l (by simp [fvarLeaves, hl]),
   fun l hl => h l (by simp [fvarLeaves, hl])⟩

theorem FvarsOk.of_app {f a : Expr}
    {d : Nat} {ρ : Nat → V} (h : FvarsOk V cval env φ d ρ (.app f a)) :
    FvarsOk V cval env φ d ρ f ∧ FvarsOk V cval env φ d ρ a :=
  ⟨fun l hl => h l (by simp [fvarLeaves, hl]),
   fun l hl => h l (by simp [fvarLeaves, hl])⟩

theorem FvarsOk.of_fvar {idx : Nat} {n : Name} {ty : Expr}
    {d : Nat} {ρ : Nat → V} (h : FvarsOk V cval env φ d ρ (.fvar idx n ty)) :
    (idx < d ∧ AnnotOk V cval env φ d ρ ty ∧
      ∃ T, interpExpr V cval env φ d ρ ty = some T ∧ ρ idx ∈ˢ T) ∧
    FvarsOk V cval env φ d ρ ty :=
  ⟨h (idx, n, ty) (by simp [fvarLeaves]),
   fun l hl => h l (by simp [fvarLeaves, hl])⟩

/-- Valuation extensionality (per leaf, via well-scopedness). -/
theorem FvarsOk.ext {e : Expr} {d : Nat} {ρ ρ' : Nat → V}
    (h : ∀ i, i < d → ρ i = ρ' i) (hw : WScoped d e)
    (hok : FvarsOk V cval env φ d ρ e) : FvarsOk V cval env φ d ρ' e := by
  intro l hl
  obtain ⟨hlt, hA, T, hT, hmem⟩ := hok l hl
  obtain ⟨hlb, hlw⟩ := WScoped_leaves e hw l hl
  have hbelow : fvarsBelow d l.2.2 := fvarsBelow_mono (by omega) hlw.fvarsBelow
  refine ⟨hlt, AnnotOk.ext l.2.2 h hbelow hA, T, ?_, ?_⟩
  · rw [← interp_ext l.2.2 h hbelow]
    exact hT
  · rw [← h l.1 hlt]
    exact hmem

/-- Weakening at the top (per leaf). -/
theorem FvarsOk.weaken_top {e : Expr} {d : Nat} {ρ : Nat → V} {x : V}
    (hw : WScoped d e) (hok : FvarsOk V cval env φ d ρ e) :
    FvarsOk V cval env φ (d + 1) (updV V ρ d x) e := by
  intro l hl
  obtain ⟨hlt, hA, T, hT, hmem⟩ := hok l hl
  obtain ⟨hlb, hlw⟩ := WScoped_leaves e hw l hl
  have hlw' : WScoped d l.2.2 := hlw.mono (by omega)
  refine ⟨by omega, AnnotOk.weaken_top hlw' hA, T, ?_, ?_⟩
  · rw [interp_weaken_top hlw']
    exact hT
  · simp only [updV]
    have : l.1 ≠ d := by omega
    simp [this, hmem]

/-- Opening a binder: the fresh variable's condition is supplied by the
membership `x ∈ ⟦ty⟧`; old leaves weaken. -/
theorem FvarsOk.instantiate1 {d : Nat} {n : Name} {ty : Expr}
    {ρ : Nat → V} {x A : V}
    (hwty : WScoped d ty) (hty : FvarsOk V cval env φ d ρ ty)
    (haty : AnnotOk V cval env φ d ρ ty)
    (hA : interpExpr V cval env φ d ρ ty = some A) (hx : x ∈ˢ A)
    (body : Expr) (k : Nat) (hwbody : WScoped d body)
    (hbody : FvarsOk V cval env φ d ρ body) :
    FvarsOk V cval env φ (d + 1) (updV V ρ d x) (body.instantiate1 (.fvar d n ty) k) := by
  intro l hl
  rcases fvarLeaves_instantiate1 body k hl with hl' | hl'
  · exact FvarsOk.weaken_top hwbody hbody l hl'
  · simp only [fvarLeaves, List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · refine ⟨by omega, AnnotOk.weaken_top hwty haty, A, ?_, ?_⟩
      · rw [interp_weaken_top hwty]
        exact hA
      · simp [updV, hx]
    · exact FvarsOk.weaken_top hwty hty l hl'

end Setlec
