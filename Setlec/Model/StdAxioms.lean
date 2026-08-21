import Setlec.Kernel.StdAxioms
import Setlec.Model.Basis.Util
import Setlec.Model.Basis.Eq.Install

/-!
# Standard axioms: models for `propext` and `Classical.choice`

The checker accepts exactly the two standard axioms, with their types
pinned up to the exporter's unstable hygienic binder names
(`ConstantVal.matchesPin`).  This module provides

* the bridge from `Expr.eraseNames`-equality to `Expr.ErasedEq`, so
  the interpretation of a stored type can be transported to the pinned
  type (the interpretation never reads what `eraseNames` erases);
* set-theoretic values for the two axioms together with the `hkey`
  membership facts `extend_basis_one` needs.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open SetTheory Expr

/-- Name erasure only changes what `ErasedEq` ignores. -/
theorem Expr.ErasedEq.of_eraseNames :
    ∀ {a b : Expr}, a.eraseNames = b.eraseNames → ErasedEq a b
  | .bvar _, b, h => by
    match b, h with
    | .bvar _, h =>
      simp only [eraseNames, Expr.bvar.injEq] at h
      exact h
  | .fvar _ _ tya, b, h => by
    match b, h with
    | .fvar _ _ tyb, h =>
      simp only [eraseNames, Expr.fvar.injEq] at h
      exact h.1
  | .sort _, b, h => by
    match b, h with
    | .sort _, h =>
      simp only [eraseNames, Expr.sort.injEq] at h
      exact h
  | .const _ _, b, h => by
    match b, h with
    | .const _ _, h =>
      simp only [eraseNames, Expr.const.injEq] at h
      exact h
  | .app fa aa, b, h => by
    match b, h with
    | .app fb ab, h =>
      simp only [eraseNames, Expr.app.injEq] at h
      exact ⟨of_eraseNames h.1, of_eraseNames h.2⟩
  | .lam _ tya ba ma, b, h => by
    match b, h with
    | .lam _ tyb bb mb, h =>
      simp only [eraseNames, Expr.lam.injEq] at h
      exact ⟨h.2.2.2, of_eraseNames h.2.1, of_eraseNames h.2.2.1⟩
  | .forallE _ tya ba ma, b, h => by
    match b, h with
    | .forallE _ tyb bb mb, h =>
      simp only [eraseNames, Expr.forallE.injEq] at h
      exact ⟨h.2.2.2, of_eraseNames h.2.1, of_eraseNames h.2.2.1⟩
  | .letE _ tya va ba, b, h => by
    match b, h with
    | .letE _ tyb vb bb, h =>
      simp only [eraseNames, Expr.letE.injEq] at h
      exact ⟨of_eraseNames h.2.1, of_eraseNames h.2.2.1,
        of_eraseNames h.2.2.2⟩
  | .lit _, b, h => by
    match b, h with
    | .lit _, h =>
      simp only [eraseNames, Expr.lit.injEq] at h
      exact h
  | .proj _ _ ea, b, h => by
    match b, h with
    | .proj _ _ eb, h =>
      simp only [eraseNames, Expr.proj.injEq] at h
      exact ⟨h.1, h.2.1, of_eraseNames h.2.2⟩

variable {V : Type u} [SetTheory V]

/-- A `matchesPin` hit lets the closed interpretation be computed on
the pinned type instead of the stored one. -/
theorem interpClosed_matchesPin {cval : ConstVal V} {env : Env}
    {ψ : Name → Nat} {cv pin : ConstantVal}
    (h : ConstantVal.matchesPin cv pin = true) :
    interpClosed V cval env ψ cv.type = interpClosed V cval env ψ pin.type := by
  simp only [ConstantVal.matchesPin, Bool.and_eq_true, beq_iff_eq] at h
  exact interp_erasedEq (Expr.ErasedEq.of_eraseNames h.2) 0 (rho0 V)

end Setlec
