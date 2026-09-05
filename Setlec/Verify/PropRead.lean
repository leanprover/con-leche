import Setlec.Kernel.PropRead
import Setlec.Verify.Shift

/-!
# The head-symbol prop-ness readers under the verification walks
(task #168)

The readers (`Setlec/Kernel/PropRead.lean`) look only at head symbols,
arities and binder data, none of which a free-variable shift touches —
so every reader commutes with `shiftFrom`, which is all the
deep-embedding lemma family (`Setlec/Verify/Deep.lean`) needs of them.
-/

namespace Setlec

open Expr

theorem Expr.numArgs_shiftFrom {p : Nat} :
    ∀ (e : Expr), (shiftFrom p e).numArgs = e.numArgs := by
  intro e
  induction e <;> simp_all [shiftFrom, numArgs]
  case fvar => split <;> rfl

theorem residualPW_peelPis_shiftFrom {p : Nat} :
    ∀ (k : Nat) (e : Expr),
      residualPW ((shiftFrom p e).peelPis k) = residualPW (e.peelPis k) := by
  intro k
  induction k with
  | zero =>
    intro e
    cases e <;> try rfl
    case fvar => simp only [shiftFrom]; split <;> rfl
  | succ k ih =>
    intro e
    cases e <;> try rfl
    case fvar => simp only [shiftFrom]; split <;> rfl
    case forallE n ty b m => exact ih b

theorem headTypePW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (h : Expr) (n : Nat) :
    headTypePW find? (shiftFrom p h) n = headTypePW find? h n := by
  cases h <;> try rfl
  case fvar =>
    simp only [shiftFrom]
    split <;> simp only [headTypePW, residualPW_peelPis_shiftFrom]

theorem typeSortPW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (T : Expr) :
    typeSortPW find? (shiftFrom p T) = typeSortPW find? T := by
  cases T <;> try rfl
  case fvar =>
    simp only [shiftFrom]
    split <;> simp only [typeSortPW, getAppFn, numArgs, headTypePW,
      residualPW_peelPis_shiftFrom]
  case app f x =>
    have h1 := getAppFn_shiftFrom (p := p) (.app f x)
    have h2 := numArgs_shiftFrom (p := p) (.app f x)
    simp only [shiftFrom] at h1 h2 ⊢
    simp only [typeSortPW, h1, h2, headTypePW_shiftFrom]

theorem headProofPW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (h : Expr) :
    headProofPW find? (shiftFrom p h) = headProofPW find? h := by
  cases h <;> try rfl
  case fvar =>
    simp only [shiftFrom]
    split <;> simp only [headProofPW, typeSortPW_shiftFrom]

/-- `proofPW` through the total `lamPw` reader (the shape the walks
rewrite). -/
theorem proofPW_eq (find? : Name → Option ConstantInfo) (a : Expr) :
    proofPW find? a =
      match a.lamPw with
      | some pw => some pw
      | none => headProofPW find? a.getAppFn := by
  cases a <;> rfl

theorem proofPW_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (a : Expr) :
    proofPW find? (shiftFrom p a) = proofPW find? a := by
  rw [proofPW_eq, proofPW_eq, lamPw_shiftFrom, getAppFn_shiftFrom,
    headProofPW_shiftFrom]

theorem notProofFast_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (a : Expr) :
    notProofFast find? (shiftFrom p a) = notProofFast find? a := by
  simp only [notProofFast, proofPW_shiftFrom]

theorem isProofFast_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (a : Expr) :
    isProofFast find? (shiftFrom p a) = isProofFast find? a := by
  simp only [isProofFast, proofPW_shiftFrom]

end Setlec
