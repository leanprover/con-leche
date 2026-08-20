import Setlec.Model.Core.StructEta

/-!
# Checker-core soundness: Irrel

Part of the mutual soundness claims layer (split from
`Setlec/Model/TypeChecker.lean`; see that module's docstring).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

section Claims

variable {m : EnvModel V env} {fuel : Nat}
variable (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
  (ihi : InferClaims m φ fuel)

/-- Soundness of the stuck-term fallback: pair eta in either direction,
else proof irrelevance. -/
theorem stuckIrrel_sound {m : EnvModel V env} {fuel : Nat}
    (ihAll : ∀ f, f ≤ fuel →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f)
    {d : Nat} {a b : Expr} {ρ : Nat → V} {va vb : V}
    (h : stuckIrrel env fuel d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  cases fuel with
  | zero => exact nomatch h
  | succ f =>
  simp only [stuckIrrel, Bind.bind, Except.bind] at h
  cases hp1 : pairEtaCert env f d a b with
  | error e => rw [hp1] at h; exact nomatch h
  | ok r₁ =>
  rw [hp1] at h
  dsimp only at h
  cases r₁ with
  | true =>
    cases f with
    | zero => exact nomatch hp1
    | succ f' =>
    obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll f' (by omega)
    exact pairEta_sound ihwL ihdL ihiL hp1 hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hp2 : pairEtaCert env f d b a with
  | error e => rw [hp2] at h; exact nomatch h
  | ok r₂ =>
  rw [hp2] at h
  dsimp only at h
  cases r₂ with
  | true =>
    cases f with
    | zero => exact nomatch hp2
    | succ f' =>
    obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll f' (by omega)
    exact (pairEta_sound ihwL ihdL ihiL hp2 hwb hwa hbb hba hLbb hLba
      hokb hoka hab haa hvb hva).symm
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hs1 : structEtaCert env f d a b with
  | error e => rw [hs1] at h; exact nomatch h
  | ok r₃ =>
  rw [hs1] at h
  dsimp only at h
  cases r₃ with
  | true =>
    cases f with
    | zero => exact nomatch hs1
    | succ f' =>
    exact structEta_sound (fuelTop := f') (fun ff hff => ihAll ff
        (by omega))
      (Nat.le_refl _) hs1 hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hs2 : structEtaCert env f d b a with
  | error e => rw [hs2] at h; exact nomatch h
  | ok r₄ =>
  rw [hs2] at h
  dsimp only at h
  cases r₄ with
  | true =>
    cases f with
    | zero => exact nomatch hs2
    | succ f' =>
    exact (structEta_sound (fuelTop := f') (fun ff hff => ihAll ff
        (by omega))
      (Nat.le_refl _) hs2 hwb hwa hbb hba hLbb hLba
      hokb hoka hab haa hvb hva).symm
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hu1 : structUnitCert env f d a b with
  | error e => rw [hu1] at h; exact nomatch h
  | ok r₅ =>
  rw [hu1] at h
  dsimp only at h
  cases r₅ with
  | true =>
    cases f with
    | zero => exact nomatch hu1
    | succ f' =>
    exact structUnit_sound (fuelTop := f') (fun ff hff => ihAll ff
        (by omega))
      (Nat.le_refl _) hu1 hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases f with
  | zero => exact nomatch h
  | succ f' =>
  obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll f' (by omega)
  obtain ⟨hpa, hpb⟩ := proofIrrel_pt ihwL ihiL h hwa hwb hba hbb
    hLba hLbb hoka hokb haa hab
  rw [hva] at hpa
  rw [hvb] at hpb
  exact (Option.some.inj hpa).trans (Option.some.inj hpb).symm

end Claims

end Setlec
