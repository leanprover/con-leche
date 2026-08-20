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
struct eta in either direction, unit-likeness, else proof
irrelevance. -/
theorem stuckIrrel_sound {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    {d : Nat} {a b : Expr} {ρ : Nat → V} {va vb : V}
    (h : stuckIrrelP env fuel d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) :
    va = vb := by
  dsimp only [stuckIrrelP] at h
  simp only [stuckIrrel, Bind.bind, Except.bind] at h
  simp only [pairEtaCert_fold, structEtaCert_fold, structUnitCert_fold,
    proofIrrel_fold] at h
  cases hp1 : pairEtaCertP env fuel d a b with
  | error e => rw [hp1] at h; exact nomatch h
  | ok r₁ =>
  rw [hp1] at h
  dsimp only at h
  cases r₁ with
  | true =>
    exact pairEta_sound ihw ihd ihi hp1 hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hp2 : pairEtaCertP env fuel d b a with
  | error e => rw [hp2] at h; exact nomatch h
  | ok r₂ =>
  rw [hp2] at h
  dsimp only at h
  cases r₂ with
  | true =>
    exact (pairEta_sound ihw ihd ihi hp2 hwb hwa hbb hba hLbb hLba
      hokb hoka hab haa hvb hva).symm
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hs1 : structEtaCertP env fuel d a b with
  | error e => rw [hs1] at h; exact nomatch h
  | ok r₃ =>
  rw [hs1] at h
  dsimp only at h
  cases r₃ with
  | true =>
    exact structEta_sound ihw ihd ihi hs1 hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hs2 : structEtaCertP env fuel d b a with
  | error e => rw [hs2] at h; exact nomatch h
  | ok r₄ =>
  rw [hs2] at h
  dsimp only at h
  cases r₄ with
  | true =>
    exact (structEta_sound ihw ihd ihi hs2 hwb hwa hbb hba hLbb hLba
      hokb hoka hab haa hvb hva).symm
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hu1 : structUnitCertP env fuel d a b with
  | error e => rw [hu1] at h; exact nomatch h
  | ok r₅ =>
  rw [hu1] at h
  dsimp only at h
  cases r₅ with
  | true =>
    exact structUnit_sound ihw ihd ihi hu1 hwa hwb hba hbb hLba hLbb
      hoka hokb haa hab hva hvb
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨hpa, hpb⟩ := proofIrrel_pt ihw ihi h hwa hwb hba hbb
    hLba hLbb hoka hokb haa hab
  rw [hva] at hpa
  rw [hvb] at hpb
  exact (Option.some.inj hpa).trans (Option.some.inj hpb).symm

end Claims

end Setlec
