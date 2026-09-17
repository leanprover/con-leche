module

public import ConLeche.Model.Steps.Stuck
public import ConLeche.Verify.EraseAnnots

public section

/-!
# `denoteMeta` does not read `fvar` annotations (task #315)

`denoteMeta` answers `.bvar (d - 1 - idx)` at every `fvar` leaf
(`Model/Annot/Bit.lean`), so the type annotation a variable carries is
invisible to it.  What the syntactic side needs is the *equational*
form of that: two terms that differ only in their annotations —
`Expr.eraseAnnots`-equal, `ConLeche/Verify/EraseAnnots.lean` — read
alike.

This is the currency in which an abstract-then-open roundtrip
(`Expr.abstractRange` drops the annotation, `openPisAtFvars` recreates
it from the opener's domain) reaches the model tier: the two sides are
equal only up to annotations, and `denoteMeta_congr_eraseAnnots` says
that is enough.
-/

namespace ConLeche.Model

open ConLeche.Semantics
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

variable {env : Env} {φ : Name → Nat}

/-- **The congruence**: `denoteMeta` reads two terms that differ only
in `fvar` type annotations alike.  Stated as an equation, so the two
runs fail together as well. -/
theorem denoteMeta_congr_eraseAnnots {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (d : Nat) (e₁ : Expr) (e₂ : Expr), e₁.eraseAnnots = e₂.eraseAnnots →
      denoteMeta acval env φ d e₁ = denoteMeta acval env φ d e₂ := by
  intro d e₁
  induction d, e₁ using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain rfl := Expr.eraseAnnots_eq_sort h.symm
    rfl
  | case2 d idx ty =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain ⟨ty', rfl⟩ := Expr.eraseAnnots_eq_fvar h.symm
    rw [denoteMeta, denoteMeta]
  | case3 d n us ci hf hlen =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain rfl := Expr.eraseAnnots_eq_const h.symm
    rfl
  | case4 d n us ci hf hlen =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain rfl := Expr.eraseAnnots_eq_const h.symm
    rfl
  | case5 d n us hf =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain rfl := Expr.eraseAnnots_eq_const h.symm
    rfl
  | case6 d ty body m ihty ihbody =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain ⟨ty₂, b₂, rfl, hty, hb⟩ := Expr.eraseAnnots_eq_forallE h.symm
    rw [denoteMeta, denoteMeta, ihty ty₂ hty.symm,
      ihbody (b₂.instantiate1 (.fvar d ty₂)) ?_]
    rw [Expr.eraseAnnots_instantiate1, Expr.eraseAnnots_instantiate1, hb]
    rfl
  | case7 d ty body m ihty ihbody =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain ⟨ty₂, b₂, rfl, hty, hb⟩ := Expr.eraseAnnots_eq_lam h.symm
    rw [denoteMeta, denoteMeta, ihty ty₂ hty.symm,
      ihbody (b₂.instantiate1 (.fvar d ty₂)) ?_]
    rw [Expr.eraseAnnots_instantiate1, Expr.eraseAnnots_instantiate1, hb]
    rfl
  | case8 d f a ihf iha =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain ⟨f₂, a₂, rfl, hf, ha⟩ := Expr.eraseAnnots_eq_app h.symm
    rw [denoteMeta, denoteMeta, ihf f₂ hf.symm, iha a₂ ha.symm]
  | case9 d ty val body =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain ⟨ty₂, v₂, b₂, rfl, -, -, -⟩ := Expr.eraseAnnots_eq_letE h.symm
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain ⟨pe₂, rfl, hpe⟩ := Expr.eraseAnnots_eq_proj h.symm
    rw [denoteMeta, denoteMeta, ihe pe₂ hpe.symm]
  | case11 d n hsup =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain rfl := Expr.eraseAnnots_eq_lit h.symm
    rfl
  | case12 d n hsup =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain rfl := Expr.eraseAnnots_eq_lit h.symm
    rfl
  | case13 d s hsup =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain rfl := Expr.eraseAnnots_eq_lit h.symm
    rfl
  | case14 d s hsup =>
    intro e₂ h
    simp only [Expr.eraseAnnots] at h
    obtain rfl := Expr.eraseAnnots_eq_lit h.symm
    rfl
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro e₂ h
    cases x with
    | bvar i =>
      simp only [Expr.eraseAnnots] at h
      obtain rfl := Expr.eraseAnnots_eq_bvar h.symm
      rfl
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-- **The erasure law**: erasing the annotations moves no reading. -/
theorem denoteMeta_eraseAnnots {acval : Name → (Name → Nat) → AnnotTerm}
    (d : Nat) (e : Expr) :
    denoteMeta acval env φ d e.eraseAnnots = denoteMeta acval env φ d e :=
  denoteMeta_congr_eraseAnnots d e.eraseAnnots e (Expr.eraseAnnots_idem e)

/-- The spine transposes the erasure law. -/
theorem DenoteMetaSpine.eraseAnnots {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d (as.map Expr.eraseAnnots) vs ↔
        DenoteMetaSpine acval env φ d as vs := by
  intro as
  induction as with
  | nil =>
    intro vs
    exact Iff.rfl
  | cons a as ih =>
    intro vs
    constructor
    · intro h
      cases h with
      | cons ha htl =>
        exact .cons (by rw [← denoteMeta_eraseAnnots d a]; exact ha) (ih.mp htl)
    · intro h
      cases h with
      | cons ha htl =>
        exact .cons (by rw [denoteMeta_eraseAnnots d a]; exact ha) (ih.mpr htl)

end ConLeche.Model
