import Setlec.SetR.Interp2.Step2.Levels

/-!
# Level-locality — the syntactic kit

Two facts the level-locality statements need before any checker
reasoning starts, both about `Level`/`Expr` alone:

* `Level.substFn_agree` — two assignments that agree on `ps` agree,
  after `substFn` at *any* parameter list, at every parameter of `ps`,
  provided the substituted levels have their own parameters in `ps`.
  This is what `denote2`'s `.const` clause needs: the two sides read
  the valuation at two assignments, and the valuation law speaks about
  agreement, not about the assignments themselves.
* `Expr.allLevelParamsDefined_instantiate1_gen` — opening a binder with
  an `fvar` whose type is parameter-bounded keeps the body bounded (the
  `constsResolve_instantiate1_gen` shape, `Verify/InstSpine.lean`).
-/

namespace Setlec

/-- `substFn` reads the assignment only through the substituted levels'
parameters — the `ps`-indexed form (no length condition: a ragged
list falls through to the assignment itself, where the agreement
hypothesis answers directly). -/
theorem Level.substFn_agree {φ₁ φ₂ : Name → Nat} {ps : List Name}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ {ks : List Name} {us : List Level},
      (∀ u ∈ us, u.allParamsDefined ps = true) →
      ∀ p ∈ ps, Level.substFn φ₁ ks us p = Level.substFn φ₂ ks us p := by
  intro ks
  induction ks with
  | nil => intro us _ p hp; exact hφ p hp
  | cons k ks ih =>
    intro us hus p hp
    cases us with
    | nil => exact hφ p hp
    | cons u us =>
      simp only [Level.substFn]
      split
      · exact Level.eval_ext (hus u (by simp)) hφ
      · exact ih (fun x hx => hus x (by simp [hx])) p hp

/-- Opening a binder keeps the level parameters bounded. -/
theorem Expr.allLevelParamsDefined_instantiate1_gen {ps : List Name}
    {v : Expr} (hv : v.allLevelParamsDefined ps = true) :
    ∀ {e : Expr} (k : Nat), e.allLevelParamsDefined ps = true →
      (e.instantiate1 v k).allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | fvar idx n ty _ => intro k h; exact h
  | sort u => intro k h; exact h
  | const n us => intro k h; exact h
  | lit l => intro k h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [Expr.instantiate1, Expr.allLevelParamsDefined,
      Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam n ty body m ihty ihbody =>
    intro k h
    simp only [Expr.instantiate1, Expr.allLevelParamsDefined,
      Bool.and_eq_true] at h ⊢
    exact ⟨ihty k h.1, ihbody (k + 1) h.2⟩
  | forallE n ty body m ihty ihbody =>
    intro k h
    simp only [Expr.instantiate1, Expr.allLevelParamsDefined,
      Bool.and_eq_true] at h ⊢
    exact ⟨ihty k h.1, ihbody (k + 1) h.2⟩
  | letE n ty val body ihty ihval ihbody =>
    intro k h
    simp only [Expr.instantiate1, Expr.allLevelParamsDefined,
      Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihty k h.1.1, ihval k h.1.2⟩, ihbody (k + 1) h.2⟩
  | proj s i e ih =>
    intro k h
    simp only [Expr.instantiate1, Expr.allLevelParamsDefined] at h ⊢
    exact ih k h

/-- The binder-opening form `denote2` uses: the substituted term is the
`fvar` carrying the binder's own type. -/
theorem Expr.allLevelParamsDefined_open {ps : List Name}
    {ty body : Expr} {d : Nat} {n : Name}
    (hty : ty.allLevelParamsDefined ps = true)
    (hbody : body.allLevelParamsDefined ps = true) :
    (body.instantiate1 (.fvar d n ty)).allLevelParamsDefined ps
      = true :=
  Expr.allLevelParamsDefined_instantiate1_gen
    (v := .fvar d n ty) hty 0 hbody

end Setlec
