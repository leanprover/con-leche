import Setlec.Kernel.TypeChecker
import Setlec.Verify.Shift

/-!
# Abstraction and the open/close roundtrip

`annotate` opens each binder, processes the body, and re-closes it with
`abstract1`.  The lemmas here make that roundtrip exact:

* `fvarConsistent d n ty e`: every reachable `fvar d` leaf is exactly
  `fvar d n ty` — true of any opened body and preserved by `annotate`;
* `abstract1_instantiate1`: closing then re-opening is the identity,
  given consistency and no loose bound variables;
* scoping and loose-bvar bookkeeping for `abstract1`/`instantiate1` and
  their preservation through `annotate`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Setlec

open Expr

/-- Every reachable `fvar` leaf with index `d` is exactly `fvar d n ty`. -/
def Expr.fvarConsistent (d : Nat) (n : Name) (ty : Expr) : Expr → Prop
  | .fvar idx n' ty' => idx = d → n' = n ∧ ty' = ty
  | .app f a => fvarConsistent d n ty f ∧ fvarConsistent d n ty a
  | .lam _ t b _ | .forallE _ t b _ => fvarConsistent d n ty t ∧ fvarConsistent d n ty b
  | .letE _ t v b => fvarConsistent d n ty t ∧ fvarConsistent d n ty v ∧ fvarConsistent d n ty b
  | .proj _ _ e => fvarConsistent d n ty e
  | _ => True

/-- Closing then re-opening a binder body is the identity. -/
theorem abstract1_instantiate1 {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), fvarConsistent d n ty e → e.looseBVarsBounded k = true →
      (e.abstract1 d k).instantiate1 (.fvar d n ty) k = e := by
  intro e
  induction e <;> intro k hc hb <;>
    simp_all [Expr.fvarConsistent, Expr.looseBVarsBounded, Expr.abstract1, Expr.instantiate1]
  case bvar i =>
    have h1 : ¬ (i = k) := by omega
    have h2 : ¬ (i > k) := by omega
    simp [h1, h2]
  case fvar idx n' ty' ih =>
    by_cases hidx : idx = d
    · obtain ⟨rfl, rfl⟩ := hc hidx
      simp [hidx, Expr.instantiate1]
    · simp [hidx, Expr.instantiate1]

/-- Abstracting away the top variable lowers the scope bound. -/
theorem WScoped.abstract1 {d : Nat} :
    ∀ {e : Expr} (k : Nat), WScoped (d + 1) e → WScoped d (e.abstract1 d k) := by
  intro e
  induction e <;> intro k hw <;>
    simp_all [Expr.abstract1, WScoped]
  case fvar idx n' ty' ih =>
    by_cases hidx : idx = d
    · simp [hidx, WScoped]
    · simp only [hidx, if_false, WScoped]
      exact ⟨by omega, hw.2⟩

/-- Opening establishes consistency: a body free of `fvar d` opened with
`fvar d n ty` mentions it consistently. -/
theorem fvarConsistent_instantiate1 {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), fvarsBelow d e →
      fvarConsistent d n ty (e.instantiate1 (.fvar d n ty) k) := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.instantiate1, fvarsBelow, Expr.fvarConsistent]
  case bvar i =>
    split
    · simp [Expr.fvarConsistent]
    · split <;> simp [Expr.fvarConsistent]
  case fvar idx n' ty' ih =>
    omega

/-- Consistency at `d` survives opening with a *different* index. -/
theorem fvarConsistent_instantiate1' {d d' : Nat} {n n' : Name} {ty ty' : Expr}
    (hne : d ≠ d') :
    ∀ (e : Expr) (k : Nat), fvarConsistent d n ty e →
      fvarConsistent d n ty (e.instantiate1 (.fvar d' n' ty') k) := by
  intro e
  induction e <;> intro k hc <;>
    simp_all [Expr.instantiate1, Expr.fvarConsistent]
  case bvar i =>
    split
    · simp [Expr.fvarConsistent]
      intro h
      exact absurd h.symm hne
    · split <;> simp [Expr.fvarConsistent]

/-- Consistency at `d` survives abstracting a *different* index. -/
theorem fvarConsistent_abstract1 {d d' : Nat} {n : Name} {ty : Expr}
    (hne : d ≠ d') :
    ∀ (e : Expr) (k : Nat), fvarConsistent d n ty e →
      fvarConsistent d n ty (e.abstract1 d' k) := by
  intro e
  induction e <;> intro k hc <;>
    simp_all [Expr.abstract1, Expr.fvarConsistent]
  case fvar idx n'' ty'' ih =>
    split
    · simp [Expr.fvarConsistent]
    · simpa [Expr.fvarConsistent] using hc

/-- Opening lowers the loose-bvar bound by one. -/
theorem looseBVarsBounded_instantiate1 {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d n ty) k).looseBVarsBounded k = true := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.instantiate1, Expr.looseBVarsBounded]
  case bvar i =>
    split
    · simp [Expr.looseBVarsBounded]
    · split <;> simp [Expr.looseBVarsBounded] <;> omega

/-- Abstracting raises the loose-bvar bound by one. -/
theorem looseBVarsBounded_abstract1 {d : Nat} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.abstract1 d k).looseBVarsBounded (k + 1) = true := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.abstract1, Expr.looseBVarsBounded]
  case bvar i => omega
  case fvar idx n' ty' ih =>
    split <;> simp [Expr.looseBVarsBounded] <;> omega

/-! ## Preservation through `annotate` -/

/-- Inversion for `annotate` on applications: whatever the embedded
application-rule check did, a successful result is the two annotated
subterms reassembled. -/
theorem annotate_app_inv {env : Env} {d : Nat} {f a e' : Expr}
    (h : annotate env d (.app f a) = .ok e') :
    ∃ f' a', annotate env d f = .ok f' ∧ annotate env d a = .ok a' ∧
      e' = .app f' a' := by
  simp only [annotate, Bind.bind, Except.bind] at h
  cases hf : annotate env d f with
  | error e => rw [hf] at h; exact nomatch h
  | ok f' =>
  rw [hf] at h; dsimp only at h
  cases ha : annotate env d a with
  | error e => rw [ha] at h; exact nomatch h
  | ok a' =>
  rw [ha] at h; dsimp only at h
  cases hit : inferType env d f' with
  | error e => rw [hit] at h; exact nomatch h
  | ok tf =>
  rw [hit] at h; dsimp only at h
  cases hwh : whnf env whnfFuel tf with
  | error e => rw [hwh] at h; exact nomatch h
  | ok w =>
  rw [hwh] at h; dsimp only at h
  cases w with
  | forallE n ty body m =>
    dsimp only at h
    cases hia : inferType env d a' with
    | error e => rw [hia] at h; exact nomatch h
    | ok ta =>
    rw [hia] at h; dsimp only at h
    cases hde : isDefEq env d ta ty with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h; dsimp only at h
    cases b with
    | true =>
      simp only [if_true, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨f', a', rfl, rfl, h.symm⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      exact nomatch h
  | bvar i => exact nomatch h
  | fvar i n' t' => exact nomatch h
  | sort u => exact nomatch h
  | const n' us => exact nomatch h
  | app f'' a'' => exact nomatch h
  | lam n' t' b' m' => exact nomatch h
  | letE n' t' v' b' => exact nomatch h
  | lit l' => exact nomatch h
  | proj s' i' e'' => exact nomatch h

theorem annotate_WScoped {env : Env} :
    ∀ (e : Expr) {d : Nat} {e' : Expr},
      annotate env d e = .ok e' → WScoped d e → WScoped d e'
  | .bvar i, d, e', h, hw => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | .fvar idx n ty, d, e', h, hw => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | .sort u, d, e', h, hw => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | .const n us, d, e', h, hw => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | .app f a, d, e', h, hw => by
    simp only [WScoped] at hw
    obtain ⟨f', a', hf, ha, rfl⟩ := annotate_app_inv h
    simp only [WScoped]
    exact ⟨annotate_WScoped f hf hw.1, annotate_WScoped a ha hw.2⟩
  | .forallE n ty body m, d, e', h, hw => by
    simp only [WScoped] at hw
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hty : annotate env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    have hwty' := annotate_WScoped ty hty hw.1
    cases hbody : annotate env (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferType env (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hes : ensureSort env bt with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hwbody' := annotate_WScoped (body.instantiate1 (.fvar d n ty')) hbody
      (hwty'.instantiate1 0 hw.2)
    simp only [WScoped]
    exact ⟨hwty', WScoped.abstract1 0 hwbody'⟩
  | .lam n ty body m, d, e', h, hw => by
    simp only [WScoped] at hw
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hty : annotate env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    have hwty' := annotate_WScoped ty hty hw.1
    cases hbody : annotate env (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferType env (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hit2 : inferType env (d + 1) bt with
    | error e => rw [hit2] at h; exact nomatch h
    | ok bt2 =>
    rw [hit2] at h; dsimp only at h
    cases hes : ensureSort env bt2 with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hwbody' := annotate_WScoped (body.instantiate1 (.fvar d n ty')) hbody
      (hwty'.instantiate1 0 hw.2)
    simp only [WScoped]
    exact ⟨hwty', WScoped.abstract1 0 hwbody'⟩
  | .letE _ _ _ _, d, e', h, _ => by simp [annotate] at h
  | .lit _, d, e', h, _ => by simp [annotate] at h
  | .proj _ _ _, d, e', h, _ => by simp [annotate] at h
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

theorem annotate_fvarConsistent {env : Env} {d₀ : Nat} {n₀ : Name} {ty₀ : Expr} :
    ∀ (e : Expr) {d : Nat} {e' : Expr}, d₀ < d →
      annotate env d e = .ok e' → fvarConsistent d₀ n₀ ty₀ e →
      fvarConsistent d₀ n₀ ty₀ e'
  | .bvar i, d, e', _, h, hc => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hc
  | .fvar idx n ty, d, e', _, h, hc => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hc
  | .sort u, d, e', _, h, hc => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hc
  | .const n us, d, e', _, h, hc => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hc
  | .app f a, d, e', hd, h, hc => by
    simp only [Expr.fvarConsistent] at hc
    obtain ⟨f', a', hf, ha, rfl⟩ := annotate_app_inv h
    exact ⟨annotate_fvarConsistent f hd hf hc.1, annotate_fvarConsistent a hd ha hc.2⟩
  | .forallE n ty body m, d, e', hd, h, hc => by
    simp only [Expr.fvarConsistent] at hc
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hty : annotate env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotate env (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferType env (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hes : ensureSort env bt with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Expr.fvarConsistent]
    exact ⟨annotate_fvarConsistent ty hd hty hc.1,
      fvarConsistent_abstract1 (by omega) _ 0
        (annotate_fvarConsistent _ (by omega) hbody
          (fvarConsistent_instantiate1' (by omega) body 0 hc.2))⟩
  | .lam n ty body m, d, e', hd, h, hc => by
    simp only [Expr.fvarConsistent] at hc
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hty : annotate env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotate env (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferType env (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hit2 : inferType env (d + 1) bt with
    | error e => rw [hit2] at h; exact nomatch h
    | ok bt2 =>
    rw [hit2] at h; dsimp only at h
    cases hes : ensureSort env bt2 with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Expr.fvarConsistent]
    exact ⟨annotate_fvarConsistent ty hd hty hc.1,
      fvarConsistent_abstract1 (by omega) _ 0
        (annotate_fvarConsistent _ (by omega) hbody
          (fvarConsistent_instantiate1' (by omega) body 0 hc.2))⟩
  | .letE _ _ _ _, d, e', _, h, _ => by simp [annotate] at h
  | .lit _, d, e', _, h, _ => by simp [annotate] at h
  | .proj _ _ _, d, e', _, h, _ => by simp [annotate] at h
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

theorem annotate_looseBVars {env : Env} :
    ∀ (e : Expr) {d : Nat} {e' : Expr},
      annotate env d e = .ok e' → e.looseBVarsBounded 0 = true →
      e'.looseBVarsBounded 0 = true
  | .bvar i, d, e', h, hb => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | .fvar idx n ty, d, e', h, hb => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | .sort u, d, e', h, hb => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | .const n us, d, e', h, hb => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | .app f a, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨f', a', hf, ha, rfl⟩ := annotate_app_inv h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨annotate_looseBVars f hf hb.1, annotate_looseBVars a ha hb.2⟩
  | .forallE n ty body m, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hty : annotate env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotate env (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferType env (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hes : ensureSort env bt with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨annotate_looseBVars ty hty hb.1, ?_⟩
    exact looseBVarsBounded_abstract1 _ 0
      (annotate_looseBVars _ hbody (looseBVarsBounded_instantiate1 body 0 hb.2))
  | .lam n ty body m, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hty : annotate env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotate env (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferType env (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hit2 : inferType env (d + 1) bt with
    | error e => rw [hit2] at h; exact nomatch h
    | ok bt2 =>
    rw [hit2] at h; dsimp only at h
    cases hes : ensureSort env bt2 with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨annotate_looseBVars ty hty hb.1, ?_⟩
    exact looseBVarsBounded_abstract1 _ 0
      (annotate_looseBVars _ hbody (looseBVarsBounded_instantiate1 body 0 hb.2))
  | .letE _ _ _ _, d, e', h, _ => by simp [annotate] at h
  | .lit _, d, e', h, _ => by simp [annotate] at h
  | .proj _ _ _, d, e', h, _ => by simp [annotate] at h
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)



/-! ## Leaf equivalence

`annotate`-then-`abstract1` returns a term with the same skeleton and the
same `fvar`/`bvar` leaves as the unopened input — only binder annotations
(and inner binder bodies, recursively in the same way) differ.  `LeafEquiv`
captures exactly what `FvarsOk` can see, so `FvarsOk` transports across it.
-/

/-- Same constructor skeleton and identical `fvar`/`bvar` leaves;
binder names/metadata may differ. -/
def Expr.LeafEquiv : Expr → Expr → Prop
  | .bvar i, .bvar j => i = j
  | .fvar idx n ty, .fvar idx' n' ty' => idx = idx' ∧ n = n' ∧ ty = ty'
  | .sort _, .sort _ => True
  | .const _ _, .const _ _ => True
  | .lit _, .lit _ => True
  | .app f a, .app f' a' => LeafEquiv f f' ∧ LeafEquiv a a'
  | .lam _ ty b _, .lam _ ty' b' _ => LeafEquiv ty ty' ∧ LeafEquiv b b'
  | .forallE _ ty b _, .forallE _ ty' b' _ => LeafEquiv ty ty' ∧ LeafEquiv b b'
  | .letE _ ty v b, .letE _ ty' v' b' =>
    LeafEquiv ty ty' ∧ LeafEquiv v v' ∧ LeafEquiv b b'
  | .proj _ _ e, .proj _ _ e' => LeafEquiv e e'
  | _, _ => False

theorem Expr.LeafEquiv.refl : ∀ (e : Expr), Expr.LeafEquiv e e := by
  intro e
  induction e <;> simp_all [Expr.LeafEquiv]

/-- Leaf-equivalent terms have the same free-variable content. -/
theorem Expr.LeafEquiv.hasFvar_eq : ∀ (e₁ e₂ : Expr), Expr.LeafEquiv e₁ e₂ →
    e₁.hasFvar = e₂.hasFvar := by
  intro e₁
  induction e₁ with
  | fvar idx n ty _ =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
  | app f a ihf iha =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
    case app f' a' => rw [ihf f' hle.1, iha a' hle.2]
  | lam n ty body m ihty ihbody =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
    case lam n' ty' body' m' => rw [ihty ty' hle.1, ihbody body' hle.2]
  | forallE n ty body m ihty ihbody =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
    case forallE n' ty' body' m' => rw [ihty ty' hle.1, ihbody body' hle.2]
  | letE n ty val body ihty ihval ihbody =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
    case letE n' ty' val' body' =>
      rw [ihty ty' hle.1, ihval val' hle.2.1, ihbody body' hle.2.2]
  | proj s i e ih =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
    case proj s' i' e' => exact ih e' hle
  | bvar i =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
  | sort u =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
  | const n us =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
  | lit l =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]



/-- Un-instantiation: if `y` has the same leaves as `x` opened with
`fvar D`, then abstracting `D` out of `y` recovers the leaves of `x` —
provided `x` does not mention `fvar D` and has no loose bvars above `k`. -/
theorem leafEquiv_abstract_of_inst {D : Nat} {n : Name} {ty : Expr} :
    ∀ (x : Expr) (k : Nat) (y : Expr),
      Expr.LeafEquiv (x.instantiate1 (.fvar D n ty) k) y →
      fvarsBelow D x → x.looseBVarsBounded (k + 1) = true →
      Expr.LeafEquiv x (y.abstract1 D k) := by
  intro x
  induction x with
  | bvar i =>
    intro k y hle hf hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1] at hle
    by_cases hik : i = k
    · simp only [hik, if_pos rfl] at hle
      cases y <;> simp_all [Expr.LeafEquiv]
      case fvar idx n' ty' =>
        obtain ⟨rfl, -, -⟩ := hle
        simp [Expr.abstract1, Expr.LeafEquiv, hik]
    · have hik' : ¬ (i > k) := by omega
      simp only [hik, if_false, hik', Expr.instantiate1] at hle
      cases y <;> simp_all [Expr.LeafEquiv]
      case bvar j =>
        subst hle
        simp [Expr.abstract1, Expr.LeafEquiv]
  | fvar idx n' ty' _ =>
    intro k y hle hf hb
    simp only [Expr.fvarsBelow] at hf
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv]
    case fvar idx2 n2 ty2 =>
      obtain ⟨rfl, rfl, rfl⟩ := hle
      have : ¬ (idx = D) := by omega
      simp [Expr.abstract1, this, Expr.LeafEquiv]
  | sort u =>
    intro k y hle hf hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | const nm us =>
    intro k y hle hf hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | lit l =>
    intro k y hle hf hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | app f a ihf iha =>
    intro k y hle hf hb
    simp only [Expr.fvarsBelow] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | lam nm tyx body ihm ihty ihbody =>
    intro k y hle hf hb
    simp only [Expr.fvarsBelow] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | forallE nm tyx body ihm ihty ihbody =>
    intro k y hle hf hb
    simp only [Expr.fvarsBelow] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | letE nm tyx vx body ihty ihv ihbody =>
    intro k y hle hf hb
    simp only [Expr.fvarsBelow] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | proj s i e ih =>
    intro k y hle hf hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
    case proj s2 i2 e2 => exact ih k e2 hle hf hb

/-- `annotate` preserves skeleton and leaves. -/
theorem annotate_leafEquiv {env : Env} :
    ∀ (e : Expr) {d : Nat} {e' : Expr},
      annotate env d e = .ok e' → WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeafEquiv e e'
  | .bvar i, d, e', h, _, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ Expr.LeafEquiv.refl _
  | .fvar idx n ty, d, e', h, _, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ Expr.LeafEquiv.refl _
  | .sort u, d, e', h, _, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ Expr.LeafEquiv.refl _
  | .const n us, d, e', h, _, _ => by
    simp only [annotate, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ Expr.LeafEquiv.refl _
  | .app f a, d, e', h, hw, hb => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨f', a', hf, ha, rfl⟩ := annotate_app_inv h
    simp only [Expr.LeafEquiv]
    exact ⟨annotate_leafEquiv f hf hw.1 hb.1, annotate_leafEquiv a ha hw.2 hb.2⟩
  | .forallE n ty body m, d, e', h, hw, hb => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hty : annotate env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotate env (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferType env (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hes : ensureSort env bt with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Expr.LeafEquiv]
    refine ⟨annotate_leafEquiv ty hty hw.1 hb.1, ?_⟩
    refine leafEquiv_abstract_of_inst (D := d) (n := n) (ty := ty') body 0 body' ?_
      hw.2.fvarsBelow hb.2
    exact annotate_leafEquiv (body.instantiate1 (.fvar d n ty')) hbody
      ((annotate_WScoped ty hty hw.1).instantiate1 0 hw.2)
      (looseBVarsBounded_instantiate1 body 0 hb.2)
  | .lam n ty body m, d, e', h, hw, hb => by
    simp only [WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [annotate, Bind.bind, Except.bind] at h
    cases hty : annotate env d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotate env (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferType env (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hit2 : inferType env (d + 1) bt with
    | error e => rw [hit2] at h; exact nomatch h
    | ok bt2 =>
    rw [hit2] at h; dsimp only at h
    cases hes : ensureSort env bt2 with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Expr.LeafEquiv]
    refine ⟨annotate_leafEquiv ty hty hw.1 hb.1, ?_⟩
    refine leafEquiv_abstract_of_inst (D := d) (n := n) (ty := ty') body 0 body' ?_
      hw.2.fvarsBelow hb.2
    exact annotate_leafEquiv (body.instantiate1 (.fvar d n ty')) hbody
      ((annotate_WScoped ty hty hw.1).instantiate1 0 hw.2)
      (looseBVarsBounded_instantiate1 body 0 hb.2)
  | .letE _ _ _ _, d, e', h, _, _ => by simp [annotate] at h
  | .lit _, d, e', h, _, _ => by simp [annotate] at h
  | .proj _ _ _, d, e', h, _, _ => by simp [annotate] at h
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

end Setlec
