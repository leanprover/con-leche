module

public import ConLeche.Verify.Subst
public import ConLeche.Kernel.Inductives.Positivity

public section

/-!
# Generated telescopes, as syntax

The generated recursor stage (`Kernel/Inductives/GenRec.lean`) stores
the generated recursor type as generated (`classConstOk`): a
`closeTelescope` over the shared prefix, the class's index binders and
its major, of a PLAIN body (a variable applied to variables).  What its
readings need, as pure syntax:

* **the shared prefix stays shared** (`SameDoms`): two telescopes with
  the same first `n` domains keep them equal through `abstract1` and
  `instantiate1`, and open to the same variables;
* **a plain term is left alone by annotation** (`annotateCore_plain`);
* **a motive's type keeps its shape** (`EndsInSort`): `∀ …, Sort u`
  survives erasure and the de Bruijn operations.
-/

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-! ## Erasure and the de Bruijn operations -/

/-! ## The same first domains -/

/-- The first `n` binders of two `∀`-telescopes have the same domains
(the binder data may differ). -/
@[expose] def SameDoms : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | n + 1, .forallE A b _, .forallE A' b' _ => A = A' ∧ SameDoms n b b'
  | _ + 1, _, _ => False

theorem SameDoms.abstract1 {d : Nat} :
    ∀ (n : Nat) {e₁ e₂ : Expr} (k : Nat), SameDoms n e₁ e₂ →
      SameDoms n (e₁.abstract1 d k) (e₂.abstract1 d k)
  | 0, _, _, _, _ => trivial
  | n + 1, .forallE A b m, .forallE A' b' m', k, h => by
    obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, SameDoms.abstract1 n (k + 1) h⟩

theorem SameDoms.instantiate1 {v : Expr} :
    ∀ (n : Nat) {e₁ e₂ : Expr} (k : Nat), SameDoms n e₁ e₂ →
      SameDoms n (e₁.instantiate1 v k) (e₂.instantiate1 v k)
  | 0, _, _, _, _ => trivial
  | n + 1, .forallE A b m, .forallE A' b' m', k, h => by
    obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, SameDoms.instantiate1 n (k + 1) h⟩

/-- Two telescopes over the same prefix have the same first domains. -/
theorem SameDoms.closeTelescope_append :
    ∀ (P : List (Expr × BinderMeta)) (X₁ X₂ : List (Expr × BinderMeta)) (i : Nat)
      (B₁ B₂ : Expr),
      SameDoms P.length (closeTelescope (P ++ X₁) i B₁) (closeTelescope (P ++ X₂) i B₂)
  | [], _, _, _, _, _ => trivial
  | (dom, bm) :: P, X₁, X₂, i, B₁, B₂ => by
    simp only [List.cons_append, closeTelescope, List.length_cons]
    exact ⟨rfl, SameDoms.abstract1 _ 0 (SameDoms.closeTelescope_append P X₁ X₂ (i + 1) B₁ B₂)⟩

/-- **Opening two telescopes with the same first domains** gives the
same variables. -/
theorem SameDoms.open :
    ∀ (n : Nat) {d : Nat} {e₁ e₂ : Expr} {fvs₁ fvs₂ : List Expr} {o₁ o₂ : Expr},
      SameDoms n e₁ e₂ → openPisAtFvars n e₁ d = some (fvs₁, o₁) →
      openPisAtFvars n e₂ d = some (fvs₂, o₂) → fvs₁ = fvs₂
  | 0, _, _, _, _, _, _, _, _, h₁, h₂ => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    rw [← h₁.1, ← h₂.1]
  | n + 1, d, .forallE A b m, .forallE A' b' m', fvs₁, fvs₂, o₁, o₂, h, h₁, h₂ => by
    obtain ⟨rfl, h⟩ := h
    simp only [openPisAtFvars] at h₁ h₂
    split at h₁
    · next fvs₁' o₁' hop₁ =>
      split at h₂
      · next fvs₂' o₂' hop₂ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h₁ h₂
        rw [← h₁.1, ← h₂.1, SameDoms.open n (SameDoms.instantiate1 n 0 h) hop₁ hop₂]
      · exact nomatch h₂
    · exact nomatch h₁

/-- A telescope with `n` leading binders opens. -/
theorem SameDoms.open_isSome :
    ∀ (n : Nat) {d : Nat} {e : Expr}, SameDoms n e e →
      ∃ fvs o, openPisAtFvars n e d = some (fvs, o)
  | 0, _, e, _ => ⟨[], e, rfl⟩
  | n + 1, d, .forallE A b m, h => by
    obtain ⟨fvs, o, hop⟩ := SameDoms.open_isSome n (d := d + 1)
      (SameDoms.instantiate1 (v := .fvar d A) n 0 h.2)
    exact ⟨.fvar d A :: fvs, o, by simp [openPisAtFvars, hop]⟩

/-! ## Plain bodies -/

/-! ## A motive's type: `∀ …, Sort u` -/

/-- `m` leading `∀`-binders, then `Sort u`. -/
@[expose] def EndsInSort : Nat → Level → Expr → Prop
  | 0, u, e => e = .sort u
  | m + 1, u, .forallE _ b _ => EndsInSort m u b
  | _ + 1, _, _ => False

theorem EndsInSort.of_erasedEq {u : Level} :
    ∀ (m : Nat) {e e' : Expr}, Expr.ErasedEq e e' → EndsInSort m u e' → EndsInSort m u e
  | 0, e, e', he, h => by
    simp only [EndsInSort] at h ⊢
    subst h
    match e, he with
    | .sort v, he => rw [show v = u from he]
  | m + 1, e, e', he, h => by
    match e', h with
    | .forallE A' b' mb', h =>
      match e, he with
      | .forallE A b mb, he => exact EndsInSort.of_erasedEq m he.2.2 h
      | .bvar _, he | .fvar _ _, he | .sort _, he | .const _ _, he | .app _ _, he
      | .lam _ _ _, he | .letE _ _ _, he | .lit _, he | .proj _ _ _, he => exact he.elim
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h | .lam _ _ _, h
    | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => exact h.elim

theorem EndsInSort.abstract1 {u : Level} {d : Nat} :
    ∀ (m : Nat) {e : Expr} (k : Nat), EndsInSort m u e → EndsInSort m u (e.abstract1 d k)
  | 0, e, k, h => by
    simp only [EndsInSort] at h ⊢
    subst h; rfl
  | m + 1, .forallE A b mb, k, h => EndsInSort.abstract1 m (k + 1) h

theorem EndsInSort.stripPis {u : Level} :
    ∀ (m : Nat) {e : Expr}, EndsInSort m u e → ∃ bs, e.stripPis m = some (bs, .sort u)
  | 0, e, h => by
    simp only [EndsInSort] at h
    subst h
    exact ⟨[], rfl⟩
  | m + 1, .forallE A b mb, h => by
    obtain ⟨bs, hbs⟩ := EndsInSort.stripPis m h
    exact ⟨(A, mb) :: bs, by simp [Expr.stripPis, hbs]⟩

end ConLeche
