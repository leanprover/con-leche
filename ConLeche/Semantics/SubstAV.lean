module

import ConLeche.Verify.Denote.VClosed
public import ConLeche.Semantics.Tower.TowerKit

@[expose] public section

/-!
# Parallel substitution of annotated terms

`AnnotTerm.substAV τ e k` replaces every bound variable `k + j` (at or
above the cut `k`) by `τ j`, lifted over the `k` binders passed.  It is
the reading-side twin of the Expr operation `Expr.substFvars`
(`Verify/SubstFvars.lean`): a container frame's constructor type is the
recorded member-abstracted constructor type with its parameter and hole
variables replaced ALL AT ONCE — by the key's parameters and by the
frame's holes or the other members' formers — and its reading is the
recorded reading so substituted (`denoteMeta_substFvars`,
`Model/Annot/BitSubstFvars.lean`).  The one semantic lemma
(`interp_substAV`) reads it at the valuation holding `τ`'s values; for
`τ` of length one it is `interp_inst`'s content.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term
open ConLeche.SetTheory

universe w

namespace AnnotTerm

/-- **Parallel substitution** at the cut `k`: `bvar (k + j) ↦ (τ j).liftN k`. -/
def substAV (τ : Nat → AnnotTerm) : AnnotTerm → (k : Nat) → AnnotTerm
  | .bvar i, k => if i < k then .bvar i else (τ (i - k)).liftN k
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app f a, k => .app (substAV τ f k) (substAV τ a k)
  | .lam u A b, k => .lam u (substAV τ A k) (substAV τ b (k + 1))
  | .pi u v A B, k => .pi u v (substAV τ A k) (substAV τ B (k + 1))
  | .eqE a b, k => .eqE (substAV τ a k) (substAV τ b k)
  | .fst e, k => .fst (substAV τ e k)
  | .snd e, k => .snd (substAV τ e k)
  | .prf, _ => .prf

@[simp] theorem substAV_app (τ : Nat → AnnotTerm) (f a : AnnotTerm) (k : Nat) :
    substAV τ (.app f a) k = .app (substAV τ f k) (substAV τ a k) := rfl
@[simp] theorem substAV_pi (τ : Nat → AnnotTerm) (u v : Nat) (A B : AnnotTerm) (k : Nat) :
    substAV τ (.pi u v A B) k = .pi u v (substAV τ A k) (substAV τ B (k + 1)) := rfl
@[simp] theorem substAV_lam (τ : Nat → AnnotTerm) (u : Nat) (A b : AnnotTerm) (k : Nat) :
    substAV τ (.lam u A b) k = .lam u (substAV τ A k) (substAV τ b (k + 1)) := rfl
@[simp] theorem substAV_fst (τ : Nat → AnnotTerm) (e : AnnotTerm) (k : Nat) :
    substAV τ (.fst e) k = .fst (substAV τ e k) := rfl
@[simp] theorem substAV_snd (τ : Nat → AnnotTerm) (e : AnnotTerm) (k : Nat) :
    substAV τ (.snd e) k = .snd (substAV τ e k) := rfl

theorem substAV_bvar_lt (τ : Nat → AnnotTerm) {i k : Nat} (h : i < k) :
    substAV τ (.bvar i) k = .bvar i := by
  simp [substAV, h]

theorem substAV_bvar_ge (τ : Nat → AnnotTerm) {i k : Nat} (h : k ≤ i) :
    substAV τ (.bvar i) k = (τ (i - k)).liftN k := by
  simp [substAV, show ¬ i < k by omega]

/-- **A term closed below the cut is fixed.** -/
theorem substAV_eq_self (τ : Nat → AnnotTerm) : ∀ (e : AnnotTerm) {k : Nat},
    Term.bvarsBelow k e.erase → substAV τ e k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    have h' : i < k := h
    simp [substAV, h']
  | sort u => intro _ _; rfl
  | const c us => intro _ _; rfl
  | prf => intro _ _; rfl
  | app f a ihf iha => intro k h; rw [substAV_app, ihf h.1, iha h.2]
  | lam u A b ihA ihb => intro k h; rw [substAV_lam, ihA h.1, ihb h.2]
  | pi u v A B ihA ihB => intro k h; rw [substAV_pi, ihA h.1, ihB h.2]
  | eqE a b iha ihb => intro k h; show AnnotTerm.eqE _ _ = _; rw [iha h.1, ihb h.2]
  | fst e ihe => intro k h; rw [substAV_fst, ihe h]
  | snd e ihe => intro k h; rw [substAV_snd, ihe h]

theorem substAV_mkAppN (τ : Nat → AnnotTerm) (k : Nat) :
    ∀ (as : List AnnotTerm) (f : AnnotTerm),
      substAV τ (mkAppN f as) k = mkAppN (substAV τ f k) (as.map (substAV τ · k))
  | [], _ => rfl
  | a :: as, f => by
    rw [mkAppN_cons, substAV_mkAppN τ k as, substAV_app]; rfl

theorem substAV_projAV (τ : Nat → AnnotTerm) (k : Nat) :
    ∀ (i : Nat) (e : AnnotTerm), substAV τ (projAV i e) k = projAV i (substAV τ e k)
  | 0, _ => rfl
  | i + 1, e => by
    show substAV τ (projAV i (.snd e)) k = projAV i (.snd (substAV τ e k))
    rw [substAV_projAV τ k i]; rfl

end AnnotTerm

variable (V : Type w) [SetTheory V]

/-- The valuation `substAV τ · k` reads its subject at: the `k` innermost
positions kept, position `k + j` holding `τ j`'s value (read below the
`k` binders). -/
noncomputable def substE (τ : Nat → AnnotTerm) (k : Nat) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else interp V (shiftE k 0 ρ) (τ (i - k))

theorem cons_substE (τ : Nat → AnnotTerm) (k : Nat) (x : V) (ρ : Nat → V) :
    cons x (substE V τ k ρ) = substE V τ (k + 1) (cons x ρ) := by
  funext i
  cases i with
  | zero => simp [substE]
  | succ j =>
    show substE V τ k ρ j = substE V τ (k + 1) (cons x ρ) (j + 1)
    simp only [substE]
    by_cases h : j < k
    · rw [ite_eq_left h, ite_eq_left (show j + 1 < k + 1 by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_right (show ¬ (j + 1 < k + 1) by omega), shiftE_succ_cons,
        show j + 1 - (k + 1) = j - k by omega]

/-- **The substitution lemma** for parallel substitution. -/
theorem interp_substAV (τ : Nat → AnnotTerm) :
    ∀ (e : AnnotTerm) (k : Nat) (ρ : Nat → V),
      interp V ρ (AnnotTerm.substAV τ e k) = interp V (substE V τ k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    by_cases h : i < k
    · rw [AnnotTerm.substAV_bvar_lt τ h, interp_bvar, interp_bvar]
      simp [substE, h]
    · rw [AnnotTerm.substAV_bvar_ge τ (by omega), interp_liftN, interp_bvar]
      simp only [substE, ite_eq_right h]
  | sort u => intro k ρ; rfl
  | const c us => intro k ρ; rfl
  | prf => intro k ρ; rfl
  | app f a ihf iha =>
    intro k ρ; rw [AnnotTerm.substAV_app, interp_app, interp_app, ihf, iha]
  | lam u A b ihA ihb =>
    intro k ρ
    rw [AnnotTerm.substAV_lam, interp_lam, interp_lam, ihA]
    congr 1
    funext x
    rw [ihb, ← cons_substE]
  | pi u v A B ihA ihB =>
    intro k ρ
    rw [AnnotTerm.substAV_pi, interp_pi, interp_pi, ihA]
    congr 1
    funext x
    rw [ihB, ← cons_substE]
  | eqE a b iha ihb =>
    intro k ρ
    show interp V ρ (.eqE _ _) = _
    rw [interp_eqE, interp_eqE, iha, ihb]
  | fst e ihe => intro k ρ; rw [AnnotTerm.substAV_fst, interp_fst, interp_fst, ihe]
  | snd e ihe => intro k ρ; rw [AnnotTerm.substAV_snd, interp_snd, interp_snd, ihe]

/-- Below a spine of values, the cut moves up by the spine's length. -/
theorem substE_consList (τ : Nat → AnnotTerm) :
    ∀ (fs : List V) (k : Nat) (ρ : Nat → V),
      substE V τ (fs.length + k) (consList fs ρ) = consList fs (substE V τ k ρ)
  | [], k, ρ => by simp [consList]
  | f :: fs, k, ρ => by
    rw [List.length_cons, show fs.length + 1 + k = fs.length + (k + 1) by omega, consList_cons,
      substE_consList τ fs (k + 1) (cons f ρ), ← cons_substE, consList_cons]


/-! ## Π-towers -/

namespace AnnotTerm

/-- A Π-tower's binder data, substituted at increasing cuts. -/
def substTele (τ : Nat → AnnotTerm) : Nat → List (Nat × Nat × AnnotTerm) → List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | k, d :: ds => (d.1, d.2.1, substAV τ d.2.2 k) :: substTele τ (k + 1) ds

theorem substAV_mkPisAV (τ : Nat → AnnotTerm) (B : AnnotTerm) :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) (k : Nat),
      substAV τ (mkPisAV ab B) k = mkPisAV (substTele τ k ab) (substAV τ B (k + ab.length))
  | [], k => rfl
  | d :: ab, k => by
    show AnnotTerm.pi _ _ _ (substAV τ (mkPisAV ab B) (k + 1)) = AnnotTerm.pi _ _ _ _
    rw [substAV_mkPisAV τ B ab (k + 1), List.length_cons, show k + 1 + ab.length = k + (ab.length + 1)
      by omega]


end AnnotTerm

/-- **A spine fits a substituted telescope exactly when it fits the
telescope at the substituted valuation.** -/
theorem spineFit_substTele (τ : Nat → AnnotTerm) :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) (k : Nat) (ρ : Nat → V) (fs : List V),
      SpineFit ρ ((AnnotTerm.substTele τ k ab).map (·.2.2)) fs ↔
        SpineFit (substE V τ k ρ) (ab.map (·.2.2)) fs
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | d :: ab, k, ρ, f :: fs => by
    show (f ∈ˢ interp V ρ (AnnotTerm.substAV τ d.2.2 k) ∧ _) ↔ (f ∈ˢ interp V _ d.2.2 ∧ _)
    rw [interp_substAV, spineFit_substTele τ ab (k + 1) (cons f ρ) fs, ← cons_substE]

end ConLeche.Semantics
