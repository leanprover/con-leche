module

public import Fragment.Interp

@[expose] public section

/-!
# The semantic invariant `WellDenoted`

There is no typing judgement in the proof.  In its place stands a
**semantic** judgement on terms, `WellDenoted M φ ρ e`, defined by
recursion on the term: it holds of a term when it holds of the
subterms and one condition on the term's own shape is met.  The
invariant **records what is a type** — a truth value or a strict set
(`IsTy`, `Lib.lean`), the sets whose members are all the point or none
of them:

* an application's argument is in the function's domain, `a ∈ dom(f)`
  (`AppliesTo`): the function is the point, or a graph whose domain is
  a type holding the argument;
* a λ's domain is a type, the body is well-denoted at every value of
  the domain, and some family of types bounds it;
* a Π's domain is a type, the body is well-denoted at every value of
  the domain and denotes a type there;
* a `let` has its value well-denoted, and its body well-denoted at the
  value's value (task #342, F4); its type is not read, as the
  interpretation does not read it;
* variables, sorts and constants are always well-denoted.

The regime of a binder is no datum of the term (task #344): it is
read off these values by the interpretation, and the type clauses are
what makes that reading coherent — an abstraction is a member of its
function space (`SetLib.lamV_mem`) because every fibre is a
type.  The predicate transports along `Expr.inst` by the substitution
lemmas of `Interp.lean` (`WellDenoted_inst0`); a β step at a redex that
is not the point keeps the denotation and the invariant
(`Sound.lean`, `Red.beta_sound`).

A **context** `Γ` is satisfied by an environment `ρ` (`Sat`) when each
`Γ[i]` is well-denoted and a type under the rest of `ρ`, and `ρ i` a
member of it — the semantic reading of `Γ ⊢`.

Con-leche's `ConLeche/Semantics/WellDenoted.lean` is the same recursive
definition on its terms `Term`, with the same type clauses and
further ones for their projections, equalities and proof term; it
states the application clause through a function space holding the
head, whose domain is a type holding the argument, which implies
`AppliesTo` (`appliesTo_of_mem_piR`).
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V] (M : Name → List Nat → V) (φ : Name → Nat)

/-- **The semantic invariant** (see the module docstring): a binder's
domain is a type; a binder's codomain fibres are types; an application's
argument is in the function's domain (`AppliesTo`). -/
def WellDenoted : (Nat → V) → Expr → Prop
  | _, .bvar _ => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | ρ, .app f a =>
    WellDenoted ρ f ∧ WellDenoted ρ a ∧ AppliesTo (interp M φ ρ f) (interp M φ ρ a)
  | ρ, .lam A b =>
    WellDenoted ρ A ∧ IsTy (interp M φ ρ A) ∧
      (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted (cons x ρ) b) ∧
      ∃ B : V → V,
        (∀ x, x ∈ˢ interp M φ ρ A → interp M φ (cons x ρ) b ∈ˢ B x) ∧
        (∀ x, x ∈ˢ interp M φ ρ A → IsTy (B x))
  | ρ, .pi A B =>
    WellDenoted ρ A ∧ IsTy (interp M φ ρ A) ∧
      (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted (cons x ρ) B) ∧
      (∀ x, x ∈ˢ interp M φ ρ A → IsTy (interp M φ (cons x ρ) B))
  | ρ, .letE _ v b =>
    WellDenoted ρ v ∧ WellDenoted (cons (interp M φ ρ v) ρ) b

@[simp] theorem WellDenoted_bvar (ρ : Nat → V) (i : Nat) : WellDenoted M φ ρ (.bvar i) := trivial
@[simp] theorem WellDenoted_sort (ρ : Nat → V) (u : Level) : WellDenoted M φ ρ (.sort u) := trivial
@[simp] theorem WellDenoted_const (ρ : Nat → V) (c : Name) (ls : List Level) :
    WellDenoted M φ ρ (.const c ls) := trivial

theorem WellDenoted_app (ρ : Nat → V) (f a : Expr) :
    WellDenoted M φ ρ (.app f a) ↔
      (WellDenoted M φ ρ f ∧ WellDenoted M φ ρ a ∧
        AppliesTo (interp M φ ρ f) (interp M φ ρ a)) := by
  rw [WellDenoted]

theorem WellDenoted_lam (ρ : Nat → V) (A : Expr) (b : Expr) :
    WellDenoted M φ ρ (.lam A b) ↔
      (WellDenoted M φ ρ A ∧ IsTy (interp M φ ρ A) ∧
        (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) b) ∧
        ∃ B : V → V,
          (∀ x, x ∈ˢ interp M φ ρ A → interp M φ (cons x ρ) b ∈ˢ B x) ∧
          (∀ x, x ∈ˢ interp M φ ρ A → IsTy (B x))) := by
  rw [WellDenoted]

theorem WellDenoted_pi (ρ : Nat → V) (A : Expr) (B : Expr) :
    WellDenoted M φ ρ (.pi A B) ↔
      (WellDenoted M φ ρ A ∧ IsTy (interp M φ ρ A) ∧
        (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) B) ∧
        (∀ x, x ∈ˢ interp M φ ρ A → IsTy (interp M φ (cons x ρ) B))) := by
  rw [WellDenoted]

theorem WellDenoted_letE (ρ : Nat → V) (T v b : Expr) :
    WellDenoted M φ ρ (.letE T v b) ↔
      (WellDenoted M φ ρ v ∧ WellDenoted M φ (cons (interp M φ ρ v) ρ) b) := by
  rw [WellDenoted]

theorem WellDenoted_liftN (n : Nat) :
    ∀ (e : Expr) (k : Nat) (ρ : Nat → V),
      WellDenoted M φ ρ (e.liftN n k) ↔ WellDenoted M φ (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i => intro k ρ; simp
  | sort u => intro k ρ; simp
  | const c ls => intro k ρ; simp
  | app f a ihf iha =>
    intro k ρ
    rw [Expr.liftN_app, WellDenoted_app, WellDenoted_app, ihf, iha, interp_liftN, interp_liftN]
  | lam A b ihA ihb =>
    intro k ρ
    rw [Expr.liftN_lam, WellDenoted_lam, WellDenoted_lam, ihA, interp_liftN]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl)))
    · rw [ihb, cons_shiftE]
    · rw [interp_liftN, cons_shiftE]
  | pi A B ihA ihB =>
    intro k ρ
    rw [Expr.liftN_pi, WellDenoted_pi, WellDenoted_pi, ihA, interp_liftN]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · rw [ihB, cons_shiftE]
    · rw [interp_liftN, cons_shiftE]
  | letE T v b _ ihv ihb =>
    intro k ρ
    rw [Expr.liftN_letE, WellDenoted_letE, WellDenoted_letE, ihv, ihb, interp_liftN, cons_shiftE]

/-- The invariant through instantiation, given the substituted term's. -/
theorem WellDenoted_inst :
    ∀ (e a : Expr) (k : Nat) (ρ : Nat → V),
      WellDenoted M φ (shiftE k 0 ρ) a →
      (WellDenoted M φ ρ (e.inst a k) ↔
        WellDenoted M φ (instE k (interp M φ (shiftE k 0 ρ) a) ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ ha
    simp only [Expr.inst_bvar, WellDenoted_bvar, iff_true]
    by_cases h : i < k
    · rw [ite_eq_left h]; exact trivial
    · rw [ite_eq_right h]
      by_cases h2 : i = k
      · rw [ite_eq_left h2]; exact (WellDenoted_liftN M φ k a 0 ρ).mpr ha
      · rw [ite_eq_right h2]; exact trivial
  | sort u => intro a k ρ _; simp
  | const c ls => intro a k ρ _; simp
  | app f b ihf ihb =>
    intro a k ρ ha
    rw [Expr.inst_app, WellDenoted_app, WellDenoted_app, ihf a k ρ ha, ihb a k ρ ha, interp_inst, interp_inst]
  | lam A b ihA ihb =>
    intro a k ρ ha
    rw [Expr.inst_lam, WellDenoted_lam, WellDenoted_lam, ihA a k ρ ha, interp_inst]
    have ha' : ∀ x, WellDenoted M φ (shiftE (k + 1) 0 (cons x ρ)) a := by
      intro x; rwa [shiftE_succ_cons]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl)))
    · rw [ihb a (k + 1) (cons x ρ) (ha' x), shiftE_succ_cons, cons_instE]
    · rw [interp_inst, shiftE_succ_cons, cons_instE]
  | pi A B ihA ihB =>
    intro a k ρ ha
    rw [Expr.inst_pi, WellDenoted_pi, WellDenoted_pi, ihA a k ρ ha, interp_inst]
    have ha' : ∀ x, WellDenoted M φ (shiftE (k + 1) 0 (cons x ρ)) a := by
      intro x; rwa [shiftE_succ_cons]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · rw [ihB a (k + 1) (cons x ρ) (ha' x), shiftE_succ_cons, cons_instE]
    · rw [interp_inst, shiftE_succ_cons, cons_instE]
  | letE T v b _ ihv ihb =>
    intro a k ρ ha
    have ha' : ∀ x, WellDenoted M φ (shiftE (k + 1) 0 (cons x ρ)) a := by
      intro x; rwa [shiftE_succ_cons]
    rw [Expr.inst_letE, WellDenoted_letE, WellDenoted_letE, ihv a k ρ ha, interp_inst,
      ihb a (k + 1) _ (ha' _), shiftE_succ_cons, cons_instE]

theorem WellDenoted_inst0 {e a : Expr} {ρ : Nat → V} (ha : WellDenoted M φ ρ a) :
    WellDenoted M φ ρ (e.inst a) ↔ WellDenoted M φ (cons (interp M φ ρ a) ρ) e := by
  have h := WellDenoted_inst M φ e a 0 ρ (by rwa [shiftE_zero_zero])
  rwa [shiftE_zero_zero, instE_zero] at h

/-- The invariant through level instantiation. -/
theorem WellDenoted_instL (ps : List Name) (ls : List Level) :
    ∀ (e : Expr) (ρ : Nat → V),
      WellDenoted M φ ρ (e.instL ps ls) ↔ WellDenoted M (Level.substVal φ ps ls) ρ e := by
  intro e
  induction e with
  | bvar i => intro ρ; simp
  | sort u => intro ρ; simp
  | const c ls => intro ρ; simp
  | app f a ihf iha =>
    intro ρ
    rw [Expr.instL_app, WellDenoted_app, WellDenoted_app, ihf, iha, interp_instL, interp_instL]
  | lam A b ihA ihb =>
    intro ρ
    rw [Expr.instL_lam, WellDenoted_lam, WellDenoted_lam, ihA, interp_instL]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihb _))
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl)))
    rw [interp_instL]
  | pi A B ihA ihB =>
    intro ρ
    rw [Expr.instL_pi, WellDenoted_pi, WellDenoted_pi, ihA, interp_instL]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihB _))
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    rw [interp_instL]
  | letE T v b _ ihv ihb =>
    intro ρ
    rw [Expr.instL_letE, WellDenoted_letE, WellDenoted_letE, ihv, ihb, interp_instL]

/-! ### Establishing the application clause -/

/-- **The application clause, from the function's type**: a function in a
Π's interpretation and an argument in the Π's domain make a
well-denoted application, the Π's own clauses supplying that the
domain is a type. -/
theorem WellDenoted_app_of {ρ : Nat → V} {f a A B : Expr}
    (hf : WellDenoted M φ ρ f) (ha : WellDenoted M φ ρ a)
    (hpi : WellDenoted M φ ρ (.pi A B))
    (hmemf : interp M φ ρ f ∈ˢ interp M φ ρ (.pi A B))
    (hmema : interp M φ ρ a ∈ˢ interp M φ ρ A) :
    WellDenoted M φ ρ (.app f a) := by
  rw [WellDenoted_app]
  rw [interp_pi] at hmemf
  rw [WellDenoted_pi] at hpi
  exact ⟨hf, ha, appliesTo_of_mem_piR hmemf hpi.2.1 hmema⟩

/-! ## Contexts -/

/-- **Satisfaction of a context**: every entry is a well-denoted type
under the environment beyond it, and the variable's value is a member
of it.  The semantic `Γ ⊢`. -/
def Sat : List Expr → (Nat → V) → Prop
  | [], _ => True
  | A :: Γ, ρ =>
    Sat Γ (fun i => ρ (i + 1)) ∧ WellDenoted M φ (fun i => ρ (i + 1)) A ∧
      IsTy (interp M φ (fun i => ρ (i + 1)) A) ∧ ρ 0 ∈ˢ interp M φ (fun i => ρ (i + 1)) A

@[simp] theorem Sat_nil (ρ : Nat → V) : Sat M φ [] ρ := trivial

theorem Sat_cons {Γ : List Expr} {A : Expr} {ρ : Nat → V} {x : V} :
    Sat M φ (A :: Γ) (cons x ρ) ↔
      Sat M φ Γ ρ ∧ WellDenoted M φ ρ A ∧ IsTy (interp M φ ρ A) ∧ x ∈ˢ interp M φ ρ A := Iff.rfl

theorem Sat_get : ∀ {Γ : List Expr} {ρ : Nat → V} {i : Nat} {A : Expr},
    Sat M φ Γ ρ → Γ[i]? = some A →
    WellDenoted M φ (shiftE (i + 1) 0 ρ) A ∧ IsTy (interp M φ (shiftE (i + 1) 0 ρ) A) ∧
      ρ i ∈ˢ interp M φ (shiftE (i + 1) 0 ρ) A
  | [], _, _, _, _, h => by simp at h
  | B :: Γ, ρ, 0, A, hs, h => by
    simp at h
    subst h
    rw [shiftE_zero]
    exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2⟩
  | B :: Γ, ρ, i + 1, A, hs, h => by
    simp at h
    have := Sat_get (ρ := fun j => ρ (j + 1)) hs.1 h
    rw [shiftE_zero] at this ⊢
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

end Fragment
