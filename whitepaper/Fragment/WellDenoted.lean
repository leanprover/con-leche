module

public import Fragment.Interp

@[expose] public section

/-!
# The invariant `WellDenoted`

There is no typing judgement in the proof.  In its place stands a
**semantic** predicate on terms, hereditary through the term:

* an application applies a member of some product to a member of its
  domain (and, at a proposition, the fibres are truth values);
* a λ has a bounded codomain — some fibre family the body lands in —
  and if its annotation says "proposition" then the fibres are truth
  values;
* a Π's body is well-denoted at every point of the domain, and if its
  annotation says "proposition" then the body IS a truth value there;
* variables, sorts and constants are always well-denoted.

The binder clauses are where the annotation is held to account: the
datum may claim "proposition" only where the body really denotes a
truth value.  Unlike a typing judgement the predicate is preserved by
β without a substitution lemma about derivations: it transports along
`Expr.inst` by the substitution lemmas of `Interp.lean`
(`WellDenoted_inst0`), and a β step at a well-denoted redex keeps the
denotation and the invariant (`WellDenoted_beta_graph`,
`WellDenoted_beta_prop`).

Mirrors `ConLeche/Semantics/WellDenoted.lean` (with `AnnotValid`, the
annotation's truthfulness, folded into the binder clauses — con-leche
keeps it as a separate conjunct `WellDenotedV`), on the fragment's
syntax.

A **context** `Γ` is satisfied by an environment `ρ` (`Sat`) when each
`ρ i` is a member of what `Γ[i]` denotes under the rest of `ρ`, with
`Γ[i]` itself well-denoted there — the semantic reading of `Γ ⊢`.
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V]

/-- **The invariant**: hereditary well-denotedness of a term under an
environment (see the module docstring). -/
def WellDenoted (M : Name → List Nat → V) (φ : Name → Nat) : (Nat → V) → Expr → Prop
  | ρ, .pi A pw B =>
    WellDenoted M φ ρ A ∧
    (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) B) ∧
    (pw.holds φ = true → ∀ x, x ∈ˢ interp M φ ρ A → interp M φ (cons x ρ) B ∈ˢ univ 0)
  | ρ, .lam A pw b =>
    WellDenoted M φ ρ A ∧
    (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) b) ∧
    ∃ B : V → V,
      (∀ x, x ∈ˢ interp M φ ρ A → interp M φ (cons x ρ) b ∈ˢ B x) ∧
      (pw.holds φ = true → ∀ x, x ∈ˢ interp M φ ρ A → B x ∈ˢ univ 0)
  | ρ, .app f a =>
    WellDenoted M φ ρ f ∧ WellDenoted M φ ρ a ∧
    ∃ (p : Bool) (A : V) (B : V → V),
      interp M φ ρ f ∈ˢ piR p A B ∧ interp M φ ρ a ∈ˢ A ∧
      (p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0)
  | _, .bvar _ => True
  | _, .sort _ => True
  | _, .const _ _ => True

variable (M : Name → List Nat → V) (φ : Name → Nat)

/-! ### Clause equations -/

@[simp] theorem WellDenoted_bvar (ρ : Nat → V) (i : Nat) :
    WellDenoted M φ ρ (.bvar i) = True := by rw [WellDenoted]
@[simp] theorem WellDenoted_sort (ρ : Nat → V) (u : Level) :
    WellDenoted M φ ρ (.sort u) = True := by rw [WellDenoted]
@[simp] theorem WellDenoted_const (ρ : Nat → V) (c : Name) (ls : List Level) :
    WellDenoted M φ ρ (.const c ls) = True := by rw [WellDenoted]
theorem WellDenoted_pi (ρ : Nat → V) (A : Expr) (pw : PropWhen) (B : Expr) :
    WellDenoted M φ ρ (.pi A pw B) =
      (WellDenoted M φ ρ A ∧
        (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) B) ∧
        (pw.holds φ = true → ∀ x, x ∈ˢ interp M φ ρ A →
          interp M φ (cons x ρ) B ∈ˢ univ 0)) := by
  rw [WellDenoted]
theorem WellDenoted_lam (ρ : Nat → V) (A : Expr) (pw : PropWhen) (b : Expr) :
    WellDenoted M φ ρ (.lam A pw b) =
      (WellDenoted M φ ρ A ∧
        (∀ x, x ∈ˢ interp M φ ρ A → WellDenoted M φ (cons x ρ) b) ∧
        ∃ B : V → V,
          (∀ x, x ∈ˢ interp M φ ρ A → interp M φ (cons x ρ) b ∈ˢ B x) ∧
          (pw.holds φ = true → ∀ x, x ∈ˢ interp M φ ρ A → B x ∈ˢ univ 0)) := by
  rw [WellDenoted]
theorem WellDenoted_app (ρ : Nat → V) (f a : Expr) :
    WellDenoted M φ ρ (.app f a) =
      (WellDenoted M φ ρ f ∧ WellDenoted M φ ρ a ∧
        ∃ (p : Bool) (A : V) (B : V → V),
          interp M φ ρ f ∈ˢ piR p A B ∧ interp M φ ρ a ∈ˢ A ∧
          (p = true → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0)) := by
  rw [WellDenoted]

/-! ### The substitution metatheory -/

/-- The invariant through lifting. -/
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
    rw [Expr.liftN_app, WellDenoted_app, WellDenoted_app, ihf, iha,
      interp_liftN, interp_liftN]
  | lam A pw b ihA ihb =>
    intro k ρ
    rw [Expr.liftN_lam, WellDenoted_lam, WellDenoted_lam, ihA, interp_liftN]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl))
    · rw [ihb, cons_shiftE]
    · rw [interp_liftN, cons_shiftE]
  | pi A pw B ihA ihB =>
    intro k ρ
    rw [Expr.liftN_pi, WellDenoted_pi, WellDenoted_pi, ihA, interp_liftN]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (imp_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · rw [ihB, cons_shiftE]
    · rw [interp_liftN, cons_shiftE]

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
    rw [Expr.inst_bvar]
    by_cases h : i < k
    · simp [if_pos h]
    · by_cases h2 : i = k
      · simp only [if_neg h, if_pos h2, WellDenoted_bvar, iff_true]
        exact (WellDenoted_liftN M φ k a 0 ρ).mpr ha
      · simp [if_neg h, if_neg h2]
  | sort u => intro a k ρ _; simp
  | const c ls => intro a k ρ _; simp
  | app f b ihf ihb =>
    intro a k ρ ha
    rw [Expr.inst_app, WellDenoted_app, WellDenoted_app, ihf a k ρ ha,
      ihb a k ρ ha, interp_inst, interp_inst]
  | lam A pw b ihA ihb =>
    intro a k ρ ha
    rw [Expr.inst_lam, WellDenoted_lam, WellDenoted_lam, ihA a k ρ ha, interp_inst]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl))
    · have ha' : WellDenoted M φ (shiftE (k + 1) 0 (cons x ρ)) a := by
        rw [shiftE_succ_cons]; exact ha
      rw [ihb a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
    · rw [interp_inst, shiftE_succ_cons, cons_instE]
  | pi A pw B ihA ihB =>
    intro a k ρ ha
    rw [Expr.inst_pi, WellDenoted_pi, WellDenoted_pi, ihA a k ρ ha, interp_inst]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (imp_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · have ha' : WellDenoted M φ (shiftE (k + 1) 0 (cons x ρ)) a := by
        rw [shiftE_succ_cons]; exact ha
      rw [ihB a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
    · rw [interp_inst, shiftE_succ_cons, cons_instE]

/-- **Substitution at the innermost binder** — the β transport form:
`b[x := a]` is well-denoted exactly when `b` is, under `⟦a⟧ :: ρ`. -/
theorem WellDenoted_inst0 {e a : Expr} {ρ : Nat → V} (ha : WellDenoted M φ ρ a) :
    WellDenoted M φ ρ (e.inst a) ↔
      WellDenoted M φ (cons (interp M φ ρ a) ρ) e := by
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
  | lam A pw b ihA ihb =>
    intro ρ
    rw [Expr.instL_lam, WellDenoted_lam, WellDenoted_lam, ihA, interp_instL,
      PropWhen.holds_substL]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihb _))
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl))
    rw [interp_instL]
  | pi A pw B ihA ihB =>
    intro ρ
    rw [Expr.instL_pi, WellDenoted_pi, WellDenoted_pi, ihA, interp_instL,
      PropWhen.holds_substL]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihB _))
      (imp_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    rw [interp_instL]

/-! ### The β step -/

/-- **β in the graph regime, from the invariant alone.**  At a redex
whose λ is annotated `never`, the application's slot is a graph-regime
product (the λ denotes a graph, never the point), so the graph's
domain is the λ's own and the argument is in it; the graph's β fires
and the invariant transports.  No certificate is needed — this is the
soundness of `Red.betaGate`. -/
theorem WellDenoted_beta_graph {A b a : Expr} {ρ : Nat → V}
    (h : WellDenoted M φ ρ (.app (.lam A .never b) a)) :
    interp M φ ρ (.app (.lam A .never b) a) = interp M φ ρ (b.inst a) ∧
    WellDenoted M φ ρ (b.inst a) := by
  rw [WellDenoted_app] at h
  obtain ⟨hlam, ha, p, A', B', hslot, hmem, -⟩ := h
  rw [WellDenoted_lam] at hlam
  obtain ⟨-, hbody, B, hfib, -⟩ := hlam
  -- the slot's product is in the graph regime: the λ is not the point
  have hp : p = false := by
    cases p
    · rfl
    · exact absurd (eq_pt_of_mem_piR_true hslot) lamR_false_ne_pt
  subst hp
  -- a graph determines its domain: the slot's domain is the λ's own
  have hown : interp M φ ρ (.lam A .never b) ∈ˢ piR false (interp M φ ρ A) B :=
    lamR_mem hfib
  have hAA : interp M φ ρ A = A' := piR_dom_unique hown hslot
  have haA : interp M φ ρ a ∈ˢ interp M φ ρ A := by rw [hAA]; exact hmem
  refine ⟨?_, (WellDenoted_inst0 M φ ha).mpr (hbody _ haA)⟩
  rw [interp_app, interp_lam, PropWhen.holds_never, app_lamR_false haA, interp_inst0]

/-- **β at any regime, given the argument's membership** — the fact the
certified β step supplies (`Red.beta`: the argument's type is
definitionally equal to the domain).  At a proposition both sides are
the point; above it the graph's β fires. -/
theorem WellDenoted_beta {A b a : Expr} {pw : PropWhen} {ρ : Nat → V}
    (h : WellDenoted M φ ρ (.app (.lam A pw b) a))
    (hmem : interp M φ ρ a ∈ˢ interp M φ ρ A) :
    interp M φ ρ (.app (.lam A pw b) a) = interp M φ ρ (b.inst a) ∧
    WellDenoted M φ ρ (b.inst a) := by
  rw [WellDenoted_app] at h
  obtain ⟨hlam, ha, -⟩ := h
  rw [WellDenoted_lam] at hlam
  obtain ⟨-, hbody, B, hfib, hz⟩ := hlam
  refine ⟨?_, (WellDenoted_inst0 M φ ha).mpr (hbody _ hmem)⟩
  rw [interp_app, interp_lam, app_lamR hmem hfib hz, interp_inst0]

/-! ### Establishing the application clause -/

/-- **The application slot, from the function's type**: a function in a
Π's interpretation and an argument in the Π's domain make a
well-denoted application, the Π's own annotation clause supplying the
truth-value component at a proposition. -/
theorem WellDenoted_app_of {ρ : Nat → V} {f a A B : Expr} {pw : PropWhen}
    (hf : WellDenoted M φ ρ f) (ha : WellDenoted M φ ρ a)
    (hpi : WellDenoted M φ ρ (.pi A pw B))
    (hmemf : interp M φ ρ f ∈ˢ interp M φ ρ (.pi A pw B))
    (hmema : interp M φ ρ a ∈ˢ interp M φ ρ A) :
    WellDenoted M φ ρ (.app f a) := by
  rw [WellDenoted_pi] at hpi
  rw [WellDenoted_app]
  exact ⟨hf, ha, pw.holds φ, interp M φ ρ A, fun x => interp M φ (cons x ρ) B,
    hmemf, hmema, hpi.2.2⟩

/-! ## Contexts -/

/-- **Satisfaction of a context**: each entry is well-denoted under the
environment beyond it, and the variable's value is a member of it.
The semantic `Γ ⊢`. -/
def Sat (M : Name → List Nat → V) (φ : Name → Nat) : List Expr → (Nat → V) → Prop
  | [], _ => True
  | A :: Γ, ρ =>
    Sat M φ Γ (fun i => ρ (i + 1)) ∧
    WellDenoted M φ (fun i => ρ (i + 1)) A ∧
    ρ 0 ∈ˢ interp M φ (fun i => ρ (i + 1)) A

@[simp] theorem Sat_nil (ρ : Nat → V) : Sat M φ [] ρ := trivial

/-- Extending the context and the environment together. -/
theorem Sat_cons {Γ : List Expr} {A : Expr} {ρ : Nat → V} {x : V} :
    Sat M φ (A :: Γ) (cons x ρ) ↔
      Sat M φ Γ ρ ∧ WellDenoted M φ ρ A ∧ x ∈ˢ interp M φ ρ A := Iff.rfl

/-- Reading an entry: `Γ[i]` is well-denoted, and `ρ i` a member of
it, under the environment shifted past `i`. -/
theorem Sat_get : ∀ {Γ : List Expr} {ρ : Nat → V} {i : Nat} {A : Expr},
    Sat M φ Γ ρ → Γ[i]? = some A →
    WellDenoted M φ (shiftE (i + 1) 0 ρ) A ∧ ρ i ∈ˢ interp M φ (shiftE (i + 1) 0 ρ) A
  | [], _, _, _, _, h => by simp at h
  | B :: Γ, ρ, 0, A, hs, h => by
    simp at h
    subst h
    rw [shiftE_zero]
    exact ⟨hs.2.1, hs.2.2⟩
  | B :: Γ, ρ, i + 1, A, hs, h => by
    simp at h
    have := Sat_get (ρ := fun j => ρ (j + 1)) hs.1 h
    rw [shiftE_zero] at this ⊢
    exact this

end Fragment
