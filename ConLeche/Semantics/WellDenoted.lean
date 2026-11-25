module

public import ConLeche.Semantics.Kit
import ConLeche.SetTheory.Derive.Sigma
@[expose] public section

/-!
# `WellDenoted`: the semantic invariant over `interp` (task #151 tier C; task #342)

The model's invariant on `Term`.  It holds of a term when
it holds of the subterms and one condition on the term's own shape is
met; the conditions **record what is a type** (`IsTy X := X ∈ univZero
∨ Strict X`, the sets whose members are all the point or none of them):

* an application's function applies to its argument (`AppliesTo`): it
  is the point, or a graph whose domain is a type holding the argument
  — a graph determines its domain (`graph_dom_unique`);
* a λ's domain is a type and the body is well-denoted at every value of
  the domain;
* a Π's domain is a type, the body is well-denoted at every value of
  the domain and denotes a type there;
* a `let` has its value well-denoted, and its body well-denoted at the
  value;
* variables, sorts, constants and the proof are always well-denoted.

The binders' regimes are read off the values by `interp` (`piV`/`lamV`);
the type clauses are what makes that reading coherent: an abstraction
is a member of its function space (`lamV_mem`) when its body values lie
in types, which the typing rules supply.  The predicate transports along `inst` (`WellDenoted_inst0`); a
β step at a redex that is not the point keeps the denotation and the
invariant (`WellDenoted_beta`).

Every type fact is the semantic content of a `Sort` the checker
inferred; `IsTy_univ`, `IsTy_piV` and `IsTy_of_mem_univ` produce them.
-/

namespace ConLeche.Semantics
open ConLeche.Term (Term)
open ConLeche.SetModel

open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-- Kinded hereditary truthfulness of the binder/application structure
under a variable environment (see the module docstring). -/
def WellDenoted : (Nat → V) → Term → Prop
  | ρ, .pi A B =>
    WellDenoted ρ A ∧ IsTy (interp V ρ A) ∧
    (∀ x, x ∈ˢ interp V ρ A → WellDenoted (cons x ρ) B) ∧
    (∀ x, x ∈ˢ interp V ρ A → IsTy (interp V (cons x ρ) B))
  | ρ, .lam A b =>
    WellDenoted ρ A ∧ IsTy (interp V ρ A) ∧
    (∀ x, x ∈ˢ interp V ρ A → WellDenoted (cons x ρ) b)
  | ρ, .app f a =>
    WellDenoted ρ f ∧ WellDenoted ρ a ∧ AppliesTo (interp V ρ f) (interp V ρ a)
  | ρ, .fst e =>
    WellDenoted ρ e ∧
    ∃ u v A Bf, ∃ hS : HasSigmaPairs A Bf, interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf hS ∧
      A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v
  | ρ, .snd e =>
    WellDenoted ρ e ∧
    ∃ u v A Bf, ∃ hS : HasSigmaPairs A Bf, interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf hS ∧
      A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v
  | ρ, .eqE a b => WellDenoted ρ a ∧ WellDenoted ρ b
  | ρ, .letE v b => WellDenoted ρ v ∧ WellDenoted (cons (interp V ρ v) ρ) b
  | _, .bvar _ => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | _, .prf => True

/-! ### Clause equations -/

@[simp] theorem WellDenoted_bvar (ρ : Nat → V) (i : Nat) :
    WellDenoted V ρ (.bvar i) = True := by rw [WellDenoted]
@[simp] theorem WellDenoted_sort (ρ : Nat → V) (u : Nat) :
    WellDenoted V ρ (.sort u) = True := by rw [WellDenoted]
@[simp] theorem WellDenoted_const (ρ : Nat → V) (c : ConLeche.Term.BConst)
    (us : List Nat) : WellDenoted V ρ (.const c us) = True := by
  rw [WellDenoted]
@[simp] theorem WellDenoted_prf (ρ : Nat → V) :
    WellDenoted V ρ .prf = True := by rw [WellDenoted]
theorem WellDenoted_pi (ρ : Nat → V) (A B : Term) :
    WellDenoted V ρ (.pi A B) =
      (WellDenoted V ρ A ∧ IsTy (interp V ρ A) ∧
        (∀ x, x ∈ˢ interp V ρ A → WellDenoted V (cons x ρ) B) ∧
        (∀ x, x ∈ˢ interp V ρ A → IsTy (interp V (cons x ρ) B))) := by
  rw [WellDenoted]
theorem WellDenoted_lam (ρ : Nat → V) (A b : Term) :
    WellDenoted V ρ (.lam A b) =
      (WellDenoted V ρ A ∧ IsTy (interp V ρ A) ∧
        (∀ x, x ∈ˢ interp V ρ A → WellDenoted V (cons x ρ) b)) := by
  rw [WellDenoted]
theorem WellDenoted_app (ρ : Nat → V) (f a : Term) :
    WellDenoted V ρ (.app f a) =
      (WellDenoted V ρ f ∧ WellDenoted V ρ a ∧
        AppliesTo (interp V ρ f) (interp V ρ a)) := by
  rw [WellDenoted]
theorem WellDenoted_fst (ρ : Nat → V) (e : Term) :
    WellDenoted V ρ (.fst e) =
      (WellDenoted V ρ e ∧
        ∃ u v A Bf, ∃ hS : HasSigmaPairs A Bf,
          interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf hS ∧
          A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v) := by
  rw [WellDenoted]
theorem WellDenoted_snd (ρ : Nat → V) (e : Term) :
    WellDenoted V ρ (.snd e) =
      (WellDenoted V ρ e ∧
        ∃ u v A Bf, ∃ hS : HasSigmaPairs A Bf,
          interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf hS ∧
          A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v) := by
  rw [WellDenoted]
theorem WellDenoted_eqE (ρ : Nat → V) (a b : Term) :
    WellDenoted V ρ (.eqE a b) = (WellDenoted V ρ a ∧ WellDenoted V ρ b) := by
  rw [WellDenoted]
/-- A `let`: the value at `ρ`, the body at the value; the type is not
in the node and is not read. -/
theorem WellDenoted_letE (ρ : Nat → V) (v b : Term) :
    WellDenoted V ρ (.letE v b) =
      (WellDenoted V ρ v ∧ WellDenoted V (cons (interp V ρ v) ρ) b) := by
  rw [WellDenoted]

/-! ### The substitution metatheory -/

/-- Truthfulness through lifting. -/
theorem WellDenoted_liftN (n : Nat) :
    ∀ (e : Term) (k : Nat) (ρ : Nat → V),
      WellDenoted V ρ (e.liftN n k) ↔ WellDenoted V (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [Term.liftN_bvar]
    split <;> simp
  | sort u => intro k ρ; simp
  | const c us => intro k ρ; simp
  | app f a ihf iha =>
    intro k ρ
    rw [Term.liftN_app, WellDenoted_app, WellDenoted_app, ihf, iha,
      interp_liftN, interp_liftN]
  | lam A b ihA ihb =>
    intro k ρ
    rw [Term.liftN_lam, WellDenoted_lam, WellDenoted_lam, ihA, interp_liftN]
    refine and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl ?_))
    rw [ihb, cons_shiftE]
  | pi A B ihA ihB =>
    intro k ρ
    rw [Term.liftN_pi, WellDenoted_pi, WellDenoted_pi, ihA, interp_liftN]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · rw [ihB, cons_shiftE]
    · rw [interp_liftN, cons_shiftE]
  | letE v b ihv ihb =>
    intro k ρ
    rw [Term.liftN_letE, WellDenoted_letE, WellDenoted_letE, ihv,
      interp_liftN, ihb, cons_shiftE]
  | eqE a b iha ihb =>
    intro k ρ
    rw [Term.liftN_eqE, WellDenoted_eqE, WellDenoted_eqE, iha, ihb]
  | fst e ihe =>
    intro k ρ
    rw [Term.liftN_fst, WellDenoted_fst, WellDenoted_fst, ihe,
      interp_liftN]
  | snd e ihe =>
    intro k ρ
    rw [Term.liftN_snd, WellDenoted_snd, WellDenoted_snd, ihe,
      interp_liftN]
  | prf => intro k ρ; simp

/-- Truthfulness through instantiation. -/
theorem WellDenoted_inst :
    ∀ (e a : Term) (k : Nat) (ρ : Nat → V),
      WellDenoted V (shiftE k 0 ρ) a →
      (WellDenoted V ρ (e.inst a k) ↔
        WellDenoted V (instE k (interp V (shiftE k 0 ρ) a) ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ ha
    show WellDenoted V ρ
        (if i < k then .bvar i
         else if i = k then Term.liftN k a else .bvar (i - 1)) ↔ _
    by_cases h : i < k
    · simp [ite_eq_left h]
    · by_cases h2 : i = k
      · simp only [ite_eq_right h, ite_eq_left h2, WellDenoted_bvar, iff_true]
        exact (WellDenoted_liftN V k a 0 ρ).mpr ha
      · simp [ite_eq_right h, ite_eq_right h2]
  | sort u => intro a k ρ _; simp [Term.inst]
  | const c us => intro a k ρ _; simp [Term.inst]
  | app f b ihf ihb =>
    intro a k ρ ha
    rw [Term.inst_app, WellDenoted_app, WellDenoted_app, ihf a k ρ ha,
      ihb a k ρ ha, interp_inst, interp_inst]
  | lam A b ihA ihb =>
    intro a k ρ ha
    rw [Term.inst_lam, WellDenoted_lam, WellDenoted_lam, ihA a k ρ ha,
      interp_inst]
    refine and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl ?_))
    have ha' : WellDenoted V (shiftE (k + 1) 0 (cons x ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihb a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
  | pi A B ihA ihB =>
    intro a k ρ ha
    rw [Term.inst_pi, WellDenoted_pi, WellDenoted_pi, ihA a k ρ ha,
      interp_inst]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · have ha' : WellDenoted V (shiftE (k + 1) 0 (cons x ρ)) a := by
        rw [shiftE_succ_cons]; exact ha
      rw [ihB a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
    · rw [interp_inst, shiftE_succ_cons, cons_instE]
  | letE v b ihv ihb =>
    intro a k ρ ha
    rw [Term.inst_letE, WellDenoted_letE, WellDenoted_letE, ihv a k ρ ha,
      interp_inst]
    refine and_congr Iff.rfl ?_
    have ha' : WellDenoted V (shiftE (k + 1) 0
        (cons (interp V (instE k (interp V (shiftE k 0 ρ) a) ρ) v) ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihb a (k + 1) _ ha', shiftE_succ_cons, cons_instE]
  | eqE x y ihx ihy =>
    intro a k ρ ha
    rw [Term.inst_eqE, WellDenoted_eqE, WellDenoted_eqE, ihx a k ρ ha,
      ihy a k ρ ha]
  | fst e ihe =>
    intro a k ρ ha
    rw [Term.inst_fst, WellDenoted_fst, WellDenoted_fst, ihe a k ρ ha,
      interp_inst]
  | snd e ihe =>
    intro a k ρ ha
    rw [Term.inst_snd, WellDenoted_snd, WellDenoted_snd, ihe a k ρ ha,
      interp_inst]
  | prf => intro a k ρ _; simp [Term.inst]

/-- Substitution at the outermost binder — the β/ζ transport form. -/
theorem WellDenoted_inst0 {e a : Term} {ρ : Nat → V}
    (ha : WellDenoted V ρ a) :
    WellDenoted V ρ (e.inst a) ↔
      WellDenoted V (cons (interp V ρ a) ρ) e := by
  have h := WellDenoted_inst V e a 0 ρ (by rwa [shiftE_zero_zero])
  rwa [shiftE_zero_zero, instE_zero] at h

/-- **ζ, graded**: a `let` interprets as its reduct, and with its value
graded it is graded exactly when its reduct is.  Unconditional: no
binder, so no regime. -/
theorem interp_zeta (v b : Term) (ρ : Nat → V) :
    interp V ρ (.letE v b) = interp V ρ (b.inst v) := by
  rw [interp_letE, interp_inst0]

theorem WellDenoted_zeta {v b : Term} {ρ : Nat → V}
    (hv : WellDenoted V ρ v) :
    WellDenoted V ρ (.letE v b) ↔ WellDenoted V ρ (b.inst v) := by
  rw [WellDenoted_letE, WellDenoted_inst0 V hv]
  exact and_iff_right hv

/-! ### The graded β step

At a redex that is not the point, from the subject's `WellDenoted`
alone: the λ is not the point (`app_pt`), so it is a graph and the
application clause reads the argument off the graph: it lies in the
λ's domain (`appliesTo_graph`), and β is `app_lamV`.  At the point there
is nothing to show: the claims that read this are conditional on "not
the point". -/

/-- **The graded β step** at a redex that is not the point. -/
theorem WellDenoted_beta {A b a : Term} {ρ : Nat → V}
    (h : WellDenoted V ρ (.app (.lam A b) a))
    (hne : interp V ρ (.app (.lam A b) a) ≠ pt) :
    interp V ρ a ∈ˢ interp V ρ A ∧
    interp V ρ (.app (.lam A b) a) = interp V ρ (b.inst a) ∧
    WellDenoted V ρ (b.inst a) := by
  rw [WellDenoted_app] at h
  obtain ⟨hlam, ha, hap⟩ := h
  have hlne : interp V ρ (.lam A b) ≠ pt := by
    intro h0; apply hne; rw [interp_app, h0, app_pt]
  obtain ⟨-, -, hbody⟩ := (WellDenoted_lam V ρ A b).mp hlam
  have hgraph : interp V ρ (.lam A b) =
      graph (fun x => interp V (cons x ρ) b) (interp V ρ A)
        (interp_hasGraph_cons ρ (interp V ρ A) b) := by
    rw [interp_lam] at hlne ⊢; exact lamV_eq_graph hlne
  have haA : interp V ρ a ∈ˢ interp V ρ A := by
    rw [hgraph] at hap; exact (appliesTo_graph.mp hap).2
  refine ⟨haA, ?_, (WellDenoted_inst0 V ha).mpr (hbody _ haA)⟩
  rw [interp_app, interp_lam, app_lamV haA, interp_inst0]

/-! ## The app slot's establishment -/

/-- **The application clause**, from the function's membership in a
Π-type's reading, the argument in its domain, and the domain a type. -/
theorem appSlot_of_pi {ρ : Nat → V} {f a Aa Ba : Term}
    (hf : interp V ρ f ∈ˢ interp V ρ (.pi Aa Ba))
    (ha : interp V ρ a ∈ˢ interp V ρ Aa)
    (hdom : IsTy (interp V ρ Aa)) :
    AppliesTo (interp V ρ f) (interp V ρ a) := by
  rw [interp_pi] at hf
  exact appliesTo_of_mem_piV hf hdom ha

/-- The full app-clause establishment: the hereditary halves plus the
slot, the shape the `app` claim discharges. -/
theorem WellDenoted_app_of {ρ : Nat → V} {f a Aa Ba : Term}
    (hokf : WellDenoted V ρ f) (hoka : WellDenoted V ρ a)
    (hf : interp V ρ f ∈ˢ interp V ρ (.pi Aa Ba))
    (ha : interp V ρ a ∈ˢ interp V ρ Aa)
    (hdom : IsTy (interp V ρ Aa)) :
    WellDenoted V ρ (.app f a) := by
  rw [WellDenoted_app]
  exact ⟨hokf, hoka, appSlot_of_pi V hf ha hdom⟩

end ConLeche.Semantics
