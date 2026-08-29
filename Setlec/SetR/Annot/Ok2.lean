import Setlec.SetR.Interp2.Kit
import Setlec.SetTheory.Derive.Sigma

/-!
# `AnnotOk2`: kinded hereditary truthfulness over `interp2` (task #151 tier C)

The second soundness's invariant — `AnnotOkV`'s clause-for-clause
transpose onto the annotated syntax and the two-regime interpretation,
with the two upgrades the removal campaign stands on (the architecture
record in `Setlec/SetR/DESIGN.md`, validated by `Interp2/Pilot.lean`):

* **the application slot carries the product kind** —
  `∃ v A B, ⟦f⟧ ∈ piR v A B ∧ ⟦a⟧ ∈ A` — so at a provably-positive
  kind the membership *pins* the domain (`piR_dom_unique`, no side
  condition) and the runtime argument re-check becomes derivable;
* **the λ clause carries the fibre package at the node's own
  annotation** — `∃ B, (∀ x ∈ ⟦A⟧, ⟦b⟧ ∈ B x) ∧ (v = 0 → fibres are
  truth values)` — the semantic content of `Annotates.lam`'s cached
  codomain sort, and what `graded_beta_pos` consumes.

Being a **semantic** predicate on the annotated term, `AnnotOk2`
transports across reduction the way `AnnotOkV` does — the finding-A2
constraint (annotations do not cross `Red`) binds derivation-backed
relations, not this invariant.

The substitution metatheory is the `AnnotOkV` pair, verbatim modulo
`interp → interp2` and the two extra clause components (which only
mention `interp2` of the clause's own subterms, so they ride the same
rewrites).
-/

namespace Setlec.SetR.Interp2

open SetTheory
open Setlec.SetR (AVExpr)

universe w

variable (V : Type w) [SetTheory V]

/-- Kinded hereditary truthfulness of the binder/application structure
under a variable environment (see the module docstring). -/
def AnnotOk2 : (Nat → V) → AVExpr → Prop
  | ρ, .pi _u _v A B =>
    AnnotOk2 ρ A ∧
    ∀ x, x ∈ˢ interp2 V ρ A → AnnotOk2 (cons x ρ) B
  | ρ, .lam v A b =>
    AnnotOk2 ρ A ∧
    (∀ x, x ∈ˢ interp2 V ρ A → AnnotOk2 (cons x ρ) b) ∧
    ∃ B : V → V,
      (∀ x, x ∈ˢ interp2 V ρ A → interp2 V (cons x ρ) b ∈ˢ B x) ∧
      (v = 0 → ∀ x, x ∈ˢ interp2 V ρ A → B x ∈ˢ (univZero : V))
  | ρ, .app f a =>
    AnnotOk2 ρ f ∧ AnnotOk2 ρ a ∧
    ∃ (v : Nat) (A : V) (B : V → V),
      interp2 V ρ f ∈ˢ piR v A B ∧ interp2 V ρ a ∈ˢ A
  | ρ, .letE T v b =>
    AnnotOk2 ρ T ∧ AnnotOk2 ρ v ∧
    AnnotOk2 (cons (interp2 V ρ v) ρ) b
  | ρ, .proj i e =>
    AnnotOk2 ρ e ∧ i < 2 ∧
    ∃ u v A Bf, interp2 V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v
  | ρ, .eqE _ a b => AnnotOk2 ρ a ∧ AnnotOk2 ρ b
  | _, .bvar _ => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | _, .prf => True

/-! ### Clause equations -/

@[simp] theorem AnnotOk2_bvar (ρ : Nat → V) (i : Nat) :
    AnnotOk2 V ρ (.bvar i) = True := by rw [AnnotOk2]
@[simp] theorem AnnotOk2_sort (ρ : Nat → V) (u : Nat) :
    AnnotOk2 V ρ (.sort u) = True := by rw [AnnotOk2]
@[simp] theorem AnnotOk2_const (ρ : Nat → V) (c : Setlec.TT.BConst)
    (us : List Nat) : AnnotOk2 V ρ (.const c us) = True := by
  rw [AnnotOk2]
@[simp] theorem AnnotOk2_prf (ρ : Nat → V) :
    AnnotOk2 V ρ .prf = True := by rw [AnnotOk2]
theorem AnnotOk2_pi (ρ : Nat → V) (u v : Nat) (A B : AVExpr) :
    AnnotOk2 V ρ (.pi u v A B) =
      (AnnotOk2 V ρ A ∧
        ∀ x, x ∈ˢ interp2 V ρ A → AnnotOk2 V (cons x ρ) B) := by
  rw [AnnotOk2]
theorem AnnotOk2_lam (ρ : Nat → V) (v : Nat) (A b : AVExpr) :
    AnnotOk2 V ρ (.lam v A b) =
      (AnnotOk2 V ρ A ∧
        (∀ x, x ∈ˢ interp2 V ρ A → AnnotOk2 V (cons x ρ) b) ∧
        ∃ B : V → V,
          (∀ x, x ∈ˢ interp2 V ρ A → interp2 V (cons x ρ) b ∈ˢ B x) ∧
          (v = 0 → ∀ x, x ∈ˢ interp2 V ρ A →
            B x ∈ˢ (univZero : V))) := by
  rw [AnnotOk2]
theorem AnnotOk2_app (ρ : Nat → V) (f a : AVExpr) :
    AnnotOk2 V ρ (.app f a) =
      (AnnotOk2 V ρ f ∧ AnnotOk2 V ρ a ∧
        ∃ (v : Nat) (A : V) (B : V → V),
          interp2 V ρ f ∈ˢ piR v A B ∧ interp2 V ρ a ∈ˢ A) := by
  rw [AnnotOk2]
theorem AnnotOk2_letE (ρ : Nat → V) (T v b : AVExpr) :
    AnnotOk2 V ρ (.letE T v b) =
      (AnnotOk2 V ρ T ∧ AnnotOk2 V ρ v ∧
        AnnotOk2 V (cons (interp2 V ρ v) ρ) b) := by
  rw [AnnotOk2]
theorem AnnotOk2_proj (ρ : Nat → V) (i : Nat) (e : AVExpr) :
    AnnotOk2 V ρ (.proj i e) =
      (AnnotOk2 V ρ e ∧ i < 2 ∧
        ∃ u v A Bf, interp2 V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
          A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v) := by
  rw [AnnotOk2]
theorem AnnotOk2_eqE (ρ : Nat → V) (T a b : AVExpr) :
    AnnotOk2 V ρ (.eqE T a b) = (AnnotOk2 V ρ a ∧ AnnotOk2 V ρ b) := by
  rw [AnnotOk2]

/-! ### The substitution metatheory (the `AnnotOkV` pair, transposed) -/

/-- Truthfulness through lifting. -/
theorem AnnotOk2_liftN (n : Nat) :
    ∀ (e : AVExpr) (k : Nat) (ρ : Nat → V),
      AnnotOk2 V ρ (e.liftN n k) ↔ AnnotOk2 V (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [AVExpr.liftN_bvar]
    split <;> simp
  | sort u => intro k ρ; simp
  | const c us => intro k ρ; simp
  | app f a ihf iha =>
    intro k ρ
    rw [AVExpr.liftN_app, AnnotOk2_app, AnnotOk2_app, ihf, iha,
      interp2_liftN, interp2_liftN]
  | lam v A b ihA ihb =>
    intro k ρ
    rw [AVExpr.liftN_lam, AnnotOk2_lam, AnnotOk2_lam, ihA, interp2_liftN]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl))
    · rw [ihb, cons_shiftE]
    · rw [interp2_liftN, cons_shiftE]
  | pi u v A B ihA ihB =>
    intro k ρ
    rw [AVExpr.liftN_pi, AnnotOk2_pi, AnnotOk2_pi, ihA, interp2_liftN]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)
    rw [ihB, cons_shiftE]
  | letE T v b ihT ihv ihb =>
    intro k ρ
    rw [AVExpr.liftN_letE, AnnotOk2_letE, AnnotOk2_letE, ihT, ihv,
      interp2_liftN, ihb, cons_shiftE]
  | eqE T a b ihT iha ihb =>
    intro k ρ
    rw [AVExpr.liftN_eqE, AnnotOk2_eqE, AnnotOk2_eqE, iha, ihb]
  | proj i e ihe =>
    intro k ρ
    rw [AVExpr.liftN_proj, AnnotOk2_proj, AnnotOk2_proj, ihe,
      interp2_liftN]
  | prf => intro k ρ; simp

/-- Truthfulness through instantiation. -/
theorem AnnotOk2_inst :
    ∀ (e a : AVExpr) (k : Nat) (ρ : Nat → V),
      AnnotOk2 V (shiftE k 0 ρ) a →
      (AnnotOk2 V ρ (e.inst a k) ↔
        AnnotOk2 V (instE k (interp2 V (shiftE k 0 ρ) a) ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ ha
    show AnnotOk2 V ρ
        (if i < k then .bvar i
         else if i = k then AVExpr.liftN k a else .bvar (i - 1)) ↔ _
    by_cases h : i < k
    · simp [if_pos h]
    · by_cases h2 : i = k
      · simp only [if_neg h, if_pos h2, AnnotOk2_bvar, iff_true]
        exact (AnnotOk2_liftN V k a 0 ρ).mpr ha
      · simp [if_neg h, if_neg h2]
  | sort u => intro a k ρ _; simp [AVExpr.inst]
  | const c us => intro a k ρ _; simp [AVExpr.inst]
  | app f b ihf ihb =>
    intro a k ρ ha
    rw [AVExpr.inst_app, AnnotOk2_app, AnnotOk2_app, ihf a k ρ ha,
      ihb a k ρ ha, interp2_inst, interp2_inst]
  | lam v A b ihA ihb =>
    intro a k ρ ha
    rw [AVExpr.inst_lam, AnnotOk2_lam, AnnotOk2_lam, ihA a k ρ ha,
      interp2_inst]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl))
    · have ha' : AnnotOk2 V (shiftE (k + 1) 0 (cons x ρ)) a := by
        rw [shiftE_succ_cons]; exact ha
      rw [ihb a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
    · have ha' : AnnotOk2 V (shiftE (k + 1) 0 (cons x ρ)) a := by
        rw [shiftE_succ_cons]; exact ha
      rw [interp2_inst, shiftE_succ_cons, cons_instE]
  | pi u v A B ihA ihB =>
    intro a k ρ ha
    rw [AVExpr.inst_pi, AnnotOk2_pi, AnnotOk2_pi, ihA a k ρ ha,
      interp2_inst]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)
    have ha' : AnnotOk2 V (shiftE (k + 1) 0 (cons x ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihB a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
  | letE T v b ihT ihv ihb =>
    intro a k ρ ha
    rw [AVExpr.inst_letE, AnnotOk2_letE, AnnotOk2_letE, ihT a k ρ ha,
      ihv a k ρ ha, interp2_inst]
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    have ha' : AnnotOk2 V (shiftE (k + 1) 0
        (cons (interp2 V (instE k (interp2 V (shiftE k 0 ρ) a) ρ) v)
          ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihb a (k + 1) _ ha', shiftE_succ_cons, cons_instE]
  | eqE T x y ihT ihx ihy =>
    intro a k ρ ha
    rw [AVExpr.inst_eqE, AnnotOk2_eqE, AnnotOk2_eqE, ihx a k ρ ha,
      ihy a k ρ ha]
  | proj i e ihe =>
    intro a k ρ ha
    rw [AVExpr.inst_proj, AnnotOk2_proj, AnnotOk2_proj, ihe a k ρ ha,
      interp2_inst]
  | prf => intro a k ρ _; simp [AVExpr.inst]

/-- Substitution at the outermost binder — the β/ζ transport form. -/
theorem AnnotOk2_inst0 {e a : AVExpr} {ρ : Nat → V}
    (ha : AnnotOk2 V ρ a) :
    AnnotOk2 V ρ (e.inst a) ↔
      AnnotOk2 V (cons (interp2 V ρ a) ρ) e := by
  have h := AnnotOk2_inst V e a 0 ρ (by rwa [shiftE_zero_zero])
  rwa [shiftE_zero_zero, instE_zero] at h

/-! ### The graded β step, complete

`RedS2`'s β case in both conjuncts, at a provably-positive codomain
kind: the interp2-equality *and* the truthfulness transport, from the
subject's `AnnotOk2` alone — no argument re-check.  This is the
family-2 removal's core theorem; `Interp2/Pilot.lean`'s
`graded_beta_pos` is its value-level kernel.  At kind `0` the domain
membership is not recoverable (impredicativity — the #49/#73 residue),
which is why the runtime gate is a kind test, not a deletion. -/
theorem AnnotOk2_beta_pos {v : Nat} (hv : v ≠ 0) {A b a : AVExpr}
    {ρ : Nat → V}
    (h : AnnotOk2 V ρ (.app (.lam v A b) a)) :
    interp2 V ρ (.app (.lam v A b) a) = interp2 V ρ (b.inst a) ∧
    AnnotOk2 V ρ (b.inst a) := by
  rw [AnnotOk2_app] at h
  obtain ⟨hlam, ha, v', A', B', hslot, hmem⟩ := h
  rw [AnnotOk2_lam] at hlam
  obtain ⟨-, hbody, B, hfib, -⟩ := hlam
  -- the slot's product is in the graph regime: the λ is not `pt`
  have hv' : v' ≠ 0 := by
    intro h0
    subst h0
    have h1 := eq_pt_of_mem_piR_zero hslot
    rw [interp2_lam] at h1
    exact lamR_ne_pt hv h1
  -- rigidity pins the slot's domain to the λ's own
  have hown : interp2 V ρ (.lam v A b)
      ∈ˢ piR v (interp2 V ρ A) B := by
    rw [interp2_lam]
    exact lamR_mem hfib
  have hAA : interp2 V ρ A = A' := piR_dom_unique hv hv' hown hslot
  have haA : interp2 V ρ a ∈ˢ interp2 V ρ A := by
    rw [hAA]
    exact hmem
  refine ⟨?_, ?_⟩
  · rw [interp2_app, interp2_lam, app_lamR_pos hv haA, interp2_inst0]
  · exact (AnnotOk2_inst0 V ha).mpr (hbody _ haA)

end Setlec.SetR.Interp2
