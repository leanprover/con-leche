import Lech.Semantics.Ok2
import Lech.Verify.Denote.VClosed

/-!
# Terms that do not mention certain variables (task #188)

`NoBVar P e`: no de Bruijn variable whose index satisfies `P` occurs
in `e` (`P` shifted under each binder).  Its consequence — the one the
recursive route needs — is that the interpretation and the grading of
such a term do not depend on the frame's values at those indices
(`interp2_congr_noBVar`, `AnnotOk2_congr_noBVar`): the constructor
tower functor of a recursive type is spelled over the field chains
with the recursive slots reading an arbitrary set `X`, while the
ordinary domains' grading was established at a frame whose recursive
slots hold the proof point (the constructors are read at a dummy
former whose carrier is `PUnit`); the ordinary domains do not mention
the recursive slots (a kernel guard, `directUsedLater`), so the
grading transfers.
-/

namespace Lech.Semantics
open Lech.SetModel

open SetTheory
open Lech.VExpr (VExpr)

universe w

variable {V : Type w} [SetTheory V]

/-- The index set `P` seen under one more binder. -/
def shiftP (P : Nat → Prop) : Nat → Prop
  | 0 => False
  | i + 1 => P i

/-- No variable whose index satisfies `P` occurs in the term. -/
def NoBVar (P : Nat → Prop) : AVExpr → Prop
  | .bvar i => ¬ P i
  | .sort _ => True
  | .const _ _ => True
  | .prf => True
  | .app f a => NoBVar P f ∧ NoBVar P a
  | .lam _ A b => NoBVar P A ∧ NoBVar (shiftP P) b
  | .pi _ _ A B => NoBVar P A ∧ NoBVar (shiftP P) B
  | .letE T v b => NoBVar P T ∧ NoBVar P v ∧ NoBVar (shiftP P) b
  | .eqE T a b => NoBVar P T ∧ NoBVar P a ∧ NoBVar P b
  | .proj _ e => NoBVar P e

/-- Two frames agreeing off `P`. -/
def AgreeOff (P : Nat → Prop) (σ σ' : Nat → V) : Prop := ∀ i, ¬ P i → σ i = σ' i

omit [SetTheory V] in
theorem agreeOff_cons {P : Nat → Prop} {σ σ' : Nat → V} (h : AgreeOff P σ σ') (x : V) :
    AgreeOff (shiftP P) (cons x σ) (cons x σ') := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i => exact h i hi

omit [SetTheory V] in
theorem agreeOff_cons_of {P : Nat → Prop} {σ σ' : Nat → V} (h : AgreeOff P σ σ') {x x' : V}
    (hx : x = x') : AgreeOff (shiftP P) (cons x σ) (cons x' σ') := by
  subst hx; exact agreeOff_cons h x

/-- **The interpretation of a term ignores the variables it does not
mention.** -/
theorem interp2_congr_noBVar :
    ∀ (e : AVExpr) {P : Nat → Prop} {σ σ' : Nat → V},
      NoBVar P e → AgreeOff P σ σ' → interp2 V σ e = interp2 V σ' e := by
  intro e
  induction e with
  | bvar i => intro P σ σ' h hag; exact hag i h
  | sort u => intros; rfl
  | const c us => intros; rfl
  | app f a ihf iha =>
    intro P σ σ' h hag
    simp only [interp2_app, ihf h.1 hag, iha h.2 hag]
  | lam v A b ihA ihb =>
    intro P σ σ' h hag
    simp only [interp2_lam, ihA h.1 hag]
    congr 1
    funext x
    exact ihb h.2 (agreeOff_cons hag x)
  | pi u v A B ihA ihB =>
    intro P σ σ' h hag
    simp only [interp2_pi, ihA h.1 hag]
    congr 1
    funext x
    exact ihB h.2 (agreeOff_cons hag x)
  | letE T e b ihT ihe ihb =>
    intro P σ σ' h hag
    simp only [interp2_letE]
    rw [ihe h.2.1 hag]
    exact ihb h.2.2 (agreeOff_cons hag _)
  | eqE T a b ihT iha ihb =>
    intro P σ σ' h hag
    simp only [interp2_eqE, iha h.2.1 hag, ihb h.2.2 hag]
  | proj i e ihe =>
    intro P σ σ' h hag
    simp only [interp2_proj, ihe h hag]
  | prf => intros; rfl

/-- **The grading of a term ignores the variables it does not
mention.** -/
theorem AnnotOk2_congr_noBVar :
    ∀ (e : AVExpr) {P : Nat → Prop} {σ σ' : Nat → V},
      NoBVar P e → AgreeOff P σ σ' → (AnnotOk2 V σ e ↔ AnnotOk2 V σ' e) := by
  intro e
  induction e with
  | bvar i => intros; simp
  | sort u => intros; simp
  | const c us => intros; simp
  | app f a ihf iha =>
    intro P σ σ' h hag
    rw [AnnotOk2_app, AnnotOk2_app, ihf h.1 hag, iha h.2 hag,
      interp2_congr_noBVar f h.1 hag, interp2_congr_noBVar a h.2 hag]
  | lam v A b ihA ihb =>
    intro P σ σ' h hag
    rw [AnnotOk2_lam, AnnotOk2_lam, ihA h.1 hag, interp2_congr_noBVar A h.1 hag]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihb h.2 (agreeOff_cons hag x)))
      (exists_congr fun B => and_congr
        (forall_congr' fun x => imp_congr Iff.rfl ?_) Iff.rfl))
    rw [interp2_congr_noBVar b h.2 (agreeOff_cons hag x)]
  | pi u v A B ihA ihB =>
    intro P σ σ' h hag
    rw [AnnotOk2_pi, AnnotOk2_pi, ihA h.1 hag, interp2_congr_noBVar A h.1 hag]
    exact and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl (ihB h.2 (agreeOff_cons hag x)))
  | letE T v b ihT ihv ihb =>
    intro P σ σ' h hag
    rw [AnnotOk2_letE, AnnotOk2_letE, ihT h.1 hag, ihv h.2.1 hag,
      ihb h.2.2 (agreeOff_cons_of hag (interp2_congr_noBVar v h.2.1 hag))]
  | eqE T a b ihT iha ihb =>
    intro P σ σ' h hag
    rw [AnnotOk2_eqE, AnnotOk2_eqE, iha h.2.1 hag, ihb h.2.2 hag]
  | proj i e ihe =>
    intro P σ σ' h hag
    rw [AnnotOk2_proj, AnnotOk2_proj, ihe h hag, interp2_congr_noBVar e h hag]
  | prf => intros; simp

omit [SetTheory V] in
theorem shiftP_mono {P Q : Nat → Prop} (h : ∀ i, Q i → P i) : ∀ i, shiftP Q i → shiftP P i
  | 0, hi => hi.elim
  | i + 1, hi => h i hi

omit [SetTheory V] in
theorem NoBVar.mono :
    ∀ {e : AVExpr} {P Q : Nat → Prop}, (∀ i, Q i → P i) → NoBVar P e → NoBVar Q e := by
  intro e
  induction e with
  | bvar i => intro P Q h h'; exact fun hq => h' (h i hq)
  | sort u => intros; trivial
  | const c us => intros; trivial
  | app f a ihf iha => intro P Q h h'; exact ⟨ihf h h'.1, iha h h'.2⟩
  | lam v A b ihA ihb => intro P Q h h'; exact ⟨ihA h h'.1, ihb (shiftP_mono h) h'.2⟩
  | pi u v A B ihA ihB => intro P Q h h'; exact ⟨ihA h h'.1, ihB (shiftP_mono h) h'.2⟩
  | letE T v b ihT ihv ihb =>
    intro P Q h h'
    exact ⟨ihT h h'.1, ihv h h'.2.1, ihb (shiftP_mono h) h'.2.2⟩
  | eqE T a b ihT iha ihb => intro P Q h h'; exact ⟨ihT h h'.1, iha h h'.2.1, ihb h h'.2.2⟩
  | proj i e ihe => intro P Q h h'; exact ihe h h'
  | prf => intros; trivial

omit [SetTheory V] in
/-- A term bounded below `k` mentions no variable at or above `k`. -/
theorem NoBVar_of_bvarsBelow :
    ∀ {e : AVExpr} {k : Nat} {P : Nat → Prop}, VExpr.bvarsBelow k e.erase →
      (∀ i, P i → k ≤ i) → NoBVar P e := by
  intro e
  induction e with
  | bvar i =>
    intro k P h hP
    show ¬ P i
    intro hi
    have := hP i hi
    have h' : i < k := h
    omega
  | sort u => intros; trivial
  | const c us => intros; trivial
  | app f a ihf iha => intro k P h hP; exact ⟨ihf h.1 hP, iha h.2 hP⟩
  | lam v A b ihA ihb =>
    intro k P h hP
    refine ⟨ihA h.1 hP, ihb (k := k + 1) h.2 ?_⟩
    intro i hi
    cases i with
    | zero => exact hi.elim
    | succ i => exact Nat.succ_le_succ (hP i hi)
  | pi u v A B ihA ihB =>
    intro k P h hP
    refine ⟨ihA h.1 hP, ihB (k := k + 1) h.2 ?_⟩
    intro i hi
    cases i with
    | zero => exact hi.elim
    | succ i => exact Nat.succ_le_succ (hP i hi)
  | letE T v b ihT ihv ihb =>
    intro k P h hP
    refine ⟨ihT h.1 hP, ihv h.2.1 hP, ihb (k := k + 1) h.2.2 ?_⟩
    intro i hi
    cases i with
    | zero => exact hi.elim
    | succ i => exact Nat.succ_le_succ (hP i hi)
  | eqE T a b ihT iha ihb =>
    intro k P h hP
    exact ⟨ihT h.1 hP, iha h.2.1 hP, ihb h.2.2 hP⟩
  | proj i e ihe => intro k P h hP; exact ihe h hP
  | prf => intros; trivial

omit [SetTheory V] in
/-- Lifting at a cutoff never introduces the inserted variables. -/
theorem NoBVar_liftN (n : Nat) :
    ∀ (e : AVExpr) (k : Nat) {P : Nat → Prop},
      (∀ i, P i → k ≤ i ∧ i < k + n) → NoBVar P (e.liftN n k) := by
  intro e
  induction e with
  | bvar i =>
    intro k P hP
    show ¬ P (if i < k then i else i + n)
    intro h
    split at h
    · have := hP _ h; omega
    · have := hP _ h; omega
  | sort u => intros; trivial
  | const c us => intros; trivial
  | app f a ihf iha => intro k P hP; exact ⟨ihf k hP, iha k hP⟩
  | lam v A b ihA ihb =>
    intro k P hP
    refine ⟨ihA k hP, ihb (k + 1) ?_⟩
    intro i hi
    cases i with
    | zero => exact hi.elim
    | succ i => have := hP i hi; omega
  | pi u v A B ihA ihB =>
    intro k P hP
    refine ⟨ihA k hP, ihB (k + 1) ?_⟩
    intro i hi
    cases i with
    | zero => exact hi.elim
    | succ i => have := hP i hi; omega
  | letE T v b ihT ihv ihb =>
    intro k P hP
    refine ⟨ihT k hP, ihv k hP, ihb (k + 1) ?_⟩
    intro i hi
    cases i with
    | zero => exact hi.elim
    | succ i => have := hP i hi; omega
  | eqE T a b ihT iha ihb => intro k P hP; exact ⟨ihT k hP, iha k hP, ihb k hP⟩
  | proj i e ihe => intro k P hP; exact ihe k hP
  | prf => intros; trivial

end Lech.Semantics
