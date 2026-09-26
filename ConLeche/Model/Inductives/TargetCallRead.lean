module

public import ConLeche.Model.Inductives.TargetNodeRead
public import ConLeche.Model.Annot.BitSubstFvars
public import ConLeche.Semantics.NoBVar
public import ConLeche.Model.Inductives.NestPosMono
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Inductives.PosFieldLeaf
import ConLeche.Verify.Shift
import ConLeche.Verify.Subst
import ConLeche.Semantics.SubstAV

public section

/-!
# A call's readings through the walk's substitution (lane NESTIND, session 27)

The call's tie (`callTie`, `TargetCallTie.lean`) says, syntactically, that
the callee's telescope and major are the walk's field telescope and leaf
under ONE parallel substitution of the walk's variables (`substFvars`).
This file reads that at the rule's frame: the call's telescope, read at the
rule's depth (`teleDoms`), is the walk's read at the walk's depth and
substituted (`teleDoms_substFvars`), and a spine fits the first at a
valuation exactly when it fits the second at the substituted valuation
(`spineFit_substAt`).  Hole-free readings do not see the holes' values
(`interp_congr_holeFree`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A list substituted at rising cut-offs -/

/-- Entry `l` substituted at the cut `k + l` — a telescope's domains
through a parallel substitution. -/
@[expose] def substAt (τ : Nat → AnnotTerm) : Nat → List AnnotTerm → List AnnotTerm
  | _, [] => []
  | k, a :: as => AnnotTerm.substAV τ a k :: substAt τ (k + 1) as

theorem substAt_length (τ : Nat → AnnotTerm) :
    ∀ (k : Nat) (as : List AnnotTerm), (substAt τ k as).length = as.length
  | _, [] => rfl
  | k, _ :: as => by simp [substAt, substAt_length τ (k + 1) as]

/-- **A spine fits substituted domains exactly when it fits the domains at
the substituted valuation.** -/
theorem spineFit_substAt (τ : Nat → AnnotTerm) :
    ∀ (as : List AnnotTerm) (k : Nat) (σ : Nat → V) (bs : List V),
      SpineFit σ (substAt τ k as) bs ↔ SpineFit (substE V τ k σ) as bs
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | a :: as, k, σ, b :: bs => by
    simp only [substAt, SpineFit, interp_substAV]
    rw [cons_substE]
    exact and_congr Iff.rfl (spineFit_substAt τ as (k + 1) (cons b σ) bs)

/-! ## `fvarsBelow` through an opening -/

theorem fvarsBelow_instantiateList {D : Nat} :
    ∀ (os : List Expr), (∀ x ∈ os, Expr.fvarsBelow D x) →
      ∀ (e : Expr) (k : Nat), Expr.fvarsBelow D e → Expr.fvarsBelow D (e.instantiateList os k)
  | [], _, e, k, h => by rw [Expr.instantiateList_nil]; exact h
  | v :: vs, hos, e, k, h => by
    rw [Expr.instantiateList_cons]
    exact Expr.fvarsBelow_instantiate1_gen (hos v List.mem_cons_self) k
      (fvarsBelow_instantiateList vs (fun x hx => hos x (List.mem_cons_of_mem _ hx)) e (k + 1) h)

theorem LocList.fvarsBelow {B q : Nat} {os : List Expr} (h : LocList B q os) :
    ∀ x ∈ os, Expr.fvarsBelow (B + q) x := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨ty, hty⟩ := h.2 j (by rw [← h.1]; exact hj)
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hty
  rw [hty]
  show B + q - 1 - j < B + q
  have := h.1; omega

/-! ## A telescope read through a parallel substitution -/

variable {env : Env} {φ : Name → Nat}

/-- **A telescope erasure-equal to a substituted one reads as the
substituted reading**: opened at the rule's variables above `B`, entry
`l` reads as the walk's entry, opened at the walk's variables above `b`,
substituted at the cut `q + l`. -/
theorem teleDoms_substFvars (m : EnvModel V env) {b B : Nat} {s : Nat → Expr}
    {x : Nat → AnnotTerm}
    (hs : ∀ i, i < b → Expr.WScoped B (s i) ∧ (s i).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env φ B (s i) = some (x i)) :
    ∀ (tysR tysW : List Expr) (q : Nat) (osR osW : List Expr), LocList B q osR → LocList b q osW →
      tysR.length = tysW.length →
      (∀ (l : Nat) (tR tW : Expr), tysR[l]? = some tR → tysW[l]? = some tW →
        Expr.ErasedEq tR (Expr.substFvars b B s tW)) →
      (∀ tW ∈ tysW, Expr.fvarsBelow b tW) →
      teleDoms m.acval env φ B osR tysR
        = (teleDoms m.acval env φ b osW tysW).map (substAt (substTau b B x) q)
  | [], [], _, _, _, _, _, _, _, _ => by simp [teleDoms, substAt]
  | [], _ :: _, _, _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _, _ => by simp at hl
  | tR :: tysR, tW :: tysW, q, osR, osW, hR, hW, hl, hE, hfb => by
    have hq1 : osR.length = q := hR.1
    have hq2 : osW.length = q := hW.1
    have hsb : ∀ v, v < b → (s v).looseBVarsBounded 0 = true := fun v hv => (hs v hv).2.1
    -- the head entry
    have hE0 : Expr.ErasedEq (tR.instantiateList osR 0)
        (Expr.substFvars b B s (tW.instantiateList osW 0)) :=
      (erasedEq_instantiateList osR 0 (hE 0 tR tW rfl rfl)).trans
        (Expr.substFvars_instantiateList hsb q osW osR hq2 hq1
          (fun j hj => by
            obtain ⟨ty, h1⟩ := hW.2 j hj
            obtain ⟨ty', h2⟩ := hR.2 j hj
            exact ⟨ty, ty', h1, h2⟩) tW 0)
    have hfbW : Expr.fvarsBelow (b + q) (tW.instantiateList osW 0) :=
      fvarsBelow_instantiateList osW (by simpa using hW.fvarsBelow) tW 0
        (Expr.fvarsBelow_mono (Nat.le_add_right b q) (hfb tW List.mem_cons_self))
    have hread : denoteMeta m.acval env φ (B + q) (tR.instantiateList osR 0)
        = (denoteMeta m.acval env φ (b + q) (tW.instantiateList osW 0)).map
            (AnnotTerm.substAV (substTau b B x) · q) := by
      rw [denoteMeta_erasedEq hE0]
      exact denoteMeta_substFvars m hs _ q hfbW
    -- the rest, one binder down
    have ih := teleDoms_substFvars m hs tysR tysW (q + 1)
      (.fvar (B + q) (tR.instantiateList osR 0) :: osR)
      (.fvar (b + q) (tW.instantiateList osW 0) :: osW) (hR.cons _) (hW.cons _)
      (by simpa using hl) (fun l t1 t2 h1 h2 => hE (l + 1) t1 t2 (by simpa using h1)
        (by simpa using h2)) (fun t ht => hfb t (List.mem_cons_of_mem _ ht))
    simp only [teleDoms, hq1, hq2]
    rw [hread, ih]
    cases denoteMeta m.acval env φ (b + q) (tW.instantiateList osW 0) with
    | none => rfl
    | some a =>
      cases teleDoms m.acval env φ b (.fvar (b + q) (tW.instantiateList osW 0) :: osW) tysW with
      | none => rfl
      | some r => rfl

/-! ## Hole-free readings do not see the holes -/

theorem NoBVar.or :
    ∀ {e : AnnotTerm} {P Q : Nat → Prop}, NoBVar P e → NoBVar Q e →
      NoBVar (fun i => P i ∨ Q i) e := by
  intro e
  induction e with
  | bvar i =>
    intro P Q h1 h2 h
    rcases h with h | h
    · exact h1 h
    · exact h2 h
  | sort u => intros; trivial
  | const c us => intros; trivial
  | prf => intros; trivial
  | app f a ihf iha => intro P Q h1 h2; exact ⟨ihf h1.1 h2.1, iha h1.2 h2.2⟩
  | lam v A b ihA ihb =>
    intro P Q h1 h2
    refine ⟨ihA h1.1 h2.1, ?_⟩
    have := ihb h1.2 h2.2
    refine NoBVar.mono (fun i hi => ?_) this
    cases i with
    | zero => exact hi.elim
    | succ i => exact hi
  | pi u v A B ihA ihB =>
    intro P Q h1 h2
    refine ⟨ihA h1.1 h2.1, ?_⟩
    have := ihB h1.2 h2.2
    refine NoBVar.mono (fun i hi => ?_) this
    cases i with
    | zero => exact hi.elim
    | succ i => exact hi
  | eqE a b iha ihb => intro P Q h1 h2; exact ⟨iha h1.1 h2.1, ihb h1.2 h2.2⟩
  | fst e ih => intro P Q h1 h2; exact ih h1 h2
  | snd e ih => intro P Q h1 h2; exact ih h1 h2

/-- **A term reads alike at two valuations agreeing off `P` below its
scope.** -/
theorem interp_congr_offBelow {e : AnnotTerm} {P : Nat → Prop} {D : Nat} (hP : NoBVar P e)
    (hD : Term.bvarsBelow D e.erase) {σ σ' : Nat → V} (h : ∀ j, j < D → ¬ P j → σ j = σ' j) :
    interp V σ e = interp V σ' e := by
  have hD' : NoBVar (fun j => D ≤ j) e := NoBVar_of_bvarsBelow hD fun _ h => h
  refine interp_congr_noBVar e (NoBVar.or hP hD') fun j hj => ?_
  simp only [not_or] at hj
  exact h j (by omega) hj.1

end ConLeche.Model
