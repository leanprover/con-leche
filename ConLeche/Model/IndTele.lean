module

import ConLeche.Model.Annot.Laws
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Shift
import ConLeche.Kernel.Checker
import ConLeche.Kernel.CheckerBase
public import ConLeche.Model.IndCons
import ConLeche.Semantics.DeclRun
import ConLeche.Semantics.EnvFacts
import ConLeche.Semantics.IndBlockFacts
import ConLeche.Verify.Abstract
import ConLeche.Verify.Denote.Rename
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Subst

public section

/-!
# The reading's ∀-telescope (task #161, IND TIER part 2)

`PiTeleAV`: a reading's ∀-telescope.  `denoteMeta` reads a `∀` to
`.pi 0 (pwBit φ mb.pw)`, so the reading's telescope carries *bits*, and
`PiTeleAV`'s `cons` quantifies them existentially.  Nothing downstream
reads them — the consumers are `TeleFitPA` (which quantifies its own)
and `wellDenotedV_mkAppN_of_fit` (which takes them from the grading).

`consN` names the environment a fit ends in.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## The reading's telescope -/

/-- **A reading's ∀-telescope.**  The bits are existential
(see the module docstring): a `∀` reads to `.pi 0 (pwBit φ mb.pw)` and
no consumer of this file reads either component. -/
inductive PiTeleAV : Nat → AnnotTerm → List AnnotTerm → AnnotTerm → Prop
  | nil {T : AnnotTerm} : PiTeleAV 0 T [] T
  | cons {k u v : Nat} {A B R : AnnotTerm} {Γ : List AnnotTerm} :
      PiTeleAV k B Γ R → PiTeleAV (k + 1) (.pi u v A B) (Γ ++ [A]) R

theorem PiTeleAV.length : ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm}, PiTeleAV k T Γ R → Γ.length = k := by
  intro k T Γ R h
  induction h with
  | nil => rfl
  | cons _ ih => simp [ih]

/-- A telescope of positive length exposes its head `.pi`. -/
theorem PiTeleAV.succ_inv {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm} (h : PiTeleAV (k + 1) T Γ R) :
    ∃ (u v : Nat) (A B : AnnotTerm) (Γ' : List AnnotTerm),
      T = .pi u v A B ∧ Γ = Γ' ++ [A] ∧ PiTeleAV k B Γ' R := by
  cases h with
  | cons h' => exact ⟨_, _, _, _, _, rfl, rfl, h'⟩

/-! ## The environment a fit ends in -/

/-- The environment a fit ends in: the arguments consed in order. -/
@[expose] def consN : List V → (Nat → V) → (Nat → V)
  | [], ρ => ρ
  | t :: ts, ρ => consN ts (cons t ρ)

omit [SetTheory V] in
@[simp] theorem consN_nil (ρ : Nat → V) : consN [] ρ = ρ := rfl

omit [SetTheory V] in
@[simp] theorem consN_cons (t : V) (ts : List V) (ρ : Nat → V) :
    consN (t :: ts) ρ = consN ts (cons t ρ) := rfl

omit [SetTheory V] in
/-- Above the spine `consN` is the ambient environment, shifted. -/
theorem consN_shift : ∀ (ts : List V) (ρ : Nat → V) (j : Nat),
    consN ts ρ (j + ts.length) = ρ j := by
  intro ts
  induction ts with
  | nil => intro ρ j; rfl
  | cons t tsr ih =>
    intro ρ j
    rw [consN_cons,
      show j + (t :: tsr).length = (j + 1) + tsr.length from by
        simp only [List.length_cons]; omega,
      ih (cons t ρ) (j + 1)]
    rfl

omit [SetTheory V] in
/-- `consN`'s action below the spine: index `j` names argument
`ts.length - 1 - j` (the last argument consed is `.bvar 0`). -/
theorem consN_getElem? : ∀ (ts : List V) (ρ : Nat → V) (j : Nat),
    j < ts.length → ts[ts.length - 1 - j]? = some (consN ts ρ j) := by
  intro ts
  induction ts with
  | nil => intro ρ j hj; exact absurd hj (by simp)
  | cons t tsr ih =>
    intro ρ j hj
    rw [consN_cons]
    rcases Nat.lt_or_ge j tsr.length with h | h
    · rw [show (t :: tsr).length - 1 - j = (tsr.length - 1 - j) + 1 from by
        simp only [List.length_cons]; omega,
        List.getElem?_cons_succ]
      exact ih (cons t ρ) j h
    · have hj' : j = tsr.length := by
        simp only [List.length_cons] at hj; omega
      subst hj'
      have hs := consN_shift tsr (cons t ρ) 0
      rw [Nat.zero_add] at hs
      rw [hs, show (t :: tsr).length - 1 - tsr.length = 0 from by
        simp only [List.length_cons]; omega]
      rfl

end ConLeche.Model
