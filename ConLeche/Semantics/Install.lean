module

public import ConLeche.Semantics.Canon
import ConLeche.Semantics.WellDenoted
import ConLeche.Verify.EnvGuards
public import ConLeche.Verify.Denote.Install

@[expose] public section

/-!
# The `acval` install algebra — the install tier's V-free half

The one theorem that mentions `V` (`acvalWith_wellDenoted`) takes
`WellDenoted` as a hypothesis and returns it.

The `EnvModel` install keys are **six syntactic fields and two semantic
ones**: `acval` (data), `acval_erase`, `acval_closed`,
`acval_params`, `acval_defn` and `acval_thm` mention no
`V` at all, while only `acval_wellDenoted` and `mem_type2` do.  So the first
thing the install tier needs is not semantics — it is the *algebra*
of extending a canonical annotated valuation at one fresh name, and
the fact that extending it there moves nothing already denoted.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name natLitSupported strLitSupported)

universe w

/-! ## The one-name update -/

/-- Extend a canonical annotated valuation at one name. -/
def acvalWith (acval : Name → (Name → Nat) → AnnotTerm) (n : Name)
    (A : (Name → Nat) → AnnotTerm) : Name → (Name → Nat) → AnnotTerm :=
  fun c ψ => if c = n then A ψ else acval c ψ

theorem acvalWith_ne {acval : Name → (Name → Nat) → AnnotTerm}
    {n : Name} {A : (Name → Nat) → AnnotTerm} {c : Name} (h : c ≠ n) :
    acvalWith acval n A c = acval c := by
  funext ψ; simp [acvalWith, h]

theorem acvalWith_self {acval : Name → (Name → Nat) → AnnotTerm}
    {n : Name} {A : (Name → Nat) → AnnotTerm} :
    acvalWith acval n A n = A := by
  funext ψ; simp [acvalWith]

/-! ## The three syntactic fields, transported

`acval_erase`, `acval_closed` and `acval_params` are conditions on an
install-fixed object with no `interp` in them (the
`EnvModel` docstrings say so of the last two).  Each therefore extends by
a case split on the updated name and nothing else. -/

/-- `acval_closed` extends. -/
theorem acvalWith_closed {acval : Name → (Name → Nat) → AnnotTerm}
    {n : Name} {A : (Name → Nat) → AnnotTerm}
    (h : ∀ (m : Name) (ψ : Name → Nat) (k : Nat),
      (acval m ψ).liftN 1 k = acval m ψ)
    (hA : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ) :
    ∀ (m : Name) (ψ : Name → Nat) (k : Nat),
      (acvalWith acval n A m ψ).liftN 1 k
        = acvalWith acval n A m ψ := by
  intro m ψ k
  by_cases hm : m = n
  · subst hm
    rw [acvalWith_self]
    exact hA ψ k
  · rw [acvalWith_ne hm]
    exact h m ψ k

/-- `acval_params` extends across a `cons`: the stored entries are the
old ones plus the installed one, and the new leaf answers for itself.

Note the environment moves here, unlike in the two above — the field
is indexed by `env.find?`.  Freshness is **not** needed: the `cons`
shadows, so the installed entry answers first either way. -/
theorem acvalWith_params {acval : Name → (Name → Nat) → AnnotTerm}
    {env : Env} {c₀ : ConLeche.ConstantInfo}
    {A : (Name → Nat) → AnnotTerm}
    (h : ∀ (m : Name) (ci : ConLeche.ConstantInfo),
      env.find? m = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acval m ψ₁ = acval m ψ₂)
    (hA : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂) :
    ∀ (m : Name) (ci : ConLeche.ConstantInfo),
      (⟨c₀ :: env.consts⟩ : Env).find? m = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acvalWith acval c₀.name A m ψ₁
          = acvalWith acval c₀.name A m ψ₂ := by
  intro m ci hf ψ₁ ψ₂ hp
  rw [Env.find?_cons] at hf
  by_cases hm : c₀.name = m
  · rw [if_pos hm] at hf
    obtain rfl := Option.some.inj hf
    subst hm
    rw [acvalWith_self]
    exact hA ψ₁ ψ₂ hp
  · rw [if_neg hm] at hf
    rw [acvalWith_ne (fun hh => hm hh.symm)]
    exact h m ci hf ψ₁ ψ₂ hp

/-! ## The one semantic field that extends for free

`acval_wellDenoted` is one of the two `EnvModel` fields that mention `V` at all,
and it is the one that carries no environment index: it is a fact
about each leaf on its own.  So its extension asks the install for
exactly the new leaf's truthfulness and nothing more.

Its partner `mem_type2` does **not** extend here, and the reason is
worth the contrast: `mem_type2` conditions on a reading of the
constant's *type* **in the extended environment**, so its transport
needs the run-stability fact this file names as missing, not a case
split. -/

/-- `acval_wellDenoted` extends. -/
theorem acvalWith_wellDenoted {V : Type w} [SetTheory V]
    {acval : Name → (Name → Nat) → AnnotTerm} {n : Name}
    {A : (Name → Nat) → AnnotTerm}
    (h : ∀ (m : Name) (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (acval m ψ))
    (hA : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ)) :
    ∀ (m : Name) (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (acvalWith acval n A m ψ) := by
  intro m ψ ρ
  by_cases hm : m = n
  · subst hm
    rw [acvalWith_self]
    exact hA ψ ρ
  · rw [acvalWith_ne hm]
    exact h m ψ ρ

end ConLeche.Semantics
