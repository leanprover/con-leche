import Lech.Verify.Denote.SubstAlgebra

/-!
# The context-transformation relations

`LiftCtx` and `InstCtx` — inserting binders into a context and
substituting one away — in the style of lean4lean's
`Ctx.LiftN`/`Ctx.InstN`: under a binder the cut grows by one and the
binder's own type is transformed at the old cut, which is exactly what
the relations' `succ` constructors record.  With them, the four
`getElem?` lemmas that say what each relation does to a variable
lookup.

**What this file used to also hold.**  The two derivation-level lemmas
they were generalized for — `HasType.weakenN`/`weakenHead` and
`HasType.instN`/`instantiate`, one induction over the derivation each —
were the declarative lane's substitution metatheory.  That lane was
retired (task #148 T7b) and the set route weakens its own relation
family instead (`Lech/SetBase/Weaken.lean`, which is why it imports this
file), so the four theorems had no consumer left and went with it.  The
relations stayed: they are `HasType`-free, and `Lech/SetBase/Weaken.lean`
is built on `LiftCtx` directly.

*The cost accounting the deleted half carried is worth keeping in one
sentence, because it is the only measured estimate of a job of that
shape: an independent review priced the substitution algebra at 15–25
lemmas and it landed at 19, with no Church-Rosser, no unique typing and
no normalization — and the non-obvious half was that **weakening is as
expensive as substitution**, because several rules embed lifts in their
own statements (`natStepT`, `quotInvT`, `arrow`, `relT`, `eta`), so the
full commutation kit is needed already for the weakening lemma.*
-/
namespace Lech.TT

open VExpr

/-! ## The context transformations -/

/-- `LiftCtx n k Γ Γ'`: the context `Γ'` is `Γ` with `n` new entries
inserted at position `k`; the `k` entries below the insertion point are
lifted, each at its own depth.  (Transpose of lean4lean's
`Ctx.LiftN`.) -/
inductive LiftCtx (n : Nat) : Nat → List VExpr → List VExpr → Prop where
  | zero (As : List VExpr) {Γ : List VExpr} (h : As.length = n) :
      LiftCtx n 0 Γ (As ++ Γ)
  | succ {k : Nat} {Γ Γ' : List VExpr} (A : VExpr) :
      LiftCtx n k Γ Γ' → LiftCtx n (k + 1) (A :: Γ) (A.liftN n k :: Γ')

/-- `InstCtx Γ₀ v A₀ k Γ Γ'`: the context `Γ` is `Γ'` with an entry
`A₀` inserted at position `k` (so `Γ'` ends in `Γ₀`, the context that
types the substituted value `v`); the `k` entries below the cut are
instantiated, each at its own depth. -/
inductive InstCtx (Γ₀ : List VExpr) (v A₀ : VExpr) :
    Nat → List VExpr → List VExpr → Prop where
  | zero : InstCtx Γ₀ v A₀ 0 (A₀ :: Γ₀) Γ₀
  | succ {k : Nat} {Γ Γ' : List VExpr} (B : VExpr) :
      InstCtx Γ₀ v A₀ k Γ Γ' →
      InstCtx Γ₀ v A₀ (k + 1) (B :: Γ) (B.inst v k :: Γ')

/-- Below the cut, lookups answer with a lift at the entry's own
depth. -/
theorem LiftCtx.getElem?_lt {n k : Nat} {Γ Γ' : List VExpr}
    (H : LiftCtx n k Γ Γ') {i : Nat} {A : VExpr} (hik : i < k)
    (h : Γ[i]? = some A) : Γ'[i]? = some (A.liftN n (k - 1 - i)) := by
  induction H generalizing i with
  | zero As hAs => omega
  | @succ k Γ Γ' B H ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      cases h
      rw [List.getElem?_cons_zero, show k + 1 - 1 - 0 = k by omega]
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      rw [List.getElem?_cons_succ, show k + 1 - 1 - (i + 1) = k - 1 - i by omega]
      exact ih (by omega) h

/-- At or above the cut, lookups answer unchanged, `n` places later. -/
theorem LiftCtx.getElem?_ge {n k : Nat} {Γ Γ' : List VExpr}
    (H : LiftCtx n k Γ Γ') {i : Nat} {A : VExpr} (hik : k ≤ i)
    (h : Γ[i]? = some A) : Γ'[i + n]? = some A := by
  induction H generalizing i with
  | @zero As Γ hAs =>
    rw [List.getElem?_append_right (by omega),
      show i + n - As.length = i by omega]
    exact h
  | @succ k Γ Γ' B H ih =>
    cases i with
    | zero => omega
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      rw [show i + 1 + n = i + n + 1 by omega, List.getElem?_cons_succ]
      exact ih (by omega) h

/-- Below the cut, lookups answer with an instantiation at the entry's
own depth. -/
theorem InstCtx.getElem?_lt {Γ₀ : List VExpr} {v A₀ : VExpr} {k : Nat}
    {Γ Γ' : List VExpr} (H : InstCtx Γ₀ v A₀ k Γ Γ') {i : Nat} {A : VExpr}
    (hik : i < k) (h : Γ[i]? = some A) :
    Γ'[i]? = some (A.inst v (k - 1 - i)) := by
  induction H generalizing i with
  | zero => omega
  | @succ k Γ Γ' B H ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      cases h
      rw [List.getElem?_cons_zero, show k + 1 - 1 - 0 = k by omega]
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      rw [List.getElem?_cons_succ, show k + 1 - 1 - (i + 1) = k - 1 - i by omega]
      exact ih (by omega) h

/-- At the cut sits the type of the substituted value. -/
theorem InstCtx.getElem?_eq {Γ₀ : List VExpr} {v A₀ : VExpr} {k : Nat}
    {Γ Γ' : List VExpr} (H : InstCtx Γ₀ v A₀ k Γ Γ') : Γ[k]? = some A₀ := by
  induction H with
  | zero => rfl
  | succ B H ih => exact ih

/-- Above the cut, lookups answer unchanged, one place earlier. -/
theorem InstCtx.getElem?_gt {Γ₀ : List VExpr} {v A₀ : VExpr} {k : Nat}
    {Γ Γ' : List VExpr} (H : InstCtx Γ₀ v A₀ k Γ Γ') {i : Nat} {A : VExpr}
    (hik : k < i) (h : Γ[i]? = some A) : Γ'[i - 1]? = some A := by
  induction H generalizing i with
  | zero =>
    cases i with
    | zero => omega
    | succ i => rw [List.getElem?_cons_succ] at h; exact h
  | @succ k Γ Γ' B H ih =>
    cases i with
    | zero => omega
    | succ i =>
      cases i with
      | zero => omega
      | succ i =>
        rw [List.getElem?_cons_succ] at h
        rw [show i + 1 + 1 - 1 = (i + 1 - 1) + 1 by omega,
          List.getElem?_cons_succ]
        exact ih (by omega) h

/-- The instantiated part of an `InstCtx` context is a plain prefix
over `Γ₀`: forgetting what the entries are gives a head insertion. -/
theorem InstCtx.toLiftCtx {Γ₀ : List VExpr} {v A₀ : VExpr} {k : Nat}
    {Γ Γ' : List VExpr} (H : InstCtx Γ₀ v A₀ k Γ Γ') :
    LiftCtx k 0 Γ₀ Γ' := by
  induction H with
  | zero => exact .zero [] rfl
  | @succ k Γ Γ' B H ih =>
    cases ih with
    | zero As hAs => exact .zero (B.inst v k :: As) (by simp [hAs])

end Lech.TT
