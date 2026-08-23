import Setlec.Model.DirectParams
import Setlec.Model.Extend.Model

/-!
# Installing a direct simple structure into the model

`checkDirectStruct` (`Setlec/Kernel/Checker.lean`) installs, in order,
the type former's model companion, the type former, the constructor's
companion, the constructor, the recursor with its rule, and then per
field a projection companion and the projection function.  This module
supplies the model-side counterpart of each step.

The **companions** are opaque constants of the same type carrying the
same value; installing them is uniform, so it is factored out here
(`extend_direct_companion`).  They are what makes the environment
invariant's modeled-value bridges (`ModeledOk`) hold verbatim for a
directly installed block: the direct path is its own preprocessor.
-/

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-! ### The per-field universe walk -/

/-- Inversion of the field-universe walk: every field's domain was
inferred, its sort ensured, and that sort checked `≤` the structure's
result sort. -/
theorem checkDirectFieldUniv_inv {env : Env} {F : Nat} {s : Level}
    {depth nP : Nat} {fvs : List Expr} :
    ∀ (k : Nat),
      checkDirectFieldUniv (fueledOps F) env s depth nP fvs k = .ok () →
      ∀ j, j < k → ∃ fv ty u, fvs[nP + j]? = some fv ∧
        inferTypeCore env F depth (Expr.fvarTypeD fv) = .ok ty ∧
        ensureSortCore env F depth ty = .ok u ∧
        Level.leq u s = some true := by
  intro k
  induction k with
  | zero => intro _ j hj; exact absurd hj (by omega)
  | succ k ih =>
    intro h j hj
    rw [checkDirectFieldUniv] at h
    simp only [fueledOps_inferType, fueledOps_ensureSort, Bind.bind,
      Except.bind, unwrapOr] at h
    cases hfv : fvs[nP + k]? with
    | none => rw [hfv] at h; exact nomatch h
    | some fv =>
      rw [hfv] at h
      simp only [pure, Except.pure] at h
      cases hty : inferTypeCore env F depth (Expr.fvarTypeD fv) with
      | error _ => rw [hty] at h; exact nomatch h
      | ok ty =>
        rw [hty] at h
        dsimp only [] at h
        cases hu : ensureSortCore env F depth ty with
        | error _ => rw [hu] at h; exact nomatch h
        | ok u =>
          rw [hu] at h
          simp only [liftFueled] at h
          cases hle : Level.leq u s with
          | none => rw [hle] at h; exact nomatch h
          | some b =>
            rw [hle] at h
            cases b with
            | false =>
              simp only [pure, Except.pure, Bool.false_eq_true, if_false,
                throw, throwThe, MonadExceptOf.throw] at h
              exact nomatch h
            | true =>
              simp only [pure, Except.pure, if_true] at h
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
              · exact ih h j hj'
              · exact ⟨fv, ty, u, hfv, hty, hu, hle⟩

/-- Install a direct block's **model companion**: an opaque constant of
a given type carrying a given value.  An `axiomInfo` triggers none of
the inductive-kind obligations, so the only real inputs are the type's
syntactic well-formedness, the key membership, and the value's
level-parameter extensionality. -/
theorem extend_direct_companion {env : Env} (m : EnvModel V env)
    {n : Name} {lps : List Name} {ty : Expr} {v₀ : (Name → Nat) → V}
    (hfind' : env.find? n = none)
    (hnempty : n ≠ emptyName)
    (htf : ty.hasFvar = false)
    (htp : ty.allLevelParamsDefined lps = true)
    (htr : ty.constsResolve env = true)
    (htb : ty.looseBVarsBounded 0 = true)
    (hkey : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m.val env ψ ty = some T ∧ v₀ ψ ∈ˢ T)
    (hparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ lps, ψ₁ p = ψ₂ p) → v₀ ψ₁ = v₀ ψ₂)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) ty) :
    ∃ m' : EnvModel V ⟨.axiomInfo ⟨n, lps, ty⟩ :: env.consts⟩,
      (∀ ψ, m'.val n ψ = v₀ ψ) ∧
      (∀ n' ψ, n' ≠ n → m'.val n' ψ = m.val n' ψ) := by
  have hwf : ConstWF ⟨ConstantInfo.axiomInfo ⟨n, lps, ty⟩ :: env.consts⟩
      (.axiomInfo ⟨n, lps, ty⟩) := by
    refine ⟨htf, htp, Expr.constsResolve_mono htr, htb, ?_, ?_, ?_⟩
    · intro _ _ _ heq; exact nomatch heq
    · intro _ _ _ _ heq; exact nomatch heq
    · intro _ _ heq; exact nomatch heq
  exact extend_fresh m (.axiomInfo ⟨n, lps, ty⟩) v₀ hfind' hwf htr
    (fun _ _ _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq)
    hkey hparams hAty
    (fun _ _ heq => nomatch heq)
    (fun _ _ _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq)
    (fun heq => absurd heq hnempty)
    (fun hb _ => by simp [ConstantInfo.isBasis] at hb)
    (fun _ _ _ _ heq => nomatch heq)
    (fun _ _ _ _ _ _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq)
    (fun _ hk => by
      rcases hk with ⟨_, _, heq⟩ | ⟨_, _, _, heq⟩ <;> exact nomatch heq)
    (fun _ _ _ _ _ _ _ heq => nomatch heq)
    (fun _ heq _ => nomatch heq)
    (fun _ _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq)
    (fun _ _ _ _ _ _ heq => nomatch heq)
    (fun _ _ _ _ _ _ heq => nomatch heq)

end Setlec
