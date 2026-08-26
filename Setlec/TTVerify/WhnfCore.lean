import Setlec.TTVerify.Claims

/-!
# `whnfCore`, clause by clause

The transpose of `Setlec/Model/Core/Whnf.lean`, against the
certificate-only claims of `Setlec/TTVerify/Claims.lean`.

`whnfCoreBody` (`Setlec/Kernel/Core.lean`) has four groups of clauses:

| clause | bridge side |
|---|---|
| leaves (`sort`, `fvar`, `forallE`, `lam`, `const`, `lit`) | the reduct *is* the subject; `Deq.refl` |
| `.app` with a λ head | `denote_beta_step` (`Setlec/TTVerify/Inst.lean`) |
| `.app` otherwise | `iotaRec`, plus `congrApp` for the head's own reduction |
| `.proj` | the structural rule, `projCert`, `projLitToCtor` |
| `.letE` | `HasType.zeta`, premise-free |

This module holds them as they are proved.  The leaves are here; the
rest is noted at the end of `Setlec/TTVerify/DESIGN.md` §7 with its
scale.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {env : Env} {fuel d : Nat}

/-! ## The leaf clauses

Six shapes that `whnfCoreBody` returns unchanged.  Each unfolding is
`rfl`: the body's clause is `pure e`, and `pure` at `Except` is `.ok`.

These are the clauses where the certificate-only shape shows its
economy — with a typing hypothesis threaded they would each have had to
carry it across, which for a subject that does not move is pure
bookkeeping. -/

@[simp] theorem whnfCore_sort (u : Level) :
    whnfCore env (fuel + 1) d (.sort u) = .ok (.sort u) := rfl

@[simp] theorem whnfCore_fvar (idx : Nat) (n : Name) (ty : Expr) :
    whnfCore env (fuel + 1) d (.fvar idx n ty) = .ok (.fvar idx n ty) := rfl

@[simp] theorem whnfCore_forallE (n : Name) (ty body : Expr)
    (bi : BinderMeta) :
    whnfCore env (fuel + 1) d (.forallE n ty body bi) =
      .ok (.forallE n ty body bi) := rfl

@[simp] theorem whnfCore_lam (n : Name) (ty body : Expr) (mb : BinderMeta) :
    whnfCore env (fuel + 1) d (.lam n ty body mb) =
      .ok (.lam n ty body mb) := rfl

@[simp] theorem whnfCore_const (n : Name) (us : List Level) :
    whnfCore env (fuel + 1) d (.const n us) = .ok (.const n us) := rfl

@[simp] theorem whnfCore_lit (l : Literal) :
    whnfCore env (fuel + 1) d (.lit l) = .ok (.lit l) := rfl

/-- The leaf clauses satisfy the `whnfCore` claim, for any denotation
and context: the reduct is the subject, so the equation is `refl` and
nothing has to be re-denoted.

Stated over the six shapes at once because that is how the eventual
`CheckStepTT` case split consumes them. -/
theorem whnfCore_leaf_claim {cval : TConstVal} {φ : Name → Nat}
    {Δ : List VExpr} {e e' : Expr} {v : VExpr}
    (hleaf : (∃ u, e = .sort u) ∨ (∃ idx n ty, e = .fvar idx n ty) ∨
      (∃ n ty body bi, e = .forallE n ty body bi) ∨
      (∃ n ty body mb, e = .lam n ty body mb) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l))
    (h : whnfCore env (fuel + 1) d e = .ok e')
    (hv : denote cval env φ d e = some v) :
    ∃ v', denote cval env φ d e' = some v' ∧ Deq Δ v v' := by
  have he : e' = e := by
    rcases hleaf with ⟨u, rfl⟩ | ⟨idx, n, ty, rfl⟩ | ⟨n, ty, body, bi, rfl⟩ |
      ⟨n, ty, body, mb, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
      simp only [whnfCore_sort, whnfCore_fvar, whnfCore_forallE,
        whnfCore_lam, whnfCore_const, whnfCore_lit, Except.ok.injEq] at h <;>
      exact h.symm
  subst he
  exact ⟨v, hv, Deq.refl⟩

end Setlec.TTVerify
