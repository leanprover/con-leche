module

public import ConLeche.Model.Inductives.BlockData
public import ConLeche.Model.Inductives.FixNoBVar
public section

/-!
# The shadow context: a recursive constructor's entries graded off the
recursive slots (task #188)

The functor of a recursive family is graded at every family `X` over
the index tuples, so a constructor's ordinary domains must be graded at
frames whose recursive slots hold an arbitrary member of `X`'s fibre —
not of the block's own.  The checker's claims grade a reading only at
frames satisfying the context it was inferred in, which pins the
recursive slots to the block's fibre (possibly empty).  What licenses
the transfer is that no ordinary domain (nor the residual) mentions a
recursive variable (`nativeOpenedOk`), so the claims' context can
be the **shadow context** `shadowCtx`: the constructor's context with
every recursive binder replaced by `Sort 0` — a context satisfied by
the point at those slots — which `CtxOk` accepts because it
constrains a context only at the leaves of the term read.  The rows
(`ClaimsAt.sortRow`) at the shadow context grade every entry, and the
residual, at every frame satisfying it (`fixShadowGrading`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The shadow context -/

/-- Binder `b` (the parameters first) is a recursive field. -/
@[expose] def recAt (nP : Nat) (ks : List RecFieldKind) (b : Nat) : Prop :=
  nP ≤ b ∧ (ks.getD (b - nP) .ordinary = .recursive ∨ ks.getD (b - nP) .ordinary = .reflexive)

instance (nP : Nat) (ks : List RecFieldKind) (b : Nat) : Decidable (recAt nP ks b) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

section Kit

variable {nP k : Nat} {ks : List RecFieldKind} {Γ : List AnnotTerm} {fvs : List Expr}

omit [SetTheory V] in
theorem mentionsFvar_false {q : Nat} {e : Expr} (h : e.mentionsFvar q = false) :
    ∀ l ∈ e.fvarLeaves, l.1 ≠ q := by
  intro l hl
  unfold Expr.mentionsFvar at h
  rw [List.any_eq_false] at h
  simpa using h l hl

end Kit

/-! ## The shadow context is a context for a leaf-free term -/

/-! ## The entries, graded at the shadow context -/

end ConLeche.Model
