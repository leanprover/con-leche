module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Subst
public import ConLeche.Model.Inductives.ErasureKit
import ConLeche.Verify.Inductives.NestCallSyn

public section

/-!
# The positivity walk's OUTPUT: syntactic lemmas

`nestPos` (`Kernel/Inductives/Positivity.lean`) returns, besides a
field's kind, the field's NORMAL FORM.  This file holds the erasure- and
occurrence-level lemmas its readings need; the output's shape is read
off the positivity DERIVATION (`PosDerivShape.lean`), and
how the normal form relates to the declared type is semantic
(`NestPosRed.lean`).
-/

namespace ConLeche.Model

open ConLeche (Env Expr Name Level NestCtx BinderMeta closeTelescope openPisAtFvars)

/-! ## Erasure-level lemmas -/

/-- The occurrence test ignores what erasure ignores. -/
theorem erasedEq_nestOcc {names : List Name} {lo hi : Nat} :
    ∀ (a b : Expr), Expr.ErasedEq a b → a.nestOcc names lo hi = b.nestOcc names lo hi := by
  intro a
  induction a with
  | bvar i => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | fvar i ty _ => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | sort u => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | const n us => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | lit l => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | app f a ihf iha =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, ihf _ h.1, iha _ h.2]
  | lam ty bd mm iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.2.1, ihb _ h.2.2]
  | forallE ty bd mm iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.2.1, ihb _ h.2.2]
  | letE ty v bd iht ihv ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.1, ihv _ h.2.1, ihb _ h.2.2]
  | proj s i e ih =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, ih _ h.2.2]

end ConLeche.Model
