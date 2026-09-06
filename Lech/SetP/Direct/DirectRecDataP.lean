import Lech.SetP.Direct.DirectStageCtorP

/-!
# The recursor's data (task #175 W4c, P3 module 6, part 7; S2)

`RecData`: the recursor type's reading, peeled — the Π-tower over
`nP + 3` binder data (parameters, motive, minor, major) ending in the
motive applied to the major (`.app (.bvar 2) (.bvar 0)`), with every
codomain bit zero exactly when the elimination level is (`elimLevel`:
the fresh parameter of the large eliminator, `zero` for the small
one), graded, bounded, depending only on the recursor's level
parameters.  Since task #175 S2 the stored recursor is the
*generated* one, so the data is read off syntactically
(`recData_of`, `Lech/SetP/Direct/DirectRecReadP.lean`); the record
is crossed to the recursor's own extension by `RecData.cross`.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- The recursor's elimination level: the fresh parameter at the large
eliminator, `zero` at the small one (the kernel's `directElimLevel`). -/
def elimLevel (p : DirectParts) : Level :=
  Lech.directElimLevel p.elim p.large

theorem elimLevel_eq (p : DirectParts) :
    elimLevel p = if p.large then .param p.elim else .zero := rfl

theorem stripPis_one_inv {e : Expr} {bs : List (Name × Expr × BinderMeta)}
    {b : Expr} (h : e.stripPis 1 = some (bs, b)) :
    ∃ nm dom mb, e = .forallE nm dom b mb ∧ bs = [(nm, dom, mb)] := by
  match e, h with
  | .forallE nm dom body mb, h =>
    simp only [Expr.stripPis, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨nm, dom, mb, rfl, rfl⟩
  | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
  | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
    simp [Expr.stripPis] at h

theorem openPisAtFvars_one (nm : Name) (dom body : Expr) (mb : BinderMeta)
    (d : Nat) :
    openPisAtFvars 1 (.forallE nm dom body mb) d
      = some ([.fvar d nm dom], body.instantiate1 (.fvar d nm dom)) := rfl

/-! ## The recursor's data -/

/-- **The recursor type's reading, peeled.** -/
structure RecData {env : Env} (m : EnvS2Core V env) (cvR : ConstantVal)
    (nP : Nat) (elimL : Level)
    (rds : (Name → Nat) → List (Nat × Nat × AVExpr)) : Prop where
  read : ∀ ψ : Name → Nat, denoteP m.acval env ψ 0 cvR.type
    = some (mkPisAV (rds ψ) (.app (.bvar 2) (.bvar 0)))
  len : ∀ ψ : Name → Nat, (rds ψ).length = nP + 3
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AVExpr), d ∈ rds ψ →
    (elimL.eval ψ = 0 ↔ d.2.1 = 0)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOkP V ρ (mkPisAV (rds ψ) (.app (.bvar 2) (.bvar 0)))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (rds ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvR.levelParams, ψ₁ p = ψ₂ p) →
    rds ψ₁ = rds ψ₂

/-- The recursor's data crosses a cons whose slot does not mention the
stored recursor. -/
theorem RecData.cross {m : EnvS2Core V env} {cvR : ConstantVal}
    {nP : Nat} {elimL : Level}
    {rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (h : RecData m cvR nP elimL rds)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none) (hat : ConsCrossAt c₀ cvR.type)
    (hcb : ConstsBound env cvR.type)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    RecData m₂ cvR nP elimL rds where
  read ψ := by
    rw [hac]
    exact denoteP_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params

end Lech.SetP
