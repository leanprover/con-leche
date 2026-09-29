module

public import ConLeche.Model.Inductives.TargetCallTie
public import ConLeche.Model.Inductives.TargetNodeRb

public section

/-!
# The callee's major, opened

* `callMajor_open` — a call's typing run (`TargetCallRun`) peels the
  callee's type at the call's arguments to a `∀` whose domain, opened at
  bvar-closed terms, is a constant `I.{us}` applied to parameters `P` and
  the call's (opened) indices; `I.{us} P` names a member (a member callee:
  its head; an outside one: official's `is_nested`), and `P` is the
  prefix's first `nP` variables (member callee) or the callee major's own
  parameters up to the variables' annotations (outside callee);
* `readback_erasedEq_substFvars` — below a frame stack's holes, the one
  substitution of a call (`callSubst`) is the node read-back
  (`nodeRb`), up to the variables' annotations.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor RecShape NestCtx NestHole BinderMeta nestHoleImg)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The one substitution below the holes is the read-back -/

/-- Below `b₀ ≤ b`, the substitution does not see its bound. -/
theorem substFvars_congr_below {D : Nat} {s : Nat → Expr} {b₀ b : Nat} (hb : b₀ ≤ b) :
    ∀ (X : Expr), X.fvarsBelow b₀ → Expr.substFvars b D s X = Expr.substFvars b₀ D s X := by
  intro X
  induction X with
  | bvar i => intro _; rfl
  | fvar i ty _ =>
    intro h
    simp only [Expr.fvarsBelow] at h
    simp only [Expr.substFvars, if_pos h, if_pos (Nat.lt_of_lt_of_le h hb)]
  | sort u => intro _; rfl
  | const n us => intro _; rfl
  | lit l => intro _; rfl
  | app f a ihf iha => intro h; simp only [Expr.substFvars, ihf h.1, iha h.2]
  | lam t body m iht ihb => intro h; simp only [Expr.substFvars, iht h.1, ihb h.2]
  | forallE t body m iht ihb => intro h; simp only [Expr.substFvars, iht h.1, ihb h.2]
  | letE t v body iht ihv ihb =>
    intro h; simp only [Expr.substFvars, iht h.1, ihv h.2.1, ihb h.2.2]
  | proj n i e ih => intro h; simp only [Expr.substFvars, ih h]

/-- **The one substitution below the holes is the read-back**, up to the
variables' annotations. -/
theorem readback_erasedEq_substFvars {ctx : NestCtx} {prog : List NestHole} {fvsF : List Expr}
    {b D : Nat} (hb : ctx.hiAt prog.length ≤ b) {x : Expr}
    (hx : x.fvarsBelow (ctx.hiAt prog.length)) :
    Expr.ErasedEq (nodeRb ctx prog x) (Expr.substFvars b D (callSubst ctx prog fvsF) x) := by
  rw [nodeRb, substFvars_congr_below hb x hx]
  refine Expr.replaceFVars_erasedEq_substFvars (fun v hv ty => ?_) x hx
  by_cases h1 : v < ctx.nP
  · rw [nestHoleImg_none_of_lt h1]
    simp only [callSubst, if_pos h1, Option.getD_none]
    simp [Expr.ErasedEq]
  · obtain ⟨e, he⟩ := ConLeche.nestHoleImg_isSome (Nat.le_of_not_lt h1) prog hv
    simp only [callSubst, if_neg h1, if_pos hv, he, Option.getD_some]
    exact Expr.ErasedEq.rfl _

end ConLeche.Model
