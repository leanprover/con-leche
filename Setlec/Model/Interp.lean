import Setlec.Kernel.Env
import Setlec.SetTheory.Basic

/-!
# Interpretation of expressions in the set model

`interpExpr` maps (closed, well-typed) kernel expressions to elements of the
set-theoretic universe `V`.  It is partial (`Option`): expression forms the
checker does not support yet are uninterpreted.  It grows in lockstep with
the checker — the invariant maintained across iterations is that everything
the checker *accepts* is interpreted.

Currently the checker accepts nothing, and correspondingly nothing is
interpreted.  This is deliberately *not* a degenerate placeholder: because
`interpExpr` is `none` everywhere, a non-empty environment provably has no
model (`EnvModel` below), so the consistency theorem in
`Setlec.Model.Consistency` really does depend on the checker rejecting
everything.
-/

namespace Setlec

variable (V : Type u) [SetTheory V]

/-- Interpret a closed expression as an element of `V`, if supported. -/
def interpExpr (_e : Expr) : Option V := none

open SetTheory in
/-- A model of an environment: a set-theoretic value for every constant, such
that each constant's type is interpreted and the constant's value is a member
of it.  (Typing of definition *bodies*, level polymorphism, etc. will refine
this structure as the checker learns to accept such declarations.) -/
structure EnvModel (env : Env) where
  /-- The interpretation of each constant. -/
  val : Name → V
  /-- Every constant is a member of (the interpretation of) its type. -/
  mem_type : ∀ c ∈ env.consts, ∃ t, interpExpr V c.type = some t ∧ val c.name ∈ˢ t

end Setlec
