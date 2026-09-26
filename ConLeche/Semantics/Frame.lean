module

public import ConLeche.Verify.InferLeaves

@[expose] public section

/-!
# The opened binder's frame conditions

One theorem, `frame_open2`: pure `Expr` scoping arithmetic
(`WScoped`, `looseBVarsBounded`, `LeavesBounded` under
`instantiate1`), mentioning no model at all.
-/

namespace ConLeche.Semantics

open ConLeche (Expr Name)

/-- The frame conditions of an opened binder, *without* the context. -/
theorem frame_open2 {d : Nat} {ty body : Expr}
    (hwty : Expr.WScoped d ty) (hbty : ty.looseBVarsBounded 0 = true)
    (hwb : Expr.WScoped d body)
    (hbb : body.looseBVarsBounded 1 = true)
    (hLty : Expr.LeavesBounded ty)
    (hLbody : Expr.LeavesBounded body) :
    Expr.WScoped (d + 1) (body.instantiate1 (.fvar d ty)) ∧
      (body.instantiate1 (.fvar d ty)).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (body.instantiate1 (.fvar d ty)) := by
  refine ⟨Expr.WScoped.instantiate1 hwty 0 hwb,
    ConLeche.looseBVarsBounded_instantiate1 body 0 hbb, fun l hl => ?_⟩
  rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
  · exact hLbody l h2
  · rw [Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hbty
    · exact hLty l h3

end ConLeche.Semantics
