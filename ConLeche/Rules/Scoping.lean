module

public import ConLeche.Rules.Derived
public import ConLeche.Verify.Shift
public import ConLeche.Verify.InferLeaves
public import ConLeche.Verify.EnvWF

public section

/-!
# Derivations preserve scoping (task #305)

The syntactic frame the semantic soundness theorems thread through a
derivation's premises: a reduct or an inferred type of a well-scoped,
bound, leaf-bounded subject is itself well-scoped, bound, and has no
new free-variable leaves.  These are the twins, ON THE INDUCTIVE, of
the run lemmas `whnfCore_WScoped` / `whnf_fvarLeaves` /
`inferTypeCore_looseBVars` (`Verify/InferLemmas.lean:3203`,
`Verify/InferLeaves.lean:693-968`, `Verify/InferIOLeaves.lean`), with
the same hypotheses: the environment's well-formedness supplies the
closedness of what δ and ι splice in (`unfoldDefinition_WScoped`,
`recRhs`), the rescues carry their own scope guard as a premise, and
everything else is a subterm or a substitution instance.

Proof shape (lane R-scope): one mutual structural recursion over the
six relations; the `DefEq`, `DefEqList` and `EtaProjCerts` motives are
`True`.  Nothing here reads the model; `sorry` until the lane lands.

The `looseBVars` statement for `Infer` carries `LeavesBounded` as the
run lemma does (`inferTypeCore_looseBVars`): the `fvar` clause returns
a stored leaf annotation, which `looseBVarsBounded` does not descend
into.
-/

namespace ConLeche.Rules

open ConLeche (EnvWF)

variable {env : Env}

theorem Red.wscoped (hwf : EnvWF env) {d : Nat} {e e' : Expr}
    (h : Red env d e e') (hw : Expr.WScoped d e) : Expr.WScoped d e' := by
  sorry

theorem Red.fvarLeaves (hwf : EnvWF env) {d : Nat} {e e' : Expr}
    (h : Red env d e e') (hw : Expr.WScoped d e) :
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves := by
  sorry

theorem Red.looseBVars (hwf : EnvWF env) {d : Nat} {e e' : Expr}
    (h : Red env d e e') (hw : Expr.WScoped d e)
    (hb : e.looseBVarsBounded 0 = true) (hLb : Expr.LeavesBounded e) :
    e'.looseBVarsBounded 0 = true := by
  sorry

theorem Infer.wscoped (hwf : EnvWF env) {g : Grade} {d : Nat} {e t : Expr}
    (h : Infer env g d e t) (hw : Expr.WScoped d e) : Expr.WScoped d t := by
  sorry

theorem Infer.fvarLeaves (hwf : EnvWF env) {g : Grade} {d : Nat} {e t : Expr}
    (h : Infer env g d e t) (hw : Expr.WScoped d e) :
    ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves := by
  sorry

theorem Infer.looseBVars (hwf : EnvWF env) {g : Grade} {d : Nat} {e t : Expr}
    (h : Infer env g d e t) (hw : Expr.WScoped d e)
    (hb : e.looseBVarsBounded 0 = true) (hLb : Expr.LeavesBounded e) :
    t.looseBVarsBounded 0 = true := by
  sorry

/-- The leaf bound is inherited along a reduction (a corollary of
`Red.fvarLeaves`). -/
theorem Red.leavesBounded (hwf : EnvWF env) {d : Nat} {e e' : Expr}
    (h : Red env d e e') (hw : Expr.WScoped d e) (hLb : Expr.LeavesBounded e) :
    Expr.LeavesBounded e' :=
  fun l hl => hLb l (Red.fvarLeaves hwf h hw l hl)

/-- The leaf bound is inherited by an inferred type (a corollary of
`Infer.fvarLeaves`). -/
theorem Infer.leavesBounded (hwf : EnvWF env) {g : Grade} {d : Nat} {e t : Expr}
    (h : Infer env g d e t) (hw : Expr.WScoped d e) (hLb : Expr.LeavesBounded e) :
    Expr.LeavesBounded t :=
  fun l hl => hLb l (Infer.fvarLeaves hwf h hw l hl)

/-- The inferred type of a λ is a ∀ at the λ's own annotation — a shape
fact read off the `lam` rule's conclusion (`infer_lam_meta_copy`'s
twin); the λ clause's chain case consumes it. -/
theorem Infer.lam_shape {g : Grade} {d : Nat} {ty body t : Expr}
    {mb : BinderMeta} (h : Infer env g d (.lam ty body mb) t) :
    ∃ bt, t = .forallE ty bt mb := by
  cases h with
  | lam _ _ _ _ _ _ _ => exact ⟨_, rfl⟩

end ConLeche.Rules
