module

public import ConLeche.Rules.Rel

/-!
# A Π-type or a sort reduces only to itself

Model-free (moved from `Model/Inductives/ContLeaf.lean` so the rules
bridge can read it, task #368).
-/

public section

namespace ConLeche.Rules

open ConLeche (Env Expr)

/-- A Π-type or a sort: a value no reduction step moves. -/
@[expose] def RedVal : Expr → Prop
  | .forallE .. => True
  | .sort _ => True
  | _ => False

/-- **A Π-type or a sort reduces only to itself.** -/
theorem Red.eq_of_redVal {env : Env} {d : Nat} :
    ∀ {e e' : Expr}, Red env d e e' → RedVal e → e' = e
  | _, _, .refl, _ => rfl
  | _, _, .trans h₁ h₂, hv =>
    have h1 := Red.eq_of_redVal h₁ hv
    have h2 := Red.eq_of_redVal h₂ (h1 ▸ hv)
    h2.trans h1
  | e, _, .delta hu, hv => by
    cases e <;> simp [RedVal] at hv <;> simp [ConLeche.unfoldDefinition, Expr.getAppFn] at hu
  | e, _, .iota hfn .., hv => by
    cases e <;> simp [RedVal] at hv <;> simp [Expr.getAppFn] at hfn
  | e, _, .kRec hfn .., hv => by
    cases e <;> simp [RedVal] at hv <;> simp [Expr.getAppFn] at hfn
  | e, _, .rescueK _ _ _ _ _ hinf hred hfn .., hv =>
    have key := fun h => Red.eq_of_redVal hred h
    by
    cases e <;> simp [RedVal] at hv <;> cases hinf <;>
      (rw [key (by simp [RedVal])] at hfn; simp [Expr.getAppFn] at hfn)
  | e, _, .rescueEta _ _ _ _ _ hinf hred hfn .., hv =>
    have key := fun h => Red.eq_of_redVal hred h
    by
    cases e <;> simp [RedVal] at hv <;> cases hinf <;>
      (rw [key (by simp [RedVal])] at hfn; simp [Expr.getAppFn] at hfn)
  | e, _, .rescueAnd _ _ _ _ hinf hred hfn .., hv =>
    have key := fun h => Red.eq_of_redVal hred h
    by
    cases e <;> simp [RedVal] at hv <;> cases hinf <;>
      (rw [key (by simp [RedVal])] at hfn; simp [Expr.getAppFn] at hfn)
  | _, _, .appFn _, hv => hv.elim
  | _, _, .projArg _, hv => hv.elim
  | _, _, .beta, hv => hv.elim
  | _, _, .zeta, hv => hv.elim
  | _, _, .natLit _, hv => hv.elim
  | _, _, .strLit _, hv => hv.elim
  | _, _, .natSucc .., hv => hv.elim
  | _, _, .natOp .., hv => hv.elim
  | _, _, .proj .., hv => hv.elim

end ConLeche.Rules
