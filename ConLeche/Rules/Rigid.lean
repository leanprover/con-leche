module

public import ConLeche.Rules.Rel

@[expose] public section

/-!
# Rigid heads reduce only to themselves (task #342 L18)

A ∀ and a sort are in normal form for every `Red` rule: no rule's
left-hand side is one, except the rescues', whose subject is a major
`m` whose io-inferred type reduces to a constant-headed application —
and a ∀'s or a sort's type is a sort, which (by this lemma, recursively)
reduces only to itself.  The io grade's hereditary claim `IORel` is keyed
on the *syntax* of an inferred type (a ∀), and is carried along a
reduction of that type by this lemma (`Model/Rules/IORel.lean`).
-/

namespace ConLeche.Rules

variable {env : Env}

/-- A ∀ or a sort. -/
def IsRigid : Expr → Prop
  | .forallE .. => True
  | .sort _ => True
  | _ => False

theorem IsRigid.getAppFn {e : Expr} (h : IsRigid e) : e.getAppFn = e := by
  cases e <;> first | rfl | exact h.elim

theorem IsRigid.not_const {e : Expr} (h : IsRigid e) {c : Name} {us : List Level} :
    e.getAppFn ≠ .const c us := by
  rw [h.getAppFn]; intro he; subst he; exact h.elim

/-- A rigid term's inferred type is a sort. -/
theorem Infer.sort_of_rigid {g : Grade} {d : Nat} {e t : Expr}
    (h : Infer env g d e t) (hr : IsRigid e) : ∃ u, t = .sort u := by
  cases h with
  | sort => exact ⟨_, rfl⟩
  | forallE => exact ⟨_, rfl⟩
  | _ => exact hr.elim

/-- **A ∀ or a sort reduces only to itself.** -/
theorem Red.rigid : ∀ {d : Nat} {e e' : Expr}, Red env d e e' → IsRigid e → e' = e
  | _, _, _, .refl, _ => rfl
  | _, _, _, .trans h₁ h₂, hr => by
    have e₁ := Red.rigid h₁ hr
    subst e₁
    exact Red.rigid h₂ hr
  | _, _, _, .appFn _, hr => hr.elim
  | _, _, _, .projArg _, hr => hr.elim
  | _, _, _, .beta, hr => hr.elim
  | _, _, _, .zeta, hr => hr.elim
  | _, _, e, .delta h, hr => by
    rename_i e₀
    have : unfoldDefinition env e₀ = none := by
      unfold unfoldDefinition; rw [hr.getAppFn]
      cases e₀ <;> first | rfl | exact hr.elim
    rw [this] at h; exact nomatch h
  | _, _, _, .natLit _, hr => hr.elim
  | _, _, _, .strLit _, hr => hr.elim
  | _, _, _, .natSucc .., hr => hr.elim
  | _, _, _, .natOp .., hr => hr.elim
  | _, _, _, .proj .., hr => hr.elim
  | _, _, _, .iota hhead .., hr => absurd hhead hr.not_const
  | _, _, _, .kRec hhead .., hr => absurd hhead hr.not_const
  | _, _, _, .rescueK _ _ _ _ _ htm htmaj hthead .., hr => by
    have hrec : IsRigid _ → _ := fun h => Red.rigid htmaj h
    obtain ⟨u, rfl⟩ := Infer.sort_of_rigid htm hr
    have := hrec trivial
    subst this
    exact absurd hthead (IsRigid.not_const (e := .sort u) trivial)
  | _, _, _, .rescueEta _ _ _ _ _ htm htmaj hthead .., hr => by
    have hrec : IsRigid _ → _ := fun h => Red.rigid htmaj h
    obtain ⟨u, rfl⟩ := Infer.sort_of_rigid htm hr
    have := hrec trivial
    subst this
    exact absurd hthead (IsRigid.not_const (e := .sort u) trivial)
  | _, _, _, .rescueAnd _ _ _ _ htm htmaj hthead .., hr => by
    have hrec : IsRigid _ → _ := fun h => Red.rigid htmaj h
    obtain ⟨u, rfl⟩ := Infer.sort_of_rigid htm hr
    have := hrec trivial
    subst this
    exact absurd hthead (IsRigid.not_const (e := .sort u) trivial)

end ConLeche.Rules
