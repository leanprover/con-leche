module

public import ConLeche.Verify.SubstFvars
public import ConLeche.Verify.Subst

public section

/-!
# A replacement of free variables is a parallel substitution, up to annotations

`Expr.replaceFVars` (the kernel's) and `Expr.substFvars` (the
verification's, `SubstFvars.lean`) agree below the substitution's bound up
to the free variables' annotations (`ErasedEq`), when the substitution
agrees with the replacement.  The class check's commutation equation and
the old route's read-back both read through it.
-/

namespace ConLeche.Expr

/-- **The read-back as a parallel substitution**: below `b`, replacing the
mapped variables (keeping the others, up to their annotations) is
`substFvars` at a substitution agreeing with it. -/
theorem replaceFVars_erasedEq_substFvars {g : Nat → Option Expr} {b D : Nat} {s : Nat → Expr}
    (hs : ∀ v, v < b → ∀ ty, ErasedEq ((g v).getD (.fvar v ty)) (s v)) :
    ∀ (X : Expr), X.fvarsBelow b → ErasedEq (X.replaceFVars g) (substFvars b D s X) := by
  intro X
  induction X with
  | bvar i => intro _; exact ErasedEq.rfl _
  | fvar i ty _ =>
    intro h
    simp only [fvarsBelow] at h
    simp only [replaceFVars, substFvars, if_pos h]
    exact hs i h ty
  | sort u => intro _; exact ErasedEq.rfl _
  | const n us => intro _; exact ErasedEq.rfl _
  | lit l => intro _; exact ErasedEq.rfl _
  | app f a ihf iha =>
    intro h; exact ⟨ihf h.1, iha h.2⟩
  | lam t body m iht ihb =>
    intro h; exact ⟨rfl, iht h.1, ihb h.2⟩
  | forallE t body m iht ihb =>
    intro h; exact ⟨rfl, iht h.1, ihb h.2⟩
  | letE t v body iht ihv ihb =>
    intro h; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj n i e ih =>
    intro h; exact ⟨rfl, rfl, ih h⟩

end ConLeche.Expr
