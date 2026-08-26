import Setlec.TT.Judgment

/-!
# Derivable equations

`Deq Γ a b` — "the layer derives `a ≡ b` in `Γ`" — with the `eqE` type
slot existentially quantified, plus the congruence and equivalence
lemmas every consumer of the equational rules wants.

The `eqE` slot is semantically inert (`Setlec/TT/Syntax.lean`), so the
equational rules leave it unconstrained; carrying an arbitrary slot
through a proof is pure noise.  `Deq` hides it, and `Deq.toHasType`
recovers the judgment at *any* slot the caller wants.

This is not specific to any one client.  It was written for the
numeral families (`Setlec/TT/Nat/*`, task #119) and is equally what the
bridge's definitional-equality claims are stated with — the checker's
`isDefEq` returning `true` becomes a `Deq` between denotations — so it
lives here, next to the judgment it is about.
-/

namespace Setlec.TT

/-- `Deq Γ a b` — the layer derives the equation `a ≡ b` in context
`Γ`.  The `eqE` type slot is existentially quantified because it is
semantically inert; `Deq.toHasType` recovers the judgment at any slot
the caller wants.

**The slot is inert *derivationally*, not merely semantically.**  The
existential loses nothing: `Deq.toHasType` produces a derivation at an
arbitrary slot from a derivation at any one slot, by applying `symm`
twice.  So an equation derivable at one type slot is derivable at
*every* type slot — the ruling recorded in `Setlec/TT/Syntax.lean` (the
interpretation never reads `ty`) has this stronger, purely syntactic
counterpart, and a rule-writer may rely on it: constraining a `T` slot
in a new equational rule would constrain nothing. -/
def Deq (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ T, HasType Γ .prf (.eqE T a b)

namespace Deq

variable {Γ : List VExpr} {a b c f f' x x' y y' : VExpr}

/-- Any derivation of an equation between `a` and `b` is a `Deq`. -/
theorem intro {T p : VExpr} (h : HasType Γ p (.eqE T a b)) : Deq Γ a b :=
  ⟨T, HasType.symm (T' := T) (HasType.symm (T' := T) h)⟩

/-- A `Deq` is a derivation at **any** type slot: the slot is inert, so
two applications of `symm` retype it. -/
theorem toHasType (h : Deq Γ a b) (T : VExpr) :
    HasType Γ .prf (.eqE T a b) :=
  h.elim fun T₀ hp =>
    HasType.symm (T' := T) (HasType.symm (T' := T₀) hp)

@[refl] theorem refl : Deq Γ a a := ⟨a, .refl⟩

theorem symm (h : Deq Γ a b) : Deq Γ b a :=
  ⟨a, HasType.symm (T' := a) (h.toHasType a)⟩

theorem trans (h : Deq Γ a b) (h' : Deq Γ b c) : Deq Γ a c :=
  ⟨a, HasType.trans (T'' := a) (h.toHasType a) (h'.toHasType b)⟩

/-- Congruence for application (the checker's `defeqSpine`, one slot). -/
theorem app (hf : Deq Γ f f') (hx : Deq Γ x x') :
    Deq Γ (.app f x) (.app f' x') :=
  ⟨f, HasType.congrApp (T'' := f) (hf.toHasType f) (hx.toHasType x)⟩

theorem appFun (hf : Deq Γ f f') : Deq Γ (.app f x) (.app f' x) :=
  app hf refl

theorem appArg (hx : Deq Γ x x') : Deq Γ (.app f x) (.app f x') :=
  app refl hx

/-- Equality reflection, in `Deq` form. -/
theorem conv {t A B : VExpr} (ht : HasType Γ t A) (h : Deq Γ A B) :
    HasType Γ t B :=
  HasType.conv ht (h.toHasType A)

end Deq

/-- Binary application.  The operations' certified recurrences
(`natOpEquations`, `DivModClauses`) are all spines of this shape, so
naming it keeps the hypotheses of the op lemmas readable and
syntactically close to the certificates the bridge will denote. -/
def ap2 (f a b : VExpr) : VExpr := .app (.app f a) b

theorem Deq.ap2 {Γ : List VExpr} {f x x' y y' : VExpr}
    (hx : Deq Γ x x') (hy : Deq Γ y y') :
    Deq Γ (Setlec.TT.ap2 f x y) (Setlec.TT.ap2 f x' y') :=
  Deq.app (Deq.appArg hx) hy

end Setlec.TT
