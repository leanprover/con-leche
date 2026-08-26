import Setlec.TT.Judgment

/-!
# Numerals, and the derivable-equation calculus they are computed with

The checker accepts `Nat.add 12345 67890 = 80235` through certified GMP
fast paths, never through 12345 ι steps.  This directory supplies the
layer's side of that: `numeral n` is the unary constructor form of a
meta-level `Nat`, and `Setlec/TT/Nat/Ops.lean` /
`Setlec/TT/Nat/WfOps.lean` prove — by *meta*-induction on the Lean-level
`Nat` — that any term satisfying an operation's certified recurrences
computes that operation on numerals.

Two disciplines, both load-bearing:

* **`numeral` is a definition to reason about, never to evaluate.**
  Nothing here `decide`s it, `#eval`s it, or `simp`s with an equation
  that would unfold it at a literal; `numeral 12345` must stay an
  opaque term of the proof, or the elaborator would build the very
  object the fast path exists to avoid.  Accordingly `numeral_zero`
  and `numeral_succ` are deliberately **not** `@[simp]`.
* **`HasType` is a `Prop`.**  Every statement below asserts the
  *existence* of a derivation; no derivation object is ever built.

## Why the equations are `Deq`, not `HasType … (.eqE T …)`

The `eqE` type slot is semantically inert (`Setlec/TT/Syntax.lean`), so
the equational rules leave it unconstrained.  Carrying an arbitrary
slot through fifteen lemmas would be pure noise, so the equations below
are stated with `Deq`, which existentially quantifies it.  Nothing is
lost: `Deq.toHasType` re-slots at *any* type by applying `symm` twice,
and `Deq.intro` goes the other way.
-/

namespace Setlec.TT

/-! ## Derivable equations -/

/-- `Deq Γ a b` — the layer derives the equation `a ≡ b` in context
`Γ`.  The `eqE` type slot is existentially quantified because it is
semantically inert; `Deq.toHasType` recovers the judgment at any slot
the caller wants. -/
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

/-! ## Numerals -/

/-- The unary constructor form of a meta-level `Nat`: `Nat.succ` applied
`n` times to `Nat.zero`.  **Reason about it; never evaluate it.** -/
def numeral : Nat → VExpr
  | 0 => natZeroT
  | n + 1 => natSuccT (numeral n)

theorem numeral_zero : numeral 0 = natZeroT := rfl

theorem numeral_succ (n : Nat) : numeral (n + 1) = natSuccT (numeral n) := rfl

/-! ## The typing correspondence

Every numeral is a closed term of type `Nat`, in every context.  This
is the layer's counterpart of `Setlec/Model/NatLit.lean`'s
`natLitVal_mem_nat` ("every numeral value is a member of the `Nat`
value"), and like it, it is a two-case meta-induction over the
constructors' own typing. -/

theorem hasType_natZeroT {Γ : List VExpr} : HasType Γ natZeroT natT :=
  .const

theorem hasType_natSuccT {Γ : List VExpr} {e : VExpr}
    (h : HasType Γ e natT) : HasType Γ (natSuccT e) natT :=
  HasType.app (A := natT) (B := natT) .const h

/-- **The typing correspondence**: `numeral n` is a `Nat`. -/
theorem hasType_numeral {Γ : List VExpr} : ∀ n : Nat,
    HasType Γ (numeral n) natT
  | 0 => hasType_natZeroT
  | n + 1 => hasType_natSuccT (hasType_numeral n)

end Setlec.TT
