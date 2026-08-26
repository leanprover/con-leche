import Setlec.TT.Deq

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
are stated with `Deq` (`Setlec/TT/Deq.lean`), which existentially
quantifies it.  Nothing is lost: `Deq.toHasType` re-slots at *any* type
by applying `symm` twice, and `Deq.intro` goes the other way.
-/

namespace Setlec.TT


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
