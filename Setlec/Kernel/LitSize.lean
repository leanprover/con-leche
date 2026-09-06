import Setlec.Kernel.Core

/-!
# `Expr.sizeL` — the literal-weighted size

`Expr.sizeB` is the measure for recursion through instantiated binder
bodies.  A recursion that also expands literals into their constructor
forms — `natLitToConstructor`, one `Nat.succ` layer at a time, and
`strLitToConstructor` — needs a literal to weigh more than its
expansion; `sizeL` is `sizeB` with the literal leaves so weighted.  Used
by `Setlec.Semantics.sem`.
-/

namespace Setlec

/-- The `sizeL` of `strLitToConstructor`'s character-list spine. -/
def strLitWeight : List Char → Nat
  | [] => 3
  | c :: cs => 3 * c.toNat + 9 + strLitWeight cs

/-- A literal weighs one more than its constructor form. -/
def Literal.weight : Literal → Nat
  | .natVal k => 3 * k + 2
  | .strVal s => strLitWeight s.toList + 3

/-- `sizeB` with literal leaves weighted by `Literal.weight`. -/
def Expr.sizeL : Expr → Nat
  | .bvar _ | .fvar .. | .sort _ | .const .. => 1
  | .lit l => l.weight
  | .app f a => sizeL f + sizeL a + 1
  | .lam _ ty body _ | .forallE _ ty body _ => sizeL ty + sizeL body + 1
  | .letE _ ty val body => sizeL ty + sizeL val + sizeL body + 1
  | .proj _ _ e => sizeL e + 1

/-- Instantiating with a size-1 replacement preserves `sizeL`. -/
theorem Expr.sizeL_instantiate1 (v : Expr) (hv : sizeL v = 1) :
    ∀ (e : Expr) (d : Nat), sizeL (instantiate1 e v d) = sizeL e := by
  intro e
  induction e <;> intro d <;> simp [instantiate1, sizeL, *]
  case bvar i =>
    split
    · exact hv
    · split <;> rfl

theorem Expr.sizeL_natLitToConstructor_lt (k : Nat) :
    (natLitToConstructor k).sizeL < (Expr.lit (.natVal k)).sizeL := by
  cases k <;> simp [natLitToConstructor, sizeL, Literal.weight] <;> omega

theorem strLitWeight_foldr (l : List Char) :
    (l.foldr
      (init := Expr.app (.const listNilName [.zero]) (.const charName []))
      fun c e =>
        .app (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e).sizeL
      = strLitWeight l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldr_cons, Expr.sizeL, Literal.weight, strLitWeight, ih]
    omega

theorem Expr.sizeL_strLitToConstructor_lt (s : String) :
    (strLitToConstructor s).sizeL < (Expr.lit (.strVal s)).sizeL := by
  unfold strLitToConstructor
  simp only [Expr.sizeL, Literal.weight, strLitWeight_foldr]
  omega

end Setlec
