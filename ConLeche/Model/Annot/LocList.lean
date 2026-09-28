module

public import ConLeche.Kernel.ExprOps

public section

/-!
# The local opening of a term above a free frame

`LocList B d xs`: `xs` opens the `d` loose bound variables of a term as
the free variables `B … B+d-1` (`bvar j ↦ fvar (B + d - 1 - j)`), their
stored types free — `denoteMeta` does not read them.  The pattern every
"two terms read alike under binders" induction uses (`targetAbs_read`,
the class abstraction's `classAbsSpec_read`).
-/

namespace ConLeche.Model
open ConLeche (Expr)

/-! ## The local opening -/

/-- **A local opening above a free frame**: `xs` replaces the `d`
loose bound variables of a term by the free variables above the frame
`B`, `bvar j ↦ fvar (B + d - 1 - j)`.  The stored types are free:
`denoteMeta` does not read them. -/
@[expose] def LocList (B d : Nat) (xs : List Expr) : Prop :=
  xs.length = d ∧ ∀ j, j < d → ∃ ty : Expr, xs[j]? = some (.fvar (B + d - 1 - j) ty)

theorem LocList.nil (B : Nat) : LocList B 0 [] :=
  ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

theorem LocList.cons {B d : Nat} {xs : List Expr} (h : LocList B d xs) (ty : Expr) :
    LocList B (d + 1) (Expr.fvar (B + d) ty :: xs) := by
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  cases j with
  | zero => exact ⟨ty, by simp⟩
  | succ j =>
    obtain ⟨ty', hty'⟩ := h.2 j (by omega)
    refine ⟨ty', ?_⟩
    rw [show B + (d + 1) - 1 - (j + 1) = B + d - 1 - j from by omega]
    simpa using hty'

/-- Opening a local variable the list covers. -/
theorem LocList.bvar_lt {B d j : Nat} {xs : List Expr} (h : LocList B d xs) (hj : j < d) :
    ∃ ty : Expr, (Expr.bvar j).instantiateList xs 0 = .fvar (B + d - 1 - j) ty := by
  obtain ⟨ty, hty⟩ := h.2 j hj
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hty
  refine ⟨ty, ?_⟩
  rw [Expr.instantiateList, if_neg (by omega), dif_pos (by omega)]
  simp only [Nat.sub_zero]
  rw [show xs[j] = Expr.fvar (B + d - 1 - j) ty from hget, Expr.instantiateList]

/-- Opening a loose variable above the locals: lowered, unread. -/
theorem LocList.bvar_ge {B d j : Nat} {xs : List Expr} (h : LocList B d xs) (hj : d ≤ j) :
    (Expr.bvar j).instantiateList xs 0 = .bvar (j - d) := by
  rw [Expr.instantiateList, if_neg (by omega), dif_neg (by rw [h.1]; omega), h.1]

end ConLeche.Model
