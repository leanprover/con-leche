module

public import ConLeche.Term.Subst

@[expose] public section

/-!
# Types of the built-in constants

The smart constructors for the built-in constants' `Term` types are
what the denotation function emits (`ConLeche/Verify/Denote.lean`) and what
`ConLeche/Semantics/BasisType.lean`, `ConLeche/SetModel/Value.lean` and
`ConLeche/Model/Capstone.lean` read.
-/

namespace ConLeche.Term

open Term

/-- Level lookup with a `0` default. -/
def lv (us : List Nat) (i : Nat) : Nat := us.getD i 0

/-! ## The quotient's two levels

A quotient constant reads two levels: the *domain* level `u` of its type argument
(`α : Sort u`, `lv us 0`) and the *construction* level the quotient is built at.  Its level list
carries a *lift* `ℓ` past its own levels: the construction level is `u` at the lift `0`, and
`max ℓ u` otherwise.  The released kernel's `Quot.{u} α r : Sort u` is read at the lift `0`, the
form of lean4 PR #15023, `Quot.{u} α r : Sort (max 1 u)`, at the lift `1`. -/

/-- The construction level at a lift `ℓ` over the domain level `u`. -/
def qcl (ℓ u : Nat) : Nat :=
  match ℓ with
  | 0 => u
  | l + 1 => max (l + 1) u

/-- A quotient constant's construction level, its lift read at slot `i`. -/
def quotCl (us : List Nat) (i : Nat) : Nat := qcl (lv us i) (lv us 0)

theorem le_qcl (ℓ u : Nat) : u ≤ qcl ℓ u := by
  cases ℓ with
  | zero => exact Nat.le_refl u
  | succ l => exact Nat.le_max_right _ _

theorem le_quotCl (us : List Nat) (i : Nat) : lv us 0 ≤ quotCl us i := le_qcl _ _

/-- `Quot`, `Quot.mk`, `Quot.ind`'s construction level, read off its level list. -/
@[simp] theorem quotCl_pair (u ℓ : Nat) : quotCl [u, ℓ] 1 = qcl ℓ u := rfl

/-- `Quot.lift`'s construction level, read off its level list. -/
@[simp] theorem quotCl_triple (u v ℓ : Nat) : quotCl [u, v, ℓ] 2 = qcl ℓ u := rfl

/-- At a positive lift the construction level is never `0`. -/
theorem qcl_ne_zero {ℓ : Nat} (u : Nat) (h : ℓ ≠ 0) : qcl ℓ u ≠ 0 := by
  cases ℓ with
  | zero => exact absurd rfl h
  | succ l => exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos l) (Nat.le_max_left _ _))

/-! ## Smart constructors -/

/-- `Empty.{u}` (level-polymorphic: `Empty.{0}` is `False`) -/
def emptyT (u : Nat) : Term := .const .empty [u]

/-! ## The block carrier's tuple spelling (task #315)

`lfpTuple k` binds ONE tuple of index sets and ONE operator on the
tuple of families, so its type mentions two right-nested pair towers —
`⟨Sort u_0, …, Sort u_{k-1}⟩` and `⟨I_0 → Sort w, …, I_{k-1} → Sort w⟩`
— and the members' index sets are read off the first by the uniform
projection family.  Both towers are NON-dependent: component `m` may
mention the ambient tuple variable but never an earlier component, so
the former takes the components **already lifted to their own depth**
(component `m` sits under `m` of the tower's fibre binders). -/

/-- An upper bound for every level a list mentions (`0` past its
end, so the bound is global in the index — which is what a tower's
formation premise wants). -/
def levMax (us : List Nat) : Nat := us.foldr Nat.max 0

theorem lv_le_levMax : ∀ (us : List Nat) (m : Nat), lv us m ≤ levMax us
  | [], m => by simp [lv, levMax]
  | u :: us, 0 => by
    show u ≤ Nat.max u (levMax us)
    exact Nat.le_max_left _ _
  | u :: us, m + 1 => by
    show lv us m ≤ Nat.max u (levMax us)
    exact Nat.le_trans (lv_le_levMax us m) (Nat.le_max_right _ _)

/-- The sort of `lfpTuple k`'s index-set tuple `⟨Sort u_0, …⟩`. -/
def tupleIdxSort (us : List Nat) : Nat := levMax us + 1

/-- The sort of `lfpTuple k`'s family tuple `⟨I_0 → Sort w, …⟩`. -/
def tupleFamSort (k : Nat) (us : List Nat) : Nat :=
  Nat.max (levMax us) (lv us k + 1)

end ConLeche.Term
