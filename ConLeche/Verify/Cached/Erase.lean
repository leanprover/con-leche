module

public import ConLeche.Verify.Shift

public section

/-!
# The cached representation's field facts (task #163)

`Expr` is `ConLeche.Expr` and the four derived data are its
`@[computed_field]`s; this module holds the facts the cached operations
consume, each unconditional:

* **field exactness** — `bvarB_eq`, `fvarB_eq`, `hasLP_eq`
  (`ConLeche/Kernel/ExprOps.lean`): the computed fields *are* the spec
  functions `Expr.bvarBound`, `Expr.fvarRange`, `Expr.hasLevelParam`,
  so every cutoff the cached operations take is the cutoff the spec
  takes;
* **the cutoff consequences** — `bvarB_le`, `fvarB_le`, `hasLP_false`:
  a field at or below the cursor licenses the skip;
* **equality** — `beq` is `decide (· = ·)`, so the `EquivBEq` and
  `LawfulHashable` premises of the `Std.HashMap` lemmas are the
  standard ones, and `beq_iff` is `beq_iff_eq`.
-/

namespace ConLeche.Expr

/-! ## Field exactness

The two range fields are *packed* and **saturate** at `satRange`
(`Kernel/Expr.lean`, task #167), so the exactness argument
(`ConLeche/Kernel/ExprOps.lean`) runs in two steps and lands on
unconditional equations:

1. `bvarBRaw_exact` / `fvarBRaw_exact` — the stored field is the spec
   function **below saturation** (an induction on the packed word's
   per-constructor equations);
2. `bvarBoundMemo_eq` / `fvarRangeMemo_eq` — the saturated branch's
   memoized recomputation is the spec function *everywhere*.

Their conjunction is `bvarB_eq` / `fvarB_eq`: saturation is a
representation decision, so no skip site grows a guard. -/

/-! ### Exactness below saturation -/

/-! ### The saturated branch: the memoized walks are the spec functions

The memo invariant is the usual one — every stored answer is the spec
function of its key — and the walks preserve it. -/

/-! ### The unconditional field equations -/

/-- Cutoff consequence: a bound at or below the cursor certifies
`looseBVarsBounded`. -/
theorem bvarB_le {e : Expr} {d : Nat} (hle : e.bvarB ≤ d) :
    Expr.looseBVarsBounded d e = true :=
  Expr.looseBVarsBounded_iff.mpr (bvarB_eq e ▸ hle)

/-- Cutoff consequence: a range at or below the base certifies
`Expr.fvarsBelow` — the predicate the abstraction traversals consume
(`abstractRange_eq_self`). -/
theorem fvarB_le {e : Expr} {d : Nat} (hle : e.fvarB ≤ d) :
    Expr.fvarsBelow d e :=
  Expr.fvarsBelow_iff.mpr (fvarB_eq e ▸ hle)

/-! ### Has-level-param -/

/-- Invisibility consequence: level instantiation is the identity on a
node whose flag is off (the `O(1)` shortcut every `instLevelParams`
traversal takes). -/
theorem hasLP_false {e : Expr} {ks : List Name} {us : List Level}
    (h : e.hasLP = false) :
    e.instantiateLevelParams ks us = e :=
  Expr.instantiateLevelParams_eq_self (by rw [← Expr.hasLP_eq e, h])

/-! ## Equality

`beq` is `decide (· = ·)` (`ConLeche/Kernel/Expr.lean`), and the hash
is a *function* of the node. -/

/-- `beq` in its unfolded form decides equality. -/
theorem beq_eq {a b : Expr} (h : Expr.beq a b = true) : a = b :=
  of_decide_eq_true h

/-- …and is reflexive there. -/
@[simp] theorem beq_self (a : Expr) : Expr.beq a a = true := by
  simp [Expr.beq]

/-- Soundness of a decided equality — the form the memo proofs
consume (a memo hit's key is only `BEq`-equal to the query). -/
theorem beq_sound {a b : Expr} (h : (a == b) = true) : a = b :=
  eq_of_beq h

/-- Equality is an equivalence — the `Std.HashMap` lemmas' first
premise (an instance, so every memo-preservation proof gets it for
free). -/
instance : EquivBEq Expr where
  symm h := by rw [eq_of_beq h]; exact beq_self_eq_true _
  trans hab hbc := by rw [eq_of_beq hab]; exact hbc
  rfl := beq_self_eq_true _

/-- The `O(1)` `Hashable` instance (the computed field) is lawful for
it — the `Std.HashMap` lemmas' second premise. -/
instance : LawfulHashable Expr where
  hash_eq _ _ h := by rw [eq_of_beq h]

/-- Decided equality **is** equality. -/
theorem beq_iff {a b : Expr} : (a == b) = true ↔ a = b := beq_iff_eq

end ConLeche.Expr
