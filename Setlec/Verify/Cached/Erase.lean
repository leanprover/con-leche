import Setlec.Cached.ExprC
import Setlec.Kernel.ArenaWF
import Setlec.Verify.IExpr

/-!
# The cached representation's field facts (task #163; rewritten at #172
B3a)

This module used to be the *seam floor*: an erasure `eraseC : ExprC →
Expr`, its injectivity on the field invariant `WFc`, field exactness
conditioned on `WFc`, and a normal-form characterization of a
hash-checking equality — everything needed to relate a second
expression type to the spec's one.

**There is no seam.**  `ExprC` is `Setlec.Expr` and the four derived
data are its `@[computed_field]`s, so what is left is the three facts
the cached operations actually consume, each now unconditional:

* **field exactness** — `bvarB_eq`, `fvarB_eq`, `hasLP_eq`: the
  computed fields *are* the spec functions `Expr.bvarBound`,
  `Expr.fvarRange`, `Expr.hasLevelParam`.  Same recurrence, one
  written in a `with` block and one as an ordinary definition, so
  every cutoff the cached operations take is the cutoff the spec
  takes;
* **the cutoff consequences** — `bvarB_le`, `fvarB_le`, `hasLP_false`:
  a field at or below the cursor licenses the skip;
* **equality** — `beq` is `decide (· = ·)`, so the `EquivBEq` and
  `LawfulHashable` premises of the `Std.HashMap` lemmas are the
  standard ones, and `beq_iff` is `beq_iff_eq`.

Deleted with the seam: `eraseC` and `eraseC_inj`, `hashSpec` and
`hash_exact`, `zeroC`/`beqSpec_iff_zeroC` and the whole normal-form
apparatus, `MemoErase`/`toExprGo_spec`/`toExpr_eq` (there is no
readback).  847 lines to this.

`WFc` survives — see `Setlec/Cached/ExprC.lean`'s note: it is the
predicate of `WDeclC`, which six frozen direct-parse capstone letters
are stated over.  It is *total* (`WFc_all`), so the arguments the
lemmas below still take are vestigial and are removed when that
statement change is ratified.
-/

namespace Setlec.Cached

open Setlec

namespace ExprC

/-! ## The inversion lemmas

`rfl` plus totality now: a node's children are well-formed because
everything is, and a node *is* its constructor's application. -/

theorem WFc.fvar_inv {idx : Nat} {n : Name} {ty : ExprC}
    (_hw : WFc (.fvar idx n ty)) :
    WFc ty ∧ Expr.fvar idx n ty = mkFVar idx n ty :=
  ⟨WFc_all ty, rfl⟩

theorem WFc.app_inv {f a : ExprC} (_hw : WFc (.app f a)) :
    WFc f ∧ WFc a ∧ Expr.app f a = mkApp f a :=
  ⟨WFc_all f, WFc_all a, rfl⟩

theorem WFc.lam_inv {n : Name} {ty b : ExprC} {m : BinderMeta}
    (_hw : WFc (.lam n ty b m)) :
    WFc ty ∧ WFc b ∧ Expr.lam n ty b m = mkLam n ty b m :=
  ⟨WFc_all ty, WFc_all b, rfl⟩

theorem WFc.forallE_inv {n : Name} {ty b : ExprC} {m : BinderMeta}
    (_hw : WFc (.forallE n ty b m)) :
    WFc ty ∧ WFc b ∧ Expr.forallE n ty b m = mkForallE n ty b m :=
  ⟨WFc_all ty, WFc_all b, rfl⟩

theorem WFc.letE_inv {n : Name} {ty v b : ExprC}
    (_hw : WFc (.letE n ty v b)) :
    WFc ty ∧ WFc v ∧ WFc b ∧ Expr.letE n ty v b = mkLetE n ty v b :=
  ⟨WFc_all ty, WFc_all v, WFc_all b, rfl⟩

theorem WFc.proj_inv {s : Name} {i : Nat} {e : ExprC}
    (_hw : WFc (.proj s i e)) :
    WFc e ∧ Expr.proj s i e = mkProj s i e :=
  ⟨WFc_all e, rfl⟩

/-! ## Field exactness

The same exactness the arena's `TWF.bvarBoundD_exact2` /
`fvarRangeD_exact2` / `ehasParamD_exact2` provide for the parallel
arrays — without the arrays, and without a hypothesis. -/

/-- The `bvarB` field is `Expr.bvarBound`. -/
theorem bvarB_eq : ∀ e : ExprC, e.bvarB = Expr.bvarBound e := by
  intro e
  induction e <;> simp_all [Expr.bvarB, Expr.bvarBound]

@[inherit_doc bvarB_eq]
theorem bvarB_exact {e : ExprC} (_hw : WFc e) : e.bvarB = Expr.bvarBound e :=
  bvarB_eq e

/-- Cutoff consequence: a bound at or below the cursor certifies
`looseBVarsBounded` (the transposition of `TWF.bvarBoundD_le2`). -/
theorem bvarB_le {e : ExprC} {d : Nat} (_hw : WFc e) (hle : e.bvarB ≤ d) :
    Expr.looseBVarsBounded d e = true :=
  EStore.looseBVarsBounded_iff.mpr (bvarB_eq e ▸ hle)

/-- The `fvarB` field is `Expr.fvarRange`. -/
theorem fvarB_eq : ∀ e : ExprC, e.fvarB = Expr.fvarRange e := by
  intro e
  induction e <;> simp_all [Expr.fvarB, Expr.fvarRange]

@[inherit_doc fvarB_eq]
theorem fvarB_exact {e : ExprC} (_hw : WFc e) : e.fvarB = Expr.fvarRange e :=
  fvarB_eq e

/-- Cutoff consequence: a range at or below the base certifies
`Expr.fvarsBelow` — the predicate the abstraction traversals consume
(`abstractRange_eq_self`); the transposition of `TWF.fvarRangeD_le`. -/
theorem fvarB_le {e : ExprC} {d : Nat} (_hw : WFc e) (hle : e.fvarB ≤ d) :
    Expr.fvarsBelow d e :=
  EStore.fvarsBelow_iff.mpr (fvarB_eq e ▸ hle)

/-! ### Has-level-param -/

/-- The node-level walk is the kernel's `Level.hasParam`. -/
theorem levelHasParam_eq : ∀ u : Level, levelHasParam u = u.hasParam := by
  intro u
  induction u <;> simp_all [levelHasParam, Level.hasParam]

/-- …and its list fold is `List.any`. -/
theorem levelsHaveParam_eq : ∀ us : List Level,
    levelsHaveParam us = us.any Level.hasParam := by
  intro us
  induction us with
  | nil => rfl
  | cons u us ih => simp [levelsHaveParam, List.any_cons, levelHasParam_eq, ih]

/-- The `hasLP` field is `Expr.hasLevelParam`. -/
theorem hasLP_eq : ∀ e : ExprC, e.hasLP = Expr.hasLevelParam e := by
  intro e
  induction e <;>
    simp_all [Expr.hasLP, Expr.hasLevelParam, levelHasParam_eq,
      levelsHaveParam_eq]

@[inherit_doc hasLP_eq]
theorem hasLP_exact {e : ExprC} (_hw : WFc e) : e.hasLP = Expr.hasLevelParam e :=
  hasLP_eq e

/-- Invisibility consequence: level instantiation is the identity on a
node whose flag is off (the `O(1)` shortcut every `instLevelParams`
traversal takes). -/
theorem hasLP_false {e : ExprC} {ks : List Name} {us : List Level}
    (_hw : WFc e) (h : e.hasLP = false) :
    e.instantiateLevelParams ks us = e :=
  Expr.instantiateLevelParams_eq_self (by rw [← hasLP_eq e, h])

/-! ## Equality

`beq` is `decide (· = ·)` (`Setlec/Kernel/Expr.lean`): with the hash a
*function* of the node there is nothing for the old `beqSpec`/`zeroC`
normal-form apparatus to say.  It existed only to characterize a
descent that compared *stored* hashes, which could disagree with the
term. -/

/-- `beq` in its unfolded form decides equality. -/
theorem beq_eq {a b : ExprC} (h : Expr.beq a b = true) : a = b :=
  of_decide_eq_true h

/-- …and is reflexive there. -/
@[simp] theorem beq_self (a : ExprC) : Expr.beq a a = true := by
  simp [Expr.beq]

/-- Soundness of a decided equality — the form the memo proofs
consume (a memo hit's key is only `BEq`-equal to the query). -/
theorem beq_sound {a b : ExprC} (h : (a == b) = true) : a = b :=
  eq_of_beq h

/-- Equality is an equivalence — the `Std.HashMap` lemmas' first
premise (an instance, so every memo-preservation proof gets it for
free). -/
instance : EquivBEq ExprC where
  symm h := by rw [eq_of_beq h]; exact beq_self_eq_true _
  trans hab hbc := by rw [eq_of_beq hab]; exact hbc
  rfl := beq_self_eq_true _

/-- The `O(1)` `Hashable` instance (the computed field) is lawful for
it — the `Std.HashMap` lemmas' second premise. -/
instance : LawfulHashable ExprC where
  hash_eq _ _ h := by rw [eq_of_beq h]

/-- Decided equality **is** equality.  (Before B3a the `←` direction
needed `WFc` on both sides — `eraseC_inj` — because distinct field
blocks could erase alike; the arguments are vestigial.) -/
theorem beq_iff {a b : ExprC} (_ha : WFc a) (_hb : WFc b) :
    (a == b) = true ↔ a = b := beq_iff_eq

end ExprC

end Setlec.Cached
