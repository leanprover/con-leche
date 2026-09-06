import Lech.Cached.ExprC
import Lech.Verify.Shift

/-!
# The cached representation's field facts (task #163; rewritten at #172
B3a)

This module used to be the *seam floor*: an erasure `eraseC : ExprC →
Expr`, its injectivity on the field invariant `WFc`, field exactness
conditioned on `WFc`, and a normal-form characterization of a
hash-checking equality — everything needed to relate a second
expression type to the spec's one.

**There is no seam.**  `ExprC` is `Lech.Expr` and the four derived
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

**Task #172 B3b**: `WFc` itself is gone — the six direct-parse capstone
letters it survived for are restated over `List DeclC` — so the
lemmas below take no invariant argument, the six `WFc.*_inv`
inversions are deleted (a node's children need no certificate), and
what is left is exactly three field equations and their two cutoff
consequences.
-/

namespace Lech.Cached

open Lech

namespace ExprC

/-! ## Field exactness

The same exactness the arena's `TWF.bvarBoundD_exact2` /
`fvarRangeD_exact2` / `ehasParamD_exact2` provide for the parallel
arrays — without the arrays, and without a hypothesis.

Since task #167 the two range fields are *packed* and **saturate** at
`satRange` (`Kernel/Expr.lean`), so the exactness argument runs in two
steps and lands on the same unconditional equations:

1. `bvarBRaw_exact` / `fvarBRaw_exact` — the stored field is the spec
   function **below saturation** (an induction on the packed word's
   per-constructor equations);
2. `bvarBoundMemo_eq` / `fvarRangeMemo_eq` — the saturated branch's
   memoized recomputation is the spec function *everywhere*.

Their conjunction is `bvarB_eq` / `fvarB_eq` **verbatim as before**:
saturation is a representation decision, so no statement below it
moves and no skip site grows a guard. -/

/-! ### Exactness below saturation -/

/-- The packed loose-bvar field is `Expr.bvarBound` wherever it did not
saturate. -/
theorem bvarBRaw_exact : ∀ e : ExprC, e.bvarBRaw < satRange →
    e.bvarBRaw = Expr.bvarBound e := by
  intro e
  induction e with
  | bvar i => intro h; simp_all [satRange, Expr.bvarBound]; omega
  | fvar _ _ _ _ | sort _ | const _ _ | lit _ =>
    intro _; simp [Expr.bvarBound]
  | app f a ihf iha =>
    intro h
    rw [Expr.bvarBRaw_app] at h ⊢
    rw [ihf (by omega), iha (by omega), Expr.bvarBound]
  | lam n ty b m iht ihb =>
    intro h
    rw [Expr.bvarBRaw_lam] at h ⊢
    have hb : b.bvarBRaw ≠ satRange := by
      intro hb'; rw [hb'] at h; simp at h; omega
    have hb2 : b.bvarBRaw < satRange := by
      have := Expr.bvarBRaw_lt b; simp [satRange] at *; omega
    rw [if_neg hb, iht (by omega), ihb hb2, Expr.bvarBound]
  | forallE n ty b m iht ihb =>
    intro h
    rw [Expr.bvarBRaw_forallE] at h ⊢
    have hb : b.bvarBRaw ≠ satRange := by
      intro hb'; rw [hb'] at h; simp at h; omega
    have hb2 : b.bvarBRaw < satRange := by
      have := Expr.bvarBRaw_lt b; simp [satRange] at *; omega
    rw [if_neg hb, iht (by omega), ihb hb2, Expr.bvarBound]
  | letE n ty v b iht ihv ihb =>
    intro h
    rw [Expr.bvarBRaw_letE] at h ⊢
    have hb : b.bvarBRaw ≠ satRange := by
      intro hb'; rw [hb'] at h; simp at h; omega
    have hb2 : b.bvarBRaw < satRange := by
      have := Expr.bvarBRaw_lt b; simp [satRange] at *; omega
    rw [if_neg hb, iht (by omega), ihv (by omega), ihb hb2, Expr.bvarBound]
  | proj s i sub ih =>
    intro h
    rw [Expr.bvarBRaw_proj] at h ⊢
    rw [ih h, Expr.bvarBound]

/-- The packed fvar-range field is `Expr.fvarRange` wherever it did not
saturate. -/
theorem fvarBRaw_exact : ∀ e : ExprC, e.fvarBRaw < satRange →
    e.fvarBRaw = Expr.fvarRange e := by
  intro e
  induction e with
  | fvar idx _ _ _ => intro h; simp_all [satRange, Expr.fvarRange]; omega
  | bvar _ | sort _ | const _ _ | lit _ => intro _; simp [Expr.fvarRange]
  | app f a ihf iha =>
    intro h
    rw [Expr.fvarBRaw_app] at h ⊢
    rw [ihf (by omega), iha (by omega), Expr.fvarRange]
  | lam n ty b m iht ihb =>
    intro h
    rw [Expr.fvarBRaw_lam] at h ⊢
    rw [iht (by omega), ihb (by omega), Expr.fvarRange]
  | forallE n ty b m iht ihb =>
    intro h
    rw [Expr.fvarBRaw_forallE] at h ⊢
    rw [iht (by omega), ihb (by omega), Expr.fvarRange]
  | letE n ty v b iht ihv ihb =>
    intro h
    rw [Expr.fvarBRaw_letE] at h ⊢
    rw [iht (by omega), ihv (by omega), ihb (by omega), Expr.fvarRange]
  | proj s i sub ih =>
    intro h
    rw [Expr.fvarBRaw_proj] at h ⊢
    rw [ih h, Expr.fvarRange]

/-! ### The saturated branch: the memoized walks are the spec functions

The memo invariant is the usual one — every stored answer is the spec
function of its key — and the walks preserve it. -/

/-- The `bvarBound` walk's memo invariant. -/
def MemoBInv (memo : Std.HashMap ExprC Nat) : Prop :=
  ∀ (e : ExprC) (r : Nat), memo[e]? = some r → r = Expr.bvarBound e

theorem MemoBInv.empty : MemoBInv {} := by
  intro e r h; simp at h

theorem MemoBInv.insert {memo : Std.HashMap ExprC Nat} (hm : MemoBInv memo)
    {e : ExprC} {r : Nat} (heq : r = Expr.bvarBound e) :
    MemoBInv (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← (beq_iff_eq ..).mp hbeq]
    exact heq
  · exact hm e' r' hk

/-- **The memoized `bvarBound` walk agrees with `Expr.bvarBound`.** -/
theorem bvarBoundGo_spec : ∀ (e : ExprC) {memo : Std.HashMap ExprC Nat},
    MemoBInv memo →
      (Expr.bvarBoundGo memo e).1 = Expr.bvarBound e ∧
        MemoBInv (Expr.bvarBoundGo memo e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro memo hm
    rw [Expr.bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | fvar idx n ty _ | sort u | const n us | lit l =>
    intro memo hm
    rw [Expr.bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | app f a ihf iha =>
    intro memo hm
    rw [Expr.bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := ihf hm
      obtain ⟨h2, hm2⟩ := iha hm1
      refine ⟨by simp [h1, h2, Expr.bvarBound], hm2.insert ?_⟩
      simp [h1, h2, Expr.bvarBound]
  | lam n ty b m iht ihb | forallE n ty b m iht ihb =>
    intro memo hm
    rw [Expr.bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := iht hm
      obtain ⟨h2, hm2⟩ := ihb hm1
      refine ⟨by simp [h1, h2, Expr.bvarBound], hm2.insert ?_⟩
      simp [h1, h2, Expr.bvarBound]
  | letE n ty v b iht ihv ihb =>
    intro memo hm
    rw [Expr.bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := iht hm
      obtain ⟨h2, hm2⟩ := ihv hm1
      obtain ⟨h3, hm3⟩ := ihb hm2
      refine ⟨by simp [h1, h2, h3, Expr.bvarBound], hm3.insert ?_⟩
      simp [h1, h2, h3, Expr.bvarBound]
  | proj s i sub ih =>
    intro memo hm
    rw [Expr.bvarBoundGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := ih hm
      refine ⟨by simp [h1, Expr.bvarBound], hm1.insert ?_⟩
      simp [h1, Expr.bvarBound]

@[inherit_doc bvarBoundGo_spec]
theorem bvarBoundMemo_eq (e : ExprC) :
    Expr.bvarBoundMemo e = Expr.bvarBound e :=
  (bvarBoundGo_spec e MemoBInv.empty).1

/-- The `fvarRange` walk's memo invariant. -/
def MemoFInv (memo : Std.HashMap ExprC Nat) : Prop :=
  ∀ (e : ExprC) (r : Nat), memo[e]? = some r → r = Expr.fvarRange e

theorem MemoFInv.empty : MemoFInv {} := by
  intro e r h; simp at h

theorem MemoFInv.insert {memo : Std.HashMap ExprC Nat} (hm : MemoFInv memo)
    {e : ExprC} {r : Nat} (heq : r = Expr.fvarRange e) :
    MemoFInv (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← (beq_iff_eq ..).mp hbeq]
    exact heq
  · exact hm e' r' hk

/-- **The memoized `fvarRange` walk agrees with `Expr.fvarRange`.** -/
theorem fvarRangeGo_spec : ∀ (e : ExprC) {memo : Std.HashMap ExprC Nat},
    MemoFInv memo →
      (Expr.fvarRangeGo memo e).1 = Expr.fvarRange e ∧
        MemoFInv (Expr.fvarRangeGo memo e).2 := by
  intro e
  induction e with
  | fvar idx n ty _ =>
    intro memo hm
    rw [Expr.fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | bvar i | sort u | const n us | lit l =>
    intro memo hm
    rw [Expr.fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · exact ⟨rfl, hm.insert rfl⟩
  | app f a ihf iha =>
    intro memo hm
    rw [Expr.fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := ihf hm
      obtain ⟨h2, hm2⟩ := iha hm1
      refine ⟨by simp [h1, h2, Expr.fvarRange], hm2.insert ?_⟩
      simp [h1, h2, Expr.fvarRange]
  | lam n ty b m iht ihb | forallE n ty b m iht ihb =>
    intro memo hm
    rw [Expr.fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := iht hm
      obtain ⟨h2, hm2⟩ := ihb hm1
      refine ⟨by simp [h1, h2, Expr.fvarRange], hm2.insert ?_⟩
      simp [h1, h2, Expr.fvarRange]
  | letE n ty v b iht ihv ihb =>
    intro memo hm
    rw [Expr.fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := iht hm
      obtain ⟨h2, hm2⟩ := ihv hm1
      obtain ⟨h3, hm3⟩ := ihb hm2
      refine ⟨by simp [h1, h2, h3, Expr.fvarRange], hm3.insert ?_⟩
      simp [h1, h2, h3, Expr.fvarRange]
  | proj s i sub ih =>
    intro memo hm
    rw [Expr.fvarRangeGo.eq_def]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, hm1⟩ := ih hm
      refine ⟨by simp [h1, Expr.fvarRange], hm1.insert ?_⟩
      simp [h1, Expr.fvarRange]

@[inherit_doc fvarRangeGo_spec]
theorem fvarRangeMemo_eq (e : ExprC) :
    Expr.fvarRangeMemo e = Expr.fvarRange e :=
  (fvarRangeGo_spec e MemoFInv.empty).1

/-! ### The unconditional field equations -/

/-- The `bvarB` field is `Expr.bvarBound`. -/
theorem bvarB_eq : ∀ e : ExprC, e.bvarB = Expr.bvarBound e := by
  intro e
  show (if e.bvarBRaw == satRange then Expr.bvarBoundMemo e
    else e.bvarBRaw) = _
  split
  · rename_i h; exact bvarBoundMemo_eq e
  · rename_i h
    have hne : e.bvarBRaw ≠ satRange := by simpa using h
    have := Expr.bvarBRaw_lt e
    exact bvarBRaw_exact e (by simp [satRange] at *; omega)

/-- Cutoff consequence: a bound at or below the cursor certifies
`looseBVarsBounded` (the transposition of `TWF.bvarBoundD_le2`). -/
theorem bvarB_le {e : ExprC} {d : Nat} (hle : e.bvarB ≤ d) :
    Expr.looseBVarsBounded d e = true :=
  Expr.looseBVarsBounded_iff.mpr (bvarB_eq e ▸ hle)

/-- The `fvarB` field is `Expr.fvarRange`. -/
theorem fvarB_eq : ∀ e : ExprC, e.fvarB = Expr.fvarRange e := by
  intro e
  show (if e.fvarBRaw == satRange then Expr.fvarRangeMemo e
    else e.fvarBRaw) = _
  split
  · rename_i h; exact fvarRangeMemo_eq e
  · rename_i h
    have hne : e.fvarBRaw ≠ satRange := by simpa using h
    have := Expr.fvarBRaw_lt e
    exact fvarBRaw_exact e (by simp [satRange] at *; omega)

/-- Cutoff consequence: a range at or below the base certifies
`Expr.fvarsBelow` — the predicate the abstraction traversals consume
(`abstractRange_eq_self`); the transposition of `TWF.fvarRangeD_le`. -/
theorem fvarB_le {e : ExprC} {d : Nat} (hle : e.fvarB ≤ d) :
    Expr.fvarsBelow d e :=
  Expr.fvarsBelow_iff.mpr (fvarB_eq e ▸ hle)

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
    simp_all [Expr.hasLevelParam, levelHasParam_eq, levelsHaveParam_eq]

/-- Invisibility consequence: level instantiation is the identity on a
node whose flag is off (the `O(1)` shortcut every `instLevelParams`
traversal takes). -/
theorem hasLP_false {e : ExprC} {ks : List Name} {us : List Level}
    (h : e.hasLP = false) :
    e.instantiateLevelParams ks us = e :=
  Expr.instantiateLevelParams_eq_self (by rw [← hasLP_eq e, h])

/-! ## Equality

`beq` is `decide (· = ·)` (`Lech/Kernel/Expr.lean`): with the hash a
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
blocks could erase alike; B3b deleted the hypotheses with the
invariant.) -/
theorem beq_iff {a b : ExprC} : (a == b) = true ↔ a = b := beq_iff_eq

end ExprC

end Lech.Cached
