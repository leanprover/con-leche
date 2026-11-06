module

public import Lean.Expr
/- `Expr.Data.looseBVarRange` & co. and the computed field's equations are
not exposed by `Lean.Expr`/`Lean.Level`; the field lemmas below read them. -/
import all Lean.Expr
import all Lean.Level

/-!
# Stop-gap axioms: what C's `Expr.mkData` computes (task #451, lane G)

**Stop-gap, by the maintainer's ruling of 2026-11-04**, an explicit exception
to "no new axioms", confined to this one file: `InLean/*` is axiom-free,
con-leche's capstones and `tests/ConLecheTests/Axioms.lean` are untouched, and
only `InLeanProof/*` may depend on these.

**Why.**  InLean's cutoffs read Lean's cached fields (`looseBVarRange`,
`hasFVar`, `hasLevelParam`, …), and on the stock toolchain those are computed
by `@[extern] opaque` functions with no Lean definition, so no proof can say
what they are.

**What the lean4 branch does instead.**  It gives `Expr.mkData` & co. a Lean
body (`@[extern "lean_expr_mk_data"] def` with these right-hand sides), so the
statements below become theorems there.

**Removal.**  When InLean runs on a toolchain with those bodies: replace each
`axiom` by a theorem (`rfl`-like) and drop `scripts/inlean_mkdata_check.lean`.

**What is claimed.**  Only what C does when it returns:
`src/kernel/expr.cpp` `lean_expr_mk_data`, `lean_expr_mk_app_data`,
`src/kernel/level.cpp` `lean_level_mk_data`.  C panics on a range above
`1048575` or a level depth above `16777215`, and nothing is claimed there: the
two `mkData` axioms are conditional on the bound.

**Soundness.**  Nothing here quantifies over all `Expr`s; `Expr.bvar (2^20)`
exists in the logic.  That a term is in range is a hypothesis (`Expr.RangeOk`)
or a checked fact.  Each axiom is satisfiable: define the opaque function by
its right-hand side (`mkAppData` by C's formula).  `mkAppData` is stated by
its field equations alone, with no claim about the hash or the approximate
depth, which no proof reads.  `scripts/inlean_mkdata_check.lean` compares all
three with C on boundary and random inputs and on every node of `Init`.
-/

public section

namespace InLeanProof

open Lean

/-- The bound C's `lean_expr_mk_data` enforces. -/
abbrev maxRange : Nat := 1048575

/-- The bound C's `lean_level_mk_data` enforces. -/
abbrev maxLevelDepth : Nat := 16777215

/-- The value `lean_expr_mk_data` computes. -/
@[expose] def mkDataNat (h : UInt64) (r : Nat) (d : UInt32) (a b c e : Bool) : Nat :=
  h.toUInt32.toNat + (min 255 d.toNat) * 2 ^ 32 + a.toNat * 2 ^ 40 + b.toNat * 2 ^ 41 +
    c.toNat * 2 ^ 42 + e.toNat * 2 ^ 43 + r * 2 ^ 44

/-- The value `lean_level_mk_data` computes. -/
@[expose] def levelMkDataNat (h : UInt64) (d : Nat) (m p : Bool) : Nat :=
  h.toUInt32.toNat + m.toNat * 2 ^ 32 + p.toNat * 2 ^ 33 + d * 2 ^ 40

/-- **`Expr.mkData`**, `expr.cpp:105`, in range. -/
axiom Expr.mkData_eq (h : UInt64) (r : Nat) (d : UInt32) (a b c e : Bool) (hr : r ≤ maxRange) :
    Expr.mkData h r d a b c e = UInt64.ofNat (mkDataNat h r d a b c e)

/-- **`Expr.mkAppData`**, `expr.cpp:120`: the range is the maximum, the flags
the disjunction.  No claim about the hash or the approximate depth. -/
axiom Expr.mkAppData_fields (f a : Expr.Data) :
    (Expr.mkAppData f a).looseBVarRange.toNat = max f.looseBVarRange.toNat a.looseBVarRange.toNat ∧
    (Expr.mkAppData f a).hasFVar = (f.hasFVar || a.hasFVar) ∧
    (Expr.mkAppData f a).hasExprMVar = (f.hasExprMVar || a.hasExprMVar) ∧
    (Expr.mkAppData f a).hasLevelMVar = (f.hasLevelMVar || a.hasLevelMVar) ∧
    (Expr.mkAppData f a).hasLevelParam = (f.hasLevelParam || a.hasLevelParam)

/-- **`Level.mkData`**, `level.cpp:44`, in range. -/
axiom Level.mkData_eq (h : UInt64) (d : Nat) (m p : Bool) (hd : d ≤ maxLevelDepth) :
    Level.mkData h d m p = UInt64.ofNat (levelMkDataNat h d m p)

/-! ## The field lemmas (theorems, from the axioms) -/

theorem flag_read (x k : UInt64) (hk : k.toNat < 64) :
    ((x.shiftRight k).land 1 == 1) = decide (x.toNat / 2 ^ k.toNat % 2 = 1) := by
  have h : ((x >>> k) &&& 1).toNat = x.toNat / 2 ^ k.toNat % 2 := by
    simp [UInt64.toNat_shiftRight, UInt64.toNat_and, Nat.shiftRight_eq_div_pow,
      Nat.and_one_is_mod, Nat.mod_eq_of_lt hk]
  have hiff : (((x >>> k) &&& 1) = 1) ↔ x.toNat / 2 ^ k.toNat % 2 = 1 := by
    rw [← h, ← UInt64.toNat_inj]; rfl
  show (((x >>> k) &&& 1) == 1) = _
  rw [Bool.eq_iff_iff]; simp [hiff]

theorem shiftRight_toNat (x k : UInt64) (hk : k.toNat < 64) :
    (x.shiftRight k).toNat = x.toNat / 2 ^ k.toNat := by
  show (x >>> k).toNat = _
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hk]

/-! ### Reading the fields of a word -/

theorem Data.range_read (x : Expr.Data) :
    x.looseBVarRange.toNat = UInt64.toNat x / 2 ^ 44 := by
  have hx : UInt64.toNat x < 2 ^ 64 := UInt64.toNat_lt x
  have h : (UInt64.shiftRight x 44).toNat = UInt64.toNat x / 2 ^ 44 :=
    shiftRight_toNat x 44 (by decide)
  show (UInt64.shiftRight x 44).toUInt32.toNat = _
  rw [UInt64.toNat_toUInt32, h]
  omega

theorem Data.fvar_read (x : Expr.Data) : x.hasFVar = decide (UInt64.toNat x / 2 ^ 40 % 2 = 1) :=
  flag_read x 40 (by decide)

theorem Data.emvar_read (x : Expr.Data) :
    x.hasExprMVar = decide (UInt64.toNat x / 2 ^ 41 % 2 = 1) :=
  flag_read x 41 (by decide)

theorem Data.lmvar_read (x : Expr.Data) :
    x.hasLevelMVar = decide (UInt64.toNat x / 2 ^ 42 % 2 = 1) :=
  flag_read x 42 (by decide)

theorem Data.lparam_read (x : Expr.Data) :
    x.hasLevelParam = decide (UInt64.toNat x / 2 ^ 43 % 2 = 1) :=
  flag_read x 43 (by decide)

theorem Level.Data.depth_read (x : Level.Data) : x.depth.toNat = UInt64.toNat x / 2 ^ 40 % 2 ^ 32 := by
  have h : (UInt64.shiftRight x 40).toNat = UInt64.toNat x / 2 ^ 40 :=
    shiftRight_toNat x 40 (by decide)
  show (UInt64.shiftRight x 40).toUInt32.toNat = _
  rw [UInt64.toNat_toUInt32, h]

theorem Level.Data.mvar_read (x : Level.Data) : x.hasMVar = decide (UInt64.toNat x / 2 ^ 32 % 2 = 1) :=
  flag_read x 32 (by decide)

theorem Level.Data.param_read (x : Level.Data) : x.hasParam = decide (UInt64.toNat x / 2 ^ 33 % 2 = 1) :=
  flag_read x 33 (by decide)

/-! ### `Expr.mkData`'s fields -/

section fields
variable (h : UInt64) (r : Nat) (d : UInt32) (a b c e : Bool) (hr : r ≤ maxRange)
include hr

theorem mkData_toNat :
    UInt64.toNat (Expr.mkData h r d a b c e) = mkDataNat h r d a b c e := by
  have h1 : h.toUInt32.toNat < 2 ^ 32 := h.toUInt32.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  have hr' : r ≤ 1048575 := hr
  have hlt : mkDataNat h r d a b c e < 2 ^ 64 := by
    unfold mkDataNat
    cases a <;> cases b <;> cases c <;> cases e <;>
      simp only [Bool.toNat_true, Bool.toNat_false] <;> omega
  rw [Expr.mkData_eq h r d a b c e hr, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]

theorem mkData_looseBVarRange : (Expr.mkData h r d a b c e).looseBVarRange.toNat = r := by
  have h1 : h.toUInt32.toNat < 2 ^ 32 := h.toUInt32.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  rw [Data.range_read, mkData_toNat h r d a b c e hr]
  unfold mkDataNat
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false] <;> omega

theorem mkData_hasFVar : (Expr.mkData h r d a b c e).hasFVar = a := by
  have h1 : h.toUInt32.toNat < 2 ^ 32 := h.toUInt32.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  rw [Data.fvar_read, mkData_toNat h r d a b c e hr]
  unfold mkDataNat
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

theorem mkData_hasExprMVar : (Expr.mkData h r d a b c e).hasExprMVar = b := by
  have h1 : h.toUInt32.toNat < 2 ^ 32 := h.toUInt32.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  rw [Data.emvar_read, mkData_toNat h r d a b c e hr]
  unfold mkDataNat
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

theorem mkData_hasLevelMVar : (Expr.mkData h r d a b c e).hasLevelMVar = c := by
  have h1 : h.toUInt32.toNat < 2 ^ 32 := h.toUInt32.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  rw [Data.lmvar_read, mkData_toNat h r d a b c e hr]
  unfold mkDataNat
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

theorem mkData_hasLevelParam : (Expr.mkData h r d a b c e).hasLevelParam = e := by
  have h1 : h.toUInt32.toNat < 2 ^ 32 := h.toUInt32.toNat_lt
  have h2 : min 255 d.toNat ≤ 255 := Nat.min_le_left _ _
  rw [Data.lparam_read, mkData_toNat h r d a b c e hr]
  unfold mkDataNat
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp only [Bool.toNat_true, Bool.toNat_false, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

end fields

/-! ### `Level.mkData`'s fields -/

section levelFields
variable (h : UInt64) (dp : Nat) (m p : Bool) (hd : dp ≤ maxLevelDepth)
include hd

theorem levelMkData_toNat :
    UInt64.toNat (Level.mkData h dp m p) = levelMkDataNat h dp m p := by
  have h1 : h.toUInt32.toNat < 2 ^ 32 := h.toUInt32.toNat_lt
  have hd' : dp ≤ 16777215 := hd
  have hlt : levelMkDataNat h dp m p < 2 ^ 64 := by
    unfold levelMkDataNat
    cases m <;> cases p <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> omega
  rw [Level.mkData_eq h dp m p hd, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]

theorem levelMkData_depth : (Level.mkData h dp m p).depth.toNat = dp := by
  have h1 : h.toUInt32.toNat < 2 ^ 32 := h.toUInt32.toNat_lt
  have hd' : dp ≤ 16777215 := hd
  rw [Level.Data.depth_read, levelMkData_toNat h dp m p hd]
  unfold levelMkDataNat
  cases m <;> cases p <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> omega

theorem levelMkData_hasMVar : (Level.mkData h dp m p).hasMVar = m := by
  have h1 : h.toUInt32.toNat < 2 ^ 32 := h.toUInt32.toNat_lt
  rw [Level.Data.mvar_read, levelMkData_toNat h dp m p hd]
  unfold levelMkDataNat
  cases m <;> cases p <;>
    simp only [Bool.toNat_true, Bool.toNat_false, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

theorem levelMkData_hasParam : (Level.mkData h dp m p).hasParam = p := by
  have h1 : h.toUInt32.toNat < 2 ^ 32 := h.toUInt32.toNat_lt
  rw [Level.Data.param_read, levelMkData_toNat h dp m p hd]
  unfold levelMkDataNat
  cases m <;> cases p <;>
    simp only [Bool.toNat_true, Bool.toNat_false, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

end levelFields

end InLeanProof
