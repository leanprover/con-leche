import Setlec.TT.Judgment

/-!
# The substitution algebra of `VExpr`

The commutation identities between `VExpr.liftN` and `VExpr.inst`
(`Setlec/TT/Subst.lean`), plus their consequences for the types of the
built-in constants and for the smart constructors that appear in the
rules of `HasType`.  They exist to serve
`Setlec/TTVerify/HasTypeSubst.lean`, which needs lifting and
instantiation to commute in every rule whose conclusion mentions
`inst` or an inner `liftN`.

**Why this lives on the bridge side and not in `Setlec/TT/*`.**  The
layer deliberately has *no syntactic metatheory* —
`Setlec/TT/Subst.lean` is definitions plus constructor-wise `rfl`
equations, and advertises that (lean4lean's counterpart is ~123
theorems).  These identities are a bridge need, exactly like
`Setlec/TTVerify/Weaken.lean` and `Setlec/TTVerify/Inversion.lean`, so
they are filed with the bridge to keep the accounting honest.

Every identity is proved by structural induction on the expression
with the cuts generalized; the `bvar` cases are `omega` case splits and
everything else is congruence.
-/

namespace Setlec.TT
namespace VExpr

/-! ## Lift / lift -/

/-- Lifting by zero is the identity — the degenerate case the
substitution lemma leaves behind at the outermost binder. -/
theorem liftN_zero : ∀ (e : VExpr) (k : Nat), VExpr.liftN 0 e k = e := by
  intro e
  induction e <;> intro k <;>
    simp_all [VExpr.liftN]

/-- Two lifts at the same cut compose by addition. -/
theorem liftN_liftN_add : ∀ (e : VExpr) (m n k : Nat),
    liftN n (liftN m e k) k = liftN (m + n) e k := by
  intro e
  induction e with
  | bvar i =>
    intro m n k
    simp only [liftN_bvar]
    by_cases h : i < k
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg (show ¬ i + m < k by omega)]
      congr 1; omega
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f a ihf iha => intro m n k; simp only [liftN_app, ihf, iha]
  | lam A b ihA ihb => intro m n k; simp only [liftN_lam, ihA, ihb]
  | pi A B ihA ihB => intro m n k; simp only [liftN_pi, ihA, ihB]
  | letE T v b ihT ihv ihb =>
    intro m n k; simp only [liftN_letE, ihT, ihv, ihb]
  | eqE T a b ihT iha ihb =>
    intro m n k; simp only [liftN_eqE, ihT, iha, ihb]
  | proj i e ihe => intro m n k; simp only [liftN_proj, ihe]

/-- A lift at a low cut moves past a lift at a high cut, pushing the
high cut up by the amount of the low lift. -/
theorem liftN_liftN_comm : ∀ (e : VExpr) {j k : Nat}, j ≤ k →
    ∀ (m n : Nat), liftN m (liftN n e k) j = liftN n (liftN m e j) (k + m) := by
  intro e
  induction e with
  | bvar i =>
    intro j k hjk m n
    by_cases h1 : i < j
    · simp only [liftN_bvar, if_pos h1, if_pos (show i < k by omega),
        if_pos (show i < k + m by omega)]
    · by_cases h2 : i < k
      · simp only [liftN_bvar, if_neg h1, if_pos h2,
          if_pos (show i + m < k + m by omega)]
      · simp only [liftN_bvar, if_neg h1, if_neg h2,
          if_neg (show ¬ i + n < j by omega),
          if_neg (show ¬ i + m < k + m by omega)]
        congr 1; omega
  | sort u => intro _ _ _ _ _; rfl
  | const c us => intro _ _ _ _ _; rfl
  | prf => intro _ _ _ _ _; rfl
  | app f a ihf iha =>
    intro j k hjk m n
    simp only [liftN_app, ihf hjk, iha hjk]
  | lam A b ihA ihb =>
    intro j k hjk m n
    simp only [liftN_lam, ihA hjk, ihb (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 + m = k + m + 1 by omega]
  | pi A B ihA ihB =>
    intro j k hjk m n
    simp only [liftN_pi, ihA hjk, ihB (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 + m = k + m + 1 by omega]
  | letE T v b ihT ihv ihb =>
    intro j k hjk m n
    simp only [liftN_letE, ihT hjk, ihv hjk, ihb (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 + m = k + m + 1 by omega]
  | eqE T a b ihT iha ihb =>
    intro j k hjk m n
    simp only [liftN_eqE, ihT hjk, iha hjk, ihb hjk]
  | proj i e ihe =>
    intro j k hjk m n
    simp only [liftN_proj, ihe hjk]

/-- A lift whose cut lands inside the range opened by an earlier lift
is absorbed into it. -/
theorem liftN_liftN_absorb : ∀ (e : VExpr) {j k m : Nat}, k ≤ j → j ≤ k + m →
    ∀ (n : Nat), liftN n (liftN m e k) j = liftN (m + n) e k := by
  intro e
  induction e with
  | bvar i =>
    intro j k m h1 h2 n
    simp only [liftN_bvar]
    by_cases h : i < k
    · rw [if_pos h, if_pos (show i < j by omega), if_pos h]
    · rw [if_neg h, if_neg (show ¬ i + m < j by omega), if_neg h]
      congr 1; omega
  | sort u => intro _ _ _ _ _ _; rfl
  | const c us => intro _ _ _ _ _ _; rfl
  | prf => intro _ _ _ _ _ _; rfl
  | app f a ihf iha =>
    intro j k m h1 h2 n
    simp only [liftN_app, ihf h1 h2, iha h1 h2]
  | lam A b ihA ihb =>
    intro j k m h1 h2 n
    simp only [liftN_lam, ihA h1 h2,
      ihb (show k + 1 ≤ j + 1 by omega) (show j + 1 ≤ k + 1 + m by omega)]
  | pi A B ihA ihB =>
    intro j k m h1 h2 n
    simp only [liftN_pi, ihA h1 h2,
      ihB (show k + 1 ≤ j + 1 by omega) (show j + 1 ≤ k + 1 + m by omega)]
  | letE T v b ihT ihv ihb =>
    intro j k m h1 h2 n
    simp only [liftN_letE, ihT h1 h2, ihv h1 h2,
      ihb (show k + 1 ≤ j + 1 by omega) (show j + 1 ≤ k + 1 + m by omega)]
  | eqE T a b ihT iha ihb =>
    intro j k m h1 h2 n
    simp only [liftN_eqE, ihT h1 h2, iha h1 h2, ihb h1 h2]
  | proj i e ihe =>
    intro j k m h1 h2 n
    simp only [liftN_proj, ihe h1 h2]

/-! ## Lift / inst -/

/-- Lifting an instantiated term: the lift moves inside, its cut
stepping over the removed binder, and hits the substituted term at the
distance between the two cuts. -/
theorem liftN_inst_comm : ∀ (e : VExpr) {j k : Nat}, j ≤ k →
    ∀ (a : VExpr) (n : Nat),
    liftN n (inst e a j) k = inst (liftN n e (k + 1)) (liftN n a (k - j)) j := by
  intro e
  induction e with
  | bvar i =>
    intro j k hjk a n
    by_cases h1 : i < j
    · simp only [inst_bvar, liftN_bvar, if_pos h1, if_pos (show i < k by omega),
        if_pos (show i < k + 1 by omega)]
    · by_cases h2 : i = j
      · simp only [inst_bvar, liftN_bvar, if_neg h1, if_pos h2,
          if_pos (show i < k + 1 by omega)]
        rw [liftN_liftN_comm a (Nat.zero_le (k - j)) j n,
          show k - j + j = k by omega]
      · by_cases h3 : i < k + 1
        · simp only [inst_bvar, liftN_bvar, if_neg h1, if_neg h2, if_pos h3,
            if_pos (show i - 1 < k by omega)]
        · simp only [inst_bvar, liftN_bvar, if_neg h1, if_neg h2, if_neg h3,
            if_neg (show ¬ i - 1 < k by omega),
            if_neg (show ¬ i + n < j by omega),
            if_neg (show ¬ i + n = j by omega)]
          congr 1; omega
  | sort u => intro _ _ _ _ _; rfl
  | const c us => intro _ _ _ _ _; rfl
  | prf => intro _ _ _ _ _; rfl
  | app f b ihf ihb =>
    intro j k hjk a n
    simp only [inst_app, liftN_app, ihf hjk, ihb hjk]
  | lam A b ihA ihb =>
    intro j k hjk a n
    simp only [inst_lam, liftN_lam, ihA hjk, ihb (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | pi A B ihA ihB =>
    intro j k hjk a n
    simp only [inst_pi, liftN_pi, ihA hjk, ihB (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | letE T v b ihT ihv ihb =>
    intro j k hjk a n
    simp only [inst_letE, liftN_letE, ihT hjk, ihv hjk,
      ihb (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | eqE T b c ihT ihb ihc =>
    intro j k hjk a n
    simp only [inst_eqE, liftN_eqE, ihT hjk, ihb hjk, ihc hjk]
  | proj i e ihe =>
    intro j k hjk a n
    simp only [inst_proj, liftN_proj, ihe hjk]

/-- Instantiating strictly above a lift: the instantiation moves under
the lift, its cut shrunk by the lift amount. -/
theorem inst_liftN_comm : ∀ (e : VExpr) {j k m : Nat}, j + m ≤ k →
    ∀ (a : VExpr),
    inst (liftN m e j) a k = liftN m (inst e a (k - m)) j := by
  intro e
  induction e with
  | bvar i =>
    intro j k m hjk a
    by_cases h1 : i < j
    · simp only [liftN_bvar, inst_bvar, if_pos h1, if_pos (show i < k by omega),
        if_pos (show i < k - m by omega)]
    · by_cases h2 : i < k - m
      · simp only [liftN_bvar, inst_bvar, if_neg h1, if_pos h2,
          if_pos (show i + m < k by omega)]
      · by_cases h3 : i = k - m
        · simp only [liftN_bvar, inst_bvar, if_neg h1, if_neg h2, if_pos h3,
            if_neg (show ¬ i + m < k by omega),
            if_pos (show i + m = k by omega)]
          rw [liftN_liftN_absorb a (Nat.zero_le j)
              (show j ≤ 0 + (k - m) by omega) m,
            show k - m + m = k by omega]
        · simp only [liftN_bvar, inst_bvar, if_neg h1, if_neg h2, if_neg h3,
            if_neg (show ¬ i + m < k by omega),
            if_neg (show ¬ i + m = k by omega),
            if_neg (show ¬ i - 1 < j by omega)]
          congr 1; omega
  | sort u => intro _ _ _ _ _; rfl
  | const c us => intro _ _ _ _ _; rfl
  | prf => intro _ _ _ _ _; rfl
  | app f b ihf ihb =>
    intro j k m hjk a
    simp only [liftN_app, inst_app, ihf hjk, ihb hjk]
  | lam A b ihA ihb =>
    intro j k m hjk a
    simp only [liftN_lam, inst_lam, ihA hjk,
      ihb (show j + 1 + m ≤ k + 1 by omega)]
    rw [show k + 1 - m = k - m + 1 by omega]
  | pi A B ihA ihB =>
    intro j k m hjk a
    simp only [liftN_pi, inst_pi, ihA hjk,
      ihB (show j + 1 + m ≤ k + 1 by omega)]
    rw [show k + 1 - m = k - m + 1 by omega]
  | letE T v b ihT ihv ihb =>
    intro j k m hjk a
    simp only [liftN_letE, inst_letE, ihT hjk, ihv hjk,
      ihb (show j + 1 + m ≤ k + 1 by omega)]
    rw [show k + 1 - m = k - m + 1 by omega]
  | eqE T b c ihT ihb ihc =>
    intro j k m hjk a
    simp only [liftN_eqE, inst_eqE, ihT hjk, ihb hjk, ihc hjk]
  | proj i e ihe =>
    intro j k m hjk a
    simp only [liftN_proj, inst_proj, ihe hjk]

/-- Instantiating a variable that a lift just introduced: the
substitution cancels one unit of the lift and the substituted term
never appears. -/
theorem inst_liftN_absorb : ∀ (e : VExpr) {j k m : Nat}, j ≤ k → k ≤ j + m →
    ∀ (a : VExpr),
    inst (liftN (m + 1) e j) a k = liftN m e j := by
  intro e
  induction e with
  | bvar i =>
    intro j k m h1 h2 a
    simp only [liftN_bvar]
    by_cases h : i < j
    · rw [if_pos h, if_pos h, inst_bvar, if_pos (show i < k by omega)]
    · rw [if_neg h, if_neg h, inst_bvar,
        if_neg (show ¬ i + (m + 1) < k by omega),
        if_neg (show ¬ i + (m + 1) = k by omega)]
      exact congrArg VExpr.bvar (by omega)
  | sort u => intro _ _ _ _ _ _; rfl
  | const c us => intro _ _ _ _ _ _; rfl
  | prf => intro _ _ _ _ _ _; rfl
  | app f b ihf ihb =>
    intro j k m h1 h2 a
    simp only [liftN_app, inst_app, ihf h1 h2, ihb h1 h2]
  | lam A b ihA ihb =>
    intro j k m h1 h2 a
    simp only [liftN_lam, inst_lam, ihA h1 h2,
      ihb (show j + 1 ≤ k + 1 by omega) (show k + 1 ≤ j + 1 + m by omega)]
  | pi A B ihA ihB =>
    intro j k m h1 h2 a
    simp only [liftN_pi, inst_pi, ihA h1 h2,
      ihB (show j + 1 ≤ k + 1 by omega) (show k + 1 ≤ j + 1 + m by omega)]
  | letE T v b ihT ihv ihb =>
    intro j k m h1 h2 a
    simp only [liftN_letE, inst_letE, ihT h1 h2, ihv h1 h2,
      ihb (show j + 1 ≤ k + 1 by omega) (show k + 1 ≤ j + 1 + m by omega)]
  | eqE T b c ihT ihb ihc =>
    intro j k m h1 h2 a
    simp only [liftN_eqE, inst_eqE, ihT h1 h2, ihb h1 h2, ihc h1 h2]
  | proj i e ihe =>
    intro j k m h1 h2 a
    simp only [liftN_proj, inst_proj, ihe h1 h2]

/-! ## Inst / inst -/

/-- Two instantiations commute: the outer one moves inside (its cut
stepping over the inner one's removed binder) and hits the inner
substituted term at the distance between the cuts. -/
theorem inst_inst_comm : ∀ (e : VExpr) {j k : Nat}, j ≤ k →
    ∀ (a b : VExpr),
    inst (inst e b j) a k = inst (inst e a (k + 1)) (inst b a (k - j)) j := by
  intro e
  induction e with
  | bvar i =>
    intro j k hjk a b
    by_cases h1 : i < j
    · simp only [inst_bvar, if_pos h1, if_pos (show i < k by omega),
        if_pos (show i < k + 1 by omega)]
    · by_cases h2 : i = j
      · simp only [inst_bvar, if_neg h1, if_pos h2,
          if_pos (show i < k + 1 by omega)]
        rw [inst_liftN_comm b (show 0 + j ≤ k by omega) a]
      · by_cases h3 : i < k + 1
        · simp only [inst_bvar, if_neg h1, if_neg h2, if_pos h3,
            if_pos (show i - 1 < k by omega)]
        · by_cases h4 : i = k + 1
          · simp only [inst_bvar, if_neg h1, if_neg h2, if_neg h3, if_pos h4,
              if_neg (show ¬ i - 1 < k by omega),
              if_pos (show i - 1 = k by omega)]
            rw [inst_liftN_absorb a (Nat.zero_le j) (show j ≤ 0 + k by omega)]
          · simp only [inst_bvar, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
              if_neg (show ¬ i - 1 < k by omega),
              if_neg (show ¬ i - 1 = k by omega),
              if_neg (show ¬ i - 1 < j by omega),
              if_neg (show ¬ i - 1 = j by omega)]
  | sort u => intro _ _ _ _ _; rfl
  | const c us => intro _ _ _ _ _; rfl
  | prf => intro _ _ _ _ _; rfl
  | app f c ihf ihc =>
    intro j k hjk a b
    simp only [inst_app, ihf hjk, ihc hjk]
  | lam A c ihA ihc =>
    intro j k hjk a b
    simp only [inst_lam, ihA hjk, ihc (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | pi A B ihA ihB =>
    intro j k hjk a b
    simp only [inst_pi, ihA hjk, ihB (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | letE T v c ihT ihv ihc =>
    intro j k hjk a b
    simp only [inst_letE, ihT hjk, ihv hjk, ihc (show j + 1 ≤ k + 1 by omega)]
    rw [show k + 1 - (j + 1) = k - j by omega]
  | eqE T c d ihT ihc ihd =>
    intro j k hjk a b
    simp only [inst_eqE, ihT hjk, ihc hjk, ihd hjk]
  | proj i e ihe =>
    intro j k hjk a b
    simp only [inst_proj, ihe hjk]

end VExpr

/-! ## The built-in constants' types are closed -/

/-- Lifting is the identity on the (closed) type of a built-in
constant. -/
@[simp] theorem BConst.liftN_type (c : BConst) (us : List Nat) (n k : Nat) :
    (c.type us).liftN n k = c.type us := by
  cases c <;>
    simp +arith [BConst.type, natT, natZeroT, natSuccT, punitT, punitUnitT,
      psigmaT, quotT, quotMkT, relT, arrow, emptyT, negT, VExpr.lift]

/-- Instantiation is the identity on the (closed) type of a built-in
constant. -/
@[simp] theorem BConst.inst_type (c : BConst) (us : List Nat) (a : VExpr)
    (k : Nat) : (c.type us).inst a k = c.type us := by
  cases c <;>
    simp +arith [BConst.type, natT, natZeroT, natSuccT, punitT, punitUnitT,
      psigmaT, quotT, quotMkT, relT, arrow, emptyT, negT, VExpr.lift]

/-! ## Distribution over the smart constructors

The rules of `HasType` are written with the smart constructors of
`Setlec/TT/Const.lean` and the premise-type formers `natStepT` /
`quotInvT` (`Setlec/TT/Judgment.lean`).  The lemmas below push `liftN`
and `inst` through each of them, so that the `HasType` inductions can
normalize every rule's premises and conclusion by `simp only`.  The
applicative ones are `rfl`; `arrow`, `relT`, `natStepT` and `quotInvT`
contain inner lifts and need the commutation identities above. -/

section Distrib
open VExpr

variable (a : VExpr) (n k : Nat)

@[simp] theorem liftN_natT : natT.liftN n k = natT := rfl
@[simp] theorem inst_natT : natT.inst a k = natT := rfl
@[simp] theorem liftN_natZeroT : natZeroT.liftN n k = natZeroT := rfl
@[simp] theorem inst_natZeroT : natZeroT.inst a k = natZeroT := rfl
@[simp] theorem liftN_punitT (u : Nat) : (punitT u).liftN n k = punitT u := rfl
@[simp] theorem inst_punitT (u : Nat) : (punitT u).inst a k = punitT u := rfl
@[simp] theorem liftN_punitUnitT (u : Nat) :
    (punitUnitT u).liftN n k = punitUnitT u := rfl
@[simp] theorem inst_punitUnitT (u : Nat) :
    (punitUnitT u).inst a k = punitUnitT u := rfl

@[simp] theorem liftN_natSuccT (e : VExpr) :
    (natSuccT e).liftN n k = natSuccT (e.liftN n k) := rfl
@[simp] theorem inst_natSuccT (e : VExpr) :
    (natSuccT e).inst a k = natSuccT (e.inst a k) := rfl

@[simp] theorem liftN_natRecT (u : Nat) (M z s t : VExpr) :
    (natRecT u M z s t).liftN n k =
      natRecT u (M.liftN n k) (z.liftN n k) (s.liftN n k) (t.liftN n k) := rfl
@[simp] theorem inst_natRecT (u : Nat) (M z s t : VExpr) :
    (natRecT u M z s t).inst a k =
      natRecT u (M.inst a k) (z.inst a k) (s.inst a k) (t.inst a k) := rfl

@[simp] theorem liftN_punitRecT (u v : Nat) (M m t : VExpr) :
    (punitRecT u v M m t).liftN n k =
      punitRecT u v (M.liftN n k) (m.liftN n k) (t.liftN n k) := rfl
@[simp] theorem inst_punitRecT (u v : Nat) (M m t : VExpr) :
    (punitRecT u v M m t).inst a k =
      punitRecT u v (M.inst a k) (m.inst a k) (t.inst a k) := rfl

@[simp] theorem liftN_psigmaT (u v : Nat) (A B : VExpr) :
    (psigmaT u v A B).liftN n k = psigmaT u v (A.liftN n k) (B.liftN n k) := rfl
@[simp] theorem inst_psigmaT (u v : Nat) (A B : VExpr) :
    (psigmaT u v A B).inst a k = psigmaT u v (A.inst a k) (B.inst a k) := rfl

@[simp] theorem liftN_psigmaMkT (u v : Nat) (A B x y : VExpr) :
    (psigmaMkT u v A B x y).liftN n k =
      psigmaMkT u v (A.liftN n k) (B.liftN n k) (x.liftN n k) (y.liftN n k) := rfl
@[simp] theorem inst_psigmaMkT (u v : Nat) (A B x y : VExpr) :
    (psigmaMkT u v A B x y).inst a k =
      psigmaMkT u v (A.inst a k) (B.inst a k) (x.inst a k) (y.inst a k) := rfl

@[simp] theorem liftN_pfstT (p : VExpr) :
    (pfstT p).liftN n k = pfstT (p.liftN n k) := rfl
@[simp] theorem inst_pfstT (p : VExpr) :
    (pfstT p).inst a k = pfstT (p.inst a k) := rfl
@[simp] theorem liftN_psndT (p : VExpr) :
    (psndT p).liftN n k = psndT (p.liftN n k) := rfl
@[simp] theorem inst_psndT (p : VExpr) :
    (psndT p).inst a k = psndT (p.inst a k) := rfl

@[simp] theorem liftN_quotMkT (u : Nat) (A r x : VExpr) :
    (quotMkT u A r x).liftN n k =
      quotMkT u (A.liftN n k) (r.liftN n k) (x.liftN n k) := rfl
@[simp] theorem inst_quotMkT (u : Nat) (A r x : VExpr) :
    (quotMkT u A r x).inst a k =
      quotMkT u (A.inst a k) (r.inst a k) (x.inst a k) := rfl

@[simp] theorem liftN_quotLiftT (u v : Nat) (A r B f h q : VExpr) :
    (quotLiftT u v A r B f h q).liftN n k =
      quotLiftT u v (A.liftN n k) (r.liftN n k) (B.liftN n k) (f.liftN n k)
        (h.liftN n k) (q.liftN n k) := rfl
@[simp] theorem inst_quotLiftT (u v : Nat) (A r B f h q : VExpr) :
    (quotLiftT u v A r B f h q).inst a k =
      quotLiftT u v (A.inst a k) (r.inst a k) (B.inst a k) (f.inst a k)
        (h.inst a k) (q.inst a k) := rfl

@[simp] theorem liftN_arrow (A B : VExpr) :
    (arrow A B).liftN n k = arrow (A.liftN n k) (B.liftN n k) := by
  simp only [arrow, liftN_pi, VExpr.lift]
  rw [liftN_liftN_comm B (Nat.zero_le k) 1 n]

@[simp] theorem inst_arrow (A B : VExpr) :
    (arrow A B).inst a k = arrow (A.inst a k) (B.inst a k) := by
  simp only [arrow, inst_pi, VExpr.lift]
  rw [inst_liftN_comm B (show 0 + 1 ≤ k + 1 by omega) a,
    Nat.add_sub_cancel]

@[simp] theorem liftN_relT (A : VExpr) :
    (relT A).liftN n k = relT (A.liftN n k) := by
  simp only [relT, liftN_pi, liftN_sort, VExpr.lift]
  rw [liftN_liftN_comm A (Nat.zero_le k) 1 n]

@[simp] theorem inst_relT (A : VExpr) :
    (relT A).inst a k = relT (A.inst a k) := by
  simp only [relT, inst_pi, inst_sort, VExpr.lift]
  rw [inst_liftN_comm A (show 0 + 1 ≤ k + 1 by omega) a, Nat.add_sub_cancel]

@[simp] theorem liftN_natStepT (M : VExpr) :
    (natStepT M).liftN n k = natStepT (M.liftN n k) := by
  simp only [natStepT, liftN_pi, liftN_app, liftN_natT, liftN_natSuccT,
    liftN_bvar, if_pos (show (0:Nat) < k + 1 by omega),
    if_pos (show (1:Nat) < k + 1 + 1 by omega)]
  rw [liftN_liftN_comm M (Nat.zero_le k) 1 n,
    liftN_liftN_comm M (Nat.zero_le k) 2 n]

@[simp] theorem inst_natStepT (M : VExpr) :
    (natStepT M).inst a k = natStepT (M.inst a k) := by
  simp only [natStepT, inst_pi, inst_app, inst_natT, inst_natSuccT, inst_bvar,
    if_pos (show (0:Nat) < k + 1 by omega),
    if_pos (show (1:Nat) < k + 1 + 1 by omega)]
  rw [inst_liftN_comm M (show 0 + 1 ≤ k + 1 by omega) a,
    inst_liftN_comm M (show 0 + 2 ≤ k + 1 + 1 by omega) a]
  simp

@[simp] theorem liftN_quotInvT (A r B f : VExpr) :
    (quotInvT A r B f).liftN n k =
      quotInvT (A.liftN n k) (r.liftN n k) (B.liftN n k) (f.liftN n k) := by
  simp only [quotInvT, liftN_pi, liftN_eqE, liftN_app, mkAppN_cons, mkAppN_nil,
    liftN_bvar, if_pos (show (1:Nat) < k + 1 + 1 + 1 by omega),
    if_pos (show (2:Nat) < k + 1 + 1 + 1 by omega),
    if_pos (show (1:Nat) < k + 1 + 1 by omega),
    if_pos (show (0:Nat) < k + 1 + 1 by omega)]
  rw [liftN_liftN_comm A (Nat.zero_le k) 1 n,
    liftN_liftN_comm r (Nat.zero_le k) 2 n,
    liftN_liftN_comm B (Nat.zero_le k) 3 n,
    liftN_liftN_comm f (Nat.zero_le k) 3 n]

@[simp] theorem inst_quotInvT (A r B f : VExpr) :
    (quotInvT A r B f).inst a k =
      quotInvT (A.inst a k) (r.inst a k) (B.inst a k) (f.inst a k) := by
  simp only [quotInvT, inst_pi, inst_eqE, inst_app, mkAppN_cons, mkAppN_nil,
    inst_bvar, if_pos (show (1:Nat) < k + 1 + 1 + 1 by omega),
    if_pos (show (2:Nat) < k + 1 + 1 + 1 by omega),
    if_pos (show (1:Nat) < k + 1 + 1 by omega),
    if_pos (show (0:Nat) < k + 1 + 1 by omega)]
  rw [inst_liftN_comm A (show 0 + 1 ≤ k + 1 by omega) a,
    inst_liftN_comm r (show 0 + 2 ≤ k + 1 + 1 by omega) a,
    inst_liftN_comm B (show 0 + 3 ≤ k + 1 + 1 + 1 by omega) a,
    inst_liftN_comm f (show 0 + 3 ≤ k + 1 + 1 + 1 by omega) a]
  simp

end Distrib

end Setlec.TT
