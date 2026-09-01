import Setlec.SetR.Annot.Bit
import Setlec.SetR.Annot.Ok2

/-!
# `AnnotValidV` — bit validity, on the bit (task #161, P3.2)

The regime numerals of a `denoteP` image are *claims* — the input's
own validated annotations, read at a ground valuation.  `interp2`
dispatches on them (`piR`/`lamR`), so the soundness ladder needs, at
exactly one place per binder former, that the claimed bit is
semantically right.  `AnnotValidV` is that predicate, and nothing
else:

* **the `pi` clause carries the bit component** — `v = 0 → the
  codomain fibres are truth values` — the fact `AnnotOk2` does *not*
  carry at `pi` (its app clause carries the kind package, its λ clause
  the fibre package, but a bare product's regime has no home there);
* **the λ clause carries nothing** — the λ-side regime facts live in
  `AnnotOk2`'s λ clause already (`∃ B, fibres + (v = 0 → truth
  values)`), and the chain rule's semantic content is the model's own
  impredicativity (`piR_zero_mem_univZero`): an inner λ's ∀-type at
  bit `0` is a truth value *because it is a `piR 0`*, no run needed;
* every other clause is hereditary plumbing, clause-for-clause the
  `AnnotOk2` environment discipline (so the substitution metatheory
  rides the identical rewrites).

**Establishment is from run inversions, never a validity
metatheorem.**  `ValidInfer` — "every inferred type has a sort" — is
*refuted* at the application clause (`Annot/Validity.lean`, the
`DefEq`-crossing wall), so `AnnotValidV` is never established by
recursion on derivations.  It is established at the checker's own
visit sites, where the P2 validation conjunct
(`(zeronessOf v).equiv m.pw`, `inferTypeCore_forallE_inv`) meets the
run lemma's semantic sort fact; `pwBit_zero_mem_univZero` below is
that establishment step, isolated.  Preservation is the substitution
pair (`AnnotValidV_liftN`/`AnnotValidV_inst`) + the level-crossing
laws (`denotePInstLevels` upstream of any `interp2` fact).
-/

namespace Setlec.SetR.Interp2

open SetTheory
open Setlec.SetR (AVExpr)
open Setlec (Name Level PropWhen)

universe w

variable (V : Type w) [SetTheory V]

/-- Bit validity of the binder annotations under a variable
environment (see the module docstring): the one new fact is the `pi`
clause's `v = 0` component; everything else is the hereditary
environment discipline of `AnnotOk2`. -/
def AnnotValidV : (Nat → V) → AVExpr → Prop
  | ρ, .pi _u v A B =>
    AnnotValidV ρ A ∧
    (∀ x, x ∈ˢ interp2 V ρ A → AnnotValidV (cons x ρ) B) ∧
    (v = 0 → ∀ x, x ∈ˢ interp2 V ρ A →
      interp2 V (cons x ρ) B ∈ˢ (univZero : V))
  | ρ, .lam _v A b =>
    AnnotValidV ρ A ∧
    ∀ x, x ∈ˢ interp2 V ρ A → AnnotValidV (cons x ρ) b
  | ρ, .app f a => AnnotValidV ρ f ∧ AnnotValidV ρ a
  | ρ, .letE T v b =>
    AnnotValidV ρ T ∧ AnnotValidV ρ v ∧
    AnnotValidV (cons (interp2 V ρ v) ρ) b
  | ρ, .eqE _ a b => AnnotValidV ρ a ∧ AnnotValidV ρ b
  | ρ, .proj _ e => AnnotValidV ρ e
  | _, .bvar _ => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | _, .prf => True

/-! ### Clause equations -/

@[simp] theorem AnnotValidV_bvar (ρ : Nat → V) (i : Nat) :
    AnnotValidV V ρ (.bvar i) = True := by rw [AnnotValidV]
@[simp] theorem AnnotValidV_sort (ρ : Nat → V) (u : Nat) :
    AnnotValidV V ρ (.sort u) = True := by rw [AnnotValidV]
@[simp] theorem AnnotValidV_const (ρ : Nat → V) (c : Setlec.TT.BConst)
    (us : List Nat) : AnnotValidV V ρ (.const c us) = True := by
  rw [AnnotValidV]
@[simp] theorem AnnotValidV_prf (ρ : Nat → V) :
    AnnotValidV V ρ .prf = True := by rw [AnnotValidV]
theorem AnnotValidV_pi (ρ : Nat → V) (u v : Nat) (A B : AVExpr) :
    AnnotValidV V ρ (.pi u v A B) =
      (AnnotValidV V ρ A ∧
        (∀ x, x ∈ˢ interp2 V ρ A → AnnotValidV V (cons x ρ) B) ∧
        (v = 0 → ∀ x, x ∈ˢ interp2 V ρ A →
          interp2 V (cons x ρ) B ∈ˢ (univZero : V))) := by
  rw [AnnotValidV]
theorem AnnotValidV_lam (ρ : Nat → V) (v : Nat) (A b : AVExpr) :
    AnnotValidV V ρ (.lam v A b) =
      (AnnotValidV V ρ A ∧
        ∀ x, x ∈ˢ interp2 V ρ A → AnnotValidV V (cons x ρ) b) := by
  rw [AnnotValidV]
theorem AnnotValidV_app (ρ : Nat → V) (f a : AVExpr) :
    AnnotValidV V ρ (.app f a) =
      (AnnotValidV V ρ f ∧ AnnotValidV V ρ a) := by rw [AnnotValidV]
theorem AnnotValidV_letE (ρ : Nat → V) (T v b : AVExpr) :
    AnnotValidV V ρ (.letE T v b) =
      (AnnotValidV V ρ T ∧ AnnotValidV V ρ v ∧
        AnnotValidV V (cons (interp2 V ρ v) ρ) b) := by rw [AnnotValidV]
theorem AnnotValidV_eqE (ρ : Nat → V) (T a b : AVExpr) :
    AnnotValidV V ρ (.eqE T a b) =
      (AnnotValidV V ρ a ∧ AnnotValidV V ρ b) := by rw [AnnotValidV]
theorem AnnotValidV_proj (ρ : Nat → V) (i : Nat) (e : AVExpr) :
    AnnotValidV V ρ (.proj i e) = AnnotValidV V ρ e := by
  rw [AnnotValidV]

/-! ## The establishment step, isolated

The `pi` component at a checker-visited node: the P2 run inversion
supplies `(zeronessOf v).equiv pw` (the site passed), the run lemma
supplies the codomain's semantic sort membership, and the bit laws
turn the claimed bit into the sort's true zero — impredicativity is
not consulted, the sort fact is enough. -/

variable {V}

/-- A validated zero bit puts the sort's inhabitants in `univZero`:
the pointwise establishment step for `AnnotValidV`'s `pi` component
(and for `AnnotOk2`'s λ-clause `v = 0` component at the leaf case). -/
theorem pwBit_zero_mem_univZero {v : Level} {pw : PropWhen}
    {φ : Name → Nat}
    (hz : PropWhen.equiv (Level.zeronessOf v) pw = true)
    (hb : pwBit φ pw = 0) {x : V}
    (hx : x ∈ˢ (univ (Level.eval φ v) : V)) :
    x ∈ˢ (univZero : V) := by
  have h0 : Level.eval φ v = 0 := by
    have := (pwBit_of_equiv_zeronessOf hz φ).mp hb
    exact this
  rw [h0, univ_zero] at hx
  exact hx

/-! ## Preservation: the substitution pair

Clause for clause `AnnotOk2_liftN`/`AnnotOk2_inst` — the `pi` bit
component mentions only `interp2` of the clause's own subterms, so it
rides `interp2_liftN`/`cons_shiftE` exactly as the λ clause's fibre
package does there. -/

variable (V)

/-- Bit validity through lifting. -/
theorem AnnotValidV_liftN (n : Nat) :
    ∀ (e : AVExpr) (k : Nat) (ρ : Nat → V),
      AnnotValidV V ρ (e.liftN n k) ↔ AnnotValidV V (shiftE n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [AVExpr.liftN_bvar]
    split <;> simp
  | sort u => intro k ρ; simp
  | const c us => intro k ρ; simp
  | app f a ihf iha =>
    intro k ρ
    rw [AVExpr.liftN_app, AnnotValidV_app, AnnotValidV_app, ihf, iha]
  | lam v A b ihA ihb =>
    intro k ρ
    rw [AVExpr.liftN_lam, AnnotValidV_lam, AnnotValidV_lam, ihA,
      interp2_liftN]
    refine and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
    rw [ihb, cons_shiftE]
  | pi u v A B ihA ihB =>
    intro k ρ
    rw [AVExpr.liftN_pi, AnnotValidV_pi, AnnotValidV_pi, ihA,
      interp2_liftN]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (imp_congr Iff.rfl (forall_congr' fun x =>
        imp_congr Iff.rfl ?_)))
    · rw [ihB, cons_shiftE]
    · rw [interp2_liftN, cons_shiftE]
  | letE T v b ihT ihv ihb =>
    intro k ρ
    rw [AVExpr.liftN_letE, AnnotValidV_letE, AnnotValidV_letE, ihT, ihv,
      interp2_liftN, ihb, cons_shiftE]
  | eqE T a b ihT iha ihb =>
    intro k ρ
    rw [AVExpr.liftN_eqE, AnnotValidV_eqE, AnnotValidV_eqE, iha, ihb]
  | proj i e ihe =>
    intro k ρ
    rw [AVExpr.liftN_proj, AnnotValidV_proj, AnnotValidV_proj, ihe]
  | prf => intro k ρ; simp

/-! ### Instantiation — and the one premise that had to change

`AnnotOk2_inst` takes `AnnotOk2 V (shiftE k 0 ρ) a`, and the P3 brief
proposed the same premise here.  **It does not work, for a structural
reason worth recording.**  The `bvar` clause at `i = k` reduces the
goal to `AnnotValidV V ρ (a.liftN k)`, which `AnnotValidV_liftN`
turns into `AnnotValidV V (shiftE k 0 ρ) a` — *bit validity of the
substituted term itself*.  `AnnotOk2` does not imply it (the two
predicates are independent: `AnnotOk2`'s `pi` clause carries no bit
component at all, which is exactly why `AnnotValidV` exists).

So the premise below is the **matching** one, `AnnotValidV` of `a`,
not the conjunction: no other clause reads anything about `a` beyond
what its own induction hypothesis supplies, so asking for `AnnotOkP`
would over-charge the lemma.  The conjunction form is available as
`AnnotOkP_inst0` (`Interp2/OkPTransport.lean`), where it is assembled
from this lemma and `AnnotOk2_inst` — each half paying only its own
premise. -/

/-- Bit validity through instantiation. -/
theorem AnnotValidV_inst :
    ∀ (e a : AVExpr) (k : Nat) (ρ : Nat → V),
      AnnotValidV V (shiftE k 0 ρ) a →
      (AnnotValidV V ρ (e.inst a k) ↔
        AnnotValidV V (instE k (interp2 V (shiftE k 0 ρ) a) ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ ha
    show AnnotValidV V ρ
        (if i < k then .bvar i
         else if i = k then AVExpr.liftN k a else .bvar (i - 1)) ↔ _
    by_cases h : i < k
    · simp [if_pos h]
    · by_cases h2 : i = k
      · simp only [if_neg h, if_pos h2, AnnotValidV_bvar, iff_true]
        exact (AnnotValidV_liftN V k a 0 ρ).mpr ha
      · simp [if_neg h, if_neg h2]
  | sort u => intro a k ρ _; simp [AVExpr.inst]
  | const c us => intro a k ρ _; simp [AVExpr.inst]
  | app f b ihf ihb =>
    intro a k ρ ha
    rw [AVExpr.inst_app, AnnotValidV_app, AnnotValidV_app, ihf a k ρ ha,
      ihb a k ρ ha]
  | lam v A b ihA ihb =>
    intro a k ρ ha
    rw [AVExpr.inst_lam, AnnotValidV_lam, AnnotValidV_lam, ihA a k ρ ha,
      interp2_inst]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)
    have ha' : AnnotValidV V (shiftE (k + 1) 0 (cons x ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihb a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
  | pi u v A B ihA ihB =>
    intro a k ρ ha
    rw [AVExpr.inst_pi, AnnotValidV_pi, AnnotValidV_pi, ihA a k ρ ha,
      interp2_inst]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (imp_congr Iff.rfl (forall_congr' fun x =>
        imp_congr Iff.rfl ?_)))
    · have ha' : AnnotValidV V (shiftE (k + 1) 0 (cons x ρ)) a := by
        rw [shiftE_succ_cons]; exact ha
      rw [ihB a (k + 1) (cons x ρ) ha', shiftE_succ_cons, cons_instE]
    · rw [interp2_inst, shiftE_succ_cons, cons_instE]
  | letE T v b ihT ihv ihb =>
    intro a k ρ ha
    rw [AVExpr.inst_letE, AnnotValidV_letE, AnnotValidV_letE,
      ihT a k ρ ha, ihv a k ρ ha, interp2_inst]
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    have ha' : AnnotValidV V (shiftE (k + 1) 0
        (cons (interp2 V (instE k (interp2 V (shiftE k 0 ρ) a) ρ) v)
          ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihb a (k + 1) _ ha', shiftE_succ_cons, cons_instE]
  | eqE T x y ihT ihx ihy =>
    intro a k ρ ha
    rw [AVExpr.inst_eqE, AnnotValidV_eqE, AnnotValidV_eqE, ihx a k ρ ha,
      ihy a k ρ ha]
  | proj i e ihe =>
    intro a k ρ ha
    rw [AVExpr.inst_proj, AnnotValidV_proj, AnnotValidV_proj,
      ihe a k ρ ha]
  | prf => intro a k ρ _; simp [AVExpr.inst]

/-- Substitution at the outermost binder — the β/ζ transport form,
`AnnotOk2_inst0`'s mirror. -/
theorem AnnotValidV_inst0 {e a : AVExpr} {ρ : Nat → V}
    (ha : AnnotValidV V ρ a) :
    AnnotValidV V ρ (e.inst a) ↔
      AnnotValidV V (cons (interp2 V ρ a) ρ) e := by
  have h := AnnotValidV_inst V e a 0 ρ (by rwa [shiftE_zero_zero])
  rwa [shiftE_zero_zero, instE_zero] at h

end Setlec.SetR.Interp2
