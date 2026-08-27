import Setlec.TTVerify.Rename
import Setlec.TTVerify.SubstAlgebra

/-!
# Opening a telescope, and substituting a spine into what is left

The phase's shared piece, named in `Setlec/TTVerify/DeclInd.lean`:
**the thing that moves a spine between two descriptions of the same
telescope.**  Both folds and both bottoms need the *residual* of a
`∀`-telescope after `k` arguments, and the two sides describe it
differently:

* the pins describe it **syntactically**, as `stripPis`' body with `k`
  loose bvars;
* the laws consume it **semantically**, as a `VExpr` with the use
  site's spine `xs` already substituted.

Composing the two is: open the `k` binders at fresh variables
(`Expr.instSeq` at `openFvars`, so the existing `instSeq_*` algebra
applies verbatim), denote, then substitute `xs` — which is
`VExpr.instSeq`, the missing half.

**Why `VExpr.instSeq` mirrors `Expr.instSeq` clause for clause**
(descending cuts, the same `t - 1`): the two are applied to the *same*
telescope, one before and one after `denote`, and every index fact is
then a transcription rather than a re-derivation.  The one place they
differ is `instSeq_bvar`, and the difference is instructive:
`Expr.instantiate1` does **not** lift, so the `Expr` lemma needs
`looseBVarsBounded 0` on every argument; `VExpr.inst` does, so the
`VExpr` lemma needs nothing and pays instead by producing
`liftN c x` — the lifts the consumer's own `inst` then absorbs.
-/

namespace Setlec.TT
namespace VExpr

/-! ## `VExpr.instSeq` -/

/-- Instantiate a spine at descending cuts, outermost argument first —
the term-side counterpart of `Setlec.Expr.instSeq`. -/
def instSeq : List VExpr → Nat → VExpr → VExpr
  | [], _, e => e
  | a :: as, t, e => instSeq as (t - 1) (e.inst a t)

@[simp] theorem instSeq_nil (t : Nat) (e : VExpr) : instSeq [] t e = e := rfl

theorem instSeq_cons (a : VExpr) (as : List VExpr) (t : Nat) (e : VExpr) :
    instSeq (a :: as) t e = instSeq as (t - 1) (e.inst a t) := rfl

/-- A closed term is untouched. -/
theorem instSeq_eq_self_of_closed {e : VExpr} (h : Closed e) :
    ∀ (as : List VExpr) (t : Nat), instSeq as t e = e := by
  intro as
  induction as with
  | nil => intro t; rfl
  | cons a as ih => intro t; rw [instSeq_cons, inst_eq_self_of_closed h, ih]

@[simp] theorem instSeq_sort (as : List VExpr) (t u : Nat) :
    instSeq as t (.sort u) = .sort u :=
  instSeq_eq_self_of_closed (e := .sort u) trivial as t

@[simp] theorem instSeq_const (as : List VExpr) (t : Nat) (c : BConst)
    (us : List Nat) : instSeq as t (.const c us) = .const c us :=
  instSeq_eq_self_of_closed (e := .const c us) trivial as t

theorem instSeq_app : ∀ (as : List VExpr) (t : Nat) (f a : VExpr),
    instSeq as t (.app f a) = .app (instSeq as t f) (instSeq as t a) := by
  intro as
  induction as with
  | nil => intro t f a; rfl
  | cons x xs ih => intro t f a; rw [instSeq_cons, inst_app, ih]; rfl

theorem instSeq_mkAppN : ∀ (as : List VExpr) (t : Nat) (f : VExpr)
    (args : List VExpr),
    instSeq as t (mkAppN f args) =
      mkAppN (instSeq as t f) (args.map (instSeq as t ·)) := by
  intro as t f args
  induction args generalizing f with
  | nil => rfl
  | cons a args ih =>
    rw [mkAppN_cons, ih, instSeq_app]
    rfl

/-- Instantiation distributes over an application spine. -/
theorem inst_mkAppN : ∀ (args : List VExpr) (f a : VExpr) (k : Nat),
    (mkAppN f args).inst a k =
      mkAppN (f.inst a k) (args.map (·.inst a k)) := by
  intro args
  induction args with
  | nil => intro f a k; rfl
  | cons x xs ih => intro f a k; rw [mkAppN_cons, ih]; rfl

/-- Under a binder the cut steps up — the transcription of
`Expr.instSeq_forallE`, with the same side condition. -/
theorem instSeq_pi : ∀ (as : List VExpr) (t : Nat) (A B : VExpr),
    as.length ≤ t + 1 →
    instSeq as t (.pi A B) = .pi (instSeq as t A) (instSeq as (t + 1) B) := by
  intro as
  induction as with
  | nil => intro t A B _; rfl
  | cons x xs ih =>
    intro t A B hlen
    simp only [List.length_cons] at hlen
    rw [instSeq_cons, inst_pi,
      ih (t - 1) (A.inst x t) (B.inst x (t + 1)) (by omega)]
    rw [instSeq_cons (t := t) (e := A), instSeq_cons (t := t + 1) (e := B)]
    cases xs with
    | nil => rfl
    | cons y ys => rw [show t - 1 + 1 = t + 1 - 1 from by simp at hlen; omega]

/-- Instantiating the variables a lift just introduced, one per
argument: each absorbs one unit of the lift. -/
theorem instSeq_liftN : ∀ (as : List VExpr) (t : Nat) (a : VExpr),
    as.length ≤ t + 1 → instSeq as t (liftN (t + 1) a 0) =
      liftN (t + 1 - as.length) a 0 := by
  intro as
  induction as with
  | nil => intro t a _; simp
  | cons x xs ih =>
    intro t a hlen
    simp only [List.length_cons] at hlen
    rw [instSeq_cons, inst_liftN_absorb a (Nat.zero_le t) (by omega) x]
    cases xs with
    | nil => simp [instSeq_nil]
    | cons y ys =>
      simp only [List.length_cons] at hlen
      have ht : t - 1 + 1 = t := by omega
      have h := ih (t - 1) a (by simp only [List.length_cons]; omega)
      rw [ht] at h
      rw [h]
      simp only [List.length_cons]
      congr 1
      omega

/-- A variable below the substituted range is untouched. -/
theorem instSeq_bvar_lt : ∀ (as : List VExpr) (t j : Nat),
    j + as.length ≤ t → instSeq as t (.bvar j) = .bvar j := by
  intro as
  induction as with
  | nil => intro t j _; rfl
  | cons x xs ih =>
    intro t j hlen
    simp only [List.length_cons] at hlen
    rw [instSeq_cons, inst_bvar, if_pos (by omega)]
    exact ih (t - 1) j (by omega)

/-- **Resolving a variable in the substituted range.**  With `k`
arguments at cuts `c + k - 1 … c`, the variable `c + i` becomes the
`i`-th argument *counted from the innermost*, lifted past the `c`
binders the residual sits under.

The lift is not noise: the consumer instantiates those `c` binders
next, and `inst_liftN_absorb` removes exactly one unit per binder. -/
theorem instSeq_bvar_hit : ∀ (as : List VExpr) (c i : Nat) (x : VExpr),
    as[as.length - 1 - i]? = some x → i < as.length →
    instSeq as (c + as.length - 1) (.bvar (c + i)) = liftN c x 0 := by
  intro as
  induction as with
  | nil => intro c i x _ h; simp at h
  | cons a as ih =>
    intro c i x hx hi
    simp only [List.length_cons] at hi
    have hlen : c + (as.length + 1) - 1 = c + as.length := by omega
    by_cases hin : i = as.length
    · subst hin
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      rw [List.length_cons, hlen, instSeq_cons, inst_bvar,
        if_neg (by omega), if_pos rfl]
      rcases Nat.eq_zero_or_pos (c + as.length) with h0 | h0
      · have hc : c = 0 := by omega
        have hl : as.length = 0 := by omega
        rw [hc, List.eq_nil_of_length_eq_zero hl]
        simp
      · obtain ⟨m, hm⟩ : ∃ m, c + as.length = m + 1 :=
          ⟨c + as.length - 1, by omega⟩
        rw [hm, show m + 1 - 1 = m from by omega,
          instSeq_liftN as m a (by omega)]
        congr 1
        omega
    · have hilt : i < as.length := by omega
      rw [List.length_cons, hlen, instSeq_cons, inst_bvar, if_pos (by omega)]
      refine ih c i x ?_ hilt
      simp only [List.length_cons] at hx
      rw [show as.length + 1 - 1 - i = (as.length - 1 - i) + 1 from by omega] at hx
      simpa using hx

end VExpr
end Setlec.TT

namespace Setlec.TTVerify

open Setlec.TT

/-! ## Opening a telescope's binders

The `Expr` half.  Opening is `Expr.instSeq` at a run of fresh
variables, so `instSeq_forallE`, `instSeq_mkAppN`, `instSeq_bvar` and
`instSeq_eq_self` all apply unchanged; the only fact this section adds
is the one the `Expr` side was missing — that an instantiation *below*
the substituted range passes through (`instSeq_instantiate1_in`, the
dual of `Expr.instSeq_instantiate1_out`). -/

/-- The `k` opening variables of a telescope at depth `d`, outermost
first.  `denote` reads neither name nor annotation
(`Setlec/TTVerify/Denote.lean`), so canonical ones are as good as the
binders' own — which is what lets a *single* opening stand for the two
telescopes an alignment relates. -/
def openFvars : Nat → Nat → List Expr
  | _, 0 => []
  | d, k + 1 => Expr.fvar d Name.anonymous (.sort .zero) :: openFvars (d + 1) k

@[simp] theorem openFvars_length : ∀ (d k : Nat), (openFvars d k).length = k
  | _, 0 => rfl
  | d, k + 1 => by simp [openFvars, openFvars_length (d + 1) k]

theorem openFvars_zero (d : Nat) : openFvars d 0 = [] := rfl

theorem openFvars_succ (d k : Nat) :
    openFvars d (k + 1) =
      Expr.fvar d Name.anonymous (.sort .zero) :: openFvars (d + 1) k := rfl

theorem openFvars_bounded : ∀ (d k : Nat),
    ∀ a ∈ openFvars d k, a.looseBVarsBounded 0 = true
  | _, 0 => by intro a ha; exact nomatch ha
  | d, k + 1 => by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | h
    · rfl
    · exact openFvars_bounded (d + 1) k a h

theorem openFvars_getElem? : ∀ {d k i : Nat}, i < k →
    (openFvars d k)[i]? =
      some (Expr.fvar (d + i) Name.anonymous (.sort .zero))
  | _, 0, _, h => absurd h (by omega)
  | d, k + 1, 0, _ => by simp [openFvars]
  | d, k + 1, i + 1, h => by
    rw [openFvars_succ, List.getElem?_cons_succ,
      openFvars_getElem? (d := d + 1) (k := k) (i := i) (by omega)]
    congr 2
    omega

/-- **An instantiation below the substituted range passes through.**
The dual of `Expr.instSeq_instantiate1_out`, and the fact that lets a
residual's *own* binders be opened by `denote` after the telescope's
have been opened by `instSeq`. -/
theorem instSeq_instantiate1_in {b : Expr}
    (hbb : b.looseBVarsBounded 0 = true) :
    ∀ (args : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      args.length ≤ t →
      (Expr.instSeq args t e).instantiate1 b 0 =
        Expr.instSeq args (t - 1) (e.instantiate1 b 0) := by
  intro args
  induction args with
  | nil => intro t e _ _; rfl
  | cons a as ih =>
    intro t e hb hlen
    simp only [List.length_cons] at hlen
    show (Expr.instSeq as (t - 1) (e.instantiate1 a t)).instantiate1 b 0 = _
    rw [ih (t - 1) (fun x hx => hb x (List.mem_cons_of_mem _ hx)) (by omega)]
    show _ = Expr.instSeq as (t - 1 - 1) ((e.instantiate1 b 0).instantiate1 a (t - 1))
    rw [show t = (t - 1) + 1 from by omega]
    rw [Expr.instantiate1_instantiate1 (hb a List.mem_cons_self) hbb e 0 (t - 1)
      (Nat.zero_le _)]
    simp

end Setlec.TTVerify
