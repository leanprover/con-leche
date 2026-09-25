module

public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Verify.Subst
import ConLeche.Verify.Abstract
import ConLeche.Verify.Shift

public section

/-!
# The calls' syntactic tie to the walk's recorded normal forms (lane NESTIND, session 26)

K.53′ (`targetCallOk`'s last step) compares, up to the free variables'
annotations (`Expr.eraseFVarTys`), the callee's major type under the
called field's telescope with the walk's RECORDED normal form of that
field (`NestCtorNf.ty`, read back, opened at the rule's field variables,
`targetFieldNfs`).  This file turns that comparison into facts about the
walk's own normal form:

* `Expr.eraseFVarTys_eq_iff` — the comparison IS erasure equality;
* `targetPiDomsWith_close` — the recorded telescope, read back and opened
  at the rule's fields, is the walk's normal forms with every hole, field
  and parameter variable moved at once (`Expr.substFvars`).
-/

namespace ConLeche

namespace Expr

/-! ## The comparison K.53′ runs up to -/

theorem eraseFVarTys_fvar (i : Nat) (ty : Expr) :
    (Expr.fvar i ty).eraseFVarTys = .fvar i (.sort .zero) := rfl

/-- **K.53′'s comparison is erasure equality.** -/
theorem eraseFVarTys_eq_iff : ∀ {a b : Expr}, a.eraseFVarTys = b.eraseFVarTys ↔ ErasedEq a b := by
  intro a
  induction a <;> intro b <;> cases b <;>
    simp_all [eraseFVarTys, replaceFVars, ErasedEq, and_comm, and_left_comm]

/-! ## Reading a closed telescope back and opening it -/

/-- One binder closed (`abstract1`), the holes replaced, reopened at `x`:
the variable is `x` itself. -/
theorem replaceFVars_abstract1_instantiate1 {f : Nat → Option Expr} {v : Nat}
    (hfv : f v = none) (hf : ∀ i y, f i = some y → y.looseBVarsBounded 0 = true) (x : Expr) :
    ∀ (T : Expr) (k : Nat), T.looseBVarsBounded k = true →
      ((T.abstract1 v k).replaceFVars f).instantiate1 x k
        = T.replaceFVars (fun i => if i = v then some x else f i) := by
  intro T
  induction T with
  | bvar j =>
    intro k hb
    simp only [looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [abstract1, replaceFVars, instantiate1]
    rw [if_neg (by omega), if_neg (by omega)]
  | fvar i ty _ =>
    intro k _
    by_cases hiv : i = v
    · subst hiv
      simp [abstract1, replaceFVars]
    · simp only [abstract1, if_neg hiv, replaceFVars]
      cases hfi : f i with
      | none => simp
      | some y =>
        simp only [Option.getD_some]
        exact instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le k) (hf i y hfi))
  | sort u => intro k _; rfl
  | const n us => intro k _; rfl
  | lit l => intro k _; rfl
  | app a b iha ihb =>
    intro k hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [abstract1, replaceFVars, instantiate1, iha k hb.1, ihb k hb.2]
  | lam t b m iht ihb =>
    intro k hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [abstract1, replaceFVars, instantiate1, iht k hb.1, ihb (k + 1) hb.2]
  | forallE t b m iht ihb =>
    intro k hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [abstract1, replaceFVars, instantiate1, iht k hb.1, ihb (k + 1) hb.2]
  | letE t w b iht ihw ihb =>
    intro k hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [abstract1, replaceFVars, instantiate1, iht k hb.1.1, ihw k hb.1.2,
      ihb (k + 1) hb.2]
  | proj n i e ih =>
    intro k hb
    simp only [looseBVarsBounded] at hb
    simp only [abstract1, replaceFVars, instantiate1, ih k hb]

end Expr

/-- A closed telescope has no loose bound variable, when its domains and
body have none. -/
theorem closeTelescope_bounded :
    ∀ (nds : List (Expr × BinderMeta)) (hi : Nat) (cur : Expr),
      (∀ nd ∈ nds, nd.1.looseBVarsBounded 0 = true) → cur.looseBVarsBounded 0 = true →
      (closeTelescope nds hi cur).looseBVarsBounded 0 = true
  | [], _, _, _, hc => hc
  | (nd, bm) :: rest, hi, cur, hn, hc => by
    simp only [closeTelescope, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hn _ List.mem_cons_self, looseBVarsBounded_abstract1 _ 0
      (closeTelescope_bounded rest (hi + 1) cur (fun x hx => hn x (List.mem_cons_of_mem _ hx)) hc)⟩

/-- The substitution a recorded telescope's `l`-th domain, opened at the
rule's fields `xs`, carries: the fields `hi ..< hi + l` to `xs`, the rest
as `f` (the read-back). -/
@[expose] def extendF (f : Nat → Option Expr) (hi : Nat) (xs : List Expr) : Nat → Option Expr :=
  fun i => if hi ≤ i ∧ i < hi + xs.length then xs[i - hi]? else f i

theorem targetPiDomsWith_length :
    ∀ (xs : List Expr) (e : Expr) (doms : List Expr), targetPiDomsWith xs e = some doms →
      doms.length = xs.length
  | [], _, doms, h => by simp only [targetPiDomsWith, Option.some.injEq] at h; subst h; rfl
  | x :: xs, e, doms, h => by
    match e, h with
    | .forallE d b _, h =>
      simp only [targetPiDomsWith] at h
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [targetPiDomsWith_length xs _ r hr]

/-- **A recorded telescope, read back and opened at the rule's fields**
(`targetFieldNfs`'s opening of `NestCtorNf.ty`): its `l`-th domain is the
walk's `l`-th normal form with the read-back `f` and the first `l` fields
moved to the rule's. -/
theorem targetPiDomsWith_close :
    ∀ (nds : List (Expr × BinderMeta)) (hi : Nat) (cur : Expr) (f : Nat → Option Expr)
      (fvs doms : List Expr),
      (∀ i, hi ≤ i → f i = none) → (∀ i y, f i = some y → y.looseBVarsBounded 0 = true) →
      (∀ x ∈ fvs, x.looseBVarsBounded 0 = true) →
      (∀ nd ∈ nds, nd.1.looseBVarsBounded 0 = true) → cur.looseBVarsBounded 0 = true →
      fvs.length ≤ nds.length →
      targetPiDomsWith fvs ((closeTelescope nds hi cur).replaceFVars f) = some doms →
      ∀ l d, doms[l]? = some d → ∃ nd : Expr × BinderMeta, nds[l]? = some nd ∧
        d = nd.1.replaceFVars (extendF f hi (fvs.take l))
  | _, _, _, _, [], doms, _, _, _, _, _, _, h, l, d, hd => by
    simp only [targetPiDomsWith, Option.some.injEq] at h
    subst h; exact nomatch hd
  | [], _, _, _, _ :: _, _, _, _, _, _, _, hlen, _, _, _, _ => by simp at hlen
  | (nd, bm) :: rest, hi, cur, f, x :: xs, doms, hf, hfc, hx, hn, hc, hlen, h, l, d, hd => by
    have hT : (closeTelescope rest (hi + 1) cur).looseBVarsBounded 0 = true :=
      closeTelescope_bounded rest (hi + 1) cur (fun y hy => hn y (List.mem_cons_of_mem _ hy)) hc
    simp only [closeTelescope, Expr.replaceFVars, targetPiDomsWith] at h
    rw [Expr.replaceFVars_abstract1_instantiate1 (hf hi (Nat.le_refl _)) hfc x _ 0 hT] at h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    cases l with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      refine ⟨_, rfl, ?_⟩
      congr 1
      funext i
      simp only [extendF]
      split
      · rename_i h'; simp at h'; omega
      · rfl
    | succ l =>
      simp only [List.getElem?_cons_succ] at hd
      have hl : l < xs.length := by
        have := (List.getElem?_eq_some_iff.mp hd).1
        rw [targetPiDomsWith_length xs _ r hr] at this; exact this
      obtain ⟨nd', hnd', rfl⟩ := targetPiDomsWith_close rest (hi + 1) cur
        (fun i => if i = hi then some x else f i) xs r
        (fun i hi' => by rw [if_neg (by omega)]; exact hf i (by omega))
        (fun i y hy => by
          by_cases hih : i = hi
          · rw [if_pos hih] at hy; cases hy; exact hx _ List.mem_cons_self
          · rw [if_neg hih] at hy; exact hfc i y hy)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (fun y hy => hn y (List.mem_cons_of_mem _ hy)) hc (by simpa using hlen) hr l d hd
      refine ⟨nd', by simpa using hnd', ?_⟩
      congr 1
      funext i
      simp only [extendF, List.take_succ_cons, List.length_cons, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hl)]
      by_cases h1 : i = hi
      · subst h1
        have e1 : (i ≤ i ∧ i < i + (l + 1)) := ⟨Nat.le_refl _, by omega⟩
        have e2 : ¬ (i + 1 ≤ i ∧ i < i + 1 + l) := by omega
        simp [e1, e2]
      · by_cases h2 : hi + 1 ≤ i ∧ i < hi + 1 + l
        · rw [if_pos h2, if_pos (by omega)]
          obtain ⟨k, rfl⟩ : ∃ k, i = hi + 1 + k := ⟨i - (hi + 1), by omega⟩
          rw [show hi + 1 + k - (hi + 1) = k by omega, show hi + 1 + k - hi = k + 1 by omega]
          rfl
        · rw [if_neg h2, if_neg h1, if_neg (by omega)]


end ConLeche
