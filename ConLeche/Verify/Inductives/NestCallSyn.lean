module

public import ConLeche.Kernel.Inductives.RecCheck
import ConLeche.Verify.Subst
import ConLeche.Verify.Abstract
import ConLeche.Verify.Shift
public import ConLeche.Verify.SubstFvars

public section

/-!
# The calls' syntactic tie to the walk's recorded normal forms

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


/-! ## One substitution for the read-back and the renaming -/

namespace Expr

/-- **The read-back as a parallel substitution**: below `b`, replacing the
mapped variables (keeping the others, up to their annotations) is
`substFvars` at a substitution agreeing with it. -/
theorem replaceFVars_erasedEq_substFvars {g : Nat → Option Expr} {b D : Nat} {s : Nat → Expr}
    (hs : ∀ v, v < b → ∀ ty, ErasedEq ((g v).getD (.fvar v ty)) (s v)) :
    ∀ (X : Expr), X.fvarsBelow b → ErasedEq (X.replaceFVars g) (substFvars b D s X) := by
  intro X
  induction X with
  | bvar i => intro _; exact ErasedEq.rfl _
  | fvar i ty _ =>
    intro h
    simp only [fvarsBelow] at h
    simp only [replaceFVars, substFvars, if_pos h]
    exact hs i h ty
  | sort u => intro _; exact ErasedEq.rfl _
  | const n us => intro _; exact ErasedEq.rfl _
  | lit l => intro _; exact ErasedEq.rfl _
  | app f a ihf iha =>
    intro h; exact ⟨ihf h.1, iha h.2⟩
  | lam t body m iht ihb =>
    intro h; exact ⟨rfl, iht h.1, ihb h.2⟩
  | forallE t body m iht ihb =>
    intro h; exact ⟨rfl, iht h.1, ihb h.2⟩
  | letE t v body iht ihv ihb =>
    intro h; exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj n i e ih =>
    intro h; exact ⟨rfl, rfl, ih h⟩

/-- `substFvars` keeps erasure equality. -/
theorem ErasedEq.substFvars {b D : Nat} {s : Nat → Expr} :
    ∀ {x y : Expr}, ErasedEq x y → ErasedEq (Expr.substFvars b D s x) (Expr.substFvars b D s y) := by
  intro x
  induction x with
  | bvar i => intro y h; cases y <;> simp_all [ErasedEq, Expr.substFvars]
  | fvar i ty _ =>
    intro y h
    cases y <;> simp only [ErasedEq] at h
    subst h
    by_cases hi : i < b
    · simp only [Expr.substFvars, if_pos hi]; exact ErasedEq.rfl _
    · simp only [Expr.substFvars, if_neg hi]; simp [ErasedEq]
  | sort u => intro y h; cases y <;> simp_all [ErasedEq, Expr.substFvars]
  | const n us => intro y h; cases y <;> simp_all [ErasedEq, Expr.substFvars]
  | lit l => intro y h; cases y <;> simp_all [ErasedEq, Expr.substFvars]
  | app f a ihf iha =>
    intro y h
    cases y <;> simp only [ErasedEq] at h
    exact ⟨ihf h.1, iha h.2⟩
  | lam t body m iht ihb =>
    intro y h
    cases y <;> simp only [ErasedEq] at h
    exact ⟨h.1, iht h.2.1, ihb h.2.2⟩
  | forallE t body m iht ihb =>
    intro y h
    cases y <;> simp only [ErasedEq] at h
    exact ⟨h.1, iht h.2.1, ihb h.2.2⟩
  | letE t v body iht ihv ihb =>
    intro y h
    cases y <;> simp only [ErasedEq] at h
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj n i e ih =>
    intro y h
    cases y <;> simp only [ErasedEq] at h
    exact ⟨h.1, h.2.1, ih h.2.2⟩

/-- `substFvars` passes a Π-tower. -/
theorem substFvars_mkPisOf {b D : Nat} {s : Nat → Expr} :
    ∀ (tele : List (Expr × BinderMeta)) (X : Expr),
      Expr.substFvars b D s (Expr.mkPisOf tele X)
        = Expr.mkPisOf (tele.map fun p => (Expr.substFvars b D s p.1, p.2)) (Expr.substFvars b D s X)
  | [], _ => rfl
  | (t, bm) :: r, X => by
    simp only [Expr.mkPisOf, Expr.substFvars, List.map_cons, substFvars_mkPisOf r X]

/-- **Two erasure-equal towers of one length** are erasure-equal binder by
binder and in their bodies. -/
theorem ErasedEq.mkPisOf_inv :
    ∀ {tele tele' : List (Expr × BinderMeta)} {X X' : Expr}, tele.length = tele'.length →
      ErasedEq (Expr.mkPisOf tele X) (Expr.mkPisOf tele' X') →
      (∀ (l : Nat) (p p' : Expr × BinderMeta), tele[l]? = some p → tele'[l]? = some p' →
        p.2 = p'.2 ∧ ErasedEq p.1 p'.1) ∧ ErasedEq X X'
  | [], [], _, _, _, h => ⟨fun l p p' hp _ => by simp at hp, h⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | (t, bm) :: r, (t', bm') :: r', X, X', hl, h => by
    simp only [Expr.mkPisOf, ErasedEq] at h
    obtain ⟨hm, ht, hr⟩ := h
    obtain ⟨hall, hX⟩ := ErasedEq.mkPisOf_inv (by simpa using hl) hr
    refine ⟨fun l p p' hp hp' => ?_, hX⟩
    cases l with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hp'
      subst hp; subst hp'
      exact ⟨hm, ht⟩
    | succ l => exact hall l p p' (by simpa using hp) (by simpa using hp')

/-- **Opening commutes with the substitution**, at variables above `b`
moved to the same positions above `D`. -/
theorem substFvars_instantiateList {b D : Nat} {s : Nat → Expr}
    (hs : ∀ v, v < b → (s v).looseBVarsBounded 0 = true) :
    ∀ (m : Nat) (osW osR : List Expr), osW.length = m → osR.length = m →
      (∀ j, j < m → ∃ ty ty', osW[j]? = some (.fvar (b + m - 1 - j) ty) ∧
        osR[j]? = some (.fvar (D + m - 1 - j) ty')) →
      ∀ (e : Expr) (d : Nat),
        ErasedEq ((Expr.substFvars b D s e).instantiateList osR d)
          (Expr.substFvars b D s (e.instantiateList osW d))
  | 0, [], [], _, _, _, e, d => by
    rw [instantiateList_nil, instantiateList_nil]; exact ErasedEq.rfl _
  | m + 1, w :: ws, r :: rs, hw, hr, hall, e, d => by
    obtain ⟨ty, ty', hw0, hr0⟩ := hall 0 (by omega)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hw0 hr0
    subst hw0; subst hr0
    rw [instantiateList_cons, instantiateList_cons, substFvars_instantiate1 hs]
    refine ErasedEq.instantiate1 (substFvars_instantiateList hs m ws rs (by simpa using hw)
      (by simpa using hr) (fun j hj => ?_) e (d + 1)) ?_
    · obtain ⟨t1, t2, h1, h2⟩ := hall (j + 1) (by omega)
      refine ⟨t1, t2, ?_, ?_⟩
      · simp only [List.getElem?_cons_succ] at h1
        rw [show b + (m + 1) - 1 - (j + 1) = b + m - 1 - j by omega] at h1; exact h1
      · simp only [List.getElem?_cons_succ] at h2
        rw [show D + (m + 1) - 1 - (j + 1) = D + m - 1 - j by omega] at h2; exact h2
    · rw [substFvars_fvar_ge (by omega)]
      show _ = _
      simp only [show b + (m + 1) - 1 - 0 - b + D = D + (m + 1) - 1 - 0 by omega]

end Expr

end ConLeche
