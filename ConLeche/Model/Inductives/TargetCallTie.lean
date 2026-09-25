module

public import ConLeche.Model.Inductives.PosFieldLeaf
public import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Inductives.NestPosOut

public section

/-!
# A call's callee against the walk's normal form of its field (lane NESTIND, session 26)

K.53′ says, up to erasure, that the called field's recorded normal form
(read back, opened at the rule's fields) IS the callee's major type under
the field's telescope.  The recorded normal form is the walk's own
(`targetPiDomsWith_close`), so, with ONE parallel substitution
`callSubst` (parameters kept, every hole to its constant, the earlier
fields to the rule's, the telescope's variables moved from the walk's
depth to the rule's), the callee's telescope is the walk's field
telescope substituted and its major the walk's leaf substituted
(`callTie`).
-/

namespace ConLeche.Model
open ConLeche (Env Expr Name Level NestCtx NestHole BinderMeta nestHoleConst extendF)

/-- **The one substitution** of a field's walk variables below the field
(`b = hiAt |prog| + i`): the block's parameters kept, each hole to its
constant (`nestHoleConst`), the earlier fields to the rule's `fvsF`. -/
@[expose] def callSubst (ctx : NestCtx) (prog : List NestHole) (fvsF : List Expr) : Nat → Expr :=
  fun v => if v < ctx.nP then .fvar v (.sort .zero)
    else if v < ctx.hiAt prog.length then (nestHoleConst ctx prog v).getD default
    else (fvsF[v - ctx.hiAt prog.length]?).getD default

theorem nestHoleConst_lt_nP {ctx : NestCtx} {prog : List NestHole} {v : Nat} (hv : v < ctx.nP) :
    nestHoleConst ctx prog v = none := by
  unfold nestHoleConst
  rw [if_neg (by omega), if_neg (by simp [NestCtx.hiAt]; omega)]

theorem nestHoleConst_ge {ctx : NestCtx} {prog : List NestHole} {v : Nat}
    (hv : ctx.hiAt prog.length ≤ v) : nestHoleConst ctx prog v = none := by
  unfold nestHoleConst
  rw [if_neg (by simp [NestCtx.hiAt] at hv ⊢; omega), if_neg (by omega)]

theorem nestHoleConst_hole {ctx : NestCtx} {prog : List NestHole} {v : Nat} (h1 : ctx.nP ≤ v)
    (h2 : v < ctx.hiAt prog.length) : ∃ n us, nestHoleConst ctx prog v = some (.const n us) := by
  unfold nestHoleConst
  by_cases h0 : v < ctx.hiAt 0
  · rw [if_pos ⟨h1, h0⟩]; exact ⟨_, _, rfl⟩
  · rw [if_neg (by omega), if_pos ⟨by omega, h2⟩]
    have hl : v - ctx.hiAt 0 < prog.reverse.length := by
      simp [NestCtx.hiAt] at h0 h2 ⊢; omega
    rw [List.getElem?_eq_getElem hl]
    exact ⟨_, _, rfl⟩

/-- **The recorded field, as the one substitution**: the `i`-th opened
domain of the read-back telescope is the walk's normal form substituted,
up to erasure. -/
theorem dom_erasedEq_callSubst {ctx : NestCtx} {prog : List NestHole} {fvsF : List Expr} {i B : Nat}
    (hi : i ≤ fvsF.length) {nd : Expr} (hnd : nd.fvarsBelow (ctx.hiAt prog.length + i)) :
    Expr.ErasedEq (nd.replaceFVars (extendF (nestHoleConst ctx prog) (ctx.hiAt prog.length)
        (fvsF.take i)))
      (Expr.substFvars (ctx.hiAt prog.length + i) B (callSubst ctx prog fvsF) nd) := by
  refine Expr.replaceFVars_erasedEq_substFvars (fun v hv ty => ?_) nd hnd
  simp only [extendF, callSubst, List.length_take, Nat.min_eq_left hi]
  by_cases h1 : v < ctx.nP
  · rw [if_neg (by simp [NestCtx.hiAt] at *; omega), nestHoleConst_lt_nP h1, if_pos h1]
    simp [Expr.ErasedEq]
  · rw [if_neg h1]
    by_cases h2 : v < ctx.hiAt prog.length
    · rw [if_neg (by omega), if_pos h2]
      obtain ⟨n, us, hc⟩ := nestHoleConst_hole (prog := prog) (by omega) h2
      rw [hc]
      exact Expr.ErasedEq.rfl _
    · rw [if_pos ⟨by omega, hv⟩, if_neg h2, List.getElem?_take_of_lt (by omega)]
      have hl : v - ctx.hiAt prog.length < fvsF.length := by omega
      rw [List.getElem?_eq_getElem hl]
      exact Expr.ErasedEq.rfl _

/-! ## Towers of one length -/

/-- A term that is no `∀`. -/
@[expose] def NotPi (e : Expr) : Prop := ∀ a b bm, e ≠ .forallE a b bm

theorem ErasedEq.notPi {x y : Expr} (h : Expr.ErasedEq x y) (hy : NotPi y) : NotPi x := by
  intro a b bm hx
  subst hx
  cases y with
  | forallE a' b' bm' => exact hy a' b' bm' rfl
  | _ => simp [Expr.ErasedEq] at h

/-- **Erasure-equal towers over non-`∀` bodies have one length.** -/
theorem mkPisOf_length_of_erasedEq :
    ∀ {t1 t2 : List (Expr × BinderMeta)} {X1 X2 : Expr}, NotPi X1 → NotPi X2 →
      Expr.ErasedEq (Expr.mkPisOf t1 X1) (Expr.mkPisOf t2 X2) → t1.length = t2.length
  | [], [], _, _, _, _, _ => rfl
  | [], (a, bm) :: r, X1, X2, h1, _, h => by
    simp only [Expr.mkPisOf] at h
    cases X1 with
    | forallE a1 b1 m1 => exact (h1 a1 b1 m1 rfl).elim
    | _ => simp [Expr.ErasedEq] at h
  | (a, bm) :: r, [], X1, X2, _, h2, h => by
    simp only [Expr.mkPisOf] at h
    cases X2 with
    | forallE a1 b1 m1 => exact (h2 a1 b1 m1 rfl).elim
    | _ => simp [Expr.ErasedEq] at h
  | (a, bm) :: r, (a', bm') :: r', X1, X2, h1, h2, h => by
    simp only [Expr.mkPisOf, Expr.ErasedEq] at h
    simp [mkPisOf_length_of_erasedEq h1 h2 h.2.2]

end ConLeche.Model
