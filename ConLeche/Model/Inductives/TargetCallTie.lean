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

theorem callSubst_notPi {ctx : NestCtx} {prog : List NestHole} {fvsF : List Expr}
    (hfv : ∀ x ∈ fvsF, ∃ j ty, x = .fvar j ty) {i : Nat} (hi : i ≤ fvsF.length) {v : Nat}
    (hv : v < ctx.hiAt prog.length + i) : NotPi (callSubst ctx prog fvsF v) := by
  intro a b bm h
  simp only [callSubst] at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i h1 h2
      obtain ⟨n, us, hc⟩ := nestHoleConst_hole (prog := prog) (by omega) h2
      rw [hc] at h; exact nomatch h
    · rename_i h2
      have hl : v - ctx.hiAt prog.length < fvsF.length := by omega
      rw [List.getElem?_eq_getElem hl, Option.getD_some] at h
      obtain ⟨j, ty, hj⟩ := hfv _ (List.getElem_mem hl)
      rw [hj] at h; exact nomatch h

theorem substFvars_notPi {b D : Nat} {s : Nat → Expr} (hs : ∀ v, v < b → NotPi (s v)) {X : Expr}
    (hX : NotPi X) : NotPi (Expr.substFvars b D s X) := by
  intro a c bm h
  cases X with
  | forallE a' b' bm' => exact hX a' b' bm' rfl
  | fvar v ty =>
    by_cases hv : v < b
    · rw [Expr.substFvars_fvar_lt hv] at h; exact hs v hv a c bm h
    · rw [Expr.substFvars_fvar_ge (by omega)] at h; exact nomatch h
  | _ => simp [Expr.substFvars] at h

/-- **THE TIE**: a call's callee major under its telescope, erasure-equal
to the recorded normal form of its field (K.53′ at the walk's own normal
form, `targetPiDomsWith_close`), is the walk's field tower substituted by
`callSubst`: one telescope length, each domain the walk's substituted, the
major the walk's leaf substituted. -/
theorem callTie {ctx : NestCtx} {prog : List NestHole} {fvsF : List Expr} {i B : Nat}
    (hfv : ∀ x ∈ fvsF, ∃ j ty, x = .fvar j ty) (hi : i ≤ fvsF.length) {nd : Expr}
    (hnd : nd.fvarsBelow (ctx.hiAt prog.length + i))
    {tele teleW : List (Expr × BinderMeta)} {majDom leafC : Expr}
    (hK : Expr.ErasedEq (nd.replaceFVars (extendF (nestHoleConst ctx prog) (ctx.hiAt prog.length)
      (fvsF.take i))) (Expr.mkPisOf tele majDom))
    (hshape : nd = Expr.mkPisOf teleW leafC) (hmaj : NotPi majDom) (hleaf : NotPi leafC) :
    tele.length = teleW.length ∧
    (∀ (l : Nat) (p p' : Expr × BinderMeta), tele[l]? = some p → teleW[l]? = some p' →
      p.2 = p'.2 ∧ Expr.ErasedEq p.1
        (Expr.substFvars (ctx.hiAt prog.length + i) B (callSubst ctx prog fvsF) p'.1)) ∧
    Expr.ErasedEq majDom
      (Expr.substFvars (ctx.hiAt prog.length + i) B (callSubst ctx prog fvsF) leafC) := by
  have h1 := (Expr.ErasedEq.symm hK).trans (dom_erasedEq_callSubst (B := B) hi hnd)
  rw [hshape, Expr.substFvars_mkPisOf] at h1
  have hNP := substFvars_notPi (b := ctx.hiAt prog.length + i) (D := B)
    (fun v hv => callSubst_notPi hfv hi hv) hleaf
  have hlen := mkPisOf_length_of_erasedEq hmaj hNP h1
  rw [List.length_map] at hlen
  obtain ⟨hall, hX⟩ := Expr.ErasedEq.mkPisOf_inv (by simpa using hlen) h1
  refine ⟨hlen, fun l p p' hp hp' => ?_, hX⟩
  have := hall l p (Expr.substFvars (ctx.hiAt prog.length + i) B (callSubst ctx prog fvsF) p'.1,
    p'.2) hp (by simp [hp'])
  exact this

end ConLeche.Model
