import Setlec.SetP.DirectStageCtorP

/-!
# The recursor stage's syntactic kit (task #175 W4c, P3 module 6, part 6)

Three syntactic facts the recursor's frames need:

* `openPisAtFvars_shiftFrom` — opening a shifted term one depth
  deeper is the opening shifted (`Expr.shiftFrom`): the checker opens
  the minor premise's field telescope at depth `nP + 2` (under the
  minor's own binder) while its reading opens it at `nP + 1`;
* `piDoms_of_infer` — the per-binder domain inference runs of an
  inferred Π-type (the motive's and the minor's own bits);
* `instPisAt_erasedEq` — `instPisAt` at erased-equal inputs gives
  erased-equal outputs (the recursor's parameter pins compare the
  constructor's domains instantiated at the *recursor's* variables).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal BinderMeta)

/-! ## Opening one depth deeper -/

theorem openPisAtFvars_shiftFrom {p : Nat} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      p ≤ d → openPisAtFvars n e d = some (fvs, o) →
      openPisAtFvars n (e.shiftFrom p) (d + 1)
        = some (fvs.map (Expr.shiftFrom p), o.shiftFrom p)
  | 0, e, d, fvs, o, _, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | n + 1, e, d, fvs, o, hpd, h => by
    match e, h with
    | .forallE nm dom body mb, h =>
      simp only [openPisAtFvars] at h
      split at h
      · next fvs' o' h' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ih := openPisAtFvars_shiftFrom n (p := p) (d := d + 1) (by omega) h'
        rw [Expr.shiftFrom_instantiate1 hpd] at ih
        show (match openPisAtFvars n
            ((body.shiftFrom p).instantiate1
              (.fvar (d + 1) nm (dom.shiftFrom p))) (d + 1 + 1) with
          | some (fvs, e) => some (Expr.fvar (d + 1) nm (dom.shiftFrom p) :: fvs, e)
          | none => none) = _
        have hf : Expr.shiftFrom p (Expr.fvar d nm dom)
            = Expr.fvar (d + 1) nm (dom.shiftFrom p) := by
          simp [Expr.shiftFrom, show d ≥ p from hpd]
        rw [ih, List.map_cons, hf]
      · exact nomatch h
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [openPisAtFvars] at h

/-- The top-level form: a term below the cut opens one depth deeper
to its opening's shift. -/
theorem openPisAtFvars_succ_of_below {p : Nat} (n : Nat) {e : Expr} {d : Nat}
    {fvs : List Expr} {o : Expr} (hpd : p ≤ d) (hfb : Expr.fvarsBelow p e)
    (h : openPisAtFvars n e d = some (fvs, o)) :
    openPisAtFvars n e (d + 1) = some (fvs.map (Expr.shiftFrom p), o.shiftFrom p) := by
  have := openPisAtFvars_shiftFrom n hpd h
  rwa [Expr.shiftFrom_eq_self hfb] at this

/-! ## The per-binder domain runs -/

/-- **The Π-prefix's domain runs**: in an inferred Π-type, each of the
first `n` opened binders' annotations is inferred at its own depth. -/
theorem piDoms_of_infer {env : Env} {mode : CheckMode} :
    ∀ (n : Nat) {F d : Nat} {e t : Expr} {fvs : List Expr} {opened : Expr},
      openPisAtFvars n e d = some (fvs, opened) →
      Setlec.inferTypeCore mode env F d e = .ok t →
      ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
        ∃ (F' : Nat) (tj : Expr),
          Setlec.inferTypeCore mode env F' (d + j) (Expr.fvarTypeD x) = .ok tj
  | 0, F, d, e, t, fvs, opened, hop, _, j, x, hx => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact nomatch hx
  | n + 1, F, d, e, t, fvs, opened, hop, h, j, x, hx => by
    match e, hop, h with
    | .forallE nm dom body mb, hop, h =>
      match F, h with
      | 0, h => rw [Setlec.inferTypeCore_zero] at h; exact nomatch h
      | F + 1, h =>
        obtain ⟨tty, u, bt, v, hty, -, hbt, -, -, rfl⟩ :=
          Setlec.inferTypeCore_forall_inv h
        simp only [openPisAtFvars] at hop
        split at hop
        · next fvs' e' hop' =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hop
          obtain ⟨rfl, rfl⟩ := hop
          cases j with
          | zero =>
            obtain rfl : Expr.fvar d nm dom = x := by simpa using hx
            exact ⟨F, tty, by rw [Nat.add_zero]; exact hty⟩
          | succ j =>
            simp only [List.getElem?_cons_succ] at hx
            obtain ⟨F', tj, hj⟩ := piDoms_of_infer n hop' hbt j x hx
            exact ⟨F', tj, by rw [show d + (j + 1) = d + 1 + j from by omega]; exact hj⟩
        · exact nomatch hop
    | .bvar _, hop, _ | .fvar _ _ _, hop, _ | .sort _, hop, _
    | .const _ _, hop, _ | .app _ _, hop, _ | .lam _ _ _ _, hop, _
    | .letE _ _ _ _, hop, _ | .lit _, hop, _ | .proj _ _ _, hop, _ =>
      simp [openPisAtFvars] at hop

/-! ## `instPisAt` at erased-equal inputs -/

theorem ErasedEq.forallE_inv {nm : Name} {ty b : Expr} {m : BinderMeta} {e' : Expr}
    (h : Expr.ErasedEq (.forallE nm ty b m) e') :
    ∃ nm' ty' b', e' = .forallE nm' ty' b' m ∧
      Expr.ErasedEq ty ty' ∧ Expr.ErasedEq b b' := by
  match e', h with
  | .forallE nm' ty' b' m', h =>
    obtain ⟨rfl, h1, h2⟩ := h
    exact ⟨nm', ty', b', rfl, h1, h2⟩
  | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
  | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h => exact h.elim

theorem instPisAt_erasedEq :
    ∀ (as as' : List Expr) {ty ty' : Expr} {ds ds' : List Expr} {rs rs' : Expr},
      Expr.instPisAt as ty = some (ds, rs) →
      Expr.instPisAt as' ty' = some (ds', rs') →
      Expr.ErasedEq ty ty' →
      (∀ (i : Nat) (a a' : Expr), as[i]? = some a → as'[i]? = some a' →
        Expr.ErasedEq a a') →
      as.length = as'.length →
      (∀ (i : Nat) (x x' : Expr), ds[i]? = some x → ds'[i]? = some x' →
        Expr.ErasedEq x x') ∧ Expr.ErasedEq rs rs'
  | [], [], ty, ty', ds, ds', rs, rs', h, h', hty, _, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h h'
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨fun i x x' hx _ => (nomatch hx), hty⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, hlen => by simp at hlen
  | a :: as, a' :: as', ty, ty', ds, ds', rs, rs', h, h', hty, has, hlen => by
    match ty, h with
    | .forallE nm dom body mb, h =>
      obtain ⟨nm', dom', body', rfl, hdom, hbody⟩ := ErasedEq.forallE_inv hty
      simp only [Expr.instPisAt] at h h'
      cases h1 : Expr.instPisAt as (body.instantiate1 a) with
      | none => rw [h1] at h; exact nomatch h
      | some q =>
      cases h1' : Expr.instPisAt as' (body'.instantiate1 a') with
      | none => rw [h1'] at h'; exact nomatch h'
      | some q' =>
      rw [h1] at h
      rw [h1'] at h'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h h'
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := h'
      have haa' : Expr.ErasedEq a a' := has 0 a a' rfl rfl
      obtain ⟨ihd, ihr⟩ := instPisAt_erasedEq as as' h1 h1'
        (Expr.ErasedEq.instantiate1 hbody haa')
        (fun i x x' hx hx' => has (i + 1) x x' (by simpa using hx) (by simpa using hx'))
        (by simpa using hlen)
      refine ⟨fun i x x' hx hx' => ?_, ihr⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hx'
        subst hx hx'
        exact hdom
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx hx'
        exact ihd i x x' hx hx'
    | .bvar _, h | .fvar _ _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.instPisAt] at h

end Setlec.SetR.Interp2
