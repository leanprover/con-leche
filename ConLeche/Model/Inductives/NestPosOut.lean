module

public import ConLeche.Kernel.Inductives.Positivity
public import ConLeche.Verify.Subst
import ConLeche.Verify.Inductives.NestCallSyn

public section

/-!
# The positivity walk's OUTPUT: syntactic lemmas

`nestPos` (`Kernel/Inductives/Positivity.lean`) returns, besides a
field's kind, the field's NORMAL FORM.  This file holds the erasure- and
occurrence-level lemmas its readings need; the output's shape is read
off the positivity DERIVATION (`PosDerivShape.lean`), and
how the normal form relates to the declared type is semantic
(`NestPosRed.lean`).
-/

namespace ConLeche.Model

open ConLeche (Env Expr Name Level NestCtx BinderMeta closeTelescope openPisAtFvars)

/-! ## Erasure-level lemmas -/

/-- The occurrence test ignores what erasure ignores. -/
theorem erasedEq_nestOcc {names : List Name} {lo hi : Nat} :
    ∀ (a b : Expr), Expr.ErasedEq a b → a.nestOcc names lo hi = b.nestOcc names lo hi := by
  intro a
  induction a with
  | bvar i => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | fvar i ty _ => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | sort u => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | const n us => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | lit l => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | app f a ihf iha =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, ihf _ h.1, iha _ h.2]
  | lam ty bd mm iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.2.1, ihb _ h.2.2]
  | forallE ty bd mm iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.2.1, ihb _ h.2.2]
  | letE ty v bd iht ihv ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.1, ihv _ h.2.1, ihb _ h.2.2]
  | proj s i e ih =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, ih _ h.2.2]

/-- Closing a bvar-bounded term then re-opening it gives it back up to
erasure (`abstract1_instantiate1` without the annotation premise). -/
theorem erasedEq_abstract1_instantiate1 {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      Expr.ErasedEq ((e.abstract1 d k).instantiate1 (.fvar d ty) k) e := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.abstract1, Expr.instantiate1]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    exact Expr.ErasedEq.rfl _
  | fvar idx ty' _ =>
    intro k _
    simp only [Expr.abstract1]
    split
    · rename_i h
      simp only [Expr.instantiate1, ite_true]
      exact h.symm
    · exact Expr.ErasedEq.rfl _
  | sort u => intro k _; exact Expr.ErasedEq.rfl _
  | const n us => intro k _; exact Expr.ErasedEq.rfl _
  | lit l => intro k _; exact Expr.ErasedEq.rfl _
  | app f a ihf iha =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihf k hb.1, iha k hb.2⟩
  | lam t b mm iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨rfl, iht k hb.1, ihb (k + 1) hb.2⟩
  | forallE t b mm iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨rfl, iht k hb.1, ihb (k + 1) hb.2⟩
  | letE t v b iht ihv ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨iht k hb.1.1, ihv k hb.1.2, ihb (k + 1) hb.2⟩
  | proj s i e ih =>
    intro k hb
    simp only [Expr.looseBVarsBounded] at hb
    exact ⟨rfl, rfl, ih k hb⟩

/-- Abstracting a non-hole variable changes no occurrence. -/
theorem nestOcc_abstract1 {names : List Name} {lo hi d : Nat} (hd : ¬ (lo ≤ d ∧ d < hi)) :
    ∀ (e : Expr) (k : Nat), (e.abstract1 d k).nestOcc names lo hi = e.nestOcc names lo hi := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro k
    simp only [Expr.abstract1]
    split
    · rename_i h
      subst h
      simp [Expr.nestOcc, hd]
    · rfl
  | bvar i => intro k; rfl
  | sort u => intro k; rfl
  | const n us => intro k; rfl
  | lit l => intro k; rfl
  | app f a ihf iha => intro k; simp [Expr.abstract1, Expr.nestOcc, ihf, iha]
  | lam t b mm iht ihb => intro k; simp [Expr.abstract1, Expr.nestOcc, iht, ihb]
  | forallE t b mm iht ihb => intro k; simp [Expr.abstract1, Expr.nestOcc, iht, ihb]
  | letE t v b iht ihv ihb => intro k; simp [Expr.abstract1, Expr.nestOcc, iht, ihv, ihb]
  | proj s i e ih => intro k; simp [Expr.abstract1, Expr.nestOcc, ih]

/-- Erasure-equal terms have erasure-equal heads and argument spines. -/
theorem erasedEq_getApp :
    ∀ (e e' : Expr), Expr.ErasedEq e e' →
      Expr.ErasedEq e.getAppFn e'.getAppFn ∧ e.getAppArgs.length = e'.getAppArgs.length ∧
      ∀ (i : Nat) (x x' : Expr), e.getAppArgs[i]? = some x → e'.getAppArgs[i]? = some x' → Expr.ErasedEq x x' := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro e' h
    cases e' with
    | app f' a' =>
      obtain ⟨hf, ha⟩ := h
      obtain ⟨h1, h2, h3⟩ := ihf f' hf
      refine ⟨h1, by simp [Expr.getAppArgs, h2], fun i x x' hx hx' => ?_⟩
      simp only [Expr.getAppArgs] at hx hx'
      by_cases hi : i < f.getAppArgs.length
      · rw [List.getElem?_append_left hi] at hx
        rw [List.getElem?_append_left (by omega)] at hx'
        exact h3 i x x' hx hx'
      · rw [List.getElem?_append_right (by omega)] at hx
        rw [List.getElem?_append_right (by omega)] at hx'
        rw [h2] at hx
        cases hq : i - f'.getAppArgs.length with
        | zero =>
          rw [hq] at hx hx'
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hx'
          subst hx hx'
          exact ha
        | succ q => rw [hq] at hx; simp at hx
    | _ => simp [Expr.ErasedEq] at h
  | _ =>
    intro e' h
    cases e' <;> simp_all [Expr.ErasedEq, Expr.getAppFn, Expr.getAppArgs]

/-- **Opening a term erasure-equal to a closed telescope**: it opens, its
body is the telescope's body and its domains the closed pieces, up to
erasure. -/
theorem open_of_erasedEq_closeTelescope :
    ∀ (nds : List (Expr × BinderMeta)) (d : Nat) (body e : Expr),
      (∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) → body.looseBVarsBounded 0 = true →
      Expr.ErasedEq e (closeTelescope nds d body) →
      ∃ xs rest, openPisAtFvars nds.length e d = some (xs, rest) ∧ Expr.ErasedEq rest body ∧
        ∀ (i : Nat) (x nd : Expr), xs[i]? = some x → nds[i]?.map (·.1) = some nd →
          Expr.ErasedEq x.fvarTypeD nd
  | [], d, body, e, _, _, he => by
    refine ⟨[], e, by simp [openPisAtFvars], by simpa [closeTelescope] using he,
      fun i x nd hx _ => nomatch hx⟩
  | (dom, bm) :: nds, d, body, e, hcl, hb, he => by
    cases e with
    | forallE a b bm' =>
      simp only [closeTelescope] at he
      obtain ⟨-, ha, hbE⟩ := he
      have hcl' : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true :=
        fun p hp => hcl p (List.mem_cons_of_mem _ hp)
      have hC := closeTelescope_bounded nds (d + 1) body hcl' hb
      have hE : Expr.ErasedEq (b.instantiate1 (.fvar d a)) (closeTelescope nds (d + 1) body) :=
        Expr.ErasedEq.trans (Expr.ErasedEq.instantiate1 hbE (v' := .fvar d dom) rfl)
          (erasedEq_abstract1_instantiate1 _ 0 hC)
      obtain ⟨xs, rest, hop, hrest, hdoms⟩ :=
        open_of_erasedEq_closeTelescope nds (d + 1) body _ hcl' hb hE
      refine ⟨.fvar d a :: xs, rest, ?_, hrest, fun i x nd hx hnd => ?_⟩
      · simp only [List.length_cons, openPisAtFvars, hop]
      · cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hnd
          subst hx hnd
          exact ha
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx hnd
          exact hdoms i x nd hx hnd
    | _ => simp [closeTelescope, Expr.ErasedEq] at he

end ConLeche.Model
