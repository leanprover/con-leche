module

import ConLeche.Verify.Denote.OpenRevDenote
public import ConLeche.Model.IndPointKit
public import ConLeche.Model.BasisEq
public section

/-!
# The two opened towers, read (task #161, IND TIER part 5)

`openPisAtFvars_denotePTele` and `instLamsAt_denotePTele`: **the reading
is blind to an opener** (`denoteMeta_erasedEq`'s `fvar` clause compares
indices only), so an `openPisAtFvars`/`instLamsAt` run at any
same-index opener spine produces the same tower.

The λ tower is a `LamTele` relation: `AnnotTerm`'s `.lam` carries a
*bit*, and `LamTele` quantifies the bits existentially exactly as
`PiTeleAV` does; the consumers read neither.  `PiTeleAV.length` bounds
an index into the tail context.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name BinderMeta)

universe w

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## The opened `∀` telescope -/

/-- **The opening walk, read**: opening a
telescope whose reading succeeds yields the `.pi` tower's context, the
opened body's reading, and each opener's annotation read *at its own
depth* to its tower entry. -/
theorem openPisAtFvars_denotePTele :
    ∀ (k : Nat) {e : Expr} {j : Nat} {fvs : List Expr} {body : Expr}
      {T : AnnotTerm},
      openPisAtFvars k e j = some (fvs, body) →
      denoteMeta acval env φ j e = some T →
      ∃ (Γ : List AnnotTerm) (R : AnnotTerm),
        PiTeleAV k T Γ R ∧
        denoteMeta acval env φ (j + k) body = some R ∧
        ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
          denoteMeta acval env φ (j + i) (Expr.fvarTypeD x)
            = some (Γ.getD (k - 1 - i) default) := by
  intro k
  induction k with
  | zero =>
    intro e j fvs body T h hT
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], T, .nil, hT, fun i x hx => nomatch hx⟩
  | succ k ih =>
    intro e j fvs body T h hT
    match e, h with
    | .forallE dom bodyE mb, h =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars k (bodyE.instantiate1 (.fvar j dom))
          (j + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [denoteMeta_forallE] at hT
        cases hA : denoteMeta acval env φ j dom with
        | none => rw [hA] at hT; exact nomatch hT
        | some A => ?_
        rw [hA] at hT
        cases hB : denoteMeta acval env φ (j + 1)
            (bodyE.instantiate1 (.fvar j dom)) with
        | none => rw [hB] at hT; exact nomatch hT
        | some B => ?_
        rw [hB] at hT
        obtain rfl : T = .pi 0 (pwBit φ mb.pw) A B := by
          simpa using hT.symm
        obtain ⟨Γ', R, htele, hbody, hdoms⟩ := ih hop hB
        have hΓlen : Γ'.length = k := htele.length
        refine ⟨Γ' ++ [A], R, .cons htele, ?_, ?_⟩
        · rw [show j + (k + 1) = j + 1 + k from by omega]
          exact hbody
        · intro i x hx
          cases i with
          | zero =>
            obtain rfl : Expr.fvar j dom = x := by simpa using hx
            show denoteMeta acval env φ (j + 0) dom = _
            rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
              simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD]
              rw [List.getElem?_append_right (by omega), hΓlen,
                Nat.sub_self]
              rfl]
            exact hA
          | succ i =>
            rw [List.getElem?_cons_succ] at hx
            have h1 := hdoms i x hx
            have hik : i < k := by
              rcases Nat.lt_or_ge i k with h' | h'
              · exact h'
              · exfalso
                rw [List.getElem?_eq_none
                  (by rw [openPisAtFvars_length _ hop]; omega)] at hx
                exact nomatch hx
            rw [show (Γ' ++ [A]).getD (k + 1 - 1 - (i + 1)) default
                = Γ'.getD (k - 1 - i) default from by
              simp only [List.getD]
              rw [show k + 1 - 1 - (i + 1) = k - 1 - i from by omega,
                List.getElem?_append_left (by omega)]]
            rw [show j + (i + 1) = j + 1 + i from by omega]
            exact h1

/-! ## The λ telescope -/

end ConLeche.Model
