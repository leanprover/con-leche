module

public import ConLeche.Model.Inductives.BlockRecRule

public section

/-!
# Frame openings, extended by openers

Two facts about opening lists: a frame opening extended by a
telescope's own openers (`FvarList.openExtend`), or by the `ih`
openers standing before a position (`FvarList.openerExtend`), is again
a frame opening.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BinderMeta PropWhen)

universe uv

variable {V : Type uv} [SetTheory V] {env : Env}

/-- **The opener list, extended by the openers standing before it**,
is a frame opening: `openPisAtFvars` puts opener `k` at index
`rP + nF + k`, so the first `r` of them REVERSED head the opening
list, exactly as `FvarList`'s descending index wants. -/
theorem FvarList.openerExtend {E r : Nat} {L fvs : List Expr} (hL : FvarList E L)
    (hidx : ∀ (j : Nat) (x : Expr), fvs[j]? = some x → ∃ ty, x = Expr.fvar (E + j) ty)
    (hwsty : ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
      Expr.WScoped (E + j) (Expr.fvarTypeD x))
    (hlen : r ≤ fvs.length) :
    FvarList (E + r) ((fvs.take r).reverse ++ L) := by
  have htl : (fvs.take r).length = r := by rw [List.length_take]; omega
  refine ⟨by rw [List.length_append, List.length_reverse, htl, hL.1]; omega,
    fun j hj => ?_, fun x hx => ?_⟩
  · by_cases hjr : j < r
    · have hlt : r - 1 - j < (fvs.take r).length := by rw [htl]; omega
      obtain ⟨y, hy⟩ : ∃ y, (fvs.take r)[r - 1 - j]? = some y :=
        ⟨(fvs.take r)[r - 1 - j], List.getElem?_eq_getElem hlt⟩
      obtain ⟨ty, hty⟩ := hidx (r - 1 - j) y (by
        rw [← hy, List.getElem?_take_of_lt (show r - 1 - j < r from by omega)])
      refine ⟨ty, ?_⟩
      rw [List.getElem?_append_left (by rw [List.length_reverse, htl]; omega),
        List.getElem?_reverse (by rw [htl]; omega), htl, hy, hty]
      congr 2
      omega
    · obtain ⟨ty, hty⟩ := hL.2.1 (j - r) (by omega)
      refine ⟨ty, ?_⟩
      rw [List.getElem?_append_right (by rw [List.length_reverse, htl]; omega),
        List.length_reverse, htl, hty]
      congr 2
      omega
  · rcases List.mem_append.mp hx with hx' | hx'
    · rw [List.mem_reverse] at hx'
      obtain ⟨q, hq⟩ := List.getElem?_of_mem hx'
      have hqr : q < r := by
        have := (List.getElem?_eq_some_iff.mp hq).1
        rw [htl] at this; exact this
      have hq' : fvs[q]? = some x := by
        rw [← hq, List.getElem?_take_of_lt hqr]
      obtain ⟨ty, rfl⟩ := hidx q x hq'
      have := hwsty q _ hq'
      simp only [Expr.WScoped]
      exact ⟨by omega, this⟩
    · exact Expr.WScoped.mono (by omega) (hL.2.2 x hx')

end ConLeche.Model
