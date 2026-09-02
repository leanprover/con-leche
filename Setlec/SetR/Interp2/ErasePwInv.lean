import Setlec.SetR.Install.Axiom

/-!
# The `erasePw ∘ eraseNames` head inversions (task #161)

`ConstantVal.matchesPin` compares through `erasePw` *and*
`eraseNames`.  `Install/Axiom.lean` has the two constant-head
inversions; the pinned telescopes need the four remaining heads, and
composing the two erasures once here keeps every consumer's chain one
step per node.

These lemmas landed in `Interp2/AxiomBitsP.lean` (ENDGAME A) and moved
here **verbatim** at ENDGAME D, when the reduce-operation pin's shape
lemma (`Interp2/ReduceOpsP.lean`) needed them from *below* `HarvestP`
— which `AxiomBitsP` imports.  Nothing else changed.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (Expr Name Level BinderMeta)

/-- `erasePw ∘ eraseNames` inversion at a `∀`: the head is a `∀`, and
its name and meta are exactly what the comparison forgives. -/
theorem erasePwNames_forallE_invS {e : Expr} {n : Name} {ty b : Expr}
    {m : BinderMeta}
    (h : e.erasePw.eraseNames = .forallE n ty b m) :
    ∃ n' ty' b' m', e = .forallE n' ty' b' m' ∧
      ty'.erasePw.eraseNames = ty ∧ b'.erasePw.eraseNames = b := by
  cases e with
  | forallE n' ty' b' m' =>
    simp only [Expr.erasePw, Expr.eraseNames, Expr.forallE.injEq] at h
    exact ⟨n', ty', b', m', rfl, h.2.1, h.2.2.1⟩
  | _ => simp only [Expr.erasePw, Expr.eraseNames] at h; exact nomatch h

/-- `erasePw ∘ eraseNames` inversion at a sort (both erasures fix
it). -/
theorem erasePwNames_sort_invS {e : Expr} {u : Level}
    (h : e.erasePw.eraseNames = .sort u) : e = .sort u := by
  cases e with
  | sort u' => simp only [Expr.erasePw, Expr.eraseNames] at h; rw [h]
  | _ => simp only [Expr.erasePw, Expr.eraseNames] at h; exact nomatch h

/-- `erasePw ∘ eraseNames` inversion at an application. -/
theorem erasePwNames_app_invS {e : Expr} {f a : Expr}
    (h : e.erasePw.eraseNames = .app f a) :
    ∃ f' a', e = .app f' a' ∧ f'.erasePw.eraseNames = f ∧
      a'.erasePw.eraseNames = a := by
  cases e with
  | app f' a' =>
    simp only [Expr.erasePw, Expr.eraseNames, Expr.app.injEq] at h
    exact ⟨f', a', rfl, h.1, h.2⟩
  | _ => simp only [Expr.erasePw, Expr.eraseNames] at h; exact nomatch h

/-- `erasePw ∘ eraseNames` inversion at a constant (the composite of
`Install/Axiom.lean`'s two head inversions). -/
theorem erasePwNames_const_invS {e : Expr} {n : Name} {us : List Level}
    (h : e.erasePw.eraseNames = .const n us) : e = .const n us :=
  erasePw_const_invS (eraseNames_const_invS h)

/-- `erasePw ∘ eraseNames` inversion at a bound variable. -/
theorem erasePwNames_bvar_invS {e : Expr} {i : Nat}
    (h : e.erasePw.eraseNames = .bvar i) : e = .bvar i := by
  cases e with
  | bvar i' => simp only [Expr.erasePw, Expr.eraseNames] at h; rw [h]
  | _ => simp only [Expr.erasePw, Expr.eraseNames] at h; exact nomatch h


end Setlec.SetR.Interp2
