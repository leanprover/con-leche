module

import ConLeche.Verify.EnvGuards
public import ConLeche.Verify.NatOpFrag

public section

/-!
# The pinned `ofReduce` axioms' shapes (V-free)

`ofReduceNat`/`ofReduceBool` differ only in their element type, so
every shape fact about them is one `split`.  Both soundness routes
consume these and neither may import the other, so they live in the
shared tier (task #148 T6).
-/

namespace ConLeche.Verify

open ConLeche.Term

/-! ## The two shapes, uniformly

`ofReduceOp` and `reduceElemName` both branch on the axiom's name, so
every fact below is stated once and discharged by `rcases` on the two
possibilities. -/

/-- The pinned type of an `ofReduce*` axiom, in the uniform spelling
its two instances share. -/
theorem ofReducePin_type {n : Name}
    (hn : n = ofReduceNatName ∨ n = ofReduceBoolName) :
    (ofReducePinA n).type =
      .forallE
        (.const (reduceElemName (ofReduceOp n)) [])
        (.forallE
          (.const (reduceElemName (ofReduceOp n)) [])
          (.forallE
            (Expr.mkAppN (.const eqName [.succ .zero])
              [.const (reduceElemName (ofReduceOp n)) [],
               .app (.const (ofReduceOp n) []) (.bvar 1), .bvar 0])
            (Expr.mkAppN (.const eqName [.succ .zero])
              [.const (reduceElemName (ofReduceOp n)) [],
               .bvar 2, .bvar 1]))) := by
  rcases hn with rfl | rfl <;> rfl

/-- The element inductive's pinned type is `Sort 1`. -/
theorem reduceElem_sort {env : Env} {c : Name}
    (h : reduceElemOk env c = true) :
    ∃ ci, env.find? (reduceElemName c) = some ci ∧
      ci.toConstantVal.levelParams = [] ∧
      ci.toConstantVal.type = .sort (.succ .zero) := by
  by_cases hc : c = reduceNatName
  · rw [reduceElemOk, ite_eq_left hc] at h
    rw [reduceElemName, ite_eq_left hc]
    cases hf : env.find? natName with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      cases ci with
      | indInfo cvN caps =>
        refine ⟨.indInfo cvN caps, rfl, ?_, ?_⟩
        · simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            decide_eq_true_eq] at h
          exact h.1.2
        · simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at h
          show cvN.type = _
          simpa [natA, ConstantInfo.toConstantVal, BasisDSL.type1] using h.2
      | _ => exact nomatch h
  · rw [reduceElemOk, ite_eq_right hc] at h
    rw [reduceElemName, ite_eq_right hc]
    cases hf : env.find? boolName with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      cases ci with
      | indInfo cvB caps =>
        refine ⟨.indInfo cvB caps, rfl, ?_, ?_⟩
        · simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            decide_eq_true_eq] at h
          exact h.1.2
        · simp only [ConstantVal.matchesPin, Bool.and_eq_true,
            beq_iff_eq] at h
          show cvB.type = _
          simpa [boolCvA] using h.2
      | _ => exact nomatch h

/-- Name and level-parameter components of a `matchesPin` hit. -/
theorem matchesPin_invT {cv pin : ConstantVal}
    (h : ConstantVal.matchesPin cv pin = true) :
    cv.name = pin.name ∧ cv.levelParams = pin.levelParams := by
  simp only [ConstantVal.matchesPin, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

end ConLeche.Verify
