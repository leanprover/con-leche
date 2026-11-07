module

public import ConLeche.Semantics.Decl
public import ConLeche.Verify.Extend.Inversions
import ConLeche.Kernel.Checker

@[expose] public section

/-!
# The declaration-level RUN inversions (task #148 T6)

Two inversions from `checkDecl`'s own steps into the V-free run
records of `Semantics/Decl.lean`: `certifyNatEqs` into `NatEqsRun`, and
a quotient record into `DeclQuotRun`.  Each inverts a statement
about the checker into a statement about the checker; no valuation, no
relation and no model appears in any of them.

Consumer: `Semantics/Bridge/DeclRun.lean`.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

variable {pins : List NatOpPinSet}

/-- **`certifyNatEqs`, exposed as runs** (task #161 P4 H1 at the
literal tier): the verdict is one `isDefEqCore` success per equation,
and the recorded form is the checker's literal call —
`fueledOps_isDefEq` at fuel `F`, depth `2`.  The P tier's
`NatOps` establishment consumes these through `DefEqClaim`. -/
theorem natEqsRun_of_certs {F : Nat} {env : Env} :
    ∀ (eqs : List (Expr × Expr)),
      certifyNatEqs (m := CheckM) (fueledOps .verified F) env eqs = .ok true →
      NatEqsRun F env eqs := by
  intro eqs
  induction eqs with
  | nil => intro _ eq heq; exact nomatch heq
  | cons e rest ih =>
    intro h eq heq
    simp only [certifyNatEqs, fueledOps_isDefEq, Bind.bind,
      Except.bind] at h
    cases hx : isDefEqCore .verified false env F 2 e.1 e.2 with
    | error err => rw [hx] at h; exact nomatch h
    | ok b =>
      cases b with
      | false =>
        rw [hx] at h
        simp only [Bool.false_eq_true, ite_false, pure, Except.pure,
          Except.ok.injEq] at h
      | true =>
        rw [hx] at h
        simp only [ite_true] at h
        rcases List.mem_cons.mp heq with rfl | heq'
        · exact hx
        · exact ih h eq heq'

/-! ## A quotient record

The comparison with the slot's pin, the slots it needs, and one fresh
push (`installBasisDecl_inv`). -/

/-- **A quotient record's check and install, bridged.** -/
theorem declQuotRunOf {env env₂ : Env} {k : QuotKind} {cv : ConstantVal}
    (h : checkQuotRecord (m := CheckM) env k cv = .ok env₂) :
    DeclQuotRun env k cv env₂ := by
  unfold checkQuotRecord at h
  by_cases h1 : quotPinHit k cv = true
  · rw [ite_eq_left h1] at h
    by_cases h2 : quotPredsOk env.find? k = true
    · rw [ite_eq_left h2] at h
      obtain ⟨hfresh, rfl⟩ := installBasisDecl_inv h
      exact ⟨h1, h2, Option.isNone_iff_eq_none.mpr hfresh, rfl⟩
    · rw [ite_eq_right h2] at h
      exact nomatch h
  · rw [ite_eq_right h1] at h
    exact nomatch h

end ConLeche.Semantics
