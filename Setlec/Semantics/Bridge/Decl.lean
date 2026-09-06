import Setlec.Semantics.Decl
import Setlec.Verify.Extend.Inversions
import Setlec.Verify.IotaWalkInv

/-!
# The declaration-level RUN inversions (task #148 T6; the derivation
half removed 2026-09-05)

Four inversions from `checkDecl`'s own steps into the V-free run
records of `SetBase/Decl.lean`: `certifyNatEqs` into `NatEqsRunR`, the
elimination-template fold into `DeclIndR.TemplatesR`, and the pinned
basis fold into `BasisInstallR`/`DeclBasisR`.  Each inverts a statement
about the checker into a statement about the checker; no valuation, no
relation and no model appears in any of them.

**What this file used to be.**  2 755 lines: the six per-kind
declaration bridges (`declDefnR`, `declThmR`, `declOpaqueR`,
`declAxiomR`, the `indDecl` walk packs, the four pin bridges) that took
`checkDecl`'s run and produced a `DeclR` *derivation* — the collapsed
model's front door, premised throughout on `checkBridge`
(`SetBase/Bridge/Main.lean`) and hence on `mode.betaGate = false`.  The
SetR removal's Stage C deleted the relation family those derivations
inhabited, so the bridges went with it; a proof-term probe had already
put every one of them outside both surviving capstones' closures and
outside the run route the graded fold calls.

The four survivors are here, and not in the grave, because each has a
live consumer: `SetBase/Bridge/DeclRun.lean` for the walks' runs and
the template fold, and `checkDeclRun_of`'s basis arm for the pair
below.
-/

namespace Setlec.Semantics

open Setlec.TT Setlec.TTVerify

/-- **`certifyNatEqs`, exposed as runs** (task #161 P4 H1 at the
literal tier): the verdict is one `isDefEqCore` success per equation,
and the recorded form is the checker's literal call —
`fueledOps_isDefEq` at fuel `F`, depth `2`.  The P tier's
`NatOpsP` establishment consumes these through `DefEqClaims2P`
instead of the relational `NatEqsR` below (whose `DefEq` only has
collapse-currency soundness). -/
theorem natEqsRunR_of_certs {μ : CheckMode} {F : Nat} {env : Env} :
    ∀ (eqs : List (Expr × Expr)),
      certifyNatEqs (m := CheckM) (fueledOps μ F) env eqs = .ok true →
      NatEqsRunR μ F env eqs := by
  intro eqs
  induction eqs with
  | nil => intro _ eq heq; exact nomatch heq
  | cons e rest ih =>
    intro h eq heq
    simp only [certifyNatEqs, fueledOps_isDefEq, Bind.bind,
      Except.bind] at h
    cases hx : isDefEqCore μ env F 2 e.1 e.2 with
    | error err => rw [hx] at h; exact nomatch h
    | ok b =>
      cases b with
      | false =>
        rw [hx] at h
        simp only [Bool.false_eq_true, if_false, pure, Except.pure,
          Except.ok.injEq] at h
      | true =>
        rw [hx] at h
        simp only [if_true] at h
        rcases List.mem_cons.mp heq with rfl | heq'
        · exact hx
        · exact ih h eq heq'

/-! ## `indDecl`, the back half: the elimination-template fold

`checkIndDecl`'s last-but-one step is a fold over `List.range nF`.  The
template fold is a pure stored-data install and inverts outright.  (Its
sibling, the projection-*function* fold, was parametric in `ProjFnR`'s
inversion and went with `ProjFnR`.) -/

/-- **The elimination-template fold, inverted.** -/
theorem templatesR_of {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (l : List Nat) {env' env₂ : Env},
      l.foldlM (installProjTemplateStep (m := CheckM) T ctorName lps
        nP nF) env' = .ok env₂ →
      DeclIndR.TemplatesR T ctorName lps nP nF env' l env₂
  | [], env', env₂, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | i :: l, env', env₂, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hstep : installProjTemplateStep (m := CheckM) T ctorName lps
        nP nF env' i with
    | error e => intro h; exact nomatch h
    | ok env'' =>
      intro h
      refine ⟨env'', ?_, templatesR_of l h⟩
      simp only [installProjTemplateStep] at hstep
      by_cases hfr : (env'.find? (projFnName T i)).isNone = true
      · rw [if_pos hfr] at hstep
        simp only [installProjTemplate] at hstep
        revert hstep
        cases hrec : env'.find? (T.str "rec") with
        | none =>
          intro hstep
          dsimp only at hstep
          simp only [pure, Except.pure, Except.ok.injEq] at hstep
          exact Or.inl hstep.symm
        | some ci =>
          match ci with
          | .recInfo cvR mI rP [rule] =>
            intro hstep
            dsimp only at hstep
            by_cases hcond :
                (env'.find? (projFnName T i)).isNone = true ∧
                  mI = rP ∧ rP = nP + 2 ∧ rule.ctor = ctorName ∧
                  i < nF
            · rw [if_pos hcond] at hstep
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              exact Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hfr,
                hstep.symm⟩
            · rw [if_neg hcond] at hstep
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              exact Or.inl hstep.symm
          | .recInfo cvR mI rP [] | .recInfo cvR mI rP (_ :: _ :: _)
          | .axiomInfo _ | .defnInfo _ _ _ | .thmInfo _ _
          | .indInfo _ _ | .ctorInfo _ _ _ | .projInfo _ =>
            intro hstep
            dsimp only at hstep
            simp only [pure, Except.pure, Except.ok.injEq] at hstep
            exact Or.inl hstep.symm
      · rw [if_neg hfr] at hstep
        simp only [pure, Except.pure, Except.ok.injEq] at hstep
        exact Or.inl hstep.symm


/-! ## `basisDecl`

The simplest branch: a guard on the pinned `Eq` former, then a fold of
duplicate checks.  `BasisInstallR` records exactly the fold's output —
each constant fresh, then consed — so the inversion is one induction
over `installBasisDecl_inv`. -/

/-- **The pinned-block fold, inverted** into `BasisInstallR`. -/
theorem foldlM_installBasisDecl_invR :
    ∀ (l : List ConstantInfo) {env env₁ : Env},
      l.foldlM (installBasisDecl (m := CheckM)) env = .ok env₁ →
      BasisInstallR env l env₁
  | [], env, env₁, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | ci :: l, env, env₁, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hi : installBasisDecl (m := CheckM) env ci with
    | error e => intro h; exact nomatch h
    | ok env' =>
      intro h
      obtain ⟨hfresh, rfl⟩ := installBasisDecl_inv hi
      exact ⟨Option.isNone_iff_eq_none.mpr hfresh,
        foldlM_installBasisDecl_invR l h⟩

/-- **`basisDecl`, bridged.** -/
theorem declBasisR {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {kind : BasisKind}
    (h : checkDecl μ (fueledOps μ F) env (.basisDecl kind) = .ok env₂) :
    DeclBasisR env kind env₂ := by
  simp only [checkDecl, Bind.bind, Except.bind] at h
  by_cases hk : kind = .quotK
  · subst hk
    by_cases hEq : env.find? eqName = some eqA
    · simp only [hEq, if_true] at h
      exact ⟨fun _ => hEq, foldlM_installBasisDecl_invR _ h⟩
    · simp [hEq] at h
  · simp only [if_neg hk] at h
    exact ⟨fun hh => absurd hh hk, foldlM_installBasisDecl_invR _ h⟩

end Setlec.Semantics
