module

public import ConLeche.Rules.Rel
import ConLeche.Verify.Rules.RedVal
import ConLeche.Verify.BoostRed.BVBridge

/-!
# The bridge of `Infer.bvUnsat` (task #368)

A pure-core run that skipped the argument check of `U E C a`
(`bvUnsatSkip`) yields the rule:

* the premises on `E` and `C` come from the inference of `U E C` itself,
  whose head's type is the pinned statement of `U`, a literal Π-type, so
  the first domain is `BVLogicalExpr` on the nose (`Red.eq_of_redVal`);
* the reductions `eval (quoteAssign x) E ⟶ false` come from the gate
  (`bvUnsat_red`: the reader's relation and `eval`'s boost lemma,
  `Verify/BoostRed/BVBridge.lean`).
-/

public section

namespace ConLeche.Rules

open ConLeche (Env Expr Name)

variable {env : Env}

/-- The inference of `U E C` carries the inferences of `E` (at the formula
type) and `C`. -/
theorem bvUnsat_infer_parts {d : Nat} {E C a tf : Expr}
    (hhit : bvUnsatHit env.find? env.findProj? (.app (.app (.const unsatThmName []) E) C) a = true)
    (h : Infer env .full d (.app (.app (.const unsatThmName []) E) C) tf) :
    ∃ tE tC, Infer env .full d E tE ∧ DefEq env d tE (.const bvLogicalExprName []) ∧
      Infer env .full d C tC := by
  obtain ⟨cvU, hfU, hlU, htU⟩ := BVUnsat.pin_U_shape (bvUnsatOk_pins (bvUnsatHit_parts hhit).2)
  cases h with
  | app h1 _ hC _ =>
    cases h1 with
    | app h0 hw hE hd =>
      cases h0 with
      | const hf _ =>
        have hty : ∀ ci, env.find? unsatThmName = some ci →
            ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams [] = uTyE := by
          intro ci hci
          rcases hfU with h' | h' <;> rw [h'] at hci <;> cases hci <;>
            simp only [ConLeche.ConstantInfo.toConstantVal, hlU, htU] <;> rfl
        rw [hty _ hf] at hw
        have heq := Red.eq_of_redVal hw trivial
        simp only [uTyE, Expr.forallE.injEq] at heq
        obtain ⟨rfl, -⟩ := heq
        exact ⟨_, _, hE rfl, hd rfl, hC rfl⟩

/-- **The reductions the gate means**: where `bvUnsatHit` accepts, the
formula evaluates to `false` at every quoted assignment. -/
theorem bvUnsat_red {d : Nat} {E C a : Expr}
    (hhit : bvUnsatHit env.find? env.findProj? (.app (.app (.const unsatThmName []) E) C) a = true) :
    ∀ x : Std.Tactic.BVDecide.BVExpr.Assignment,
      Red env d (.app (.app (.const bvEvalName []) (quoteAssign x)) E)
        (.const boolFalseName []) :=
  BoostRed.bvUnsatOk_evalFalse (bvUnsatHit_parts hhit).2

/-- **`2 ^ k` evaluates**, where the gate accepts. -/
theorem bvUnsat_pow {d : Nat} {E C a : Expr}
    (hhit : bvUnsatHit env.find? env.findProj? (.app (.app (.const unsatThmName []) E) C) a = true) :
    ∀ k : Nat, Red env d (pow2E (.lit (.natVal k))) (.lit (.natVal (2 ^ k))) :=
  BoostRed.pow2_red (bvUnsatOk_pins (bvUnsatHit_parts hhit).2)

/-- **The bridge's skip case.** -/
theorem bvUnsat_bridge {d : Nat} {f a tf ty body : Expr}
    (hf : Infer env .full d f tf) (hw : Red env d tf (.forallE ty body))
    (hsk : bvUnsatSkip env.find? env.findProj? f a body = true) :
    Infer env .full d (.app f a) (body.instantiate1 a) := by
  have hhit := bvUnsatSkip_hit hsk
  obtain ⟨E, C, rfl⟩ : ∃ E C, f = .app (.app (.const unsatThmName []) E) C := by
    unfold bvUnsatHit at hhit
    split at hhit
    · rename_i c E C
      simp only [Bool.and_eq_true, beq_iff_eq] at hhit
      exact ⟨E, C, by rw [hhit.1.1]⟩
    · exact nomatch hhit
  obtain ⟨tE, tC, hE, hd, hC⟩ := bvUnsat_infer_parts hhit hf
  exact .bvUnsat hf hw hsk hE hd hC (bvUnsat_red hhit) (bvUnsat_pow hhit)

end ConLeche.Rules
