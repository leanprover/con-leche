import ConLeche.SetP.Claims2P
import ConLeche.Semantics.Denote2Closed

/-!
# `AnnotOkP`'s substitution metatheory (task #161, P3 batch 2)

`AnnotOkP := AnnotOk2 ∧ AnnotValidV` is the P-tier truthfulness
currency (`Claims2P.lean`), and every threading clause that crosses a
binder needs it to survive the same two moves the halves survive
separately: lifting (`AnnotOk2_liftN` / `AnnotValidV_liftN`) and
instantiation (`AnnotOk2_inst0` / `AnnotValidV_inst0`).

The file exists for a *layering* reason rather than a mathematical
one.  `AnnotOkP` is defined in `Claims2P.lean`, which imports
`Annot/ValidV.lean`; so the conjunction's transport laws cannot live
beside the halves they are assembled from.  Nothing here is new
content — each lemma is `⟨half₁ …, half₂ …⟩`.

**The premises are paid per half.**  `AnnotValidV_inst` takes bit
validity of the substituted term, `AnnotOk2_inst` takes hereditary
truthfulness of it, and the conjunction takes exactly their
conjunction — no half is charged for the other's premise.  See
`Annot/ValidV.lean`'s note on why the `bvar` clause forces this.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory
open ConLeche.Semantics (AVExpr)
open ConLeche (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]

/-- Splitting the currency. -/
theorem AnnotOkP.ok2 {ρ : Nat → V} {e : AVExpr} (h : AnnotOkP V ρ e) :
    AnnotOk2 V ρ e := h.1

/-- …and its other half. -/
theorem AnnotOkP.validV {ρ : Nat → V} {e : AVExpr}
    (h : AnnotOkP V ρ e) : AnnotValidV V ρ e := h.2

/-- Assembling it. -/
theorem AnnotOkP.mk {ρ : Nat → V} {e : AVExpr} (h1 : AnnotOk2 V ρ e)
    (h2 : AnnotValidV V ρ e) : AnnotOkP V ρ e := ⟨h1, h2⟩

variable (V)

/-- **The currency through lifting** — both halves at the same
rewrite. -/
theorem AnnotOkP_liftN (n : Nat) (e : AVExpr) (k : Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (e.liftN n k) ↔ AnnotOkP V (shiftE n k ρ) e :=
  and_congr (AnnotOk2_liftN V n e k ρ) (AnnotValidV_liftN V n e k ρ)

variable {V}

/-- **The currency through outermost substitution** — the β/ζ
transport form, the shape every reduction clause consumes. -/
theorem AnnotOkP_inst0 {e a : AVExpr} {ρ : Nat → V}
    (ha : AnnotOkP V ρ a) :
    AnnotOkP V ρ (e.inst a) ↔
      AnnotOkP V (cons (interp2 V ρ a) ρ) e :=
  and_congr (AnnotOk2_inst0 V ha.1) (AnnotValidV_inst0 V ha.2)

/-- **Weakening a hoisted fact under one more binder**, in the P
currency: `AnnotOk2.hoist_lift`'s mirror, and what `CtxOkP.weakenTop`
uses to move a leaf's fourth conjunct across the new head. -/
theorem AnnotOkP.hoist_lift {Δa : List AVExpr} {X e : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ e) :
    ∀ ρ : Nat → V, Sat2 V (X :: Δa) ρ → AnnotOkP V ρ e.lift := by
  intro ρ hρ
  refine (AnnotOkP_liftN V 1 e 0 ρ).mpr ?_
  rw [shiftE_zero]
  exact h _ (Sat2_tail hρ)

/-- **The stored leaves are `inst`-invariant** — `denoteP_beta`'s
second leaf premise, discharged from the erasure link and the
collapse-lane closedness field.  (Shared home: both the infer and the
whnf quarters proved this independently at their batches; deduplicated
here at the merge.) -/
theorem acval_inst_self {env : ConLeche.Env}
    (m : EnvS2Core V env) (n : ConLeche.Name)
    (ψ : ConLeche.Name → Nat) (y : AVExpr) (k : Nat) :
    (m.acval n ψ).inst y k = m.acval n ψ :=
  AVExpr.inst_eq_self _
    (by rw [m.acval_erase]
        exact VExpr.bvarsBelow.mono (Nat.zero_le k)
          (m.cval_closed n ψ)) y

end ConLeche.SetP
