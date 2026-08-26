import Setlec.TTVerify.ProjStep

/-!
# The `isDefEq` step of `CheckStepTT`

`DefEqClaimsTT` at `fuel + 1`: a positive definitional-equality verdict
yields a derivable equation.  Transpose of `defeq_claims`
(`Setlec/Model/Core/DefEq.lean`).

**Contract (3), proved in its strongest form** (§12.3): the conclusion
is an unconditional `Deq`, with no typing hypotheses on either side.
Contracts (1) and (2) are refuted — (1) by the checker's own
post-#100 de-gating, (2) by F1 — and the equation carries no typing
because `eqE`'s type slot is inert, so the strongest form is also the
cheapest.

## The shape

`defeqBody` is `defeqLoop` at its own budget, and `defeqLoop` iterates
`defeqStep` with the continuation abstracted — the checker's own
design decision, and the bridge inherits its benefit: **every lemma
about the body is proved once, with a hypothesis about the
continuation, and the loop lemma is one induction on the budget**
(`Setlec/Kernel/Core.lean`).  That is the same factoring `whnfLoop`
got, and for the same reason.

`defeqStep`'s moves, in order, with what discharges each:

| move | discharged by |
|---|---|
| syntactic `a == b` | `Deq.refl` |
| `whnfCore` both sides | `WhnfCoreClaimsTT`, twice |
| hoisted proof irrelevance | `proof_irrel_step` |
| literal acceleration | `reduceNat_stepTT` |
| lazy delta | `denote_delta_step` — an **identity** (§2) |
| the stuck configuration | `DefEqStuckStepTT` (named) |
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- The continuation's contract, which is `DefEqClaimsTT`'s own shape
at the loop's remaining budget.

**The depth is fixed**, not quantified: `defeqLoop` hands `defeqStep` a
continuation already applied to the ambient depth, and every use of it
inside the body is at that depth.  The clauses that *do* go deeper —
the `∀` and `λ` congruences — recurse through `r.defeq` instead, which
is the claim at `fuel`, not the continuation. -/
def DefEqContTT {env : Env} (m : EnvTT env) (φ : Name → Nat) (d : Nat)
    (k : Expr → Expr → CheckM Bool) : Prop :=
  ∀ {Δ : List VExpr} {a b : Expr}, k a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → Deq Δ va vb

/-- **One iteration of the lazy-delta loop.**  The body's contract,
with the continuation abstracted exactly as the checker abstracts
it. -/
def DefEqStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {k : Expr → Expr → CheckM Bool}, DefEqContTT m φ d k →
    ∀ {Δ : List VExpr} {a b : Expr},
      defeqStep (pureFns env fuel) env d k a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
      ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
        denote m.cval env φ d b = some vb → Deq Δ va vb

/-! ## The budget induction

One induction, exactly as for `whnfLoop` — and for the same reason:
the checker abstracts the continuation, so the body's lemma is proved
once with a hypothesis about it and the loop is a trivial induction.
The bridge inherits the factoring rather than rediscovering it. -/

/-- The lazy-delta loop preserves the claim at every budget. -/
theorem defeqLoop_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hstep : DefEqStepTT m φ fuel) :
    ∀ (budget : Nat) {d : Nat} {Δ : List VExpr} {a b : Expr},
      defeqLoop (pureFns env fuel) env d budget a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
      ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
        denote m.cval env φ d b = some vb → Deq Δ va vb := by
  intro budget
  induction budget with
  | zero =>
    intro d Δ a b h
    rw [defeqLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d Δ a b h
    rw [defeqLoop] at h
    refine hstep ?_ h
    intro Δ' a' b' hkk
    exact ih hkk

/-- **`DefEqClaimsTT` at `fuel + 1`.**  The third quarter of
`CheckStepTT`, modulo the step. -/
theorem defeq_claimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hstep : DefEqStepTT m φ fuel) :
    DefEqClaimsTT m φ (fuel + 1) := by
  intro d a b Δ h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  rw [isDefEqCore_succ, defeqBody] at h
  exact defeqLoop_claim m φ hstep defeqLoopFuel h hwa hba hLa hwb hbb hLb
    hCa hCb hva hvb

/-! ## The step's opening moves

The first four are the reduction machinery already proved, applied in
the order the checker applies them.  Each ends either in a verdict
(and a `Deq` chain through the two `whnfCore` equations) or in a
handoff to the continuation. -/

/-- The frame conditions and denotation of a `whnfCore` reduct, bundled
— both sides of every move need exactly this package. -/
theorem whnfCore_package {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel d : Nat} {Δ : List VExpr} {a a' : Expr} {va : VExpr}
    (ihwc : WhnfCoreClaimsTT m φ fuel)
    (hw : whnfCore env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOk m.cval env φ d Δ a)
    (hva : denote m.cval env φ d a = some va) :
    ∃ va', denote m.cval env φ d a' = some va' ∧ Deq Δ va va' ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧ CtxOk m.cval env φ d Δ a' := by
  obtain ⟨va', hva', hD⟩ := ihwc hw hws hb hLb hC hva
  exact ⟨va', hva', hD, whnfCore_WScoped m.wf fuel hw hws,
    whnfCore_looseBVars m.wf fuel hw hb,
    fun l hl => hLb l (whnfCore_fvarLeaves m.wf fuel hw l hl),
    CtxOk.of_subset (whnfCore_fvarLeaves m.wf fuel hw) hC⟩

/-! ### A lemma withdrawn, and why

A `defeqStep_reduce` briefly lived here: "either the syntactic
short-circuit settles it, or both sides reduce and here is the
package".  It was true, it compiled, and it is **not composable** — so
it is gone rather than left as scaffolding.

The reason is worth a line because it will recur wherever a checker
body is a `do` block.  `defeqStep`'s moves are *sequential*: each one
consumes the residual hypothesis left by the previous `split`.  A lemma
that ends after two moves can hand back the facts it derived, but it
cannot hand back **the residual**, because the residual is a tail of an
anonymous `do` block and there is nothing to name it with.  So the next
move cannot start where it stopped.

> **A checker body factors into lemmas exactly where the *checker*
> factors into functions.**  `whnfLoop`/`whnfStep` and
> `defeqLoop`/`defeqStep` factor, so the loop lemmas do.  The moves
> *inside* `defeqStep` do not, so they cannot.

That is the same fact as §8.6's boundary rule, seen from the inside of
a body rather than at an obligation: `stuckIrrel` is nameable and so it
is where the obligation sits; the four moves before it are not, so
`defeqStep`'s claim is one proof.

`whnfCore_package` survives the withdrawal because it is not a *stage*
of the step but a *fact about a reduct*, and every move wants it. -/

/-! ## The step's obligations, at the checker's own function boundaries

The factoring rule (§8.6) fixes where these may sit: at functions the
checker names.  `defeqStep` calls four such, and the two that are not
already proved become obligations.

* `proofIrrel` — hoisted before lazy delta, and called again from
  `stuckIrrel`.  Two consumers, so it is a boundary worth having.  Its
  `Prop` branch is `proof_irrel_step`; its unit-like branch wants
  `punitEta` and the pinned recursor shapes.
* `stuckIrrel` — the five rescues.
* `defeqSpine` — the same-head short-circuit.
* `reduceNat` and `unfoldDefinition` — **proved**
  (`reduceNat_stepTT`, `denote_delta_step`). -/

/-- `proofIrrel`'s verdict yields an equation. -/
def ProofIrrelStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    proofIrrelP env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → Deq Δ va vb

/-- `defeqSpine`'s verdict yields an equation. -/
def DefEqSpineStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    defeqSpineP env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → Deq Δ va vb

/-- **The stuck configuration**: `defeqStep` reached its last block —
neither side reduced, neither is a proof, neither head unfolds — so the
verdict came from a leaf comparison, a congruence, or `stuckIrrel`.

**This is a case restriction, not a stage split**, and the distinction
is what makes it legitimate where the deleted `DefEqLeafStepTT` was
not.  Its hypothesis is `defeqStep`'s *own* call, with the earlier
moves' negative outcomes recorded as hypotheses; it never refers to a
position inside the body.  A consumer applies it to the untouched
original `h`, which is why it composes where a mid-body lemma cannot.

> **You may not slice a body into stages; you may slice its input
> space into cases.**  Every clause lemma in this bridge is the latter
> (`infer_app_claim` is `inferBody` restricted to `.app`); the deleted
> lemma was the former. -/
def DefEqStuckStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {k : Expr → Expr → CheckM Bool}
    {a b a' b' : Expr},
    defeqStep (pureFns env fuel) env d k a b = .ok true →
    (a == b) = false →
    whnfCore env fuel d a = .ok a' → whnfCore env fuel d b = .ok b' →
    (a' == b') = false →
    proofIrrelP env fuel d a' b' = .ok false →
    unfoldableHead env a' = false → unfoldableHead env b' = false →
    Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a' →
    Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b' →
    CtxOk m.cval env φ d Δ a' → CtxOk m.cval env φ d Δ b' →
    ∀ {va' vb' : VExpr}, denote m.cval env φ d a' = some va' →
      denote m.cval env φ d b' = some vb' → Deq Δ va' vb'

/-! ### One that was drafted and deleted

A `DefEqLeafStepTT` for "the stuck block's leaves and congruences"
was written and removed on the same pass.  The `false, false` block is
**not a named checker function** — the obligation could only be phrased
by re-invoking `defeqStep` with a dummy continuation, which is a
fabricated boundary, i.e. precisely the "sliced where the code does
not slice" defect §8.6's factoring rule names.

So the leaves and congruences are proved *inside* `defeqStep`'s claim,
and the obligations are exactly the three checker functions above.
Writing the rule down did not stop me drafting the violation; reading
it back did, which is the argument for writing rules down at all. -/

/-! ## The step, as one proof

The delta moves are where §2's identity pays inside a proof rather than
in prose: unfolding a side does not change its denotation, so the
continuation is handed *the same* `VExpr` and the accumulated equation
does not grow.  Each of the four lazy-delta branches is therefore two
lines. -/

/-- Unfolding one side and continuing: the reduct's frame conditions
and its (identical) denotation, packaged for the four delta
branches. -/
theorem delta_package {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {d : Nat} {Δ : List VExpr} {x y : Expr} {vx : VExpr}
    (hu : unfoldDefinition env x = some y)
    (hws : Expr.WScoped d x) (hb : x.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded x) (hC : CtxOk m.cval env φ d Δ x)
    (hvx : denote m.cval env φ d x = some vx) :
    denote m.cval env φ d y = some vx ∧ Expr.WScoped d y ∧
      y.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded y ∧
      CtxOk m.cval env φ d Δ y :=
  ⟨denote_delta_step m φ hcl hu hvx,
    unfoldDefinition_WScoped m.wf hu hws,
    unfoldDefinition_looseBVars m.wf hu hb,
    fun l hl => hLb l (unfoldDefinition_fvarLeaves m.wf hu l hl),
    CtxOk.of_subset (unfoldDefinition_fvarLeaves m.wf hu) hC⟩

/-- **`DefEqStepTT`**, modulo the three checker-function obligations. -/
theorem defeqStep_claim {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsTT m φ fuel) (ihw : WhnfClaimsTT m φ fuel)
    (hpi : ProofIrrelStepTT m φ fuel) (hstk : DefEqStuckStepTT m φ fuel)
    (hspine : DefEqSpineStepTT m φ fuel) : DefEqStepTT m φ fuel := by
  intro d k hk Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  have h0 := h
  simp only [defeqStep, Bind.bind, Except.bind, whnfCore_def,
    proofIrrel_fold, reduceNat_fold, defeqSpine_fold, stuckIrrel_fold,
    defeq_def] at h
  split at h
  · -- syntactic
    next hab =>
    obtain rfl : a = b := eq_of_beq hab
    obtain rfl : va = vb := by rw [hva] at hvb; exact Option.some.inj hvb
    exact Deq.refl
  · cases hwca : whnfCore env fuel d a with
    | error err => rw [hwca] at h; exact nomatch h
    | ok a' =>
    rw [hwca] at h
    dsimp only at h
    cases hwcb : whnfCore env fuel d b with
    | error err => rw [hwcb] at h; exact nomatch h
    | ok b' =>
    rw [hwcb] at h
    dsimp only at h
    obtain ⟨va', hva', hDa, hwa', hba', hLa', hCa'⟩ :=
      whnfCore_package m φ ihwc hwca hwa hba hLa hCa hva
    obtain ⟨vb', hvb', hDb, hwb', hbb', hLb', hCb'⟩ :=
      whnfCore_package m φ ihwc hwcb hwb hbb hLb hCb hvb
    -- from here every verdict is `Deq Δ va' vb'`, chained
    suffices hmid : Deq Δ va' vb' from (hDa.trans hmid).trans hDb.symm
    split at h
    · -- the reducts agree syntactically
      next hab' =>
      obtain rfl : a' = b' := eq_of_beq hab'
      obtain rfl : va' = vb' := by rw [hva'] at hvb'; exact Option.some.inj hvb'
      exact Deq.refl
    · cases hir : proofIrrelP env fuel d a' b' with
      | error err => rw [hir] at h; exact nomatch h
      | ok r =>
      rw [hir] at h
      dsimp only at h
      cases r with
      | true =>
        exact hpi hir hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
      | false =>
        -- literal acceleration, either side
        cases hna : (if !a'.hasFvar && !b'.hasFvar then
            reduceNatP env fuel d a' else pure none) with
        | error err => rw [hna] at h; exact nomatch h
        | ok o₁ =>
        rw [hna] at h
        dsimp only at h
        match o₁, hna, h with
        | some a₂, hna, h =>
          have hred : reduceNatP env fuel d a' = .ok (some a₂) := by
            split at hna
            · exact hna
            · exact nomatch hna
          obtain ⟨w, hw, hDw, hw2, hb2, hL2, hC2⟩ :=
            reduceNat_stepTT m φ ihw hred hwa' hba' hLa' hCa' hva'
          exact hDw.trans (hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hw hvb')
        | none, hna, h =>
        dsimp only at h
        cases hnb : (if !a'.hasFvar && !b'.hasFvar then
            reduceNatP env fuel d b' else pure none) with
        | error err => rw [hnb] at h; exact nomatch h
        | ok o₂ =>
        rw [hnb] at h
        dsimp only at h
        match o₂, hnb, h with
        | some b₂, hnb, h =>
          have hred : reduceNatP env fuel d b' = .ok (some b₂) := by
            split at hnb
            · exact hnb
            · exact nomatch hnb
          obtain ⟨w, hw, hDw, hw2, hb2, hL2, hC2⟩ :=
            reduceNat_stepTT m φ ihw hred hwb' hbb' hLb' hCb' hvb'
          exact (hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hva' hw).trans
            hDw.symm
        | none, hnb, h =>
        -- lazy delta
        cases hha : unfoldableHead env a' <;>
          cases hhb : unfoldableHead env b' <;>
          rw [hha, hhb] at h <;> dsimp only at h
        · -- neither head unfolds: the stuck configuration, applied to
          -- the *untouched* original hypothesis
          exact hstk h0 (by simpa using ‹¬(a == b) = true›) hwca hwcb
            (by simpa using ‹¬(a' == b') = true›) hir hha hhb
            hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
        · -- only the right head unfolds
          cases hub : unfoldDefinition env b' with
          | none => rw [hub] at h; exact nomatch h
          | some b₂ =>
            rw [hub] at h
            obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_package m φ hcl hub hwb' hbb' hLb' hCb' hvb'
            exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hva' hd2
        · -- only the left head unfolds
          cases hua : unfoldDefinition env a' with
          | none => rw [hua] at h; exact nomatch h
          | some a₂ =>
            rw [hua] at h
            obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_package m φ hcl hua hwa' hba' hLa' hCa' hva'
            exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2 hvb'
        · -- both heads unfold: the hints decide which side, or the
          -- same-head spine short-circuit fires
          have hboth : ∀ {x : CheckM Bool},
              (match unfoldDefinition env a', unfoldDefinition env b' with
                | some a₂, some b₂ => k a₂ b₂
                | _, _ => pure false) = .ok true → Deq Δ va' vb' := by
            intro x hbb2
            cases hua : unfoldDefinition env a' with
            | none => rw [hua] at hbb2; exact nomatch hbb2
            | some a₂ =>
            cases hub : unfoldDefinition env b' with
            | none => rw [hua, hub] at hbb2; exact nomatch hbb2
            | some b₂ =>
              rw [hua, hub] at hbb2
              obtain ⟨hdA, hwA, hbA, hLA, hCA⟩ :=
                delta_package m φ hcl hua hwa' hba' hLa' hCa' hva'
              obtain ⟨hdB, hwB, hbB, hLB, hCB⟩ :=
                delta_package m φ hcl hub hwb' hbb' hLb' hCb' hvb'
              exact hk hbb2 hwA hbA hLA hwB hbB hLB hCA hCB hdA hdB
          cases hlt1 : ReducibilityHint.lt (headHint env b')
              (headHint env a') <;> rw [hlt1] at h
          · -- the hints do not order the left below the right
            cases hlt2 : ReducibilityHint.lt (headHint env a')
                (headHint env b') <;> rw [hlt2] at h
            · cases hsr : (ReducibilityHint.sameRegular (headHint env a')
                  (headHint env b') && sameConstHeads a' b') <;>
                rw [hsr] at h
              · exact hboth (x := pure false) h
              · cases hsp : defeqSpineP env fuel d a' b' with
                | error err => rw [hsp] at h; exact nomatch h
                | ok r' =>
                rw [hsp] at h
                dsimp only at h
                cases r' with
                | true =>
                  exact hspine hsp hwa' hba' hLa' hwb' hbb' hLb'
                    hCa' hCb' hva' hvb'
                | false => exact hboth (x := pure false) h
            · -- the left side's hint is smaller: unfold the right
              cases hub : unfoldDefinition env b' with
              | none => rw [hub] at h; exact nomatch h
              | some b₂ =>
                rw [hub] at h
                obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
                  delta_package m φ hcl hub hwb' hbb' hLb' hCb' hvb'
                exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hva' hd2
          · -- the right side's hint is smaller: unfold the left
            cases hua : unfoldDefinition env a' with
            | none => rw [hua] at h; exact nomatch h
            | some a₂ =>
              rw [hua] at h
              obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
                delta_package m φ hcl hua hwa' hba' hLa' hCa' hva'
              exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2 hvb'

/-- **`DefEqClaimsTT` at `fuel + 1`**, with the step discharged: three
obligations remain, all at checker functions or a checker
configuration. -/
theorem defeq_claimsTT_closed {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsTT m φ fuel) (ihw : WhnfClaimsTT m φ fuel)
    (hpi : ProofIrrelStepTT m φ fuel) (hstk : DefEqStuckStepTT m φ fuel)
    (hspine : DefEqSpineStepTT m φ fuel) :
    DefEqClaimsTT m φ (fuel + 1) :=
  defeq_claimsTT m φ (defeqStep_claim m φ hcl ihwc ihw hpi hstk hspine)

end Setlec.TTVerify
