import Setlec.SetBase.Bridge.Infer

/-!
# The defeq quarter of `CheckStepR` (task #148, T3, batches a/c/d)

`DefEqClaimsR` at `fuel + 1`.  `defeqBody` is `defeqLoop` at its own
budget and `defeqLoop` iterates `defeqStep` with the continuation
abstracted — the checker's own factoring, which the bridge inherits:
the body's lemma is proved once with a hypothesis about the
continuation, and the loop is one induction on the budget.

`defeqStep`'s moves, in order, with what discharges each:

| move | discharged by |
|---|---|
| syntactic `a == b` | `DefEq.refl` (D1) |
| `whnfCore` both sides | `WhnfCoreClaimsR` twice, wrapped by `DefEq.ofRed` (D4) |
| hoisted proof irrelevance | `ProofIrrelStepR` (D8/D9) |
| literal acceleration | `ReduceNatStepR` (R8–R10, through D4) |
| lazy delta | `denote_delta_stepR` — an **identity**, so the chain does not grow |
| the stuck configuration | `DefEqStuckStepR` (D5–D7, D10–D14) |

## The batch-(a) headline: the binder congruences compose

`CtxOkR.openCong` below is the campaign's risk-R3 detection point, and
it **passes**.  `defeqStep` opens `.forallE n₁ ty₁ b₁` and
`.forallE n₂ ty₂ b₂` with *each side's own annotation*, so the two
opened bodies carry leaves `(d, n₁, ty₁)` and `(d, n₂, ty₂)` whose
denotations `A₁` and `A₂` are only definitionally equal — and the
recursive `isDefEqCore` call compares them in **one** context.  The
slack design serves this exactly: put `A₁` in the context, and give the
second side's leaf the package `Infer (A₁::Δ) (.bvar 0) (A₁.liftN 1)`
(the plain rule) together with `DefEq (A₁::Δ) (A₁.liftN 1) (A₂.liftN 1)`
— which is the domain certificate's own derivation, weakened by M1
(`DefEq.weakenHead`).  Nothing else is needed and nothing is pushed
anywhere: `CtxOkR.openWith`'s `hnew` argument has precisely that shape.

**Where the slack does *not* compose is elsewhere** — at the
`Infer x tx → Red μ Δ tx Shape` premise pairs of I6–I10, R6, R12–R14 and
D8–D13.  See the finding in `Setlec/SetR/DESIGN.md`; the obligations
below are named so that the gap is visible in the source.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-! ## The binder-congruence context step -/

/-- **Opening a binder congruence.**  The second side of a `∀`/`λ`
congruence is opened with *its own* annotation while the context holds
the *first* side's denotation; the leaf package is then the plain
`Infer.bvar` plus the weakened domain certificate.

This is design §0 decision 1 in one lemma, and the reason `CtxOkR`'s
leaf package is stated up to `DefEq` rather than as an identity. -/
theorem CtxOkR.openCong {cval : TConstVal} {φ : Name → Nat}
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {d : Nat} {Δ : List VExpr} {body ty : Expr} {n : Name} {A₁ A₂ : VExpr}
    (hb : CtxOkR mode cval env φ d Δ body)
    (ht : CtxOkR mode cval env φ d Δ ty)
    (hty : denote cval env φ d ty = some A₂)
    (htyb : Expr.fvarsBelow d ty)
    (hdom : DefEq mode env cval φ Δ A₁ A₂) :
    CtxOkR mode cval env φ (d + 1) (A₁ :: Δ)
      (body.instantiate1 (.fvar d n ty)) :=
  CtxOkR.openWith hcl hb ht hty htyb
    ⟨A₁.liftN 1, Infer.bvar rfl, hdom.weakenHead hcl A₁⟩

/-! ## The loop and its continuation -/

/-- The continuation's contract, which is `DefEqClaimsR`'s own shape at
the loop's remaining budget.  The depth is fixed, not quantified:
`defeqLoop` hands `defeqStep` a continuation already applied to the
ambient depth.  The clauses that *do* go deeper — the `∀` and `λ`
congruences — recurse through the claim at `fuel`, not through the
continuation. -/
def DefEqContR {env : Env} (m : EnvR env) (φ : Name → Nat) (d : Nat)
    (k : Expr → Expr → CheckM Bool) : Prop :=
  ∀ {Δ : List VExpr} {a b : Expr}, k a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR mode m.cval env φ d Δ a → CtxOkR mode m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → DefEq mode env m.cval φ Δ va vb

/-- **One iteration of the lazy-delta loop**, with the continuation
abstracted exactly as the checker abstracts it. -/
def DefEqStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {k : Expr → Expr → CheckM Bool}, DefEqContR (mode := mode) m φ d k →
    ∀ {Δ : List VExpr} {a b : Expr},
      defeqStep mode (pureFns mode env fuel) env d k a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      CtxOkR mode m.cval env φ d Δ a → CtxOkR mode m.cval env φ d Δ b →
      ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
        denote m.cval env φ d b = some vb → DefEq mode env m.cval φ Δ va vb

/-- The lazy-delta loop preserves the claim at every budget. -/
theorem defeqLoop_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hstep : DefEqStepR (mode := mode) m φ fuel) :
    ∀ (budget : Nat) {d : Nat} {Δ : List VExpr} {a b : Expr},
      defeqLoop mode (pureFns mode env fuel) env d budget a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      CtxOkR mode m.cval env φ d Δ a → CtxOkR mode m.cval env φ d Δ b →
      ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
        denote m.cval env φ d b = some vb →
        DefEq mode env m.cval φ Δ va vb := by
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

/-- **`DefEqClaimsR` at `fuel + 1`**, modulo the step. -/
theorem defeq_claimsR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hstep : DefEqStepR (mode := mode) m φ fuel) :
    DefEqClaimsR mode m φ (fuel + 1) := by
  intro d a b Δ h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  rw [isDefEqCore_succ, defeqBody] at h
  exact defeqLoop_claimR m φ hstep defeqLoopFuel h hwa hba hLa hwb hbb hLb
    hCa hCb hva hvb

/-! ## The step's obligations, at the checker's own function boundaries

`defeqStep` calls four functions the bridge cares about; two of them
(`reduceNat`, `unfoldDefinition`) are handled by `ReduceNatStepR` and
`denote_delta_stepR`, and the other two become obligations, together
with the stuck configuration. -/

/-- `proofIrrel`'s verdict yields an equation (D8/D9; batch c). -/
def ProofIrrelStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    proofIrrelP mode env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR mode m.cval env φ d Δ a → CtxOkR mode m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → DefEq mode env m.cval φ Δ va vb

/-- `defeqSpine`'s verdict yields an equation (D7's second entry
point). -/
def DefEqSpineStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    defeqSpineP mode env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOkR mode m.cval env φ d Δ a → CtxOkR mode m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → DefEq mode env m.cval φ Δ va vb

/-- **The stuck configuration**: `defeqStep` reached its last block —
neither side reduced, neither is a proof, neither head unfolds — so the
verdict came from a leaf comparison, a congruence (D5/D6/D7/D14) or
`stuckIrrel` (D10–D13).

This is a *case restriction*, not a stage split: its hypothesis is
`defeqStep`'s own call, with the earlier moves' negative outcomes
recorded, so a consumer applies it to the untouched original hypothesis
and it composes where a mid-body lemma cannot. -/
def DefEqStuckStepR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {k : Expr → Expr → CheckM Bool}
    {a b a' b' : Expr},
    defeqStep mode (pureFns mode env fuel) env d k a b = .ok true →
    (a == b) = false →
    whnfCore mode env fuel d a = .ok a' →
    whnfCore mode env fuel d b = .ok b' →
    (a' == b') = false →
    proofIrrelP mode env fuel d a' b' = .ok false →
    (if !a'.hasFvar && !b'.hasFvar then
      reduceNatP mode env fuel d a' else pure none) = .ok none →
    (if !a'.hasFvar && !b'.hasFvar then
      reduceNatP mode env fuel d b' else pure none) = .ok none →
    unfoldableHead env a' = false → unfoldableHead env b' = false →
    Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a' →
    Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b' →
    CtxOkR mode m.cval env φ d Δ a' → CtxOkR mode m.cval env φ d Δ b' →
    ∀ {va' vb' : VExpr}, denote m.cval env φ d a' = some va' →
      denote m.cval env φ d b' = some vb' → DefEq mode env m.cval φ Δ va' vb'

/-! ## The step, as one proof

The delta moves are where the identity of §7.2 pays inside a proof
rather than in prose: unfolding a side does not change its denotation,
so the continuation is handed *the same* `VExpr` and the accumulated
equation does not grow. -/

/-- Unfolding one side and continuing: the reduct's frame conditions and
its (identical) denotation, packaged for the four delta branches. -/
theorem delta_packageR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {d : Nat} {Δ : List VExpr} {x y : Expr} {vx : VExpr}
    (hu : unfoldDefinition env x = some y)
    (hws : Expr.WScoped d x) (hb : x.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded x) (hC : CtxOkR mode m.cval env φ d Δ x)
    (hvx : denote m.cval env φ d x = some vx) :
    denote m.cval env φ d y = some vx ∧ Expr.WScoped d y ∧
      y.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded y ∧
      CtxOkR mode m.cval env φ d Δ y :=
  ⟨denote_delta_stepR m φ hcl hu hvx,
    unfoldDefinition_WScoped m.wf hu hws,
    unfoldDefinition_looseBVars m.wf hu hb,
    fun l hl => hLb l (unfoldDefinition_fvarLeaves m.wf hu l hl),
    CtxOkR.of_subset (unfoldDefinition_fvarLeaves m.wf hu) hC⟩

/-- **`DefEqStepR`**, modulo the three checker-function obligations. -/
theorem defeqStep_claimR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsR mode m φ fuel)
    (hnat : ReduceNatStepR (mode := mode) m φ fuel)
    (hpi : ProofIrrelStepR (mode := mode) m φ fuel)
    (hstk : DefEqStuckStepR (mode := mode) m φ fuel)
    (hspine : DefEqSpineStepR (mode := mode) m φ fuel) :
    DefEqStepR (mode := mode) m φ fuel := by
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
    exact DefEq.refl
  · cases hwca : whnfCore mode env fuel d a with
    | error err => rw [hwca] at h; exact nomatch h
    | ok a' =>
    rw [hwca] at h
    dsimp only at h
    cases hwcb : whnfCore mode env fuel d b with
    | error err => rw [hwcb] at h; exact nomatch h
    | ok b' =>
    rw [hwcb] at h
    dsimp only at h
    obtain ⟨va', hva', hDa, hwa', hba', hLa', hCa'⟩ :=
      whnfCore_packageR m φ ihwc hwca hwa hba hLa hCa hva
    obtain ⟨vb', hvb', hDb, hwb', hbb', hLb', hCb'⟩ :=
      whnfCore_packageR m φ ihwc hwcb hwb hbb hLb hCb hvb
    -- from here every verdict is `DefEq Δ va' vb'`, chained through D4
    suffices hmid : DefEq mode env m.cval φ Δ va' vb' from
      ((DefEq.ofRed hDa).trans hmid).trans (DefEq.ofRed hDb).symm
    split at h
    · next hab' =>
      obtain rfl : a' = b' := eq_of_beq hab'
      obtain rfl : va' = vb' := by rw [hva'] at hvb'; exact Option.some.inj hvb'
      exact DefEq.refl
    · cases hir : proofIrrelP mode env fuel d a' b' with
      | error err => rw [hir] at h; exact nomatch h
      | ok r =>
      rw [hir] at h
      dsimp only at h
      cases r with
      | true =>
        exact hpi hir hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
      | false =>
        cases hna : (if !a'.hasFvar && !b'.hasFvar then
            reduceNatP mode env fuel d a' else pure none) with
        | error err => rw [hna] at h; exact nomatch h
        | ok o₁ =>
        rw [hna] at h
        dsimp only at h
        match o₁, hna, h with
        | some a₂, hna, h =>
          have hred : reduceNatP mode env fuel d a' = .ok (some a₂) := by
            split at hna
            · exact hna
            · exact nomatch hna
          obtain ⟨w, hw, hDw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwa' hba' hLa' hCa' hva'
          exact (DefEq.ofRed hDw).trans
            (hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hw hvb')
        | none, hna, h =>
        dsimp only at h
        cases hnb : (if !a'.hasFvar && !b'.hasFvar then
            reduceNatP mode env fuel d b' else pure none) with
        | error err => rw [hnb] at h; exact nomatch h
        | ok o₂ =>
        rw [hnb] at h
        dsimp only at h
        match o₂, hnb, h with
        | some b₂, hnb, h =>
          have hred : reduceNatP mode env fuel d b' = .ok (some b₂) := by
            split at hnb
            · exact hnb
            · exact nomatch hnb
          obtain ⟨w, hw, hDw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwb' hbb' hLb' hCb' hvb'
          exact (hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hva' hw).trans
            (DefEq.ofRed hDw).symm
        | none, hnb, h =>
        cases hha : unfoldableHead env a' <;>
          cases hhb : unfoldableHead env b' <;>
          rw [hha, hhb] at h <;> dsimp only at h
        · -- neither head unfolds: the stuck configuration
          exact hstk h0 (by simpa using ‹¬(a == b) = true›) hwca hwcb
            (by simpa using ‹¬(a' == b') = true›) hir hna hnb hha hhb
            hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
        · cases hub : unfoldDefinition env b' with
          | none => rw [hub] at h; exact nomatch h
          | some b₂ =>
            rw [hub] at h
            obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_packageR m φ hcl hub hwb' hbb' hLb' hCb' hvb'
            exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hva' hd2
        · cases hua : unfoldDefinition env a' with
          | none => rw [hua] at h; exact nomatch h
          | some a₂ =>
            rw [hua] at h
            obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
              delta_packageR m φ hcl hua hwa' hba' hLa' hCa' hva'
            exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2 hvb'
        · have hboth : ∀ {x : CheckM Bool},
              (match unfoldDefinition env a', unfoldDefinition env b' with
                | some a₂, some b₂ => k a₂ b₂
                | _, _ => pure false) = .ok true →
              DefEq mode env m.cval φ Δ va' vb' := by
            intro x hbb2
            cases hua : unfoldDefinition env a' with
            | none => rw [hua] at hbb2; exact nomatch hbb2
            | some a₂ =>
            cases hub : unfoldDefinition env b' with
            | none => rw [hua, hub] at hbb2; exact nomatch hbb2
            | some b₂ =>
              rw [hua, hub] at hbb2
              obtain ⟨hdA, hwA, hbA, hLA, hCA⟩ :=
                delta_packageR m φ hcl hua hwa' hba' hLa' hCa' hva'
              obtain ⟨hdB, hwB, hbB, hLB, hCB⟩ :=
                delta_packageR m φ hcl hub hwb' hbb' hLb' hCb' hvb'
              exact hk hbb2 hwA hbA hLA hwB hbB hLB hCA hCB hdA hdB
          cases hlt1 : ReducibilityHint.lt (headHint env b')
              (headHint env a') <;> rw [hlt1] at h
          · cases hlt2 : ReducibilityHint.lt (headHint env a')
                (headHint env b') <;> rw [hlt2] at h
            · cases hsr : (ReducibilityHint.sameRegular (headHint env a')
                  (headHint env b') && sameConstHeads a' b') <;>
                rw [hsr] at h
              · exact hboth (x := pure false) h
              · cases hsp : defeqSpineP mode env fuel d a' b' with
                | error err => rw [hsp] at h; exact nomatch h
                | ok r' =>
                rw [hsp] at h
                dsimp only at h
                cases r' with
                | true =>
                  exact hspine hsp hwa' hba' hLa' hwb' hbb' hLb'
                    hCa' hCb' hva' hvb'
                | false => exact hboth (x := pure false) h
            · cases hub : unfoldDefinition env b' with
              | none => rw [hub] at h; exact nomatch h
              | some b₂ =>
                rw [hub] at h
                obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
                  delta_packageR m φ hcl hub hwb' hbb' hLb' hCb' hvb'
                exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hva' hd2
          · cases hua : unfoldDefinition env a' with
            | none => rw [hua] at h; exact nomatch h
            | some a₂ =>
              rw [hua] at h
              obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
                delta_packageR m φ hcl hua hwa' hba' hLa' hCa' hva'
              exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2 hvb'

/-- **`DefEqClaimsR` at `fuel + 1`**, with the step discharged: three
obligations remain, all at checker functions or a checker
configuration. -/
theorem defeq_claimsR_closed {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsR mode m φ fuel)
    (hnat : ReduceNatStepR (mode := mode) m φ fuel)
    (hpi : ProofIrrelStepR (mode := mode) m φ fuel)
    (hstk : DefEqStuckStepR (mode := mode) m φ fuel)
    (hspine : DefEqSpineStepR (mode := mode) m φ fuel) :
    DefEqClaimsR mode m φ (fuel + 1) :=
  defeq_claimsR m φ (defeqStep_claimR m φ hcl ihwc hnat hpi hstk hspine)

end Setlec.SetR
