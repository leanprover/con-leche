import Setlec.SetR.Annot.EnvS2P

/-!
# The fired modeled-iota contract at `interp2` — statements (task
#161, iota tier; FROZEN by the lane lead after the consumer
validation pass)

`RecRuleLawV`/`RecRulesV`'s mirror (`Sound/Motives.lean:145/207`) at
the validated-annotation currency.  This is the campaign's long pole;
the statement-freeze discipline is at its strictest here, and every
deviation from the v1 shape is a recorded decision:

* **The law stays `AVExpr`-indexed**, exactly as `RecRuleLawV` is
  `VExpr`-indexed.  The caps/divmod value-level lesson does NOT
  transfer: the truthfulness transport is inherently about the
  applied reduct's *reading* (the producing `IotaStepP` row must hand
  the whnf loop a graded reading), and `AnnotOkP` is `AVExpr`-indexed.
  An earlier value-level draft of this file died on exactly that
  conjunct.
* **`TeleFitPA` is `TeleFitV`'s transpose, substitution-peeling** —
  `B.inst a` at the argument's *reading*, one ambient environment,
  exactly v1's shape one currency over.  The consumer-validation pass
  killed the earlier cons-environment draft: its residual diverged
  syntactically from the substituted readings the certificate's
  `defEqList` runs compare, re-opening the seal-22 gap the fit was
  meant to close.  Substitution-peeling is available here because the
  arguments are readings (the caps tier's `TeleFitP` had bare values
  and could not substitute — hence its `teleFitP_of_inst` detour,
  which this fit never needs): `denoteP_beta` gives the residual
  identity (`Tele.residual`'s mirror) directly, and the index pin
  decomposes the residual at the ambient environment, v1-verbatim.
* **The `.nested` pin clause quantifies the pin's own open reading**
  (`denoteP` at depth `rP`), concluding at the reading substituted
  along the argument prefix — `AVExpr.instRevChain`, the exact v1
  spelling one currency over.  The consumer's bridge is then the
  `denoteP` mirror of the existing `denote_openRev`/
  `denote_openRev_base` pair (`Verify/Denote/OpenRevDenote.lean`);
  the supplier converts the recorded comparand runs through the
  claims.
* **The fired equality is present** (the seal-22 draft omitted it),
  and the transport clause is `RecRuleLawV`'s final conjunct verbatim
  at the new currency.
* The law **carries the RHS reading** (`∃ Ra`), with the bare-`R`
  grading unconditional (the seal-22 correction; the
  `NatOpsP`/caps carried-reading pattern — establishment stores,
  preservation transfers forward, consumers identify by determinism).

**Establishment**: the inductive install — `IndStepPB`'s bill, where
the flagged new mathematics lives (a `Prop`-valued motive's minors at
the squash regime; the working conjecture is that both fired sides
collapse to `pt` through the truth-set memberships the rule's typing
supplies — to be proved or walled there).  **Consumers**:
`IotaStepP`/`IotaReadsP` (`Step2/WhnfP.lean:182`,
`Step2/ReadsP.lean:173`), discharged by the iota batch after the
lead's worked example validates this draft.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-- **The annotated telescope fit** (`TeleFitV`'s transpose,
substitution-peeling): each argument reading inhabits its
progressively-substituted domain, one ambient environment, the
residual an `AVExpr` at that environment. -/
inductive TeleFitPA (V : Type w) [SetTheory V] (ρ : Nat → V) :
    AVExpr → List AVExpr → AVExpr → Prop where
  | nil {T : AVExpr} : TeleFitPA V ρ T [] T
  | cons {u v : Nat} {A B rest : AVExpr} {a : AVExpr}
      {as : List AVExpr} :
      interp2 V ρ a ∈ˢ interp2 V ρ A →
      TeleFitPA V ρ (B.inst a) as rest →
      TeleFitPA V ρ (.pi u v A B) (a :: as) rest

/-- The annotated reverse-opening substitution chain
(`VExpr.instRevChain`'s `AVExpr` twin, `Verify/Denote/OpenVars.lean:80`
— outermost argument consumed first, each at cut `0`, lifted past the
arguments still to come). -/
def _root_.Setlec.SetR.AVExpr.instRevChain :
    List AVExpr → AVExpr → AVExpr
  | [], X => X
  | v :: vs, X =>
    Setlec.SetR.AVExpr.instRevChain vs (X.inst (v.liftN vs.length) 0)

/-- **The constructor residual's index pin** (`IotaIndexPinV`'s
mirror, v1-verbatim at `AVExpr`): the residual decomposes as a spine
whose trailing arguments agree with the recursor's index arguments,
all at the ambient environment. -/
def IotaIndexPinP (ρ : Nat → V) (restC : AVExpr)
    (cnP mI rP : Nat) (xs : List AVExpr) : Prop :=
  ∃ (Ha : AVExpr) (cargsa : List AVExpr),
    restC = AVExpr.mkAppN Ha cargsa ∧
    (mI = rP ∨ cargsa.length = cnP + (mI - rP)) ∧
    ∀ i, i < mI - rP →
      interp2 V ρ (cargsa.getD (cnP + i) default)
        = interp2 V ρ (xs.getD (rP + i) default)

/-- **One rule's fired modeled-iota contract at `interp2`**
(`RecRuleLawP`; `RecRuleLawV`'s mirror — see the module docstring for
every deviation). -/
def RecRuleLawP {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (n : Name) (cv : ConstantVal) (mI rP : Nat) (rl : RecRule) :
    Prop :=
  rP ≤ mI ∧
  ∀ us : List Level, us.length = cv.levelParams.length →
    ∃ Ra : AVExpr,
      denoteP m.acval env φ 0
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
        = some Ra ∧
      (∀ ρ : Nat → V, AnnotOkP V ρ Ra) ∧
      ∀ (cvj : ConstantVal) (cnP cnF : Nat),
        env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AVExpr)
        (TVa TVja restR restC : AVExpr),
        xs.length = mI →
        ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
        usj.length = cvj.levelParams.length →
        Level.substFn φ cvj.levelParams usj
          = Level.substFn φ cvj.levelParams
              (Setlec.recFireComparands rl cv.levelParams us
                cvj.levelParams [] rP).1 →
        (RecRule.fire rl = .plain →
          ∀ i, i < RecRule.ctorParams rl → i < mI →
            interp2 V ρ (ys.getD i default)
              = interp2 V ρ (xs.getD i default)) →
        (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
          ∀ i, i < RecRule.ctorParams rl →
          ∀ vpa : AVExpr,
            denoteP m.acval env φ rP
              (Setlec.TTVerify.openRev 0 rP
                ((pins.getD i default).instantiateLevelParams
                  cv.levelParams us)) = some vpa →
            interp2 V ρ (ys.getD i default)
              = interp2 V ρ
                  (Setlec.SetR.AVExpr.instRevChain (xs.take rP)
                    vpa)) →
        IotaIndexPinP (V := V) ρ restC (RecRule.ctorParams rl)
          mI rP xs →
        denoteP m.acval env φ 0
          (cv.type.instantiateLevelParams cv.levelParams us)
          = some TVa →
        denoteP m.acval env φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj)
          = some TVja →
        TeleFitPA V ρ TVa
          (xs ++ [AVExpr.mkAppN
            (m.acval (RecRule.ctor rl)
              (Level.substFn φ cvj.levelParams usj)) ys]) restR →
        TeleFitPA V ρ TVja ys restC →
        interp2 V ρ
            (AVExpr.mkAppN
              (m.acval n (Level.substFn φ cv.levelParams us))
              (xs ++ [AVExpr.mkAppN
                (m.acval (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]))
          = interp2 V ρ
              (AVExpr.mkAppN Ra
                (xs.take rP ++ ys.drop (RecRule.ctorParams rl))) ∧
        ((∀ a ∈ xs, AnnotOkP V ρ a) → (∀ b ∈ ys, AnnotOkP V ρ b) →
          AnnotOkP V ρ
            (AVExpr.mkAppN Ra
              (xs.take rP ++ ys.drop (RecRule.ctorParams rl))))

/-- The fired modeled-iota contract, keyed on every stored recursor
(`RecRulesV`'s mirror). -/
def RecRulesP {env : Env} (m : EnvS2Core V env) (φ : Name → Nat) :
    Prop :=
  ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
    (rules : List RecRule),
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      RecRuleLawP m φ n cv mI rP rl

end Setlec.SetR.Interp2
