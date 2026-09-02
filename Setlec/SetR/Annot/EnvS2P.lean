import Setlec.SetR.Interp2.Step2.AssemblyP
import Setlec.SetR.Interp2.EnvS2U

/-!
# `EnvS2PM` — the P-tier environment invariant (task #161, P4)

The install tier's target, per the P4 design note in DESIGN.md: the
denote2-free environment carrier (`EnvS2Core`) *contained*, plus the
fields the P bundles read.  (Batch 8 slimmed the containment from
`EnvS2UM` to `EnvS2Core` — the FINDING in `Annot/EnvS2Core.lean`: the
P fold stores `denoteP`-numeraled leaves and so can never supply the
denote2-currency fields, which the P surface never reads.)  The deltas
against the canonical fields, each a payoff of the fuel-free reading:

* **existence, not uniqueness** — `defn_reads` is `AcvalDefnInstP`
  (batch 4): a stored definition's or theorem's value *reads*, to the
  constant's own leaf.  The canonical `acval_defn` retreated to a
  uniqueness form because all-fuel existence is refutable
  (`envS2_defn_lam_refuted` — `denote2` fails on binders at small
  fuel); `denoteP` has no fuel, and a checked value is never out of
  fragment.
* **the stored types read, are graded, and are inhabited** —
  `type_reads`/`type_okP`/`mem_typeP`, at the *uninstantiated* type
  over every ground assignment; `denotePInstLevels` (an equality)
  delivers every instantiated form, so no arity or fuel bookkeeping
  appears anywhere.
* **the leaves are bit-valid** — `acval_validV`, `acval_ok2`'s
  `AnnotValidV` companion; establishment at install is the P2 front
  door's own validation, transported by the claims.

The bundle-supplying layer below (`constTypeP_of` the worked example;
its siblings follow the same three-field read) is what the quarter
induction (`checkSoundP_of_inputs`) consumes — the structure exists so
that a `Nonempty (EnvS2PM …)` carried through the declaration fold
makes the induction's hypotheses *facts*.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps projFnName RecRule)

universe w

variable (V : Type w) [SetTheory V]

/-- **The structural-`Nat` recurrence law at the validated-annotation
tier** (task #161, the wall's supplier): every stored structural
operation's defining equations read under `denoteP` and hold as
`interp2` equalities at the two-variable `Nat` context — `NatOpsV`
(`Sound/Motives.lean`) with `denote`/`interp`/`cval` replaced by
`denoteP`/`interp2`/`acval`, and the level composition normalized to
the plain assignment (the heads are level-monomorphic).

Supplied as an `EnvS2PM` field: established at the operation's own
install from the recorded `isDefEqCore` runs (`NatEqsRunR`) through
`DefEqClaims2P` — the run-certificate route (`Interp2/NatEqsP.lean`)
— and preserved across every other fresh cons.  Consumed by the
numeral-transport inductions (`Sound/NatOps`' shape at `interp2`),
which close `ReduceNatStepP`/`PQ` below. -/
def NatOpsP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ : Name → Nat) : Prop :=
  ∀ c ∈ Setlec.natOpNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    Setlec.natOpGuard env c = true ∧
    ∀ eq ∈ Setlec.natOpEquations 0 c, ∃ L R,
      denoteP m.acval env φ 2 eq.1 = some L ∧
      denoteP m.acval env φ 2 eq.2 = some R ∧
      ∀ (ρ : Nat → V) (x y : V),
        x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
        y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
        interp2 V (cons y (cons x ρ)) L
          = interp2 V (cons y (cons x ρ)) R

/-- **The pin-certified WF-recursive operations' guarded value
recurrences at the validated-annotation tier** — `DivModV`
(`Sound/Motives.lean`) with `interp`/`cval` replaced by
`interp2`/`acval`.  `DivModClausesV` is already valuation-generic, so
it is reused verbatim: only the valuation it is fed changes.

Supplied as an `EnvS2PM` field: established at the operation's own
install from the recorded certificate runs (`DivModPinR`'s
`checkDivModCerts` verdict) through `InferClaims2P`/`DefEqClaims2P` —
the run-certificate route again (`Interp2/DivModP.lean`) — and
preserved across every other fresh cons.  Consumed by the WF-op
numeral transports (`Sound/NatOpsWf`' shape at `interp2`). -/
def DivModP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ : Name → Nat) : Prop :=
  ∀ c ∈ Setlec.natDivModNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    Setlec.natOpGuard env c = true ∧
    ∀ (ρ : Nat → V) (x y : V),
      x ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      y ∈ˢ interp2 V ρ (m.acval Setlec.natName φ) →
      DivModClausesV V (fun n => interp2 V ρ (m.acval n φ)) c x y

/-- **The pinned `Eq` spine's value at `interp2`** — `EnvS.eq_lawV`'s
mirror one currency over, stated directly at the three-fold
application (the only form the certificate consumers read; v1 states
the two-fold `lamC` form because its η/unit consumers need the
rigidity clause, which nothing here does).

**This is an environment law, exactly as in v1**: `EqLawV` is an
`EnvS` *field*, not a theorem, because the `Eq` leaf's value is fixed
by the basis install (`Install/BasisS.lean`'s `eqValT` — the `.eqE`
former η-expanded) and by nothing else.  The P mirror is a field for
the same reason, and its supplier is the P basis install
(`BasisStepPB`, routed): the annotated `Eq` tower's *regime bits* are
invisible to every other `EnvS2PM` field, and the erasure factoring
that would import the v1 law is refuted at exactly the λ-nodes this
tower is made of (the literal-tier seal II finding 1).  See the task
#161 LITERAL TIER seal III record. -/
def EqLawP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) : Prop :=
  env.find? eqName = some eqA →
  ∀ ψ : Name → Nat,
    -- the spine's **value**: the truth set of the equation
    (∀ (ρ : Nat → V) (A a b : V),
      A ∈ˢ (univ (ψ uN) : V) → a ∈ˢ A → b ∈ˢ A →
      SetTheory.app (SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval eqName ψ)) A) a) b = eqv a b) ∧
    -- the spine's **grading**, and that it is a proposition.  (v1
    -- needs neither: `AnnotOkV` has no bit content and `CtxOkR` asks
    -- for no grading.  Both are stated here for the same reason v1
    -- restated `EqLawV` at the two-fold application — an interface
    -- field is stated at the shape its consumers read, and the
    -- certificate frame reads exactly these.)
    ∀ (ρ : Nat → V) (Aa la ra : AVExpr),
      AnnotOkP V ρ Aa → AnnotOkP V ρ la → AnnotOkP V ρ ra →
      interp2 V ρ Aa ∈ˢ (univ (ψ uN) : V) →
      interp2 V ρ la ∈ˢ interp2 V ρ Aa →
      interp2 V ρ ra ∈ˢ interp2 V ρ Aa →
      AnnotOkP V ρ
          (.app (.app (.app (m.acval eqName ψ) Aa) la) ra) ∧
        interp2 V ρ (.app (.app (.app (m.acval eqName ψ) Aa) la) ra)
          ∈ˢ (univZero : V)

/-! ## The structure-capability laws (task #161, caps tier)

`CapsOkV`'s mirror at the validated-annotation currency: the stored
families' fired η and unit-like laws, value-level, keyed exactly as
the v1 field (`Sound/Motives.lean:309`) on the stored `indInfo`, the
capability flag, the non-reserved name, and the completed family
(`EtaFamilyStored`).

Design decisions, recorded (the lane lead's freeze; the statements
below are unchanged from `Interp2/CapsP.lean`'s first landing, which
is now the *preservation* file — the definitions moved here because
the `EnvS2PM` field must import them and `CapsP` imports `EnvS2P`):

* **The telescope fit is `TeleFitP`, not `TeleFit2`.**  `TeleFit2`
  (`Annot/Spine2.lean`) demands every product in the graph regime
  (`v ≠ 0`), which a `Prop`-valued family's telescope violates.
  `TeleFitP` mirrors `TeleFitV` instead — memberships only, the
  peeled body read under the extended environment (the `interp2`
  analogue of `B.inst a`), no positivity anywhere.  Consumers recover
  residual memberships through `app_mem_piR`, whose `v = 0` fibre
  premise is the type reading's `AnnotValidV` — the literal tier's
  establishment move, reused (`NatEqsP.lean`'s finding: no bit
  positivity is ever needed).
* **The laws carry their readings** (`∃ TVa, …`), the `NatOpsP`
  pattern: establishment stores the instantiated type's reading at
  its own environment; preservation transfers it *forward*
  (`denoteP_cons_fresh_mono`); consumers identify it with their own
  reading by determinism.  The equality-form crossing is refutable
  at support-completing installs (the `LitStabilityP` lesson), so no
  backward transfer ever appears.
* **The fired content is value-level** (the divmod-leg lesson): `ts`,
  `x`, `y` are bare `V`s, and the fabricated η spine is
  `projSpines2`/`etaFabArgs2` — `projSpinesV`/`etaFabArgsV`
  (`Rel.lean:98/106`) with `cval`-leaves replaced by `interp2` values
  of the `acval` leaves at the same assignment.

**Establishment**: at the inductive install — `IndStepPB`'s bill (the
routed bundle already owes the whole `EnvS2PM` at an `indDecl` cons;
this adds no census entry).  The v1 establishment path is the
capability pipeline (kernel pin → `EtaPins` → rule_fold → `ModeledOk`
law → cert+sound, `Install/EtaLawS.lean`); the P path re-runs its
defeq certificates through the claims — the run-certificate route —
when the ind tier lands.  Consumers: `StructEtaIrrelP` /
`StructUnitIrrelP` (`Step2/CapsRowsP.lean`), discharged from the
field by the caps batch. -/

/-- **The annotated telescope fit** (`TeleFitV`'s `interp2` mirror):
each argument value inhabits its progressively-peeled domain, the
peeled body read under the extended environment.  No positivity — the
squash-regime products fit too, and consumers recover memberships
through `app_mem_piR` with the validity fibre facts. -/
inductive TeleFitP (V : Type w) [SetTheory V] :
    (Nat → V) → AVExpr → List V → V → Prop where
  | nil {ρ : Nat → V} {T : AVExpr} : TeleFitP V ρ T [] (interp2 V ρ T)
  | cons {ρ : Nat → V} {u v : Nat} {A B : AVExpr} {a : V}
      {as : List V} {rest : V} :
      a ∈ˢ interp2 V ρ A →
      TeleFitP V (cons a ρ) B as rest →
      TeleFitP V ρ (.pi u v A B) (a :: as) rest

/-- The projection spines' values: each stored projection function
applied to the type arguments and the stuck member
(`projSpinesV`'s value level). -/
noncomputable def projSpines2 {V : Type w} [SetTheory V]
    (val : Name → V) (T : Name) (ts : List V) (b : V) (nF : Nat) :
    List V :=
  (List.range nF).map fun j =>
    (ts ++ [b]).foldl SetTheory.app (val (projFnName T j))

/-- The fabricated η spine's values (`etaFabArgsV`'s value level). -/
noncomputable def etaFabArgs2 {V : Type w} [SetTheory V]
    (val : Name → V) (T : Name) (ts : List V) (b : V) (nF : Nat) :
    List V :=
  ts ++ projSpines2 val T ts b nF

/-- **The fired structural-η law of an η-capable stored family**
(`EtaLawV`'s mirror; see the note above for the shape). -/
def EtaLawP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ' : Name → Nat) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ us : List Level, us.length = cvT.levelParams.length →
  ∃ TVa : AVExpr,
    denoteP m.acval env φ' 0
      (cvT.type.instantiateLevelParams cvT.levelParams us)
      = some TVa ∧
    (∀ ρ : Nat → V, AnnotOkP V ρ TVa) ∧
    ∀ (ρ : Nat → V) (ts : List V) (rest : V) (x : V),
      ts.length = caps.etaParams →
      TeleFitP V ρ TVa ts rest →
      x ∈ˢ ts.foldl SetTheory.app
        (interp2 V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      x = (etaFabArgs2
            (fun n => interp2 V ρ
              (m.acval n (Level.substFn φ' cvT.levelParams us)))
            T ts x caps.etaFields).foldl SetTheory.app
          (interp2 V ρ
            (m.acval caps.etaCtor
              (Level.substFn φ' cvT.levelParams us)))

/-- **The fired unit-like law of a unit-like stored family**
(`UnitLawV`'s mirror). -/
def UnitLawP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ' : Name → Nat) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ us : List Level, us.length = cvT.levelParams.length →
  ∃ TVa : AVExpr,
    denoteP m.acval env φ' 0
      (cvT.type.instantiateLevelParams cvT.levelParams us)
      = some TVa ∧
    (∀ ρ : Nat → V, AnnotOkP V ρ TVa) ∧
    ∀ (ρ : Nat → V) (ts : List V) (rest : V) (x y : V),
      ts.length = caps.unitParams →
      TeleFitP V ρ TVa ts rest →
      x ∈ˢ ts.foldl SetTheory.app
        (interp2 V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      y ∈ˢ ts.foldl SetTheory.app
        (interp2 V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      x = y

/-- **The stored families' capability laws at `interp2`**
(`CapsOkV`'s mirror, keyed identically; established at the inductive
install — `IndStepPB`'s bill). -/
def CapsOkP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) : Prop :=
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    Setlec.reservedBasisNames.contains T = false →
    Setlec.EtaFamilyStored env T caps →
    ∀ φ' : Name → Nat, EtaLawP m φ' T cvT caps) ∧
  -- The unit half carries NO `EtaFamilyStored` premise — exactly as
  -- v1's `CapsOkV` unit half (`Sound/Motives.lean:315`).  The freeze
  -- transcribed the eta half's premise here by mistake; the caps
  -- batch mechanized the refutation (`etaFamilyStored_not_derivable`:
  -- a WF environment with a non-reserved unitlike-only family where
  -- the premise is false and the law vacuous), and the deletion was
  -- ratified — it strengthens the field, consumers and the
  -- `IndStepPB` establishment unchanged.
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.unitlike = true →
    Setlec.reservedBasisNames.contains T = false →
    ∀ φ' : Name → Nat, UnitLawP m φ' T cvT caps)

/-! ## The fired modeled-iota contract (task #161, iota tier)

`RecRuleLawV`/`RecRulesV`'s mirror (`Sound/Motives.lean:145/207`) at
the validated-annotation currency.  This is the campaign's long pole;
the statement-freeze discipline is at its strictest here, and every
deviation from the v1 shape is a recorded decision:

* **The law stays `AVExpr`-indexed**, exactly as `RecRuleLawV` is
  `VExpr`-indexed.  The caps/divmod value-level lesson does NOT
  transfer: the truthfulness transport is inherently about the
  applied reduct's *reading* (the producing `IotaStepP` row must hand
  the whnf loop a graded reading), and `AnnotOkP` is `AVExpr`-indexed.
  An earlier value-level draft of this block died on exactly that
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

The statements are FROZEN (task #161, after the consumer validation
pass); they landed in `Interp2/IotaLawP.lean` and moved here verbatim
when `RecRulesP` became an `EnvS2PM` field, exactly as the caps
statements did — the field must mention them and `IotaLawP` imported
this file.

**Establishment**: the inductive install — `IndStepPB`'s bill, where
the flagged new mathematics lives (a `Prop`-valued motive's minors at
the squash regime).  **Consumers**: `IotaStepP`/`IotaReadsP`
(`Step2/WhnfP.lean:182`, `Step2/ReadsP.lean:173`), discharged by the
iota tier (`Step2/IotaRowsP.lean`). -/

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
def IotaIndexPinP {V : Type w} [SetTheory V] (ρ : Nat → V)
    (restC : AVExpr) (cnP mI rP : Nat) (xs : List AVExpr) : Prop :=
  ∃ (Ha : AVExpr) (cargsa : List AVExpr),
    restC = AVExpr.mkAppN Ha cargsa ∧
    (mI = rP ∨ cargsa.length = cnP + (mI - rP)) ∧
    ∀ i, i < mI - rP →
      interp2 V ρ (cargsa.getD (cnP + i) default)
        = interp2 V ρ (xs.getD (rP + i) default)

/-- **One rule's fired modeled-iota contract at `interp2`**
(`RecRuleLawP`; `RecRuleLawV`'s mirror — see the note above for
every deviation). -/
def RecRuleLawP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ : Name → Nat)
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
def RecRulesP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ : Name → Nat) : Prop :=
  ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
    (rules : List RecRule),
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      RecRuleLawP m φ n cv mI rP rl

/-- **The P-tier environment invariant, at one mode** (see the module
docstring). -/
structure EnvS2PM (μ : CheckMode) (env : Env) where
  /-- the denote2-free environment carrier, contained (batch 8: the
  P fold stores `denoteP`-numeraled leaves, so it can never supply the
  denote2-currency fields `EnvS2UM` carries — and the P surface reads
  none of them) -/
  base2 : EnvS2Core V env
  /-- every leaf is bit-valid (`acval_ok2`'s `AnnotValidV` half) -/
  acval_validV : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotValidV V ρ (base2.acval n ψ)
  /-- every stored type reads, at every ground assignment -/
  type_reads : ∀ c ∈ env.consts, ∀ ψ : Name → Nat,
    ∃ ta : AVExpr,
      denoteP base2.acval env ψ 0 c.toConstantVal.type = some ta
  /-- the stored types' readings are graded -/
  type_okP : ∀ c ∈ env.consts, ∀ (ψ : Name → Nat) (ta : AVExpr),
    denoteP base2.acval env ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, AnnotOkP V ρ ta
  /-- stored constants inhabit their types' readings -/
  mem_typeP : ∀ c ∈ env.consts, ∀ (ψ : Name → Nat) (ta : AVExpr),
    denoteP base2.acval env ψ 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V,
      interp2 V ρ (base2.acval c.name ψ) ∈ˢ interp2 V ρ ta
  /-- stored definition and theorem values read, to the constant's own
  leaf (existence — the fuel-free upgrade of `acval_defn`) -/
  defn_reads : AcvalDefnInstP base2
  /-- the two `Nat`-literal head facts, at every assignment -/
  nat_heads : ∀ φ : Name → Nat, NatHeadsP base2 φ
  /-- the structural-`Nat` recurrence laws at every assignment (the
  literal tier's supplier; established at the operations' own installs
  from the recorded runs — `Interp2/NatEqsP.lean`) -/
  nat_ops : ∀ φ : Name → Nat, NatOpsP base2 φ
  /-- the pin-certified WF operations' guarded clauses at every
  assignment (the literal tier's other supplier; established at the
  operations' own installs from the recorded certificate runs —
  `Interp2/DivModCertP.lean`) -/
  div_mod : ∀ φ : Name → Nat, DivModP base2 φ
  /-- the pinned `Eq` spine's value and grading (an *environment law*,
  as `EnvS.eq_lawV` is: the `Eq` leaf is fixed by the basis install and
  by nothing else, so the supplier is the P basis install —
  `BasisStepPB`, routed.  Consumed by the WF operations' certificate
  frame) -/
  eq_lawP : EqLawP base2
  /-- the stored families' fired capability laws (`CapsOkV`'s mirror;
  an *environment law* for the same reason `eq_lawP` is — an
  η-capable family's leaf value is fixed by the inductive install and
  by nothing else, so the supplier is `IndStepPB`).  Consumed by the
  `stuckIrrel` cascade's two stored-family arms
  (`Step2/CapsRowsP.lean`) -/
  caps_ok : CapsOkP base2
  /-- the stored recursors' fired modeled-iota contracts (`RecRulesV`'s
  mirror; an *environment law* for the same reason `caps_ok` is — a
  recursor's rules are fixed by the inductive install and by nothing
  else, so the supplier is `IndStepPB`).  Consumed by the ι row
  (`Step2/IotaRowsP.lean`) -/
  rec_rules : ∀ φ : Name → Nat, RecRulesP base2 φ

namespace EnvS2PM

variable {V}
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- The leaf bit-validity residue, read off the field. -/
theorem acvalValidP (m : EnvS2PM V μ env) : AcvalValidP m.base2 :=
  m.acval_validV

/-- **The `const` residue, derived — the worked example of the
bundle-supplying layer.**  The three type fields at the composed
assignment `Level.substFn φ ks us`, carried to the instantiated form
by `denotePInstLevels` (an equality: no arity premise, no fuel). -/
theorem constTypeP (m : EnvS2PM V μ env) : ConstTypeP m.base2 φ := by
  intro d n ci us hf hlen
  have hmem := Setlec.SetR.Env.find?_mem hf
  have hname := Setlec.SetR.Env.find?_name hf
  obtain ⟨ta, hta⟩ :=
    m.type_reads ci hmem (Level.substFn φ ci.toConstantVal.levelParams us)
  have hwf := m.base2.base.wf ci hmem
  -- the reading is closed, hence depth-free
  have hcl : ∀ k : Nat, ta.liftN 1 k = ta := fun k =>
    denoteP_closed m.base2.acval_erase m.base2.base.cval_closed
      hwf.1 hwf.2.2.2.1 hta 1 k
  have hdepth :
      denoteP m.base2.acval env
          (Level.substFn φ ci.toConstantVal.levelParams us) d
          ci.toConstantVal.type = some ta :=
    denoteP_depth_of_closed m.base2.acval_closed hwf.1 hcl hta d
  -- the instantiated type's reading, by the crossing
  have hcross :
      denoteP m.base2.acval env φ d
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us)
        = denoteP m.base2.acval env
            (Level.substFn φ ci.toConstantVal.levelParams us) d
            ci.toConstantVal.type :=
    denotePInstLevels m.base2 φ ci.toConstantVal.levelParams us d
      ci.toConstantVal.type
  refine ⟨ta, ?_, m.type_okP ci hmem _ ta hta, ?_⟩
  · rw [hcross]; exact hdepth
  · have := m.mem_typeP ci hmem _ ta hta
    rwa [hname] at this

end EnvS2PM

/-- The empty environment carries the P invariant (the fold's base
case): the core is the mode-indexed empty's projection, and every P
field is vacuous — no constants, guards false, and the empty leaf
`.const .empty [0]` is bit-valid because a constant leaf carries no
binder. -/
noncomputable def EnvS2PM.empty (V : Type w) [SetTheory V]
    (μ : CheckMode) : EnvS2PM V μ Env.empty where
  base2 := (EnvS2UM.empty (V := V) μ).toCore
  acval_validV := fun _ _ _ => by
    show AnnotValidV V _ (.const .empty [0])
    simp
  type_reads := fun c hc => nomatch hc
  type_okP := fun c hc => nomatch hc
  mem_typeP := fun c hc => nomatch hc
  defn_reads := fun ψ cv value hmem => by
    rcases hmem with ⟨hint, hdt⟩ | hdt
    · exact nomatch hdt
    · exact nomatch hdt
  nat_heads := fun φ hg => by
    rw [show Setlec.natLitSupported Env.empty = false from rfl] at hg
    exact nomatch hg
  nat_ops := fun φ c _ cv v hint hf => by
    rw [show Env.empty.find? c = none from rfl] at hf
    exact nomatch hf
  div_mod := fun φ c _ cv v hint hf => by
    rw [show Env.empty.find? c = none from rfl] at hf
    exact nomatch hf
  eq_lawP := fun hf => by
    rw [show Env.empty.find? eqName = none from rfl] at hf
    exact nomatch hf
  caps_ok := by
    refine ⟨fun T cvT caps hf => ?_, fun T cvT caps hf => ?_⟩ <;>
      · rw [show Env.empty.find? T = none from rfl] at hf
        exact nomatch hf
  rec_rules := fun _ n _ _ _ _ hf => by
    rw [show Env.empty.find? n = none from rfl] at hf
    exact nomatch hf

end Setlec.SetR.Interp2
