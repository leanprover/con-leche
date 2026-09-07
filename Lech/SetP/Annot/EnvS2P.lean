import Lech.SetP.Step2.DefEqP
import Lech.SetP.Step2.InferIOP
import Lech.SetP.Step2.InferP
import Lech.SetP.Step2.WhnfP
import Lech.Semantics.EnvFacts
import Lech.Semantics.DivModEval
import Lech.Verify.Denote
import Lech.Verify.Denote.OpenVars
import Lech.Verify.Denote.VClosed
import Lech.Verify.ProjTele

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

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.Verify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name Level ConstantInfo ConstantVal
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
install from the recorded `isDefEqCore` runs (`NatEqsRun`) through
`DefEqClaims2P` — the run-certificate route (`Interp2/NatEqsP.lean`)
— and preserved across every other fresh cons.  Consumed by the
numeral-transport inductions (`Sound/NatOps`' shape at `interp2`),
which close `ReduceNatStepP`/`PQ` below. -/
def NatOpsP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ : Name → Nat) : Prop :=
  ∀ c ∈ Lech.natOpNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    Lech.natOpGuard env c = true ∧
    ∀ eq ∈ Lech.natOpEquations 0 c, ∃ L R,
      denoteP m.acval env φ 2 eq.1 = some L ∧
      denoteP m.acval env φ 2 eq.2 = some R ∧
      ∀ (ρ : Nat → V) (x y : V),
        x ∈ˢ interp2 V ρ (m.acval Lech.natName φ) →
        y ∈ˢ interp2 V ρ (m.acval Lech.natName φ) →
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
  ∀ c ∈ Lech.natDivModNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    Lech.natOpGuard env c = true ∧
    ∀ (ρ : Nat → V) (x y : V),
      x ∈ˢ interp2 V ρ (m.acval Lech.natName φ) →
      y ∈ˢ interp2 V ρ (m.acval Lech.natName φ) →
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

/-- **The compiler-trust opaques are the identity, at `interp2`** —
`EnvS.reduce_ops` (`ReduceOpsV`, `SetR/EnvS.lean:138`) one currency
over, with `interp`/`cval` replaced by `interp2`/`acval`.  The stored
`Lean.reduceNat`/`Lean.reduceBool` leaf, applied to a member of its
element type's reading, *is* that member.

**This is an environment law, exactly as `eq_lawP` is**: the opaque's
leaf value is fixed by its own install (`checkReducePin`'s identity
certificate) and by nothing else, so the only possible supplier is
that install.  The v1 field cannot be imported — the transfer would
be an erasure factoring of `interp2` through `interp`, refuted at
exactly the λ-nodes the operation's leaf is made of (the literal-tier
seal II finding 1, the same refutation that makes `EqLawP` a field).

**Establishment**: `reduceOpsP_install` (`Interp2/ReduceOpsP.lean`),
at the opaque cons, from `ReducePinR`'s *recorded* identity-certificate
run (`isDefEqCore μ env F 1 (.app valA (reduceCertVar c))
(reduceCertVar c) = .ok true`) through `DefEqClaims2P` at the
one-entry element context — the run-certificate route's fifth
execution.  **Preservation**: `reduceOpsP_cons_fresh` at every other
fresh cons (the law mentions two stored leaves, so it crosses).
**Consumer**: the `ofReduceNat`/`ofReduceBool` axiom branch
(`Interp2/AxiomReduceP.lean`), whose innermost membership obligation
is exactly `op a = a`. -/
def ReduceOpsP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) : Prop :=
  ∀ c ∈ Lech.reduceOpNames, ∀ cv : ConstantVal,
    env.find? c = some (.axiomInfo cv) →
    ConstantVal.matchesPin cv (Lech.reduceOpCvA c) = true →
    (env.find? (Lech.reduceElemName c)).isSome = true ∧
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (x : V),
      x ∈ˢ interp2 V ρ (m.acval (Lech.reduceElemName c) ψ) →
      SetTheory.app (interp2 V ρ (m.acval c ψ)) x = x

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
    Lech.reservedBasisNames.contains T = false →
    Lech.EtaFamilyStored env T caps →
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
    Lech.reservedBasisNames.contains T = false →
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

/-- A fit's prefix fits, to some intermediate residual
(`TeleFitV.take`).  Lives beside the inductive: the part-6 probe
repair's consumer (`IotaRowsP`) needs it upstream of the stage kits. -/
theorem TeleFitPA.take {V : Type w} [SetTheory V] {ρ : Nat → V} :
    ∀ {T rest : AVExpr} {as : List AVExpr}, TeleFitPA V ρ T as rest →
      ∀ n : Nat, ∃ mid, TeleFitPA V ρ T (as.take n) mid := by
  intro T rest as h
  induction h with
  | @nil T' =>
    intro n
    refine ⟨T', ?_⟩
    rw [List.take_nil]
    exact TeleFitPA.nil
  | @cons u v A B rest' a as' hmem htail ih =>
    intro n
    cases n with
    | zero => exact ⟨_, TeleFitPA.nil⟩
    | succ n =>
      obtain ⟨mid, hm⟩ := ih n
      exact ⟨mid, TeleFitPA.cons hmem hm⟩

/-- The annotated reverse-opening substitution chain
(`VExpr.instRevChain`'s `AVExpr` twin, `Verify/Denote/OpenVars.lean:80`
— outermost argument consumed first, each at cut `0`, lifted past the
arguments still to come). -/
def _root_.Lech.SetP.AVExpr.instRevChain :
    List AVExpr → AVExpr → AVExpr
  | [], X => X
  | v :: vs, X =>
    Lech.SetP.AVExpr.instRevChain vs (X.inst (v.liftN vs.length) 0)

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
      -- The nested pins' open readings are carried with a
      -- CONTEXT-GUARDED chain grading (task #161 part-6 probe
      -- repair, ratified: the unconditional `∀ ρ` form was REFUTED —
      -- `not_uniform_annotOk2_open_app` — because the checker's
      -- `checkAnnotList` certificate is about `pinsP`, the pins
      -- instantiated at the public frame, and converts only
      -- context-guarded).  The grading is stated of the chained term
      -- the equality half names, at the chain's own environment:
      -- `TeleFitPA` is that environment's `Sat2` in closed form.
      -- It stays an OUTER conjunct (the consumer feeds it to
      -- `DefEqClaims2P` to *produce* the equality clause consumed
      -- by the inner block — inner placement is circular).
      (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
        ∀ i, i < RecRule.ctorParams rl →
        ∃ vpa : AVExpr,
          denoteP m.acval env φ rP
            (Lech.Verify.openRev 0 rP
              ((pins.getD i default).instantiateLevelParams
                cv.levelParams us)) = some vpa ∧
          ∀ (ρ : Nat → V) (zs : List AVExpr) (TVa restR : AVExpr),
            zs.length = rP →
            (∀ z ∈ zs, AnnotOkP V ρ z) →
            denoteP m.acval env φ 0
              (cv.type.instantiateLevelParams cv.levelParams us)
              = some TVa →
            TeleFitPA V ρ TVa zs restR →
            AnnotOkP V ρ
              (Lech.SetP.AVExpr.instRevChain zs vpa)) ∧
      ∀ (cvj : ConstantVal) (cnP cnF : Nat),
        env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AVExpr)
        (TVa TVja restR restC : AVExpr),
        xs.length = mI →
        ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
        usj.length = cvj.levelParams.length →
        Level.substFn φ cvj.levelParams usj
          = Level.substFn φ cvj.levelParams
              (Lech.recFireComparands rl cv.levelParams us
                cvj.levelParams [] rP).1 →
        (RecRule.fire rl = .plain →
          ∀ i, i < RecRule.ctorParams rl → i < mI →
            interp2 V ρ (ys.getD i default)
              = interp2 V ρ (xs.getD i default)) →
        (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
          ∀ i, i < RecRule.ctorParams rl →
          ∀ vpa : AVExpr,
            denoteP m.acval env φ rP
              (Lech.Verify.openRev 0 rP
                ((pins.getD i default).instantiateLevelParams
                  cv.levelParams us)) = some vpa →
            interp2 V ρ (ys.getD i default)
              = interp2 V ρ
                  (Lech.SetP.AVExpr.instRevChain (xs.take rP)
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

/-! ## The tower projection law (task #175 wiring, W5)

A projection-table entry (the direct-structure install's native
entries — task #175 tower-flag: the only ones) is typed by the checker
generically — the stored `ty` peeled along the parameters and the
subject (`inferBody`'s tower branch) — and reduced by the structural
rule `proj_i (ctor p⃗ x⃗) ↦ x_i`; the reading is the uniform
`projAV i` (`denoteP`'s tower branch).  The P `.proj` rows therefore
need, per stored tower entry, exactly two semantic facts about the
environment: the **typing law** (the projection of a member of the
family lands in the peeled entry type's reading, graded) and the
**iota law** (the projection of a certified constructor spine is the
selected field's reading).  Both are **environment laws** in the sense
of `caps_ok`/`rec_rules` — fixed by the direct install and by nothing
else — so they are a field of `EnvS2PM`, established at the install
(`SetP/DirectInstallP`, W4c) and transported across every other cons
(`towerOkP_cons_fresh`, `SetP/RecRulesPCons.lean`).

**Why the typing law is stated over a syntactic peel** (`peelPis`)
rather than a `TeleFitPA` fit: the `.proj` infer row holds the
subject's *reduced type* as a graded reading (`AnnotOkP` of the family
application) and the subject's membership in it — never a certified
parameter spine, since the family application is a *type* the run
produced, not an application it checked.  Building a fit from the
grading alone would need the leaf's λ-domains pinned to the type
reading's Π-domains at every row; the law takes the grading and the
membership as its premises instead, and the install discharges the
pinning once.  The residual is then the *syntactic* peel of the
entry-type reading along the readings (`denoteP_piResidual_peel`,
the fit-free mirror of `teleFitPA_residual`), which the row computes
from the checker's own `instPisAt` run.

The iota law takes the constructor application's grading alone (see
its clause). -/

/-- The syntactic Π-peel along a list of readings: the fit's residual
without the memberships (`TeleFitPA`'s spine, data only). -/
def _root_.Lech.SetP.AVExpr.peelPis : AVExpr → List AVExpr → Option AVExpr
  | T, [] => some T
  | .pi _ _ _ B, a :: as => Lech.SetP.AVExpr.peelPis (B.inst a) as
  | _, _ :: _ => none

/-- A fit's residual is the peel's. -/
theorem TeleFitPA.peelPis {V : Type w} [SetTheory V] {ρ : Nat → V} :
    ∀ {T rest : AVExpr} {as : List AVExpr}, TeleFitPA V ρ T as rest →
      Lech.SetP.AVExpr.peelPis T as = some rest := by
  intro T rest as h
  induction h with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- **The structural-η law of a tower-backed family** (task #175 W4c;
`EtaLawP`'s twin at the tower kind, keyed on the entry): a member of
the family instance is the constructor at the parameters and the tower
readings (`projS`) of its own projections — the value-level content of
the η certificate's `.proj T j b` fabrication (`etaProjs`).  Keyed on
the entry so that the direct install alone answers it (the modeled
route stores no tower entries); the η row reads it through slot `0` of
an all-tower family. -/
def TowerEtaLawP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ : Name → Nat) (T : Name)
    (entry : ProjEntry) : Prop :=
  ∀ (cvT : ConstantVal) (capsT : IndCaps),
    env.find? T = some (.indInfo cvT capsT) →
    ∀ us : List Level, us.length = entry.levelParams.length →
    ∃ TVa : AVExpr,
      denoteP m.acval env φ 0
        (cvT.type.instantiateLevelParams cvT.levelParams us) = some TVa ∧
      (∀ ρ : Nat → V, AnnotOkP V ρ TVa) ∧
      ∀ (ρ : Nat → V) (ts : List V) (rest : V) (x : V),
        ts.length = entry.numParams →
        TeleFitP V ρ TVa ts rest →
        x ∈ˢ ts.foldl SetTheory.app
          (interp2 V ρ (m.acval T (Level.substFn φ entry.levelParams us))) →
        x = (ts ++ (List.range entry.numFields).map fun j =>
              Lech.SetTheory.Tower.projS j x).foldl SetTheory.app
            (interp2 V ρ
              (m.acval entry.ctor (Level.substFn φ entry.levelParams us)))

/-- **The `Prop` guard at a use's valuation** (task #175 W4c/O4): if
the structure is a proposition there, so is the field's guard level.
The typing and iota laws of a tower entry hold under it — a data
field of a `Prop`-declared structure has no projection law (its value
is not the point).  Consumers discharge it from the kernel's syntactic
guard (`inferTypeCore`'s tower branch, `ProjEntry.fireOk`) through
`towerGuardAt_of`. -/
def TowerGuardAt (φ : Name → Nat) (entry : ProjEntry) (us : List Level) :
    Prop :=
  Level.eval (Level.substFn φ entry.levelParams us) entry.structSort = 0 →
    Level.eval (Level.substFn φ entry.levelParams us) entry.fieldSort = 0

/-- **The O5 conjunct**: a non-`Prop` family's guard level is bounded
by its result sort at every valuation (the field sorts are checked
`≤` the result sort, `checkDirectFieldSorts`), so the guard holds
wherever the structure happens to be a proposition. -/
def TowerO5 (entry : ProjEntry) : Prop :=
  (Level.isEquiv entry.structSort .zero == some true) = false →
    ∀ ψ : Name → Nat,
      Level.eval ψ entry.structSort = 0 → Level.eval ψ entry.fieldSort = 0

/-- The guard at a valuation, from the kernel's syntactic guard and O5. -/
theorem towerGuardAt_of {entry : ProjEntry} {us : List Level} {φ : Name → Nat}
    (hO5 : TowerO5 entry)
    (hg : (Level.isEquiv entry.structSort .zero == some true) = true →
      (Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
        == some true) = true) :
    TowerGuardAt φ entry us := by
  intro hs
  by_cases hp : (Level.isEquiv entry.structSort .zero == some true) = true
  · have h1 := Level.isEquiv_sound (beq_iff_eq.mp (hg hp)) φ
    rw [Level.eval_subst] at h1
    simpa [Level.eval] using h1
  · exact hO5 (by simpa using hp) _ hs

/-- **The guard at a valuation, from the fire guard** (task #175 W6):
`whnfCore`'s tower fire (`ProjEntry.fireOk`) is the tower infer
branch's own guard — a `Prop`-declared family fires only where the
field's guard level is a proposition, any other family unconditionally
— so with O5 it yields `TowerGuardAt` exactly as the infer branch
does.  (Until W6 the fire was gated on the structure's sort being
provably nonzero, `TowerStructPos`, and the iota law was stated in the
graph regime only; the squash regime is now licensed by the certified
spine's fit, see `TowerEntryLawP`'s clause (B).) -/
theorem towerGuardAt_of_fireOk {entry : ProjEntry} {us : List Level}
    {φ : Name → Nat} (hO5 : TowerO5 entry)
    (hfire : entry.fireOk us = true) : TowerGuardAt φ entry us := by
  unfold ProjEntry.fireOk at hfire
  refine towerGuardAt_of hO5 (fun hp => ?_)
  rw [hp] at hfire
  simpa using hfire

/-- **One tower-backed entry's projection law** (see the section
docstring): the entry's stored data agrees with the stored former and
constructor (whose η capability is the entry's at a non-`Prop` family
— task #175 W4c/O4), the O5 bound, and at every level instantiation
the typing law and the iota law hold under the `Prop` guard at the
entry's own body reading and the constructor's, and the family's
structural-η law holds (clause (C), `TowerEtaLawP`).

Task #175 S1: the entry stores a *body* scoped at the parameters and
the subject, not a type; the typing law is stated over the reading
of `projTele (nP + 1) body` — the body under `nP + 1` dummy binders
(`Lech/Verify/ProjTele.lean`) — whose `instPisAt` peel along the
parameters and the subject is exactly the checker's one
`instantiateList` (`ProjEntry.typeAt`, `instPisAt_typeAt`).  The
dummy binders carry the reading only; the law never reads them. -/
def TowerEntryLawP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ : Name → Nat)
    (T : Name) (i : Nat) (entry : ProjEntry) : Prop :=
  entry.structName = T ∧ entry.idx = i ∧
  i < entry.numFields ∧
  (∃ (cvT : ConstantVal) (capsT : IndCaps),
    env.find? T = some (.indInfo cvT capsT) ∧
    cvT.levelParams = entry.levelParams ∧
    capsT.eta = !(Level.isEquiv entry.structSort .zero == some true) ∧
    capsT.etaCtor = entry.ctor ∧
    capsT.etaParams = entry.numParams ∧
    capsT.etaFields = entry.numFields) ∧
  TowerO5 entry ∧
  ∃ cvC : ConstantVal,
    env.find? entry.ctor
      = some (.ctorInfo cvC entry.numParams entry.numFields) ∧
    cvC.levelParams = entry.levelParams ∧
    (∀ us : List Level, us.length = entry.levelParams.length →
      -- (A) the typing law
      (∃ Ta : AVExpr,
        denoteP m.acval env φ 0
          (Lech.projTele (entry.numParams + 1)
            (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta ∧
        (TowerGuardAt φ entry us →
        ∀ (ρ : Nat → V) (vs : List AVExpr) (x rest : AVExpr),
          vs.length = entry.numParams →
          AnnotOkP V ρ (AVExpr.mkAppN
            (m.acval T (Level.substFn φ entry.levelParams us)) vs) →
          AnnotOkP V ρ x →
          interp2 V ρ x ∈ˢ interp2 V ρ (AVExpr.mkAppN
            (m.acval T (Level.substFn φ entry.levelParams us)) vs) →
          Lech.SetP.AVExpr.peelPis Ta (vs ++ [x]) = some rest →
          AnnotOkP V ρ (projAV i x) ∧ AnnotOkP V ρ rest ∧
            interp2 V ρ (projAV i x) ∈ˢ interp2 V ρ rest)) ∧
      -- (B) the iota law: the projection of a *graded* constructor
      -- application is the selected field, at every valuation under
      -- the guard (task #175 W6).  Two premises: the application's
      -- grading (its slot chain — the graph regime's whole premise,
      -- where every constructor binder is graph-regime and graph
      -- rigidity pins the memberships), and the certified spine's fit
      -- against the constructor's own type reading (`projCert`'s
      -- `iotaCerts`, through `certs_teleP`) — the squash regime's
      -- premise, where the application is the point and the fit pins
      -- the selected field to a proposition's domain (its sort is `0`
      -- there: the O5 bound at a non-`Prop` family, the guard at a
      -- `Prop`-declared one).
      (∃ TCa : AVExpr,
        denoteP m.acval env φ 0
          (cvC.type.instantiateLevelParams cvC.levelParams us) = some TCa ∧
        (TowerGuardAt φ entry us →
        ∀ (ρ : Nat → V) (ys : List AVExpr) (rest : V),
        ys.length = entry.numParams + entry.numFields →
        AnnotOkP V ρ (AVExpr.mkAppN
          (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) ys) →
        TeleFitP V ρ TCa (ys.map (interp2 V ρ)) rest →
        interp2 V ρ (projAV i (AVExpr.mkAppN
            (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) ys))
          = interp2 V ρ (ys.getD (entry.numParams + i) default)))) ∧
    -- (C) the structural-η law (task #175 W4c)
    TowerEtaLawP m φ T entry

/-- **The tower projection law, keyed on every stored entry**
(`RecRulesP`'s sibling).  Task #175 tower-flag: every stored table is
a real one, so the law is uniform — no flag premise. -/
def TowerOkP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ : Name → Nat) : Prop :=
  ∀ (T : Name) (i : Nat) (entry : ProjEntry),
    env.findProj? T i = some entry →
    TowerEntryLawP m φ T i entry

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
  /-- stored constants inhabit their types' readings (task #175 S1:
  a projection table's constant type is the closed dummy `Sort 1`
  and its leaf is `Sort 0`, so the row holds of tables too — the
  W4c-era `isTowerEntry` guard is gone; that a table is not a term is
  `inferTypeCore`'s own rejection of a `.const` naming one) -/
  mem_typeP : ∀ c ∈ env.consts,
    ∀ (ψ : Name → Nat) (ta : AVExpr),
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
  /-- every stored compiler-trust opaque is the identity on its
  element type (`EnvS.reduce_ops`'s mirror; an *environment law* for
  the same reason `eq_lawP` is — the opaque's leaf is fixed by its own
  install's identity certificate and by nothing else, so the supplier
  is `harvestOpaqueP`.  Consumed by the `ofReduce*` axiom branch) -/
  reduce_ops : ReduceOpsP base2
  /-- the stored tower-backed projection entries' typing and iota
  laws (task #175 wiring W5; an *environment law* for the same reason
  `rec_rules` is — a direct structure's entries are fixed by its
  install and by nothing else, so the supplier is the direct install
  step.  Consumed by the `.proj` rows' tower branches) -/
  tower_ok : ∀ φ : Name → Nat, TowerOkP base2 φ

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
  intro d n ci us hf _hnt hlen
  have hmem := Lech.Semantics.Env.find?_mem hf
  have hname := Lech.Semantics.Env.find?_name hf
  obtain ⟨ta, hta⟩ :=
    m.type_reads ci hmem (Level.substFn φ ci.toConstantVal.levelParams us)
  have hwf := m.base2.wf ci hmem
  -- the reading is closed, hence depth-free
  have hcl : ∀ k : Nat, ta.liftN 1 k = ta := fun k =>
    denoteP_closed m.base2.acval_erase m.base2.cval_closed
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

/-- A stored constant whose type is a constant application is not a
tower table (a table's constant type is the closed dummy `Sort 1`,
task #175 S1; the capstone reads it: a table never has type `Empty`). -/
theorem notTower_of_type_const {c : ConstantInfo} {n : Name} {us : List Level}
    (hty : c.toConstantVal.type = .const n us) : c.isTowerEntry = false := by
  cases c with
  | projInfo tbl => simp [ConstantInfo.toConstantVal] at hty
  | _ => rfl

/-- **The bridge invariant, from the P invariant** (task #161 S7,
Wall C step (e)) — `EnvS.toEnvFacts`'s P-side twin, and the last thing
`EnvS2PM.base` was for.  Every field is a projection:

| `EnvFacts` field | source |
|---|---|
| `cval`, `cval_closed`, `wf`, `proj_ok` | `base2`'s own |
| `val_params` | `acval_params`, erased |
| `ty_denotes` | `type_reads` through `denoteP_erase` |
| `defn_eq`, `thm_ok` | `defn_reads` through `denoteP_erase` |
| `rec_rhs_denotes`, `rec_params_le` | `rec_rules`' `RecRuleLawP`, whose first two components are exactly those two facts |
| `nat_op_guard` | `nat_ops`/`div_mod` through `natOpStored_inv` |

Nothing of the collapsed model is consulted, and the P lane's
`checkDeclR_ofEnvRE` runs on this. -/
def toEnvFacts {V : Type w} [SetTheory V] {μ : CheckMode}
    {env : Env} (m : EnvS2PM V μ env) : Lech.Semantics.EnvFacts env where
  cval := m.base2.cvalE
  cval_closed := m.base2.cval_closed
  wf := m.base2.wf
  val_params := fun n ci hf φ₁ φ₂ hp =>
    congrArg AVExpr.erase (m.base2.acval_params n ci hf φ₁ φ₂ hp)
  ty_denotes := fun c hc ψ => by
    obtain ⟨ta, hta⟩ := m.type_reads c hc ψ
    exact ⟨ta.erase,
      denoteP_erase m.base2.acval_erase 0 c.toConstantVal.type hta⟩
  defn_eq := fun cv value hint hmem ψ =>
    denoteP_erase m.base2.acval_erase 0 value
      (m.defn_reads ψ cv value (.inl ⟨hint, hmem⟩))
  rec_rhs_denotes := fun n cv mI rP rules hf r hr hfire us ψ hlen => by
    obtain ⟨-, hus⟩ := m.rec_rules ψ n cv mI rP rules hf r hr hfire
    obtain ⟨Ra, hRa, -, -⟩ := hus us hlen
    exact ⟨Ra.erase, denoteP_erase m.base2.acval_erase 0 _ hRa⟩
  rec_params_le := fun n cv mI rP rules hf r hr hfire =>
    (m.rec_rules (fun _ => 0) n cv mI rP rules hf r hr hfire).1
  proj_ok := m.base2.proj_ok
  thm_ok := fun cv value hmem ψ =>
    denoteP_erase m.base2.acval_erase 0 value
      (m.defn_reads ψ cv value (.inr hmem))
  nat_op_guard := fun c hmem hst => by
    obtain ⟨cv, v, hh, hf⟩ := Lech.natOpStored_inv hst
    rcases hmem with hm | hm
    · exact (m.nat_ops (fun _ => 0) c hm cv v hh hf).1
    · exact (m.div_mod (fun _ => 0) c hm cv v hh hf).1

/-- The P bridge invariant keeps the carrier's valuation —
definitionally. -/
theorem toEnvFacts_cval {V : Type w} [SetTheory V] {μ : CheckMode}
    {env : Env} (m : EnvS2PM V μ env) :
    (toEnvFacts m).cval = m.base2.cvalE := rfl

end EnvS2PM

/-- The empty environment carries the P invariant (the fold's base
case): the core is the mode-indexed empty's projection, and every P
field is vacuous — no constants, guards false, and the empty leaf
`.const .empty [0]` is bit-valid because a constant leaf carries no
binder. -/
noncomputable def EnvS2PM.empty (V : Type w) [SetTheory V]
    (μ : CheckMode) : EnvS2PM V μ Env.empty where
  base2 := EnvS2Core.empty
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
    rw [show Lech.natLitSupported Env.empty = false from rfl] at hg
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
  reduce_ops := fun c _ cv hf => by
    rw [show Env.empty.find? c = none from rfl] at hf
    exact nomatch hf
  tower_ok := fun _ T i entry hf => by
    have : Env.empty.findProj? T i = none := rfl
    rw [this] at hf
    exact nomatch hf

end Lech.SetP
