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
open Setlec (CheckMode Env Expr Name Level ConstantInfo)

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

end Setlec.SetR.Interp2
